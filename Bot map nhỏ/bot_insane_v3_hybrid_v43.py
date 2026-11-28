# V35: V18 search foundation + deadline guard + score-differential territory/item strategy
# + fixv3 (ROAM_CFG 3 muc + Snatch cum/2x2 cach 1-2 o: cum->wing, 2x2 don->hourglass)
# + fixv4/fixv5 (Boost-aware, Post-boost, Compactness chong chu L/dai hep)
# + v3 (chong ziczac, quan tinh _MEM, in_home_boost huong ra bien, SSS chiem trung tam (0,0))
# Giu: API_URL, GAME_ID, PLAYER_ID, PLAYER_TOKEN, STAGE, decide(state), stdlib, <40ms/luot.
import json
import os
from collections import deque
from heapq import heappush, heappop
from time import perf_counter, process_time, sleep
import signal
from urllib.request import Request, urlopen

API = os.environ.get("API_URL", "http://127.0.0.1:4100/api")
GAME = os.environ.get("GAME_ID", "local")
ME = os.environ.get("PLAYER_ID", "me")
TOKEN = os.environ.get("PLAYER_TOKEN", "local")
STAGE = os.environ.get("STAGE", "GROUP").upper()  # GROUP | KNOCKOUT

DIRS = ("up", "right", "down", "left")
DID = {n: i for i, n in enumerate(DIRS)}

# --- Bo nho trang thai qua cac tick: quan tinh huong + theo doi post-boost ---
_MEM = {"dir": -1, "game": None, "prev_wing": 0, "post_boost": 0}
# --- Log trang thai de theo doi khi chay ---
_LAST_ROAM = {"level": "?", "dist": "?", "boost": "0/0"}
_LAST_REASON = "init"
_CORE_CACHE = None

# =============================================================================
# HAI TRINH (Roaming Range) - 3 MUC THEO KHOANG CACH DICH GAN NHAT
# =============================================================================
ROAM_CFG = {
    "near": {
        "dist_near":      8,
        "max_depth_open": 18,
        "max_depth_late": 14,
        "beam_width":     24,
        "cnt_w":          0.38,
        "back_w":         0.42,
        "close_bonus":    0.0,
        "pull_scale":     0.8,
    },
    "mid": {
        "dist_mid":       18,
        "max_depth_open": 26,
        "max_depth_late": 19,
        "beam_width":     32,
        "cnt_w":          0.46,
        "back_w":         0.34,
        "close_bonus":    0.08,
        "pull_scale":     1.0,
    },
    "far": {
        "max_depth_open": 34,
        "max_depth_late": 24,
        "beam_width":     40,
        "cnt_w":          0.56,
        "back_w":         0.26,
        "close_bonus":    0.18,
        "pull_scale":     1.25,
    },
}

# --- Tham so sss: so luot dau tien uu tien manh chiem toa do chi dinh (mac dinh (0,0) giua map) ---
SSS = int(os.environ.get("SSS", "35"))       # so luot dau tien ap dung (0 = tat)
SSS_POS = None                               # toa do chi dinh (x, y) tren map; None = tu dong giua map (0,0)
SSS_WEIGHT = 1.0                             # he so manh/yeu luc hut ve toa do SSS_POS (vd: 1.5 manh hon, 0.5 nhe hon)

def _parse_sss_pos():
    raw = os.environ.get("SSS_POS", "").strip()
    if raw:
        parts = raw.replace(";", ",").split(",")
        if len(parts) == 2:
            return (int(parts[0]), int(parts[1]))
    return SSS_POS

# --- Tham so Boost-aware & Post-boost (tu fixv4) ---
BOOST_MIN_LEFT = 2        # wing con < N luot (dich khong stun) -> khong mo them chuoi xa
BOOST_OUT_BONUS = 1.50    # dang co wing: uu tien item NGOAI lanh tho
BOOST_IN_PENALTY = 0.35   # dang co wing: giam diem item TRONG lanh tho
BOOST_IN_WINDOW = 1.35    # toi item kip trong thoi gian wing
BOOST_LATE_PENALTY = 0.65 # toi tre sau khi het wing
POST_BOOST_TURNS = 8      # sau khi het wing: uu tien tao hai trinh moi

# --- Tham so Snatch nhanh cum item / item 2x2 cach 1-2 o (tu fixv3) ---
SNATCH_DIST = 2           # cach vi tri hien tai <= 2 buoc
SNATCH_CLUSTER_R = 2      # ban kinh Manhattan xac dinh cum (>= 2 item)
SNATCH_WING_BONUS = 2.2   # uu tien boost (wing) o gan khi co cum item
SNATCH_FREEZE_BONUS = 2.8 # uu tien dong bang (hourglass) o gan khi co item 2x2 don
SNATCH_2X2_BONUS = 1.6    # he so item 2x2 (megabomb / saber)
SNATCH_CLUSTER_BONUS = 1.5

# --- Tham so Chong chu L / dai hep 2 o & Do tron vong (tu fixv4/fixv5 + v3) ---
COMPACT_MIN = 0.40        # do dac toi thieu cua vong khép
COMPACT_W = 0.15          # thuong vong tron/vuong
NARROW_PENALTY = 1.15     # phat vong chu L / dai hep 2 o


def _turns(steps, wing):
    fast = min(steps, 2 * wing) if wing > 0 else 0
    return (fast + 1) // 2 + steps - fast


class BudgetEnd(Exception):
    pass


# Cheap legal action before building the search board. No full-map traversal.
# Risk is inferred from public state, not a specific opponent implementation.
def quick_move(st, me):
    x, y = int(me["x"]), int(me["y"])
    w, h = st["width"], st["height"]
    hd = DID.get(me.get("lastDir"), -1)
    home = str(me["index"])
    owner = st["owner"]
    trail = {tuple(c) for c in me.get("trail", ())}
    enemies = [e for e in st["players"] if e["playerId"] != ME]
    occupied = {(e["x"], e["y"]) for e in enemies}
    danger = set()
    offsets = ((0,-1),(1,0),(0,1),(-1,0))
    for e in enemies:
        if e.get("stun") or e.get("freeze"):
            continue
        rev = DID.get(e.get("lastDir"), -1)
        et = {tuple(c) for c in e.get("trail", ())}
        for d,(dx,dy) in enumerate(offsets):
            if rev >= 0 and d == (rev+2)%4: continue
            a,b=e["x"]+dx,e["y"]+dy
            if (a,b) in et: continue
            danger.add((a,b))
            if e.get("wing"):
                for nd,(ux,uy) in enumerate(offsets):
                    if nd != (d+2)%4: danger.add((a+ux,b+uy))
    # Only the local 5x5 footprint is needed for the emergency action.
    blocked=set()
    for o in st.get("obstacles", ()):
        ox,oy=o["x"],o["y"]
        if ox>x+2 or oy>y+2 or ox+o.get("w",1)<=x-2 or oy+o.get("h",1)<=y-2:
            continue
        for a in range(max(x-2,ox),min(x+3,ox+o.get("w",1))):
            for b in range(max(y-2,oy),min(y+3,oy+o.get("h",1))):
                blocked.add((a,b))
    def valid(a,b):
        return 0 <= a < w and 0 <= b < h and (a,b) not in blocked
    slash = set()
    for ev in st.get("pendingSlashes", ()):
        if ev.get("by") != ME and ev.get("turn",999)-st.get("turn",0)<=1:
            rows=ev.get("rows",[])
            if rows: slash.update(range(rows[0],rows[-1]+1))
    options=[]
    core = _CORE_CACHE
    known = core is not None and core[0]==GAME and core[1]==w and core[2]==h
    for d,(dx,dy) in enumerate(offsets):
        if hd >= 0 and d == (hd+2)%4: continue
        a,b=x+dx,y+dy
        if not valid(a,b) or (a,b) in occupied or (a,b) in trail: continue
        inside=owner[b][a]==home
        score= (35 if trail else 0) if inside else (0 if trail else 4)
        if trail and not inside and len(trail)>=int((st.get("rules") or {}).get("maxTrail",120)): score-=100
        if (a,b) in danger: score-=65
        if b in slash and not inside: score-=60
        # Local escape and open-space potential; prefer continuing rather than circling.
        escape_count = 0
        for nd,(ux,uy) in enumerate(offsets):
            if nd==(d+2)%4: continue
            c,f=a+ux,b+uy
            if valid(c,f) and (c,f) not in occupied and (c,f) not in trail:
                escape_count += 1
                score+=2
                if trail and owner[f][c]==home: score+=12
                elif not trail and owner[f][c]!=home: score+=2
        # Static leaf means permanent trap because reverse is forbidden.
        static_escape=any(nd!=(d+2)%4 and valid(a+ux,b+uy) for nd,(ux,uy) in enumerate(offsets))
        core_bad=known and bool(core[4] & (1<<((y+1)*(w+2)+x+1))) and not bool(core[4] & (1<<((b+1)*(w+2)+a+1)))
        if not escape_count: score -= 80
        if not static_escape or core_bad: score -= 10000
        for it in st.get("items", ()):
            z=2 if it.get("type") in ("megabomb","saber") else 1
            if it["x"]<=a<it["x"]+z and it["y"]<=b<it["y"]+z: score+=10
        score+=0.2*(d==hd)
        options.append((score,d))
    return DIRS[max(options)[1]] if options else None


class Board:
    def __init__(self, st, deadline=float("inf"), cpu_deadline=float("inf")):
        self.deadline = deadline
        self.cpu_deadline = cpu_deadline
        self.w = int(st["width"])
        self.h = int(st["height"])
        self.stride = self.w + 2
        self.offs = (-self.stride, 1, self.stride, -1)
        self.turn = int(st.get("turn", 0) or 0)
        cfg = st.get("config") or {}
        self.max_turns = int(cfg.get("maxTurns", 300) or 300)
        self.remaining = self.max_turns - self.turn
        self.opening = self.turn < min(80, self.max_turns // 3)
        self.late = self.remaining <= max(1, int(self.max_turns * 0.3))
        rules = st.get("rules") or {}
        self.rules = rules
        self.trail_limit = int(rules.get("maxTrail", 120))
        self.break_bonus = rules.get("breakBonus", 10)
        self.wing_turns = rules.get("wingTurns", [5, 10])
        self.wing_turns = self.wing_turns[0] if isinstance(self.wing_turns, list) else self.wing_turns
        self.freeze_turns = rules.get("freezeTurns", [10, 20])
        self.freeze_turns = self.freeze_turns[0] if isinstance(self.freeze_turns, list) else self.freeze_turns
        self.saber_rows = rules.get("saberRows", 2)
        delay = rules.get("saberDelayTurns", 4)
        tick_ms = max(1, int(st.get("tickInterval", 500) or 500))
        if delay is not None and int(delay) > 0:
            delay = max(int(delay), (2500 + tick_ms - 1) // tick_ms)

        me = next((p for p in st.get("players", []) if p.get("playerId") == ME), None)
        if me is None:
            me = st["players"][0]
        self.me = me
        self.wing = int(me.get("wing", 0) or 0)
        sx, sy = int(me["x"]), int(me["y"])
        self.sx, self.sy = sx, sy
        self.start = self.idx(sx, sy)
        self.heading = DID.get(me.get("lastDir"), -1)
        self.area = int(me.get("area", 0))
        self.score = me.get("score", self.area + me.get("bonus", 0))

        mk = str(me["index"])
        self.full = self.home = self.blocked = self.trail = self.stolen_land = 0
        self.edge = 0
        for y, row in enumerate(st.get("owner") or []):
            self.check_budget()
            left = self.idx(0, y)
            line = ((1 << self.w) - 1) << left
            self.full |= line
            if y in (0, self.h - 1):
                self.edge |= line
            self.edge |= (1 << left) | (1 << (left + self.w - 1))
            for x, ch in enumerate(row):
                if ch == mk:
                    self.home |= 1 << (left + x)
                elif ch.isdigit():
                    self.stolen_land |= 1 << (left + x)
        for o in st.get("obstacles") or []:
            ox, oy = int(o["x"]), int(o["y"])
            ow, oh = int(o.get("w", 1)), int(o.get("h", 1))
            for yy in range(oy, min(self.h, oy + oh)):
                for xx in range(ox, min(self.w, ox + ow)):
                    if 0 <= xx < self.w and 0 <= yy < self.h:
                        self.blocked |= 1 << self.idx(xx, yy)
        for x, y in me.get("trail", ()):
            if 0 <= x < self.w and 0 <= y < self.h:
                self.trail |= 1 << self.idx(x, y)
        self.free = self.full & ~self.blocked
        global _CORE_CACHE
        cached=_CORE_CACHE
        if cached is not None and cached[:4]==(GAME,self.w,self.h,self.blocked):
            core=cached[4]
        else:
            core=self.free
            if self.blocked:
                # 2-core: repeatedly remove degree-0/1 cells. Entering a
                # removed branch can never be undone without a 180-degree turn.
                while core:
                    self.check_budget()
                    a=(core<<1)&core; c=(core>>1)&core
                    d=(core<<self.stride)&core; e=(core>>self.stride)&core
                    nxt=(a&c)|(a&d)|(a&e)|(c&d)|(c&e)|(d&e)
                    if nxt==core: break
                    core=nxt
            _CORE_CACHE=(GAME,self.w,self.h,self.blocked,core)
        self.move_free=core if core & (1<<self.start) else self.free
        self.home &= self.free
        self.trail &= self.free & ~self.home
        self.trail_cnt = self.trail.bit_count()

        if self.trail_cnt > 0:
            _t = self.trail
            _xs, _ys = [], []
            while _t:
                _b = _t & -_t
                _t ^= _b
                _p = _b.bit_length() - 1
                _row, _col = divmod(_p, self.stride)
                _xs.append(_col - 1)
                _ys.append(_row - 1)
            self.init_mnx = min(_xs)
            self.init_mxx = max(_xs)
            self.init_mny = min(_ys)
            self.init_mxy = max(_ys)
        else:
            self.init_mnx = sx
            self.init_mxx = sx
            self.init_mny = sy
            self.init_mxy = sy

        self.enemies = [p for p in st.get("players", []) if p.get("playerId") != ME]
        es = [p.get("score", p.get("area", 0) + p.get("bonus", 0)) for p in self.enemies]
        order = sorted([(s, p.get("area", 0), p) for s, p in zip(es, self.enemies)],
                       key=lambda t: (t[0], t[1]), reverse=True)
        self.my_rank = 1 + sum(1 for s, a, _ in order if (s, a) > (self.score, self.area))
        self.leader = order[0][2] if order else None
        self.attack = (STAGE == "KNOCKOUT" and self.late and self.my_rank >= 2 and self.leader is not None)
        if STAGE == "KNOCKOUT" and self.late and self.my_rank == 1 and order:
            if self.score - order[0][0] < 15:
                self.attack = True

        self.target_land = 0
        victims = [p for p in self.enemies if int(p.get("stun", 0) or 0) >= 4]
        picks = []
        if self.attack and self.leader is not None:
            picks.append(self.leader)
        picks += [p for p in victims if p not in picks]
        if picks:
            marks = {str(p["index"]) for p in picks}
            for y, row in enumerate(st.get("owner") or []):
                for x, ch in enumerate(row):
                    if ch in marks:
                        self.target_land |= 1 << self.idx(x, y)
            self.target_land &= self.free

        self.enemy_cells = 0
        self.enemy_trails = {}
        self.collision = 0
        self.arr_cache = {}
        self.en_arr_cache = {}
        self.enemy_bfs = []
        self.enemy_static = []
        horizon = min(self.w * self.h, max(48, min(2*(self.w+self.h),self.trail_limit+16)))
        self.enemy_horizon = horizon
        for i, e in enumerate(self.enemies):
            pos = self.idx(int(e["x"]), int(e["y"]))
            self.enemy_cells |= 1 << pos
            for x, y in e.get("trail", ()):
                if 0 <= x < self.w and 0 <= y < self.h:
                    c = self.idx(x, y)
                    self.enemy_trails[c] = self.enemy_trails.get(c, 0) | (1 << i)
            dl = max(int(e.get("freeze", 0) or 0), int(e.get("stun", 0) or 0))
            we = int(e.get("wing", 0) or 0)
            own_trail = 0
            for ex, ey in e.get("trail", ()):
                if 0 <= ex < self.w and 0 <= ey < self.h:
                    own_trail |= 1 << self.idx(ex, ey)
            enemy_walk = (self.free & ~own_trail) | (1 << pos)
            cur_layers = self.dist_layers(1 << pos, enemy_walk, horizon)
            self.enemy_bfs.append((cur_layers, dl, we, int(e["x"]), int(e["y"])))
            self.enemy_static.append(self.dist_layers(1 << pos, self.free, horizon) if own_trail else cur_layers)
            if dl > 0:
                continue
            hd = DID.get(e.get("lastDir"), -1)
            for s, d in self.nbrs(pos, hd, self.free):
                self.collision |= 1 << s
                if we:
                    for s2, _ in self.nbrs(s, d, self.free):
                        self.collision |= 1 << s2

        self.slashes = {}
        for ev in st.get("pendingSlashes", ()):
            if ev.get("by") == ME:
                continue
            rows = ev.get("rows") or [0, -1]
            stop = int(ev.get("turn", 0) or 0) - self.turn
            for r in range(int(rows[0]), int(rows[-1]) + 1):
                if 0 <= r < self.h and stop < self.slashes.get(r, 999):
                    self.slashes[r] = stop

        enemy_areas = sorted((int(e.get("area", 0) or 0) for e in self.enemies), reverse=True)
        base_vals = {
            "bomb": min(12.0, 8.0 + 0.15 * min(16, enemy_areas[0] if enemy_areas else 0)),
            "megabomb": min(32.0, 19.0 + 0.17 * sum(min(25, a) for a in enemy_areas)),
            "wing": 10.0,
            "hourglass": min(20.0, 14.0 + 0.03 * sum(enemy_areas[:2])),
            "saber": min(42.0, 14.0 + 0.18 * self.w * max(1, int(rules.get("saberRows", 2)))),
        }
        if self.opening:
            base_vals["wing"] += 5
        self.item_cells = {}
        raw = []
        for i, it in enumerate((*st.get("items", ()), *st.get("upcomingItems", ()))):
            kind = it.get("type")
            if kind not in base_vals:
                continue
            side = 2 if kind in ("megabomb", "saber") else 1
            spawn = int(it.get("turn", self.turn) or self.turn) - self.turn
            if spawn < 0:
                spawn = 0
            v = float(base_vals[kind])
            cells = []
            coords = []
            for yy in range(int(it["y"]), min(self.h, int(it["y"]) + side)):
                for xx in range(int(it["x"]), min(self.w, int(it["x"]) + side)):
                    if 0 <= xx < self.w and 0 <= yy < self.h:
                        p = self.idx(xx, yy)
                        self.item_cells.setdefault(p, []).append((i, spawn, v, kind))
                        cells.append(p)
                        coords.append((xx, yy))
            if cells:
                raw.append((kind, spawn, v, cells, side > 1 or len(cells) > 1, coords))
        if delay is None:
            delay = 4
        self.saber_delay = delay
        return_walk = self.move_free & ~self.trail
        self.distance = self.dist_layers(self.home & self.move_free, return_walk)
        self.frontier_cells, self.frontier_sizes = self._useful_frontier()
        self.frontier = self.dist_layers(self.frontier_cells & self.move_free, self.move_free)
        self.my_bfs = self.dist_layers(1 << self.start, return_walk, min(self.w * self.h, 1200))
        self.free_count = self.free.bit_count()
        self.items_for_race = raw
        self.target_layers = self._target_field(raw)
        self.opportunity = None
        self.opp_start = 999
        self.opp_home = 999
        # Concentrated real items are strategic objectives even when a direct
        # out-and-back pickup is currently unsafe. Do not apply on sparse items.
        active=[r for r in raw if r[1]<=4 and r[0] in ("wing","hourglass","megabomb","saber")]
        if len(active)>=3 and self.remaining>35:
            groups=[]
            for kind,spawn,val,cells,_,coords in active[:24]:
                x,y=coords[0]
                close=[r for r in active[:24] if abs(r[5][0][0]-x)+abs(r[5][0][1]-y)<=max(5,min(self.w,self.h)//5)]
                groups.append((len(close),sum(r[2] for r in close),close))
            count,_,cluster=max(groups,key=lambda r:(r[0],r[1]))
            if count>=3 and count*2>=len(active):
                mask=0
                for r in cluster:
                    for p in r[3]: mask|=1<<p
                mask&=self.move_free&~self.home
                if mask:
                    layers=self.dist_layers(mask,self.move_free,64)
                    self.opp_start=self.dist_to(1<<self.start,layers)
                    self.opp_home=self.dist_to(self.home,layers)
                    if 3<self.opp_home<65 and self.opp_start<65:
                        self.opportunity=layers
        # When no single dominant cluster exists, approach the best accessible
        # resource pocket instead. Only use the extra strategic pull when
        # significant value is distributed across distinct resource regions.
        self.distributed_cluster = False
        if self.opportunity is None and len(active)>=5 and self.remaining>35:
            groups=[]
            rad=max(5,min(self.w,self.h)//5)
            for kind,spawn,val,cells,_,coords in active[:24]:
                x,y=coords[0]
                close=[r for r in active[:24] if abs(r[5][0][0]-x)+abs(r[5][0][1]-y)<=rad]
                if len(close)<3: continue
                mask=0
                for r in close:
                    for p in r[3]: mask|=1<<p
                mask&=self.move_free&~self.home
                if not mask: continue
                steps=self.dist_to(mask,self.my_bfs)
                land=self.dist_to(mask,self.distance)
                value=sum(r[2] for r in close)
                if 2<land<65 and steps<65 and value>=48:
                    groups.append((value/(5+steps),mask))
            if groups:
                _,mask=max(groups)
                layers=self.dist_layers(mask,self.move_free,64)
                self.opp_start=self.dist_to(1<<self.start,layers)
                self.opp_home=self.dist_to(self.home,layers)
                if 2<self.opp_home<65 and self.opp_start<65:
                    self.opportunity=layers
                    self.distributed_cluster=True
        self.outside = None
        self.close_cache = {}

        # --- sss luot dau: tinh khoang cach toi toa do chi dinh SSS_POS (mac dinh giua map) ---
        self.center_rush = self.turn < SSS
        self.center_layers = None
        self.start_center_dist = 999
        if self.center_rush:
            cmask = 0
            target_xy = _parse_sss_pos()
            if target_xy is not None:
                tx = max(0, min(self.w - 1, int(target_xy[0])))
                ty = max(0, min(self.h - 1, int(target_xy[1])))
                cmask = 1 << self.idx(tx, ty)
            else:
                for cy in {(self.h - 1) // 2, self.h // 2}:
                    for cx in {(self.w - 1) // 2, self.w // 2}:
                        if 0 <= cx < self.w and 0 <= cy < self.h:
                            cmask |= 1 << self.idx(cx, cy)
            cmask &= self.move_free
            if cmask:
                self.center_layers = self.dist_layers(cmask, self.move_free, 44)
                self.start_center_dist = self.dist_to(1 << self.start, self.center_layers)

        self.roam = self._calc_roam_level()

    def check_budget(self):
        if perf_counter() >= self.deadline or process_time() >= self.cpu_deadline:
            raise BudgetEnd

    def _useful_frontier(self):
        """Movement-connected neutral components; skip 1-3 cell sealed repair pockets."""
        unseen = self.move_free & ~self.home
        comps = []
        while unseen:
            self.check_budget()
            seed = unseen & -unseen
            unseen ^= seed
            comp = wave = seed
            while wave:
                self.check_budget()
                nxt = self.expand(wave) & unseen
                if not nxt:
                    break
                unseen ^= nxt
                comp |= nxt
                wave = nxt
            comps.append((comp, comp.bit_count()))
        if not comps:
            return self.move_free & ~self.home, ()
        largest = max(n for _, n in comps)
        threshold = max(4, largest // 12)
        useful = [(m, n) for m, n in comps if n >= threshold]
        if not useful:
            useful = [max(comps, key=lambda z: z[1])]
        mask = 0
        for comp, _ in useful:
            mask |= comp
        return mask, tuple(sorted((n for _, n in comps), reverse=True)[:8])

    def idx(self, x, y):
        return (y + 1) * self.stride + x + 1

    def expand(self, cells):
        return cells | (cells << 1) | (cells >> 1) | (cells << self.stride) | (cells >> self.stride)

    def dist_layers(self, cells, walk, max_steps=999):
        walk |= cells
        layers = [cells]
        while layers[-1] != walk and len(layers) <= max_steps:
            self.check_budget()
            r = self.expand(layers[-1]) & walk
            if r == layers[-1]:
                break
            layers.append(r)
        return layers

    @staticmethod
    def dist_to(bit, layers):
        lo, hi = 0, len(layers)
        while lo < hi:
            mid = (lo + hi) // 2
            if bit & layers[mid]:
                hi = mid
            else:
                lo = mid + 1
        return lo if lo < len(layers) else 999

    def nbrs(self, pos, prev, walk):
        """Uu tien di thang (prev) truoc khi re vuong goc de chong ziczac."""
        opp = (prev + 2) % 4 if prev >= 0 else -1
        if prev >= 0 and prev != opp:
            s = pos + self.offs[prev]
            if walk & (1 << s):
                yield s, prev
        for d, dl in enumerate(self.offs):
            if d == opp or d == prev:
                continue
            s = pos + dl
            if walk & (1 << s):
                yield s, d

    def step_turn(self, steps):
        return _turns(steps, self.wing)

    def enemy_arrivals(self, pos):
        c = self.en_arr_cache.get(pos)
        if c is not None:
            return c
        row, col = divmod(pos, self.stride)
        x, y = col - 1, row - 1
        ts = []
        for ei, (layers, dl, we, ex, ey) in enumerate(self.enemy_bfs):
            # A rival can close/cancel its trail on a later tick. Terrain-only
            # ETA is a conservative lower bound even while its trail exists.
            static = self.enemy_static[ei]
            d = self.dist_to(1 << pos, static)
            if d == 999:
                if len(static) <= self.enemy_horizon:
                    ts.append(999)
                    continue
                d = abs(x-ex)+abs(y-ey)
            ts.append(max(1, dl + _turns(d, max(0, we - dl))))
        t = tuple(ts)
        self.en_arr_cache[pos] = t
        return t

    def danger(self, pos):
        c = self.arr_cache.get(pos)
        if c is not None:
            return c
        eta = min(self.enemy_arrivals(pos), default=999)
        eta = min(eta, self.slashes.get(pos // self.stride - 1, 999))
        self.arr_cache[pos] = eta
        return eta

    def open_deadline(self):
        dl = 999
        t = self.trail
        while t:
            b = t & -t
            t ^= b
            dl = min(dl, self.danger(b.bit_length() - 1))
        return dl

    def flood(self, bound):
        water = self.full & ~bound
        reach = water & self.edge
        while True:
            self.check_budget()
            e = self.expand(reach) & water
            if e == reach:
                return reach
            reach = e

    def captured(self, trail):
        hit = self.close_cache.get(trail)
        if hit is None:
            if self.outside is None:
                self.outside = self.flood(self.home)
            after = self.flood(self.home | trail)
            g = self.free & ~after
            g &= self.free & ~self.home
            hit = (g.bit_count(), (g & self.stolen_land).bit_count(),
                   (after & self.free).bit_count())
            self.close_cache[trail] = hit
        return hit

    def home_route_distance(self, start, heading, blocked):
        """Exact no-reverse return BFS using four bitboard heading layers."""
        if (1 << start) & self.home:
            return 0
        walk = self.move_free & ~blocked
        prev = [0, 0, 0, 0]
        for nxt, nd in self.nbrs(start, heading, walk):
            bit = 1 << nxt
            if bit & self.home:
                return 1
            prev[nd] |= bit
        if not any(prev):
            return 999
        seen = prev[:]
        depth = 1
        limit = min(121, self.trail_limit + 1)
        while depth < limit:
            self.check_budget()
            depth += 1
            cur = [0, 0, 0, 0]
            for hd, mask in enumerate(prev):
                if not mask:
                    continue
                reverse = (hd + 2) & 3
                for nd, off in enumerate(self.offs):
                    if nd == reverse:
                        continue
                    shifted = ((mask << off) if off > 0 else (mask >> -off)) & walk & ~seen[nd]
                    if shifted & self.home:
                        return depth
                    cur[nd] |= shifted
            if not any(cur):
                break
            for d in range(4):
                seen[d] |= cur[d]
            prev = cur
        return 999

    def _calc_roam_level(self):
        near_cfg = ROAM_CFG["near"]
        mid_cfg = ROAM_CFG["mid"]
        far_cfg = ROAM_CFG["far"]
        min_dist = 999
        my_bit = 1 << self.start
        for layers, dl, wing, ex, ey in self.enemy_bfs:
            d = self.dist_to(my_bit, layers)
            if d != 999:
                min_dist = min(min_dist, d)
        if min_dist < near_cfg["dist_near"]:
            level, cfg = "near", near_cfg
        elif min_dist < mid_cfg["dist_mid"]:
            level, cfg = "mid", mid_cfg
        else:
            level, cfg = "far", far_cfg
        self.roam_level = level
        self.roam_min_dist = min_dist
        return cfg

    def _target_field(self, raw):
        mask = 0
        cands = []
        all_item_bits = 0
        for _, _, _, cells, _, _ in raw:
            for p in cells:
                all_item_bits |= 1 << p
        cluster4 = self.expand(self.expand(self.expand(self.expand(all_item_bits))))

        for kind, spawn, val, cells, is_2x2, _ in raw:
            self.check_budget()
            bp, bb = None, 0.0
            for p in cells:
                bit = 1 << p
                st = self.dist_to(bit, self.my_bfs)
                if st == 999:
                    continue
                arr = max(1, spawn, self.step_turn(st))
                if kind == "saber" and arr + self.saber_delay > self.remaining:
                    continue
                if arr >= self.remaining:
                    continue
                foe = self.danger(p)
                if arr <= foe + 2:
                    back = self.dist_to(bit, self.distance)
                    if back != 999 and self.step_turn(st + back) <= self.remaining:
                        rf = 1.25 if arr < foe else (1.0 if arr <= foe else 0.72)
                        sc = val * rf / (1.6 + arr * 0.38)
                        if self.wing > 0:
                            sc *= BOOST_OUT_BONUS if not (bit & self.home) else BOOST_IN_PENALTY
                        if is_2x2:
                            sc *= 1.15
                        nearby = (cluster4 & all_item_bits & ~bit).bit_count()
                        sc += 0.08 * min(nearby, 4)
                        if sc > bb:
                            bb, bp = sc, p
            if bp is not None:
                cands.append((bb, bp))
        for c in self.enemy_trails:
            st = self.dist_to(1 << c, self.my_bfs)
            if st != 999:
                arr = max(1, self.step_turn(st))
                if arr <= 12 and arr <= self.danger(c) + 1:
                    cands.append((10.0 / (1.5 + arr * 0.45), c))
        if self.target_land:
            t = self.target_land
            n = 0
            while t and n < 6:
                b = t & -t
                t ^= b
                n += 1
                cands.append((14.0, b.bit_length() - 1))
        if cands:
            cands.sort(reverse=True)
            for _, p in cands[:5]:
                mask |= 1 << p
            return self.dist_layers(mask & self.move_free, self.move_free, 34)
        return None


def _close_score(b, gain, stolen, reward, when, margin, force_home, turns=0, narrow=False, trail_cnt=0):
    risk = max(0, 2 - margin)
    sc = (gain + (1.6 if b.attack else 0.8) * stolen + reward) / (1.8 + when * 0.78)
    sc *= 1 / (1 + 0.72 * risk)
    sc -= 0.95 * risk
    if gain > 0:
        sc += 0.35 * min(3.0, gain / max(1, when))
    if b.opening and margin >= 3:
        sc += 0.19 * min(gain, 36)
    elif not b.opening and margin >= 4:
        sc += 0.12 * min(gain, 32)
    if b.trail:
        if force_home:
            sc += 2.0 / when - 2.5 * (when - 1)
        elif margin < 4:
            sc += (2.0 if margin <= 2 else 1.0) / when
    if turns > 0:
        sc -= 0.055 * turns
    # Chong chu L / dai hep 2 o + thuong vong tron/vuong (compactness)
    if narrow and not force_home and margin >= 3 and reward <= 1.0:
        sc -= NARROW_PENALTY
    elif trail_cnt >= 4 and gain > trail_cnt:
        compact = gain / max(1.0, (trail_cnt / 3.0) ** 2)
        if compact < COMPACT_MIN and not force_home and margin >= 3 and reward <= 1.0:
            sc -= 0.65
        else:
            sc += COMPACT_W * min(compact, 1.5)
    return sc


def emergency(b, pos, heading, stop):
    q = deque([(pos, heading, (), 0)])
    seen = {(pos, heading)}
    walk = b.move_free & ~b.trail
    while q and perf_counter() < stop:
        p, hd, first, depth = q.popleft()
        for s, d in b.nbrs(p, hd, walk):
            bit = 1 << s
            when = b.step_turn(depth + 1)
            if when > b.remaining or (when == 1 and bit & b.enemy_cells):
                continue
            if bit & b.home:
                mv = first + (d,) if when == 1 else first
                if len(mv) < 2 or not _slash_kills(b, pos, mv):
                    return mv
                continue
            key = (s, d)
            if key not in seen:
                seen.add(key)
                mv = first + (d,) if when == 1 else first
                q.append((s, d, mv, depth + 1))
    return ()


def _slash_kills(b, start, first):
    p = start
    for d in first[:2]:
        p += b.offs[d]
        bit = 1 << p
        r = p // b.stride - 1
        if b.slashes.get(r, 999) <= 1:
            return True
        if bit & b.enemy_cells:
            return True
    return False


def _is_zigzag(prev_hd, cur_hd, pprev_hd):
    if pprev_hd < 0 or prev_hd < 0 or cur_hd < 0:
        return False
    return pprev_hd == cur_hd and prev_hd != cur_hd and prev_hd != (cur_hd + 2) % 4


def _slash_kills_path(b, trail, when):
    t = trail
    while t:
        bb = t & -t
        t ^= bb
        if b.slashes.get((bb.bit_length() - 1) // b.stride - 1, 999) < when:
            return True
    return False


def choose(b, stop):
    if b.remaining <= 0:
        return ()
    stop = min(stop, perf_counter()+max(0.0,b.cpu_deadline-process_time())-0.001)
    root_dl = b.open_deadline()
    force_home = bool(b.trail and root_dl <= 3)
    if b.trail and any(b.slashes.get(y,999)==1 for x,y in b.me.get("trail",())):
        for dst,d in b.nbrs(b.start,b.heading,b.home & b.move_free & ~b.enemy_cells & ~b.collision):
            return (d,)
    in_home_boost = bool(b.wing > 0 and not b.trail and ((1 << b.start) & b.home))
    in_home_post = bool(_MEM.get("post_boost", 0) > 0 and not b.trail and ((1 << b.start) & b.home))
    mem_dir = _MEM.get("dir", -1)

    wave = [(b.start, b.heading, b.trail, b.trail_cnt,
             b.init_mnx, b.init_mxx, b.init_mny, b.init_mxy,
             root_dl, 0, 0.0, (), b.heading, -1, 0)]
    best_score, best_move = -0.15, ()
    exits = []
    closed = {}

    # --- Phan loai cum item / 2x2 o gan (1-2 o) cho snatch & boost-aware ---
    has_wing = b.wing > 0
    foe_stunned = any(int(e.get("stun", 0) or 0) + int(e.get("freeze", 0) or 0) > 0 for e in b.enemies)
    near_cluster = False
    near_lonely_2x2 = False
    item_meta = []
    for idx_it, (kind, spawn, val, cells, is_2x2, coords) in enumerate(b.items_for_race):
        if perf_counter() >= stop - 0.008: break
        mates = 0
        for j, (_, _, _, ocells, _, ocoords) in enumerate(b.items_for_race):
            if j == idx_it:
                continue
            if min(abs(x1 - x2) + abs(y1 - y2) for x1, y1 in coords for x2, y2 in ocoords) <= SNATCH_CLUSTER_R:
                mates += 1
        is_cluster = mates >= 1
        min_st = min((b.dist_to(1 << p, b.my_bfs) for p in cells), default=999)
        if min_st <= SNATCH_DIST:
            if is_cluster:
                near_cluster = True
            elif is_2x2:
                near_lonely_2x2 = True
        item_meta.append((is_cluster, is_2x2))

    item_meta.extend([(False, False)] * (len(b.items_for_race)-len(item_meta)))

    # INSANE hunter priority: cut a nearby long rival trail while we are still at home.
    adjacent = []
    if b.trail_cnt <= 2 and not force_home:
        for s, d in b.nbrs(b.start, b.heading, b.move_free & ~b.trail):
            if b.collision & (1 << s):
                continue
            victims = b.enemy_trails.get(s, 0)
            for vi, enemy in enumerate(b.enemies):
                if victims & (1 << vi) and len(enemy.get("trail", ())) >= 4:
                    adjacent.append((len(enemy.get("trail", ())), d))
    if adjacent:
        return (max(adjacent)[1],)

    # Item choice competes with expansion on the same return-safe route score.
    item_choice = None
    skip_race = False
    if not force_home:
        cands = []
        for idx_it, (kind, spawn, val, cells, is_2x2, _) in enumerate(b.items_for_race):
            is_cluster, _ = item_meta[idx_it]
            for p in cells:
                bit = 1 << p
                st = b.dist_to(bit, b.my_bfs)
                if in_home_boost and (bit & b.home) and st > 2:
                    continue
                if st == 999:
                    continue
                arr = max(1, spawn, b.step_turn(st))
                foe = min(b.enemy_arrivals(p), default=999)
                dl = b.saber_delay if kind == "saber" else 0
                if not (arr < foe or (kind in ("wing", "hourglass") and arr <= foe)) or arr + dl > b.remaining:
                    continue
                v = val
                if kind == "wing" and b.wing >= arr + 4:
                    v *= 0.45
                # Boost-aware (fixv4): uu tien item ngoai nha & kip cua so wing
                if has_wing:
                    v *= BOOST_OUT_BONUS if not (bit & b.home) else (0.85 if st <= 2 else BOOST_IN_PENALTY)
                    v *= BOOST_IN_WINDOW if arr <= b.wing else BOOST_LATE_PENALTY
                # Snatch (fixv3): cum/2x2 cach 1-2 o -> an nhanh; cum->wing, 2x2 don->hourglass
                if st <= SNATCH_DIST:
                    if is_2x2:
                        v *= SNATCH_2X2_BONUS
                    if is_cluster:
                        v *= SNATCH_CLUSTER_BONUS
                if st <= SNATCH_DIST + 2:
                    if kind == "wing" and near_cluster:
                        v *= SNATCH_WING_BONUS
                    if kind == "hourglass" and near_lonely_2x2:
                        v *= SNATCH_FREEZE_BONUS
                cands.append((v / (2 + arr * 0.85), kind, spawn, p, st, foe, v))
        cands.sort(reverse=True)
        seen_it = set()
        sel = []
        for c in cands:
            _, kind, spawn, p, _, _, _ = c
            ids = {i for i, t, _, n in b.item_cells[p] if t == spawn and n == kind}
            if ids and ids <= seen_it:
                continue
            seen_it.update(ids)
            sel.append(c)
            if len(sel) == 5:
                break
        t_now = perf_counter()
        t_stop = min(stop - 0.007, t_now + min(0.013,max(0.004,(stop-t_now)*0.5)))
        for ci, cnd in enumerate(sel):
            if perf_counter() >= t_stop:
                break
            try:
                r = _route_item(b, wave[0], cnd, t_stop, now=perf_counter(),
                                budget=(t_stop - perf_counter()) / min(2, len(sel) - ci))
            except BudgetEnd:
                break
            if r is None:
                continue
            sc, mv = r
            # Prioritize a genuinely short, return-safe item detour. A small
            # discount on a large hypothetical territory gain is not enough.
            if cnd[4] <= 3 and cnd[1] != "bomb" and cnd[2] <= 1:
                sc += 2.0
            if mv and (item_choice is None or sc > item_choice[0]):
                item_choice = (sc, mv)

    roam = b.roam
    _beam_w = roam["beam_width"]
    _cnt_w = roam["cnt_w"]
    _back_w = roam["back_w"]
    _cl_bonus = roam["close_bonus"]
    _pull_sc = roam["pull_scale"]
    _md_cap = roam["max_depth_open"] if b.opening else roam["max_depth_late"]
    max_depth = min(_md_cap + min(b.wing, b.remaining), b.remaining + min(b.wing, b.remaining))
    if not force_home and b.roam_min_dist>=18 and b.remaining>=45 and b.free_count>=800:
        max_depth=min(max_depth+12,b.remaining+min(b.wing,b.remaining),b.trail_limit+4)
        _beam_w=min(_beam_w,32)
    if force_home:
        max_depth = min(max_depth, 12)
    search_stop = stop - 0.006
    pull_boost = 1.4 if (has_wing or foe_stunned) else 1.0

    for depth in range(1, max_depth + 1):
        if perf_counter() >= search_stop:
            break
        when = b.step_turn(depth)
        pool, visited = [], {}
        for node in wave:
            if perf_counter() >= search_stop: break
            (pos, hd, trail, cnt, mnx, mxx, mny, mxy, dl, marks, rw, first, prev_hd, pprev_hd, turns) = node
            for s, d in b.nbrs(pos, hd, b.move_free & ~trail):
                bit = 1 << s
                nw_first = first + (d,) if when == 1 else first
                nrw, nmarks = rw, marks
                if when == 1 and bit & b.enemy_cells:
                    continue
                if when == 1 and bit & b.collision:
                    nrw -= 7.0
                tg = b.enemy_trails.get(s, 0) & ~nmarks
                if tg:
                    nrw += b.break_bonus * 0.8 / when ** 1.5
                    nmarks |= tg

                is_turn = (d != hd and hd >= 0)
                is_zz = _is_zigzag(hd, d, prev_hd)
                has_item_here = bool(b.item_cells.get(s))
                is_enemy_trail_here = bool(b.enemy_trails.get(s, 0))
                if is_turn:
                    nrw -= 0.24
                    if is_zz and not has_item_here and not is_enemy_trail_here:
                        nrw -= 0.75

                nturns = turns + (1 if is_turn else 0)
                n_prev_hd = hd
                n_pprev_hd = prev_hd

                for iid, appear, v, kind in b.item_cells.get(s, ()):
                    if kind == "saber" and when + b.saber_delay > b.remaining:
                        continue
                    fl = 1 << (iid + 8)
                    if _pickup_possible(b, appear, depth) and not nmarks & fl:
                        nrw += v / (1 + 0.70 * (when - 1))
                        nmarks |= fl

                ntrail, ncnt = trail, cnt
                nmnx, nmxx, nmny, nmxy = mnx, mxx, mny, mxy
                ndl = dl
                if not bit & b.home:
                    ntrail |= bit
                    ncnt += 1
                    if ncnt > b.trail_limit:
                        continue
                    row, col = divmod(s, b.stride)
                    cx, cy = col - 1, row - 1
                    nmnx, nmxx = min(mnx, cx), max(mxx, cx)
                    nmny, nmxy = min(mny, cy), max(mxy, cy)
                    ndl = min(dl, b.danger(s))
                    if ndl <= when:
                        continue
                else:
                    if ntrail and _slash_kills_path(b, trail, when):
                        continue
                if depth == 1:
                    exits.append((s, d, nrw, nw_first))
                if bit & b.home and ntrail:
                    margin = ndl - when
                    wb = max(0, nmxx - nmnx - 1)
                    hb = max(0, nmxy - nmny - 1)
                    interior = min((wb * hb) // 2, (ncnt * ncnt) // 6)
                    narrow = (ncnt >= 4 and min(nmxx - nmnx, nmxy - nmny) <= 1)
                    approx = _close_score(b, ncnt + interior, 0, nrw, when, margin, force_home,
                                          nturns, narrow, ncnt)
                    pr = closed.get(ntrail)
                    if pr is None or approx > pr[0]:
                        closed[ntrail] = (approx, when, nw_first, nrw, ndl, nturns)
                    continue
                if not ntrail:
                    fr = b.dist_to(bit, b.frontier)
                    if in_home_boost:
                        cur_fr = b.dist_to(1 << pos, b.frontier)
                        if fr > cur_fr:
                            continue
                        pri = nrw * 0.1 + 2.0 - 2.0 * min(fr, 24)
                    else:
                        dt = b.dist_to(bit, b.target_layers) if b.target_layers is not None else 999
                        dc = b.dist_to(bit, b.center_layers) if b.center_layers is not None else 999
                        walk_pen = 0.14 if in_home_post else 0.08
                        if fr != 999:
                            sc = (0.55 + nrw) / (1 + when) - walk_pen * fr
                            if dt != 999 and not in_home_post:
                                sc += 0.28 / (1 + dt)
                            if dc != 999:
                                sc += SSS_WEIGHT * 0.85 / (1 + 0.3 * dc)
                            if nw_first and mem_dir >= 0 and nw_first[0] == mem_dir:
                                sc += 0.27
                            if sc > best_score:
                                best_score, best_move = sc, nw_first
                        g = fr if in_home_post else (min(dt, dc) if (dt != 999 or dc != 999) else fr)
                        pri = nrw + 1.4 - 0.55 * min(g, 24) - (0.35 if in_home_post else 0.15) * min(fr, 12)
                        if dc != 999:
                            pri += SSS_WEIGHT * 1.4 / (1 + 0.35 * dc)
                else:
                    back = b.dist_to(bit, b.distance)
                    if back == 999 or ncnt+back-1>b.trail_limit or b.step_turn(depth + back) > b.remaining:
                        continue
                    margin = ndl - b.step_turn(depth + back)
                    dt = b.dist_to(bit, b.target_layers) if b.target_layers is not None and margin >= 4 else 999
                    pull = _pull_sc * pull_boost * 0.9 / (1 + dt) if dt != 999 else 0.0
                    pri = ncnt * _cnt_w + nrw * 0.4 + pull - _back_w * back - 1.7 * max(0, 2 - margin)
                    if b.opportunity is not None and margin>=3:
                        od=b.dist_to(bit,b.opportunity)
                        if od<999: pri+=(0.32 if b.distributed_cluster else 0.22)*max(-5,min(12,b.opp_home-od))
                    if ncnt >= 4 and min(nmxx - nmnx, nmxy - nmny) <= 1 and margin >= 4 and nrw <= 1.0:
                        pri -= 0.55
                    if b.center_layers is not None and margin >= 3:
                        dc = b.dist_to(bit, b.center_layers)
                        if dc != 999:
                            pri += SSS_WEIGHT * 2.2 / (1 + 0.3 * dc)
                key = (s, d, nw_first[0] if nw_first else -1, ntrail)
                if key not in visited or pri > visited[key]:
                    visited[key] = pri
                    pool.append((pri, key, (s, d, ntrail, ncnt, nmnx, nmxx, nmny, nmxy,
                                           ndl, nmarks, nrw, nw_first,
                                           n_prev_hd, n_pprev_hd, nturns)))
        if not pool:
            break
        pool.sort(key=lambda e: e[0], reverse=True)
        wave = []
        for pri, key, node in pool:
            if key in visited and pri == visited[key]:
                del visited[key]
                wave.append(node)
                if len(wave) == _beam_w:
                    break
    if closed and perf_counter() < stop:
        ranked = sorted(((v[0], v[1], v[2], v[3], v[4], v[5], t)
                         for t, v in closed.items()), key=lambda x: x[0], reverse=True)
        firsts=set(); diverse=[]; rest=[]
        for entry in ranked:
            k=entry[2]
            if k not in firsts:
                firsts.add(k); diverse.append(entry)
            else: rest.append(entry)
        ranked=diverse+rest
        for i, entry in enumerate(ranked):
            if i >= 18 or perf_counter() >= stop:
                break
            approx, when, first, nrw, ndl, nturns, trail = entry
            try:
                gain, stolen, open_after = b.captured(trail) if trail else (0, 0, b.free_count)
            except BudgetEnd:
                break
            tcnt = trail.bit_count() if trail else 0
            # Existing enclosed holes will be filled by any closure; reward
            # new territory rather than repeatedly returning to tiny pockets.
            if trail and b.outside is not None:
                old_holes=(b.free & ~b.home & ~b.outside).bit_count()
                gain=max(tcnt,gain-max(0,old_holes-2))
                stolen=max(0,stolen-(b.stolen_land & ~b.outside & ~b.home).bit_count())
            margin = ndl - when
            narrow = (tcnt >= 4 and gain <= tcnt + 1)
            sc = _close_score(b, gain, stolen, nrw, when, margin, force_home,
                              nturns, narrow, tcnt)
            if (not force_home and margin >= 5 and b.remaining > when + 8
                    and tcnt <= 2 and gain <= tcnt + 1
                    and open_after > max(16, b.free_count // 10)):
                sc -= 5.0 if b.roam_min_dist >= 12 else 3.0
            if gain:
                sc += 0.3 * min(2.0, gain / max(1, len(first)))
            sc += _cl_bonus * min(gain, 40) * 0.01
            if b.center_layers is not None and trail:
                min_dc = 999
                tc = trail
                while tc:
                    bb = tc & -tc
                    tc ^= bb
                    d_c = b.dist_to(bb, b.center_layers)
                    if d_c < min_dc:
                        min_dc = d_c
                if min_dc < b.start_center_dist:
                    sc += SSS_WEIGHT * (1.8 * (b.start_center_dist - min_dc) / max(1, when) + 1.0 / (1 + 0.25 * min_dc))
            if b.opportunity is not None and trail and margin>=3 and not force_home:
                od=b.dist_to(trail,b.opportunity)
                if od<999:
                    progress=max(0,b.opp_home-od)
                    if b.distributed_cluster:
                        sc+=min(4.5,1.6*progress/max(2,when)+0.24*progress)
                    else:
                        sc+=min(2.6,1.25*progress/max(2,when)+0.12*progress)
            if first and mem_dir >= 0 and first[0] == mem_dir:
                sc += 0.27
            if sc > best_score:
                t = trail
                dl = 999
                while t:
                    bb = t & -t
                    t ^= bb
                    dl = min(dl, b.danger(bb.bit_length() - 1))
                margin = dl - when
                if margin >= 1 or force_home:
                    best_score, best_move = sc, first
    if item_choice is not None and item_choice[0] > best_score:
        return item_choice[1]
    if best_move:
        return best_move
    if in_home_boost and wave:
        out_nodes = [n for n in wave if n[2] and n[11]]
        if out_nodes:
            return max(out_nodes, key=lambda n: (n[8], n[10]))[11]
    if b.remaining == 1:
        prof = [(rw, f) for _, _, rw, f in exits if rw > 0]
        return max(prof)[1] if prof else ()
    if b.trail:
        homeward = emergency(b, b.start, b.heading, stop)
        if homeward:
            return homeward
        legal = [(b.dist_to(1 << s, b.distance), -b.danger(s), f)
                 for s, _, _, f in exits if not b.collision & (1 << s)]
        if legal:
            return min(legal)[2]
        if not exits:
            for _, d in b.nbrs(b.start, b.heading, b.move_free & ~b.enemy_cells & ~b.collision):
                return (d,)
    if exits:
        if not b.trail:
            return min(exits, key=lambda e: (b.dist_to(1 << e[0], b.frontier), -b.danger(e[0])))[3]
        return min(exits, key=lambda e: (b.dist_to(1 << e[0], b.distance), -b.danger(e[0])))[3]
    for _, d in b.nbrs(b.start, b.heading, b.move_free):
        return (d,)
    return ()


def _pickup_possible(b, spawn, depth):
    when = b.step_turn(depth)
    # Existing items can be picked on either substep; new items spawn after both.
    return spawn < when or (spawn == when and b.step_turn(depth+1) != when)


def _safe_item_return(b, goal, heading, trail, pk, wing, deadline, stop):
    if not trail:
        return pk, trail, 999
    # Search only a bounded number of candidate return routes. A route is
    # accepted only if the actual cells remain safe until it closes.
    limit = min(b.trail_limit-trail.bit_count()+1, 60)
    if limit <= 0:
        return None
    d0=b.dist_to(1<<goal,b.distance)
    if d0>limit:
        return None
    q=[(d0,0,goal,heading,trail,deadline)]
    seen=set()
    visits=0
    while q and visits<180:
        visits+=1
        if perf_counter()>=stop:
            return None
        _,n,pos,hd,tr,dl=heappop(q)
        when=pk+_turns(n+1,wing)
        for dst,nd in b.nbrs(pos,hd,b.move_free&~tr):
            bit=1<<dst
            if bit&b.home:
                if when<=b.remaining and dl-when>=2:
                    return when,tr,dl-when
                continue
            if n+1>=limit or when>=b.remaining:
                continue
            nt=tr|bit
            left=b.dist_to(bit,b.distance)
            if n+1+left>limit:
                continue
            ndl=min(dl,b.danger(dst))
            if ndl-pk-_turns(n+1+left,wing)<2:
                continue
            key=(dst,nd,nt)
            if key not in seen:
                seen.add(key)
                heappush(q,(n+1+left,n+1,dst,nd,nt,ndl))
    return None


def _route_item(b, root, cnd, stop, now, budget):
    stop = min(stop, perf_counter() + max(0.001, budget))
    _, kind, spawn, goal, est, foe, val = cnd
    if not ((1<<goal)&b.move_free): return None
    dl = min(foe - 1 if foe != 999 else 999, b.remaining - (b.saber_delay if kind == "saber" else 0))
    if max(1, spawn) > dl:
        return None
    start_pos, start_hd, start_trail = root[0], root[1], root[2]
    roll = b.dist_layers(1 << goal, b.move_free, min(48, est + 12))
    wave = [(start_pos, start_hd, start_trail, root[8], ())]
    max_steps = min(46, est + 12, dl + min(b.wing, dl if dl != 999 else 0))

    item_bonus_bits = 0
    for p in b.item_cells:
        if p != goal:
            item_bonus_bits |= 1 << p

    for depth in range(1, max_steps + 1):
        if not wave or perf_counter() >= stop:
            break
        when = b.step_turn(depth)
        queue, picks = [], []
        for pos, hd, trail, dln, first in wave:
            for s, d in b.nbrs(pos, hd, b.move_free & ~trail):
                if b.dist_to(1 << s, roll) == 999 or b.step_turn(depth + b.dist_to(1 << s, roll)) > dl:
                    continue
                bit = 1 << s
                if when == 1 and bit & (b.enemy_cells | b.collision):
                    continue
                nf = first + (d,) if when == 1 else first
                if bit & b.home:
                    ntrail, ndl = 0, 999
                else:
                    ndl = min(dln, b.danger(s))
                    if ndl <= when:
                        continue
                    ntrail = trail | bit
                    if ntrail.bit_count() > b.trail_limit:
                        continue
                side_bonus = 0.0
                if bit & item_bonus_bits:
                    for _, appear, v, _ in b.item_cells.get(s, ()):
                        if _pickup_possible(b, appear, depth):
                            side_bonus += v / (1 + 0.50 * (when - 1))
                if s == goal and _pickup_possible(b, spawn, depth):
                    pk = when
                    if pk <= dl and (bit & b.home or ndl > pk):
                        grade = min(10, ndl - pk) - 0.12 * ntrail.bit_count() if not bit & b.home else 10
                        grade += side_bonus
                        picks.append((grade, nf, pk, ntrail, ndl, d, side_bonus))
                    continue
                back = b.dist_to(bit, roll)
                pri = -back - 0.06 * (ntrail.bit_count() if ntrail else 0) + 0.10 * min(6, ndl - when)
                pri += 0.15 * side_bonus
                queue.append((pri, (s, d, ntrail, ndl, nf)))
        if picks:
            picks.sort(reverse=True)
            best = None
            for grade, first, pk, ntrail, trail_deadline, final_hd, side_bonus in picks:
                if perf_counter() >= stop:
                    break
                wing_after = max(0, b.wing - pk)
                if kind == "wing":
                    wing_after = max(wing_after, b.wing_turns)
                if ntrail:
                    ret = _safe_item_return(b, goal, final_hd, ntrail, pk, wing_after, trail_deadline, stop)
                    if ret is None:
                        continue
                    when_home, complete_trail, margin = ret
                    try:
                        gain, stolen, _ = b.captured(complete_trail)
                    except BudgetEnd:
                        return best
                    sc = _close_score(b, gain, stolen, val + side_bonus,
                                      when_home, margin, False,
                                      trail_cnt=complete_trail.bit_count())
                else:
                    sc = (val + side_bonus) / (1.8 + pk * 0.78)
                if best is None or sc > best[0]:
                    best = (sc, first)
            if best is not None:
                return best
        queue.sort(reverse=True)
        seen = set()
        nw = []
        for _, n in queue:
            k = (n[0], n[1], n[4][0] if n[4] else -1)
            if k not in seen:
                seen.add(k)
                nw.append(n)
                if len(nw) == 9:
                    break
        wave = nw
    return None


def _alarm_handler(signum, frame):
    raise BudgetEnd


def decide(state):
    global _LAST_REASON
    me = next((p for p in state.get("players", []) if p.get("playerId") == ME), None)
    if me is None:
        _LAST_REASON = "player-missing"
        return None
    if me.get("stun", 0) or me.get("freeze", 0):
        _MEM["dir"] = -1
        _LAST_REASON = "stun/freeze"
        return None
    started, cpu_start = perf_counter(), process_time()
    fallback = quick_move(state, me)
    stop = started+0.030
    alarm = False
    try:
        if hasattr(signal, "setitimer"):
            try:
                signal.signal(signal.SIGALRM, _alarm_handler)
                alarm = True
                signal.setitimer(signal.ITIMER_REAL, max(0.0001,started+0.032-perf_counter()))
            except (ValueError,OSError):
                alarm = False
        return _decide_search(state, fallback, stop, cpu_start+0.024)
    except BudgetEnd:
        _LAST_REASON = "budget-fallback"
        return fallback
    finally:
        if alarm:
            try:
                signal.setitimer(signal.ITIMER_REAL, 0)
            except (BudgetEnd, ValueError, OSError):
                pass


def _decide_search(state, fallback, stop, cpu_stop):
    global _LAST_REASON
    b = Board(state, stop, cpu_stop)
    if _MEM.get("game") != GAME:
        _MEM["game"] = GAME
        _MEM["dir"] = -1
        _MEM["prev_wing"] = 0
        _MEM["post_boost"] = 0

    # Theo doi post-boost (khi wing vua het -> uu tien tao hai trinh moi)
    if _MEM["prev_wing"] > 0 and b.wing == 0:
        _MEM["post_boost"] = POST_BOOST_TURNS
    elif _MEM["post_boost"] > 0:
        _MEM["post_boost"] = 0 if b.trail_cnt > 0 else _MEM["post_boost"] - 1
    _MEM["prev_wing"] = b.wing

    _LAST_ROAM["level"] = b.roam_level
    _LAST_ROAM["dist"] = b.roam_min_dist
    _LAST_ROAM["boost"] = "%d/%d" % (b.wing, _MEM["post_boost"])

    if b.trail_cnt == 0:
        _MEM["dir"] = -1

    # Recheck the quick action against the full core after board construction.
    legal = {d for _,d in b.nbrs(b.start,b.heading,b.move_free & ~b.trail & ~b.enemy_cells)}
    if legal and (fallback not in DID or DID[fallback] not in legal):
        fallback=DIRS[min(legal)]
    mv = choose(b, stop)
    if not mv:
        _MEM["dir"] = -1
        _LAST_REASON = "fallback" if fallback else "no-legal-move"
        return fallback
    _LAST_REASON = "planned"

    legal = {d for _, d in b.nbrs(b.start, b.heading, b.move_free & ~b.trail & ~b.enemy_cells)}
    if mv[0] not in legal:
        _LAST_REASON = "invalid-plan-fallback" if fallback else "no-legal-move"
        return fallback
    _MEM["dir"] = mv[0]
    if len(mv) >= 2 and b.wing > 0:
        first_pos = b.start+b.offs[mv[0]]
        second_pos = first_pos+b.offs[mv[1]]
        trail_after = 0 if (1<<first_pos)&b.home else b.trail|(1<<first_pos)
        if not ((1<<second_pos)&b.move_free&~trail_after&~b.enemy_cells):
            return DIRS[mv[0]]
        out = [DIRS[mv[0]], DIRS[mv[1]]]
        if _slash_kills(b, b.start, mv[:2]):
            return DIRS[mv[0]]
        opp = (mv[0] + 2) % 4
        if mv[1] == opp:
            return DIRS[mv[0]]
        return out
    return DIRS[mv[0]]


def _get(path, timeout=5):
    with urlopen(API + "/game/" + GAME + path, timeout=timeout) as r:
        return json.load(r)


def _act(body, timeout=5):
    req = Request(API + "/game/" + GAME + "/player/" + ME + "/move",
                  data=json.dumps(body).encode(),
                  headers={"Content-Type": "application/json", "x-player-token": TOKEN}, method="POST")
    try:
        with urlopen(req, timeout=timeout) as r:
            raw = r.read()
        data = json.loads(raw.decode("utf-8")) if raw else {}
        return True, data.get("turn")
    except Exception as e:
        print("Lenh bi tu choi:", repr(e), flush=True)
        return False, None


def main():
    print("INSANE-V3 Hybrid V43 bat dau", ME, GAME, STAGE, flush=True)
    last = -1
    while True:
        try:
            st = _get("/status")
            if st.get("status") == "finished":
                print("Tran ket thuc", st.get("currentTurn"), flush=True)
                return
            tick = int(st.get("tickInterval") or 500)
            turn = st.get("currentTurn")
            if st.get("status") == "playing" and turn is not None and turn != last:
                state = _get("/state")
                if int(state.get("turn", -1)) != int(turn):
                    sleep(0.01)
                    continue
                state["tickInterval"] = tick
                t0 = perf_counter()
                c0 = process_time()
                cmd = decide(state)
                dt = (perf_counter() - t0) * 1000
                cpu_ms = (process_time() - c0) * 1000
                # Recheck after planning: a tick may have advanced during a long
                # decision. Never send an old move into the next tick's queue.
                fresh = _get("/status", timeout=1.2)
                if fresh.get("status") != "playing" or int(fresh.get("currentTurn", -2)) != int(turn):
                    print("missed", turn, "stale-state", "%.1fms" % dt, flush=True)
                    last = int(turn)
                    continue
                last = int(turn)
                ok, accepted_turn = True, None
                if isinstance(cmd, list):
                    ok, accepted_turn = _act({"directions": cmd})
                elif isinstance(cmd, str):
                    ok, accepted_turn = _act({"direction": cmd})
                # If the server accepted the action for a later turn because a
                # tick raced the POST, that queued action already covers it.
                # Skip that turn instead of submitting a duplicate.
                if accepted_turn is not None:
                    last = max(last, int(accepted_turn) - 1)
                reason = _LAST_REASON
                print("luot", last, cmd, "%.1fms" % dt,
                      "| roam=%s dist=%s boost=%s reason=%s sent=%s accepted=%s cpu=%.1fms" %
                      (_LAST_ROAM["level"], _LAST_ROAM["dist"], _LAST_ROAM["boost"], reason, ok, accepted_turn, cpu_ms),
                      flush=True)
            sleep(min(0.15, max(0.015, tick / 12000)))
        except Exception as e:
            print("Loi:", repr(e), flush=True)
            sleep(0.05)


if __name__ == "__main__":
    main()
