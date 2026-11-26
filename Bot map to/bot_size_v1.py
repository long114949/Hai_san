# Bot Chiếm lãnh thổ - bản hoàn thiện (Python 3.12, chỉ dùng thư viện chuẩn)
# Biến môi trường do hệ thống đặt: API_URL, GAME_ID, PLAYER_ID, PLAYER_TOKEN.
#
# Kiến trúc (theo tài liệu chiến thuật): mỗi lượt tính lại từ state, chọn CẢ MỘT KẾ HOẠCH
# đến lúc về nhà rồi chỉ gửi 1 bước (2 bước nếu đang có Động cơ tăng tốc).
#   1. BFS: đường về nhà, "thời gian tới" của từng đối thủ, thời điểm họ khép vòng.
#   2. Flood Fill: ước lượng số ô sẽ chiếm (ô đối thủ nhân trọng số wEnemy).
#   3. Slack: (thời gian đối thủ nhanh nhất tới đường vẽ) - (thời điểm mình khép vòng) >= margin.
#   4. Kế hoạch: vòng chữ nhật từ ô mép lãnh thổ, đi nhặt vật phẩm, đi cắt đường vẽ đối thủ.
#   5. Điểm kế hoạch = (ô chiếm + giá trị vật phẩm + giá trị cắt) / (thời gian + 1).
#   6. Ba phong cách (An toàn / Cân bằng / Tấn công) và tự chuyển chế độ theo thế trận.

import json
import os
import random
import time
import urllib.error
import urllib.request
from collections import deque

API = os.environ["API_URL"]
GAME = os.environ["GAME_ID"]
ME = os.environ["PLAYER_ID"]
TOKEN = os.environ["PLAYER_TOKEN"]

# ===================== THAM SỐ =====================
FIXED_MODE = "expand"  # bản chuyên cho map có khối đá lớn ở giữa: chỉ tập trung mở rộng
SAFE_MID = False       # tự chuyển sang An toàn giữa trận khi dẫn xa? (mô phỏng cho thấy làm chậm đất)
SEARCH_FRAC = 0.30     # thời gian tìm kế hoạch tối đa = 30% tickInterval
MAX_STARTS = 8         # số ô mép lãnh thổ (gần tàu nhất) thử làm điểm xuất phát
FAR_STARTS = 2         # thêm bấy nhiêu ô mép ở phía xa tàu địch nhất
TOP_LOOPS = 12         # số vòng chữ nhật được tính chính xác mỗi lượt (map lớn nên Flood Fill tốn hơn)
STEP_A = 2             # chỉ thử cạnh đi ra là bội của STEP_A (vòng to nên không cần thử từng ô)
STEP_B = 3             # chỉ thử cạnh ngang là bội của STEP_B
NEAR_REAL = 6          # địch cách <= bấy nhiêu bước thì tính đúng thời gian, xa hơn thì nhân thêm hệ số delay
WAIT_MAX = 5           # ở nhà mà chưa có kế hoạch đủ an toàn: chờ tối đa bấy nhiêu lượt (margin hạ dần khi chờ)
KEEP_RATIO = 0.85      # giữ kế hoạch cũ nếu còn >= 85% điểm kế hoạch mới tốt nhất
TRAIL_RESERVE = 4      # chừa lại bấy nhiêu ô so với maxTrail
WING_VALUE = 22        # giá trị (quy ra ô) của giày tăng tốc, chưa nhân itemCoef
ITEM_MARGIN_BONUS = 2  # đi nhặt vật phẩm được phép dùng margin thấp hơn bấy nhiêu lượt (2 = chỉ cần slack >= 0 ở chế độ Cân bằng)
ITEM_PLANS = 5         # số vật phẩm thử lập kế hoạch riêng mỗi lượt

MODES = {
    # Map nhiều đá ngầm, các căn cứ cách nhau xa: không đánh nhau, chỉ mở rộng nhanh bằng vòng to.
    # delay > 1: coi như địch ở xa sẽ không lao thẳng tới đường vẽ của mình (giảm nhịp độ phòng thủ).
    "expand": dict(maxOut=26, maxSide=40, margin=1, wEnemy=1.3, leaderBoost=1.0, hunt=5,
                   cutVal=12, itemCoef=1.0, itemRad=14, avoid=True, delay=1.8),
    "safe": dict(delay=1.0, maxOut=5, maxSide=8, margin=3, wEnemy=1.3, leaderBoost=1.0, hunt=2,
                 cutVal=12, itemCoef=1.0, itemRad=10, avoid=True),
    "bal": dict(delay=1.0, maxOut=8, maxSide=10, margin=2, wEnemy=1.8, leaderBoost=1.0, hunt=7,
                cutVal=16, itemCoef=1.6, itemRad=18, avoid=True),
    "atk": dict(delay=1.0, maxOut=11, maxSide=13, margin=1, wEnemy=2.6, leaderBoost=1.6, hunt=14,
                cutVal=22, itemCoef=2.2, itemRad=26, avoid=False),
}

DIRS = {"up": (0, -1), "right": (1, 0), "down": (0, 1), "left": (-1, 0)}
DNAMES = ["up", "right", "down", "left"]
OPP = {"up": "down", "down": "up", "left": "right", "right": "left"}
PERP = {"up": ("left", "right"), "down": ("left", "right"),
        "left": ("up", "down"), "right": ("up", "down")}
INF = 10 ** 6

MEMO = {"plan": None, "expect": None, "extra": 0.0, "cut": None, "wait": 0, "tick": 500,
        "wing_off": 0, "sent2": False, "prevpos": None, "errs": 0, "mode": "bal"}


# ===================== GỌI API =====================
def get(path):
    with urllib.request.urlopen(f"{API}/game/{GAME}{path}", timeout=5) as res:
        return json.load(res)


def act(action, body=None):
    req = urllib.request.Request(
        f"{API}/game/{GAME}/player/{ME}/{action}",
        data=json.dumps(body or {}).encode(),
        headers={"Content-Type": "application/json", "x-player-token": TOKEN},
        method="POST",
    )
    try:
        urllib.request.urlopen(req, timeout=5).close()
        return True
    except urllib.error.HTTPError as err:
        print("Lệnh", action, "bị từ chối:", err.code, err.read().decode(), flush=True)
        return False


# ===================== HÌNH HỌC LƯỚI =====================
_GEO = {}


def geo(W, H):
    g = _GEO.get((W, H))
    if g:
        return g
    N = W * H
    XS = [i % W for i in range(N)]
    YS = [i // W for i in range(N)]
    NB = [[] for _ in range(N)]
    STEP = {}
    for i in range(N):
        for d in DNAMES:
            dx, dy = DIRS[d]
            nx, ny = XS[i] + dx, YS[i] + dy
            if 0 <= nx < W and 0 <= ny < H:
                j = ny * W + nx
                NB[i].append((j, d))
                STEP[(i, j)] = d
    NBI = [[j for j, _ in nb] for nb in NB]
    g = (XS, YS, NB, NBI, STEP)
    _GEO[(W, H)] = g
    return g


def xy(c):
    if isinstance(c, dict):
        return int(c["x"]), int(c["y"])
    return int(c[0]), int(c[1])


def stime(steps, wing):
    """Số lượt cần để đi `steps` ô khi còn `wing` lượt tăng tốc (2 ô/lượt)"""
    if wing > 0:
        if steps <= 2 * wing:
            return (steps + 1) // 2
        return wing + (steps - 2 * wing)
    return steps


# ===================== BỘ NÃO =====================
class Brain:
    def __init__(self, state, memo):
        self.t0 = time.time()
        self.memo = memo
        W = self.W = state["width"]
        H = self.H = state["height"]
        N = self.N = W * H
        self.XS, self.YS, self.NB, self.NBI, self.STEP = geo(W, H)
        rules = state.get("rules") or {}
        self.maxTrail = rules.get("maxTrail", 120)
        self.stunTurns = rules.get("stunTurns", 10)
        self.turn = state.get("turn", state.get("currentTurn", 0)) or 0
        cfg = state.get("config") or {}
        self.maxTurns = cfg.get("maxTurns")
        self.remaining = (self.maxTurns - self.turn) if self.maxTurns else 10 ** 6
        tick = memo.get("tick") or 500
        self.deadline = self.t0 + SEARCH_FRAC * tick / 1000.0

        # --- bản đồ ---
        own = [-1] * N
        obs = bytearray(N)
        for y, row in enumerate(state["owner"]):
            for x, ch in enumerate(row):
                if ch == ".":
                    continue
                if ch.isdigit():
                    own[y * W + x] = int(ch)
                else:
                    obs[y * W + x] = 1
        for o in state.get("obstacles") or []:
            try:
                ox, oy = xy(o)
                obs[oy * W + ox] = 1
            except Exception:
                pass
        self.own, self.obs = own, obs

        # --- người chơi ---
        me = None
        opps = []
        for p in state["players"]:
            if p["playerId"] == ME:
                me = p
            else:
                opps.append(p)
        self.me = me
        if me is None:
            return
        self.my_idx = me["index"]
        self.mine = bytearray(1 if own[i] == self.my_idx else 0 for i in range(N))
        self.pos = me["y"] * W + me["x"]
        self.lastdir = me.get("lastDir") if me.get("lastDir") in OPP else None
        self.mytrail = []
        for c in me.get("trail") or []:
            try:
                cx, cy = xy(c)
                self.mytrail.append(cy * W + cx)
            except Exception:
                pass
        self.mytrail_set = set(self.mytrail)
        self.in_home = bool(self.mine[self.pos])

        self.opps = []
        for p in opps:
            tr = []
            for c in p.get("trail") or []:
                try:
                    cx, cy = xy(c)
                    tr.append(cy * W + cx)
                except Exception:
                    pass
            self.opps.append(dict(index=p["index"], id=p["playerId"], pos=p["y"] * W + p["x"],
                                  trail=tr, stun=p.get("stun", 0), freeze=p.get("freeze", 0),
                                  wing=p.get("wing", 0), area=p.get("area", 0),
                                  score=p.get("score", 0)))
        self.heads = {o["pos"] for o in self.opps}
        self.etrail = {}
        for k, o in enumerate(self.opps):
            for c in o["trail"]:
                self.etrail[c] = k

        # tăng tốc: chỉ dùng 2 bước/lượt khi server cho phép (có wing và chưa bị tắt)
        self.wing = me.get("wing", 0) if memo.get("wing_off", 0) <= 0 else 0
        L = 400
        w = self.wing
        self.ST = [0] + [((i + 1) // 2 if i <= 2 * w else w + (i - 2 * w)) if w > 0 else i
                         for i in range(1, L + 1)]

        # --- pendingSlashes của đối thủ ---
        self.slashes = []
        for s in state.get("pendingSlashes") or []:
            try:
                if s.get("by") == ME:
                    continue
                rows = set()
                for r in s.get("rows") or []:
                    rows.add(int(r["y"]) if isinstance(r, dict) else int(r))
                self.slashes.append((int(s.get("turn", 0)) - self.turn, rows))
            except Exception:
                pass

        self.state_items = state.get("items") or []
        self.state_upcoming = state.get("upcomingItems") or []
        self.my_score = me.get("score", 0)
        self.my_area = me.get("area", 0)

    # ---------- chọn chế độ ----------
    def choose_mode(self):
        name = FIXED_MODE
        if name is None:
            N = self.N
            frac = (self.turn / self.maxTurns) if self.maxTurns else 0.5
            top = max((o["score"] for o in self.opps), default=0)
            diff = self.my_score - top
            if frac < 0.12:
                name = "bal"
            elif frac >= 0.8:
                name = "safe" if diff > 0 else ("atk" if diff < -0.03 * N else "bal")
            else:
                name = "safe" if (SAFE_MID and diff > 0.08 * N) else ("atk" if diff < -0.06 * N else "bal")
        self.mode_name = name
        self.mode = MODES[name]
        self.memo["mode"] = name

    # ---------- BFS ----------
    def bfs(self, src, passable, ban=None):
        N = self.N
        NB = self.NB
        dist = [INF] * N
        par = [-1] * N
        dist[src] = 0
        q = deque([src])
        while q:
            c = q.popleft()
            dc = dist[c] + 1
            for j, d in NB[c]:
                if dist[j] != INF or not passable[j]:
                    continue
                if c == src and ban is not None and d == ban:
                    continue
                dist[j] = dc
                par[j] = c
                q.append(j)
        return dist, par

    def path_from(self, par, target, src):
        p = []
        c = target
        while c != src:
            p.append(c)
            c = par[c]
            if c < 0:
                return None
        p.reverse()
        return p

    def enemy_fields(self):
        """Với mỗi đối thủ: thời gian tới từng ô (đã cộng choáng/đóng băng) và thời điểm khép vòng"""
        N = self.N
        NBI = self.NBI
        obs = self.obs
        self.tre = []
        self.eclose = []
        for o in self.opps:
            dist = [INF] * N
            dist[o["pos"]] = 0
            q = deque([o["pos"]])
            while q:
                c = q.popleft()
                dc = dist[c] + 1
                for j in NBI[c]:
                    if dist[j] == INF and not obs[j]:
                        dist[j] = dc
                        q.append(j)
            base = o["stun"] + o["freeze"]
            w = o["wing"]
            dl = self.mode.get("delay", 1.0)
            tab = []
            for s in range(N + 2):
                t = stime(s, w)
                if dl != 1.0 and t > NEAR_REAL:
                    t = NEAR_REAL + (t - NEAR_REAL) * dl
                tab.append(base + t)
            self.tre.append([tab[d] if d < INF else INF for d in dist])
            # thời điểm họ khép vòng: BFS về lãnh thổ của họ, tránh đường vẽ của họ
            if not o["trail"]:
                self.eclose.append(0)
                continue
            blocked = set(o["trail"])
            d2 = {o["pos"]: 0}
            q = deque([o["pos"]])
            found = INF
            while q:
                c = q.popleft()
                if self.own[c] == o["index"] and c != o["pos"]:
                    found = d2[c]
                    break
                for j in NBI[c]:
                    if j not in d2 and not obs[j] and j not in blocked:
                        d2[j] = d2[c] + 1
                        q.append(j)
            self.eclose.append(base + stime(found, w) if found < INF else INF)
        self.rmin = [INF] * N
        if self.tre:
            for i in range(N):
                m = INF
                for t in self.tre:
                    if t[i] < m:
                        m = t[i]
                self.rmin[i] = m
        self.rex = {}

    def rex_of(self, ei):
        if ei not in self.rex:
            N = self.N
            others = [t for k, t in enumerate(self.tre) if k != ei]
            self.rex[ei] = [min((t[i] for t in others), default=INF) for i in range(N)]
        return self.rex[ei]

    def prepare(self):
        N = self.N
        obs = self.obs
        mine = self.mine
        # đường về nhà (tránh đường vẽ của mình)
        pas_home = bytearray(0 if (obs[i] or i in self.mytrail_set) else 1 for i in range(N))
        dh = [INF] * N
        q = deque()
        for i in range(N):
            if mine[i]:
                dh[i] = 0
                q.append(i)
        NBI = self.NBI
        while q:
            c = q.popleft()
            for j in NBI[c]:
                if dh[j] == INF and pas_home[j]:
                    dh[j] = dh[c] + 1
                    q.append(j)
        self.dh = dh
        # đường từ tàu mình tới mọi ô
        ban = OPP[self.lastdir] if self.lastdir else None
        pas_me = bytearray(pas_home)
        for h in self.heads:
            pas_me[h] = 0
        self.dme, self.dpar = self.bfs(self.pos, pas_me, ban)
        # đi bộ trong lãnh thổ
        if self.in_home:
            pas_w = bytearray(1 if (mine[i] and not obs[i]) else 0 for i in range(N))
            self.dwalk, self.wpar = self.bfs(self.pos, pas_w, ban)
        self.enemy_fields()
        self.trail_rmin = min((self.rmin[c] for c in self.mytrail), default=INF)

        # vùng nguy hiểm: ô đối thủ có thể bước vào ở lượt tới
        danger = set()
        for o in self.opps:
            danger.add(o["pos"])
            if o["stun"] + o["freeze"] > 1:
                continue
            r = 2 if o["wing"] > 0 else 1
            x0, y0 = self.XS[o["pos"]], self.YS[o["pos"]]
            for dx in range(-r, r + 1):
                for dy in range(-r, r + 1):
                    if abs(dx) + abs(dy) <= r:
                        x, y = x0 + dx, y0 + dy
                        if 0 <= x < self.W and 0 <= y < self.H:
                            danger.add(y * self.W + x)
        self.danger = danger

        # trọng số ô và tổng tích luỹ
        leader = max(self.opps, key=lambda o: o["score"])["index"] if self.opps else -9
        m = self.mode
        wgt = [0.0] * N
        for i in range(N):
            if mine[i] or obs[i]:
                continue
            o = self.own[i]
            if o < 0:
                wgt[i] = 1.0
            else:
                wgt[i] = m["wEnemy"] * (m["leaderBoost"] if o == leader else 1.0)
        self.wgt = wgt
        W, H = self.W, self.H
        PS = [0.0] * ((W + 1) * (H + 1))
        for y in range(H):
            run = 0.0
            for x in range(W):
                run += wgt[y * W + x]
                PS[(y + 1) * (W + 1) + x + 1] = PS[y * (W + 1) + x + 1] + run
        self.PS = PS

        self.prep_items()

    def rect_sum(self, x0, y0, x1, y1):
        PS = self.PS
        s = self.W + 1
        return PS[(y1 + 1) * s + x1 + 1] - PS[y0 * s + x1 + 1] - PS[(y1 + 1) * s + x0] + PS[y0 * s + x0]

    # ---------- vật phẩm ----------
    def item_value(self, typ):
        m = self.mode
        n_opp = max(1, len(self.opps))
        areas = [o["area"] for o in self.opps] or [0]
        if typ == "saber":
            v = 0.55 * 2 * self.W
        elif typ == "megabomb":
            v = 0.5 * n_opp * min(sum(areas) / len(areas), 25)
        elif typ == "hourglass":
            top = max((o["score"] for o in self.opps), default=0)
            v = 22 if top > self.my_score else 12
        elif typ == "bomb":
            v = 0.6 * min(max(areas), 16)
        elif typ == "wing":
            v = WING_VALUE
        else:
            v = 5
        return v * m["itemCoef"]

    def prep_items(self):
        W = self.W
        size = {"megabomb": 2, "saber": 2}
        self.itemblocks = []
        self.itemmap = {}
        raws = [(r, 0) for r in self.state_items] + \
               [(r, max(0, int(r.get("turn", 0)) - self.turn)) for r in self.state_upcoming
                if isinstance(r, dict)]
        for bid, (raw, avail) in enumerate(raws):
            try:
                ix, iy = xy(raw)
            except Exception:
                continue
            typ = raw.get("type") if isinstance(raw, dict) else None
            s = size.get(typ, 1)
            cells = [(iy + b) * W + (ix + a) for a in range(s) for b in range(s)
                     if 0 <= ix + a < W and 0 <= iy + b < self.H]
            if not cells:
                continue
            dist = min(self.dme[c] for c in cells)
            if dist > self.mode["itemRad"] or dist >= INF:
                continue
            val = self.item_value(typ)
            if val <= 0:
                continue
            self.itemblocks.append(dict(bid=bid, cells=cells, val=val, avail=avail, dist=dist))
            for c in cells:
                self.itemmap[c] = (val, bid, avail)

    # ---------- Flood Fill ----------
    def flood(self, trail_cells):
        """Giá trị (đã nhân trọng số) các ô sẽ thành của mình khi khép vòng, gồm cả ô đường vẽ"""
        W, H = self.W, self.H
        XS, YS = self.XS, self.YS
        xs = [XS[c] for c in trail_cells]
        ys = [YS[c] for c in trail_cells]
        x0, x1 = max(0, min(xs) - 1), min(W - 1, max(xs) + 1)
        y0, y1 = max(0, min(ys) - 1), min(H - 1, max(ys) + 1)
        wall = bytearray(self.mine)
        for c in trail_cells:
            wall[c] = 1
        vis = bytearray(self.N)
        stack = []
        for x in range(x0, x1 + 1):
            for y in (y0, y1):
                c = y * W + x
                if not wall[c] and not vis[c]:
                    vis[c] = 1
                    stack.append(c)
        for y in range(y0 + 1, y1):
            for x in (x0, x1):
                c = y * W + x
                if not wall[c] and not vis[c]:
                    vis[c] = 1
                    stack.append(c)
        NBI = self.NBI
        while stack:
            c = stack.pop()
            for j in NBI[c]:
                if vis[j] or wall[j]:
                    continue
                xj, yj = XS[j], YS[j]
                if xj < x0 or xj > x1 or yj < y0 or yj > y1:
                    continue
                vis[j] = 1
                stack.append(j)
        gain = 0.0
        wgt = self.wgt
        obs = self.obs
        for y in range(y0 + 1, y1):
            base = y * W
            for x in range(x0 + 1, x1):
                c = base + x
                if not vis[c] and not wall[c] and not obs[c]:
                    gain += wgt[c]
        # ô đường vẽ chưa thuộc mình cũng thành của mình
        gain += sum(1 for c in trail_cells if not self.mine[c])
        return gain

    # ---------- đánh giá một kế hoạch ----------
    def evaluate(self, path, kind, extra=0.0, cut=None):
        if not path:
            return None
        STEP = self.STEP
        mine, obs = self.mine, self.obs
        ST = self.ST
        rmin = self.rmin
        mts = self.mytrail_set
        prev = self.pos
        lastdir = self.lastdir
        out = not mine[prev]
        seen = set()
        newt = []
        close_i = None
        itemval = 0.0
        taken = set()
        itemmap = self.itemmap
        for i, c in enumerate(path, 1):
            d = STEP.get((prev, c))
            if d is None:
                return None
            if lastdir is not None and OPP[d] == lastdir:
                return None
            if obs[c] or c in mts:
                return None
            lastdir = d
            prev = c
            im = itemmap.get(c)
            if im is not None and im[1] not in taken:
                t = ST[i]
                if t >= im[2] and t < rmin[c]:
                    taken.add(im[1])
                    itemval += im[0]
            if mine[c]:
                if out:
                    close_i = i
                    break
            else:
                if c in seen:
                    return None
                seen.add(c)
                out = True
                newt.append((c, i))
        if close_i is None:
            if out:
                return None
            close_i = len(path)
        path = path[:close_i]
        if len(self.mytrail) + len(newt) > self.maxTrail - TRAIL_RESERVE:
            return None
        T = ST[close_i]
        if T > self.remaining - 1:
            return None
        # Đang đi bộ trong nhà (chưa lộ đường vẽ) thì không tính vào thời gian bị lộ: mỗi lượt
        # đều tính lại nên nếu địch lại gần, kế hoạch tự bị loại trước khi ta rời nhà.
        Texp = T
        if newt and not self.mytrail:
            Texp = T - max(0, ST[newt[0][1]] - 1)
        first = path[0]
        if first in self.heads:
            return None
        if self.mode["avoid"] and first in self.danger and first not in self.etrail:
            return None

        cells = self.mytrail + [c for c, _ in newt]
        slack = 99
        if cells:
            r = INF
            if cut is None:
                for c in cells:
                    if rmin[c] < r:
                        r = rmin[c]
            else:
                ei, tcut = cut
                rex = self.rex_of(ei)
                tre = self.tre[ei]
                st = self.stunTurns
                for c in cells:
                    a = rex[c]
                    b = tre[c]
                    if b > tcut:
                        b += st
                    m = a if a < b else b
                    if m < r:
                        r = m
            slack = r - Texp if r < INF else 99
        # đợt quét (saber) của đối thủ
        if self.slashes and cells:
            YS = self.YS
            laid = [(c, 0) for c in self.mytrail] + [(c, ST[i]) for c, i in newt]
            for ts, rows in self.slashes:
                if ts < 0:
                    continue
                for c, t0 in laid:
                    if YS[c] in rows and t0 <= ts <= T:
                        return None
        gain = self.flood(cells) if cells else 0.0  # cells gồm cả đường vẽ đã có: khép vòng ngay vẫn được tính
        score = (gain + itemval + extra) / (T + 1.0)
        return dict(path=path, score=score, slack=slack, T=T, gain=gain, item=itemval,
                    kind=kind, extra=extra, cut=cut)

    # ---------- đường quay về ----------
    def descend(self, cur, blocked, target, lastdir):
        """Từ ô cur (ngoài lãnh thổ) đi về nhà theo trường khoảng cách dh, hướng về ô target"""
        dh, NB, mine, XS, YS = self.dh, self.NB, self.mine, self.XS, self.YS
        tx, ty = XS[target], YS[target]
        path = []
        blocked = set(blocked)
        while not mine[cur]:
            if dh[cur] >= INF:
                return None
            best = None
            for j, d in NB[cur]:
                if dh[j] == dh[cur] - 1 and j not in blocked:
                    if lastdir is not None and OPP[d] == lastdir:
                        continue
                    key = abs(XS[j] - tx) + abs(YS[j] - ty)
                    if best is None or key < best[0]:
                        best = (key, j, d)
            if best is None:
                return self.return_bfs(cur, blocked, lastdir, path)
            path.append(best[1])
            blocked.add(best[1])
            lastdir = best[2]
            cur = best[1]
            if len(path) > 250:
                return None
        return path

    def return_bfs(self, cur, blocked, lastdir, head):
        """Dự phòng: trường dh không còn đường (bị chính kế hoạch chặn) thì BFS tránh các ô đã dùng"""
        mine, obs, mts, NB = self.mine, self.obs, self.mytrail_set, self.NB
        prev = {cur: None}
        q = deque([cur])
        while q:
            c = q.popleft()
            if c != cur and mine[c]:
                p = []
                while c != cur:
                    p.append(c)
                    c = prev[c]
                return head + p[::-1]
            for j, d in NB[c]:
                if j in prev or obs[j] or j in mts or j in blocked:
                    continue
                if c == cur and lastdir is not None and OPP[d] == lastdir:
                    continue
                prev[j] = c
                q.append(j)
        return None

    # ---------- các nguồn kế hoạch ----------
    def home_plans(self, plans):
        """Đang ngoài khơi: về nhà ngay (tới vài ô lãnh thổ khác nhau)"""
        if self.in_home:
            return
        cand = [(self.dme[c], c) for c in range(self.N) if self.mine[c] and self.dme[c] < INF]
        cand.sort()
        used = set()
        for d, c in cand[:60]:
            p = self.path_from(self.dpar, c, self.pos)
            if not p:
                continue
            key = (p[0], len(p))
            if p[0] in used:
                continue
            used.add(p[0])
            ev = self.evaluate(p, "home")
            if ev:
                plans.append(ev)
            if len(used) >= 3:
                break

    def starts(self):
        if not self.in_home:
            return [(self.pos, [])]
        N = self.N
        dw = self.dwalk
        mine, obs, NBI = self.mine, self.obs, self.NBI
        border = []
        for c in range(N):
            if dw[c] < INF and mine[c]:
                for j in NBI[c]:
                    if not mine[j] and not obs[j]:
                        border.append(c)
                        break
        random.shuffle(border)
        border.sort(key=lambda c: dw[c])
        XS, YS = self.XS, self.YS
        chosen = []
        for c in border:
            if all(abs(XS[c] - XS[k]) + abs(YS[c] - YS[k]) >= 3 for k in chosen):
                chosen.append(c)
                if len(chosen) >= MAX_STARTS:
                    break
        # thêm vài điểm xuất phát Ở PHÍA XA địch nhất: gần địch thì đi bộ sang đó thay vì đứng chờ
        if self.opps:
            far = sorted(border, key=lambda c: -min(self.rmin[c], 60))
            added = 0
            for c in far:
                if all(abs(XS[c] - XS[k]) + abs(YS[c] - YS[k]) >= 3 for k in chosen):
                    chosen.append(c)
                    added += 1
                    if added >= FAR_STARTS:
                        break
        out = []
        for c in chosen:
            out.append((c, self.path_from(self.wpar, c, self.pos) or []))
        return out

    def gen_loops(self, plans):
        W, H, N = self.W, self.H, self.N
        XS, YS, STEP = self.XS, self.YS, self.STEP
        obs, mine, rmin, dh = self.obs, self.mine, self.rmin, self.dh
        mts = self.mytrail_set
        itemmap = self.itemmap
        m = self.mode
        margin = self.margin_eff
        maxOut, maxSide = m["maxOut"], m["maxSide"]
        remaining = self.remaining
        ntrail = len(self.mytrail)
        relaxed = self.memo["wait"] >= WAIT_MAX  # chờ đủ lâu: ép mở rộng, chọn vòng ít nguy hiểm nhất
        pre_slack = -10 ** 6 if relaxed else margin - 1
        cands = []
        for s, walk in self.starts():
            if time.time() > self.deadline:
                break
            d0 = len(walk)
            sx, sy = XS[s], YS[s]
            if walk:
                prevcell = walk[-2] if len(walk) >= 2 else self.pos
                wdir = STEP.get((prevcell, walk[-1]))
            else:
                wdir = self.lastdir
            for dn in DNAMES:
                if wdir is not None and OPP[dn] == wdir:
                    continue
                dx, dy = DIRS[dn]
                x, y = sx, sy
                rm1 = self.trail_rmin
                ib1 = 0.0
                for a in range(1, maxOut + 1):
                    x += dx
                    y += dy
                    if not (0 <= x < W and 0 <= y < H):
                        break
                    c = y * W + x
                    if obs[c] or c in mts or mine[c]:
                        break
                    if rmin[c] < rm1:
                        rm1 = rmin[c]
                    im = itemmap.get(c)
                    if im is not None and a < rmin[c] + 1:
                        ib1 += im[0]
                    if a != 1 and (a < 2 or (a % STEP_A and a != maxOut)):
                        continue
                    for pn in PERP[dn]:
                        px, py = DIRS[pn]
                        x2, y2 = x, y
                        rm2 = rm1
                        ib2 = ib1
                        for b in range(1, maxSide + 1):
                            x2 += px
                            y2 += py
                            if not (0 <= x2 < W and 0 <= y2 < H):
                                break
                            c2 = y2 * W + x2
                            if obs[c2] or c2 in mts or mine[c2]:
                                break
                            if rmin[c2] < rm2:
                                rm2 = rmin[c2]
                            im2 = itemmap.get(c2)
                            if im2 is not None and a + b < rmin[c2] + 1:
                                ib2 += im2[0]
                            if b < 2 or (b % STEP_B and b != maxSide):
                                continue
                            ret = dh[c2]
                            if ret >= INF:
                                continue
                            Te = d0 + a + b + ret
                            if Te >= remaining - 1:
                                continue
                            if ntrail + a + b + ret > self.maxTrail - TRAIL_RESERVE:
                                continue
                            if rm2 - (Te - max(0, d0 - 1) if not ntrail else Te) < pre_slack:
                                continue
                            area = self.rect_sum(min(sx, x2), min(sy, y2), max(sx, x2), max(sy, y2))
                            risk = 1.0
                            if relaxed:
                                risk = max(0.15, min(1.0, 1.0 + (rm2 - Te) / (Te + 1.0)))
                            cands.append(((area + ib2) / (Te + 1.0) * risk * random.uniform(0.95, 1.05),
                                          s, walk, dn, a, pn, b))
        cands.sort(key=lambda t: -t[0])
        valid = 0
        for est, s, walk, dn, a, pn, b in cands[:TOP_LOOPS * 6]:
            if time.time() > self.deadline or valid >= TOP_LOOPS:
                break
            path = list(walk)
            cur = s
            dx, dy = DIRS[dn]
            px, py = DIRS[pn]
            leg = []
            x, y = XS[s], YS[s]
            for _ in range(a):
                x += dx
                y += dy
                leg.append(y * W + x)
            for _ in range(b):
                x += px
                y += py
                leg.append(y * W + x)
            ldir = pn
            ret = self.descend(leg[-1], set(leg), s, ldir)
            if ret is None:
                continue
            path += leg + ret
            ev = self.evaluate(path, "loop")
            if ev:
                plans.append(ev)
                valid += 1

    def item_plans(self, plans):
        blocks = sorted(self.itemblocks, key=lambda b: -b["val"] / (b["dist"] + 3.0))[:ITEM_PLANS]
        for b in blocks:
            if time.time() > self.deadline:
                break
            c = min(b["cells"], key=lambda k: self.dme[k])
            p1 = self.path_from(self.dpar, c, self.pos)
            if not p1:
                continue
            if not self.mine[c]:
                ret = self.descend(c, set(p1), self.pos, self.STEP.get((p1[-2] if len(p1) > 1 else self.pos, c)))
                if ret is None:
                    continue
                p1 = p1 + ret
            ev = self.evaluate(p1, "item")
            if ev:
                plans.append(ev)

    def cut_plans(self, plans):
        m = self.mode
        cands = []
        for c, ei in self.etrail.items():
            d = self.dme[c]
            if d > m["hunt"] or d >= INF or c in self.heads:
                continue
            if self.ST[d] >= self.eclose[ei]:
                continue  # tới nơi thì họ đã khép vòng
            cands.append((d, c, ei))
        cands.sort()
        for d, c, ei in cands[:4]:
            if time.time() > self.deadline:
                break
            p1 = self.path_from(self.dpar, c, self.pos)
            if not p1:
                continue
            last = self.STEP.get((p1[-2] if len(p1) > 1 else self.pos, c))
            ret = self.descend(c, set(p1), self.pos, last) if not self.mine[c] else []
            if ret is None:
                continue
            ev = self.evaluate(p1 + ret, "cut", extra=m["cutVal"], cut=(ei, self.ST[len(p1)]))
            if ev:
                plans.append(ev)

    def adjacent_cut(self):
        """Luật luôn bật: đường vẽ đối thủ cách đúng 1 bước và bước đó an toàn thì cắt ngay"""
        if len(self.mytrail) >= self.maxTrail - 2:
            return None
        for j, d in self.NB[self.pos]:
            if j not in self.etrail or j in self.heads or self.obs[j] or j in self.mytrail_set:
                continue
            if self.lastdir is not None and OPP[d] == self.lastdir:
                continue
            ei = self.etrail[j]
            if self.eclose[ei] < 1:
                continue
            return j
        return None

    def old_plan(self, plans):
        m = self.memo
        pl = m.get("plan")
        if pl and m.get("expect") == self.pos:
            cut = m.get("cut")
            ev = self.evaluate(list(pl), "old", extra=m.get("extra", 0.0), cut=cut)
            if ev:
                plans.append(ev)

    # ---------- quyết định ----------
    def think(self):
        t_start = time.time()
        m = self.memo
        if m.get("sent2") and m.get("prevpos") == self.pos and m.get("exp2") is not None \
                and self.pos != m["exp2"]:
            m["wing_off"] = 30
            self.wing = 0
            print("Lệnh 2 bước không chạy, tắt đi 2 ô trong 30 lượt", flush=True)
        m["sent2"] = False
        if m.get("wing_off", 0) > 0:
            m["wing_off"] -= 1
        self.choose_mode()
        self.prepare()
        self.margin_eff = max(0, self.mode["margin"] - m["wait"] // 2)

        j = self.adjacent_cut()
        if j is not None:
            return self.emit([j], dict(kind="cut1", score=0, slack=0, T=1), t_start)

        plans = []
        self.old_plan(plans)
        old = plans[0] if plans else None
        self.home_plans(plans)
        self.cut_plans(plans)
        self.item_plans(plans)
        self.gen_loops(plans)

        good = [p for p in plans if p["slack"] >= self.margin_eff - (ITEM_MARGIN_BONUS if p["item"] > 0 else 0)]
        best = None
        if good:
            best = max(good, key=lambda p: p["score"])
            if old and old in good and old["score"] >= KEEP_RATIO * best["score"]:
                best = old
            m["wait"] = 0
        else:
            if self.in_home:
                # Chưa có vòng nào đủ an toàn: vẫn ĐI BỘ TRONG NHÀ tới ô xuất phát tốt nhất (đi trong nhà
                # không bị cắt), chỉ đứng chờ khi bước kế tiếp là rời khỏi lãnh thổ.
                cand = max(plans, key=lambda p: (p["slack"], p["score"])) if plans else None
                if cand is None:
                    sts = self.starts()
                    if sts and sts[0][1]:
                        return self.emit(sts[0][1], dict(kind="approach", score=0, slack=-9, T=len(sts[0][1])),
                                         t_start, single=True)
                elif self.mine[cand["path"][0]]:
                    return self.emit(cand["path"], dict(kind="approach", score=cand["score"], slack=cand["slack"],
                                                         T=cand["T"]), t_start, single=True)
            if self.in_home and m["wait"] < WAIT_MAX:
                m["wait"] += 1  # tính cả khi không còn kế hoạch nào (bị lọc hết)
                m["plan"] = None
                why = "chưa đủ an toàn" if plans else "mọi vòng đều bị địch chặn"
                print(f"L{self.turn} chờ ({m['wait']}/{WAIT_MAX}): {why}", flush=True)
                return ("stay",)
            if plans:
                best = max(plans, key=lambda p: p["score"] * max(0.15, min(1.0, 1.0 + p["slack"] / (p["T"] + 1.0))))
            elif self.in_home and m["wait"] >= WAIT_MAX:
                m["wait"] = WAIT_MAX  # vẫn giữ chế độ nới: lượt sau sinh vòng với bộ lọc rộng
                return self.fallback(t_start)
            else:
                m["wait"] = 0
        if best is None:
            return self.fallback(t_start)
        if self.in_home and best["kind"] == "home":
            pass
        return self.emit(best["path"], best, t_start)

    def fallback(self, t_start):
        """Không có kế hoạch hợp lệ: đi một bước an toàn về phía nhà, nếu không có thì đứng yên"""
        best = None
        for j, d in self.NB[self.pos]:
            if self.obs[j] or j in self.mytrail_set or j in self.heads:
                continue
            if self.lastdir is not None and OPP[d] == self.lastdir:
                continue
            if self.mode["avoid"] and j in self.danger and j not in self.etrail:
                continue
            key = (0 if self.mine[j] else 1, self.dh[j])
            if best is None or key < best[0]:
                best = (key, j)
        if best is None or self.in_home:
            self.memo["plan"] = None
            return ("stay",)
        return self.emit([best[1]], dict(kind="fallback", score=0, slack=-9, T=1), t_start)

    def emit(self, path, info, t_start, single=False):
        m = self.memo
        pos = self.pos
        steps = [path[0]]
        two = False
        if self.wing > 0 and len(path) >= 2 and not single:
            c1 = path[1]
            if c1 not in self.danger and c1 not in self.heads:
                steps.append(c1)
                two = True
        dirs = []
        prev = pos
        for c in steps:
            dirs.append(self.STEP[(prev, c)])
            prev = c
        k = len(steps)
        m["plan"] = path[k:] or None
        m["expect"] = path[k - 1]
        m["extra"] = info.get("extra", 0.0) if isinstance(info, dict) else 0.0
        cut = info.get("cut") if isinstance(info, dict) else None
        m["cut"] = (cut[0], max(0, cut[1] - k)) if cut else None
        m["sent2"] = two
        m["prevpos"] = pos
        m["exp2"] = path[k - 1]
        ms = (time.time() - t_start) * 1000
        print(f"L{self.turn} {self.mode_name} {info.get('kind')} diem={info.get('score', 0):.1f} "
              f"slack={info.get('slack')} T={info.get('T')} {ms:.0f}ms", flush=True)
        return ("move", dirs)


def _decide(state):
    b = Brain(state, MEMO)
    if b.me is None or b.me.get("stun", 0) > 0 or b.me.get("freeze", 0) > 0:
        MEMO["plan"] = None
        return None
    return b.think()


def decide(state):
    """Trả về None (không gửi lệnh), ("stay",) hoặc ("move", [hướng, ...])"""
    try:
        return _decide(state)
    except Exception as err:
        MEMO["errs"] += 1
        if MEMO["errs"] <= 5:
            print("Lỗi decide:", repr(err), flush=True)
        MEMO["plan"] = None
        return ("stay",)


def main():
    print("Bot", ME, "bắt đầu trận", GAME, flush=True)
    last_turn = -1
    tries = 0
    while True:
        try:
            status = get("/status")
            if status["status"] == "finished":
                print("Trận đã kết thúc ở lượt", status["currentTurn"], flush=True)
                return
            MEMO["tick"] = status.get("tickInterval") or 500
            if status["status"] == "playing" and status["currentTurn"] != last_turn:
                res = decide(get("/state"))
                ok = True
                if res is not None:
                    if res[0] == "stay":
                        ok = act("stay")
                    else:
                        dirs = res[1]
                        body = {"direction": dirs[0]} if len(dirs) == 1 else {"directions": dirs}
                        ok = act("move", body)
                tries += 1
                if ok or tries >= 3:
                    last_turn = status["currentTurn"]
                    tries = 0
            time.sleep(min(0.25, max(0.05, MEMO["tick"] / 4000)))
        except Exception as err:
            print("Lỗi:", err, flush=True)
            time.sleep(1)


if __name__ == "__main__":
    main()
