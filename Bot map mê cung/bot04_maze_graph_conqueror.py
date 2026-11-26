# Python 3.12 | stdlib only | single-file tournament bot
import json
import os
import time
import math
import heapq
import urllib.error
import urllib.request
from collections import deque
API = os.environ.get('API_URL', '')
GAME = os.environ.get('GAME_ID', '')
ME = os.environ.get('PLAYER_ID', '')
TOKEN = os.environ.get('PLAYER_TOKEN', '')
DIRS = ((0, -1, 'up'), (1, 0, 'right'), (0, 1, 'down'), (-1, 0, 'left'))
OPP = {'up': 'down', 'down': 'up', 'left': 'right', 'right': 'left'}
DELTA = {d: (dx, dy) for dx, dy, d in DIRS}
ITEM_SIZE = {'bomb': 1, 'wing': 1, 'hourglass': 1, 'megabomb': 2, 'saber': 2}
INF = 10 ** 9
PLAN = None
LAST_NO_MOVE = -1
FRONTIER_TARGET = None
FRONTIER_HISTORY = deque(maxlen=12)
RECENT_POSITIONS = deque(maxlen=24)
LAST_AREA = -1
NO_CAPTURE_TURNS = 0
OWN_DIST_SIGNATURE = None
OWN_DIST_CACHE = None
OWN_DIST_SOURCES = None
DECISION_DEADLINE = 0.0
BLOCKED_CACHE_KEY = None
BLOCKED_CACHE = None
def decision_budget_over():
  return DECISION_DEADLINE > 0.0 and time.perf_counter() >= DECISION_DEADLINE
def get(path):
  t0=time.perf_counter()
  with urllib.request.urlopen(API+'/game/'+GAME+path,timeout=0.8) as r: data=json.load(r)
  ms=(time.perf_counter()-t0)*1000
  if ms>=80: print('API GET',path,'-',round(ms),'ms',flush=True)
  return data
def act(action, body=None):
  req=urllib.request.Request(API+'/game/'+GAME+'/player/'+ME+'/'+action,data=json.dumps(body or {}).encode(),headers={'Content-Type':'application/json','x-player-token':TOKEN},method='POST')
  t0=time.perf_counter()
  try:
    with urllib.request.urlopen(req,timeout=0.8) as r: r.read()
    ms=(time.perf_counter()-t0)*1000
    if ms>=80: print('API',action,'-',round(ms),'ms',flush=True)
  except urllib.error.HTTPError as e: print('Move rejected',e.code,e.read().decode(errors='replace'),flush=True)
def turns_for_steps(steps, wing):
  steps = max(0, int(steps))
  wing = max(0, int(wing or 0))
  boosted = min(steps, 2 * wing)
  return (boosted + 1) // 2 + steps - boosted
def build_context(s):
  w, h = (int(s['width']), int(s['height']))
  n = w * h
  players = s.get('players', [])
  me = next((p for p in players if p.get('playerId') == ME), None)
  if me is None:
    return None
  grid = [-1] * n
  for y, row in enumerate(s.get('owner', [])):
    base = y * w
    if isinstance(row, str):
      for x, ch in enumerate(row[:w]):
        code = ord(ch) - 48
        if 0 <= code <= 9:
          grid[base + x] = code
    else:
      for x, value in enumerate(row[:w]):
        if isinstance(value, int):
          grid[base + x] = value
  global BLOCKED_CACHE_KEY, BLOCKED_CACHE
  if BLOCKED_CACHE is None or BLOCKED_CACHE_KEY != (w, h):
    blocked = bytearray(n)
    for ob in s.get('obstacles', []):
      if isinstance(ob, dict):
        x0, y0 = int(ob['x']), int(ob['y'])
        ow = int(ob['w']) if 'w' in ob else 1
        oh = int(ob['h']) if 'h' in ob else 1
      elif isinstance(ob, (list, tuple)) and len(ob) >= 2:
        x0, y0, ow, oh = int(ob[0]), int(ob[1]), 1, 1
      else:
        continue
      for y in range(max(0, y0), min(h, y0 + max(1, oh))):
        row_base = y * w
        for x in range(max(0, x0), min(w, x0 + max(1, ow))):
          blocked[row_base + x] = 1
    BLOCKED_CACHE_KEY = (w, h)
    BLOCKED_CACHE = bytes(blocked)
  blocked = BLOCKED_CACHE
  me_idx = int(me.get('index', 0))
  others = [p for p in players if p.get('index') != me_idx]
  my_trail = set()
  for xy in me.get('trail', []):
    if len(xy) >= 2:
      x, y = (int(xy[0]), int(xy[1]))
      if 0 <= x < w and 0 <= y < h:
        my_trail.add(y * w + x)
  enemy_trail = {}
  occupied = set()
  for p in others:
    x, y = (int(p.get('x', -1)), int(p.get('y', -1)))
    if 0 <= x < w and 0 <= y < h:
      occupied.add(y * w + x)
    for xy in p.get('trail', []):
      if len(xy) >= 2:
        tx, ty = (int(xy[0]), int(xy[1]))
        if 0 <= tx < w and 0 <= ty < h:
          enemy_trail[ty * w + tx] = p
  counts = [0] * max(4, len(players))
  for owner in grid:
    if 0 <= owner < len(counts):
      counts[owner] += 1
  rules = s.get('rules') or {}
  cfg = s.get('config') or {}
  turn = int(s.get('turn', 0))
  max_turns = int(cfg.get('maxTurns', 600))
  start = int(me.get('y', 0)) * w + int(me.get('x', 0))
  return {'s': s, 'w': w, 'h': h, 'n': n, 'grid': grid, 'blocked': blocked, 'me': me, 'meidx': me_idx, 'others': others, 'mytrail': my_trail, 'enemytrail': enemy_trail, 'occupied': occupied, 'counts': counts, 'rules': rules, 'turn': turn, 'remaining': max(0, max_turns - turn), 'maxturns': max_turns, 'start': start}
def neighbors(c, cell, order=0):
  w, h = (c['w'], c['h'])
  x, y = (cell % w, cell // w)
  for j in range(4):
    dx, dy, d = DIRS[j + order & 3]
    nx, ny = (x + dx, y + dy)
    if 0 <= nx < w and 0 <= ny < h:
      yield (ny * w + nx, d)
def bfs_out_tree(c, order, goal_cells=None, max_steps=INF):
  n = c['n']
  start = c['start']
  grid = c['grid']
  me = c['meidx']
  start_left = 0 if grid[start] == me else 1
  total = 2 * n
  prev = [-2] * total
  pdir = [None] * total
  dist = [-1] * total
  root = start * 2 + start_left
  prev[root] = -1
  dist[root] = 0
  q = deque([root])
  last = c['me'].get('lastDir')
  direction_order = DIRS[order:] + DIRS[:order]
  pending = set(goal_cells or ())
  visits = 0
  while q and (not goal_cells or pending):
    visits += 1
    if (visits & 7) == 0 and decision_budget_over():
      break
    z = q.popleft()
    cell, left = (z >> 1, z & 1)
    if dist[z] >= max_steps:
      continue
    nd = dist[z] + 1
    x, y = (cell % c['w'], cell // c['w'])
    for dx, dy, d in direction_order:
      nx, ny = (x + dx, y + dy)
      if nx < 0 or ny < 0 or nx >= c['w'] or ny >= c['h']:
        continue
      u = ny * c['w'] + nx
      if c['blocked'][u] or u in c['mytrail'] or u in c['occupied']:
        continue
      if z == root and last and (OPP.get(d) == last):
        continue
      is_own = grid[u] == me
      if left and is_own:
        continue
      nleft = 0 if not left and is_own else 1
      nz = u * 2 + nleft
      if prev[nz] != -2:
        continue
      prev[nz] = z
      pdir[nz] = d
      dist[nz] = nd
      q.append(nz)
      if nleft and u in pending:
        pending.discard(u)
  return (prev, pdir, dist)
def extract_out_path(tree, target):
  prev, pdir, dist = tree
  z = target * 2 + 1
  if z >= len(prev) or dist[z] <= 0:
    return None
  cells, dirs = ([], [])
  while prev[z] >= 0:
    cells.append(z >> 1)
    dirs.append(pdir[z])
    z = prev[z]
  cells.reverse()
  dirs.reverse()
  return (dirs, cells)
def fast_home_route(c, start, forbidden, order, last_dir=None, heuristic=None):
 if heuristic is not None and 0 <= start < len(heuristic):
  w, h = c['w'], c['h']
  current, previous_dir = start, last_dir
  dirs, cells = [], []
  seen = {start}
  for step_i in range(c['n']):
   if (step_i & 7) == 0 and decision_budget_over():
    return None
   if c['grid'][current] == c['meidx'] and current != start:
    return dirs, cells
   base = heuristic[current]
   if base <= 0:
    break
   best = None
   x, y = current % w, current // w
   for j in range(4):
    dx, dy, direction = DIRS[(j + order) & 3]
    if previous_dir and OPP.get(direction) == previous_dir:
     continue
    nx, ny = x + dx, y + dy
    if nx < 0 or ny < 0 or nx >= w or ny >= h:
     continue
    nxt = ny * w + nx
    if c['blocked'][nxt] or nxt in forbidden or nxt in c['occupied'] or nxt in seen:
     continue
    value = heuristic[nxt]
    if value < 0 or value >= base:
     continue
    key = (value, 0 if c['grid'][nxt] == c['meidx'] else 1, j)
    if best is None or key < best[0]:
     best = (key, nxt, direction)
   if best is None:
    break
   _, nxt, direction = best
   dirs.append(direction)
   cells.append(nxt)
   seen.add(nxt)
   current, previous_dir = nxt, direction
  if dirs and c['grid'][current] == c['meidx']:
   return dirs, cells
 return bfs_home(c, start, forbidden, order, last_dir, heuristic)
def bfs_home(c, start, forbidden, order, last_dir=None, heuristic=None):
 n, w, h = c['n'], c['w'], c['h']
 grid, blocked, occupied = c['grid'], c['blocked'], c['occupied']
 gscore = [INF] * n
 prev = [-2] * n
 pdir = [None] * n
 gscore[start] = 0
 prev[start] = -1
 h0 = heuristic[start] if heuristic is not None and heuristic[start] >= 0 else 0
 heap = [(h0, 0, start)]
 dirs = DIRS[order:] + DIRS[:order]
 goal = -1
 visits = 0
 while heap:
  visits += 1
  if (visits & 7) == 0 and decision_budget_over():
   return None
  _, cost, v = heapq.heappop(heap)
  if cost != gscore[v]:
   continue
  if grid[v] == c['meidx'] and v != start:
   goal = v
   break
  x, y = v % w, v // w
  for dx, dy, d in dirs:
   if v == start and last_dir and OPP.get(d) == last_dir:
    continue
   nx, ny = x + dx, y + dy
   if nx < 0 or ny < 0 or nx >= w or ny >= h:
    continue
   u = ny * w + nx
   if blocked[u] or u in forbidden or u in occupied:
    continue
   ng = cost + 1
   if ng >= gscore[u]:
    continue
   gscore[u] = ng
   prev[u] = v
   pdir[u] = d
   hv = heuristic[u] if heuristic is not None and heuristic[u] >= 0 else 0
   heapq.heappush(heap, (ng + hv, ng, u))
 if goal < 0:
  return None
 cells, directions = [], []
 v = goal
 while v != start:
  cells.append(v)
  directions.append(pdir[v])
  v = prev[v]
 cells.reverse()
 directions.reverse()
 return directions, cells
def multi_source_distance(c, sources, initial=None, new_sources=None):
  n, w, h = (c['n'], c['w'], c['h'])
  blocked = c['blocked']
  dmap = list(initial) if initial is not None else [-1] * n
  q = deque()
  roots = new_sources if initial is not None else sources
  for source in roots or ():
    if 0 <= source < n and not blocked[source] and dmap[source] != 0:
      dmap[source] = 0
      q.append(source)
  visits = 0
  while q:
    visits += 1
    if (visits & 7) == 0 and decision_budget_over():
      return None
    v = q.popleft()
    nd = dmap[v] + 1
    x, y = (v % w, v // w)
    if x:
      u = v - 1
      if not blocked[u] and (dmap[u] < 0 or dmap[u] > nd):
        dmap[u] = nd; q.append(u)
    if x + 1 < w:
      u = v + 1
      if not blocked[u] and (dmap[u] < 0 or dmap[u] > nd):
        dmap[u] = nd; q.append(u)
    if y:
      u = v - w
      if not blocked[u] and (dmap[u] < 0 or dmap[u] > nd):
        dmap[u] = nd; q.append(u)
    if y + 1 < h:
      u = v + w
      if not blocked[u] and (dmap[u] < 0 or dmap[u] > nd):
        dmap[u] = nd; q.append(u)
  return dmap
def enemy_distance_map(c, p, max_steps=64):
  n, w, h = (c['n'], c['w'], c['h'])
  x, y = (int(p.get('x', -1)), int(p.get('y', -1)))
  start = y * w + x
  d = [-1] * n
  if x < 0 or y < 0 or x >= w or y >= h or c['blocked'][start]:
    return d
  own_trail = set()
  for xy in p.get('trail', []):
    if len(xy) >= 2:
      tx, ty = (int(xy[0]), int(xy[1]))
      if 0 <= tx < w and 0 <= ty < h:
        own_trail.add(ty * w + tx)
  own_trail.discard(start)
  blocked = c['blocked']
  d[start] = 0
  q = deque([start])
  visits = 0
  while q:
    visits += 1
    if (visits & 7) == 0 and decision_budget_over():
      break
    v = q.popleft()
    if d[v] >= max_steps:
      continue
    nd = d[v] + 1
    x, y = (v % w, v // w)
    if x:
      u = v - 1
      if not blocked[u] and u not in own_trail and d[u] < 0:
        d[u] = nd; q.append(u)
    if x + 1 < w:
      u = v + 1
      if not blocked[u] and u not in own_trail and d[u] < 0:
        d[u] = nd; q.append(u)
    if y:
      u = v - w
      if not blocked[u] and u not in own_trail and d[u] < 0:
        d[u] = nd; q.append(u)
    if y + 1 < h:
      u = v + w
      if not blocked[u] and u not in own_trail and d[u] < 0:
        d[u] = nd; q.append(u)
  return d
def enemy_eta(c, p, dist):
  if dist < 0:
    return INF
  wait = max(int(p.get('stun', 0) or 0), int(p.get('freeze', 0) or 0))
  return wait + turns_for_steps(dist, p.get('wing', 0))
def flood_capture(c, trail):
  if decision_budget_over():
    return (0.0, 0, 0, 0)
  n, w, h = (c['n'], c['w'], c['h'])
  me, grid, blocked = (c['meidx'], c['grid'], c['blocked'])
  own_rows = [0] * h
  enemy_rows = [0] * h
  blocked_rows = [0] * h
  barrier_rows = [0] * h
  for y in range(h):
    base = y * w
    own = enemy = rocks = 0
    for x in range(w):
      v = base + x
      bit = 1 << x
      owner = grid[v]
      if owner == me:
        own |= bit
      elif owner >= 0:
        enemy |= bit
      if blocked[v]:
        rocks |= bit
    own_rows[y] = own
    enemy_rows[y] = enemy
    blocked_rows[y] = rocks
    barrier_rows[y] = own
  for v in c['mytrail']:
    barrier_rows[v // w] |= 1 << (v % w)
  for v in trail:
    barrier_rows[v // w] |= 1 << (v % w)
  full = (1 << w) - 1
  open_rows = [full ^ row for row in barrier_rows]
  outside = [0] * h
  frontier = [0] * h
  side = 1 | (1 << (w - 1)) if w > 1 else 1
  for y in range(h):
    edge = full if y == 0 or y == h - 1 else side
    seed = edge & open_rows[y]
    outside[y] = seed
    frontier[y] = seed
  while True:
    if decision_budget_over():
      return (0.0, 0, 0, 0)
    next_frontier = [0] * h
    changed = False
    for y in range(h):
      f = frontier[y]
      if not f:
        continue
      spread = ((f << 1) & full) | (f >> 1)
      if y:
        spread |= frontier[y - 1]
      if y + 1 < h:
        spread |= frontier[y + 1]
      fresh = spread & open_rows[y] & ~outside[y]
      if fresh:
        outside[y] |= fresh
        next_frontier[y] = fresh
        changed = True
    if not changed:
      break
    frontier = next_frontier
  center_bits = sum(1 << x for x in range(w) if 18 <= x <= 31)
  core_bits = sum(1 << x for x in range(w) if 22 <= x <= 27)
  gain = 0.0
  raw = center_gain = core_gain = 0
  for y in range(h):
    captured = full & ~outside[y] & ~own_rows[y] & ~blocked_rows[y]
    if not captured:
      continue
    count = captured.bit_count()
    enemies = (captured & enemy_rows[y]).bit_count()
    raw += count
    gain += count + 2.6 * enemies
    if 18 <= y <= 31:
      center = captured & center_bits
      center_count = center.bit_count()
      center_enemies = (center & enemy_rows[y]).bit_count()
      center_gain += center_count
      gain += 0.42 * (center_count + 2.5 * center_enemies)
    if 22 <= y <= 27:
      core_count = (captured & core_bits).bit_count()
      core_gain += core_count
      gain += 0.38 * core_count
  return (gain, raw, center_gain, core_gain)
def item_values(c):
  leader = max((c['counts'][p['index']] for p in c['others'] if 0 <= int(p.get('index', -1)) < len(c['counts'])), default=0)
  behind = c['counts'][c['meidx']] < leader
  w = c['w']
  return {'saber': 0.55 * int(c['rules'].get('saberRows', 2)) * w * 1.15, 'megabomb': 0.5 * len(c['others']) * min(leader, 25) * 1.2, 'hourglass': 22.0 if behind else 12.0, 'bomb': 0.6 * min(leader, 16) * 1.2, 'wing': 8.0}
def route_item_value(c, cells, close_turns):
  if not cells:
    return 0.0
  w, h = (c['w'], c['h'])
  specs = [(it, False) for it in c['s'].get('items', [])]
  specs += [(it, True) for it in c['s'].get('upcomingItems', c['s'].get('upcoming', []))]
  values = item_values(c)
  total = 0.0
  for item, upcoming in specs:
    kind = item.get('type', '')
    size = ITEM_SIZE.get(kind, 1)
    x0, y0 = (int(item.get('x', -1)), int(item.get('y', -1)))
    footprint = set()
    for dy in range(size):
      for dx in range(size):
        x, y = (x0 + dx, y0 + dy)
        if 0 <= x < w and 0 <= y < h:
          footprint.add(y * w + x)
    if not footprint:
      continue
    enemy = INF
    for p, dmap in c['enemy_maps']:
      d = min((dmap[v] for v in footprint if dmap[v] >= 0), default=-1)
      enemy = min(enemy, enemy_eta(c, p, d))
    if upcoming:
      spawn_in = max(0, int(item.get('turn', c['turn']) - c['turn']))
      moves = sum((2 if t <= int(c['me'].get('wing', 0) or 0) else 1 for t in range(1, spawn_in + 1)))
      if moves <= 0 or moves > len(cells) or spawn_in > close_turns:
        continue
      if cells[moves - 1] in footprint and enemy > spawn_in:
        total += values.get(kind, 2.0) * 0.9
    else:
      hit = next((step for step, cell in enumerate(cells, 1) if cell in footprint), None)
      if hit is None:
        continue
      arrival = turns_for_steps(hit, c['me'].get('wing', 0))
      if arrival <= close_turns and enemy > arrival:
        total += values.get(kind, 2.0)
  return total
def select_item_targets(c, tree):
  prev, pdir, dist = tree
  w, h = (c['w'], c['h'])
  wing = int(c['me'].get('wing', 0) or 0)
  specs = [(it, False) for it in c['s'].get('items', [])]
  specs += [(it, True) for it in c['s'].get('upcomingItems', c['s'].get('upcoming', []))]
  values = item_values(c)
  ranked = []
  for item, upcoming in specs:
    kind = item.get('type', '')
    size = ITEM_SIZE.get(kind, 1)
    x0, y0 = (int(item.get('x', -1)), int(item.get('y', -1)))
    footprint = [(y0 + dy) * w + x0 + dx for dy in range(size) for dx in range(size) if 0 <= x0 + dx < w and 0 <= y0 + dy < h]
    best_cell, best_ratio = (None, -1.0)
    spawn_in = max(0, int(item.get('turn', c['turn']) - c['turn'])) if upcoming else 0
    enemy = INF
    for p, dmap in c['enemy_maps']:
      d = min((dmap[v] for v in footprint if dmap[v] >= 0), default=-1)
      enemy = min(enemy, enemy_eta(c, p, d))
    for cell in footprint:
      if c['blocked'][cell] or c['grid'][cell] == c['meidx'] or cell in c['occupied'] or (cell in c['mytrail']):
        continue
      steps = dist[cell * 2 + 1]
      if steps <= 0:
        continue
      arrival = turns_for_steps(steps, wing)
      if (upcoming and arrival < spawn_in) or enemy <= arrival:
        continue
      ratio = values.get(kind, 2.0) / (arrival + 5.0)
      if ratio > best_ratio:
        best_ratio, best_cell = (ratio, cell)
    if best_cell is not None:
      ranked.append((best_ratio, best_cell, item))
  ranked.sort(reverse=True, key=lambda x: x[0])
  result, used = ([], set())
  for ratio, cell, item in ranked:
    key = (item.get('type'), item.get('x'), item.get('y'))
    if key in used:
      continue
    used.add(key)
    result.append((cell, item))
    if len(result) >= 4:
      break
  return result
def route_cut_value(c, cells):
  total = 0.0
  seen = set()
  bonus = float(c['rules'].get('breakBonus', 10))
  for cell in cells:
    p = c['enemytrail'].get(cell)
    if p is None or p.get('index') in seen:
      continue
    seen.add(p.get('index'))
    total += bonus + min(20, len(p.get('trail', []))) * 0.25
  return total
def pending_slash_eta(c, trail):
  if not trail:
    return INF
  rows = {v // c['w'] for v in trail}
  my_id = c['me'].get('playerId')
  earliest = INF
  for slash in c['s'].get('pendingSlashes', c['s'].get('slashes', [])):
    if slash.get('by') == my_id:
      continue
    r = slash.get('rows', [0, -1])
    if any((int(r[0]) <= y <= int(r[1]) for y in rows)):
      when = max(0, int(slash.get('turn', c['turn']) - c['turn']))
      earliest = min(earliest, when)
  return earliest
def pending_slash_hits(c, trail, turns):
  return pending_slash_eta(c, trail) < turns
def nearest_enemy_eta(c, cells):
  if not cells:
    return (INF, None)
  best, who = (INF, None)
  for p, dmap in c.get('enemy_maps', []):
    if decision_budget_over():
      return (0, p)
    d = -1
    for cell_i, v in enumerate(cells):
      if (cell_i & 63) == 0 and decision_budget_over():
        return (0, p)
      if 0 <= v < len(dmap) and dmap[v] >= 0 and (d < 0 or dmap[v] < d):
        d = dmap[v]
    eta = enemy_eta(c, p, d)
    if eta < best:
      best, who = (eta, p)
  return (best, who)
def attack_margin(c, enemy=None):
  margin = 3
  if enemy is not None:
    if int(enemy.get('wing', 0) or 0) > 0:
      margin = 4
    if len(enemy.get('trail', [])) >= 6:
      margin = max(margin, 4)
  if c['remaining'] <= 18 and c['counts'][c['meidx']] >= max(c['counts']):
    margin = max(margin, 4)
  return margin
def best_home_route(c):
  if not c['mytrail']:
    return None
  own_cells = []
  for v, owner in enumerate(c['grid']):
    if (v & 127) == 0 and decision_budget_over():
      return None
    if owner == c['meidx']:
      own_cells.append(v)
  if not own_cells:
    return None
  heuristic = multi_source_distance(c, own_cells)
  start = c['start']
  safe_best = None
  risky_best = None
  for order in (0, 2):
    route = bfs_home(c, start, c['mytrail'], order, c['me'].get('lastDir'), heuristic)
    if not route or not route[0]:
      continue
    dirs, cells = route
    first_count = 2 if int(c['me'].get('wing', 0) or 0) > 0 and len(dirs) > 1 else 1
    collision = immediate_enemy_collision(c, cells[:first_count], dirs[:first_count])
    eta, enemy = nearest_enemy_eta(c, set(c['mytrail']) | set(cells))
    route_turns = turns_for_steps(len(dirs), c['me'].get('wing', 0))
    exposed = set(c['mytrail']) | {v for v in cells if c['grid'][v] != c['meidx']}
    slash_risk = pending_slash_hits(c, exposed, route_turns)
    risk = 0.0 if eta >= INF else max(0.0, 4.0 - eta) * 0.35
    score = len(dirs) + risk + (1000.0 if slash_risk else 0.0)
    candidate = (score, dirs, cells, collision, eta, enemy, slash_risk)
    if collision or slash_risk:
      if risky_best is None or score < risky_best[0]:
        risky_best = candidate
    elif safe_best is None or score < safe_best[0]:
      safe_best = candidate
  best = safe_best if safe_best is not None else risky_best
  if best is None:
    return None
  return {'dirs': best[1], 'cells': best[2], 'collision': best[3], 'enemy_eta': best[4], 'enemy': best[5], 'slash_risk': best[6], 'turns': turns_for_steps(len(best[1]), c['me'].get('wing', 0)), 'heuristic': heuristic}
def possible_saber_threat(c, trail, home_turns):
  if not trail or not c.get('enemy_maps'):
    return False
  if not any(it.get('type') == 'saber' for it in c['s'].get('items', [])) and not any(it.get('type') == 'saber' for it in c['s'].get('upcomingItems', c['s'].get('upcoming', []))):
    return False
  trail_rows = {v // c['w'] for v in trail}
  if not trail_rows:
    return False
  r = min(c['h'], int(c['rules'].get('saberRows', 2) or 2))
  starts = max(1, c['h'] - r + 1)
  hit_starts = 0
  for y0 in range(c['h'] - r + 1):
    if (y0 & 7) == 0 and decision_budget_over():
      return True
    if any((y0 <= y < y0 + r for y in trail_rows)):
      hit_starts += 1
  hit_probability = hit_starts / starts
  if hit_probability < 0.18:
    return False
  tick_ms = max(1, int(c['s'].get('tickInterval', 500) or 500))
  delay = max(int(c['rules'].get('saberDelayTurns', 4) or 0), (2500 + tick_ms - 1) // tick_ms)
  items = [(it, 0) for it in c['s'].get('items', [])]
  items += [(it, max(0, int(it.get('turn', c['turn']) - c['turn']))) for it in c['s'].get('upcomingItems', c['s'].get('upcoming', []))]
  w = c['w']
  for item_i, (item, spawn_in) in enumerate(items):
    if (item_i & 3) == 0 and decision_budget_over():
      return True
    if item.get('type') != 'saber':
      continue
    x0, y0 = (int(item.get('x', -1)), int(item.get('y', -1)))
    footprint = [(y0 + dy) * w + x0 + dx for dy in range(2) for dx in range(2) if 0 <= x0 + dx < w and 0 <= y0 + dy < c['h']]
    if not footprint:
      continue
    for enemy_i, (enemy, dmap) in enumerate(c['enemy_maps']):
      if decision_budget_over():
        return True
      d = min((dmap[v] for v in footprint if dmap[v] >= 0), default=-1)
      eta = enemy_eta(c, enemy, d)
      pickup_at = max(eta, spawn_in)
      if pickup_at < INF and pickup_at + delay < home_turns:
        if hit_probability >= 0.35:
          return True
  return False
def possible_hourglass_attack(c, trail, close_turns, plan_cells=None):
  if not trail or close_turns <= 0:
    return None
  if not any(it.get('type') == 'hourglass' for it in c['s'].get('items', [])) and not any(it.get('type') == 'hourglass' for it in c['s'].get('upcomingItems', c['s'].get('upcoming', []))):
    return None
  targets = max(0, int(c['rules'].get('freezeTargets', 2) or 0))
  if targets <= 0:
    return None
  fr = c['rules'].get('freezeTurns', [10, 20])
  freeze_max = int(fr[1] if isinstance(fr, (list, tuple)) and len(fr) > 1 else fr or 20)
  if freeze_max <= 0:
    return None
  exposed = set(trail)
  w = c['w']
  items = [(it, 0, False) for it in c['s'].get('items', [])]
  items += [(it, max(0, int(it.get('turn', c['turn']) - c['turn'])), True) for it in c['s'].get('upcomingItems', c['s'].get('upcoming', []))]
  own_cells = list(plan_cells if plan_cells is not None else [])
  players = [c['me']] + c['others']
  me = c['me']
  best = None
  for item_i, (item, spawn_in, upcoming) in enumerate(items):
    if (item_i & 3) == 0 and decision_budget_over():
      return None
    if item.get('type') != 'hourglass':
      continue
    x0, y0 = (int(item.get('x', -1)), int(item.get('y', -1)))
    if not (0 <= x0 < w and 0 <= y0 < c['h']):
      continue
    cell = y0 * w + x0
    own_pick = None
    if own_cells:
      if upcoming:
        steps = sum((2 if t <= int(me.get('wing', 0) or 0) else 1 for t in range(1, spawn_in + 1)))
        if 0 < steps <= len(own_cells) and own_cells[steps - 1] == cell:
          own_pick = spawn_in
      else:
        for step, v in enumerate(own_cells, 1):
          if v == cell:
            own_pick = turns_for_steps(step, me.get('wing', 0))
            break
    for picker_i, (picker, dmap) in enumerate(c.get('enemy_maps', [])):
      if decision_budget_over():
        return best
      d = dmap[cell] if 0 <= cell < len(dmap) else -1
      pickup = max(enemy_eta(c, picker, d), spawn_in)
      if pickup >= INF or pickup >= close_turns:
        continue
      if own_pick is not None and own_pick < pickup:
        continue
      pool = [p for p in players if p.get('playerId') != picker.get('playerId')]
      pool.sort(key=lambda p: (-c['counts'][int(p.get('index', 0))], int(p.get('index', 0))))
      frozen = {p.get('playerId') for p in pool[:targets]}
      if me.get('playerId') not in frozen:
        continue
      for attacker_i, (attacker, amap) in enumerate(c.get('enemy_maps', [])):
        if decision_budget_over():
          return best
        if attacker.get('playerId') in frozen:
          continue
        d2 = min((amap[v] for v in exposed if 0 <= v < len(amap) and amap[v] >= 0), default=-1)
        eta = enemy_eta(c, attacker, d2)
        if eta <= pickup + freeze_max:
          cand = (pickup, eta, picker.get('playerId'))
          if best is None or cand < best:
            best = cand
  return best
def trail_return_danger(c, route=None):
  if not c['mytrail']:
    return (False, '', None)
  home = route or best_home_route(c)
  if home is None:
    return (True, 'no-return-path', None)
  home_turns = home['turns']
  max_trail = int(c['rules'].get('maxTrail', 120) or 120)
  if len(c['mytrail']) + max(1, len(home['dirs'])) >= max_trail - 1:
    return (True, 'trail-limit', home)
  if c['remaining'] <= home_turns + 2:
    return (True, 'endgame', home)
  escape_trail = set(c['mytrail'])
  escape_trail.update((v for v in home['cells'] if c['grid'][v] != c['meidx']))
  if pending_slash_hits(c, escape_trail, home_turns):
    return (True, 'pending-saber', home)
  if possible_saber_threat(c, escape_trail, home_turns):
    return (True, 'enemy-saber-race', home)
  if possible_hourglass_attack(c, escape_trail, home_turns, home['cells']):
    return (True, 'enemy-hourglass', home)
  eta, enemy = nearest_enemy_eta(c, c['mytrail'])
  margin = attack_margin(c, enemy)
  if eta <= home_turns + margin:
    return (True, 'enemy-cut-slack', home)
  return (False, 'safe', home)
def self_break_route(c):
  start = c['start']
  if not c['mytrail']:
    return None
  last = c['me'].get('lastDir')
  max_trail = int(c['rules'].get('maxTrail', 120) or 120)
  budget = max(0, max_trail - len(c['mytrail']) - 1)
  if budget <= 0:
    return None
  q = deque([start])
  prev = {start: None}
  pdir = {}
  depth = {start: 0}
  goal = -1
  visits = 0
  while q:
    visits += 1
    if (visits & 7) == 0 and decision_budget_over():
      return None
    v = q.popleft()
    dv = depth[v]
    if dv >= budget:
      continue
    for u, d in neighbors(c, v):
      if v == start and last and (OPP.get(d) == last):
        continue
      if c['blocked'][u] or u in c['occupied']:
        continue
      if u in prev:
        continue
      prev[u] = v
      pdir[u] = d
      depth[u] = dv + 1
      if u in c['mytrail']:
        goal = u
        q.clear()
        break
      if c['grid'][u] == c['meidx']:
        continue
      q.append(u)
  if goal < 0:
    return None
  dirs, cells = ([], [])
  v = goal
  while v != start:
    dirs.append(pdir[v])
    cells.append(v)
    v = prev[v]
  dirs.reverse()
  cells.reverse()
  return (dirs, cells)
def emergency_self_break(c):
  route = self_break_route(c)
  if not route or not route[0]:
    return None
  dirs, cells = route
  count = 1
  if int(c['me'].get('wing', 0) or 0) > 0 and len(dirs) >= 2:
    if not immediate_enemy_collision(c, cells[:2], dirs[:2]):
      count = 2
  return dirs[:count]
def immediate_enemy_collision(c, cells, dirs):
  if not cells:
    return False
  for p in c['others']:
    ex, ey = (int(p.get('x', -1)), int(p.get('y', -1)))
    if ex < 0 or ey < 0:
      continue
    pos = ey * c['w'] + ex
    reach1 = {pos}
    reach2 = {pos}
    if not p.get('stun', 0) and (not p.get('freeze', 0)):
      first = []
      last = p.get('lastDir')
      for _, _, d in DIRS:
        if last and OPP.get(d) == last:
          continue
        dx, dy = DELTA[d]
        x, y = (ex + dx, ey + dy)
        if 0 <= x < c['w'] and 0 <= y < c['h']:
          u = y * c['w'] + x
          if not c['blocked'][u]:
            reach1.add(u)
            first.append((u, d))
      reach2.update(reach1)
      if int(p.get('wing', 0) or 0) > 0:
        for u, d1 in first:
          x, y = (u % c['w'], u // c['w'])
          for _, _, d2 in DIRS:
            if OPP.get(d2) == d1:
              continue
            dx, dy = DELTA[d2]
            xx, yy = (x + dx, y + dy)
            if 0 <= xx < c['w'] and 0 <= yy < c['h']:
              v = yy * c['w'] + xx
              if not c['blocked'][v]:
                reach2.add(v)
    if cells[0] in reach1:
      return True
    if int(c['me'].get('wing', 0) or 0) > 0 and len(cells) > 1 and (cells[1] in reach2):
      return True
  return False
def select_targets(c, tree0, own_dist):
  w, h, n = (c['w'], c['h'], c['n'])
  grid, blocked, me = (c['grid'], c['blocked'], c['meidx'])
  dist = tree0[2]
  center_cells = [v for v in range(n) if not blocked[v] and 16 <= v % w <= 33 and 16 <= v // w <= 33]
  center_unclaimed = sum(1 for v in center_cells if grid[v] != me)
  early_center = center_unclaimed > max(10, int(len(center_cells) * 0.28)) and c['turn'] < int(c['maxturns'] * 0.90)
  candidates = set()
  if early_center:
    for x, y in ((24, 24), (25, 24), (24, 25), (25, 25), (23, 24), (26, 24), (24, 23), (25, 26), (21, 20), (28, 20), (21, 29), (28, 29)):
      if 0 <= x < w and 0 <= y < h:
        v = y * w + x
        if not blocked[v] and grid[v] != me:
          candidates.add(v)
    for y in range(18, min(32, h)):
      for x in range(18, min(32, w)):
        v = y * w + x
        if not blocked[v] and grid[v] != me and (dist[v * 2 + 1] > 0):
          candidates.add(v)
    mx, my = (int(c['me'].get('x', 0)), int(c['me'].get('y', 0)))
    qx = 1 if mx < w // 2 else -1
    qy = 1 if my < h // 2 else -1
    for dy in range(4, 15, 2):
      for dx in range(4, 15, 2):
        x, y = (mx + qx * dx, my + qy * dy)
        if 0 <= x < w and 0 <= y < h:
          v = y * w + x
          if not blocked[v] and grid[v] != me:
            candidates.add(v)
  else:
    tile = 8
    for y0 in range(0, h, tile):
      for x0 in range(0, w, tile):
        best = -1
        best_key = (-1, -1)
        for y in range(y0, min(h, y0 + tile)):
          for x in range(x0, min(w, x0 + tile)):
            v = y * w + x
            if blocked[v] or grid[v] == me or dist[v * 2 + 1] <= 0:
              continue
            key = (own_dist[v], 1 if grid[v] >= 0 and grid[v] != me else 0, dist[v * 2 + 1])
            if key > best_key:
              best_key, best = (key, v)
        if best >= 0:
          candidates.add(best)
    for y in range(20, 30):
      for x in range(20, 30):
        v = y * w + x
        if not blocked[v] and grid[v] != me and (dist[v * 2 + 1] > 0):
          candidates.add(v)
  valid = [v for v in candidates if 0 <= v < n and (not blocked[v]) and (grid[v] != me) and (v not in c['mytrail']) and (v not in c['occupied']) and (dist[v * 2 + 1] > 0)]
  cx, cy = ((w - 1) / 2.0, (h - 1) / 2.0)
  if early_center:
    valid.sort(key=lambda v: (-(own_dist[v] if own_dist[v] >= 0 else 0),
                             abs(v % w - cx) + abs(v // w - cy),
                             dist[v * 2 + 1]))
  else:
    valid.sort(key=lambda v: (-(own_dist[v] if own_dist[v] >= 0 else 0), -(1 if grid[v] >= 0 and grid[v] != me else 0), abs(v % w - cx) + abs(v // w - cy), dist[v * 2 + 1]))
  if early_center:
    anchors = []
    for x, y in ((25, 25), (24, 31), (25, 26), (24, 30), (25, 24), (24, 25), (25, 30), (24, 24)):
      v = y * w + x
      if v in valid and v not in anchors:
        anchors.append(v)
    rest = [v for v in valid if v not in set(anchors)]
    return ((anchors[:8] + rest[:16])[:24], early_center)
  return (valid[:24], early_center)
def plan_score(c, out_dirs, out_cells, home_dirs, home_cells, early_center, target_item=None):
  if decision_budget_over():
    return None
  me = c['me']
  dirs = out_dirs + home_dirs
  cells = out_cells + home_cells
  if not dirs or not cells:
    return None
  if me.get('lastDir') and OPP.get(dirs[0]) == me.get('lastDir'):
    return None
  for i in range(1, len(dirs)):
    if OPP.get(dirs[i]) == dirs[i - 1]:
      return None
  new_trail = {v for v in cells if c['grid'][v] != c['meidx']}
  full_trail = c['mytrail'] | new_trail
  max_trail = int(c['rules'].get('maxTrail', 120) or 120)
  if len(full_trail) > max_trail:
    return None
  total_steps = len(dirs)
  close_turns = turns_for_steps(total_steps, me.get('wing', 0))
  if close_turns + 4 > c['remaining']:
    return None
  if pending_slash_hits(c, full_trail, close_turns):
    return None
  maze_profile = c['w'] == 50 and c['h'] == 50 and 0.23 <= (sum(c['blocked']) / float(c['n'])) <= 0.28
  saber_risk = possible_saber_threat(c, full_trail, close_turns)
  if saber_risk and not maze_profile:
    return None
  hourglass_risk = possible_hourglass_attack(c, full_trail, close_turns, cells)
  if hourglass_risk is not None and (not maze_profile or hourglass_risk[0] <= 5):
    return None
  if immediate_enemy_collision(c, cells, dirs):
    return None
  nearest_eta, nearest_enemy = nearest_enemy_eta(c, full_trail)
  if nearest_eta <= 2:
    return None
  slack = nearest_eta - close_turns if nearest_eta < INF else INF
  margin = attack_margin(c, nearest_enemy)
  deficit = max(0, margin - slack) if slack < INF else 0
  risk_weight = 0.012
  if nearest_enemy and len(nearest_enemy.get('trail', [])) >= 6:
    risk_weight *= 1.55
  if nearest_enemy and int(nearest_enemy.get('wing', 0) or 0) > 0:
    risk_weight *= 1.35
  risk_penalty = min(2.5, deficit * risk_weight)
  if saber_risk and maze_profile:
    risk_penalty += 1.35
  if hourglass_risk is not None and maze_profile:
    risk_penalty += min(3.0, 0.8 + max(0, 12 - hourglass_risk[0]) * 0.18)
  area_value, raw_area, center_area, core_area = flood_capture(c, full_trail)
  if raw_area <= 0 or decision_budget_over():
    return None
  item_value = route_item_value(c, cells, close_turns)
  if target_item is not None:
    kind = target_item.get('type', '')
    spawn_in = max(0, int(target_item.get('turn', c['turn']) - c['turn']))
    if target_item in c['s'].get('items', []):
      sx, sy = (int(target_item.get('x', -1)), int(target_item.get('y', -1)))
      size = ITEM_SIZE.get(kind, 1)
      actually_touched = any((sx <= v % c['w'] < sx + size and sy <= v // c['w'] < sy + size for v in cells))
      if actually_touched:
        item_value = max(item_value, item_values(c).get(kind, 2.0) * 0.95)
    elif spawn_in > 0:
      wing = int(me.get('wing', 0) or 0)
      spawn_steps = sum((2 if t <= wing else 1 for t in range(1, spawn_in + 1)))
      sx, sy = (int(target_item.get('x', -1)), int(target_item.get('y', -1)))
      size = ITEM_SIZE.get(kind, 1)
      if 0 < spawn_steps <= len(cells):
        v = cells[spawn_steps - 1]
        if sx <= v % c['w'] < sx + size and sy <= v // c['w'] < sy + size:
          item_value = max(item_value, item_values(c).get(kind, 2.0) * 0.9)
  cut_value = route_cut_value(c, cells)
  center_route = sum((1 for v in out_cells if 21 <= v % c['w'] <= 28 and 21 <= v // c['w'] <= 28))
  center_bonus = min(110.0, center_area * (0.88 if maze_profile else 0.62) + core_area * (2.0 if maze_profile else 1.55))
  if early_center and center_route:
    center_bonus += min(48.0, center_route * (0.95 if maze_profile else 0.72))
  elif center_route:
    center_bonus += min(22.0, center_route * 0.28)
  value = area_value + item_value * 1.65 + cut_value + center_bonus
  efficiency = value / (close_turns + 2.0)
  own_dist = c.get('own_dist', [])
  expansion_dist = own_dist[out_cells[-1]] if own_dist and out_cells[-1] < len(own_dist) else 0
  expansion_bonus = min(12.0, max(0, expansion_dist - 4) * 0.35)
  absolute_gain = 0.98 * math.sqrt(max(0.0, area_value)) + (0.080 if maze_profile else 0.035) * min(raw_area, 360)
  score = 0.72 * efficiency + absolute_gain + expansion_bonus - risk_penalty
  if target_item is not None and item_value > 0:
    score += 1.25 + min(1.0, item_value * 0.02)
  if maze_profile and raw_area < 24 and item_value < 8 and cut_value < 10:
    return None
  if maze_profile and raw_area < 52 and len(out_dirs) < 18 and item_value < 8 and cut_value < 10 and center_route < 7:
    return None
  if raw_area < 16 and item_value < 10 and center_route < 3 and cut_value < 12:
    return None
  if raw_area < 32 and len(home_dirs) > len(out_dirs) + 8 and item_value < 12 and center_route < 4:
    score -= min(4.0, (len(home_dirs) - len(out_dirs) - 8) * 0.22)
  if RECENT_POSITIONS and (not c['mytrail']):
    recent = tuple(RECENT_POSITIONS)[-12:]
    seen = set(recent)
    repeated = sum((1 for v in out_cells[:10] if v in seen))
    score -= min(4.0, repeated * 0.45)
    if len(recent) >= 6 and out_cells and (out_cells[0] in recent[-6:]):
      score -= 1.25
  return {'score': score, 'dirs': dirs, 'cells': cells, 'area': raw_area, 'item': item_value, 'cut': cut_value, 'turns': close_turns, 'slack': nearest_eta - close_turns if nearest_eta < INF else INF, 'center': center_area, 'target': out_cells[-1], 'home_target': home_cells[-1] if home_cells else c['start']}
def plan_emergency_return(c):
  global PLAN
  PLAN = None
  if not c['mytrail']:
    return None
  home = best_home_route(c)
  if home is None:
    return emergency_self_break(c)
  if home.get('slash_risk'):
    rescue = self_break_route(c)
    slash_eta = pending_slash_eta(c, c['mytrail'])
    if rescue and turns_for_steps(len(rescue[0]), c['me'].get('wing', 0)) < slash_eta:
      return emergency_self_break(c)
  hg = possible_hourglass_attack(c, set(c['mytrail']) | set(home['cells']), home['turns'], home['cells'])
  if hg is not None and home['turns'] > hg[0]:
    rescue = self_break_route(c)
    if rescue and len(rescue[0]) == 1 and (turns_for_steps(1, c['me'].get('wing', 0)) <= hg[0]):
      return emergency_self_break(c)
  dirs = home['dirs']
  cells = home['cells']
  count = 1
  if int(c['me'].get('wing', 0) or 0) > 0 and len(dirs) >= 2:
    if not immediate_enemy_collision(c, cells[:2], dirs[:2]):
      count = 2
  return dirs[:count]
def cached_plan_action(c):
  global PLAN
  if PLAN is None:
    return None
  w, me = (c['w'], c['me'])
  pos = int(me.get('y', 0)) * w + int(me.get('x', 0))
  if pos != PLAN.get('expected', -1):
    PLAN = None
    return None
  i = PLAN.get('index', 0)
  dirs = PLAN.get('dirs', [])
  cells = PLAN.get('cells', [])
  if i >= len(dirs):
    PLAN = None
    return None
  rem_dirs, rem_cells = (dirs[i:], cells[i:])
  if not rem_cells or (me.get('lastDir') and OPP.get(rem_dirs[0]) == me.get('lastDir')):
    PLAN = None
    return None
  home_target = PLAN.get('home_target', -1)
  if not 0 <= home_target < c['n'] or c['grid'][home_target] != c['meidx']:
    replacement = next((k for k in range(i, len(cells)) if c['grid'][cells[k]] == c['meidx']), None)
    if replacement is not None:
      PLAN['dirs'] = dirs[:replacement + 1]
      PLAN['cells'] = cells[:replacement + 1]
      PLAN['home_target'] = cells[replacement]
      dirs, cells = (PLAN['dirs'], PLAN['cells'])
      rem_dirs, rem_cells = (dirs[i:], cells[i:])
    else:
      PLAN = None
      return None
  if any((c['blocked'][v] or v in c['occupied'] for v in rem_cells[:2])):
    PLAN = None
    return None
  full = set(c['mytrail'])
  full.update((v for v in rem_cells if c['grid'][v] != c['meidx']))
  max_trail = int(c['rules'].get('maxTrail', 120) or 120)
  if len(full) > max_trail - 1:
    PLAN = None
    return None
  remain_turns = turns_for_steps(len(rem_dirs), me.get('wing', 0))
  slash_eta = pending_slash_eta(c, full)
  maze_profile = w == 50 and c['h'] == 50 and 0.23 <= (sum(c['blocked']) / float(c['n'])) <= 0.28
  if maze_profile:
    if slash_eta <= remain_turns:
      PLAN = None
      return None
  else:
    home = best_home_route(c)
    if home is not None:
      danger, reason, _ = trail_return_danger(c, home)
      if danger:
        PLAN = None
        return None
      if slash_eta < remain_turns:
        PLAN = None
        return None
    else:
      hg = possible_hourglass_attack(c, full, remain_turns, rem_cells)
      if hg is not None:
        rescue = self_break_route(c)
        if rescue and len(rescue[0]) == 1 and (turns_for_steps(1, me.get('wing', 0)) <= hg[0]):
          PLAN = None
          return emergency_self_break(c)
      eta, enemy = nearest_enemy_eta(c, c['mytrail'])
      margin = attack_margin(c, enemy)
      urgent_enemy = eta <= remain_turns + margin
      urgent_saber = slash_eta <= remain_turns + 1
      if urgent_enemy or urgent_saber:
        rescue = self_break_route(c)
        if rescue and turns_for_steps(len(rescue[0]), me.get('wing', 0)) + 1 <= min(eta, slash_eta):
          PLAN = None
          return emergency_self_break(c)
  if immediate_enemy_collision(c, rem_cells[:2], rem_dirs[:2]):
    PLAN = None
    return None
  count = 1
  if int(me.get('wing', 0) or 0) > 0 and len(rem_dirs) >= 2:
    c1, c2 = (rem_cells[0], rem_cells[1])
    stop_for_spawn = False
    for it in c['s'].get('upcomingItems', c['s'].get('upcoming', [])):
      spawn_in = int(it.get('turn', c['turn']) - c['turn'])
      size = ITEM_SIZE.get(it.get('type'), 1)
      x0, y0 = (int(it.get('x', -1)), int(it.get('y', -1)))
      in1 = x0 <= c1 % w < x0 + size and y0 <= c1 // w < y0 + size
      in2 = x0 <= c2 % w < x0 + size and y0 <= c2 // w < y0 + size
      if spawn_in <= 1 and in1 and (not in2):
        stop_for_spawn = True
        break
    if not stop_for_spawn:
      count = 2
  PLAN['index'] = i + count
  PLAN['expected'] = rem_cells[count - 1]
  if PLAN['index'] >= len(dirs):
    PLAN = None
  return rem_dirs[:count]
def local_loop_fallback(c, trees, early_center, own_dist):
  best = None
  w, h = c['w'], c['h']
  for order, tree in enumerate(trees):
    if decision_budget_over():
      break
    dist = tree[2]
    sampled = {}
    probe = set(range(0, c['n'], 2))
    for item in c['s'].get('items', []) + c['s'].get('upcomingItems', c['s'].get('upcoming', [])):
      size = ITEM_SIZE.get(item.get('type'), 1)
      x0, y0 = (int(item.get('x', -1)), int(item.get('y', -1)))
      for dy in range(size):
        for dx in range(size):
          x, y = x0 + dx, y0 + dy
          if 0 <= x < w and 0 <= y < h:
            v = y * w + x
            probe.add(v)
            for u, _ in neighbors(c, v):
              probe.add(u)
    for probe_i, v in enumerate(probe):
      if (probe_i & 31) == 0 and decision_budget_over():
        break
      d = dist[v * 2 + 1]
      if d < 8 or d > 68 or c['blocked'][v] or c['grid'][v] == c['meidx']:
        continue
      if v in c['mytrail'] or v in c['occupied']:
        continue
      key = (v // w // 5, v % w // 5)
      free = 0
      for u, _ in neighbors(c, v):
        if not c['blocked'][u] and c['grid'][u] != c['meidx'] and u not in c['occupied']:
          free += 1
      own_gap = own_dist[v] if own_dist[v] >= 0 else 0
      rank = (own_gap, d, free)
      old = sampled.get(key)
      if old is None or rank > old[0]:
        sampled[key] = (rank, v)
    targets = [x[1] for x in sampled.values()]
    targets.sort(key=lambda v: (-(own_dist[v] if own_dist[v] >= 0 else 0),
                                -dist[v * 2 + 1],
                                abs(v % w - (w - 1) / 2) + abs(v // w - (h - 1) / 2)))
    for target in targets[:2]:
      if decision_budget_over():
        break
      path = extract_out_path(tree, target)
      if path is None:
        continue
      out_dirs, out_cells = path
      if not out_dirs:
        continue
      forbidden = c['mytrail'] | {v for v in out_cells if c['grid'][v] != c['meidx']}
      if len(forbidden) >= int(c['rules'].get('maxTrail', 120) or 120):
        continue
      home = fast_home_route(c, target, forbidden, (order + 1) & 3, out_dirs[-1], own_dist)
      if home is None:
        continue
      candidate = plan_score(c, out_dirs, out_cells, home[0], home[1], early_center)
      if candidate and (best is None or candidate['score'] > best['score']):
        best = candidate
  return best
def quick_frontier_step(c):
  start = c['start']
  me = c['meidx']
  last = c['me'].get('lastDir')
  options = []
  for u, d in neighbors(c, start):
    if last and OPP.get(d) == last:
      continue
    if c['blocked'][u] or u in c['occupied'] or u in c['mytrail']:
      continue
    exits = 0
    for v, _ in neighbors(c, u):
      if not c['blocked'][v] and v not in c['occupied'] and v not in c['mytrail'] and c['grid'][v] != me:
        exits += 1
    if c['grid'][u] == me:
      score = 4.0 * exits - 0.7 * RECENT_POSITIONS.count(u) - (2.0 if u in FRONTIER_HISTORY else 0.0)
    else:
      score = 1.2 * exits - 0.9 * RECENT_POSITIONS.count(u) - 3.0
    options.append((score, d))
  if not options:
    return None
  options.sort(reverse=True)
  return options[0][1]
def frontier_reposition(c):
  global FRONTIER_TARGET
  start, w, h = (c['start'], c['w'], c['h'])
  me = c['meidx']
  recent_counts = {}
  for old_pos in RECENT_POSITIONS:
    recent_counts[old_pos] = recent_counts.get(old_pos, 0) + 1
  if c['grid'][start] != me:
    home = bfs_home(c, start, c['mytrail'], 0, c['me'].get('lastDir'))
    return home[0][0] if home and home[0] else None
  def exits_at(v):
    return [u for u, _ in neighbors(c, v) if not c['blocked'][u] and u not in c['occupied'] and (u not in c['mytrail']) and (c['grid'][u] != me)]
  if FRONTIER_TARGET is not None:
    if FRONTIER_TARGET == start or c['grid'][FRONTIER_TARGET] != me or (not exits_at(FRONTIER_TARGET)):
      FRONTIER_HISTORY.append(FRONTIER_TARGET)
      FRONTIER_TARGET = None
    else:
      q = deque([start])
      prev = {start: None}
      first = {}
      visits = 0
      while q:
        visits += 1
        if (visits & 7) == 0 and decision_budget_over():
          return quick_frontier_step(c)
        v = q.popleft()
        if v == FRONTIER_TARGET:
          return first.get(v)
        for u, d in neighbors(c, v):
          if u in prev or c['blocked'][u] or u in c['occupied'] or (c['grid'][u] != me):
            continue
          if v == start and c['me'].get('lastDir') and (OPP.get(d) == c['me'].get('lastDir')):
            continue
          prev[u] = v
          first[u] = d if v == start else first[v]
          q.append(u)
      FRONTIER_HISTORY.append(FRONTIER_TARGET)
      FRONTIER_TARGET = None
  n = c['n']
  dist = [-1] * n
  first = [None] * n
  dist[start] = 0
  q = deque([start])
  best_target = -1
  best_score = INF
  visits = 0
  while q:
    visits += 1
    if (visits & 7) == 0 and decision_budget_over():
      return quick_frontier_step(c)
    v = q.popleft()
    if dist[v] >= 52:
      continue
    exit_count = 0
    for u, d in neighbors(c, v):
      if c['blocked'][u] or u in c['occupied'] or u in c['mytrail']:
        continue
      if c['grid'][u] != me:
        exit_count += 1
        continue
      if dist[u] >= 0:
        continue
      if v == start and c['me'].get('lastDir') and (OPP.get(d) == c['me'].get('lastDir')):
        continue
      dist[u] = dist[v] + 1
      first[u] = d if v == start else first[v]
      q.append(u)
    if exit_count and v != start:
      history_penalty = (5.0 if v in FRONTIER_HISTORY else 0.0) + min(2.0, recent_counts.get(v, 0) * 0.45)
      enemy_gap = min((dm[v] for _, dm in c.get('enemy_maps', []) if dm[v] >= 0), default=INF)
      safety_bonus = min(6, enemy_gap) * 0.06 if enemy_gap < INF else 0.0
      score = -0.30 * dist[v] - 0.85 * exit_count + history_penalty - safety_bonus
      if score < best_score:
        best_score, best_target = score, v
  if best_target >= 0:
    FRONTIER_TARGET = best_target
    return first[FRONTIER_TARGET]
  options = []
  for u, d in neighbors(c, start):
    if c['blocked'][u] or u in c['occupied'] or c['grid'][u] != me:
      continue
    if c['me'].get('lastDir') and OPP.get(d) == c['me'].get('lastDir'):
      continue
    exits = len(exits_at(u))
    enemy_gap = min((dm[u] for _, dm in c.get('enemy_maps', []) if dm[u] >= 0), default=INF)
    options.append((-exits, -enemy_gap, d))
  options.sort()
  return options[0][2] if options else None
def len_path(prev, target):
  n = 0
  v = target
  while prev.get(v) is not None:
    n += 1
    v = prev[v]
  return n
def choose(c):
  global PLAN
  me = c['me']
  if int(me.get('stun', 0) or 0) > 0:
    PLAN = None
    return None
  if int(me.get('freeze', 0) or 0) > 0:
    PLAN = None
    return None
  start = c['start']
  if start < 0 or start >= c['n'] or c['blocked'][start]:
    PLAN = None
    return None
  if PLAN is not None:
    cached = cached_plan_action(c)
    if cached:
      return cached
  maze_profile = c['w'] == 50 and c['h'] == 50 and 0.23 <= (sum(c['blocked']) / float(c['n'])) <= 0.28
  enemy_horizon = 24 if maze_profile else c['w'] + c['h']
  c['enemy_maps'] = []
  for enemy in c['others']:
    if decision_budget_over():
      return legal_fallback(c)
    c['enemy_maps'].append((enemy, enemy_distance_map(c, enemy, enemy_horizon)))
  if c['mytrail']:
    danger, reason, home = trail_return_danger(c)
    return plan_emergency_return(c)
  center_total = sum(1 for v in range(c['n']) if not c['blocked'][v] and 16 <= v % c['w'] <= 33 and 16 <= v // c['w'] <= 33)
  center_unclaimed = sum(1 for v in range(c['n']) if not c['blocked'][v] and 16 <= v % c['w'] <= 33 and 16 <= v // c['w'] <= 33 and c['grid'][v] != c['meidx'])
  early_center = center_unclaimed > max(10, int(center_total * 0.28)) and c['turn'] < int(c['maxturns'] * 0.90)
  global OWN_DIST_SIGNATURE, OWN_DIST_CACHE, OWN_DIST_SOURCES
  own_cells = [v for v, owner in enumerate(c['grid']) if owner == c['meidx']]
  own_sources = set(own_cells)
  own_sig = (c['w'], c['h'], c['meidx'], len(own_cells), hash(tuple(own_cells)))
  if OWN_DIST_CACHE is None or OWN_DIST_SOURCES is None or not OWN_DIST_SOURCES.issubset(own_sources):
    next_dist = multi_source_distance(c, own_cells)
  elif own_sources == OWN_DIST_SOURCES:
    next_dist = OWN_DIST_CACHE
  else:
    next_dist = multi_source_distance(c, own_cells, OWN_DIST_CACHE, own_sources - OWN_DIST_SOURCES)
  if next_dist is None or decision_budget_over():
    return legal_fallback(c)
  OWN_DIST_CACHE = next_dist
  OWN_DIST_SOURCES = frozenset(own_sources)
  OWN_DIST_SIGNATURE = own_sig
  own_dist = OWN_DIST_CACHE
  c['own_dist'] = own_dist
  best = None
  sx, sy = (start % c['w'], start // c['w'])
  search_order = 0 if sx < c['w'] // 2 else (3 if sy >= c['h'] // 2 else 2)
  focus_goals = None
  if early_center:
    focus_goals = set()
    for by in range(4):
      for bx in range(4):
        best_cell = -1
        best_rank = (-1, -1)
        for yy in range(18 + by * 4, min(34, 22 + by * 4)):
          for xx in range(18 + bx * 4, min(34, 22 + bx * 4)):
            if xx >= c['w'] or yy >= c['h']:
              continue
            v = yy * c['w'] + xx
            if c['blocked'][v] or c['grid'][v] == c['meidx'] or v in c['occupied']:
              continue
            gap = own_dist[v] if own_dist[v] >= 0 else 0
            rank = (gap, -abs(xx - 25) - abs(yy - 25))
            if rank > best_rank:
              best_rank, best_cell = rank, v
        if best_cell >= 0:
          focus_goals.add(best_cell)
    for item in c['s'].get('items', []) + c['s'].get('upcomingItems', c['s'].get('upcoming', [])):
      size = ITEM_SIZE.get(item.get('type'), 1)
      x0, y0 = int(item.get('x', -1)), int(item.get('y', -1))
      for dy in range(size):
        for dx in range(size):
          x, y = x0 + dx, y0 + dy
          if 0 <= x < c['w'] and 0 <= y < c['h']:
            v = y * c['w'] + x
            if not c['blocked'][v] and c['grid'][v] != c['meidx'] and v not in c['occupied']:
              focus_goals.add(v)
  trees = [bfs_out_tree(c, search_order, focus_goals, 60 if maze_profile else INF)]
  targets, early_center = select_targets(c, trees[0], own_dist)
  item_targets = select_item_targets(c, trees[0])
  item_target_map = {cell: item for cell, item in item_targets}
  center_targets = [v for v in targets if 18 <= v % c['w'] <= 31 and 18 <= v // c['w'] <= 31]
  outer_targets = [v for v in targets if v not in set(center_targets)]
  all_targets = []
  if early_center:
    ordered_targets = [cell for cell, _ in item_targets[:3]] + center_targets[:2] + outer_targets[:2]
  else:
    ordered_targets = [cell for cell, _ in item_targets[:3]] + outer_targets[:4] + center_targets[:2]
  for v in ordered_targets:
    if v not in all_targets:
      all_targets.append(v)
  max_trail = int(c['rules'].get('maxTrail', 120) or 120)
  evaluated = 0
  for order, tree in enumerate(trees):
    target_batch = all_targets[:3]
    for target in target_batch:
      if decision_budget_over():
        break
      if evaluated >= 3:
        break
      evaluated += 1
      path = extract_out_path(tree, target)
      if path is None:
        continue
      out_dirs, out_cells = path
      if not out_dirs:
        continue
      new_out = {v for v in out_cells if c['grid'][v] != c['meidx']}
      if len(c['mytrail'] | new_out) >= max_trail:
        continue
      forbidden = c['mytrail'] | new_out
      home = fast_home_route(c, target, forbidden, order + 1 & 3, out_dirs[-1], own_dist)
      if home is None:
        continue
      home_dirs, home_cells = home
      candidate = plan_score(c, out_dirs, out_cells, home_dirs, home_cells, early_center, item_target_map.get(target))
      if candidate and (best is None or candidate['score'] > best['score']):
        best = candidate
  if best is None:
    best = local_loop_fallback(c, trees, early_center, own_dist)
  if best is None and me.get('trail'):
    return plan_emergency_return(c)
  if best is None:
    move = frontier_reposition(c)
    return move
  dirs = best['dirs']
  if not dirs:
    return None
  count = 1
  if int(me.get('wing', 0) or 0) > 0 and len(dirs) >= 2:
    c1, c2 = (best['cells'][0], best['cells'][1])
    stop_for_spawn = False
    for it in c['s'].get('upcomingItems', c['s'].get('upcoming', [])):
      spawn_in = int(it.get('turn', c['turn']) - c['turn'])
      size = ITEM_SIZE.get(it.get('type'), 1)
      x0, y0 = (int(it.get('x', -1)), int(it.get('y', -1)))
      in1 = x0 <= c1 % c['w'] < x0 + size and y0 <= c1 // c['w'] < y0 + size
      in2 = x0 <= c2 % c['w'] < x0 + size and y0 <= c2 // c['w'] < y0 + size
      if spawn_in <= 1 and in1 and (not in2):
        stop_for_spawn = True
        break
    closing_now = bool(c['mytrail']) and c['grid'][c1] == c['meidx']
    if not stop_for_spawn and (not closing_now) and (not immediate_enemy_collision(c, best['cells'][:2], dirs[:2])):
      count = 2
  PLAN = {'dirs': list(dirs), 'cells': list(best['cells']), 'index': count, 'expected': best['cells'][count - 1], 'home_target': best.get('home_target', -1)}
  if count >= len(dirs):
    PLAN = None
  return dirs[:count]
def validate_move(c, move):
  if isinstance(move, str):
    dirs = [move]
  elif isinstance(move, (list, tuple)):
    dirs = list(move[:2])
  else:
    return None
  if not dirs:
    return None
  x, y = (int(c['me'].get('x', -1)), int(c['me'].get('y', -1)))
  last = c['me'].get('lastDir')
  checked = []
  for d in dirs:
    if d not in DELTA or (last and OPP.get(d) == last):
      return None
    dx, dy = DELTA[d]
    x, y = (x + dx, y + dy)
    if not (0 <= x < c['w'] and 0 <= y < c['h']):
      return None
    cell = y * c['w'] + x
    if c['blocked'][cell] or cell in c['occupied']:
      return None
    checked.append(d)
    last = d
  return checked
def legal_fallback(c):
  global DECISION_DEADLINE
  DECISION_DEADLINE = time.perf_counter() + 0.008
  if c['mytrail']:
    home = best_home_route(c)
    if home and home['dirs']:
      dirs, cells = (home['dirs'], home['cells'])
      count = 1
      if int(c['me'].get('wing', 0) or 0) > 0 and len(dirs) > 1:
        if not immediate_enemy_collision(c, cells[:2], dirs[:2]):
          count = 2
      return dirs[:count]
    rescue = emergency_self_break(c)
    if rescue:
      return rescue
    return None
  move = frontier_reposition(c)
  checked = validate_move(c, move) if move else None
  if checked:
    return checked
  last = c['me'].get('lastDir')
  candidates = []
  for u, d in neighbors(c, c['start']):
    if last and OPP.get(d) == last:
      continue
    if c['blocked'][u] or u in c['occupied'] or c['grid'][u] != c['meidx']:
      continue
    exits = sum((1 for v, _ in neighbors(c, u) if not c['blocked'][v] and v not in c['occupied'] and (c['grid'][v] != c['meidx'])))
    candidates.append((-exits, d))
  candidates.sort()
  return [candidates[0][1]] if candidates else None
def decide(state):
  global PLAN, FRONTIER_TARGET, RECENT_POSITIONS, LAST_AREA, NO_CAPTURE_TURNS, DECISION_DEADLINE, OWN_DIST_SIGNATURE, OWN_DIST_CACHE, OWN_DIST_SOURCES
  DECISION_DEADLINE = time.perf_counter() + 0.025
  try:
    c = build_context(state)
    if not c:
      return None
    start = c['start']
    if c['turn'] <= 0:
      RECENT_POSITIONS.clear()
      OWN_DIST_SIGNATURE = None
      OWN_DIST_CACHE = None
      OWN_DIST_SOURCES = None
    if not RECENT_POSITIONS or RECENT_POSITIONS[-1] != start:
      RECENT_POSITIONS.append(start)
    area_now = c['counts'][c['meidx']]
    if LAST_AREA >= 0 and area_now <= LAST_AREA:
      NO_CAPTURE_TURNS += 1
    else:
      NO_CAPTURE_TURNS = 0
    LAST_AREA = area_now
    hist = tuple(RECENT_POSITIONS)
    repeated_cycle = any((len(hist) >= 2 * k and hist[-k:] == hist[-2 * k:-k] for k in range(2, 7)))
    cramped_loop = len(hist) >= 10 and len(set(hist[-10:])) <= 4
    if NO_CAPTURE_TURNS >= 8 and (not c['mytrail']) and (repeated_cycle or cramped_loop):
      if FRONTIER_TARGET is not None:
        FRONTIER_HISTORY.append(FRONTIER_TARGET)
      PLAN = None
      FRONTIER_TARGET = None
      NO_CAPTURE_TURNS = 0
    if int(c['me'].get('stun', 0) or 0) > 0 or int(c['me'].get('freeze', 0) or 0) > 0:
      PLAN = None
      FRONTIER_TARGET = None
      return None
    move = choose(c)
    checked = validate_move(c, move) if move else None
    if checked:
      return checked if len(checked) > 1 else checked[0]
    PLAN = None
    fallback = legal_fallback(c)
    checked = validate_move(c, fallback) if fallback else None
    if checked:
      return checked if len(checked) > 1 else checked[0]
    return None
  except Exception as e:
    print('MAZE decision error:', repr(e), flush=True)
    PLAN = None
    try:
      c = build_context(state)
      if c and c['me'].get('stun', 0) <= 0 and (c['me'].get('freeze', 0) <= 0):
        fallback = legal_fallback(c)
        checked = validate_move(c, fallback) if fallback else None
        if checked:
          return checked if len(checked) > 1 else checked[0]
    except Exception:
      pass
    return None
def log_turn_choice(move, elapsed_ms, state):
  if isinstance(move, (list, tuple)):
    label = ', '.join(str(direction).capitalize() for direction in move[:2] if direction)
  elif move:
    label = str(move).capitalize()
  else:
    player = next((p for p in state.get('players', []) if p.get('playerId') == ME), {})
    if int(player.get('freeze', 0) or 0) > 0:
      label = 'Stay (Freeze)'
    elif int(player.get('stun', 0) or 0) > 0:
      label = 'Stay (Stun)'
    else:
      label = 'Stay'
  print(f"{label or 'Stay'} - {max(1, int(round(elapsed_ms)))}ms", flush=True)
def main():
  print('MAZE GRAPH CONQUEROR ready', ME, GAME, flush=True)
  last_turn = -1
  while True:
    try:
      status = get('/status')
      if status.get('status') == 'finished':
        print('Match finished', status.get('currentTurn'), flush=True)
        return
      turn_no = int(status.get('currentTurn', -1))
      if status.get('status') == 'playing' and turn_no >= 0 and (turn_no != last_turn):
        state = get('/state')
        state_turn = int(state.get('currentTurn', state.get('turn', turn_no)))
        if state_turn == turn_no:
          state['turn'] = turn_no
          state['tickInterval'] = status.get('tickInterval', 500)
          if not isinstance(state.get('config'), dict):
            state['config'] = {}
          if status.get('maxTurns') is not None:
            state['config']['maxTurns'] = status['maxTurns']
          decision_started = time.perf_counter()
          move = decide(state)
          decision_ms = (time.perf_counter() - decision_started) * 1000.0
          log_turn_choice(move, decision_ms, state)
          if isinstance(move, list) and move:
            act('move', {'directions': move[:2]})
          elif move:
            act('move', {'direction': move})
          last_turn = turn_no
      tick = int(status.get('tickInterval') or 500)
      time.sleep(min(0.25, max(0.05, tick / 2000.0)))
    except Exception as e:
      print('MAZE loop error:', repr(e), flush=True)
      time.sleep(0.08)
if __name__ == '__main__':
  main()
