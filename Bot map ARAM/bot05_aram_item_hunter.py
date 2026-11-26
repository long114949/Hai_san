# Python 3.12 | stdlib only | single-file tournament bot
import json
import math
import os
import time
import urllib.error
import urllib.request
from collections import deque
API = os.environ['API_URL']
GAME = os.environ['GAME_ID']
ME = os.environ['PLAYER_ID']
TOKEN = os.environ['PLAYER_TOKEN']
def get(path):
 t0=time.perf_counter()
 with urllib.request.urlopen(f'{API}/game/{GAME}{path}',timeout=0.8) as res: data=json.load(res)
 ms=(time.perf_counter()-t0)*1000
 if ms>=80: print(f'API GET {path} - {ms:.0f}ms',flush=True)
 return data
def act(action, body=None):
 req=urllib.request.Request(f'{API}/game/{GAME}/player/{ME}/{action}',data=json.dumps(body or {}).encode(),headers={'Content-Type':'application/json','x-player-token':TOKEN},method='POST')
 t0=time.perf_counter()
 try:
  with urllib.request.urlopen(req,timeout=0.8) as res: res.read()
  ms=(time.perf_counter()-t0)*1000
  if ms>=80: print(f'API {action} - {ms:.0f}ms',flush=True)
 except urllib.error.HTTPError as err: print('Lenh',action,'bi tu choi:',err.code,err.read().decode(errors='replace'),flush=True)
DIRECTIONS = ('up', 'right', 'down', 'left')
DELTA = {'up': (0, -1), 'down': (0, 1), 'left': (-1, 0), 'right': (1, 0)}
OPPOSITE = {'up': 'down', 'down': 'up', 'left': 'right', 'right': 'left'}
ITEM_SIZE = {'bomb': 1, 'megabomb': 2, 'wing': 1, 'hourglass': 1, 'saber': 2}
ITEM_VALUE = {'saber': 6, 'megabomb': 5, 'hourglass': 4, 'wing': 3, 'bomb': 3}
EMPTY = -1
INF = math.inf
RECENT_POSITIONS = deque(maxlen=24)
DECISION_DEADLINE = 0.0
def decision_budget_over():
  return DECISION_DEADLINE > 0.0 and time.perf_counter() >= DECISION_DEADLINE
PROFILE_NAME = 'BOT 5 - ARAM ITEM + TERRITORY DOMINANCE'
def js_ceil(value):
 return math.ceil(value) if math.isfinite(value) else value
def default_rules():
 return {'stunTurns': 10, 'collisionStunTurns': 2, 'maxTrail': 120, 'breakBonus': 10, 'bombSize': [3, 5], 'megaBombSize': 5, 'wingTurns': [5, 10], 'freezeTurns': [10, 20], 'freezeTargets': 2, 'itemWarnTurns': 2, 'saberRows': 2, 'saberDelayTurns': 4}
def make_seeded_random(seed):
 value = int(seed) & 4294967295
 def random_value():
  nonlocal value
  value = value + 1831565813 & 4294967295
  x = (value ^ value >> 15) * (value | 1) & 4294967295
  mixed = x + ((x ^ x >> 7) * (x | 61) & 4294967295) & 4294967295
  x = (x ^ mixed) & 4294967295
  return ((x ^ x >> 14) & 4294967295) / 4294967296.0
 return random_value
def coord_to_index(ctx, x, y):
 return y * ctx['width'] + x
def index_to_coord(ctx, index):
 return (index % ctx['width'], index // ctx['width'])
def manhattan(ctx, index, x, y):
 cx, cy = index_to_coord(ctx, index)
 return abs(cx - x) + abs(cy - y)
def current_index(ctx):
 me = ctx['me']
 return coord_to_index(ctx, me['x'], me['y'])
def is_occupied_by_other(ctx, index):
 return index in ctx['_occupied_positions']
def is_near_active_enemy(ctx, index):
 cache = ctx.get('_near_enemy_cache')
 if cache is None:
  cache = {}
  ctx['_near_enemy_cache'] = cache
 known = cache.get(index)
 if known is not None:
  return known
 x, y = index % ctx['width'], index // ctx['width']
 result = any(abs(x - ex) + abs(y - ey) <= reach for ex, ey, reach in ctx['_active_enemy_positions'])
 cache[index] = result
 return result
def next_cell(ctx, index, direction):
 x, y = index_to_coord(ctx, index)
 dx, dy = DELTA[direction]
 nx, ny = (x + dx, y + dy)
 if nx < 0 or ny < 0 or nx >= ctx['width'] or (ny >= ctx['height']):
  return -1
 nxt = coord_to_index(ctx, nx, ny)
 if ctx['blocked'][nxt]:
  return -1
 return nxt
def item_covering(items, x, y):
 for item in items:
  size = ITEM_SIZE.get(item.get('type'), 1)
  if item['x'] <= x < item['x'] + size and item['y'] <= y < item['y'] + size:
   return item
 return None
def make_owner_grid(state):
 width = state['width']
 grid = []
 for row in state['owner']:
  values = [ord(ch) - 48 if '0' <= ch <= '9' else EMPTY for ch in row[:width]]
  if len(values) < width:
   values.extend([EMPTY] * (width - len(values)))
  grid.extend(values)
 return grid
def make_context(state, config, turn, me, grid):
 others = [p for p in state.get('players', []) if p.get('index') != me['index']]
 state_rules = state.get('rules')
 if state_rules is not None:
  rules = state_rules
 else:
  rules = {**default_rules(), **(config or {})}
 ctx = {'state': state, 'config': config or {}, 'turn': turn, 'width': state['width'], 'height': state['height'], 'grid': grid, 'rules': rules, 'blocked': bytearray(state['width'] * state['height']), 'me': me, 'others': others, 'myTrail': set(), 'enemyTrail': {}, '_enemyHomeTurns': {}, 'random': make_seeded_random(turn * 7919 + me['index'] * 104729 + 17)}
 ctx['_occupied_positions'] = {coord_to_index(ctx, int(p['x']), int(p['y'])) for p in others if 0 <= int(p.get('x', -1)) < ctx['width'] and 0 <= int(p.get('y', -1)) < ctx['height']}
 ctx['_active_enemy_positions'] = [(int(p['x']), int(p['y']), 2 if p.get('wing', 0) > 0 else 1) for p in others if p.get('stun', 0) == 0 and p.get('freeze', 0) == 0]
 for x, y in me.get('trail', []):
  ctx['myTrail'].add(coord_to_index(ctx, x, y))
 for obstacle in state.get('obstacles', []):
  idx = coord_to_index(ctx, obstacle['x'], obstacle['y'])
  if 0 <= idx < len(ctx['blocked']):
   ctx['blocked'][idx] = 1
 for player in others:
  for x, y in player.get('trail', []):
   ctx['enemyTrail'][coord_to_index(ctx, x, y)] = player
 return ctx
def is_legal_direction(ctx, direction):
 last_direction = ctx['me'].get('lastDir')
 return not (last_direction and OPPOSITE[direction] == last_direction) and next_cell(ctx, current_index(ctx), direction) >= 0
def bfs(ctx, start, last_direction, is_goal, is_valid, radius=INF):
 total = ctx['width'] * ctx['height']
 previous = [-2] * total
 first_direction = [None] * total
 queue = deque()
 previous[start] = -1
 for direction in DIRECTIONS:
  if last_direction and OPPOSITE[direction] == last_direction:
   continue
  nxt = next_cell(ctx, start, direction)
  if nxt < 0 or previous[nxt] != -2 or (not is_valid(nxt)):
   continue
  previous[nxt] = start
  first_direction[nxt] = direction
  queue.append(nxt)
 start_x, start_y = index_to_coord(ctx, start)
 visits = 0
 while queue:
  visits += 1
  if (visits & 7) == 0 and decision_budget_over():
   return None
  cell = queue.popleft()
  if is_goal(cell):
   full_path = []
   cursor = cell
   while cursor != start and cursor >= 0:
    full_path.append(cursor)
    cursor = previous[cursor]
   full_path.reverse()
   path = full_path[:-1]
   path_dirs = []
   cursor = start
   for step_cell in full_path:
    x0, y0 = index_to_coord(ctx, cursor)
    x1, y1 = index_to_coord(ctx, step_cell)
    dx, dy = (x1 - x0, y1 - y0)
    path_dirs.append('right' if dx == 1 else 'left' if dx == -1 else 'down' if dy == 1 else 'up')
    cursor = step_cell
   return {'firstDir': first_direction[cell], 'dist': len(full_path), 'path': path, 'fullPath': full_path, 'directions': path_dirs, 'target': cell}
  if manhattan(ctx, cell, start_x, start_y) >= radius:
   continue
  for direction in DIRECTIONS:
   nxt = next_cell(ctx, cell, direction)
   if nxt < 0 or previous[nxt] != -2 or (not is_valid(nxt)):
    continue
   previous[nxt] = cell
   first_direction[nxt] = first_direction[cell]
   queue.append(nxt)
 return None
def find_path_home(ctx, start, last_direction, additional_blocked=None, avoid_near_enemy=False):
 additional_blocked = additional_blocked or set()
 return bfs(ctx, start, last_direction, lambda cell: ctx['grid'][cell] == ctx['me']['index'], lambda cell: cell not in ctx['myTrail'] and cell not in additional_blocked and (not is_occupied_by_other(ctx, cell)) and (not avoid_near_enemy or not is_near_active_enemy(ctx, cell)))
def _outside_masks(width, height, boundary_rows):
 full = (1 << width) - 1
 open_rows = [full ^ row for row in boundary_rows]
 outside = [0] * height
 frontier = [0] * height
 side_bits = 1 | 1 << width - 1 if width > 1 else 1
 for y in range(height):
  edge = open_rows[y]
  if y != 0 and y != height - 1:
   edge &= side_bits
  outside[y] = edge
  frontier[y] = edge
 while True:
  next_frontier = [0] * height
  changed = False
  for y in range(height):
   spread = frontier[y] << 1 & full | frontier[y] >> 1
   if y:
    spread |= frontier[y - 1]
   if y + 1 < height:
    spread |= frontier[y + 1]
   new_cells = spread & open_rows[y] & ~outside[y]
   if new_cells:
    next_frontier[y] = new_cells
    outside[y] |= new_cells
    changed = True
  if not changed:
   break
  frontier = next_frontier
 return outside
def estimate_enclosed_area(ctx, projected_trail, enemy_weight=1.5):
 width, height = (ctx['width'], ctx['height'])
 total = width * height
 my_index = ctx['me']['index']
 full = (1 << width) - 1
 boundary_rows = [0] * height
 own_rows = [0] * height
 enemy_rows = [0] * height
 blocked_rows = [0] * height
 for y in range(height):
  base = y * width
  own_mask = enemy_mask = blocked_mask = 0
  for x in range(width):
   cell = base + x
   owner = ctx['grid'][cell]
   bit = 1 << x
   if owner == my_index:
    own_mask |= bit
   elif owner >= 0:
    enemy_mask |= bit
   if ctx['blocked'][cell]:
    blocked_mask |= bit
  own_rows[y] = own_mask
  enemy_rows[y] = enemy_mask
  blocked_rows[y] = blocked_mask
  boundary_rows[y] = own_mask
 for cell in ctx['myTrail']:
  boundary_rows[cell // width] |= 1 << cell % width
 for cell in projected_trail:
  boundary_rows[cell // width] |= 1 << cell % width
 outside = _outside_masks(width, height, boundary_rows)
 value = 0.0
 for y in range(height):
  inside = full & ~outside[y]
  capturable = inside & ~blocked_rows[y]
  enemy = capturable & enemy_rows[y]
  empty = capturable & ~(own_rows[y] | enemy_rows[y])
  value += empty.bit_count() + enemy_weight * enemy.bit_count()
 return value
def count_forward_non_owned(ctx, direction):
 count = 0
 cell = current_index(ctx)
 for _ in range(8):
  cell = next_cell(ctx, cell, direction)
  if cell < 0:
   break
  if ctx['grid'][cell] != ctx['me']['index']:
   count += 1
 return count
def turns_until_enemy_can_touch_trail(ctx, trail_cells):
 best = INF
 cells = list(trail_cells)
 if not cells:
  return best
 for enemy in ctx['others']:
  nearest = INF
  for cell in cells:
   nearest = min(nearest, manhattan(ctx, cell, enemy['x'], enemy['y']))
  speed = 2 if enemy.get('wing', 0) > 0 else 1
  turns = math.ceil(nearest / speed) + max(enemy.get('stun', 0), enemy.get('freeze', 0))
  best = min(best, turns)
 return best
def turns_until_enemy_can_reach_cell(ctx, cell):
 best = INF
 for enemy in ctx['others']:
  speed = 2 if enemy.get('wing', 0) > 0 else 1
  turns = manhattan(ctx, cell, enemy['x'], enemy['y']) / speed + max(enemy.get('stun', 0), enemy.get('freeze', 0))
  best = min(best, turns)
 return best
def turns_until_enemy_can_return_home(ctx, enemy, max_turns=None):
 cache = ctx.setdefault('_enemyHomeTurns', {})
 key = (enemy.get('index'), max_turns)
 if key in cache:
  return cache[key]
 enemy_trail = {coord_to_index(ctx, x, y) for x, y in enemy.get('trail', [])}
 wait = max(int(enemy.get('stun', 0) or 0), int(enemy.get('freeze', 0) or 0))
 wing = int(enemy.get('wing', 0) or 0)
 if max_turns is None:
  max_steps = int(ctx['rules'].get('maxTrail', 120) or 120) + 2 * wing
 else:
  available = max(0, int(max_turns) - wait)
  max_steps = 2 * min(wing, available) + max(0, available - wing)
 result = bfs(ctx, coord_to_index(ctx, enemy['x'], enemy['y']), enemy.get('lastDir'), lambda cell: ctx['grid'][cell] == enemy['index'], lambda cell: cell not in enemy_trail, max_steps + 1)
 value = turns_for_steps(result['dist'], wing) + wait if result else INF
 cache[key] = value
 return value
def is_slash_danger(ctx, cell, within_turns, slashes):
 y = cell // ctx['width']
 return any((0 <= slash['left'] <= within_turns and y >= slash['y0'] and (y <= slash['y1']) for slash in slashes))
def simulate_our_step(me, ctx, direction):
 dx, dy = DELTA[direction]
 x = me['x'] + dx
 y = me['y'] + dy
 cell = coord_to_index(ctx, x, y)
 returns_home = ctx['grid'][cell] == me['index']
 hit_enemy_trail = cell in ctx['enemyTrail']
 if hit_enemy_trail:
  trail = list(me.get('trail', []))
 elif returns_home:
  trail = []
 else:
  trail = [*me.get('trail', []), [x, y]]
 return {**me, 'x': x, 'y': y, 'lastDir': direction, 'trail': trail}
def capture_cells_after_closure(grid, width, height, blocked, player_index, trail):
 full = (1 << width) - 1
 boundary_rows = [0] * height
 own_rows = [0] * height
 blocked_rows = [0] * height
 for y in range(height):
  base = y * width
  own_mask = blocked_mask = 0
  for x in range(width):
   cell = base + x
   if grid[cell] == player_index:
    own_mask |= 1 << x
   if blocked[cell]:
    blocked_mask |= 1 << x
  own_rows[y] = own_mask
  blocked_rows[y] = blocked_mask
  boundary_rows[y] = own_mask
 for x, y in trail:
  if 0 <= x < width and 0 <= y < height:
   boundary_rows[y] |= 1 << x
 outside = _outside_masks(width, height, boundary_rows)
 captured = []
 for y in range(height):
  mask = full & ~outside[y] & ~blocked_rows[y] & ~own_rows[y]
  base = y * width
  while mask:
   bit = mask & -mask
   x = bit.bit_length() - 1
   captured.append(base + x)
   mask ^= bit
 return captured
def simulate_first_substep_for_wing(state, context, player, direction, grid):
 width, height = (context['width'], context['height'])
 dx, dy = DELTA[direction]
 x, y = (player['x'] + dx, player['y'] + dy)
 cell = coord_to_index(context, x, y)
 own_index = player['index']
 hit = context['enemyTrail'].get(cell)
 old_trail = [list(point) for point in player.get('trail', [])]
 second_state = dict(state)
 cloned_players = []
 for raw_player in state.get('players', []):
  clone = dict(raw_player)
  clone['trail'] = [list(point) for point in raw_player.get('trail', [])]
  cloned_players.append(clone)
 second_state['players'] = cloned_players
 own_raw = next((p for p in cloned_players if p.get('playerId') == player['playerId']))
 own_raw['x'], own_raw['y'] = (x, y)
 own_raw['lastDir'] = direction
 second_grid = grid[:]
 if hit is not None:
  own_raw['trail'] = old_trail
  victim = next((p for p in cloned_players if p.get('playerId') == hit.get('playerId')), None)
  if victim is not None:
   victim['trail'] = []
   victim['stun'] = max(int(victim.get('stun', 0)), int(context['rules'].get('stunTurns', 10)))
 elif second_grid[cell] == own_index:
  own_raw['trail'] = []
  if old_trail:
   captured = capture_cells_after_closure(second_grid, width, height, context['blocked'], own_index, old_trail)
   captured_set = set(captured)
   for captured_cell in captured:
    second_grid[captured_cell] = own_index
   for other in cloned_players:
    if other.get('playerId') == player['playerId']:
     continue
    other['trail'] = [point for point in other.get('trail', []) if point[1] * width + point[0] not in captured_set]
 else:
  own_raw['trail'] = old_trail + [[x, y]]
 second_state['owner'] = [''.join(('.' if second_grid[row * width + col] < 0 else str(second_grid[row * width + col]) for col in range(width))) for row in range(height)]
 second_me = {'index': own_index, 'playerId': player['playerId'], 'x': x, 'y': y, 'lastDir': direction, 'trail': own_raw['trail'], 'wing': own_raw.get('wing', 0)}
 return (second_state, second_me, second_grid)
def emergency_trail_break(ctx):
 current = current_index(ctx)
 goals = ctx['myTrail'] - {current}
 if not goals:
  return None
 result = bfs(ctx, current, ctx['me'].get('lastDir'), lambda cell: cell in goals, lambda cell: not is_occupied_by_other(ctx, cell), ctx['width'] + ctx['height'])
 return result['firstDir'] if result else None
def insane_pick(ctx):
 current = current_index(ctx)
 me = ctx['me']
 my_index = me['index']
 turns_left = ctx['config'].get('maxTurns', 300) - ctx['turn']
 my_speed = 2 if me.get('wing', 0) > 0 else 1
 slashes = []
 for slash in ctx['state'].get('slashes', []):
  rows = slash.get('rows', [0, -1])
  slashes.append({'y0': rows[0], 'y1': rows[1], 'left': slash['turn'] - ctx['turn'] + 1, 'by': slash.get('by')})
 def slash_danger(cell, within_turns):
  my_id = me.get('playerId')
  return any((slash.get('by') != my_id and 0 <= slash['left'] <= within_turns and (cell // ctx['width'] >= slash['y0']) and (cell // ctx['width'] <= slash['y1']) for slash in slashes))
 def is_safe_direction(direction):
  if not is_legal_direction(ctx, direction):
   return False
  nxt = next_cell(ctx, current, direction)
  return nxt not in ctx['myTrail'] and (not is_occupied_by_other(ctx, nxt)) and (not is_near_active_enemy(ctx, nxt)) and (not (ctx['grid'][nxt] != my_index and slash_danger(nxt, 8)))
 safe_directions = [d for d in DIRECTIONS if is_safe_direction(d)]
 if not safe_directions:
  rescue = emergency_trail_break(ctx) if me.get('trail') else None
  if rescue:
   return rescue
  for direction in DIRECTIONS:
   if is_legal_direction(ctx, direction) and next_cell(ctx, current, direction) not in ctx['myTrail']:
    return direction
  return None
 home_path = find_path_home(ctx, current, me.get('lastDir'), avoid_near_enemy=True)
 if home_path is None:
  home_path = find_path_home(ctx, current, me.get('lastDir'))
 def best_home_direction():
  if home_path and home_path['firstDir'] in safe_directions:
   return home_path['firstDir']
  if home_path and home_path['firstDir'] and is_legal_direction(ctx, home_path['firstDir']):
   return home_path['firstDir']
  if me.get('trail'):
   rescue = emergency_trail_break(ctx)
   if rescue:
    return rescue
  return safe_directions[0]
 is_inside = ctx['grid'][current] == my_index
 if me.get('trail') and turns_left <= math.ceil((home_path['dist'] if home_path else 0) / my_speed) + 3:
  return best_home_direction()
 if not me.get('trail') and is_inside and (turns_left <= 4):
  return None
 if me.get('trail'):
  home_turns = math.ceil((home_path['dist'] if home_path else 99) / my_speed)
  if any((slash_danger(cell, home_turns + 2) for cell in ctx['myTrail'])):
   return best_home_direction()
 adjacent_victims = []
 for direction in safe_directions:
  victim = ctx['enemyTrail'].get(next_cell(ctx, current, direction))
  if victim:
   adjacent_victims.append((direction, victim))
 adjacent_victims.sort(key=lambda entry: len(entry[1].get('trail', [])), reverse=True)
 if adjacent_victims:
  return adjacent_victims[0][0]
 item_values = {}
 actual_items = ctx['state'].get('items', [])
 for item in actual_items:
  size = ITEM_SIZE.get(item.get('type'), 1)
  value = ITEM_VALUE.get(item.get('type'), 2)
  for dy in range(size):
   for dx in range(size):
    cell = coord_to_index(ctx, item['x'] + dx, item['y'] + dy)
    item_values[cell] = value
 upcoming_turns = {}
 for item in ctx['state'].get('upcoming', []):
  size = ITEM_SIZE.get(item.get('type'), 1)
  value = ITEM_VALUE.get(item.get('type'), 2) * 0.9
  for dy in range(size):
   for dx in range(size):
    cell = coord_to_index(ctx, item['x'] + dx, item['y'] + dy)
    item_values[cell] = value
    upcoming_turns[cell] = item['turn']
 if item_values:
  if current in upcoming_turns and upcoming_turns[current] >= ctx['turn'] and (turns_until_enemy_can_touch_trail(ctx, ctx['myTrail']) > 2):
   return None
  def is_item_goal(cell):
   if cell not in item_values:
    return False
   x, y = index_to_coord(ctx, cell)
   return item_covering(actual_items, x, y) is not None or cell in upcoming_turns
  item_path = bfs(ctx, current, me.get('lastDir'), is_item_goal, lambda cell: cell not in ctx['myTrail'] and (not is_occupied_by_other(ctx, cell)) and (not is_near_active_enemy(ctx, cell)) and (ctx['grid'][cell] == my_index or not slash_danger(cell, 8)), 12)
  if item_path and item_path['firstDir'] in safe_directions:
   target = item_path['target']
   value = item_values[target]
   travel_turns = math.ceil(item_path['dist'] / my_speed)
   spawn_delay = upcoming_turns[target] - ctx['turn'] + 1 if target in upcoming_turns else 0
   wait_turns = max(0, spawn_delay - travel_turns)
   can_reach_before_enemy = travel_turns < turns_until_enemy_can_reach_cell(ctx, target)
   trail_extension = [cell for cell in item_path['path'] if ctx['grid'][cell] != my_index]
   if ctx['grid'][target] == my_index:
    return_path = {'dist': 0}
   else:
    return_path = find_path_home(ctx, target, None, set(item_path['path']))
   return_dist = return_path['dist'] if return_path else INF
   projected_trail_length = len(me.get('trail', [])) + len(trail_extension) + return_dist
   total_turns = js_ceil((item_path['dist'] + return_dist) / my_speed) + wait_turns
   safe_to_collect = not trail_extension or total_turns + 2 < turns_until_enemy_can_touch_trail(ctx, [*ctx['myTrail'], *trail_extension])
   if can_reach_before_enemy and safe_to_collect and (projected_trail_length < min(ctx['rules'].get('maxTrail', 120) - 5, 60)) and (wait_turns <= 3) and (value / (travel_turns + wait_turns + 1) >= 0.35):
    return item_path['firstDir']
 if len(me.get('trail', [])) <= 2:
  target_path = bfs(ctx, current, me.get('lastDir'), lambda cell: cell in ctx['enemyTrail'] and len(ctx['enemyTrail'][cell].get('trail', [])) >= 5, lambda cell: cell not in ctx['myTrail'] and (not is_occupied_by_other(ctx, cell)) and (not is_near_active_enemy(ctx, cell)), 12)
  victim = ctx['enemyTrail'].get(target_path['target']) if target_path else None
  if target_path and victim and (target_path['firstDir'] in safe_directions) and (math.ceil(target_path['dist'] / my_speed) < turns_until_enemy_can_return_home(ctx, victim)):
   return target_path['firstDir']
 if not me.get('trail'):
  if not is_inside:
   return best_home_direction()
  def local_potential(cell):
   x, y = index_to_coord(ctx, cell)
   value = 0.0
   for yy in range(max(0, y - 5), min(ctx['height'] - 1, y + 5) + 1):
    for xx in range(max(0, x - 5), min(ctx['width'] - 1, x + 5) + 1):
     index = coord_to_index(ctx, xx, yy)
     owner = ctx['grid'][index]
     if owner != my_index and (not ctx['blocked'][index]) and (not slash_danger(index, 8)):
      value += 1.5 if owner >= 0 else 1.0
   return value - 8 / max(1, turns_until_enemy_can_touch_trail(ctx, [cell]))
  choices = []
  for direction in safe_directions:
   nxt = next_cell(ctx, current, direction)
   if ctx['grid'][nxt] == my_index:
    continue
   score = local_potential(nxt) + ctx['random']() * 0.5
   choices.append((score, direction))
  choices.sort(key=lambda entry: entry[0], reverse=True)
  if choices and choices[0][0] > 0:
   return choices[0][1]
  fallback = bfs(ctx, current, me.get('lastDir'), lambda cell: ctx['grid'][cell] != my_index, lambda cell: not is_occupied_by_other(ctx, cell))
  return fallback['firstDir'] if fallback else safe_directions[0]
 enemy_arrival = turns_until_enemy_can_touch_trail(ctx, ctx['myTrail'])
 max_trail = min(ctx['rules'].get('maxTrail', 120) - 5, 80 if me.get('wing', 0) > 0 else 60)
 if not home_path or math.ceil(home_path['dist'] / my_speed) + 2 >= enemy_arrival or len(me.get('trail', [])) + home_path['dist'] >= max_trail:
  return best_home_direction()
 best = None
 for direction in safe_directions:
  nxt = next_cell(ctx, current, direction)
  if ctx['grid'][nxt] == my_index:
   score = estimate_enclosed_area(ctx, []) / max(1, len(me.get('trail', [])))
  else:
   return_path = find_path_home(ctx, nxt, direction, {nxt}, avoid_near_enemy=True)
   if not return_path or any((ctx['grid'][cell] != my_index and slash_danger(cell, math.ceil(return_path['dist'] / my_speed) + 2) for cell in return_path['path'])):
    continue
   projected_enemy_arrival = turns_until_enemy_can_touch_trail(ctx, [*ctx['myTrail'], nxt])
   if math.ceil(return_path['dist'] / my_speed) + 2 >= projected_enemy_arrival or len(me.get('trail', [])) + 1 + return_path['dist'] > max_trail:
    continue
   score = estimate_enclosed_area(ctx, [nxt, *return_path['path']]) / (len(me.get('trail', [])) + 1 + return_path['dist'])
  score += ctx['random']() * 0.01
  if best is None or score > best['score']:
   best = {'direction': direction, 'score': score}
 return best['direction'] if best else best_home_direction()
MODE_TABLE = {'safe': {'maxOut': 9, 'maxSide': 12, 'margin': 4, 'enemyWeight': 2.0, 'huntRadius': 5, 'cutValue': 16, 'itemMul': 2.4, 'itemRadius': 20, 'avoidEnemy': True}, 'balanced': {'maxOut': 15, 'maxSide': 18, 'margin': 3, 'enemyWeight': 2.3, 'huntRadius': 9, 'cutValue': 20, 'itemMul': 3.6, 'itemRadius': 30, 'avoidEnemy': True}, 'attack': {'maxOut': 19, 'maxSide': 21, 'margin': 2, 'enemyWeight': 2.7, 'huntRadius': 12, 'cutValue': 24, 'itemMul': 4.0, 'itemRadius': 38, 'avoidEnemy': False}}
CW_DIR = {'up': 'right', 'right': 'down', 'down': 'left', 'left': 'up'}
CCW_DIR = {v: k for k, v in CW_DIR.items()}
def territory_counts(ctx):
 cached = ctx.get('_territory_counts')
 if cached is not None:
  return cached
 counts = [0] * max(4, len(ctx['state'].get('players', [])))
 for owner in ctx['grid']:
  if 0 <= owner < len(counts):
   counts[owner] += 1
 ctx['_territory_counts'] = counts
 return counts
def choose_strategy_mode(ctx):
 config = ctx.get('config', {})
 max_turns = int(config.get('maxTurns', ctx['state'].get('maxTurns', 300)) or 300)
 max_turns = max(1, max_turns)
 turn = int(ctx.get('turn', 0))
 remaining = max(0, max_turns - turn)
 n = ctx['width'] * ctx['height']
 players = ctx['state'].get('players', [])
 counts = territory_counts(ctx)
 my_index = ctx['me']['index']
 scores = {}
 for p in players:
  idx = p.get('index', -1)
  if idx < 0:
   continue
  fallback = counts[idx] if idx < len(counts) else 0
  score = p.get('score', p.get('points', fallback))
  try:
   scores[idx] = float(score)
  except (TypeError, ValueError):
   scores[idx] = float(fallback)
 my_score = scores.get(my_index, float(counts[my_index] if my_index < len(counts) else 0))
 leader_score = max((v for k, v in scores.items() if k != my_index), default=my_score)
 gap = my_score - leader_score
 if turn < 0.12 * max_turns:
  mode = 'balanced'
 elif remaining <= 0.2 * max_turns:
  if gap >= 0:
   mode = 'safe'
  elif -gap > 0.03 * n:
   mode = 'attack'
  else:
   mode = 'balanced'
 elif gap > 0.08 * n:
  mode = 'safe'
 elif -gap > 0.06 * n:
  mode = 'attack'
 else:
  mode = 'balanced'
 params = dict(MODE_TABLE[mode])
 if ctx['width'] == 30 and ctx['height'] == 30:
  obstacle_rows = sum((1 for y in range(ctx['height']) if ctx['blocked'][y * ctx['width']:(y + 1) * ctx['width']].count(1) >= 24))
  if obstacle_rows >= 8:
   params['maxOut'] = max(params['maxOut'], 15 if mode == 'balanced' else 19)
   params['maxSide'] = max(params['maxSide'], 18 if mode == 'balanced' else 21)
   params['itemRadius'] = max(params['itemRadius'], 30)
 if mode == 'attack' and my_score > leader_score:
  params['enemyWeight'] *= 1.6
 params['name'] = mode
 params['remaining'] = remaining
 params['maxTurns'] = max_turns
 params['scoreGap'] = gap
 return params
def turns_for_steps(steps, wing_turns):
 steps = max(0, int(steps))
 wing_turns = max(0, int(wing_turns or 0))
 if steps <= 0:
  return 0
 boosted = min(wing_turns, (steps + 1) // 2)
 return boosted + max(0, steps - 2 * wing_turns)
def build_home_field(ctx, max_distance=64):
 total = ctx['width'] * ctx['height']
 my_index = ctx['me']['index']
 dist = [-1] * total
 next_home = [-1] * total
 occupied = {coord_to_index(ctx, p['x'], p['y']) for p in ctx['others']}
 q = deque()
 for cell, owner in enumerate(ctx['grid']):
  if (cell & 255) == 0 and decision_budget_over():
   return None
  if owner == my_index and (not ctx['blocked'][cell]) and (cell not in occupied):
   dist[cell] = 0
   q.append(cell)
 width, height = (ctx['width'], ctx['height'])
 visits = 0
 while q:
  visits += 1
  if (visits & 7) == 0 and decision_budget_over():
   return None
  cell = q.popleft()
  if dist[cell] >= max_distance:
   continue
  x, y = (cell % width, cell // width)
  for direction in DIRECTIONS:
   dx, dy = DELTA[direction]
   nx, ny = (x + dx, y + dy)
   if nx < 0 or ny < 0 or nx >= width or (ny >= height):
    continue
   nxt = ny * width + nx
   if dist[nxt] >= 0 or ctx['blocked'][nxt] or nxt in ctx['myTrail'] or (nxt in occupied):
    continue
   dist[nxt] = dist[cell] + 1
   next_home[nxt] = cell
   q.append(nxt)
 return (dist, next_home, occupied)
def direction_between(ctx, a, b):
 ax, ay = index_to_coord(ctx, a)
 bx, by = index_to_coord(ctx, b)
 if bx > ax:
  return 'right'
 if bx < ax:
  return 'left'
 if by > ay:
  return 'down'
 return 'up'
def reconstruct_home_route(ctx, endpoint, home_field, forbidden, previous_direction, occupied):
 dist, next_home, _ = home_field
 my_index = ctx['me']['index']
 if ctx['grid'][endpoint] == my_index:
  return ([], [])
 if endpoint < 0 or endpoint >= len(dist) or dist[endpoint] < 0:
  return None
 options = []
 for direction in DIRECTIONS:
  if previous_direction and OPPOSITE[direction] == previous_direction:
   continue
  nxt = next_cell(ctx, endpoint, direction)
  if nxt < 0 or nxt in forbidden or nxt in ctx['myTrail'] or nxt in occupied or dist[nxt] < 0:
   continue
  options.append((dist[nxt] + 1, direction, nxt))
 options.sort(key=lambda x: x[0])
 for _, first_direction, first_cell in options:
  route_cells = [first_cell]
  route_dirs = [first_direction]
  current = first_cell
  previous = first_direction
  guard = 0
  valid = True
  while ctx['grid'][current] != my_index:
   if (guard & 7) == 0 and decision_budget_over():
    return None
   nxt = next_home[current]
   if nxt < 0 or nxt in forbidden or nxt in ctx['myTrail'] or nxt in occupied or ctx['blocked'][nxt]:
    valid = False
    break
   direction = direction_between(ctx, current, nxt)
   if OPPOSITE[direction] == previous:
    valid = False
    break
   route_dirs.append(direction)
   route_cells.append(nxt)
   current = nxt
   previous = direction
   guard += 1
   if guard > len(dist):
    valid = False
    break
  if valid:
   return (route_dirs, route_cells)
 return None
def build_enemy_distance_maps(ctx, targets=None, max_steps=64):
 width, height = (ctx['width'], ctx['height'])
 total = width * height
 maps = []
 targets = targets or []
 for enemy in ctx['others']:
  if targets:
   nearest = min((abs(enemy['x'] - c % width) + abs(enemy['y'] - c // width) for c in targets))
   if nearest > max_steps:
    continue
  start = coord_to_index(ctx, enemy['x'], enemy['y'])
  dist = [-1] * total
  dist[start] = 0
  q = deque([start])
  visits = 0
  while q:
   visits += 1
   if (visits & 7) == 0 and decision_budget_over():
    return []
   cell = q.popleft()
   if dist[cell] >= max_steps:
    continue
   x, y = (cell % width, cell // width)
   nd = dist[cell] + 1
   if x and (not ctx['blocked'][cell - 1]) and (dist[cell - 1] < 0):
    dist[cell - 1] = nd
    q.append(cell - 1)
   if x + 1 < width and (not ctx['blocked'][cell + 1]) and (dist[cell + 1] < 0):
    dist[cell + 1] = nd
    q.append(cell + 1)
   if y and (not ctx['blocked'][cell - width]) and (dist[cell - width] < 0):
    dist[cell - width] = nd
    q.append(cell - width)
   if y + 1 < height and (not ctx['blocked'][cell + width]) and (dist[cell + width] < 0):
    dist[cell + width] = nd
    q.append(cell + width)
  maps.append((enemy, dist))
 return maps
def enemy_turns_to_cell(enemy, steps):
 if steps < 0:
  return INF
 wait = max(int(enemy.get('stun', 0) or 0), int(enemy.get('freeze', 0) or 0))
 return wait + turns_for_steps(steps, enemy.get('wing', 0))
def earliest_enemy_arrival(ctx, cells, enemy_maps):
 if not cells or not enemy_maps:
  return INF
 best = INF
 for enemy, dist in enemy_maps:
  nearest = INF
  for ci, cell in enumerate(cells):
   if (ci & 15) == 0 and decision_budget_over():
    return -INF
   d = dist[cell]
   if d >= 0 and d < nearest:
    nearest = d
    if nearest == 0:
     break
  if nearest != INF:
   best = min(best, enemy_turns_to_cell(enemy, nearest))
 return best
def pending_slash_hits(ctx, trail_cells, plan_turns):
 width = ctx['width']
 my_id = ctx['me'].get('playerId')
 rows = {cell // width for cell in trail_cells}
 for slash in ctx['state'].get('slashes', ctx['state'].get('pendingSlashes', [])):
  if slash.get('by') == my_id:
   continue
  slash_rows = slash.get('rows', [0, -1])
  left = int(slash.get('turn', ctx['turn']) - ctx['turn'] + 1)
  if 0 <= left <= plan_turns + 1:
   if any((slash_rows[0] <= y <= slash_rows[1] for y in rows)):
    return True
 return False
def item_equivalent_value(ctx, item, mode, leader_area, behind):
 kind = item.get('type', '')
 rules = ctx['rules']
 if kind == 'saber':
  rows = rules.get('saberRows', 2)
  try:
   rows = int(rows[0] if isinstance(rows, (list, tuple)) else rows)
  except (TypeError, ValueError):
   rows = 2
  value = 0.55 * rows * ctx['width']
 elif kind == 'megabomb':
  value = 0.5 * max(1, len(ctx['others'])) * min(leader_area, 25)
 elif kind == 'hourglass':
  value = 22 if behind else 12
 elif kind == 'bomb':
  value = 0.6 * min(leader_area, 16)
 elif kind == 'wing':
  value = 7
 else:
  value = ITEM_VALUE.get(kind, 2)
 return value * mode['itemMul']
def route_item_value(ctx, route_cells, mode, counts, max_turns):
 if not route_cells:
  return 0.0
 item_map = ctx.get('_route_item_map')
 if item_map is None:
  players = ctx['state'].get('players', [])
  my_idx = ctx['me']['index']
  enemy_counts = [counts[p['index']] for p in players if p.get('index') != my_idx and 0 <= p.get('index', -1) < len(counts)]
  leader_area = max(enemy_counts, default=0)
  behind = any((counts[my_idx] < v for v in enemy_counts))
  item_map = {}
  actual = ctx['state'].get('items', [])
  upcoming = ctx['state'].get('upcoming', ctx['state'].get('upcomingItems', []))
  for upcoming_flag, collection in ((False, actual), (True, upcoming)):
   for j, item in enumerate(collection):
    size = ITEM_SIZE.get(item.get('type'), 1)
    x0, y0 = (int(item.get('x', -1)), int(item.get('y', -1)))
    value = item_equivalent_value(ctx, item, mode, leader_area, behind)
    spawn_in = max(0, int(item.get('turn', ctx['turn']) - ctx['turn'] + 1)) if upcoming_flag else 0
    key = ('u' if upcoming_flag else 'a', j)
    entry = (key, value * (0.9 if upcoming_flag else 1.0), spawn_in)
    for dy in range(size):
     for dx in range(size):
      x, y = x0 + dx, y0 + dy
      if 0 <= x < ctx['width'] and 0 <= y < ctx['height']:
       cell = y * ctx['width'] + x
       item_map.setdefault(cell, []).append(entry)
  ctx['_route_item_map'] = item_map
 if not item_map:
  return 0.0
 total = 0.0
 seen = set()
 wing = ctx['me'].get('wing', 0)
 for step, cell in enumerate(route_cells, 1):
  entries = item_map.get(cell)
  if not entries:
   continue
  arrival = turns_for_steps(step, wing)
  for key, value, spawn_in in entries:
   if key in seen:
    continue
   if arrival >= spawn_in:
    total += value
    seen.add(key)
 return total
def route_cut_value(ctx, route_cells, mode):
 if not route_cells or not ctx['enemyTrail']:
  return 0.0
 enemies = {p['index']: p for p in ctx['others']}
 touched = {}
 for step, cell in enumerate(route_cells, 1):
  victim = ctx['enemyTrail'].get(cell)
  if not victim:
   continue
  idx = victim['index']
  if idx in touched:
   continue
  our_turns = turns_for_steps(step, ctx['me'].get('wing', 0))
  if our_turns < turns_until_enemy_can_return_home(ctx, victim, our_turns):
   touched[idx] = len(victim.get('trail', []))
 return sum((mode['cutValue'] * (1.0 + min(20, length) / 100.0) for length in touched.values()))
def rough_route_area(ctx, trail_cells, a=1, b=1):
 if not trail_cells:
  return 0.0
 return max(float(a * b), float(len(trail_cells)))
def validate_plan(ctx, directions, route_cells, new_trail, mode, enemy_maps, occupied, max_trail, allow_unsafe=False):
 if not directions:
  return None
 if OPPOSITE.get(directions[0]) == ctx['me'].get('lastDir'):
  return None
 for i in range(1, len(directions)):
  if OPPOSITE[directions[i]] == directions[i - 1]:
   return None
 if len(ctx['myTrail']) + len(set(new_trail)) > max_trail:
  return None
 turns = turns_for_steps(len(directions), ctx['me'].get('wing', 0))
 if turns > mode['remaining']:
  return None
 full_trail = set(ctx['myTrail'])
 full_trail.update(new_trail)
 full_trail_list = list(full_trail)
 if pending_slash_hits(ctx, full_trail_list, turns):
  return None
 slack = INF
 if full_trail_list:
  if decision_budget_over():
   return None
  enemy_time = earliest_enemy_arrival(ctx, full_trail_list, enemy_maps)
  if decision_budget_over():
   return None
  if enemy_time != INF:
   slack = enemy_time - turns
   if not allow_unsafe and slack < mode['margin']:
    return None
 if mode['avoidEnemy'] and len(route_cells) > 0:
  for cell in route_cells[:2]:
   if cell in occupied or is_near_active_enemy(ctx, cell):
    return None
 return {'turns': turns, 'slack': slack, 'trail': full_trail_list}
def make_plan_candidate(ctx, directions, route_cells, new_trail, mode, enemy_maps, occupied, max_trail, counts, extra_item=0.0, extra_cut=0.0, emergency=False, rough=0.0, label='loop'):
 if enemy_maps:
  checked = validate_plan(ctx, directions, route_cells, new_trail, mode, enemy_maps, occupied, max_trail, allow_unsafe=emergency)
  if checked is None:
   return None
 else:
  if not directions or len(ctx['myTrail']) + len(set(new_trail)) > max_trail:
   return None
  if OPPOSITE.get(directions[0]) == ctx['me'].get('lastDir'):
   return None
  for i in range(1, len(directions)):
   if OPPOSITE.get(directions[i]) == directions[i - 1]:
    return None
  turns = turns_for_steps(len(directions), ctx['me'].get('wing', 0))
  if turns > mode['remaining']:
   return None
  checked = {'turns': turns, 'slack': INF}
 item_value = route_item_value(ctx, route_cells, mode, counts, mode['maxTurns'])
 cut_value = route_cut_value(ctx, route_cells, mode)
 return {'directions': directions, 'route_cells': route_cells, 'new_trail': new_trail, 'turns': checked['turns'], 'slack': checked['slack'], 'item_value': item_value + extra_item, 'cut_value': cut_value + extra_cut, 'rough': rough, 'label': label}
def rectangular_candidates(ctx, mode, home_field, enemy_maps, occupied, max_trail, counts):
 candidates = []
 start = current_index(ctx)
 my_idx = ctx['me']['index']
 max_out = min(mode['maxOut'], max(1, max_trail - len(ctx['myTrail']) - 1))
 max_side = mode['maxSide']
 current_dir = ctx['me'].get('lastDir')
 line_samples = {max(1, max_out // 2), max_out}
 side_samples = {max(1, max_side // 2), max_side}
 for first_dir in DIRECTIONS:
  if current_dir and OPPOSITE[first_dir] == current_dir:
   continue
  straight_cells = []
  straight_dirs = []
  straight_trail = []
  cur = start
  left_home = ctx['grid'][cur] != my_idx
  if cur in ctx['myTrail']:
   left_home = True
  for a in range(1, max_out + 1):
   if decision_budget_over():
    return candidates
   nxt = next_cell(ctx, cur, first_dir)
   if nxt < 0 or nxt in ctx['myTrail'] or nxt in occupied:
    break
   if nxt in straight_cells:
    break
   straight_cells.append(nxt)
   straight_dirs.append(first_dir)
   if ctx['grid'][nxt] != my_idx:
    left_home = True
    if nxt not in ctx['enemyTrail']:
     straight_trail.append(nxt)
   elif left_home:
    cand = make_plan_candidate(ctx, list(straight_dirs), list(straight_cells), list(straight_trail), mode, enemy_maps, occupied, max_trail, counts, rough=rough_route_area(ctx, straight_trail, a, 1), label='straight-close')
    if cand:
     candidates.append(cand)
    break
   cur = nxt
   if straight_trail and a in line_samples:
    forbidden = set(ctx['myTrail']) | set(straight_trail)
    home = reconstruct_home_route(ctx, cur, home_field, forbidden, first_dir, occupied)
    if home is not None:
     ret_dirs, ret_cells = home
     all_dirs = straight_dirs + ret_dirs
     all_cells = straight_cells + ret_cells
     added = [c for c in all_cells if ctx['grid'][c] != my_idx and c not in ctx['enemyTrail']]
     cand = make_plan_candidate(ctx, all_dirs, all_cells, added, mode, enemy_maps, occupied, max_trail, counts, rough=rough_route_area(ctx, added, a, 1), label='line-home')
     if cand:
      candidates.append(cand)
      if len(candidates) >= 12:
       return candidates
   if not straight_trail:
    continue
   for turn_dir in (CW_DIR[first_dir], CCW_DIR[first_dir]):
    if decision_budget_over():
     return candidates
    side_cells = []
    side_dirs = []
    side_trail = []
    side_cur = cur
    side_closed = False
    for b in range(1, max_side + 1):
     if decision_budget_over():
      return candidates
     side_next = next_cell(ctx, side_cur, turn_dir)
     if side_next < 0 or side_next in ctx['myTrail'] or side_next in occupied or (side_next in straight_cells) or (side_next in side_cells):
      break
     side_cells.append(side_next)
     side_dirs.append(turn_dir)
     if ctx['grid'][side_next] != my_idx:
      if side_next not in ctx['enemyTrail']:
       side_trail.append(side_next)
     else:
      side_closed = True
     out_cells = straight_cells + side_cells
     out_dirs = straight_dirs + side_dirs
     out_trail = straight_trail + side_trail
     if side_closed:
      cand = make_plan_candidate(ctx, out_dirs, out_cells, out_trail, mode, enemy_maps, occupied, max_trail, counts, rough=rough_route_area(ctx, out_trail, a, b), label='rectangle-close')
      if cand:
       candidates.append(cand)
       if len(candidates) >= 12:
        return candidates
      break
     if b in side_samples:
      forbidden = set(ctx['myTrail']) | set(out_trail)
      home = reconstruct_home_route(ctx, side_next, home_field, forbidden, turn_dir, occupied)
     else:
      home = None
     if home is not None:
      ret_dirs, ret_cells = home
      all_dirs = out_dirs + ret_dirs
      all_cells = out_cells + ret_cells
      added = [c for c in all_cells if ctx['grid'][c] != my_idx and c not in ctx['enemyTrail']]
      cand = make_plan_candidate(ctx, all_dirs, all_cells, added, mode, enemy_maps, occupied, max_trail, counts, rough=rough_route_area(ctx, added, a, b), label='rectangle-home')
      if cand:
       candidates.append(cand)
       if len(candidates) >= 12:
        return candidates
     side_cur = side_next
 return candidates
def direct_target_candidate(ctx, mode, target_path, target_value, label, home_field, enemy_maps, occupied, max_trail, counts, cut=False):
 if not target_path:
  return None
 route_to_target = target_path.get('fullPath', [])
 directions = target_path.get('directions', [])
 if not route_to_target or not directions:
  return None
 end = route_to_target[-1]
 new_trail = [c for c in route_to_target if ctx['grid'][c] != ctx['me']['index'] and c not in ctx['enemyTrail']]
 forbidden = set(ctx['myTrail']) | set(new_trail)
 home = reconstruct_home_route(ctx, end, home_field, forbidden, directions[-1], occupied)
 if home is None:
  return None
 ret_dirs, ret_cells = home
 all_dirs = directions + ret_dirs
 all_cells = route_to_target + ret_cells
 added = [c for c in all_cells if ctx['grid'][c] != ctx['me']['index'] and c not in ctx['enemyTrail']]
 return make_plan_candidate(ctx, all_dirs, all_cells, added, mode, enemy_maps, occupied, max_trail, counts, extra_item=0.0, extra_cut=0.0, rough=rough_route_area(ctx, added, len(directions), 1), label=label)
def hunt_candidate(ctx, mode, home_field, enemy_maps, occupied, max_trail, counts):
 if not ctx['enemyTrail']:
  return None
 start = current_index(ctx)
 path = bfs(ctx, start, ctx['me'].get('lastDir'), lambda cell: cell in ctx['enemyTrail'], lambda cell: cell not in ctx['myTrail'] and cell not in occupied and (not mode['avoidEnemy'] or not is_near_active_enemy(ctx, cell)), mode['huntRadius'])
 if not path:
  return None
 victim = ctx['enemyTrail'].get(path['target'])
 if not victim or not victim.get('trail'):
  return None
 reach_turns = turns_for_steps(path['dist'], ctx['me'].get('wing', 0))
 if reach_turns >= turns_until_enemy_can_return_home(ctx, victim, reach_turns):
  return None
 return direct_target_candidate(ctx, mode, path, mode['cutValue'], 'hunt', home_field, enemy_maps, occupied, max_trail, counts, cut=True)
def item_hunt_candidate(ctx, mode, home_field, enemy_maps, occupied, max_trail, counts):
 items = ctx['state'].get('items', [])
 if not items:
  return None
 goals = {}
 for i, item in enumerate(items):
  size = ITEM_SIZE.get(item.get('type'), 1)
  for dy in range(size):
   for dx in range(size):
    x, y = (item['x'] + dx, item['y'] + dy)
    if 0 <= x < ctx['width'] and 0 <= y < ctx['height']:
     goals[y * ctx['width'] + x] = i
 if not goals:
  return None
 start = current_index(ctx)
 path = bfs(ctx, start, ctx['me'].get('lastDir'), lambda cell: cell in goals, lambda cell: cell not in ctx['myTrail'] and cell not in occupied and (not mode['avoidEnemy'] or not is_near_active_enemy(ctx, cell)), mode['itemRadius'])
 if not path:
  return None
 item = items[goals[path['target']]]
 value = item_equivalent_value(ctx, item, mode, max(counts, default=0), counts[ctx['me']['index']] < max(counts, default=0))
 return direct_target_candidate(ctx, mode, path, value, 'item', home_field, enemy_maps, occupied, max_trail, counts, cut=False)
def plan_pick(ctx):
 mode = choose_strategy_mode(ctx)
 max_trail_rule = int(ctx['rules'].get('maxTrail', 120) or 120)
 max_trail = max(1, max_trail_rule - 1)
 remaining_trail = max(1, max_trail - len(ctx['myTrail']))
 home_horizon = min(remaining_trail, max(32, mode['maxOut'] + mode['maxSide'] + 12))
 home_field = build_home_field(ctx, home_horizon)
 if home_field is None or decision_budget_over():
  return None
 _, _, occupied = home_field
 counts = territory_counts(ctx)
 current = current_index(ctx)
 adjacent = []
 for direction in DIRECTIONS:
  if not is_legal_direction(ctx, direction):
   continue
  nxt = next_cell(ctx, current, direction)
  victim = ctx['enemyTrail'].get(nxt)
  if victim and nxt not in occupied and (not is_near_active_enemy(ctx, nxt)):
   adjacent.append((len(victim.get('trail', [])), direction))
 trail_is_urgent = bool(ctx['myTrail']) and (turns_until_enemy_can_touch_trail(ctx, ctx['myTrail']) <= 2 or pending_slash_hits(ctx, list(ctx['myTrail']), 1))
 if adjacent and (not trail_is_urgent):
  adjacent.sort(reverse=True)
  return {'directions': [adjacent[0][1]], 'mode': mode['name'], 'score': float(mode['cutValue']), 'label': 'adjacent-cut'}
 candidates = rectangular_candidates(ctx, mode, home_field, [], occupied, max_trail, counts)
 if decision_budget_over():
  return None
 candidates.sort(key=lambda c: (c['rough'] + c['item_value'] + c['cut_value']) / (c['turns'] + 2.0), reverse=True)
 candidates = candidates[:8]
 threat_targets = set(ctx['myTrail'])
 max_candidate_turns = 1
 for candidate in candidates:
  if decision_budget_over():
   return None
  threat_targets.update(candidate['new_trail'])
  max_candidate_turns = max(max_candidate_turns, candidate['turns'])
 max_enemy_wing = max((int(p.get('wing', 0) or 0) for p in ctx['others']), default=0)
 enemy_step_cap = max_enemy_wing * 2 + max_candidate_turns + mode['margin'] + 2
 enemy_maps = build_enemy_distance_maps(ctx, list(threat_targets), min(ctx['width'] + ctx['height'], enemy_step_cap))
 if decision_budget_over():
  return None
 safe_candidates = []
 for candidate in candidates:
  if decision_budget_over():
   return None
  checked = validate_plan(ctx, candidate['directions'], candidate['route_cells'], candidate['new_trail'], mode, enemy_maps, occupied, max_trail, allow_unsafe=False)
  if checked is not None:
   candidate['slack'] = checked['slack']
   safe_candidates.append(candidate)
 candidates = safe_candidates
 hunt = hunt_candidate(ctx, mode, home_field, enemy_maps, occupied, max_trail, counts)
 if hunt:
  candidates.append(hunt)
 item = item_hunt_candidate(ctx, mode, home_field, enemy_maps, occupied, max_trail, counts)
 if item:
  candidates.append(item)
 me = ctx['me']
 if me.get('trail'):
  home = reconstruct_home_route(ctx, current, home_field, set(ctx['myTrail']), me.get('lastDir'), occupied)
  if home is not None:
   dirs, cells = home
   emergency = make_plan_candidate(ctx, dirs, cells, [c for c in cells if ctx['grid'][c] != me['index']], mode, enemy_maps, occupied, max_trail, counts, emergency=True, rough=0.0, label='emergency-home')
   if emergency:
    emergency['emergency'] = True
    candidates.append(emergency)
 if not candidates:
  if me.get('trail'):
   home = reconstruct_home_route(ctx, current, home_field, set(ctx['myTrail']), me.get('lastDir'), occupied)
   if home and home[0]:
    return {'directions': home[0], 'mode': mode['name'], 'score': -1.0, 'label': 'forced-home'}
   return None
  return {'directions': [], 'mode': mode['name'], 'score': 0.0, 'label': 'hold'}
 candidates.sort(key=lambda c: (c['rough'] + c['item_value'] + c['cut_value']) / (c['turns'] + 2), reverse=True)
 total = ctx['width'] * ctx['height']
 exact_limit = 3 if total <= 2500 else 2 if total <= 10000 else 1
 best = None
 for candidate in candidates[:exact_limit]:
  if decision_budget_over():
   break
  area = estimate_enclosed_area(ctx, candidate['new_trail'], mode['enemyWeight'])
  value = area + candidate['item_value'] + candidate['cut_value']
  score = value / (candidate['turns'] + 2)
  recent = ctx.get('recent_positions', ())
  if recent and candidate.get('route_cells'):
   recent_tail = tuple(recent[-12:])
   first_cell = candidate['route_cells'][0]
   score -= min(3.0, recent_tail[-8:].count(first_cell) * 0.85)
   recent_set = set(recent_tail)
   repeated = sum((1 for cell in candidate['route_cells'][:8] if cell in recent_set))
   score -= min(2.5, repeated * 0.3)
   for period in range(2, 7):
    if len(recent_tail) >= 2 * period and recent_tail[-period:] == recent_tail[-2 * period:-period]:
     if first_cell == recent_tail[-period]:
      score -= 1.2
     break
  if candidate['slack'] != INF:
   score += min(6.0, max(0.0, candidate['slack'] - mode['margin'])) * 0.015
  candidate['area'] = area
  candidate['score'] = score
  if best is None or (score, area, candidate['slack']) > (best['score'], best['area'], best['slack']):
   best = candidate
 if best is None:
  return None
 best['mode'] = mode['name']
 best['scoreGap'] = mode['scoreGap']
 return best
ACTIVE_PLAN = None
def cached_plan_action(ctx):
 global ACTIVE_PLAN
 plan = ACTIVE_PLAN
 if not plan:
  return None
 w = ctx['width']
 me = ctx['me']
 owner = me['index']
 pos = current_index(ctx)
 i = plan['i']
 dirs = plan['dirs']
 cells = plan['cells']
 if pos != plan['expected'] or i >= len(dirs) or ctx['grid'][plan['home']] != owner:
  ACTIVE_PLAN = None
  return None
 actual = [y * w + x for x, y in me.get('trail', [])]
 if actual != plan['trail']:
  ACTIVE_PLAN = None
  return None
 rem = dirs[i:]
 trail = set(ctx['myTrail'])
 if trail and turns_until_enemy_can_touch_trail(ctx, trail) <= 1:
  ACTIVE_PLAN = None
  return None
 remain_turns = turns_for_steps(len(rem), me.get('wing', 0))
 if pending_slash_hits(ctx, list(trail), min(remain_turns, 12)):
  ACTIVE_PLAN = None
  return None
 count = 2 if me.get('wing', 0) > 0 and len(rem) >= 2 else 1
 occupied = {coord_to_index(ctx, p['x'], p['y']) for p in ctx['others']}
 prev = me.get('lastDir')
 new_trail = list(plan['trail'])
 for j in range(count):
  d = dirs[i + j]
  if prev and OPPOSITE[d] == prev or not is_legal_direction(ctx, d):
   ACTIVE_PLAN = None
   return None
  v = next_cell(ctx, pos if j == 0 else cells[i + j - 1], d)
  if v < 0 or v in occupied or v in trail or is_near_active_enemy(ctx, v):
   ACTIVE_PLAN = None
   return None
  if ctx['grid'][v] != owner:
   new_trail.append(v)
  elif j != count - 1 or i + j != len(dirs) - 1:
   ACTIVE_PLAN = None
   return None
  prev = d
 if len(set(new_trail)) + len(ctx['myTrail']) > int(ctx['rules'].get('maxTrail', 120)) - 1:
  ACTIVE_PLAN = None
  return None
 action = rem[:count]
 plan['i'] += count
 plan['expected'] = cells[plan['i'] - 1]
 plan['trail'] = new_trail
 if plan['i'] >= len(dirs):
  ACTIVE_PLAN = None
 return action if count == 2 else action[0]
def choose_insane_move(state, player_id, config=None, turn=None):
 config = config if config is not None else state.get('config') or {}
 turn = turn if turn is not None else state.get('turn', 0)
 normalized_state = dict(state)
 normalized_state['upcoming'] = state.get('upcoming', state.get('upcomingItems', []))
 normalized_state['slashes'] = state.get('slashes', state.get('pendingSlashes', []))
 normalized_state['items'] = state.get('items', [])
 normalized_state['obstacles'] = state.get('obstacles', [])
 player = next((p for p in normalized_state.get('players', []) if p.get('playerId') == player_id), None)
 global ACTIVE_PLAN
 if player is None:
  ACTIVE_PLAN = None
  return None
 if player.get('stun', 0) > 0 or player.get('freeze', 0) > 0:
  ACTIVE_PLAN = None
  return None
 grid = make_owner_grid(normalized_state)
 me = {'index': player['index'], 'playerId': player['playerId'], 'x': player['x'], 'y': player['y'], 'lastDir': player.get('lastDir'), 'trail': player.get('trail', []), 'wing': player.get('wing', 0)}
 context = make_context(normalized_state, config, turn, me, grid)
 if int(turn or 0) <= 0:
  RECENT_POSITIONS.clear()
 pos_now = current_index(context)
 if not RECENT_POSITIONS or RECENT_POSITIONS[-1] != pos_now:
  RECENT_POSITIONS.append(pos_now)
 context['recent_positions'] = tuple(RECENT_POSITIONS)
 if int(turn or 0) <= 0:
  ACTIVE_PLAN = None
 cached = cached_plan_action(context)
 if cached:
  return cached
 chosen = plan_pick(context)
 chosen_directions = list(chosen.get('directions', [])) if chosen else []
 if not chosen_directions:
  first_direction = insane_pick(context)
  if not first_direction:
   return None
  chosen_directions = [first_direction]
 if chosen and (not context['myTrail']) and (len(chosen_directions) > 1) and chosen.get('route_cells') and (len(chosen.get('route_cells', [])) == len(chosen_directions)) and (chosen.get('label') not in ('adjacent-cut', 'emergency-home', 'forced-home')):
  count0 = 2 if player.get('wing', 0) > 0 and len(chosen_directions) >= 2 else 1
  route_cells = list(chosen['route_cells'])
  expected_trail = [c for c in route_cells[:count0] if context['grid'][c] != player['index']]
  ACTIVE_PLAN = {'dirs': list(chosen_directions), 'cells': route_cells, 'i': count0, 'expected': route_cells[count0 - 1], 'trail': expected_trail, 'home': route_cells[-1]}
 else:
  ACTIVE_PLAN = None
 if player.get('wing', 0) > 0 and len(chosen_directions) >= 2:
  first_direction, second_direction = chosen_directions[:2]
  if OPPOSITE.get(second_direction) != first_direction and is_legal_direction(context, first_direction):
   first_cell = next_cell(context, current_index(context), first_direction)
   second_cell = next_cell(context, first_cell, second_direction)
   if second_cell >= 0 and second_cell not in context['myTrail'] and (second_cell not in {coord_to_index(context, p['x'], p['y']) for p in context['others']}):
    return [first_direction, second_direction]
 return chosen_directions[0] if chosen_directions else None
def intentional_hold(state, player_id):
 p = next((p for p in state.get('players', []) if p.get('playerId') == player_id), None)
 if p is None or p.get('stun', 0) > 0 or p.get('freeze', 0) > 0:
  return True
 w, h = (int(state.get('width', 0)), int(state.get('height', 0)))
 x, y = (int(p.get('x', -1)), int(p.get('y', -1)))
 turn = int(state.get('turn', state.get('currentTurn', 0)))
 cfg = state.get('config') or {}
 max_turns = int(cfg.get('maxTurns', state.get('maxTurns', 600)) or 600)
 trail = p.get('trail', [])
 if not trail and turn >= max_turns - 4 and (0 <= x < w) and (0 <= y < h):
  try:
   grid = make_owner_grid(state)
   if grid[y * w + x] == int(p.get('index', -1)):
    return True
  except Exception:
   pass
 upcoming = state.get('upcoming', state.get('upcomingItems', []))
 for item in upcoming:
  spawn_turn = int(item.get('turn', turn + 99))
  size = ITEM_SIZE.get(item.get('type'), 1)
  ix, iy = (int(item.get('x', -99)), int(item.get('y', -99)))
  if 0 <= x < w and 0 <= y < h and (ix <= x < ix + size) and (iy <= y < iy + size) and (turn <= spawn_turn <= turn + 2):
   return True
 return False
def safe_fallback_move(state, player_id):
 global DECISION_DEADLINE
 DECISION_DEADLINE = time.perf_counter() + 0.008
 p = next((p for p in state.get('players', []) if p.get('playerId') == player_id), None)
 if p is None or p.get('stun', 0) > 0 or p.get('freeze', 0) > 0:
  return None
 try:
  cfg = state.get('config') or {}
  grid = make_owner_grid(state)
  me = {'index': int(p.get('index', 0)), 'playerId': player_id, 'x': int(p.get('x', 0)), 'y': int(p.get('y', 0)), 'lastDir': p.get('lastDir'), 'trail': p.get('trail', []), 'wing': int(p.get('wing', 0) or 0)}
  ctx = make_context(state, cfg, int(state.get('turn', 0)), me, grid)
  current = current_index(ctx)
  if current < 0 or current >= ctx['width'] * ctx['height']:
   return None
  if me['trail']:
   home = find_path_home(ctx, current, me.get('lastDir'), None, False)
   if home and home.get('firstDir') and is_legal_direction(ctx, home['firstDir']):
    return home['firstDir']
   return None
  if grid[current] != me['index']:
   home = find_path_home(ctx, current, me.get('lastDir'), None, False)
   return home.get('firstDir') if home else None
  w, h, own = (ctx['width'], ctx['height'], me['index'])
  q = deque([current])
  first = {current: None}
  best = None
  recent = tuple(RECENT_POSITIONS)
  recent_set = set(recent[-12:])
  visits = 0
  while q:
   visits += 1
   if (visits & 7) == 0 and decision_budget_over():
    break
   cell = q.popleft()
   x, y = (cell % w, cell // w)
   exits = []
   for d in DIRECTIONS:
    nxt = next_cell(ctx, cell, d)
    if nxt < 0 or nxt in ctx['myTrail'] or is_occupied_by_other(ctx, nxt):
     continue
    if is_near_active_enemy(ctx, nxt):
     continue
    if grid[nxt] != own:
     exits.append(nxt)
   if exits:
    depth = 0
    v = cell
    while first[v] is not None:
     depth += 1
     v = first[v][0]
    expansion = 0.0
    for nxt in exits:
     expansion += 1.5 if grid[nxt] >= 0 else 1.0
     if nxt in recent_set:
      expansion -= 0.25
    repeat_penalty = 0.55 * recent[-12:].count(cell)
    score = depth - min(2.4, expansion * 0.35) + repeat_penalty
    if best is None or score < best[0]:
     first_dir = first[cell][1] if first[cell] is not None else None
     if first_dir is None:
      opts = []
      for d in DIRECTIONS:
       if not is_legal_direction(ctx, d):
        continue
       nxt = next_cell(ctx, cell, d)
       if nxt in exits:
        opts.append((-(1.5 if grid[nxt] >= 0 else 1.0), recent[-12:].count(nxt), d))
      if opts:
       opts.sort()
       first_dir = opts[0][2]
     if first_dir:
      best = (score, first_dir)
   for d in DIRECTIONS:
    nxt = next_cell(ctx, cell, d)
    if nxt < 0 or nxt in first or grid[nxt] != own or is_occupied_by_other(ctx, nxt):
     continue
    if cell == current and me.get('lastDir') and (OPPOSITE.get(d) == me.get('lastDir')):
     continue
    first[nxt] = (cell, d) if cell == current else first[cell]
    q.append(nxt)
  if best:
   return best[1]
  choices = []
  for d in DIRECTIONS:
   if not is_legal_direction(ctx, d):
    continue
   nxt = next_cell(ctx, current, d)
   if nxt < 0 or grid[nxt] != own or is_occupied_by_other(ctx, nxt):
    continue
   exits = sum((1 for dd in DIRECTIONS if (u := next_cell(ctx, nxt, dd)) >= 0 and grid[u] != own and (u not in ctx['myTrail']) and (not is_occupied_by_other(ctx, u))))
   score = exits - 0.65 * recent[-12:].count(nxt)
   choices.append((score, d))
  if choices:
   choices.sort(reverse=True)
   return choices[0][1]
  return None
 except Exception:
  return None
def decide(state):
 global DECISION_DEADLINE
 DECISION_DEADLINE = time.perf_counter() + 0.025
 try:
  if intentional_hold(state, ME):
   return None
  move = choose_insane_move(state, ME)
  if move is not None:
   return move
  if intentional_hold(state, ME):
   return None
  if 'ACTIVE_PLAN' in globals():
   globals()['ACTIVE_PLAN'] = None
  return safe_fallback_move(state, ME)
 except Exception as err:
  print('Loi decide:', err, flush=True)
  if 'ACTIVE_PLAN' in globals():
   globals()['ACTIVE_PLAN'] = None
  return safe_fallback_move(state, ME)
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
 print(PROFILE_NAME if 'PROFILE_NAME' in globals() else 'Specialist bot', ME, GAME, 'ready', flush=True)
 last_turn = -1
 while True:
  try:
   status = get('/status')
   if status.get('status') == 'finished':
    print('Tran da ket thuc o luot', status.get('currentTurn'), flush=True)
    return
   turn_no = int(status.get('currentTurn', -1))
   if status.get('status') == 'playing' and turn_no >= 0 and (turn_no != last_turn):
    state = get('/state')
    state_turn = int(state.get('currentTurn', state.get('turn', turn_no)))
    if state_turn == turn_no:
     if not isinstance(state.get('config'), dict):
      state['config'] = {}
     state['turn'] = turn_no
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
  except Exception as err:
   print('Loi:', err, flush=True)
   time.sleep(0.08)
if __name__ == '__main__':
 main()
