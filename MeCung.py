import json
import math
import os
import time
import urllib.error
import urllib.request
from collections import deque
import heapq
API=os.environ['API_URL']
GAME=os.environ['GAME_ID']
ME=os.environ['PLAYER_ID']
TOKEN=os.environ['PLAYER_TOKEN']
def get(path):
 with urllib.request.urlopen(f'{API}/game/{GAME}{path}',timeout=5)as res:
  return json.load(res)
def act(action,body=None):
 req=urllib.request.Request(f'{API}/game/{GAME}/player/{ME}/{action}',data=json.dumps(body or{}).encode(),headers={'Content-Type':'application/json','x-player-token':TOKEN},method='POST')
 try:
  with urllib.request.urlopen(req,timeout=5)as res:
   res.read()
 except urllib.error.HTTPError as err:
  print('Lenh',action,'bi tu choi:',err.code,err.read().decode(errors='replace'),flush=True)
DIRECTIONS=('up','right','down','left')
DELTA={'up':(0,-1),'down':(0,1),'left':(-1,0),'right':(1,0)}
OPPOSITE={'up':'down','down':'up','left':'right','right':'left'}
ITEM_SIZE={'bomb':1,'megabomb':2,'wing':1,'hourglass':1,'saber':2}
ITEM_VALUE={'saber':6,'megabomb':5,'hourglass':4,'wing':3,'bomb':3}
EMPTY=-1
INF=math.inf
PLAN_MEMORY=None
SPAWN_CELL=None
MAZE_CACHE_KEY=None
MAZE_CACHE_VALUE=None
LAST_PLAN_INFO={}
def js_ceil(value):
 return math.ceil(value)if math.isfinite(value)else value
def default_rules():
 return{'stunTurns':10,'collisionStunTurns':2,'maxTrail':120,'breakBonus':10,'bombSize':[3,5],'megaBombSize':5,'wingTurns':[5,10],'freezeTurns':[10,20],'freezeTargets':2,'itemWarnTurns':2,'saberRows':2,'saberDelayTurns':4}
def coord_to_index(ctx,x,y):
 return y*ctx['width']+x
def index_to_coord(ctx,index):
 return(index%ctx['width'],index//ctx['width'])
def manhattan(ctx,index,x,y):
 cx,cy=index_to_coord(ctx,index)
 return abs(cx-x)+abs(cy-y)
def current_index(ctx):
 me=ctx['me']
 return coord_to_index(ctx,me['x'],me['y'])
def is_occupied_by_other(ctx,index):
 return any((coord_to_index(ctx,player['x'],player['y'])==index for player in ctx['others']))
def is_near_active_enemy(ctx,index):
 return index in ctx.get('enemyReach1',())or index in ctx.get('enemyReach2',())
def next_cell(ctx,index,direction):
 x,y=index_to_coord(ctx,index)
 dx,dy=DELTA[direction]
 nx,ny=(x+dx,y+dy)
 if nx<0 or ny<0 or nx>=ctx['width']or(ny>=ctx['height']):
  return-1
 nxt=coord_to_index(ctx,nx,ny)
 if ctx['blocked'][nxt]:
  return-1
 return nxt
def item_covering(items,x,y):
 for item in items:
  size=ITEM_SIZE.get(item.get('type'),1)
  if item['x']<=x<item['x']+size and item['y']<=y<item['y']+size:
   return item
 return None
def make_owner_grid(state):
 width=state['width']
 height=state['height']
 grid=[EMPTY]*(width*height)
 for y,row in enumerate(state['owner']):
  for x in range(width):
   ch=row[x]
   grid[y*width+x]=int(ch)if ch.isdigit()else EMPTY
 return grid
def make_context(state,config,turn,me,grid):
 others=[p for p in state.get('players',[])if p.get('index')!=me['index']]
 state_rules=state.get('rules')
 if state_rules is not None:
  rules=state_rules
 else:
  rules={**default_rules(),**(config or{})}
 ctx={'state':state,'config':config or{},'turn':turn,'width':state['width'],'height':state['height'],'grid':grid,'rules':rules,'blocked':bytearray(state['width']*state['height']),'me':me,'others':others,'myTrail':set(),'enemyTrail':{},'_enemyHomeTurns':{}}
 for x,y in me.get('trail',[]):
  ctx['myTrail'].add(coord_to_index(ctx,x,y))
 for obstacle in state.get('obstacles',[]):
  idx=coord_to_index(ctx,obstacle['x'],obstacle['y'])
  if 0<=idx<len(ctx['blocked']):
   ctx['blocked'][idx]=1
 for player in others:
  for x,y in player.get('trail',[]):
   ctx['enemyTrail'][coord_to_index(ctx,x,y)]=player
 ctx['enemyReach1'],ctx['enemyReach2']=build_enemy_reach(ctx)
 build_static_row_masks(ctx)
 ctx['maze']=build_maze_analysis(ctx)
 return ctx
def is_legal_direction(ctx,direction):
 last_direction=ctx['me'].get('lastDir')
 return not(last_direction and OPPOSITE[direction]==last_direction)and next_cell(ctx,current_index(ctx),direction)>=0
def build_enemy_reach(ctx):
 reach1,reach2=(set(),set())
 for enemy in ctx['others']:
  pos=coord_to_index(ctx,enemy['x'],enemy['y'])
  reach1.add(pos)
  reach2.add(pos)
  if enemy.get('stun',0)or enemy.get('freeze',0):
   continue
  last=enemy.get('lastDir')
  first=[]
  for direction in DIRECTIONS:
   if last and OPPOSITE[direction]==last:
    continue
   cell=next_cell(ctx,pos,direction)
   if cell>=0:
    first.append((cell,direction))
    reach1.add(cell)
    if not enemy.get('wing',0):
     reach2.add(cell)
  if enemy.get('wing',0):
   for cell,direction in first:
    for direction2 in DIRECTIONS:
     if OPPOSITE[direction2]==direction:
      continue
     cell2=next_cell(ctx,cell,direction2)
     if cell2>=0:
      reach2.add(cell2)
 reach2.update(reach1)
 return(reach1,reach2)
def build_static_row_masks(ctx):
 w,h,me=(ctx['width'],ctx['height'],ctx['me']['index'])
 own,blocked=([0]*h,[0]*h)
 enemies=[{}for _ in range(h)]
 boundary=[0]*h
 for y in range(h):
  base=y*w
  for x in range(w):
   cell,bit=(base+x,1<<x)
   owner=ctx['grid'][cell]
   if owner==me:
    own[y]|=bit
    boundary[y]|=bit
   elif owner>=0:
    row=enemies[y]
    row[owner]=row.get(owner,0)|bit
   if ctx['blocked'][cell]:
    blocked[y]|=bit
 for cell in ctx['myTrail']:
  boundary[cell//w]|=1<<cell%w
 ctx['rowOwn']=own
 ctx['rowBlocked']=blocked
 ctx['rowEnemies']=enemies
 ctx['rowBoundary']=boundary
def build_voronoi_map(ctx):
 w,h=(ctx['width'],ctx['height'])
 total=w*h
 dist=[-1]*total
 masks=bytearray(total)
 q=[]
 for cell,owner in enumerate(ctx['grid']):
  if owner>=0 and(not ctx['blocked'][cell]):
   dist[cell]=0
   masks[cell]=1<<owner
   q.append(cell)
 head=0
 while head<len(q):
  cell=q[head]
  head+=1
  nd,mask=(dist[cell]+1,masks[cell])
  x,y=(cell%w,cell//w)
  if x:
   n=cell-1
   if not ctx['blocked'][n]:
    if dist[n]<0:
     dist[n],masks[n]=(nd,mask)
     q.append(n)
    elif dist[n]==nd:
     merged=masks[n]|mask
     if merged!=masks[n]:
      masks[n]=merged
      q.append(n)
  if x+1<w:
   n=cell+1
   if not ctx['blocked'][n]:
    if dist[n]<0:
     dist[n],masks[n]=(nd,mask)
     q.append(n)
    elif dist[n]==nd:
     merged=masks[n]|mask
     if merged!=masks[n]:
      masks[n]=merged
      q.append(n)
  if y:
   n=cell-w
   if not ctx['blocked'][n]:
    if dist[n]<0:
     dist[n],masks[n]=(nd,mask)
     q.append(n)
    elif dist[n]==nd:
     merged=masks[n]|mask
     if merged!=masks[n]:
      masks[n]=merged
      q.append(n)
  if y+1<h:
   n=cell+w
   if not ctx['blocked'][n]:
    if dist[n]<0:
     dist[n],masks[n]=(nd,mask)
     q.append(n)
    elif dist[n]==nd:
     merged=masks[n]|mask
     if merged!=masks[n]:
      masks[n]=merged
      q.append(n)
 ctx['voronoi']=masks
def voronoi_frontier_bonus(ctx,route_cells):
 masks=ctx.get('voronoi')
 if masks is None or not route_cells:
  return 0.0
 w,h,me=(ctx['width'],ctx['height'],ctx['me']['index'])
 my_bit=1<<me
 seen=set()
 value=0.0
 for cell in route_cells:
  x,y=(cell%w,cell//w)
  neighbors=[]
  if x:
   neighbors.append(cell-1)
  if x+1<w:
   neighbors.append(cell+1)
  if y:
   neighbors.append(cell-w)
  if y+1<h:
   neighbors.append(cell+w)
  for n in neighbors:
   if n in seen or ctx['blocked'][n]or ctx['grid'][n]!=EMPTY:
    continue
   seen.add(n)
   mask=masks[n]
   if mask&my_bit:
    value+=0.22 if mask&~my_bit else 0.34
   else:
    value-=0.08
 return value
def bfs(ctx,start,last_direction,is_goal,is_valid,radius=INF):
 total=ctx['width']*ctx['height']
 previous=[-2]*total
 first_direction=[None]*total
 queue=deque()
 previous[start]=-1
 for direction in DIRECTIONS:
  if last_direction and OPPOSITE[direction]==last_direction:
   continue
  nxt=next_cell(ctx,start,direction)
  if nxt<0 or previous[nxt]!=-2 or(not is_valid(nxt)):
   continue
  previous[nxt]=start
  first_direction[nxt]=direction
  queue.append(nxt)
 start_x,start_y=index_to_coord(ctx,start)
 while queue:
  cell=queue.popleft()
  if is_goal(cell):
   full_path=[]
   cursor=cell
   while cursor!=start and cursor>=0:
    full_path.append(cursor)
    cursor=previous[cursor]
   full_path.reverse()
   path=full_path[:-1]
   path_dirs=[]
   cursor=start
   for step_cell in full_path:
    x0,y0=index_to_coord(ctx,cursor)
    x1,y1=index_to_coord(ctx,step_cell)
    dx,dy=(x1-x0,y1-y0)
    path_dirs.append('right' if dx==1 else 'left' if dx==-1 else 'down' if dy==1 else 'up')
    cursor=step_cell
   return{'firstDir':first_direction[cell],'dist':len(full_path),'path':path,'fullPath':full_path,'directions':path_dirs,'target':cell}
  if manhattan(ctx,cell,start_x,start_y)>=radius:
   continue
  for direction in DIRECTIONS:
   nxt=next_cell(ctx,cell,direction)
   if nxt<0 or previous[nxt]!=-2 or(not is_valid(nxt)):
    continue
   previous[nxt]=cell
   first_direction[nxt]=first_direction[cell]
   queue.append(nxt)
 return None
def bfs_many_goals(ctx,start,last_direction,is_valid,radius,goal_map):
 total=ctx['width']*ctx['height']
 previous=[-2]*total
 queue=deque()
 previous[start]=-1
 for direction in DIRECTIONS:
  if last_direction and OPPOSITE[direction]==last_direction:
   continue
  nxt=next_cell(ctx,start,direction)
  if nxt>=0 and previous[nxt]==-2 and is_valid(nxt):
   previous[nxt]=start
   queue.append(nxt)
 found={}
 goal_count=len({spec_id for ids in goal_map.values()for spec_id in ids})
 sx,sy=index_to_coord(ctx,start)
 while queue and len(found)<goal_count:
  cell=queue.popleft()
  for spec_id in goal_map.get(cell,()):
   if spec_id in found:
    continue
   full_path=[]
   cursor=cell
   while cursor!=start and cursor>=0:
    full_path.append(cursor)
    cursor=previous[cursor]
   full_path.reverse()
   path_dirs=[]
   cursor=start
   for step_cell in full_path:
    path_dirs.append(direction_between(ctx,cursor,step_cell))
    cursor=step_cell
   found[spec_id]={'firstDir':path_dirs[0]if path_dirs else None,'dist':len(full_path),'path':full_path[:-1],'fullPath':full_path,'directions':path_dirs,'target':cell}
  if manhattan(ctx,cell,sx,sy)>=radius:
   continue
  x,y=(cell%ctx['width'],cell//ctx['width'])
  for direction in DIRECTIONS:
   dx,dy=DELTA[direction]
   nx,ny=(x+dx,y+dy)
   if nx<0 or ny<0 or nx>=ctx['width']or(ny>=ctx['height']):
    continue
   nxt=ny*ctx['width']+nx
   if previous[nxt]==-2 and(not ctx['blocked'][nxt])and is_valid(nxt):
    previous[nxt]=cell
    queue.append(nxt)
 return found
def find_path_home(ctx,start,last_direction,additional_blocked=None,avoid_near_enemy=False):
 additional_blocked=additional_blocked or set()
 return bfs(ctx,start,last_direction,lambda cell:ctx['grid'][cell]==ctx['me']['index'],lambda cell:cell not in ctx['myTrail']and cell not in additional_blocked and(not is_occupied_by_other(ctx,cell))and(not avoid_near_enemy or not is_near_active_enemy(ctx,cell)))
def _outside_masks(width,height,boundary_rows):
 full=(1<<width)-1
 open_rows=[full^row for row in boundary_rows]
 outside=[0]*height
 queue=deque()
 queued=bytearray(height)
 side_bits=1|1<<width-1 if width>1 else 1
 for y in range(height):
  edge=open_rows[y]
  if y!=0 and y!=height-1:
   edge&=side_bits
  if edge:
   outside[y]=edge
   queue.append(y)
   queued[y]=1
 while queue:
  y=queue.popleft()
  queued[y]=0
  row=outside[y]
  row_open=open_rows[y]
  while True:
   spread=row<<1&full|row>>1
   new_cells=spread&row_open&~row
   if not new_cells:
    break
   row|=new_cells
  outside[y]=row
  if y:
   new_cells=row&open_rows[y-1]&~outside[y-1]
   if new_cells:
    outside[y-1]|=new_cells
    if not queued[y-1]:
     queue.append(y-1)
     queued[y-1]=1
  if y+1<height:
   new_cells=row&open_rows[y+1]&~outside[y+1]
   if new_cells:
    outside[y+1]|=new_cells
    if not queued[y+1]:
     queue.append(y+1)
     queued[y+1]=1
 return outside
def estimate_enclosed_area(ctx,projected_trail,enemy_weight=1.8,leader_index=None,leader_bonus=0.0):
 width,height=(ctx['width'],ctx['height'])
 full=(1<<width)-1
 boundary_rows=ctx['rowBoundary'].copy()
 for cell in projected_trail:
  boundary_rows[cell//width]|=1<<cell%width
 outside=_outside_masks(width,height,boundary_rows)
 value=0.0
 own_rows,blocked_rows,enemy_rows=(ctx['rowOwn'],ctx['rowBlocked'],ctx['rowEnemies'])
 for y in range(height):
  capturable=full&~outside[y]&~blocked_rows[y]
  enemy_union=0
  for mask in enemy_rows[y].values():
   enemy_union|=mask
  empty=capturable&~(own_rows[y]|enemy_union)
  value+=empty.bit_count()
  for owner,mask in enemy_rows[y].items():
   amount=(capturable&mask).bit_count()
   if amount:
    weight=enemy_weight
    if isinstance(enemy_weight,dict):
     weight=enemy_weight.get(owner,1.8)
    if owner==leader_index:
     weight+=leader_bonus
    value+=amount*weight
 gained_trail=set(ctx['myTrail'])
 gained_trail.update(projected_trail)
 value+=len(gained_trail)
 return value
def turns_until_enemy_can_touch_trail(ctx,trail_cells):
 cells=list(trail_cells)
 if not cells or not ctx['others']:
  return INF
 enemy_maps=build_enemy_distance_maps(ctx,cells,max_steps=ctx['width']*ctx['height'])
 best=INF
 for enemy,distances in enemy_maps:
  nearest=min((distances[cell]for cell in cells if distances[cell]>=0),default=-1)
  if nearest>=0:
   best=min(best,enemy_turns_to_cell(enemy,nearest))
 return best
def turns_until_enemy_can_return_home(ctx,enemy,max_turns=None):
 cache=ctx.setdefault('_enemyHomeTurns',{})
 key=(enemy.get('index'),max_turns)
 if key in cache:
  return cache[key]
 enemy_trail={coord_to_index(ctx,x,y)for x,y in enemy.get('trail',[])}
 wait=max(int(enemy.get('stun',0)or 0),int(enemy.get('freeze',0)or 0))
 wing=int(enemy.get('wing',0)or 0)
 limit=int(ctx['rules'].get('maxTrail',120)or 120)
 expire_steps=max(1,limit-len(enemy_trail)+1)
 if max_turns is None:
  max_steps=expire_steps
 else:
  available=max(0,int(max_turns)-wait)
  move_steps=2*min(wing,available)+max(0,available-wing)
  max_steps=min(expire_steps,move_steps)
 result=bfs(ctx,coord_to_index(ctx,enemy['x'],enemy['y']),enemy.get('lastDir'),lambda cell:ctx['grid'][cell]==enemy['index'],lambda cell:cell not in enemy_trail,max_steps+1)
 if result:
  value=wait+turns_for_steps(result['dist'],wing)
 else:
  expires=wait+turns_for_steps(expire_steps,wing)
  value=expires if max_turns is None or expires<=max_turns else INF
 cache[key]=value
 return value
def insane_pick(ctx):
 me,current=(ctx['me'],current_index(ctx))
 if me.get('trail'):
  home=find_path_home(ctx,current,me.get('lastDir'))
  if home:
   return home['firstDir']
 legal=[d for d in DIRECTIONS if is_legal_direction(ctx,d)]
 if not legal:
  return None
 ships={coord_to_index(ctx,p['x'],p['y'])for p in ctx['others']}
 safe=[d for d in legal if next_cell(ctx,current,d)not in ships and next_cell(ctx,current,d)not in ctx['myTrail']]
 if not safe:
  return legal[0]
 best_d,best_v=(safe[0],-INF)
 for d in safe:
  cell,value=(current,0.0)
  for step in range(1,9):
   cell=next_cell(ctx,cell,d)
   if cell<0 or cell in ctx['myTrail']or cell in ships:
    break
   owner=ctx['grid'][cell]
   if owner!=me['index']:
    value+=0.35 if owner>=0 else 1.0
   if step==1 and cell in ctx['enemyReach1']:
    value-=4.0
  if value>best_v:
   best_d,best_v=(d,value)
 return best_d
def build_spawn_profile(ctx):
 """Track spawn-zone saturation, then deliberately pivot toward map center."""
 global SPAWN_CELL
 w,h=ctx['width'],ctx['height'];total=w*h
 if SPAWN_CELL is None or not(0<=SPAWN_CELL<total) or ctx['blocked'][SPAWN_CELL]:
  SPAWN_CELL=current_index(ctx)
 dist=[-1]*total;dist[SPAWN_CELL]=0;q=deque([SPAWN_CELL]);maze=ctx['maze']
 while q:
  cell=q.popleft();nd=dist[cell]+1
  for nxt in maze['neighbors'][cell]:
   if dist[nxt]<0:dist[nxt]=nd;q.append(nxt)
 radius=max(16,min(25,int(min(w,h)*0.46)))
 zone=[i for i,d in enumerate(dist) if 0<=d<=radius and not ctx['blocked'][i]]
 my_idx=ctx['me']['index']
 empty=sum(1 for i in zone if ctx['grid'][i]==EMPTY)
 own=sum(1 for i in zone if ctx['grid'][i]==my_idx)
 rival=sum(1 for i in zone if ctx['grid'][i]>=0 and ctx['grid'][i]!=my_idx)
 ratio=empty/max(1,len(zone))
 turn=int(ctx.get('turn',0));max_turns=max(1,int(ctx.get('config',{}).get('maxTurns',ctx['state'].get('maxTurns',300))or 300))
 # Do not remain in the spawn pocket for most of the match even if some cells remain.
 local_done=empty<=max(28,int(len(zone)*0.24)) or own>=int(len(zone)*0.58)
 if turn<0.30*max_turns and not local_done:
  phase='SPAWN_EXPANSION'
 elif turn<0.82*max_turns:
  phase='MIDGAME_CENTER'
 else:
  phase='ITEM_ENDGAME'
 ctx['spawnDist']=dist;ctx['spawnRadius']=radius;ctx['spawnEmpty']=empty
 ctx['spawnOwn']=own;ctx['spawnRival']=rival;ctx['spawnZoneSize']=len(zone)
 ctx['spawnEmptyRatio']=ratio;ctx['strategyPhase']=phase
 return phase=='SPAWN_EXPANSION'
def capture_region_gains(ctx,projected_trail):
 """Measure new territory near spawn and in the center with one flood fill."""
 if not projected_trail:return 0.0,0.0
 w,h=ctx['width'],ctx['height'];full=(1<<w)-1
 before=_outside_masks(w,h,ctx['rowBoundary']);boundary=ctx['rowBoundary'].copy()
 for cell in projected_trail:boundary[cell//w]|=1<<(cell%w)
 after=_outside_masks(w,h,boundary)
 dist=ctx.get('spawnDist',[]);sr=ctx.get('spawnRadius',22)
 cx,cy=(w-1)/2,(h-1)/2;cr=max(7.0,min(w,h)*0.34)
 spawn_gain=center_gain=0.0
 for y in range(h):
  newly=before[y]&~after[y]&full&~ctx['rowBlocked'][y]
  while newly:
   bit=newly&-newly;x=bit.bit_length()-1;newly-=bit;cell=y*w+x
   if ctx['grid'][cell]==ctx['me']['index']:continue
   d=dist[cell] if cell<len(dist) else -1
   if 0<=d<=sr:spawn_gain+=1.0 if d<=sr*0.72 else 0.55
   cd=abs(x-cx)+abs(y-cy)
   if cd<=cr:center_gain+=1.0 if cd<=cr*0.65 else 0.55
 return spawn_gain,center_gain
def center_route_progress(ctx,route_cells):
 if not route_cells:return 0.0
 w,h=ctx['width'],ctx['height'];cx,cy=(w-1)/2,(h-1)/2
 x0,y0=index_to_coord(ctx,current_index(ctx));start=abs(x0-cx)+abs(y0-cy)
 best=min((abs(cell%w-cx)+abs(cell//w-cy) for cell in route_cells),default=start)
 return max(0.0,start-best)

def remote_route_steps(ctx,route_cells):
 dist=ctx.get('spawnDist',[]);radius=ctx.get('spawnRadius',18)
 return sum(1 for cell in route_cells if cell<len(dist) and dist[cell]>radius)

MODE_TABLE={'safe':{'maxOut':5,'maxSide':8,'margin':3,'enemyWeight':1.3,'huntRadius':2,'cutValue':12,'itemMul':0.5,'itemRadius':6,'avoidEnemy':True},'balanced':{'maxOut':8,'maxSide':10,'margin':2,'enemyWeight':1.8,'huntRadius':7,'cutValue':16,'itemMul':1.0,'itemRadius':12,'avoidEnemy':True},'attack':{'maxOut':11,'maxSide':13,'margin':1,'enemyWeight':2.6,'huntRadius':14,'cutValue':22,'itemMul':1.7,'itemRadius':20,'avoidEnemy':False}}
CW_DIR={'up':'right','right':'down','down':'left','left':'up'}
CCW_DIR={v:k for k,v in CW_DIR.items()}
def territory_counts(ctx):
 counts=[0]*max(4,len(ctx['state'].get('players',[])))
 for owner in ctx['grid']:
  if 0<=owner<len(counts):
   counts[owner]+=1
 return counts
def choose_strategy_mode(ctx):
 config=ctx.get('config',{})
 max_turns=max(1,int(config.get('maxTurns',ctx['state'].get('maxTurns',300))or 300))
 turn=int(ctx.get('turn',0));remaining=max(0,max_turns-turn)
 n=ctx['width']*ctx['height'];players=ctx['state'].get('players',[])
 counts=territory_counts(ctx);my_index=ctx['me']['index'];scores={}
 for p in players:
  idx=p.get('index',-1)
  if idx<0:continue
  fallback=counts[idx]if idx<len(counts)else 0
  try:scores[idx]=float(p.get('score',p.get('points',fallback)))
  except(TypeError,ValueError):scores[idx]=float(fallback)
 my_score=scores.get(my_index,float(counts[my_index]if my_index<len(counts)else 0))
 leader_index=max((idx for idx in scores if idx!=my_index),key=lambda idx:scores[idx],default=-1)
 leader_score=scores.get(leader_index,my_score);gap=my_score-leader_score
 if turn<0.10*max_turns:mode='balanced'
 elif remaining<=0.25*max_turns:
  if gap>=0.025*n:mode='safe'
  elif gap<=-0.015*n:mode='attack'
  else:mode='balanced'
 elif gap>0.055*n:mode='safe'
 elif gap< -0.025*n:mode='attack'
 else:mode='balanced'
 params=dict(MODE_TABLE[mode])
 params['cutValue']=0.0
 params['huntRadius']=0
 params['avoidEnemy']=True
 if gap< -0.025*n:
  params['enemyWeight']=2.45;params['leaderBonus']=1.15;params['cutValue']*=1.42
 elif gap>0.035*n:
  params['enemyWeight']=1.55;params['leaderBonus']=0.18;params['cutValue']*=0.82
 else:
  params['enemyWeight']=2.0;params['leaderBonus']=0.55
 params['leaderIndex']=leader_index
 if any((p.get('wing',0)>0 and not p.get('stun',0) and not p.get('freeze',0)for p in players if p.get('index')!=my_index)):
  params['margin']+=1
 params['name']=mode;params['remaining']=remaining;params['maxTurns']=max_turns;params['scoreGap']=gap
 return params
def turns_for_steps(steps,wing_turns):
 steps=max(0,int(steps))
 wing_turns=max(0,int(wing_turns or 0))
 if steps<=0:
  return 0
 boosted=min(wing_turns,(steps+1)//2)
 return boosted+max(0,steps-2*wing_turns)
def build_home_field(ctx,max_distance=64):
 total=ctx['width']*ctx['height']
 my_index=ctx['me']['index']
 dist=[-1]*total
 next_home=[-1]*total
 occupied={coord_to_index(ctx,p['x'],p['y'])for p in ctx['others']}
 q=deque()
 for cell,owner in enumerate(ctx['grid']):
  if owner==my_index and(not ctx['blocked'][cell])and(cell not in occupied):
   dist[cell]=0
   q.append(cell)
 width,height=(ctx['width'],ctx['height'])
 while q:
  cell=q.popleft()
  if dist[cell]>=max_distance:
   continue
  x,y=(cell%width,cell//width)
  for direction in DIRECTIONS:
   dx,dy=DELTA[direction]
   nx,ny=(x+dx,y+dy)
   if nx<0 or ny<0 or nx>=width or(ny>=height):
    continue
   nxt=ny*width+nx
   if dist[nxt]>=0 or ctx['blocked'][nxt]or nxt in ctx['myTrail']or(nxt in occupied):
    continue
   dist[nxt]=dist[cell]+1
   next_home[nxt]=cell
   q.append(nxt)
 return(dist,next_home,occupied)
def direction_between(ctx,a,b):
 ax,ay=index_to_coord(ctx,a)
 bx,by=index_to_coord(ctx,b)
 if bx>ax:
  return 'right'
 if bx<ax:
  return 'left'
 if by>ay:
  return 'down'
 return 'up'
def build_maze_analysis(ctx):
 global MAZE_CACHE_KEY,MAZE_CACHE_VALUE
 width,height=(ctx['width'],ctx['height'])
 key=(width,height,bytes(ctx['blocked']))
 if key==MAZE_CACHE_KEY and MAZE_CACHE_VALUE is not None:
  return MAZE_CACHE_VALUE
 total=width*height
 neighbors=[[]for _ in range(total)]
 degree=[0]*total
 for cell in range(total):
  if ctx['blocked'][cell]:
   continue
  x,y=(cell%width,cell//width)
  near=neighbors[cell]
  if x and(not ctx['blocked'][cell-1]):
   near.append(cell-1)
  if x+1<width and(not ctx['blocked'][cell+1]):
   near.append(cell+1)
  if y and(not ctx['blocked'][cell-width]):
   near.append(cell-width)
  if y+1<height and(not ctx['blocked'][cell+width]):
   near.append(cell+width)
  degree[cell]=len(near)
 disc=[-1]*total
 low=[0]*total
 parent=[-1]*total
 child_count=[0]*total
 articulation=bytearray(total)
 timer=0
 for root in range(total):
  if ctx['blocked'][root]or disc[root]>=0:
   continue
  disc[root]=low[root]=timer
  timer+=1
  stack=[(root,0)]
  while stack:
   node,offset=stack[-1]
   if offset<len(neighbors[node]):
    nxt=neighbors[node][offset]
    stack[-1]=(node,offset+1)
    if disc[nxt]<0:
     parent[nxt]=node
     child_count[node]+=1
     disc[nxt]=low[nxt]=timer
     timer+=1
     stack.append((nxt,0))
    elif nxt!=parent[node]:
     low[node]=min(low[node],disc[nxt])
   else:
    stack.pop()
    par=parent[node]
    if par>=0:
     low[par]=min(low[par],low[node])
     if parent[par]>=0 and low[node]>=disc[par]:
      articulation[par]=1
    elif child_count[node]>1:
     articulation[node]=1
 result={'neighbors':tuple((tuple(row)for row in neighbors)),'degree':degree,'articulation':articulation,'corridors':tuple((i for i,d in enumerate(degree)if d==2)),'junctions':tuple((i for i,d in enumerate(degree)if d>=3)),'dead_ends':tuple((i for i,d in enumerate(degree)if d==1)),'chokepoints':tuple((i for i,flag in enumerate(articulation)if flag))}
 MAZE_CACHE_KEY=key
 MAZE_CACHE_VALUE=result
 return result
def maze_node_priority(ctx,cell):
 maze=ctx['maze'];my_idx=ctx['me']['index'];degree=maze['degree'][cell]
 near=maze['neighbors'][cell]
 frontier=sum(1 for n in near if ctx['grid'][n]!=my_idx)
 value=1.0
 if degree>=3:value+=2.0+0.5*min(4,degree-3)
 elif degree==2:value+=0.75
 elif degree==1:value+=0.10
 if maze['articulation'][cell]:value+=2.8
 value+=0.75*min(4,frontier)
 owner=ctx['grid'][cell]
 if owner==EMPTY:value+=0.45
 elif owner>=0 and owner!=my_idx:value+=0.15
 x,y=index_to_coord(ctx,cell)
 center_dist=abs(x-(ctx['width']-1)/2)+abs(y-(ctx['height']-1)/2)
 center_scale=max(1.0,(ctx['width']+ctx['height'])*0.52)
 phase=ctx.get('strategyPhase')
 center_weight=0.55 if phase=='SPAWN_EXPANSION' else 3.4 if phase=='MIDGAME_CENTER' else 2.2
 value+=center_weight*max(0.0,1.0-center_dist/center_scale)
 sd=ctx.get('spawnDist',[]);spawn_radius=ctx.get('spawnRadius',20)
 if phase=='MIDGAME_CENTER' and cell<len(sd) and sd[cell]>spawn_radius:
  value+=0.9+0.035*min(20,sd[cell]-spawn_radius)
 return value
def maze_frontier_potential(ctx,start,radius=5):
 """Estimate neutral/enemy space reachable just beyond a maze target."""
 maze=ctx['maze'];my_idx=ctx['me']['index'];seen={start};q=deque([(start,0)])
 value=0.0
 while q:
  cell,depth=q.popleft()
  if depth>=radius:continue
  for nxt in maze['neighbors'][cell]:
   if nxt in seen:continue
   seen.add(nxt);d=depth+1;owner=ctx['grid'][nxt]
   fade=1.0-d/(radius+1.0)
   if owner==EMPTY:value+=fade*(1.0+0.08*min(4,maze['degree'][nxt]))
   elif owner>=0 and owner!=my_idx:value+=0.38*fade
   if maze['degree'][nxt]>=3 and owner!=my_idx:value+=0.16*fade
   q.append((nxt,d))
 return min(22.0,value*0.24)
def maze_weighted_targets(ctx,mode,occupied,max_steps,limit=16):
 start=current_index(ctx);my_idx=ctx['me']['index']
 start_left=bool(ctx['myTrail']) or ctx['grid'][start]!=my_idx
 start_state=(start,start_left);distances={start_state:0.0};steps_used={start_state:0};previous={}
 queue=[(0.0,0,start,start_left)];best_cell_state={};last=ctx['me'].get('lastDir');maze=ctx['maze']
 sx,sy=index_to_coord(ctx,start);sc=abs(sx-(ctx['width']-1)/2)+abs(sy-(ctx['height']-1)/2)
 phase=ctx.get('strategyPhase')
 while queue:
  cost,steps,cell,left=heapq.heappop(queue);key=(cell,left)
  if cost>distances.get(key,INF)+1e-9 or steps!=steps_used.get(key):continue
  if left and ctx['grid'][cell]!=my_idx:
   priority=maze_node_priority(ctx,cell)
   if phase=='MIDGAME_CENTER':
    x,y=index_to_coord(ctx,cell);cd=abs(x-(ctx['width']-1)/2)+abs(y-(ctx['height']-1)/2)
    priority+=0.72*max(0.0,sc-cd)
    sd=ctx.get('spawnDist',[])
    if cell<len(sd) and sd[cell]>ctx.get('spawnRadius',22):priority+=0.65
   exponent=0.56 if phase=='MIDGAME_CENTER' else 0.68
   rank=priority/(steps+3.5)**exponent
   old=best_cell_state.get(cell)
   if old is None or rank>old[0]:best_cell_state[cell]=(rank,key,priority,steps)
  if steps>=max_steps:continue
  for direction in DIRECTIONS:
   if cell==start and steps==0 and last and OPPOSITE[direction]==last:continue
   nxt=next_cell(ctx,cell,direction)
   if nxt<0 or nxt in ctx['myTrail'] or nxt in occupied:continue
   owner=ctx['grid'][nxt]
   if left and owner==my_idx:continue
   new_left=left or owner!=my_idx;ns=steps+1;degree=maze['degree'][nxt]
   step_cost=1.0+(0.16 if owner==my_idx else 0.0)+(0.06 if owner>=0 else 0.0)
   if degree>=3:step_cost-=0.14
   elif degree==1:step_cost+=0.16
   if maze['articulation'][nxt]:step_cost-=0.05
   new_cost=cost+max(0.62,step_cost);nk=(nxt,new_left)
   if new_cost+1e-9<distances.get(nk,INF):
    distances[nk]=new_cost;steps_used[nk]=ns;previous[nk]=key
    heapq.heappush(queue,(new_cost,ns,nxt,new_left))
 ranked=sorted(best_cell_state.values(),key=lambda v:v[0],reverse=True);targets=[]
 for rank,key,priority,steps in ranked[:limit*3]:
  cells=[];cursor=key;guard=0
  while cursor!=start_state and cursor in previous:
   cells.append(cursor[0]);cursor=previous[cursor];guard+=1
   if guard>max_steps+2:break
  if cursor!=start_state or not cells:continue
  cells.reverse();dirs=[];prev=start
  for cell in cells:dirs.append(direction_between(ctx,prev,cell));prev=cell
  targets.append({'firstDir':dirs[0],'dist':len(cells),'path':cells[:-1],'fullPath':cells,'directions':dirs,'target':cells[-1],'priority':priority,'rank':rank})
  if len(targets)>=limit:break
 return targets
def reconstruct_home_route(ctx,endpoint,home_field,forbidden,previous_direction,occupied):
 dist,next_home,_=home_field
 my_index=ctx['me']['index']
 if ctx['grid'][endpoint]==my_index:
  return([],[])
 if endpoint<0 or endpoint>=len(dist)or dist[endpoint]<0:
  return None
 options=[]
 for direction in DIRECTIONS:
  if previous_direction and OPPOSITE[direction]==previous_direction:
   continue
  nxt=next_cell(ctx,endpoint,direction)
  if nxt<0 or nxt in forbidden or nxt in ctx['myTrail']or(nxt in occupied)or(dist[nxt]<0):
   continue
  options.append((dist[nxt]+1,direction,nxt))
 options.sort(key=lambda x:x[0])
 for _,first_direction,first_cell in options:
  route_cells=[first_cell]
  route_dirs=[first_direction]
  current=first_cell
  previous=first_direction
  valid=True
  guard=0
  while ctx['grid'][current]!=my_index:
   nxt=next_home[current]
   if nxt<0 or nxt in forbidden or nxt in ctx['myTrail']or(nxt in occupied)or ctx['blocked'][nxt]:
    valid=False
    break
   direction=direction_between(ctx,current,nxt)
   if OPPOSITE[direction]==previous:
    valid=False
    break
   route_dirs.append(direction)
   route_cells.append(nxt)
   current=nxt
   previous=direction
   guard+=1
   if guard>len(dist):
    valid=False
    break
  if valid:
   return(route_dirs,route_cells)
 return None
def build_enemy_distance_maps(ctx,targets=None,max_steps=64):
 width,height=(ctx['width'],ctx['height'])
 total=width*height
 maps=[]
 targets=targets or[]
 for enemy in ctx['others']:
  if targets:
   nearest=min((abs(enemy['x']-c%width)+abs(enemy['y']-c//width)for c in targets))
   if nearest>max_steps:
    continue
  start=coord_to_index(ctx,enemy['x'],enemy['y'])
  dist=[-1]*total
  dist[start]=0
  q=deque([start])
  while q:
   cell=q.popleft()
   if dist[cell]>=max_steps:
    continue
   x,y=(cell%width,cell//width)
   nd=dist[cell]+1
   if x and(not ctx['blocked'][cell-1])and(dist[cell-1]<0):
    dist[cell-1]=nd
    q.append(cell-1)
   if x+1<width and(not ctx['blocked'][cell+1])and(dist[cell+1]<0):
    dist[cell+1]=nd
    q.append(cell+1)
   if y and(not ctx['blocked'][cell-width])and(dist[cell-width]<0):
    dist[cell-width]=nd
    q.append(cell-width)
   if y+1<height and(not ctx['blocked'][cell+width])and(dist[cell+width]<0):
    dist[cell+width]=nd
    q.append(cell+width)
  maps.append((enemy,dist))
 return maps
def enemy_turns_to_cell(enemy,steps):
 if steps<0:
  return INF
 wait=max(int(enemy.get('stun',0)or 0),int(enemy.get('freeze',0)or 0))
 return wait+turns_for_steps(steps,enemy.get('wing',0))
def earliest_enemy_arrival(ctx,cells,enemy_maps):
 if not cells or not enemy_maps:
  return INF
 best=INF
 for enemy,dist in enemy_maps:
  nearest=INF
  for cell in cells:
   d=dist[cell]
   if d>=0 and d<nearest:
    nearest=d
    if nearest==0:
     break
  if nearest!=INF:
   best=min(best,enemy_turns_to_cell(enemy,nearest))
 return best
def pending_slash_hits(ctx,trail_cells,plan_turns):
 width=ctx['width']
 my_id=ctx['me'].get('playerId')
 rows={cell//width for cell in trail_cells}
 for slash in ctx['state'].get('slashes',ctx['state'].get('pendingSlashes',[])):
  if slash.get('by')==my_id:
   continue
  slash_rows=slash.get('rows',[0,-1])
  left=int(slash.get('turn',ctx['turn'])-ctx['turn']+1)
  if 0<=left<=plan_turns+1:
   if any((slash_rows[0]<=y<=slash_rows[1]for y in rows)):
    return True
 return False
def item_equivalent_value(ctx,item,mode,leader_area,behind):
 kind=item.get('type','')
 rules=ctx['rules']
 if kind=='saber':
  rows=rules.get('saberRows',2)
  try:
   rows=int(rows[0]if isinstance(rows,(list,tuple))else rows)
  except(TypeError,ValueError):
   rows=2
  value=0.55*rows*ctx['width']
 elif kind=='megabomb':
  value=0.5*max(1,len(ctx['others']))*min(leader_area,25)
 elif kind=='hourglass':
  value=22 if behind else 12
 elif kind=='bomb':
  value=0.6*min(leader_area,16)
 elif kind=='wing':
  value=7
 else:
  value=ITEM_VALUE.get(kind,2)
 return value*mode['itemMul']
def item_enemy_arrival(ctx,item,enemy_maps):
 if not enemy_maps:
  return INF
 w,h=(ctx['width'],ctx['height'])
 size=ITEM_SIZE.get(item.get('type'),1)
 cells=[]
 for dy in range(size):
  for dx in range(size):
   x,y=(item['x']+dx,item['y']+dy)
   if 0<=x<w and 0<=y<h:
    cells.append(y*w+x)
 best=INF
 for enemy,dist in enemy_maps:
  d=min((dist[c]for c in cells if dist[c]>=0),default=-1)
  if d>=0:
   best=min(best,enemy_turns_to_cell(enemy,d))
 return best
def prepare_item_value_lookup(ctx,mode,counts,enemy_maps=None):
 players=ctx['state'].get('players',[])
 my_idx=ctx['me']['index']
 enemy_counts=[counts[p['index']]for p in players if p.get('index')!=my_idx and 0<=p.get('index',-1)<len(counts)]
 leader_area=max(enemy_counts,default=0)
 behind=any((counts[my_idx]<v for v in enemy_counts))
 specs,cells=([],{})
 actual=ctx['state'].get('items',[])
 upcoming=ctx['state'].get('upcoming',ctx['state'].get('upcomingItems',[]))
 for item,is_upcoming in[(it,False)for it in actual]+[(it,True)for it in upcoming]:
  size=ITEM_SIZE.get(item.get('type'),1)
  rival=item_enemy_arrival(ctx,item,enemy_maps)
  spawn_in=max(0,int(item.get('turn',ctx['turn'])-ctx['turn']+1))if is_upcoming else 0
  value=item_equivalent_value(ctx,item,mode,leader_area,behind)
  spec_id=len(specs)
  specs.append((is_upcoming,spawn_in,rival,value))
  for dy in range(size):
   for dx in range(size):
    x,y=(item['x']+dx,item['y']+dy)
    if 0<=x<ctx['width']and 0<=y<ctx['height']:
     cells.setdefault(y*ctx['width']+x,[]).append(spec_id)
 ctx['_itemSpecs']=specs
 ctx['_itemCells']=cells
def route_item_value(ctx,route_cells,mode,counts,max_turns,enemy_maps=None):
 if not route_cells:
  return 0.0
 specs=ctx.get('_itemSpecs')
 cell_specs=ctx.get('_itemCells')
 if specs is None or cell_specs is None:
  return 0.0
 seen=set()
 total=0.0
 wing=ctx['me'].get('wing',0)
 for step,cell in enumerate(route_cells,1):
  for spec_id in cell_specs.get(cell,()):
   if spec_id in seen:
    continue
   seen.add(spec_id)
   upcoming,spawn_in,rival,value=specs[spec_id]
   arrival=turns_for_steps(step,wing)
   if upcoming:
    if arrival>=spawn_in and arrival<max(spawn_in,rival):
     total+=0.9*value
   elif arrival<rival:
    total+=value
 return total
def projected_trail_after_route(ctx,route_cells):
 cleared=set()
 result=[]
 my_idx=ctx['me']['index']
 wing=ctx['me'].get('wing',0)
 return_eta={}
 for step,cell in enumerate(route_cells,1):
  victim=ctx['enemyTrail'].get(cell)
  if victim is not None:
   victim_idx=victim['index']
   eta=return_eta.get(victim_idx)
   if eta is None:
    eta=turns_until_enemy_can_return_home(ctx,victim)
    return_eta[victim_idx]=eta
   arrival=turns_for_steps(step,wing)
   if victim_idx in cleared or arrival>=eta:
    if ctx['grid'][cell]!=my_idx and cell not in ctx['myTrail']:
     result.append(cell)
   else:
    cleared.add(victim_idx)
   continue
  if ctx['grid'][cell]!=my_idx and cell not in ctx['myTrail']:
   result.append(cell)
 return result
def rough_route_area(ctx,trail_cells,a=1,b=1):
 if not trail_cells:
  return 0.0
 return max(float(a*b),float(len(trail_cells)))
def validate_plan(ctx,directions,route_cells,new_trail,mode,enemy_maps,occupied,max_trail,allow_unsafe=False):
 if not directions:
  return None
 if OPPOSITE.get(directions[0])==ctx['me'].get('lastDir'):
  return None
 for i in range(1,len(directions)):
  if OPPOSITE[directions[i]]==directions[i-1]:
   return None
 if len(ctx['myTrail'])+len(set(new_trail))>max_trail:
  return None
 turns=turns_for_steps(len(directions),ctx['me'].get('wing',0))
 if turns>mode['remaining']:
  return None
 full_trail=set(ctx['myTrail'])
 full_trail.update(new_trail)
 full_trail_list=list(full_trail)
 if pending_slash_hits(ctx,full_trail_list,turns):
  return None
 slack=INF
 if full_trail_list:
  enemy_time=earliest_enemy_arrival(ctx,full_trail_list,enemy_maps)
  if enemy_time!=INF:
   slack=enemy_time-turns
   if not allow_unsafe and slack<mode['margin']:
    return None
 if route_cells:
  if route_cells[0]in ctx.get('enemyReach1',()):
   return None
  if ctx['me'].get('wing',0)>0 and len(route_cells)>1:
   if route_cells[1]in ctx.get('enemyReach2',()):
    return None
  if mode['avoidEnemy']:
   for cell in route_cells[:2]:
    if cell in occupied:
     return None
 return{'turns':turns,'slack':slack,'trail':full_trail_list}
def make_plan_candidate(ctx,directions,route_cells,new_trail,mode,enemy_maps,occupied,max_trail,counts,extra_item=0.0,extra_cut=0.0,emergency=False,rough=0.0,label='loop',maze_value=0.0):
 if enemy_maps:
  checked=validate_plan(ctx,directions,route_cells,new_trail,mode,enemy_maps,occupied,max_trail,allow_unsafe=emergency)
  if checked is None:return None
 else:
  if not directions or len(ctx['myTrail'])+len(set(new_trail))>max_trail:return None
  if OPPOSITE.get(directions[0])==ctx['me'].get('lastDir'):return None
  for i in range(1,len(directions)):
   if OPPOSITE.get(directions[i])==directions[i-1]:return None
  turns=turns_for_steps(len(directions),ctx['me'].get('wing',0))
  if turns>mode['remaining']:return None
  checked={'turns':turns,'slack':INF}
  
 item_value=route_item_value(ctx,route_cells,mode,counts,mode['maxTurns'],enemy_maps) if enemy_maps else 0.0
 return{'directions':directions,'route_cells':route_cells,'new_trail':new_trail,'turns':checked['turns'],'slack':checked['slack'],'item_value':item_value+extra_item,'cut_value':0.0,'rough':rough,'maze_value':float(maze_value),'label':label}
def rectangular_candidates(ctx,mode,home_field,enemy_maps,occupied,max_trail,counts):
 candidates=[]
 start=current_index(ctx)
 my_idx=ctx['me']['index']
 max_out=min(mode['maxOut'],max(1,max_trail-len(ctx['myTrail'])-1))
 max_side=mode['maxSide']
 current_dir=ctx['me'].get('lastDir')
 for first_dir in DIRECTIONS:
  if current_dir and OPPOSITE[first_dir]==current_dir:
   continue
  straight_cells=[]
  straight_dirs=[]
  straight_trail=[]
  cur=start
  left_home=ctx['grid'][cur]!=my_idx
  if cur in ctx['myTrail']:
   left_home=True
  for a in range(1,max_out+1):
   nxt=next_cell(ctx,cur,first_dir)
   if nxt<0 or nxt in ctx['myTrail']or nxt in occupied:
    break
   if nxt in straight_cells:
    break
   straight_cells.append(nxt)
   straight_dirs.append(first_dir)
   if ctx['grid'][nxt]!=my_idx:
    left_home=True
   straight_trail=projected_trail_after_route(ctx,straight_cells)
   if ctx['grid'][nxt]==my_idx and left_home:
    cand=make_plan_candidate(ctx,list(straight_dirs),list(straight_cells),list(straight_trail),mode,enemy_maps,occupied,max_trail,counts,rough=rough_route_area(ctx,straight_trail,a,1),label='straight-close')
    if cand:
     candidates.append(cand)
    break
   cur=nxt
   if straight_trail:
    forbidden=set(ctx['myTrail'])|set(straight_cells)
    home=reconstruct_home_route(ctx,cur,home_field,forbidden,first_dir,occupied)
    if home is not None:
     ret_dirs,ret_cells=home
     all_dirs=straight_dirs+ret_dirs
     all_cells=straight_cells+ret_cells
     added=projected_trail_after_route(ctx,all_cells)
     cand=make_plan_candidate(ctx,all_dirs,all_cells,added,mode,enemy_maps,occupied,max_trail,counts,rough=rough_route_area(ctx,added,a,1),label='line-home')
     if cand:
      candidates.append(cand)
   if not straight_trail:
    continue
   for turn_dir in(CW_DIR[first_dir],CCW_DIR[first_dir]):
    side_cells=[]
    side_dirs=[]
    side_trail=[]
    side_cur=cur
    side_closed=False
    for b in range(1,max_side+1):
     side_next=next_cell(ctx,side_cur,turn_dir)
     if side_next<0 or side_next in ctx['myTrail']or side_next in occupied or(side_next in straight_cells)or(side_next in side_cells):
      break
     side_cells.append(side_next)
     side_dirs.append(turn_dir)
     if ctx['grid'][side_next]==my_idx:
      side_closed=True
     out_cells=straight_cells+side_cells
     out_dirs=straight_dirs+side_dirs
     out_trail=projected_trail_after_route(ctx,out_cells)
     if side_closed:
      cand=make_plan_candidate(ctx,out_dirs,out_cells,out_trail,mode,enemy_maps,occupied,max_trail,counts,rough=rough_route_area(ctx,out_trail,a,b),label='rectangle-close')
      if cand:
       candidates.append(cand)
      break
     forbidden=set(ctx['myTrail'])|set(out_cells)
     home=reconstruct_home_route(ctx,side_next,home_field,forbidden,turn_dir,occupied)
     if home is not None:
      ret_dirs,ret_cells=home
      all_dirs=out_dirs+ret_dirs
      all_cells=out_cells+ret_cells
      added=projected_trail_after_route(ctx,all_cells)
      cand=make_plan_candidate(ctx,all_dirs,all_cells,added,mode,enemy_maps,occupied,max_trail,counts,rough=rough_route_area(ctx,added,a,b),label='rectangle-home')
      if cand:
       candidates.append(cand)
     side_cur=side_next
 return candidates
def direct_target_candidate(ctx,mode,target_path,target_value,label,home_field,enemy_maps,occupied,max_trail,counts,cut=False):
 if not target_path:
  return None
 route_to_target=target_path.get('fullPath',[])
 directions=target_path.get('directions',[])
 if not route_to_target or not directions:
  return None
 left_home=bool(ctx['myTrail'])or ctx['grid'][current_index(ctx)]!=ctx['me']['index']
 my_index=ctx['me']['index']
 for cell in route_to_target:
  if ctx['grid'][cell]==my_index:
   if left_home:
    return None
  else:
   left_home=True
 end=route_to_target[-1]
 new_trail=projected_trail_after_route(ctx,route_to_target)
 forbidden=set(ctx['myTrail'])|set(route_to_target)
 home=reconstruct_home_route(ctx,end,home_field,forbidden,directions[-1],occupied)
 if home is None:
  return None
 ret_dirs,ret_cells=home
 all_dirs=directions+ret_dirs
 all_cells=route_to_target+ret_cells
 added=projected_trail_after_route(ctx,all_cells)
 return make_plan_candidate(ctx,all_dirs,all_cells,added,mode,enemy_maps,occupied,max_trail,counts,extra_item=0.0,extra_cut=0.0,rough=rough_route_area(ctx,added,len(directions),1),label=label)
def maze_topology_candidates(ctx,mode,home_field,enemy_maps,occupied,max_trail,counts):
 maze=ctx['maze'];total=ctx['width']*ctx['height']
 budget=max(1,max_trail-len(ctx['myTrail'])-3)
 phase=ctx.get('strategyPhase')
 if phase=='SPAWN_EXPANSION':horizon=ctx.get('spawnRadius',22)+20
 elif phase=='MIDGAME_CENTER':horizon=min(88,max(ctx['width'],ctx['height'])+34)
 else:horizon=min(72,max(ctx['width'],ctx['height'])+18)
 max_steps=min(total,horizon,budget)
 paths=maze_weighted_targets(ctx,mode,occupied,max_steps,limit=28)
 results=[];seen_targets=set();sx,sy=index_to_coord(ctx,current_index(ctx))
 start_center=abs(sx-(ctx['width']-1)/2)+abs(sy-(ctx['height']-1)/2)
 for path in paths:
  target=path['target']
  if target in seen_targets:continue
  seen_targets.add(target);degree=maze['degree'][target]
  label='chokepoint' if maze['articulation'][target] else 'maze-sweep' if degree<=2 else 'maze-junction'
  candidate=direct_target_candidate(ctx,mode,path,0.0,label,home_field,enemy_maps,occupied,max_trail,counts,cut=False)
  if candidate is None:continue
  x,y=index_to_coord(ctx,target)
  center_dist=abs(x-(ctx['width']-1)/2)+abs(y-(ctx['height']-1)/2)
  center_progress=max(0.0,start_center-center_dist)
  sd=ctx.get('spawnDist',[]);outward=max(0.0,(sd[target]-ctx.get('spawnRadius',22))) if target<len(sd) and sd[target]>=0 else 0.0
  potential=maze_frontier_potential(ctx,target,7)
  center_boost=(0.18*center_progress+0.12*outward) if phase=='MIDGAME_CENTER' else 0.04*center_progress
  candidate['maze_value']=min(42.0,0.52*path['priority']+0.68*potential+center_boost)
  candidate['center_progress']=center_progress;candidate['target_cell']=target
  results.append(candidate)
 results.sort(key=lambda c:(c.get('maze_value',0.0)+c.get('rough',0.0))/(c.get('turns',0)+1.8),reverse=True)
 return results[:28]
def central_route_candidates(ctx,mode,home_field,enemy_maps,occupied,max_trail,counts):
 """Advance toward the center in safe stages instead of one oversized raid."""
 if ctx.get('strategyPhase')=='SPAWN_EXPANSION':return []
 w,h=ctx['width'],ctx['height'];cx,cy=(w-1)/2,(h-1)/2
 sx,sy=index_to_coord(ctx,current_index(ctx));start_dist=abs(sx-cx)+abs(sy-cy)
 budget=max(1,max_trail-len(ctx['myTrail'])-4)
 max_out=24 if ctx.get('strategyPhase')=='MIDGAME_CENTER' else 30
 paths=maze_weighted_targets(ctx,mode,occupied,min(72,budget),limit=240)
 ranked=[]
 for path in paths:
  target=path['target']
  if ctx['grid'][target]!=EMPTY or path['dist']<5 or path['dist']>max_out:continue
  x,y=index_to_coord(ctx,target);cd=abs(x-cx)+abs(y-cy)
  progress=max(0.0,start_dist-cd)
  if progress<3:continue
  ranked.append((1.1*progress-0.48*path['dist']+0.16*path['priority'],path,progress))
 ranked.sort(key=lambda z:z[0],reverse=True)
 result=[];seen=set()
 for rank,path,progress in ranked:
  target=path['target']
  if target in seen:continue
  seen.add(target)
  candidate=direct_target_candidate(ctx,mode,path,0.0,'center-push',home_field,enemy_maps,occupied,max_trail,counts,cut=False)
  if candidate is None:continue
  sd=ctx.get('spawnDist',[]);outward=max(0.0,sd[target]-ctx.get('spawnRadius',22)) if target<len(sd) and sd[target]>=0 else 0.0
  x,y=index_to_coord(ctx,target);cd=abs(x-cx)+abs(y-cy)
  candidate['maze_value']=min(46.0,15.0+0.95*progress+0.18*outward+0.55*maze_frontier_potential(ctx,target,8))
  candidate['center_progress']=progress;candidate['target_cell']=target
  result.append(candidate)
  if len(result)>=8:break
 return result
def maze_snake_candidates(ctx,mode,home_field,enemy_maps,occupied,max_trail,counts,depth_limit=24,beam_width=20):
 start=current_index(ctx);my_idx=ctx['me']['index'];last=ctx['me'].get('lastDir')
 budget=max(4,max_trail-len(ctx['myTrail'])-2)
 max_depth=min(depth_limit,budget)
 phase=ctx.get('strategyPhase');maze=ctx['maze']
 sx,sy=index_to_coord(ctx,start)
 start_center=abs(sx-(ctx['width']-1)/2)+abs(sy-(ctx['height']-1)/2)
 beam=[{'cell':start,'cells':[],'directions':[],'visited':set(),'left_home':bool(ctx['myTrail'])or ctx['grid'][start]!=my_idx,'last_dir':last,'value':0.0}]
 results=[];seen_signatures=set()
 for _depth in range(max_depth):
  expanded=[]
  for node in beam:
   cell=node['cell']
   for direction in DIRECTIONS:
    if node['last_dir'] and OPPOSITE[direction]==node['last_dir']:continue
    nxt=next_cell(ctx,cell,direction)
    if nxt<0 or nxt in ctx['myTrail'] or nxt in occupied or nxt in node['visited']:continue
    owner=ctx['grid'][nxt]
    if node['left_home'] and owner==my_idx:
     new_cells=node['cells']+[nxt];new_dirs=node['directions']+[direction]
     added=projected_trail_after_route(ctx,new_cells)
     if added:
      cand=make_plan_candidate(ctx,new_dirs,new_cells,added,mode,enemy_maps,occupied,max_trail,counts,rough=rough_route_area(ctx,added,len(new_cells),1),label='snake-close',maze_value=min(8.0,node['value']+1.4))
      if cand:results.append(cand)
     continue
    new_left=node['left_home'] or owner!=my_idx
    new_cells=node['cells']+[nxt];new_dirs=node['directions']+[direction]
    added=projected_trail_after_route(ctx,new_cells)
    if added:
     forbidden=set(ctx['myTrail']);forbidden.update(new_cells)
     home=reconstruct_home_route(ctx,nxt,home_field,forbidden,direction,occupied)
     if home is not None:
      ret_dirs,ret_cells=home;all_dirs=new_dirs+ret_dirs;all_cells=new_cells+ret_cells
      full_added=projected_trail_after_route(ctx,all_cells)
      cand=make_plan_candidate(ctx,all_dirs,all_cells,full_added,mode,enemy_maps,occupied,max_trail,counts,rough=rough_route_area(ctx,full_added,len(new_cells),1),label='snake',maze_value=min(8.0,node['value']+1.0))
      if cand:results.append(cand)
    degree=maze['degree'][nxt]
    frontier=sum(1 for n in maze['neighbors'][nxt] if ctx['grid'][n]!=my_idx and n not in ctx['myTrail'])
    step_value=1.0 if owner==EMPTY else 0.45
    if owner>=0 and owner!=my_idx:step_value+=0.45
    if degree>=3:step_value+=0.8+0.12*min(3,degree-3)
    elif degree==2:step_value+=0.48
    elif degree==1:step_value-=0.25
    if maze['articulation'][nxt]:step_value+=0.75
    step_value+=0.20*min(3,frontier)
    if phase=='MIDGAME_CENTER':
     x,y=index_to_coord(ctx,nxt)
     cd=abs(x-(ctx['width']-1)/2)+abs(y-(ctx['height']-1)/2)
     step_value+=0.18*max(-1.0,min(1.0,(start_center-cd)/8.0))
     sd=ctx.get('spawnDist',[])
     if nxt<len(sd) and sd[nxt]>ctx.get('spawnRadius',22):step_value+=0.18
    elif phase=='SPAWN_EXPANSION':
     sd=ctx.get('spawnDist',[])
     if nxt<len(sd) and sd[nxt]>ctx.get('spawnRadius',22)*0.60:step_value+=0.12
    if is_near_active_enemy(ctx,nxt):step_value-=1.2
    new_node={'cell':nxt,'cells':new_cells,'directions':new_dirs,'visited':node['visited']|{nxt},'left_home':new_left,'last_dir':direction,'value':node['value']+step_value}
    signature=(new_dirs[0] if new_dirs else direction,tuple(new_cells[-5:]))
    if signature not in seen_signatures:
     seen_signatures.add(signature);expanded.append(new_node)
  if not expanded:break
  def beam_score(n):
   score=n['value']/((len(n['cells'])+2.0)**0.56)+0.12*len(n['cells'])
   if phase=='MIDGAME_CENTER':
    x,y=index_to_coord(ctx,n['cell']);cd=abs(x-(ctx['width']-1)/2)+abs(y-(ctx['height']-1)/2)
    score+=0.22*max(0.0,start_center-cd)
   return score
  expanded.sort(key=beam_score,reverse=True)
  next_beam=[];per_first={}
  for node in expanded:
   first=node['directions'][0]
   if per_first.get(first,0)>=4:continue
   next_beam.append(node);per_first[first]=per_first.get(first,0)+1
   if len(next_beam)>=beam_width:break
  beam=next_beam
 results.sort(key=lambda c:(c.get('rough',0.0)+c.get('maze_value',0.0))/(c.get('turns',0)+1.8),reverse=True)
 return results[:36]
def item_hunt_candidates(ctx,mode,home_field,enemy_maps,occupied,max_trail,counts):
 specs=ctx.get('_itemSpecs',[])
 cell_specs=ctx.get('_itemCells',{})
 if not specs or not cell_specs:
  return[]
 start=current_index(ctx)
 radius=mode['itemRadius']*(2 if ctx['me'].get('wing',0)else 1)
 valid=lambda cell:cell not in ctx['myTrail']and cell not in occupied and(not mode['avoidEnemy']or not is_near_active_enemy(ctx,cell))
 paths=bfs_many_goals(ctx,start,ctx['me'].get('lastDir'),valid,radius,cell_specs)
 result=[]
 for spec_id,path in paths.items():
  upcoming,spawn_in,rival,_=specs[spec_id]
  arrival=turns_for_steps(path['dist'],ctx['me'].get('wing',0))
  if upcoming and arrival<spawn_in:
   continue
  candidate=direct_target_candidate(ctx,mode,path,0.0,'item',home_field,enemy_maps,occupied,max_trail,counts,cut=False)
  if candidate is not None and candidate['item_value']>0:
   result.append(candidate)
 return result
def continuation_candidate(ctx,mode,enemy_maps,occupied,max_trail,counts):
 memory=PLAN_MEMORY
 if not memory or memory.get('turn')+1!=ctx['turn']:
  return None
 if current_index(ctx)!=memory.get('expected'):
  return None
 directions=memory.get('directions',[])
 cells=memory.get('cells',[])
 if not directions or len(directions)!=len(cells):
  return None
 pos=current_index(ctx)
 for direction,cell in zip(directions,cells):
  nxt=next_cell(ctx,pos,direction)
  if nxt!=cell:
   return None
  pos=nxt
 trail=projected_trail_after_route(ctx,cells)
 return make_plan_candidate(ctx,list(directions),list(cells),trail,mode,enemy_maps,occupied,max_trail,counts,rough=rough_route_area(ctx,trail),label='continuation')
def plan_pick(ctx):
 mode=choose_strategy_mode(ctx)
 expanding=build_spawn_profile(ctx);phase=ctx.get('strategyPhase')
 if phase=='SPAWN_EXPANSION':
  mode['itemMul']=0.52;mode['itemRadius']=18;mode['maxOut']=20;mode['maxSide']=22
  snake_depth=24;snake_beam=18
 elif phase=='MIDGAME_CENTER':
  mode['itemMul']=1.75;mode['itemRadius']=44;mode['maxOut']=22;mode['maxSide']=24
  snake_depth=28;snake_beam=22
 else:
  mode['itemMul']=2.45;mode['itemRadius']=44;mode['maxOut']=18;mode['maxSide']=20
  snake_depth=24;snake_beam=18
 mode['cutValue']=0.0;mode['huntRadius']=0;mode['avoidEnemy']=True
 mode['enemyWeight']=1.0;mode['leaderBonus']=0.0;mode['margin']=max(2,mode.get('margin',2))
 ctx['leaderIndex']=mode.get('leaderIndex',-1)
 max_trail=max(1,int(ctx['rules'].get('maxTrail',120)or 120))
 remaining_trail=max(1,max_trail-len(ctx['myTrail']))
 home_field=build_home_field(ctx,min(ctx['width']*ctx['height'],remaining_trail))
 _,_,occupied=home_field;counts=territory_counts(ctx);current=current_index(ctx);me=ctx['me']
 if me.get('trail'):
  home_now=reconstruct_home_route(ctx,current,home_field,set(ctx['myTrail']),me.get('lastDir'),occupied)
  if home_now is not None and home_now[0]:
   home_steps=len(home_now[0]);home_turns=turns_for_steps(home_steps,me.get('wing',0))
   urgent_slash=pending_slash_hits(ctx,list(ctx['myTrail']),home_turns+1)
   enemy_eta=turns_until_enemy_can_touch_trail(ctx,ctx['myTrail'])
   near_limit=len(ctx['myTrail'])+home_steps>=max_trail-2
   endgame=home_turns+1>=mode['remaining']
   exposed=enemy_eta<=home_turns+mode['margin']
   if urgent_slash or near_limit or endgame or exposed:
    return{'directions':home_now[0],'mode':mode['name'],'score':-2.0,'label':'forced-safe-home'}
 # Grow larger loops first; item routes are considered in every phase, with phase-scaled value.
 candidates=rectangular_candidates(ctx,mode,home_field,[],occupied,max_trail,counts)
 candidates.extend(maze_topology_candidates(ctx,mode,home_field,[],occupied,max_trail,counts))
 candidates.extend(central_route_candidates(ctx,mode,home_field,[],occupied,max_trail,counts))
 candidates.extend(maze_snake_candidates(ctx,mode,home_field,[],occupied,max_trail,counts,depth_limit=snake_depth,beam_width=snake_beam))
 threat_targets=set(ctx['myTrail']);max_candidate_turns=1
 for candidate in candidates:
  threat_targets.update(candidate['new_trail']);max_candidate_turns=max(max_candidate_turns,candidate['turns'])
 all_items=ctx['state'].get('items',[])+ctx['state'].get('upcoming',ctx['state'].get('upcomingItems',[]))
 for item in all_items:
  size=ITEM_SIZE.get(item.get('type'),1)
  for dy in range(size):
   for dx in range(size):
    x,y=item['x']+dx,item['y']+dy
    if 0<=x<ctx['width'] and 0<=y<ctx['height']:threat_targets.add(y*ctx['width']+x)
 enemy_step_cap=min(ctx['width']*ctx['height'],max(80,max_candidate_turns+24,mode['itemRadius']+24))
 enemy_maps=build_enemy_distance_maps(ctx,list(threat_targets),enemy_step_cap)
 prepare_item_value_lookup(ctx,mode,counts,enemy_maps)
 safe=[]
 for candidate in candidates:
  checked=validate_plan(ctx,candidate['directions'],candidate['route_cells'],candidate['new_trail'],mode,enemy_maps,occupied,max_trail,allow_unsafe=False)
  if checked is None:continue
  candidate['slack']=checked['slack']
  candidate['item_value']=route_item_value(ctx,candidate['route_cells'],mode,counts,mode['maxTurns'],enemy_maps)
  candidate['cut_value']=0.0
  safe.append(candidate)
 candidates=safe
 # Do not wait until the spawn pocket is exhausted: collect useful items while advancing.
 candidates.extend(item_hunt_candidates(ctx,mode,home_field,enemy_maps,occupied,max_trail,counts))
 continuation=continuation_candidate(ctx,mode,enemy_maps,occupied,max_trail,counts)
 if continuation is not None:candidates.append(continuation)
 if me.get('trail'):
  home=reconstruct_home_route(ctx,current,home_field,set(ctx['myTrail']),me.get('lastDir'),occupied)
  if home is not None:
   dirs,cells=home
   emergency=make_plan_candidate(ctx,dirs,cells,projected_trail_after_route(ctx,cells),mode,enemy_maps,occupied,max_trail,counts,emergency=True,rough=0.0,label='emergency-home')
   if emergency:emergency['emergency']=True;candidates.append(emergency)
 if not candidates:
  if me.get('trail'):
   home=reconstruct_home_route(ctx,current,home_field,set(ctx['myTrail']),me.get('lastDir'),occupied)
   if home and home[0]:return{'directions':home[0],'mode':mode['name'],'score':-1.0,'label':'forced-home'}
  return None
 candidates.sort(key=lambda c:(c['rough']+c['item_value']+c['cut_value']+c.get('maze_value',0.0))/(c['turns']+1.8),reverse=True)
 total=ctx['width']*ctx['height'];exact_limit=14 if total<=3000 else 10 if total<=10000 else 8
 shortlist=[];used_dirs=set()
 for wanted in('continuation','center-push','item','chokepoint','maze-sweep','maze-junction','snake'):
  chosen=next((c for c in candidates if wanted in c.get('label','')),None)
  if chosen is not None and chosen not in shortlist and len(shortlist)<exact_limit:
   shortlist.append(chosen)
   if chosen.get('directions'):used_dirs.add(chosen['directions'][0])
 for candidate in candidates:
  if len(shortlist)>=exact_limit:break
  first=candidate['directions'][0] if candidate.get('directions') else 'stay'
  if first not in used_dirs:shortlist.append(candidate);used_dirs.add(first)
 if len(shortlist)<exact_limit:
  for candidate in candidates:
   if candidate not in shortlist:shortlist.append(candidate)
   if len(shortlist)>=exact_limit:break
 if total<=3000:build_voronoi_map(ctx)
 best=None
 for candidate in shortlist:
  area=estimate_enclosed_area(ctx,candidate['new_trail'],mode['enemyWeight'],mode.get('leaderIndex'),mode.get('leaderBonus',0.0))
  frontier=voronoi_frontier_bonus(ctx,candidate['route_cells'])
  spawn_gain,center_gain=capture_region_gains(ctx,candidate['new_trail'])
  center_progress=candidate.get('center_progress',center_route_progress(ctx,candidate['route_cells']))
  remote=candidate.get('remote_steps',remote_route_steps(ctx,candidate['route_cells']))
  if phase=='SPAWN_EXPANSION':
   local_bonus=3.2*spawn_gain+0.18*center_progress-0.08*remote
  elif phase=='MIDGAME_CENTER':
   local_bonus=0.35*spawn_gain+4.1*center_gain+1.85*center_progress+0.28*remote
  else:
   local_bonus=0.35*spawn_gain+1.3*center_gain+0.55*center_progress
  value=area+candidate['item_value']+0.22*frontier+candidate.get('maze_value',0.0)+local_bonus
  score=value/((candidate['turns']+2.0)**0.74)
  # Suppress tiny loops when there is still safe, uncaptured space to work with.
  if phase!='ITEM_ENDGAME' and area<12 and candidate['turns']>5:score*=0.62
  if candidate.get('slack',INF)!=INF:
   score+=min(8.0,max(0.0,candidate['slack']-mode['margin']))*0.022
   if candidate['slack']<=mode['margin']+1:score*=0.90
  candidate['area']=area;candidate['frontier']=frontier;candidate['spawn_gain']=spawn_gain;candidate['center_gain']=center_gain;candidate['center_progress']=center_progress;candidate['score']=score
  if best is None or(score,area,candidate['slack'])>(best['score'],best['area'],best['slack']):best=candidate
 if best is None:return None
 old_best=next((c for c in shortlist if c.get('label')=='continuation' and c.get('score',0.0)>=0.92*best['score']),None)
 if old_best is not None:best=old_best
 best['mode']=mode['name'];best['scoreGap']=mode['scoreGap']
 return best
def choose_insane_move(state,player_id,config=None,turn=None):
 config=config if config is not None else state.get('config')or{}
 turn=turn if turn is not None else state.get('turn',0)
 normalized_state=dict(state)
 normalized_state['upcoming']=state.get('upcoming',state.get('upcomingItems',[]))
 normalized_state['slashes']=state.get('slashes',state.get('pendingSlashes',[]))
 normalized_state['items']=state.get('items',[])
 normalized_state['obstacles']=state.get('obstacles',[])
 player=next((p for p in normalized_state.get('players',[])if p.get('playerId')==player_id),None)
 if player is None or player.get('stun',0)>0 or player.get('freeze',0)>0:
  return None
 grid=make_owner_grid(normalized_state)
 me={'index':player['index'],'playerId':player['playerId'],'x':player['x'],'y':player['y'],'lastDir':player.get('lastDir'),'trail':player.get('trail',[]),'wing':player.get('wing',0)}
 context=make_context(normalized_state,config,turn,me,grid)
 chosen=plan_pick(context)
 if chosen is None:
  first_direction=insane_pick(context)
  if not first_direction:
   return None
  chosen_directions=[first_direction]
 else:
  chosen_directions=list(chosen.get('directions',[]))
  if not chosen_directions:
   first_direction=insane_pick(context)
   if not first_direction:
    return None
   chosen_directions=[first_direction]
 move=chosen_directions[0]if chosen_directions else None
 if player.get('wing',0)>0 and len(chosen_directions)>=2:
  first_direction,second_direction=chosen_directions[:2]
  if OPPOSITE.get(second_direction)!=first_direction and is_legal_direction(context,first_direction):
   first_cell=next_cell(context,current_index(context),first_direction)
   second_cell=next_cell(context,first_cell,second_direction)if first_cell>=0 else-1
   ships={coord_to_index(context,p['x'],p['y'])for p in context['others']}
   first_ok=first_cell>=0 and first_cell not in context['myTrail']and(first_cell not in ships)and(first_cell not in context['enemyReach1'])
   second_ok=second_cell>=0 and second_cell not in context['myTrail']and(second_cell not in ships)and(second_cell not in context['enemyReach2'])
   if first_ok and second_ok:
    move=[first_direction,second_direction]
 global PLAN_MEMORY,LAST_PLAN_INFO
 LAST_PLAN_INFO={'label':chosen.get('label','unknown')if chosen else 'fallback','mode':chosen.get('mode','unknown')if chosen else 'fallback','score':round(float(chosen.get('score',0.0)),3)if chosen else 0.0,'maze_nodes':len(context['maze']['junctions']),'chokepoints':len(context['maze']['chokepoints']),'leader':context.get('leaderIndex',-1),'gap':round(float(chosen.get('scoreGap',0)) if chosen else 0.0,1),'target':chosen.get('target_enemy',-1)if chosen else -1,'phase':context.get('strategyPhase','?'),'local_empty':context.get('spawnEmpty',-1),'center_gain':round(float(chosen.get('center_gain',0.0)),1)if chosen else 0,'center_progress':round(float(chosen.get('center_progress',0.0)),1)if chosen else 0,'area':round(float(chosen.get('area',0.0)),1)if chosen else 0,'route_steps':len(chosen.get('route_cells',[]))if chosen else 0,'target_cell':chosen.get('target_cell',-1)if chosen else -1,'spawn_gain':round(float(chosen.get('spawn_gain',0.0)),1)if chosen else 0,'item_value':round(float(chosen.get('item_value',0.0)),1)if chosen else 0}
 if chosen is not None and chosen.get('route_cells')and chosen.get('directions'):
  used=len(move)if isinstance(move,list)else 1 if move else 0
  if used and len(chosen['route_cells'])>used:
   PLAN_MEMORY={'turn':int(turn),'expected':chosen['route_cells'][used-1],'directions':list(chosen['directions'][used:]),'cells':list(chosen['route_cells'][used:])}
  else:
   PLAN_MEMORY=None
 else:
  PLAN_MEMORY=None
 return move
def decide(state):
 try:
  return choose_insane_move(state,ME)
 except Exception as err:
  print('Loi decide:',err,flush=True)
  return None
def main():
 print('TITAN MAZE V4 | Bigger Expansion + Midgame Center + Item Farming',ME,'bat dau tran',GAME,flush=True)
 last_turn=-1
 while True:
  try:
   status=get('/status')
   if status['status']=='finished':
    print('Tran da ket thuc o luot',status['currentTurn'],flush=True)
    return
   if status['status']=='playing' and status['currentTurn']!=last_turn:
    turn_no=status['currentTurn']
    state=get('/state')
    if not isinstance(state.get('config'),dict):
     state['config']={}
    state['turn']=turn_no
    if status.get('maxTurns')is not None:
     state['config']['maxTurns']=status['maxTurns']
    move=decide(state)
    if isinstance(move,list):
     act('move',{'directions':move[:2]})
     print('Luot',turn_no+1,'di',move,LAST_PLAN_INFO,flush=True)
    elif move:
     act('move',{'direction':move})
     print('Luot',turn_no+1,'di',move,LAST_PLAN_INFO,flush=True)
    last_turn=turn_no
   time.sleep(min(0.25,max(0.05,(status.get('tickInterval')or 500)/4000)))
  except Exception as err:
   print('Loi:',err,flush=True)
   time.sleep(1)
if __name__=='__main__':
 main()
