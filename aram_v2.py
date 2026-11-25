import json
import math
import os
import time
import urllib.error
import urllib.request
from collections import deque
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
ARAM_ITEM_TIER={'wing':5,'bomb':4,'megabomb':4,'hourglass':3,'saber':2}
EMPTY=-1
INF=math.inf
PLAN_MEMORY=None
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
 open_cells=[i for i,b in enumerate(ctx['blocked'])if not b]
 if open_cells:
  xs=[i%ctx['width']for i in open_cells]
  ys=[i//ctx['width']for i in open_cells]
  ctx['playableArea']=len(open_cells)
  ctx['playableBounds']=(min(xs),min(ys),max(xs),max(ys))
 else:
  ctx['playableArea']=ctx['width']*ctx['height']
  ctx['playableBounds']=(0,0,ctx['width']-1,ctx['height']-1)
 ctx['enemyReach1'],ctx['enemyReach2']=build_enemy_reach(ctx)
 build_static_row_masks(ctx)
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
 best=INF
 cells=list(trail_cells)
 if not cells:
  return best
 for enemy in ctx['others']:
  nearest=INF
  for cell in cells:
   nearest=min(nearest,manhattan(ctx,cell,enemy['x'],enemy['y']))
  speed=2 if enemy.get('wing',0)>0 else 1
  turns=math.ceil(nearest/speed)+max(enemy.get('stun',0),enemy.get('freeze',0))
  best=min(best,turns)
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
 for d in safe:
  cell=next_cell(ctx,current,d)
  victim=ctx['enemyTrail'].get(cell)
  if victim and turns_until_enemy_can_return_home(ctx,victim,1)>1:
   return d
 best_d,best_v=(safe[0],-INF)
 for d in safe:
  cell,value=(current,0.0)
  for step in range(1,9):
   cell=next_cell(ctx,cell,d)
   if cell<0 or cell in ctx['myTrail']or cell in ships:
    break
   owner=ctx['grid'][cell]
   if owner!=me['index']:
    value+=1.9 if owner>=0 else 1.0
   if step==1 and cell in ctx['enemyReach1']:
    value-=4.0
   if cell in ctx['enemyTrail']:
    value+=2.0
  if value>best_v:
   best_d,best_v=(d,value)
 return best_d
MODE_TABLE={'safe':{'maxOut':5,'maxSide':8,'margin':3,'enemyWeight':1.3,'huntRadius':2,'cutValue':12,'itemMul':0.5,'itemRadius':6,'avoidEnemy':True},'balanced':{'maxOut':8,'maxSide':10,'margin':2,'enemyWeight':1.8,'huntRadius':7,'cutValue':16,'itemMul':1.0,'itemRadius':12,'avoidEnemy':True},'attack':{'maxOut':11,'maxSide':13,'margin':1,'enemyWeight':2.6,'huntRadius':14,'cutValue':22,'itemMul':1.7,'itemRadius':20,'avoidEnemy':False}}
ARAM_MODE_TABLE={'safe':{'maxOut':10,'maxSide':15,'margin':3,'enemyWeight':1.55,'huntRadius':2,'cutValue':5,'itemMul':1.2,'itemRadius':22,'avoidEnemy':True},'balanced':{'maxOut':13,'maxSide':17,'margin':2,'enemyWeight':1.85,'huntRadius':3,'cutValue':6,'itemMul':1.45,'itemRadius':27,'avoidEnemy':True},'attack':{'maxOut':15,'maxSide':18,'margin':2,'enemyWeight':2.15,'huntRadius':4,'cutValue':7,'itemMul':1.65,'itemRadius':30,'avoidEnemy':True}}
CW_DIR={'up':'right','right':'down','down':'left','left':'up'}
CCW_DIR={v:k for k,v in CW_DIR.items()}
def territory_counts(ctx):
 counts=[0]*max(4,len(ctx['state'].get('players',[])))
 for cell,owner in enumerate(ctx['grid']):
  if not ctx['blocked'][cell]and 0<=owner<len(counts):
   counts[owner]+=1
 return counts
def choose_strategy_mode(ctx):
 config=ctx.get('config',{})
 max_turns=int(config.get('maxTurns',ctx['state'].get('maxTurns',300))or 300)
 max_turns=max(1,max_turns)
 turn=int(ctx.get('turn',0))
 remaining=max(0,max_turns-turn)
 n=ctx.get('playableArea',ctx['width']*ctx['height'])
 players=ctx['state'].get('players',[])
 counts=territory_counts(ctx)
 my_index=ctx['me']['index']
 scores={}
 for p in players:
  idx=p.get('index',-1)
  if idx<0:
   continue
  fallback=counts[idx]if idx<len(counts)else 0
  score=p.get('score',p.get('points',fallback))
  try:
   scores[idx]=float(score)
  except(TypeError,ValueError):
   scores[idx]=float(fallback)
 my_score=scores.get(my_index,float(counts[my_index]if my_index<len(counts)else 0))
 leader_score=max((v for k,v in scores.items()if k!=my_index),default=my_score)
 gap=my_score-leader_score
 if turn<0.12*max_turns:
  mode='balanced'
 elif remaining<=0.2*max_turns:
  if gap>=0:
   mode='safe'
  elif-gap>0.03*n:
   mode='attack'
  else:
   mode='balanced'
 elif gap>0.08*n:
  mode='safe'
 elif-gap>0.06*n:
  mode='attack'
 else:
  mode='balanced'
 params=dict(MODE_TABLE[mode])
 leader_index=max((idx for idx in scores if idx!=my_index),key=lambda idx:scores[idx],default=-1)
 if gap<-0.03*n:
  params['enemyWeight']=1.95
  params['leaderBonus']=0.85
  params['cutValue']*=1.28
 elif gap>0.03*n:
  params['enemyWeight']=1.7
  params['leaderBonus']=0.25
  params['cutValue']*=0.92
 else:
  params['enemyWeight']=1.85
  params['leaderBonus']=0.48
 params['leaderIndex']=leader_index
 if any((p.get('wing',0)>0 and(not p.get('stun',0))and(not p.get('freeze',0))for p in players if p.get('index')!=my_index)):
  params['margin']+=1
 is_aram=ctx['width']==30 and ctx['height']==30 and n<=700
 if is_aram:
  params.update(ARAM_MODE_TABLE[mode])
  if any((p.get('wing',0)>0 and(not p.get('stun',0))and(not p.get('freeze',0))for p in players if p.get('index')!=my_index)):
   params['margin']+=1
  if gap<-0.03*n:
   params['enemyWeight']=2.1
   params['leaderBonus']=0.65
  elif gap>0.03*n:
   params['enemyWeight']=1.7
   params['leaderBonus']=0.25
  turn_ratio=turn/max_turns
  if turn_ratio<0.18:
   params['aramPhase']='SPAWN_EXPANSION'
  elif remaining<=0.18*max_turns:
   params['aramPhase']='ENDGAME'
  else:
   params['aramPhase']='MIDGAME_CENTER'
  params['aram']=True
 else:
  params['aram']=False
 params['name']=mode
 params['remaining']=remaining
 params['maxTurns']=max_turns
 params['scoreGap']=gap
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
def earliest_enemy_arrival(ctx,cells,enemy_maps,freeze_info=None):
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
   eta=enemy_turns_to_cell(enemy,nearest)
   if freeze_info and enemy.get('index')in freeze_info[2]and eta>freeze_info[0]:
    eta+=freeze_info[1]
   best=min(best,eta)
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
def aram_item_tier(ctx,kind):
 wing=int(ctx['me'].get('wing',0)or 0)
 frozen=sum(1 for p in ctx['others']if p.get('freeze',0)or p.get('stun',0))
 needed=max(1,int(ctx['rules'].get('freezeTargets',2)or 2))
 if frozen>=needed:return{'bomb':6,'megabomb':6,'wing':3,'hourglass':2,'saber':2}.get(kind,0)
 if wing>4:return{'hourglass':6,'bomb':4,'megabomb':4,'wing':3,'saber':2}.get(kind,0)
 if wing>1:return{'hourglass':6,'wing':4,'bomb':4,'megabomb':4,'saber':2}.get(kind,0)
 if wing>0:return{'hourglass':5,'wing':6,'bomb':4,'megabomb':4,'saber':2}.get(kind,0)
 return{'wing':6,'bomb':5,'megabomb':5,'hourglass':4,'saber':2}.get(kind,0)
def item_equivalent_value(ctx,item,mode,leader_area,behind):
 kind=item.get('type','')
 if mode.get('aram'):
  tier=aram_item_tier(ctx,kind)
  aram_values={6:190,5:145,4:105,3:78,2:42}
  return aram_values.get(tier,0)*mode['itemMul']
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
 specs,cells,kinds=([],{},[])
 actual=ctx['state'].get('items',[])
 upcoming=ctx['state'].get('upcoming',ctx['state'].get('upcomingItems',[]))
 for item,is_upcoming in[(it,False)for it in actual]+[(it,True)for it in upcoming]:
  size=ITEM_SIZE.get(item.get('type'),1)
  rival=item_enemy_arrival(ctx,item,enemy_maps)
  spawn_in=max(0,int(item.get('turn',ctx['turn'])-ctx['turn']+1))if is_upcoming else 0
  value=item_equivalent_value(ctx,item,mode,leader_area,behind)
  spec_id=len(specs)
  specs.append((is_upcoming,spawn_in,rival,value))
  kinds.append(item.get('type',''))
  for dy in range(size):
   for dx in range(size):
    x,y=(item['x']+dx,item['y']+dy)
    if 0<=x<ctx['width']and 0<=y<ctx['height']:
     cells.setdefault(y*ctx['width']+x,[]).append(spec_id)
 ctx['_itemSpecs']=specs
 ctx['_itemCells']=cells
 ctx['_itemKinds']=kinds
def aram_route_timing(ctx,route_cells):
 specs,cell_specs=ctx.get('_itemSpecs',[]),ctx.get('_itemCells',{})
 kinds=ctx.get('_itemKinds',[])
 wing=int(ctx['me'].get('wing',0)or 0)
 raw=ctx['rules'].get('wingTurns',[5,10])
 try:duration=min(int(v)for v in raw)if isinstance(raw,(list,tuple))else int(raw)
 except(TypeError,ValueError):duration=5
 turn,capacity,pending,used=0,0,0,False
 picked,timings=set(),[]
 for cell in route_cells:
  if capacity<=0:
   turn+=1
   if pending:wing=max(wing,pending);pending=0
   used=wing>0
   capacity=2 if used else 1
  timings.append(turn)
  for sid in cell_specs.get(cell,()):
   if sid in picked or kinds[sid]!='wing':continue
   upcoming,spawn,rival,_=specs[sid]
   if(turn>=spawn and turn<max(spawn,rival))if upcoming else turn<rival:
    picked.add(sid);pending=max(pending,duration)
  capacity-=1
  if capacity==0 and used:wing=max(0,wing-1)
 return timings
def route_item_value(ctx,route_cells,mode,counts,max_turns,enemy_maps=None):
 if not route_cells:
  return 0.0
 specs=ctx.get('_itemSpecs')
 cell_specs=ctx.get('_itemCells')
 if specs is None or cell_specs is None:
  return 0.0
 seen=set()
 total=0.0
 timings=aram_route_timing(ctx,route_cells)if mode.get('aram')else None
 dynamic_tiers={}
 if timings is not None:
  _,dynamic_order=aram_chain_bonus(ctx,route_cells,mode)
  dynamic_tiers={sid:tier for sid,_,tier in dynamic_order}
  tier_values={6:190,5:145,4:105,3:68,2:42}
 wing=ctx['me'].get('wing',0)
 for step,cell in enumerate(route_cells,1):
  for spec_id in cell_specs.get(cell,()):
   if spec_id in seen:
    continue
   seen.add(spec_id)
   upcoming,spawn_in,rival,value=specs[spec_id]
   arrival=timings[step-1]if timings else turns_for_steps(step,wing)
   if spec_id in dynamic_tiers:
    value=tier_values.get(dynamic_tiers[spec_id],value)
    value*=mode['itemMul']
   if upcoming:
    if arrival>=spawn_in and arrival<max(spawn_in,rival):
     total+=0.9*value
   elif arrival<rival:
    total+=value
 return total
def route_cut_value(ctx,route_cells,mode):
 if not route_cells or not ctx['enemyTrail']:
  return 0.0
 enemies={p['index']:p for p in ctx['others']}
 touched={}
 route_times=aram_route_timing(ctx,route_cells)if mode.get('aram')and ctx.get('_itemSpecs')else None
 for step,cell in enumerate(route_cells,1):
  victim=ctx['enemyTrail'].get(cell)
  if not victim:
   continue
  idx=victim['index']
  if idx in touched:
   continue
  our_turns=route_times[step-1]if route_times else turns_for_steps(step,ctx['me'].get('wing',0))
  if our_turns<turns_until_enemy_can_return_home(ctx,victim):
   touched[idx]=len(victim.get('trail',[]))
 leader=mode.get('leaderIndex',-1)
 return sum((mode['cutValue']*(1.0+min(30,length)/90.0)*(1.2 if idx==leader else 1.0)for idx,length in touched.items()))
def projected_trail_after_route(ctx,route_cells):
 cleared=set()
 result=[]
 my_idx=ctx['me']['index']
 wing=ctx['me'].get('wing',0)
 route_times=aram_route_timing(ctx,route_cells)if ctx.get('_itemSpecs')else None
 return_eta={}
 for step,cell in enumerate(route_cells,1):
  victim=ctx['enemyTrail'].get(cell)
  if victim is not None:
   victim_idx=victim['index']
   eta=return_eta.get(victim_idx)
   if eta is None:
    eta=turns_until_enemy_can_return_home(ctx,victim)
    return_eta[victim_idx]=eta
   arrival=route_times[step-1]if route_times else turns_for_steps(step,wing)
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
def validate_plan(ctx,directions,route_cells,new_trail,mode,enemy_maps,occupied,max_trail,allow_unsafe=False,freeze_info=None):
 if not directions:
  return None
 if OPPOSITE.get(directions[0])==ctx['me'].get('lastDir'):
  return None
 for i in range(1,len(directions)):
  if OPPOSITE[directions[i]]==directions[i-1]:
   return None
 if len(ctx['myTrail'])+len(set(new_trail))>max_trail:
  return None
 turns=(aram_route_timing(ctx,route_cells)[-1]if mode.get('aram')and route_cells else turns_for_steps(len(directions),ctx['me'].get('wing',0)))
 if turns>mode['remaining']:
  return None
 full_trail=set(ctx['myTrail'])
 full_trail.update(new_trail)
 full_trail_list=list(full_trail)
 if pending_slash_hits(ctx,full_trail_list,turns):
  return None
 slack=INF
 if full_trail_list:
  enemy_time=earliest_enemy_arrival(ctx,full_trail_list,enemy_maps,freeze_info)
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
def aram_freeze_projection(ctx,route_cells,enemy_maps):
 specs,cell_specs=ctx.get('_itemSpecs',[]),ctx.get('_itemCells',{})
 if not specs or not cell_specs or not enemy_maps:return None
 timings=aram_route_timing(ctx,route_cells)
 pickup=None
 for step,cell in enumerate(route_cells,1):
  arrival=timings[step-1]
  for sid in cell_specs.get(cell,()):
   if ctx.get('_itemKinds',[])[sid]!='hourglass':continue
   upcoming,spawn,rival,_=specs[sid]
   if(arrival>=spawn and arrival<max(spawn,rival))if upcoming else arrival<rival:
    pickup=(arrival,cell);break
  if pickup:break
 if not pickup:return None
 raw=ctx['rules'].get('freezeTurns',[10,20])
 try:duration=min(int(v)for v in raw)if isinstance(raw,(list,tuple))else int(raw)
 except(TypeError,ValueError):duration=10
 count=max(1,int(ctx['rules'].get('freezeTargets',2)or 2))
 targets=[]
 for enemy,dist in enemy_maps:
  if enemy.get('freeze',0)or enemy.get('stun',0):continue
  d=dist[pickup[1]]
  if d>=0:targets.append((d,enemy.get('index')))
 chosen={idx for _,idx in sorted(targets)[:count]}
 return(pickup[0],max(0,duration),chosen)if chosen and duration>0 else None
def make_plan_candidate(ctx,directions,route_cells,new_trail,mode,enemy_maps,occupied,max_trail,counts,extra_item=0.0,extra_cut=0.0,emergency=False,rough=0.0,label='loop'):
 if enemy_maps:
  freeze_info=aram_freeze_projection(ctx,route_cells,enemy_maps)if mode.get('aram')else None
  checked=validate_plan(ctx,directions,route_cells,new_trail,mode,enemy_maps,occupied,max_trail,allow_unsafe=emergency,freeze_info=freeze_info)
  if checked is None:
   return None
 else:
  if not directions or len(ctx['myTrail'])+len(set(new_trail))>max_trail:
   return None
  if OPPOSITE.get(directions[0])==ctx['me'].get('lastDir'):
   return None
  for i in range(1,len(directions)):
   if OPPOSITE.get(directions[i])==directions[i-1]:
    return None
  turns=turns_for_steps(len(directions),ctx['me'].get('wing',0))
  if turns>mode['remaining']:
   return None
  checked={'turns':turns,'slack':INF}
 if enemy_maps:
  item_value=route_item_value(ctx,route_cells,mode,counts,mode['maxTurns'],enemy_maps)
  cut_value=route_cut_value(ctx,route_cells,mode)
 else:
  item_value=0.0
  cut_value=0.0
 return{'directions':directions,'route_cells':route_cells,'new_trail':new_trail,'turns':checked['turns'],'slack':checked['slack'],'item_value':item_value+extra_item,'cut_value':cut_value+extra_cut,'rough':rough,'label':label}
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
def hunt_candidate(ctx,mode,home_field,enemy_maps,occupied,max_trail,counts):
 if not ctx['enemyTrail']:return None
 start=current_index(ctx);wing=int(ctx['me'].get('wing',0)or 0)
 frozen=sum(1 for p in ctx['others']if p.get('freeze',0)or p.get('stun',0))
 radius=max(int(mode.get('huntRadius',3)),5 if mode.get('aram')else 2)+(3 if wing>0 else 0)+(2 if frozen else 0)
 radius=min(12,radius)
 goals={cell:[cell]for cell in ctx['enemyTrail']}
 valid=lambda cell:cell not in ctx['myTrail']and cell not in occupied
 paths=bfs_many_goals(ctx,start,ctx['me'].get('lastDir'),valid,radius,goals)
 best=None;best_score=-INF
 for target,path in paths.items():
  victim=ctx['enemyTrail'].get(target)
  if not victim or not victim.get('trail'):continue
  timing=aram_route_timing(ctx,path.get('fullPath',[]))if mode.get('aram')else None
  reach_turns=timing[-1]if timing else turns_for_steps(path['dist'],wing)
  return_eta=turns_until_enemy_can_return_home(ctx,victim,max(1,reach_turns+1))
  if reach_turns>=return_eta:continue
  candidate=direct_target_candidate(ctx,mode,path,mode['cutValue'],'hunt',home_field,enemy_maps,occupied,max_trail,counts,cut=True)
  if candidate is None:continue
  length=len(victim.get('trail',[]));margin=return_eta-reach_turns
  score=(length+8.0)*mode['cutValue']/(candidate['turns']+2)+min(8.0,margin)*0.12
  if victim.get('index')==mode.get('leaderIndex',-1):score*=1.2
  if score>best_score:
   candidate['hunt_target']=victim.get('index');candidate['hunt_length']=length;candidate['hunt_margin']=margin
   best,best_score=candidate,score
 return best
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
  arrival=aram_route_timing(ctx,path.get('fullPath',[]))[-1]
  if upcoming and arrival<spawn_in:
   continue
  candidate=direct_target_candidate(ctx,mode,path,0.0,'item',home_field,enemy_maps,occupied,max_trail,counts,cut=False)
  if candidate is not None and candidate['item_value']>0:
   kinds=ctx.get('_itemKinds',['']*len(specs));kind=kinds[spec_id]
   combo,order=aram_chain_bonus(ctx,candidate['route_cells'],mode)
   tier=next((t for sid,step,t in order if sid==spec_id),aram_item_tier(ctx,kind))
   candidate['target_item_type']=kind
   candidate['target_item_tier']=tier
   candidate['target_item_steps']=path['dist']
   candidate['chain_count']=len(order)
   candidate['chain_order']=[kinds[sid]for sid,step,t in order if sid<len(kinds)]
   candidate['item_value']+=combo
   candidate['aram_chain_value']=candidate['item_value']
   result.append(candidate)
 return result
def aram_chain_bonus(ctx,cells,mode):
 specs,cell_specs=ctx.get('_itemSpecs',[]),ctx.get('_itemCells',{})
 kinds=ctx.get('_itemKinds',[])
 if not cells or not specs:return 0.0,[]
 timings=aram_route_timing(ctx,cells)
 raw=ctx['rules'].get('wingTurns',[5,10])
 try:wing_duration=min(int(v)for v in raw)if isinstance(raw,(list,tuple))else int(raw)
 except(TypeError,ValueError):wing_duration=5
 raw=ctx['rules'].get('freezeTurns',[10,20])
 try:freeze_duration=min(int(v)for v in raw)if isinstance(raw,(list,tuple))else int(raw)
 except(TypeError,ValueError):freeze_duration=10
 needed=max(1,int(ctx['rules'].get('freezeTargets',2)or 2))
 lock_waits=[max(int(p.get('freeze',0)or 0),int(p.get('stun',0)or 0))for p in ctx['others']]
 wing_until=max(0,int(ctx['me'].get('wing',0)or 0))
 freeze_until=0;new_frozen=0;freeze_with_wing=False
 picked=set();order=[];bonus=0.0
 for step,cell in enumerate(cells,1):
  arrival=timings[step-1]
  for sid in cell_specs.get(cell,()):
   if sid in picked:continue
   upcoming,spawn,rival,value=specs[sid]
   available=arrival>=spawn and arrival<max(spawn,rival)if upcoming else arrival<rival
   if not available:continue
   kind=kinds[sid]if sid<len(kinds)else''
   wing_active=arrival<=wing_until
   existing_locked=sum(1 for wait in lock_waits if wait>=arrival)
   freeze_active=existing_locked>0 or arrival<=freeze_until and new_frozen>0
   freezable=max(0,len(ctx['others'])-existing_locked-(new_frozen if freeze_active else 0))
   if kind=='wing':
    wing_left=max(0,wing_until-arrival)
    tier=6 if wing_left<=2 else 3 if wing_left>=4 else 5
   elif kind=='hourglass':
    tier=6 if wing_active and freezable else 4 if not wing_active and freezable else 3
    if freezable:
     new_frozen=min(needed,freezable);freeze_until=max(freeze_until,arrival+freeze_duration)
     freeze_with_wing=freeze_with_wing or wing_active
   elif kind in('bomb','megabomb'):
    tier=6 if freeze_active else 4 if wing_active else 5
   elif kind=='saber':tier=2
   else:tier=1
   if kind=='wing':wing_until=max(wing_until,arrival+wing_duration)
   picked.add(sid);order.append((sid,step,tier))
   bonus+=tier*2.2+float(value)*0.10
 if len(order)>1:bonus+=(len(order)-1)*22.0
 wing_step=next((step for sid,step,tier in order if kinds[sid]=='wing'),None)
 freeze_step=next((step for sid,step,tier in order if kinds[sid]=='hourglass'),None)
 if freeze_step is not None and freeze_with_wing:bonus+=60.0
 if wing_step is not None and freeze_step is not None and wing_step<freeze_step:bonus+=35.0
 if freeze_step is not None:
  bonus+=18.0*sum(1 for sid,step,tier in order if step>freeze_step and kinds[sid]in('bomb','megabomb'))
 return bonus,order
def aram_candidate_rank(candidate):
 turns=max(1,int(candidate.get('turns',1)))
 item=max(0.0,float(candidate.get('item_value',0.0)))
 cut=max(0.0,float(candidate.get('cut_value',0.0)))
 area=max(0.0,float(candidate.get('rough',0.0)))
 chain=max(1,int(candidate.get('chain_count',1)))
 tier=int(candidate.get('target_item_tier',0)or 0)
 tier_bonus={6:10.0,5:7.0,4:4.0,3:2.0,2:0.0}.get(tier,0.0)
 cluster_bonus=min(18.0,6.0*math.log(chain))
 wing_dist=float(candidate.get('aram_wing_distance',INF))
 wing_steps=float(candidate.get('aram_wing_steps',INF))
 local_count=int(candidate.get('aram_near_loot_count',0))
 local_value=float(candidate.get('aram_near_loot_value',0.0))
 has_wing=math.isfinite(wing_steps)
 # Keep Wing strategically valuable, but let a dense nearby loot cluster compete
 # when the closest Wing is a long detour rather than a practical first target.
 wing_bonus=(18.0*max(0.0,1.0-wing_dist/36.0))if has_wing and math.isfinite(wing_dist)else 0.0
 opportunistic=0.0
 if wing_dist>=10.0 and local_count>=2:
  opportunistic=min(105.0,34.0*(local_count-1)+0.12*local_value)
 remote_penalty=min(5.0,max(0.0,wing_steps-10.0)*0.18)if has_wing else 0.0
 return(item+0.30*cut+0.08*area+tier_bonus+cluster_bonus+wing_bonus+opportunistic)/(turns+2.0)-remote_penalty/(turns+2.0)


def aram_chain_candidates(ctx,mode,home_field,enemy_maps,occupied,max_trail,counts):
 specs,cell_specs=ctx.get('_itemSpecs',[]),ctx.get('_itemCells',{})
 if not specs or not cell_specs:return[]
 wing=int(ctx['me'].get('wing',0)or 0)
 max_steps=min(58,max(1,max_trail-len(ctx['myTrail'])-5))
 radius=min(ctx['width']+ctx['height'],mode['itemRadius']+(12 if wing>0 else 5))
 start=current_index(ctx)
 root={'pos':start,'last':ctx['me'].get('lastDir'),'cells':[],'dirs':[],'visited':set(),'left':bool(ctx['myTrail'])or ctx['grid'][start]!=ctx['me']['index'],'collected':set(),'rank':0.0}
 beam,results=[root],[]
 seen=set()
 for depth in range(7):
  expanded=[]
  for node in beam:
   node_wing=wing>0 or any(ctx.get('_itemKinds',[])[sid]=='wing'for sid in node['collected'])
   node_limit=min(58 if node_wing else 38,max_steps,max(1,max_trail-len(ctx['myTrail'])-5))
   node_radius=min(ctx['width']+ctx['height'],mode['itemRadius']+(12 if node_wing else 5))
   goals={cell:[sid for sid in ids if sid not in node['collected']]for cell,ids in cell_specs.items()if any(sid not in node['collected']for sid in ids)}
   if not goals:continue
   def valid(cell):
    return cell not in ctx['myTrail']and cell not in occupied and cell not in node['visited']and(not node['left']or ctx['grid'][cell]!=ctx['me']['index'])
   paths=bfs_many_goals(ctx,node['pos'],node['last'],valid,node_radius,goals)
   if not node['cells']:
    wing_dist=INF
    for sid,wp in paths.items():
     if sid>=len(ctx.get('_itemKinds',[]))or ctx['_itemKinds'][sid]!='wing':continue
     timing=aram_route_timing(ctx,wp.get('fullPath',[]))
     arrival=timing[-1]if timing else INF
     upcoming,spawn,rival,_=specs[sid]
     if (not upcoming and arrival<rival)or(upcoming and arrival>=spawn and arrival<max(spawn,rival)):
      wing_dist=min(wing_dist,wp['dist'])
    ctx['_aramWingDistance']=wing_dist
   for path in paths.values():
    segment=path.get('fullPath',[]);segdirs=path.get('directions',[])
    if not segment or not segdirs:continue
    newcells=node['cells']+segment;newdirs=node['dirs']+segdirs
    if len(newcells)>node_limit or len(newdirs)!=len(newcells):continue
    left,legal=node['left'],True
    for cell in segment:
     owner=ctx['grid'][cell]
     if left and owner==ctx['me']['index']:
      legal=False;break
     if owner!=ctx['me']['index']:left=True
    if not legal:continue
    bonus,order=aram_chain_bonus(ctx,newcells,mode)
    collected={sid for sid,_,_ in order}
    if len(collected)<=len(node['collected']):continue
    key=(tuple(newcells),tuple(sorted(collected)))
    if key in seen:continue
    seen.add(key)
    end=segment[-1];forbidden=set(ctx['myTrail'])|set(newcells)
    home=reconstruct_home_route(ctx,end,home_field,forbidden,segdirs[-1],occupied)
    if home is not None:
     ret_dirs,ret_cells=home;all_dirs,all_cells=newdirs+ret_dirs,newcells+ret_cells
     added=projected_trail_after_route(ctx,all_cells)
     final_bonus,final_order=aram_chain_bonus(ctx,all_cells,mode)
     candidate=make_plan_candidate(ctx,all_dirs,all_cells,added,mode,enemy_maps,occupied,max_trail,counts,extra_item=final_bonus,rough=rough_route_area(ctx,added,len(newcells),1),label='aram-chain')
     if candidate:
      kinds=ctx.get('_itemKinds',[])
      first_sid,first_step,first_tier=final_order[0]if final_order else(-1,0,0)
      candidate['target_item_tier']=first_tier
      candidate['target_item_type']=kinds[first_sid]if 0<=first_sid<len(kinds)else''
      candidate['best_item_tier']=max((tier for sid,_,tier in final_order),default=0)
      candidate['chain_count']=len({sid for sid,_,_ in final_order})
      candidate['chain_bonus']=final_bonus
      candidate['aram_chain_value']=candidate['item_value']
      candidate['chain_order']=[kinds[sid]for sid,_,_ in final_order if sid<len(kinds)]
      wing_steps=[step for sid,step,tier in final_order if sid<len(kinds)and kinds[sid]=='wing']
      near_loot=[sid for sid,step,tier in final_order if sid<len(kinds)and kinds[sid]!='wing'and step<=10]
      candidate['aram_wing_distance']=ctx.get('_aramWingDistance',INF)
      candidate['aram_wing_steps']=min(wing_steps,default=INF)
      candidate['aram_near_loot_count']=len(near_loot)
      candidate['aram_near_loot_value']=sum(specs[sid][3]for sid in near_loot)
      results.append(candidate)
    if left and ctx['grid'][end]!=ctx['me']['index']and depth+1<7:
     local_loot=[sid for sid,step,tier in order if sid<len(kinds)and kinds[sid]!='wing'and step<=10]
     local_boost=min(105.0,34.0*(len(local_loot)-1)+0.12*sum(specs[sid][3]for sid in local_loot))if ctx.get('_aramWingDistance',INF)>=10.0 and len(local_loot)>=2 else 0.0
     node_score=(sum(specs[sid][3]for sid in collected)+bonus+local_boost+6.0*math.log(max(1,len(collected))))/(len(newcells)+3.0)
     expanded.append({'pos':end,'last':segdirs[-1],'cells':newcells,'dirs':newdirs,'visited':set(newcells),'left':left,'collected':collected,'rank':node_score})
  expanded.sort(key=lambda n:(n['rank'],len(n['collected']),-len(n['cells'])),reverse=True)
  beam=expanded[:8]
  if not beam:break
 results.sort(key=lambda c:(aram_candidate_rank(c),c.get('chain_count',0),c.get('slack',-INF)),reverse=True)
 return results[:16]
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
def aram_center_bonus(ctx,candidate,mode):
 if not mode.get('aram')or mode.get('aramPhase')=='SPAWN_EXPANSION':
  return 0.0
 w,h=(ctx['width'],ctx['height'])
 x0,y0,x1,y1=ctx.get('playableBounds',(0,0,w-1,h-1))
 center_x,center_y=((x0+x1)/2.0,(y0+y1)/2.0)
 start_x,start_y=index_to_coord(ctx,current_index(ctx))
 start_dist=abs(start_x-center_x)+abs(start_y-center_y)
 route=candidate.get('route_cells',[])
 if not route:
  return 0.0
 best_dist=start_dist
 for cell in route:
  x,y=index_to_coord(ctx,cell)
  d=abs(x-center_x)+abs(y-center_y)
  if d<best_dist:
   best_dist=d
 progress=max(0.0,start_dist-best_dist)
 if mode.get('aramPhase')=='ENDGAME':
  weight=0.18
 else:
  weight=0.72
 return min(10.0,progress*weight)
def plan_pick(ctx):
 mode=choose_strategy_mode(ctx)
 max_trail_rule=int(ctx['rules'].get('maxTrail',120)or 120)
 max_trail=max(1,max_trail_rule)
 remaining_trail=max(1,max_trail-len(ctx['myTrail']))
 home_horizon=min(remaining_trail,max(66 if mode.get('aram')else 32,mode['maxOut']+mode['maxSide']+(24 if mode.get('aram')else 12)))
 home_field=build_home_field(ctx,home_horizon)
 _,_,occupied=home_field
 counts=territory_counts(ctx)
 current=current_index(ctx)
 me=ctx['me']
 if me.get('trail'):
  home_now=reconstruct_home_route(ctx,current,home_field,set(ctx['myTrail']),me.get('lastDir'),occupied)
  if home_now is not None and home_now[0]:
   home_steps=len(home_now[0])
   home_turns=turns_for_steps(home_steps,me.get('wing',0))
   urgent_slash=pending_slash_hits(ctx,list(ctx['myTrail']),home_turns+1)
   enemy_eta=turns_until_enemy_can_touch_trail(ctx,ctx['myTrail'])
   near_limit=len(ctx['myTrail'])+home_steps>=max_trail
   endgame=home_turns+1>=mode['remaining']
   exposed=enemy_eta<=home_turns+mode['margin']
   if urgent_slash or near_limit or endgame or exposed:
    return{'directions':home_now[0],'mode':mode['name'],'score':-2.0,'label':'forced-safe-home'}
 candidates=rectangular_candidates(ctx,mode,home_field,[],occupied,max_trail,counts)
 threat_targets=set(ctx['myTrail'])
 max_candidate_turns=1
 for candidate in candidates:
  threat_targets.update(candidate['new_trail'])
  max_candidate_turns=max(max_candidate_turns,candidate['turns'])
 all_items=ctx['state'].get('items',[])+ctx['state'].get('upcoming',ctx['state'].get('upcomingItems',[]))
 for item in all_items:
  size=ITEM_SIZE.get(item.get('type'),1)
  for dy in range(size):
   for dx in range(size):
    x,y=(item['x']+dx,item['y']+dy)
    if 0<=x<ctx['width']and 0<=y<ctx['height']:
     threat_targets.add(y*ctx['width']+x)
 max_enemy_wing=max((int(p.get('wing',0)or 0)for p in ctx['others']),default=0)
 item_horizon=min(ctx['width']+ctx['height'],mode['itemRadius']+(12 if mode.get('aram')and ctx['me'].get('wing',0)else 5 if mode.get('aram')else 0))
 enemy_step_cap=max(max_enemy_wing*2+max_candidate_turns+mode['margin']+2,item_horizon+max_enemy_wing*2+2)
 enemy_maps=build_enemy_distance_maps(ctx,list(threat_targets),min(ctx['width']+ctx['height'],enemy_step_cap))
 prepare_item_value_lookup(ctx,mode,counts,enemy_maps)
 safe_candidates=[]
 for candidate in candidates:
  checked=validate_plan(ctx,candidate['directions'],candidate['route_cells'],candidate['new_trail'],mode,enemy_maps,occupied,max_trail,allow_unsafe=False)
  if checked is not None:
   candidate['slack']=checked['slack']
   candidate['item_value']=route_item_value(ctx,candidate['route_cells'],mode,counts,mode['maxTurns'],enemy_maps)
   candidate['cut_value']=route_cut_value(ctx,candidate['route_cells'],mode)
   safe_candidates.append(candidate)
 candidates=safe_candidates
 hunt=hunt_candidate(ctx,mode,home_field,enemy_maps,occupied,max_trail,counts)
 if hunt:
  candidates.append(hunt)
 candidates.extend(item_hunt_candidates(ctx,mode,home_field,enemy_maps,occupied,max_trail,counts))
 if mode.get('aram'):
  candidates.extend(aram_chain_candidates(ctx,mode,home_field,enemy_maps,occupied,max_trail,counts))
 continuation=continuation_candidate(ctx,mode,enemy_maps,occupied,max_trail,counts)
 if continuation is not None:
  candidates.append(continuation)
 me=ctx['me']
 if me.get('trail'):
  home=reconstruct_home_route(ctx,current,home_field,set(ctx['myTrail']),me.get('lastDir'),occupied)
  if home is not None:
   dirs,cells=home
   emergency=make_plan_candidate(ctx,dirs,cells,projected_trail_after_route(ctx,cells),mode,enemy_maps,occupied,max_trail,counts,emergency=True,rough=0.0,label='emergency-home')
   if emergency:
    emergency['emergency']=True
    candidates.append(emergency)
 if not candidates:
  if me.get('trail'):
   home=reconstruct_home_route(ctx,current,home_field,set(ctx['myTrail']),me.get('lastDir'),occupied)
   if home and home[0]:
    return{'directions':home[0],'mode':mode['name'],'score':-1.0,'label':'forced-home'}
   return None
  return None
 if mode.get('aram'):
  candidates.sort(key=aram_candidate_rank,reverse=True)
 else:
  candidates.sort(key=lambda c:(c['rough']+c['item_value']+c['cut_value']+aram_center_bonus(ctx,c,mode))/(c['turns']+2),reverse=True)
 total=ctx['width']*ctx['height']
 exact_limit=18 if total<=2500 else 7 if total<=10000 else 4
 shortlist,used_dirs=([],set())
 if mode.get('aram'):
  # Seed the evaluation with different strategic families, not only the highest item tier.
  families=('aram-chain','item','hunt')
  for family in families:
   pool=[c for c in candidates if family in c.get('label','')]
   if pool:
    chosen=max(pool,key=aram_candidate_rank)
    if chosen not in shortlist and len(shortlist)<exact_limit:
     shortlist.append(chosen)
     if chosen.get('directions'):used_dirs.add(chosen['directions'][0])
  expansion=[c for c in candidates if c.get('item_value',0.0)<=0 and 'hunt' not in c.get('label','')]
  if expansion and len(shortlist)<exact_limit:
   chosen=max(expansion,key=aram_candidate_rank)
   if chosen not in shortlist:
    shortlist.append(chosen)
    if chosen.get('directions'):used_dirs.add(chosen['directions'][0])
  wanted_order=()
 else:
  wanted_order=('continuation','hunt','item')
 for wanted in wanted_order:
  chosen=next((c for c in candidates if wanted in c.get('label','')),None)
  if chosen is not None and chosen not in shortlist and(len(shortlist)<exact_limit):
   shortlist.append(chosen)
   if chosen['directions']:
    used_dirs.add(chosen['directions'][0])
 for candidate in candidates:
  if len(shortlist)>=exact_limit:
   break
  first=candidate['directions'][0]if candidate['directions']else 'stay'
  if first not in used_dirs:
   shortlist.append(candidate)
   used_dirs.add(first)
 if len(shortlist)<exact_limit:
  for candidate in candidates:
   if candidate not in shortlist:
    shortlist.append(candidate)
    if len(shortlist)>=exact_limit:
     break
 if total<=2500:
  build_voronoi_map(ctx)
 best=None
 for candidate in shortlist:
  area=estimate_enclosed_area(ctx,candidate['new_trail'],mode['enemyWeight'],mode.get('leaderIndex'),mode.get('leaderBonus',0.0))
  frontier=voronoi_frontier_bonus(ctx,candidate['route_cells'])
  center_bonus=aram_center_bonus(ctx,candidate,mode)
  value=area+candidate['item_value']+candidate['cut_value']+0.1*frontier+center_bonus
  score=value/(candidate['turns']+2)
  if candidate['slack']!=INF:
   score+=min(6.0,max(0.0,candidate['slack']-mode['margin']))*0.015
  candidate['area']=area
  candidate['frontier']=frontier
  candidate['center_bonus']=center_bonus
  candidate['score']=score
  if best is None or(score,area,candidate['slack'])>(best['score'],best['area'],best['slack']):
   best=candidate
 if best is None:
  return None
 old_best=None if mode.get('aram')else next((c for c in shortlist if c.get('label')=='continuation' and c.get('score',0.0)>=0.85*best['score']),None)
 if old_best is not None:
  best=old_best
 best['mode']=mode['name']
 best['scoreGap']=mode['scoreGap']
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
 global PLAN_MEMORY
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
 print('TITAN Strategy | tactical plan search + Voronoi + slack',ME,'bat dau tran',GAME,flush=True)
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
     print('Luot',turn_no+1,'di',move,flush=True)
    elif move:
     act('move',{'direction':move})
     print('Luot',turn_no+1,'di',move,flush=True)
    last_turn=turn_no
   time.sleep(min(0.25,max(0.05,(status.get('tickInterval')or 500)/4000)))
  except Exception as err:
   print('Loi:',err,flush=True)
   time.sleep(1)
if __name__=='__main__':
 main()
