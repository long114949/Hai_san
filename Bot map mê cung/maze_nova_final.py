# NOVA -- independent bitboard wavefront/disjoint loop planner
import os,time,json,math,urllib.request
from collections import Counter, deque
ME=os.environ.get('PLAYER_ID','');API=os.environ.get('API_URL','');GAME=os.environ.get('GAME_ID','');TOKEN=os.environ.get('PLAYER_TOKEN','')
DIR=('up','right','down','left');INF=100000;MEM=None
CFG=(1.12, 1.0, 1.0, 1.0, 1.05)
ITEM_RANGE=24
DEF=(3, 2, 0)
class Budget(Exception):pass
def bits(m):
    while m:
        b=m&-m;yield b.bit_length()-1;m^=b
def eta(d,w):return (min(d,2*w)+1)//2+max(0,d-2*w)
class Board:
    def __init__(self,s,deadline=None):
        self.w=w=s['width'];self.h=h=s['height'];self.n=n=w*h;self.full=(1<<n)-1;r=(1<<w)-1
        self.L=self.full//r;self.R=self.L<<(w-1);self.edge=self.L|self.R|r|(r<<(n-w));ob=0
        for o in s.get('obstacles',[]):
            x,y,a,b=(o['x'],o['y'],o.get('w',1),o.get('h',1)) if isinstance(o,dict) else (*o[:2],1,1)
            for yy in range(max(0,y),min(h,y+b)):
                if min(w,x+a)>max(0,x):ob|=((1<<(min(w,x+a)-max(0,x)))-1)<<(yy*w+max(0,x))
        self.free=self.full^ob;self.core=self.free;self.core_done=False;self.core_rounds=0
        self.plan=[];self.vis=Counter();self.turn=-1;self.expected=-1;self.failed={};self.old_own=0
        self.history=deque(maxlen=24);self.avoid={};self.item_lock=None;self.last_progress=None
        self.build_core(deadline if deadline is not None else time.perf_counter()+.01)
    def build_core(self,deadline):
        while not self.core_done and self.core_rounds<256:
            if time.perf_counter()>=deadline:break
            a,b,c,d=self.shifts(self.core)
            v=self.core&((a&b)|(a&c)|(a&d)|(b&c)|(b&d)|(c&d))
            self.core_rounds+=1
            if v==self.core:self.core_done=True;break
            self.core=v
        if self.core_rounds>=256:self.core_done=True
    def shifts(self,m):return m>>self.w,((m&~self.R)<<1)&self.full,(m<<self.w)&self.full,(m&~self.L)>>1
    def expand(self,m):
        a,b,c,d=self.shifts(m);return a|b|c|d
    def step(self,v,d):
        if d==0:return v-self.w if v>=self.w else -1
        if d==1:return v+1 if v%self.w!=self.w-1 else -1
        if d==2:return v+self.w if v+self.w<self.n else -1
        return v-1 if v%self.w else -1
    def dir(self,v,u):return 0 if u==v-self.w else 2 if u==v+self.w else 1 if u>v else 3
    def check(self):
        if time.perf_counter()>=self.deadline:raise Budget
    def wave(self,seed,allowed,limit,goal=0,first=None):
        if not seed:return []
        seen=front=seed;layers=[seed]
        for k in range(limit):
            if k%8==0:self.check()
            front=(self.expand(front) if k or first is None else first)&allowed&~seen
            if not front:break
            layers.append(front);seen|=front
            if goal&front:break
        return layers
    def reconstruct(self,layers,v,order):
        path=[v]
        for layer in reversed(layers[:-1]):
            for d in order:
                u=self.step(v,d)
                if u>=0 and layer>>u&1:path.append(u);v=u;break
            else:return []
        return path[::-1]
    def path(self,start,goal,allowed,limit,last=-1,order=(0,1,2,3),safe_first=False):
        if goal>>start&1:return [start]
        first=self.expand(1<<start)
        if last>=0:
            u=self.step(start,(last+2)%4)
            if u>=0:first&=~(1<<u)
        if safe_first:first&=~self.d1
        ls=self.wave(1<<start,allowed,limit,goal,first)
        if not ls or not ls[-1]&goal:return []
        return self.reconstruct(ls,next(bits(ls[-1]&goal)),order)
    def capture(self,tr):
        op=self.full&~(self.own|tr);seen=front=self.edge&op;k=0
        while front:
            if k%16==0:self.check()
            front=self.expand(front)&op&~seen;seen|=front;k+=1
        return self.free&~self.own&~seen
    def refresh(self,s,me):
        self.s=s;self.me=me;self.idx=me['index'];self.pos=me['y']*self.w+me['x'];self.last=DIR.index(me['lastDir']) if me.get('lastDir') in DIR else -1;self.wing=me.get('wing',0)
        self.now=s.get('turn',0);self.rem=s.get('config',{}).get('maxTurns',600)-self.now;self.rules=s.get('rules',{});self.maxtrail=self.rules.get('maxTrail',120)
        self.own=self.enemy=0
        for y,row in enumerate(s['owner']):
            own=enemy=0
            for x,ch in enumerate(row):
                if ch==self.idx or ch==str(self.idx):own|=1<<x
                elif ch in (0,1,2,3,'0','1','2','3'):enemy|=1<<x
            self.own|=own<<(y*self.w);self.enemy|=enemy<<(y*self.w)
        self.tr=0
        for x,y in me.get('trail',[]):self.tr|=1<<(y*self.w+x)
        self.occ=0;self.enemies=[]
        for p in s['players']:
            if p['index']==self.idx:continue
            v=p['y']*self.w+p['x'];self.occ|=1<<v;self.enemies.append((p,v))
        self.allowed=self.free&~self.tr&~self.occ;self.items=[];self.at={};self.slashes=[]
        self.delay=max(self.rules.get('saberDelayTurns',4),math.ceil(2500/max(1,s.get('tickInterval',200)))) if self.rules.get('saberDelayTurns',4)>0 else 0
        for it in s.get('items',[])+s.get('upcomingItems',s.get('upcoming',[])):
            x,y=it['x'],it['y'];kind=it['type'];size=2 if kind in ('saber','megabomb') else 1
            m=sum(1<<((y+dy)*self.w+x+dx) for dy in range(size) for dx in range(size) if x+dx<self.w and y+dy<self.h)&self.free
            val={'saber':self.w*self.rules.get('saberRows',2)*.96,'hourglass':32,'megabomb':31,'wing':27,'bomb':14}.get(kind,5)
            if kind=='wing' and self.wing>4:val*=.45
            if kind=='saber' and self.rem<=self.delay:val=1
            when=max(0,it.get('turn',self.now)-self.now);i=len(self.items);self.items.append((kind,m,val,when))
            for v in bits(m):self.at.setdefault(v,[]).append(i)
        for sl in s.get('pendingSlashes',s.get('slashes',[])):
            if sl.get('by')==me['playerId']:continue
            lo,hi=sl['rows'];self.slashes.append((sl['turn']-self.now,((1<<((hi-lo+1)*self.w))-1)<<(lo*self.w)))
        self.d1=self.d2=self.occ
        for p,v in self.enemies:
            if p.get('freeze',0) or p.get('stun',0):continue
            f=self.expand(1<<v)&self.free;self.d1|=f;self.d2|=f
            if p.get('wing',0):self.d2|=self.expand(f)&self.free
        self.vis[self.pos]+=1;self.turn=self.now;self.old_own|=self.own
        if self.now%32==0:
            self.failed={k:v for k,v in self.failed.items() if v>self.now}
            self.avoid={k:v for k,v in self.avoid.items() if v>self.now}
        # Detect repeated position cycles only when no pickup or capture occurs.
        stats=me.get('stats',{});progress=(stats.get('captured',0),stats.get('items',0),self.own)
        if self.last_progress!=progress or me.get('freeze') or me.get('stun') or self.tr:
            self.history.clear()
        elif not self.history or self.history[-1][0]!=self.now:
            self.history.append((self.now,self.pos))
            hist=list(self.history)
            for k in (4,6,8,10,12):
                if len(hist)<2*k:continue
                q=hist[-2*k:]
                if q[-1][0]-q[0][0]==2*k-1 and [v for _,v in q[:k]]==[v for _,v in q[k:]]:
                    for (_,v),(_,u) in zip(q[k:],q[k+1:]+q[k:k+1]):self.avoid[v,u]=self.now+12
                    self.plan=[];self.item_lock=None;self.history.clear();break
        self.last_progress=progress
    def threats(self):
        self.ed=[INF]*self.n
        for p,v in self.enemies:
            wait=max(p.get('freeze',0),p.get('stun',0));wing=p.get('wing',0)
            for d,m in enumerate(self.wave(1<<v,self.free,min(130,self.maxtrail+12))):
                e=wait+eta(d,wing)
                for idx,j in enumerate(bits(m)):
                    if idx%128==0:self.check()
                    if e<self.ed[j]:self.ed[j]=e
        self.saber=min((max(min((self.ed[v] for v in bits(m)),default=INF),when)+self.delay for k,m,val,when in self.items if k=='saber'),default=INF)
    def moves(self,path):
        v=self.pos;last=self.last;tr=self.tr;out=[]
        for i,u in enumerate(path[:2 if self.wing else 1]):
            if u<0 or u>=self.n or not self.free>>u&1 or tr>>u&1:break
            d=self.dir(v,u)
            if self.step(v,d)!=u or last>=0 and (last+2)%4==d or (self.d1 if i==0 else self.d2)>>u&1:break
            tr=0 if self.own>>u&1 else tr|1<<u
            if tr.bit_count()>self.maxtrail:break
            out.append(DIR[d]);v=u;last=d
        return out
    def fallback(self):
        try:
            if self.own and not self.own>>self.pos&1:
                p=self.path(self.pos,self.own,self.allowed,min(self.maxtrail-self.tr.bit_count()+1,100),self.last,safe_first=True)
                if len(p)>1 and self.moves(p[1:]):return p[1:]
        except Budget:pass
        c=[]
        for d in range(4):
            v=self.step(self.pos,d)
            if v<0 or not self.free>>v&1 or self.tr>>v&1 or self.last>=0 and (self.last+2)%4==d:continue
            score=100*(not self.d1>>v&1)-80*(not self.core>>v&1)+8*(self.own>>v&1)+sum(self.items[i][2] for i in self.at.get(v,[]) if self.items[i][3]<=1)-2*self.vis[v]
            # When no ordinary return is found, prefer a component with an exit.
            if self.tr and time.perf_counter()<self.deadline-.002:
                try:
                    al=self.free&~self.tr
                    ls=self.wave(1<<v,al,min(18,self.maxtrail),self.own)
                    reach=sum(m.bit_count() for m in ls)
                    score+=min(12,reach*.15)+35*bool(ls and ls[-1]&self.own)
                    if reach<=2:score-=60
                except Budget:pass
            if self.avoid.get((self.pos,v),0)>self.now:score-=18
            c.append((score,v))
        return [max(c)[1]] if c else []
    def forced_reset(self):
        # Only when no geometrically legal non-trail move exists. Server accepts
        # self-trail contact, but cancels trail and stuns; never use as normal strategy.
        c=[]
        for d in range(4):
            v=self.step(self.pos,d)
            if v<0 or not self.free>>v&1 or self.last>=0 and (self.last+2)%4==d:continue
            if self.tr>>v&1 and not self.d1>>v&1:c.append((self.vis[v],d,v))
        return min(c)[1:] if c else None
    def eval(self,path):
        if not path:return None
        tr=self.tr;closed=False;collected=set();reward=0.;en=min((self.ed[v] for v in bits(tr)),default=INF)
        for j,v in enumerate(path,1):
            if tr>>v&1:return None
            at=eta(j,self.wing)
            for i in self.at.get(v,[]):
                if i in collected:continue
                k,m,val,when=self.items[i]
                if when and (at<when or at==when and j<=2*self.wing and j%2 and j<len(path)):continue
                if self.ed[v]+1<at:val*=.55
                collected.add(i);reward+=val*(1.0+0.25/(1+at/5))
            if self.own>>v&1:
                if tr:closed=True;break
            else:
                tr|=1<<v;en=min(en,self.ed[v])
                if tr.bit_count()>self.maxtrail:return None
        if not closed and (tr or not collected):return None
        path=path[:j];turns=eta(j,self.wing)
        if turns>self.rem or not self.moves(path):return None
        if closed:
            if any(t<turns and m&tr for t,m in self.slashes) or en<=1 and turns>1:return None
            m=self.capture(tr);gain=m.bit_count();steal=(m&self.enemy).bit_count()
        else:gain=steal=0
        if not gain and not reward:return None
        risk=max(0,turns+2-en);future=max(0,turns-self.saber)*min(1,(len({v//self.w for v in bits(tr)})+2)/self.h) if closed else 0
        nov=sum(min(4,self.vis[v]) for v in path[:15])/min(15,len(path));iv,ag,rk,nv,lg=CFG
        score=((gain+steal*.65)*ag+reward*iv)/(turns+5)**(.76*lg)+math.sqrt(gain)*.45*ag-risk*.13*rk-future*.55*rk-nov*.6*nv
        if gain<=5 and not reward and not self.tr:score-=2.5
        if collected:score+=1.1*iv
        if not self.tr and self.failed.get((self.pos,path[0]),-1)>self.now:score-=3
        if self.avoid.get((self.pos,path[0]),0)>self.now and not self.tr and not reward:score-=5
        if closed and gain>=12:score+=min(2.0,(m&self.old_own).bit_count()*.025)
        return score,path,gain,reward
    def loop(self,out,order):
        if len(out)<2:return None
        path=out[1:];tr=self.tr
        for i,v in enumerate(path):
            if self.own>>v&1:
                if tr:return self.eval(path[:i+1])
            else:tr|=1<<v
        if not tr:return self.eval(path)
        if tr.bit_count()>=self.maxtrail:return None
        allowed=self.allowed&~tr;limit=min(self.maxtrail-tr.bit_count()+1,max(1,self.rem*2-len(path)),100)
        home=self.path(out[-1],self.own&allowed,allowed,limit,self.dir(out[-2],out[-1]),order)
        return self.eval(path+home[1:]) if home else None
    def search(self,itemonly=False):
        first=self.expand(1<<self.pos)&~self.d1
        if self.last>=0:
            u=self.step(self.pos,(self.last+2)%4)
            if u>=0:first&=~(1<<u)
        ls=self.wave(1<<self.pos,self.allowed&self.core,min(75,self.maxtrail+20,max(2,self.rem*2)),first=first)
        if len(ls)<2:return None
        best=None;seen=set();orders=((0,1,2,3),(2,3,0,1),(1,0,3,2),(3,2,1,0))
        def try_(v,i,k):
            nonlocal best
            if (v,k) in seen:return
            seen.add((v,k));p=self.reconstruct(ls[:i+1],v,orders[k]);c=self.loop(p,orders[(k+1)%4]) if p else None
            if c and (not itemonly or c[3]>0) and (best is None or c[0]>best[0]):best=c
        tar=[]
        for i,l in enumerate(ls[1:],1):
            if i%8==0:self.check()
            for _,m,val,when in self.items:
                if l&m and i<=min(55,int(11+val*.36)) and eta(i,self.wing)>=when:
                    for v in bits(l&m):tar.append((val/(eta(i,self.wing)+4)**.65,v,i))
        tar.sort(reverse=True)
        try:
            for _,v,i in tar[:10]:try_(v,i,0);try_(v,i,1)
            if itemonly:return best
            tar=[];unowned=self.free&~self.own
            for i in range(5,len(ls),5):
                self.check();groups={}
                for j,v in enumerate(bits(ls[i]&unowned)):
                    if j%32==0:self.check()
                    x,y=v%self.w,v//self.w;k=(x//max(4,self.w//6),y//max(4,self.h//6));m=1<<v
                    for _ in range(3):m|=self.expand(m)&self.free
                    q=(m&unowned).bit_count()*.6+min(50,self.ed[v])*.17-min(6,self.vis[v])*1.8
                    if k not in groups or q>groups[k][0]:groups[k]=(q,v)
                for q,v in groups.values():tar.append((q+min(i,38)*.24-abs(i-22)*.06,v,i))
            tar.sort(reverse=True);bands={}
            for q,v,i in tar:bands.setdefault(i//9,[]).append((q,v,i))
            chosen=[a[j] for j in range(5) for a in bands.values() if len(a)>j]
            for _,v,i in chosen[:35]:self.check();try_(v,i,0);try_(v,i,1)
            for _,v,i in tar[:10]:self.check();try_(v,i,2)
        except Budget:pass
        return best
    def valid(self,path):
        if not path or not self.moves(path):return False
        tr=self.tr;prev=self.pos;last=self.last;turns=eta(len(path),self.wing);closed=False
        if turns>self.rem:return False
        for j,v in enumerate(path,1):
            if not self.free>>v&1 or self.occ>>v&1 or tr>>v&1:return False
            d=self.dir(prev,v)
            if self.step(prev,d)!=v or last>=0 and d==(last+2)%4:return False
            prev=v;last=d
            if self.own>>v&1:
                if tr:closed=True;turns=eta(j,self.wing);break
            else:tr|=1<<v
        if tr and not closed or tr.bit_count()>self.maxtrail:return False
        if any(t<turns and m&tr for t,m in self.slashes):return False
        if self.tr and min(self.ed[v] for v in bits(self.tr))<=min(turns+1,DEF[0]):return False
        return True
    def retreat(self):
        if not self.tr:return None
        enemy=min((self.ed[v] for v in bits(self.tr)),default=INF)
        pending=min((t for t,m in self.slashes if m&self.tr),default=INF)
        if enemy>max(DEF[0]+4,9) and pending>max(DEF[0]+4,9) and not DEF[2]:return None
        # A real route home is checked before abandoning a long excursion.
        if not self.own:return None
        p=self.path(self.pos,self.own,self.allowed,min(self.maxtrail-self.tr.bit_count()+1,100),self.last,safe_first=True)
        if len(p)<2:return None
        home=eta(len(p)-1,self.wing);planned=eta(len(self.plan),self.wing) if self.plan else INF
        forecast=DEF[2] and self.saber<planned and self.saber<=home+DEF[2] and len({v//self.w for v in bits(self.tr)})>=max(3,self.h//8)
        if (enemy<=min(planned+1,home+DEF[1]) or pending<=planned or forecast) and self.moves(p[1:]):return p[1:]
        return None
    def immediate_item(self):
        # A short detour is accepted only with a verified closing route.
        # All active items are considered independently of the global top-10 shortlist.
        active={i for i,(_,_,val,when) in enumerate(self.items) if when==0 and val>=5}
        if not active:return None
        targets=[];p=self.pos
        for d in range(4):
            u=self.step(p,d)
            if u<0 or not self.moves([u]) or not self.core>>u&1:continue
            for i in self.at.get(u,[]):
                if i in active:targets.append((self.items[i][2],i,[u]))
            if self.wing:
                for dd in range(4):
                    v=self.step(u,dd)
                    if v<0 or len(self.moves([u,v]))!=2 or not self.core>>v&1:continue
                    for i in self.at.get(v,[]):
                        if i in active:targets.append((self.items[i][2],i,[u,v]))
        if not targets:return None
        # Do not replace an action that already collects the same (or better) item.
        next_cells=self.plan[:2 if self.wing else 1]
        current=max((self.items[i][2] for v in next_cells for i in self.at.get(v,[]) if i in active),default=0)
        planned=max((self.items[i][2] for v in self.plan[:16] for i in self.at.get(v,[]) if i in active),default=0)
        best=None;key=None;seen=set()
        for val,i,prefix in sorted(targets,key=lambda q:(q[0],-len(q[2])),reverse=True):
            self.check()
            if val<=current or (i,tuple(prefix)) in seen:continue
            seen.add((i,tuple(prefix)))
            for order in ((0,1,2,3),(2,3,0,1)):
                cand=self.loop([p]+prefix,order)
                if not cand:continue
                _,path,gain,reward=cand
                kind,mask,_,_=self.items[i]
                if not any(mask>>v&1 for v in path[:len(prefix)]) or reward<=0:continue
                turns=eta(len(path),self.wing)
                # Keep expensive or dangerous detours optional; no forced sacrifice.
                if turns>(10 if kind=='saber' else 7):continue
                if planned>val*1.5 and len(path)>2:continue
                exposed=self.tr
                for v in path:
                    if self.own>>v&1 and exposed:break
                    if not self.own>>v&1:exposed|=1<<v
                if exposed and (min((self.ed[v] for v in bits(exposed)),default=INF)<=turns+1 or any(t<=turns and m&exposed for t,m in self.slashes)):continue
                q=(val/(1+.12*turns)+.3*gain,-len(path))
                if key is None or q>key:key=q;best=(path,(kind,mask),self.now+3)
        return best
    def lock_item(self,path):
        # Only commit to an existing item actually on the next few steps; never
        # hold a stale target after an opponent collected it or after route invalidation.
        for v in path[:4 if self.wing else 3]:
            for i in self.at.get(v,[]):
                kind,mask,val,when=self.items[i]
                if when==0 and val>=12:
                    self.item_lock=((kind,mask),self.now+3);return
    def locked(self):
        if not self.item_lock:return False
        (kind,mask),until=self.item_lock
        if self.now>until or not self.plan or not any(k==kind and m==mask and when==0 for k,m,_,when in self.items) or not any(mask>>v&1 for v in self.plan[:4 if self.wing else 3]):
            self.item_lock=None;return False
        return True
    def choose(self):
        self.threats()
        r=self.retreat()
        if r:self.item_lock=None;self.plan=r;return self.plan
        if self.plan and not self.valid(self.plan):
            if not self.tr:self.failed[(self.pos,self.plan[0])]=self.now+16
            self.plan=[];self.item_lock=None
        # An urgent return still takes precedence over all pickups.
        if self.items and time.perf_counter()<self.deadline-.003:
            old=self.deadline;self.deadline=min(old,time.perf_counter()+.006)
            try:near=self.immediate_item()
            except Budget:near=None
            finally:self.deadline=old
            if near:
                self.plan,target,until=near;self.item_lock=(target,until);return self.plan
        locked=self.locked()
        if self.items and self.plan:
            near=close_near=0
            for i,f in enumerate(self.wave(1<<self.pos,self.allowed,ITEM_RANGE)):
                near|=f
                if i<=12:close_near|=f
            route=sum(1<<v for v in set(self.plan[:10]))
            if any(m&near and not m&route and val>=12 and (k=='saber' or (m&close_near)) for k,m,val,_ in self.items) and time.perf_counter()<self.deadline-.012:
                old=self.deadline;self.deadline=min(old,time.perf_counter()+.012)
                try:c=self.search(True)
                except Budget:c=None
                finally:self.deadline=old
                if c and c[3]>0 and (c[0]>2.5 and c[3]>=20 or c[3]>=12 and len(c[1])<=7):
                    replace=True
                    if locked:
                        kind,mask=self.item_lock[0];target_val=max((v for k,m,v,w in self.items if k==kind and m==mask and w==0),default=0)
                        # Release only for a substantially better item opportunity; no blind lock.
                        old_at=next((eta(j,self.wing) for j,v in enumerate(self.plan,1) if mask>>v&1),INF)
                        new_at=next((eta(j,self.wing) for j,v in enumerate(c[1],1) if mask>>v&1),INF)
                        replace=new_at<=old_at or c[3]>target_val*1.85
                    if replace:self.plan=c[1];self.item_lock=None;self.lock_item(self.plan)
        if self.plan:self.lock_item(self.plan);return self.plan
        best=self.search()
        if best:self.plan=best[1];self.lock_item(self.plan);return self.plan
        return self.fallback()
def decide(s,budget_ms=60):
    global MEM
    start=time.perf_counter();me=next((p for p in s.get('players',[]) if p.get('playerId')==ME),None)
    if not me:return None
    deadline=start+min(70,max(5,budget_ms))/1000
    if MEM is None or (MEM.w,MEM.h)!=(s['width'],s['height']) or s.get('turn',0)<MEM.turn:MEM=Board(s,min(deadline,start+.008))
    b=MEM;b.deadline=deadline;b.refresh(s,me)
    if not b.core_done:b.build_core(min(deadline,time.perf_counter()+.002))
    if me.get('stun',0) or me.get('freeze',0):b.plan=[];return None
    if b.plan and b.expected!=b.pos:b.plan=[];b.item_lock=None
    try:path=b.choose()
    except Budget:path=b.fallback()
    except (ValueError,IndexError,KeyError,TypeError):b.plan=[];path=b.fallback()
    move=b.moves(path)
    if not move:
        path=b.fallback();move=b.moves(path)
        if not move and path:
            v=path[0];d=b.dir(b.pos,v)
            if b.step(b.pos,d)==v and not b.tr>>v&1 and b.free>>v&1 and (b.last<0 or (b.last+2)%4!=d):move=[DIR[d]]
    if not move:
        b.plan=[];reset=b.forced_reset()
        if reset:
            d,v=reset;b.expected=v;return DIR[d]
        return None
    b.expected=path[len(move)-1];b.plan=b.plan[len(move):] if path is b.plan else []
    return move if len(move)>1 else move[0]
def request(path,body=None,timeout=.10):
    req=urllib.request.Request(API+'/game/'+GAME+path,data=None if body is None else json.dumps(body).encode(),headers={'Content-Type':'application/json','x-player-token':TOKEN},method='GET' if body is None else 'POST')
    with urllib.request.urlopen(req,timeout=timeout) as r:return json.load(r) if body is None else r.read()
def main():
    last=-1
    while True:
        t=time.perf_counter()
        try:
            status=request('/status');turn=status.get('currentTurn',-1);tick=status.get('tickInterval',500)
            if status.get('status')=='finished':return
            if status.get('status')=='playing' and turn>=0 and turn!=last:
                s=request('/state',timeout=max(.012,min(.10,tick/1000-(time.perf_counter()-t)-.04)))
                if s.get('turn',turn)==turn:
                    s['tickInterval']=tick;last=turn;move=decide(s,max(5,min(60,tick-55-(time.perf_counter()-t)*1000)))
                    print(str(move)+' - '+str(round((time.perf_counter()-t)*1000))+'ms',flush=True)
                    if move:request('/player/'+ME+'/move',{'directions':move} if isinstance(move,list) else {'direction':move},timeout=max(.012,min(.10,tick/1000-(time.perf_counter()-t))))
            time.sleep(min(.08,max(.012,tick/8000)))
        except (OSError,ValueError,KeyError) as e:print('API:',str(e)[:160],flush=True);time.sleep(.03)
if __name__=='__main__':main()
