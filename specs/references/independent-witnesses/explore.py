"""Independent finite-state enumeration from public FreeCell rules, not Lean code.
Card representation: 0..51 rank-major, CDHS suit order. Stacks bottom to top.
No automatic foundation pruning in baseline. Full equality keys, not hash-only.
"""
import sys,json,time,hashlib
from collections import deque
from pathlib import Path
rank=lambda c:c//4+1
suit=lambda c:c%4
red=lambda c:suit(c) in (1,2)
name=lambda c:'A23456789TJQK'[c//4]+'CDHS'[c%4]
def deal(seed):
 deck=list(range(52)); cols=[[] for _ in range(8)]
 for i in range(52):
  seed=(214013*seed+2531011)&0xffffffff
  j=((seed>>16)&32767)%len(deck)
  cols[i%8].append(deck[j]); deck[j]=deck[-1];deck.pop()
 return tuple(map(tuple,cols)),(),(0,0,0,0)
def canonical(st,columns=False,auto=False):
 cs,fs,hs=st
 if auto:
  cs=list(cs);fs=list(fs);hs=list(hs)
  while True:
   changed=False
   for i,c in [(i,col[-1]) for i,col in enumerate(cs) if col]+[(8+i,c) for i,c in enumerate(fs)]:
    # Safe auto-foundation: rank <=2 always safe; otherwise all opposite suits >=rank-1.
    if rank(c)==hs[suit(c)]+1 and (rank(c)<=2 or all(hs[s]>=rank(c)-1 for s in range(4) if (s in(1,2))!=red(c))):
     hs[suit(c)]+=1
     if i<8:cs[i]=cs[i][:-1]
     else:fs.remove(c)
     changed=True;break
   if not changed:break
  cs=tuple(cs);fs=tuple(fs);hs=tuple(hs)
 return (tuple(sorted(cs)) if columns else cs,tuple(sorted(fs)),hs)
def moves(st,ncells=4,back=False):
 cs,fs,hs=st
 sources=[(i,col[-1]) for i,col in enumerate(cs) if col]+[(8+i,c) for i,c in enumerate(fs)]
 if back:sources += [(20+s,4*(h-1)+s) for s,h in enumerate(hs) if h]
 for src,c in sources:
  # every destination tested independently from source removal
  for dst in range(13):
   if dst<8:
    if src==dst:continue
    if cs[dst] and not (rank(cs[dst][-1])==rank(c)+1 and red(cs[dst][-1])!=red(c)):continue
   elif dst==8:
    if src>=8 and src<20:continue
    if len(fs)>=ncells:continue
   else:
    if dst-9!=suit(c) or rank(c)!=hs[suit(c)]+1:continue
   ns=list(cs);nf=list(fs);nh=list(hs)
   if src<8:ns[src]=ns[src][:-1]
   elif src<20:nf.remove(c)
   else:nh[src-20]-=1
   if dst<8:ns[dst]=ns[dst]+(c,)
   elif dst==8:nf.append(c)
   else:nh[dst-9]+=1
   yield (tuple(ns),tuple(sorted(nf)),tuple(nh)),c,(src,dst)
def explore(columns=False,auto=False,back=False):
 start=canonical(deal(11982),columns,auto)
 seen={start};queue=deque([start]);moved=set();exposed=[];maxhome=0;empty=0;edges=0;started=time.monotonic()
 while queue:
  st=queue.popleft();cs,fs,hs=st
  maxhome=max(maxhome,sum(hs));empty=max(empty,sum(not c for c in cs))
  if any(col and col[-1]==44 for col in cs):exposed.append(st)
  for nxt,c,move in moves(st,back=back):
   moved.add(c);edges+=1;nxt=canonical(nxt,columns,auto)
   if nxt not in seen:seen.add(nxt);queue.append(nxt)
  if len(seen)>2000000:raise RuntimeError('Safety cap reached, not exhaustive')
  if edges and edges%100000<20:print('progress',len(seen),'frontier',len(queue),'edges',edges,flush=True)
 result={'columns_canonical':columns,'auto_home':auto,'foundation_return':back,'states':len(seen),'edges':edges,'max_home':maxhome,'max_empty_columns':empty,'unmoved':[name(c) for c in range(52) if c not in moved],'qclub_exposed_count':len(exposed),'seconds':time.monotonic()-started,'deal':[[name(c) for c in col] for col in deal(11982)[0]],'qclub_states':[[[[name(c) for c in col] for col in cs],[name(c) for c in fs],hs] for cs,fs,hs in exposed]}
 print(json.dumps(result,indent=2),flush=True)
 return result
if __name__=='__main__':
 mode=sys.argv[1] if len(sys.argv)>1 else 'baseline'
 r=explore(columns=mode in('canonical','auto'),auto=mode=='auto',back=mode=='back')
 Path(__file__).with_name(mode+'.json').write_text(json.dumps(r,indent=2)+'\n')
