from explore import *
import heapq,itertools

def normalize(st):return canonical(st,columns=True,auto=True)
def score(st):
 cs,fs,hs=st
 buried=sum(sum(len(col)-1-i for i,c in enumerate(col) if rank(c)<=hs[suit(c)]+1) for col in cs)
 return -sum(hs)*12+buried*2+len(fs)*3-10*sum(not col for col in cs)

def win(game,ncells):
 start=deal(game); heap=[(score(start),0,start)];seq=itertools.count(1);seen={normalize(start)};parents={start:None};n=0;t=time.monotonic()
 while heap:
  _,_,st=heapq.heappop(heap);n+=1
  if sum(st[2])==52:
   path=[]
   while st is not None:path.append(st);st=parents[st]
   path.reverse()
   out={'game':game,'ncells':ncells,'states_examined':n,'states_queued':len(seen),'seconds':time.monotonic()-t,'path':path}
   Path(__file__).with_name(f'win-{game}-{ncells}.json').write_text(json.dumps(out)+'\n')
   print('WIN',game,ncells,n,len(seen),'path',len(path),flush=True);return
  for nxt,c,m in moves(st,ncells):
   # Force safe foundation moves as actual single-card states in the witness.
   chain=[nxt]
   while True:
    safe=[]
    for nn,cc,mm in moves(chain[-1],ncells):
     if mm[1]>=9 and (rank(cc)<=2 or all(chain[-1][2][s]>=rank(cc)-1 for s in range(4) if (s in (1,2))!=red(cc))):safe.append(nn)
    if not safe:break
    chain.append(safe[0])
   nxt=chain[-1];key=canonical(nxt,columns=True)
   if key in seen:continue
   seen.add(key);last=st
   for step in chain:
    if step not in parents:parents[step]=last
    last=step
   heapq.heappush(heap,(score(nxt),next(seq),nxt))
  if n%10000==0:print('progress',game,ncells,'expanded',n,'seen',len(seen),'frontier',len(heap),'seconds',time.monotonic()-t,flush=True)
  if n>=500000:raise RuntimeError('500000 expansion safety cap; inconclusive')
 raise RuntimeError('Exhausted without win')
if __name__=='__main__':win(int(sys.argv[1]),int(sys.argv[2]))
