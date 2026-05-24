#!/usr/bin/env python3
"""
Mechanism probe: do TARGET 1 (iii_single_step, diagonal src=idx_B(t+1,0) tgt=idx_B(t,i))
and TARGET 2 (v, src bump n1->n1+1, tgt fixed idx_B(n0,i)) reduce to the
within-block recursion (block-independent offset matching, like the proven (ii)
shifts) OR to the cross-block "intermediate-block-exclusion / gateway" core?

We trace the m-ancestor chains and classify each parent step:
  - WITHIN-BLOCK: parent in same block as the column (offset decreases)
  - GATEWAY-DOWN: from offset-0 gateway of block c to a column of block c-? (cross-block)
  - INTERMEDIATE: parent lands in a block strictly between expected blocks
  - TO-G: parent lands in the G prefix (< l0)

We specifically check whether the diagonal correspondence between the two
shifted chains is established by matching WITHIN-BLOCK offsets (sound, reusable)
or whether it requires reasoning about where a GATEWAY's parent lands across
blocks (= the open shared core).
"""
import re, subprocess
YA="/home/koteitan/bms-paper/tmp/yaBMS/c/bms"
def parse(s): return [tuple(int(x) for x in m.group(1).split(',') if x.strip()) for m in re.finditer(r'\(([^)]*)\)',s)]
def fmt(A): return ''.join('('+','.join(str(x) for x in c)+')' for c in A)
def strip(A):
    if not A: return A
    h=max((len(c) for c in A),default=0)
    while h>0 and all((c[h-1] if h-1<len(c) else 0)==0 for c in A): h-=1
    return [tuple(c[:h]) for c in A]
def height(A): return max((len(c) for c in A),default=0)
def elem(A,p,r):
    if p<0 or p>=len(A): return 0
    if r<0 or r>=len(A[p]): return 0
    return A[p][r]
_MPC={}; _MISS=object()
def set_array(A): _MPC.clear()
def m_parent(A,m,i):
    key=(m,i); c=_MPC.get(key,_MISS)
    if c is not _MISS: return c
    res=None
    for pp in range(0,i):
        if elem(A,pp,m)>=elem(A,i,m): continue
        if m>0 and not m_anc(A,m-1,i,pp): continue
        res=pp
    _MPC[key]=res; return res
def m_anc(A,m,i,j):
    p=m_parent(A,m,i); seen=set()
    while p is not None:
        if p in seen: return False
        seen.add(p)
        if p==j: return True
        if p<j: return False
        p=m_parent(A,m,p)
    return False
def mpl(A):
    last=len(A)-1
    if last<0: return None
    for m in range(height(A)-1,-1,-1):
        if m_parent(A,m,last) is not None: return m
    return None
def b0(A):
    t=mpl(A); return None if t is None else m_parent(A,t,len(A)-1)
def l1(A):
    s=b0(A); return 0 if s is None else len(A)-1-s
def idxB(s,L1,t,j): return s+t*L1+j
_ec={}
def expand(text,n):
    k=(text,n)
    if k in _ec: return _ec[k]
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        v=strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: v=None
    _ec[k]=v; return v
def genuine(A):
    if any(any(x<0 for x in c) for c in A): return False
    E=expand(fmt(A),2)
    return E is not None and not any(any(x<0 for x in c) for c in E)

def classify(p, s, L1):
    """which region does index p fall in?"""
    if p < s: return ("G", None, None)
    off = p - s
    blk = off // L1
    inblk = off % L1
    return ("B", blk, inblk)

def trace_chain(E,k,src,tgt,s,L1):
    """walk parent chain from src toward tgt at level k; record block transitions."""
    set_array(E)
    steps=[]
    cur=src; seen=set()
    while True:
        p=m_parent(E,k,cur)
        if p is None: steps.append(("none",cur,None)); break
        if p in seen: steps.append(("cycle",cur,p)); break
        seen.add(p)
        rc=classify(cur,s,L1); rp=classify(p,s,L1)
        steps.append((rc,rp,cur,p))
        if p==tgt: steps.append(("HIT",p)); break
        if p<tgt: steps.append(("UNDERSHOOT",p)); break
        cur=p
    return steps

def analyze(A_orig, max_n=4):
    """For target 1 (diagonal), check whether the source gateway's parent
       crosses blocks (gateway-down) — i.e. needs intermediate-exclusion."""
    set_array(A_orig)
    s=b0(A_orig); m0=mpl(A_orig); L1=l1(A_orig)
    if s is None or m0 is None or L1<1: return None
    stats={"gateway_down":0,"within":0,"to_G":0,"intermediate_skip":0,"chains":0}
    for n in range(2,max_n+1):
        E=expand(fmt(A_orig),n)
        if E is None: continue
        for k in range(m0):
            for i in range(L1):
                for t in range(0,n-1):
                    src=idxB(s,L1,t+1,0); tgt=idxB(s,L1,t,i)
                    if max(src,tgt)>=len(E): continue
                    st=trace_chain(E,k,src,tgt,s,L1)
                    stats["chains"]+=1
                    for step in st:
                        if len(step)==4:
                            rc,rp,cur,p=step
                            if rc[0]=="B" and rp[0]=="B":
                                if rc[1]==rp[1]: stats["within"]+=1
                                elif rc[2]==0:  # source was a gateway (offset 0)
                                    stats["gateway_down"]+=1
                                    # does it land in the immediately-lower block?
                                    if rp[1] < rc[1]-1: stats["intermediate_skip"]+=1
                                else:
                                    # non-gateway crossing blocks downward
                                    stats["gateway_down"]+=1
                            elif rp[0]=="G":
                                stats["to_G"]+=1
    return stats

def analyze_v(A_orig, max_n=4):
    """Target 2 (v): chain src=idx_B(n1,j) down to tgt=idx_B(n0,i), n0<n1<n.
       Classify cross-block steps."""
    set_array(A_orig)
    s=b0(A_orig); L1=l1(A_orig)
    if s is None or L1<1: return None
    stats={"cross_block":0,"within":0,"to_G":0,"intermediate_skip":0,"chains":0,
           "gateway_cross":0}
    for n in range(2,max_n+1):
        E=expand(fmt(A_orig),n)
        if E is None: continue
        HE=height(E)
        for k in range(HE+1):
            for i in range(L1):
                for j in range(L1):
                    for n1 in range(1,n):
                        for n0 in range(0,n1):
                            src=idxB(s,L1,n1,j); tgt=idxB(s,L1,n0,i)
                            if max(src,tgt)>=len(E): continue
                            st=trace_chain(E,k,src,tgt,s,L1)
                            stats["chains"]+=1
                            for step in st:
                                if len(step)==4:
                                    rc,rp,cur,p=step
                                    if rc[0]=="B" and rp[0]=="B":
                                        if rc[1]==rp[1]: stats["within"]+=1
                                        else:
                                            stats["cross_block"]+=1
                                            if rc[2]==0: stats["gateway_cross"]+=1
                                            if rp[1] < rc[1]-1: stats["intermediate_skip"]+=1
                                    elif rp[0]=="G": stats["to_G"]+=1
    return stats

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
      "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,2)","(0,0)(1,1)(2,1)",
      "(0,0)(1,1)(2,0)(3,1)","(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)",
      "(0,0,0)(1,1,1)(2,2,2)","(0,0,0,0)(1,1,1,1)(2,2,2,1)",
      "(0,0,0)(1,1,1)(2,2,0)(3,3,1)","(0,0,0)(1,2,3)(2,3,1)"]
    seen=set(); Q=[]; CAP=400
    agg={"gateway_down":0,"within":0,"to_G":0,"intermediate_skip":0,"chains":0}
    aggv={"cross_block":0,"within":0,"to_G":0,"intermediate_skip":0,"chains":0,"gateway_cross":0}
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    for d in range(5):
        fr=[]
        for A in Q:
            if len(A)<=18 and genuine(A):
                st=analyze(A,max_n=4)
                if st:
                    for kk in agg: agg[kk]+=st[kk]
                stv=analyze_v(A,max_n=4)
                if stv:
                    for kk in aggv: aggv[kk]+=stv[kk]
            for n in range(1,4):
                if len(A)>16: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        if len(seen)>CAP: break
    print("=== TARGET 1 chain mechanism (diagonal src gateway -> tgt lower block) ===")
    print(agg)
    print("interpretation: gateway_down>0 means the diagonal chain MUST cross block")
    print("boundaries via a gateway/cross-block step (intermediate-exclusion core);")
    print("intermediate_skip>0 means it skips intermediate blocks (the hard core).")
    print("=== TARGET 2 (v) chain mechanism (src idx_B(n1,j) -> tgt idx_B(n0,i)) ===")
    print(aggv)
    print("cross_block>0 => the v chain crosses block boundaries; soundness that it")
    print("never skips intermediate blocks (intermediate_skip==0) IS the open core.")

if __name__=='__main__': main()
