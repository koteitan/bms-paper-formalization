"""Does the ANCESTOR-restricted adjacent monotone hold at the BOUNDARY level m=t-1?

ancestor_monotone(A) is proven for m < t-1.  Test the adjacent, ancestor-indexed
statement at exactly m = t-1 (and compare m=t boundary):
  s=b0_start, t=mpl, C=last_col.
  (B) m=t-1, full interval:  forall q (q==s or m_anc A m s q): forall c in (q,C]:
         elem A (c-1) m < elem A c m
  (Bg) same but only G-prefix c<=s
  (T) m=t   (one past): same full interval
Report violations; if (B) is 0 we can strengthen the invariant to m<t.
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent,
                                          mpl, b0, l1, set_array, expand)

def ancestors_of(A, m, i):
    out=[]; p=m_parent(A,m,i); seen=set()
    while p is not None:
        if p in seen: break
        seen.add(p); out.append(p); p=m_parent(A,m,p)
    return out

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set(); Q=[]
for sd in seeds:
    A=strip(parse(sd)); kk=fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP=12000; depth=15

B_chk=0;B_viol=0;B_ex=[]
Bg_chk=0;Bg_viol=0;Bg_ex=[]
T_chk=0;T_viol=0;T_ex=[]

for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A); s=b0(A); t=mpl(A)
        if s is not None and t is not None and t>=1 and len(A)<=46 and l1(A)==1:
            C=len(A)-1
            # FILTER: only the residual regime t>=2 (boundary m=t-1>=1, row-0 excluded)
            if t>=2:
              for (mm,tag) in [(t-1,'B'),(t,'T')]:
                qs=[s]+ancestors_of(A,mm,s)
                for q in qs:
                    for c in range(q+1,C+1):
                        ok=(elem(A,c-1,mm)<elem(A,c,mm))
                        if tag=='B':
                            B_chk+=1
                            if not ok:
                                B_viol+=1
                                if len(B_ex)<10: B_ex.append((fmt(A),'s',s,'t',t,'m',mm,'q',q,'c',c,'l1',l1(A)))
                            if c<=s:
                                Bg_chk+=1
                                if not ok:
                                    Bg_viol+=1
                                    if len(Bg_ex)<10: Bg_ex.append((fmt(A),'s',s,'t',t,'m',mm,'q',q,'c',c,'l1',l1(A)))
                        else:
                            T_chk+=1
                            if not ok:
                                T_viol+=1
                                if len(T_ex)<10: T_ex.append((fmt(A),'s',s,'t',t,'m',mm,'q',q,'c',c,'l1',l1(A)))
        for nn in range(1,3):
            if len(A)>40: continue
            E=expand(fmt(A),nn)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} B={B_chk}/{B_viol} Bg={Bg_chk}/{Bg_viol} T={T_chk}/{T_viol}", flush=True)
    if len(seen)>CAP: break

print("\n=== RESULTS ===")
print(f"(B) ancestor-restricted at m=t-1, full interval: checked {B_chk}, viol {B_viol}")
for e in B_ex: print("   B-VIOL:",e)
print(f"(Bg) m=t-1, G-prefix only (c<=s):                checked {Bg_chk}, viol {Bg_viol}")
for e in Bg_ex: print("   Bg-VIOL:",e)
print(f"(T) ancestor-restricted at m=t (one past):       checked {T_chk}, viol {T_viol}")
for e in T_ex: print("   T-VIOL:",e)
