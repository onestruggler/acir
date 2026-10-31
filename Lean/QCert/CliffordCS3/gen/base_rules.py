#!/usr/bin/env python3
"""Figure 2 equations in the order of Replay.baseRules (no semantic axioms)."""
def k(q): return [1+q]
def s(q): return [4+q]
def cs(j): return [7+j]
def x(q): return k(q)+s(q)*2+k(q)+[0]
def cx(j,t): return k(t)+cs(j)*2+k(t)+[0]
def equations():
    out=[([0]*4,[])]
    for r in [2,3,4]:
        for q in range(3):
            out.append((k(q)*2,[0]*3) if r==2 else (s(q)*4,[]) if r==3 else ((s(q)+k(q))*3,[0]*3))
    for r in range(5,12):
        for j in range(2):
            u,l=j,j+1;c=cs(j)
            if r==5: pair=(c*4,[])
            elif r==6: pair=(s(u)+c,c+s(u))
            elif r==7: pair=(s(l)+c,c+s(l))
            elif r==8: pair=(x(u)+c,c*3+x(u)+s(l))
            elif r==9: pair=(x(l)+c,c*3+x(l)+s(u))
            elif r==10:pair=(s(u)+k(u)+c+k(u)+c,c+k(u)+c+k(u)+s(u))
            else:pair=(s(l)+k(l)+c+k(l)+c,c+k(l)+c+k(l)+s(l))
            out.append(pair)
    a,b=cs(0),cs(1);c01,c10,c12,c21=cx(0,1),cx(0,0),cx(1,2),cx(1,1)
    out.extend([
      (b+a,a+b),
      (c10+c01+b+c01+c10,c12+c21+a+c21+c12),
      (b+c01+b*3+c01,a+c21+a*3+c21),
      (c10+c01+b*2+c01+c10,c01+b*2+c01+b*2),
      (b+k(1)+b+k(1)+a+k(1)+a,a+k(1)+a+k(1)+b+k(1)+b),
      (b+k(1)+b*3+k(1)+a+k(1)+b,a+k(1)+a*3+k(1)+b+k(1)+a)])
    out.extend(([0,g],[g,0]) for g in range(1,9))
    for aa in [k,s]:
      for bb in [k,s]:
        for q,r in [(0,1),(0,2),(1,2)]:out.append((aa(q)+bb(r),bb(r)+aa(q)))
    for aa in [k,s]:out.append((aa(0)+cs(1),cs(1)+aa(0)))
    for aa in [k,s]:out.append((aa(2)+cs(0),cs(0)+aa(2)))
    assert len(out)==54
    return [(str(i),tuple(a),tuple(b)) for i,(a,b) in enumerate(out)]
if __name__=='__main__':
    from three_words import eval_word
    for i,a,b in equations():assert eval_word(a)==eval_word(b),i
    print('All 54 defining equations hold exactly')

