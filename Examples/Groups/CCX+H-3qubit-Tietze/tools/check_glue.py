"""Check whether Section 5.5's defining K relation was retained."""
from fractions import Fraction as F
import generate as g
I=[[F(i==j) for j in range(8)] for i in range(8)]
T=[[I[i][j]-F(1,4) for j in range(8)] for i in range(8)]
def reading(w,twist=False):
    m=I
    for x in g.expand(w):
        d,a=g.matrix(x);assert d%2==0
        a=[[F(c,2**(d//2)) for c in row] for row in a]
        if twist and x not in ('NK','CCZ'):
            a=g.mul(g.mul(T,a),T)
        m=g.mul(m,a)
    return m
assert g.mul(T,T)==I
failed=[]
for n,(l,r) in g.RELATIONS.items():
    if n>=102:continue
    if reading(l,True)!=reading(r,True):failed.append(n)
print('Twisted model: failing corrected dyadic equations:',failed)
glue=('K12','X0 NK X0 NK')
print('Intended matrices satisfy K glue:',reading(glue[0])==reading(glue[1]))
print('Twisted model satisfies K glue:',reading(glue[0],True)==reading(glue[1],True))
assert not failed
assert reading(glue[0],True)!=reading(glue[1],True)
