from core import *
N=8
print('45 sem', eq(N,L45,R45), '46 sem', eq(N,L46,R46))
print('20 sem', eq(4,L20,R20), '21 sem', eq(6,L21,R21))
for sh in [(0,1,2,3),(0,2,1,3)]:
    l,r = d3(*sh); print('d3',sh, eq(4,l,r))
# rho for 46
rho = {0:2,1:3,2:5,3:4,4:6,5:7,6:1,7:0}
W46L = [H(2,3), H(2,4), H(3,5), H(4,6), H(5,7), H(4,5), H(6,7), H(6,7), Z(5), Z(4), H(4,6), H(5,7), H(2,4), H(3,5)]
W46R = [H(2,4), H(3,5), H(4,6), H(5,7), Z(5), Z(4), H(6,7), H(4,5), H(6,7), H(4,6), H(5,7), H(2,4), H(3,5), H(2,3)]
print('W46 sem (dim8)', eq(8,W46L,W46R))
# compare the tau images at all cosets with renamed 46 sides
for c in ['e','z','h','hz']:
    tl,cl = tstar(c,W46L); tr_,cr = tstar(c,W46R)
    print(c, cl, cr, len(tl), len(tr_))
    # check semantics: rep_c * W = tau * rep_c'
rep={'e':np.eye(N),'z':Zm(N,1),'h':Hm(N,0,1),'hz':Hm(N,0,1)@Zm(N,1)}
for c in rep:
    for w in (W46L,W46R):
        t,c2 = tstar(c,w)
        assert np.allclose(rep[c]@wmat(N,w), wmat(N,t)@rep[c2])
print('tau sem ok')
print(ren(rho,L46)); print(ren(rho,R46))
# parity of rho
perm=[rho[i] for i in range(8)]
inv=sum(1 for i in range(8) for j in range(i+1,8) if perm[i]>perm[j]); print('rho parity', inv%2)
# check Phi0 images
def phi0(w):
    out=[]
    i=0
    while i < len(w):
        g=w[i]
        if g[0]=='H': out.append(('hh',g[1],g[2],0,1)); i+=1
        elif g[0]=='Z': out.append(('zz',g[1],w[i+1][1])); i+=2
    return out
print(eq(N,phi0(W46L),ren(rho,L46)), eq(N,phi0(W46R),ren(rho,R46)))
print(eq(N,tstar('e',W46L)[0],phi0(W46L)), eq(N, tstar('h',W46L)[0], phi0(W46L)))
