"""Generator round trips, using proved permutation and diagonal calculus."""
import pickle
import sys
import time
import numpy as np
from collections import deque
from pathlib import Path
from table import Deriv, invert
from pc import prove_any, unfold_to
from cross import DIAG, support_vals, matw
from face_transport import FaceProof
from ctv import word_of
from kb import KB
import b2q1

CACHE = Path('../../../.handover-scratch/cs3/phase-c-current.pkl')


def diagword(m):
    assert np.allclose(m, np.diag(np.diag(m)))
    ph = [int(round(np.angle(z) / (np.pi / 2))) % 4 for z in np.diag(m)]
    e = [ph[0], ph[4]-ph[0], ph[2]-ph[0], ph[1]-ph[0],
         ph[6]-ph[4]-ph[2]+ph[0], ph[3]-ph[2]-ph[1]+ph[0],
         ph[5]-ph[4]-ph[1]+ph[0]]
    last = (ph[7] - sum(e)) % 4
    assert last % 2 == 0, ph
    return tuple(z for z, k in zip(DIAG, [v % 4 for v in e] + [last // 2]) for _ in range(k))


class Roundtrip:
    def __init__(self, P, CT, faces, done):
        self.P, self.T, self.A, self.CT, self.faces = P, P.T, P.A, CT, faces
        self.toks = ['T%d' % i for i in range(7)]
        self.kb = KB(self.T, self.toks)
        for (nm, c), e in done.items():
            if c == 'I' and e is not None:
                l, r, _ = self.T.eqs[e]
                if set(l+r) <= set(self.toks):
                    self.kb.add_equation(e)
        assert self.kb.complete()
        self.edges, self.etok, self.etok_eq = {}, {}, {}
        for p in range(8):
            for q in range(p+1, 8):
                if p ^ q not in (1, 2, 4):
                    continue
                t = {4:0, 2:1, 1:2}[p ^ q]
                flips = tuple('X%d' % s for s in range(3) if s != t and not (p >> (2-s)) & 1)
                z = 'E%d%d' % (p, q)
                self.A.define(z, flips + ('CCX%d' % t,) + flips[::-1])
                self.edges[p,q] = z
        for i in range(7):
            pq = tuple(sorted(b2q1.GRAY[i:i+2]))
            self.etok[pq] = ('T%d' % i,)
            self.etok_eq[pq] = prove_any(P, (self.edges[pq],), self.etok[pq])
        for p, q, path in [(0,1,[0,2,3,1]), (4,5,[4,0,1,5]),
                           (3,7,[3,1,5,7]), (2,6,[2,0,4,6]), (6,7,[6,4,5,7])]:
            pp = [tuple(sorted((a,b))) for a,b in zip(path,path[1:])]
            edgew = tuple(self.edges[e] for e in pp + pp[-2::-1])
            z = self.edges[p,q]
            common = set(support_vals(self.A.mats[z]).items())
            for a in edgew:
                common &= set(support_vals(self.A.mats[a]).items())
            s,x = next(iter(common))
            F = self.face(s,x)
            eq = F.prove((z,), edgew)
            D = Deriv(self.T, (z,)); D.step(0,eq)
            off = 0
            for e in pp + pp[-2::-1]:
                D.step(off, self.etok_eq[e]); off += len(self.etok[e])
            self.etok[p,q] = D.w
            self.etok_eq[p,q] = self.T.derived((z,),D.w,D.steps)
        self.classical = {}
        for q in range(3):
            self.classical_word('X%d' % q, [e for e in self.edges if e[0]^e[1] == 1 << (2-q)])
        for c in range(3):
            for t in range(3):
                if c == t: continue
                self.classical_word('CX%d%d' % (c,t), [e for e in self.edges if e[0]^e[1] == 1 << (2-t) and (e[0] >> (2-c)) & 1])
        for sw, word in [('SW01', ('CX01','CX10','CX01')), ('SW12', ('CX12','CX21','CX12'))]:
            D = Deriv(self.T, (sw,))
            D.step(0,prove_any(P,(sw,),word))
            self.expand_classical(D)
            self.classical[sw] = (D.w,self.T.derived((sw,),D.w,D.steps))
        self.stabilizer = self.stab_words()

    def face(self,s,x):
        if (s,x) not in self.faces:
            self.faces[s,x] = FaceProof(self.P,self.CT,s,x)
        return self.faces[s,x]

    def classical_word(self,z,edges):
        w = tuple(self.edges[e] for e in edges)
        D = Deriv(self.T,(z,)); D.step(0,prove_any(self.P,(z,),w))
        off = 0
        for e in edges:
            D.step(off,self.etok_eq[e]); off += len(self.etok[e])
        self.classical[z] = (D.w,self.T.derived((z,),D.w,D.steps))

    def expand_classical(self,D):
        off = 0
        while off < len(D.w):
            z = D.w[off]
            if z in self.classical:
                w,e = self.classical[z]; D.step(off,e); off += len(w)
            else: off += 1

    def perm_eq(self,u,v):
        nu,su = self.kb.reduce(tuple(u)); nv,sv = self.kb.reduce(tuple(v))
        assert nu == nv,(u,v,nu,nv)
        return self.T.derived(tuple(u),tuple(v),su+invert(sv))

    def monomial(self,w):
        D = Deriv(self.T,tuple(w))
        pos = 0
        while pos < len(D.w):
            if D.w[pos] == 'T6J':
                D.step(pos,prove_any(self.P,('T6J',),('T6','C02','CCZ')))
            pos += 1
        # Push each diagonal letter left through the token prefix.
        pos = 0
        while pos < len(D.w):
            if D.w[pos] in self.toks:
                pos += 1; continue
            assert D.w[pos] in DIAG,D.w[pos]
            start = pos
            dw = (D.w[pos],)
            while start > 0 and D.w[start-1] in self.toks:
                t = D.w[start-1]
                mt = self.A.mats[t]
                nd = diagword(mt @ matw(self.P,dw) @ mt)
                e = prove_any(self.P,(t,)+dw,nd+(t,))
                D.step(start-1,e)
                start -= 1
                pos += len(nd)-len(dw)
                dw = nd
            # All preceding letters are now diagonal; normalize them together.
            end = start + len(dw)
            old = D.w[:end]; new = diagword(matw(self.P,old))
            if old != new:
                D.step(0,prove_any(self.P,old,new))
            pos += len(new)-len(old)
            pos += 1
        split = next((i for i,z in enumerate(D.w) if z in self.toks),len(D.w))
        diag, perm = D.w[:split],D.w[split:]
        assert set(diag) <= set(DIAG) and set(perm) <= set(self.toks),D.w
        nf, steps = self.kb.reduce(perm)
        D.steps_at(steps,split)
        return D,diag,tuple(nf)

    def monomial_eq(self,u,v):
        Du,_,_ = self.monomial(u); Dv,_,_ = self.monomial(v)
        assert Du.w == Dv.w,(u,v,Du.w,Dv.w)
        return self.T.derived(tuple(u),tuple(v),Du.steps+invert(Dv.steps))

    def stab_words(self):
        I = tuple(range(8)); out = {I:()}; todo = deque([I])
        while todo:
            p = todo.popleft()
            for d in range(5):
                q = b2q1.M8.tperm(d); p2=tuple(q[x] for x in p)
                if p2 not in out: out[p2]=('T%d'%d,)+out[p]; todo.append(p2)
        return out

    def conj(self,F,k,p,q):
        P,T = self.P,self.T
        target={4:0,2:1,1:2}[p^q]
        sw = {0:'SW01',1:None,2:'SW12'}[target]
        src = {0:3,1:5,2:6}[target]
        flips = tuple('X%d'%s for s in range(3) if s != target and ((p^src)>>(2-s))&1)
        aff = flips + ((sw,) if sw else ())
        DA = Deriv(T,aff); self.expand_classical(DA); AF=DA.w
        pF = b2q1.M8.perm_of([('t',int(z[1:])) for z in F])
        pA = b2q1.M8.perm_of([('t',int(z[1:])) for z in AF])
        invA = [pA.index(i) for i in range(8)]
        S = self.stabilizer[tuple(invA[pF[i]] for i in range(8))]
        D = Deriv(T,F+(k,)+F[::-1])
        D.step(0,self.perm_eq(F,AF+S))
        D.step(len(AF)+len(S)+1,self.perm_eq(F[::-1],S[::-1]+AF[::-1]))
        for i in range(len(S)-1,-1,-1):
            D.step(len(AF)+i,prove_any(P,(S[i],k),(k,S[i])))
        D.step(len(AF)+1,self.perm_eq(S+S[::-1],()))
        ea = T.derived(aff,AF,DA.steps)
        D.step(0,ea,False)
        DAR = Deriv(T,aff[::-1]); self.expand_classical(DAR)
        er = self.perm_eq(AF[::-1],DAR.w)
        D.step(len(aff)+1,er)
        D.steps_at(invert(DAR.steps),len(aff)+1)
        if sw:
            # The swap conjugates every base letter by its proved relabelling rule.
            DK = unfold_to(P, (k,), set(P.sig[sw]))
            kw = DK.w
            swkw = (sw,)+kw+(sw,)
            DE = Deriv(T,(sw,k,sw)); DE.steps_at(DK.steps,1)
            assert DE.w == swkw
            for j in range(len(kw)-1,0,-1): DE.step(1+j,P.cancel(sw),False)
            for j,z in enumerate(kw): DE.step(j,P.push(sw,z))
            ek = T.derived((sw,k,sw),DE.w,DE.steps)
            D.step(len(flips),ek)
        m = matw(P,F+(k,)+F[::-1])
        mm = self.A.mats[sw] @ m @ self.A.mats[sw] if sw else m
        wd = word_of(P.W.B1,mm)
        assert wd is not None,(p,q,k)
        wd = P.sigma(sw,wd) if sw else tuple(wd)
        D.step(0,prove_any(P,D.w,wd))
        return wd,T.derived(F+(k,)+F[::-1],wd,D.steps)

    def atom(self,c,g):
        M = b2q1.M8
        enc = M.enc(g)
        u,c2 = b2q1.hstarM(c,enc)
        if g[0]=='i':
            D,diag,perm=self.monomial(u)
            assert not perm
            return D.w,self.T.derived(u,D.w,D.steps),c2
        F=tuple('T%d'%d[1] for d in M.vE(g[1],g[2]))
        left,cc=b2q1.hstarM(c,M.vE(g[1],g[2]))
        middle,cc=b2q1.letter_action(cc,'K')
        right,_=b2q1.hstarM(cc,list(reversed(M.vE(g[1],g[2]))))
        DL,dl,fl=self.monomial(left)
        DR,dr,fr=self.monomial(right)
        D=Deriv(self.T,u)
        D.steps_at(DL.steps,0); D.steps_at(DR.steps,len(DL.w)+1)
        # Restore the selected frame on both sides after normalizing its diagonal.
        D.step(len(dl),self.perm_eq(fl,F))
        D.step(len(dl)+len(F)+1+len(dr),self.perm_eq(fr,F[::-1]))
        d2=diagword(matw(self.P,F+dr+F[::-1]))
        D.step(len(dl)+len(F)+1,self.monomial_eq(dr+F[::-1],F[::-1]+d2))
        wk,ek=self.conj(F,middle[0],g[1],g[2])
        D.step(len(dl),ek)
        return D.w,self.T.derived(u,D.w,D.steps),c2

    def prove_a(self):
        out={}
        for x,gens in b2q1.FG.items():
            u,_=b2q1.hstarM('I',b2q1.M8.enc_word(gens))
            D=Deriv(self.T,u); off=0;c='I'
            for g in gens:
                w,e,c=self.atom(c,g); D.step(off,e); off+=len(w)
            D.step(0,prove_any(self.P,D.w,(x,)))
            out[x]=self.T.derived(u,(x,),D.steps)
            print('roundtrip',x,'proved',flush=True)
        return out


def main():
    sys.setrecursionlimit(1000000)
    start=time.monotonic()
    with CACHE.open('rb') as f: P,CT,faces,done,missing=pickle.load(f)
    R=Roundtrip(P,CT,faces,done)
    print('permutation calculus ready',time.monotonic()-start,flush=True)
    aa=R.prove_a()
    with CACHE.with_name('phase-c-roundtrips.pkl').open('wb') as f:
        pickle.dump((P,CT,faces,done,missing,aa),f,pickle.HIGHEST_PROTOCOL)
    print('all roundtrips proved',time.monotonic()-start,flush=True)


if __name__=='__main__': main()
