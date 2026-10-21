"""Write GatePermutations: each classical gate of Figure 4 as a Coxeter
word, from the permutation certificates of PermProofs.  (The frame
aliases and representative relations this script also wrote are gone:
TwoLevel derives them from the frame lemma.)"""
import generate as g
import generate_frames as f
ROOT=g.ROOT;P=g.PREFIX

CLASS={x for x in g.GATES if x.startswith(('X','CX','CCX','SWAP'))}
def classical(word):
    out=()
    for x in word.split():
        if len(x)==3 and x[0]=='t' and int(x[2])==int(x[1])+1:
            out+=(int(x[1]),)
        elif x in g.DEFS:out+=classical(g.DEFS[x])
        else:
            assert x in CLASS,x
            m=g.matrix(x)[1];p=tuple(next(i for i in range(8) if m[i][j]) for j in range(8))
            out+=f.decomposition(p)
    return out

s=f.imports('GatePermutations')
for x in sorted(CLASS):s+=f'import {P}.PermProofs.decode{x} as D{x}\n'
s+='\n'
for x in sorted(CLASS):
    s+=f'gate{x} : {x} ≈ {f.cp(classical(x))}\ngate{x} = by-assoc-and D{x}.proved Eq.refl Eq.refl\n\n'
for i in range(7):
    x='t'+str(i)+str(i+1)
    s+=f'gate{x} : {x} ≈ {f.cp((i,))}\ngate{x} = by-assoc Eq.refl\n\n'
(ROOT/'GatePermutations.agda').write_text(s,encoding='utf-8')
