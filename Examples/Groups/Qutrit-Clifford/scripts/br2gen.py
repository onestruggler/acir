"""Derive the two-qutrit box relations through the proof-producing coset
table (relcos2), and measure / emit the lemmas they need."""
import os
ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import sys, time
import relcos2 as T
import felsch as F
import relcos as RC
from br2rels import REL
S = T.S

t0 = time.time()
assert F.run()
print('table %.0fs' % (time.time() - t0), file=sys.stderr)

def derive_rel(l, r):
    sl, laml, cl = T.trace(0, l)
    sr, lamr, cr = T.trace(0, r)
    assert cl == cr and laml == lamr, (l, r, laml, lamr, cl, cr)
    st = sl + T.rev(sr)
    S.check_path(l, st, r)
    return st

PROOFS = []
for f, args, l, r in REL:
    PROOFS.append((f, args, l, r, derive_rel(l, r)))
need = S.needed([st for *_, st in PROOFS])
print('lemmas needed', len(need), 'named', sum(1 for i in need if S.eqs[i]['name'] is not None), file=sys.stderr)
lens = sorted(len(S.eqs[i]['steps'] or []) for i in need)
print('steps per lemma: max', lens[-1], 'median', lens[len(lens)//2], file=sys.stderr)
wl = sorted(max(len(S.eqs[i]['l']), len(S.eqs[i]['r'])) for i in need)
print('word length: max', wl[-1], 'median', wl[len(wl)//2], file=sys.stderr)

if len(sys.argv) > 1 and sys.argv[1] == 'test':
    from emit2 import Emitter, HEADER, COMMS
    E = Emitter(S)
    gen = E.generated(need)
    print('generated lemmas', len(gen), file=sys.stderr)
    k = int(sys.argv[2])
    body = ''.join(E.lemma(i) + '\n' for i in gen[:k])
    src = HEADER.format(title='Test slice of the two-qutrit derivations', mod='Box2Test', imports='') + COMMS + body
    open(ROOT + '/Box2Test.agda', 'w', encoding='utf-8', newline='\n').write(src)
    print('written', k, file=sys.stderr)

if len(sys.argv) > 1 and sys.argv[1] == 'emit':
    import os
    from emit2 import Emitter, HEADER, COMMS, alist
    E = Emitter(S)
    gen = E.generated(need)
    size = int(sys.argv[2])
    base = ROOT + '/'
    os.makedirs(base + 'Box2', exist_ok=True)
    parts = [gen[i:i + size] for i in range(0, len(gen), size)]
    for k, part in enumerate(parts, 1):
        imp = ('open import Examples.Groups.Qutrit-Clifford.Box2.Part%d public\n' % (k - 1)) if k > 1 else ''
        body = (COMMS if k == 1 else '') + ''.join(E.lemma(i) + '\n' for i in part)
        src = HEADER.format(title='Two-qutrit lemmas, part %d of %d' % (k, len(parts)),
                            mod='Box2.Part%d' % k, imports=imp) + body
        open(base + 'Box2/Part%d.agda' % k, 'w', encoding='utf-8', newline='\n').write(src)
    # the relations and the record
    names = {}
    out = []
    w = out.append
    for f, args, l, r, st in PROOFS:
        nm = 'b-%s-%s' % (f, '-'.join(a.strip('()').replace(' ', '') for a in args)) if args else 'b-%s' % f
        names[(f, args)] = nm
        steps = E.steps(l, st)
        w('%s : Eqn (₂₊ n)\n%s = derive (%s)\n  (%s)\n  (%s) refl\n\n' % (nm, nm, alist(l), alist(r), steps))
    def clauses(fam, fld, ty, pat):
        w('  %s : %s\n' % (fld, ty))
        for (f, args), nm in names.items():
            if f == fam:
                w('  %s %s = prf %s\n' % (fld, pat(args), nm))
    w('''br₂ : BoxRelations₂
br₂ = record
  { ruleAup-ok = Aup-ok ; ruleAB-ok = AB-ok ; ruleB-ok = B-ok ; ruleSC-ok = SC-ok
  ; ruleD-ok = D-ok ; ruleS1D-ok = S1D-ok ; ruleZ1D-ok = Z1D-ok ; ruleCD-ok = CD-ok
  ; id₂-ok = prf b-id₂ }
  where
''')
    sp = lambda args: ' '.join(args)
    clauses('ruleAup', 'Aup-ok', '∀ {n} (a : AT) →\n    (₂₊ n) ⊢ ⟪ map _↥ (Al a) ++ c₀ ∷ [] ⟫ ≈ ⟪ Aupr (ruleAup a) ⟫', sp)
    clauses('ruleAB', 'AB-ok', '∀ {n} (a : AT) (b : BT) →\n    (₂₊ n) ⊢ ⟪ Bl b ++ Al a ++ c₀ ∷ [] ⟫ ≈ ⟪ ABr (ruleAB a b) ⟫', sp)
    clauses('ruleB', 'B-ok', '∀ {n} (b : BT) (g : In1) →\n    (₂₊ n) ⊢ ⟪ Bl b ++ In1l g ⟫ ≈ ⟪ Pls (proj₂ (ruleB b g)) ++ Bl (proj₁ (ruleB b g)) ⟫', sp)
    clauses('ruleSC', 'SC-ok', '∀ {n} (c : CT) →\n    (₂₊ n) ⊢ ⟪ map _↥ (Cl c) ++ c₀ ∷ [] ⟫ ≈ ⟪ SCOls (proj₂ (ruleSC c)) ++ map _↥ (Cl (proj₁ (ruleSC c))) ⟫', sp)
    clauses('ruleD', 'D-ok', '∀ {n} (d : DT) (h : HS) →\n    (₂₊ n) ⊢ ⟪ Dl d ++ HSl h ⟫ ≈ ⟪ O2ls (proj₂ (ruleD d h)) ++ Dl (proj₁ (ruleD d h)) ⟫', sp)
    clauses('ruleS1D', 'S1D-ok', '∀ {n} (d : DT) → (₂₊ n) ⊢ ⟪ Dl d ++ s₁ ∷ [] ⟫ ≈ ⟪ s₀ ∷ Dl d ⟫', sp)
    clauses('ruleZ1D', 'Z1D-ok', '∀ {n} (d : DT) → (₂₊ n) ⊢ ⟪ Dl d ++ map _↥ Zˡ ⟫ ≈ ⟪ Zˡ ++ Dl d ⟫', sp)
    clauses('ruleCD', 'CD-ok', '∀ {n} (d : DT) →\n    (₂₊ n) ⊢ ⟪ Dl d ++ c₀ ∷ [] ⟫ ≈ ⟪ O2ls (proj₂ (ruleCD d)) ++ Dl (proj₁ (ruleCD d)) ⟫', sp)
    head = HEADER.format(title='The box relations on two qutrits (Appendix C.3), derived from C₁–C₁₄',
                         mod='Box2', imports='open import Examples.Groups.Qutrit-Clifford.Box2.Part%d\n' % len(parts))
    head = head.replace('open import Data.List.Base using (List ; [] ; _∷_)',
                        'open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)\nopen import Data.Product.Base using (proj₁ ; proj₂)')
    head = head.replace('using (Eqn ; sym⁼ ; lift⁼ ; derive ; perm ; rw)', 'using (Eqn ; prf ; sym⁼ ; lift⁼ ; derive ; perm ; rw ; ⟪_⟫)')
    head = head.replace('open import Examples.Groups.Qutrit-Clifford.Axioms\n',
                        'open import Examples.Groups.Qutrit-Clifford.Axioms\nopen import Examples.Groups.Qutrit-Clifford.NormalForm\nopen import Examples.Groups.Qutrit-Clifford.Tables\n')
    open(base + 'Box2.agda', 'w', encoding='utf-8', newline='\n').write(head + ''.join(out))
    print('emitted', len(parts), 'parts', file=sys.stderr)

if len(sys.argv) > 1 and sys.argv[1] == 'stats':
    from emit2 import Emitter
    E = Emitter(S)
    gen = E.generated(need)
    sizes = sorted(((len(S.eqs[i]['steps']) * max(len(S.eqs[i]['l']), len(S.eqs[i]['r']), 1), i) for i in gen), reverse=True)
    tot = sum(s for s, _ in sizes)
    print('total step*len', tot, file=sys.stderr)
    acc = 0
    for k, (s, i) in enumerate(sizes):
        acc += s
        if k in (10, 100, 1000): print('top', k, 'share', acc / tot, file=sys.stderr)
    for s, i in sizes[:8]:
        e = S.eqs[i]
        kinds = {}
        for (p, j, d) in e['steps']:
            if j == 'P': kinds['P'] = kinds.get('P', 0) + 1; continue
            nm = S.eqs[j]['name']
            key = 'comm' if (isinstance(nm, str) and nm.startswith('comm')) else ('ax' if nm else 'lemma')
            kinds[key] = kinds.get(key, 0) + 1
        print(i, len(e['steps']), len(e['l']), len(e['r']), kinds, file=sys.stderr)
    # share of comm steps overall
    comm = sum(1 for i in gen for (p, j, d) in S.eqs[i]['steps'] if j != 'P' and isinstance(S.eqs[j]['name'], str) and S.eqs[j]['name'].startswith('comm'))
    allst = sum(len(S.eqs[i]['steps']) for i in gen)
    print('comm steps', comm, 'of', allst, file=sys.stderr)
    dl = sorted(len(T.defw[k]) for k in range(len(T.defw)) if T.alive[k])
    print('alive def lengths', dl[-5:], 'median', dl[len(dl)//2], file=sys.stderr)
