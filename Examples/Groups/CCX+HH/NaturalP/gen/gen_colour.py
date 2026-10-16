# Generates the cases of NaturalP/CtrlColour.agda for a gate at the
# bottom (or one wire up) against any other gate, and the dispatcher
# `opp`.  Usage: python3 gen_colour.py CtrlColour.agda (rewrites the
# block between the BEGIN/END GENERATED markers).
import sys
out_path = sys.argv[1]
SUP = {0:'', 1:'₁₊ ', 2:'₂₊ ', 3:'₃₊ ', 4:'₄₊ '}
def sucs(k, var):
    # an index of the form k + var, as a pattern/term
    if k == 0: return var
    if k <= 4: return '%s%s' % (SUP[k], var)
    return 'suc (%s)' % sucs(k-1, var)
def ups(k): return ' ↥' * k

# shapes: name, gate ctor, h ctor, arity b, pos pG, T, G pattern in sig (in m)
shapes = []
for (nm, ctor, h, b) in [('X','gate₁','X-gate',1), ('CX','gate₂','CX-gate',2), ('SW','gate₂','SW-gate',2),
                         ('HH','gate₂','HH-gate',2), ('CCX','gate₃','CCX-gate',3)]:
    borrow = nm in ('HH','CCX')
    # pos 0
    T0 = b + (1 if borrow else 0)
    shapes.append((nm+'0', ctor, h, b, 0, T0))
    shapes.append((nm+'1', ctor, h, b, 1, b+1))

def Gsig(ctor, h, b, pG):
    # G at width ₄₊ m: padding 4 - pG - b + m
    pad = 4 - pG - b
    s = '%s {%s} %s' % (ctor, sucs(pad, 'm'), h)
    return ('(%s ↥)' % s) if pG == 1 else '(%s)' % s

def G0(ctor, h, b, pG, w0):
    pad = w0 - pG - b
    s = '%s {%d} %s' % (ctor, pad, h)
    return ('%s ↥' % s) if pG == 1 else s

def B0(ctor, h, b, pG, T):
    # closed gadget on T+1 wires: CTRL of G at C-width T
    pad = T - pG - b
    s = '%s {%d} %s' % (ctor, pad, h)
    if pG == 1: s = s + ' ↥'
    return 'CTRL (%s)' % s

lines = []
A = lines.append
for (nm, ctor, h, b, pG, T) in shapes:
    fn = 'opp-' + nm
    G = Gsig(ctor, h, b, pG)
    A('')
    A('%s : ∀ f (g′ : Gen (₄₊ m)) → pos g′ ≤ f → Opp %s g′' % (fn, G))
    for q in range(T+1):
        A('%s f (gate₀ ()%s) _' % (fn, ups(q)))
        for (c, cc) in [(1,'gate₁'), (2,'gate₂'), (3,'gate₃')]:
            w0 = max(4, q + c)
            a = w0 - q - c
            pat = '%s {%s} h′%s' % (cc, sucs(a, 'j'), ups(q))
            g0 = '%s {%d} h′%s' % (cc, w0 - q - c, ups(q))
            A('%s f (%s) _ =' % (fn, pat))
            A('  coreO %d [ %s ]ʷ [ %s ]ʷ tt j' % (w0 - 4, G0(ctor, h, b, pG, w0), g0))
    K1 = T + 1
    A('%s zero (g%s) ()' % (fn, ups(K1)))
    A('%s (suc f) (g%s) (s≤s p) =' % (fn, ups(K1)))
    A('  PB.trans (PB.cong PB.refl E)')
    sub = {2:'₂',3:'₃',4:'₄',5:'₅'}[K1]
    A('  (PB.trans (PB.sym (conj-pass (apart%s B₀ (Z g)) (PB.sym IH) (apart%s B₀ (Z⁻ g))))' % (sub, sub))
    A('    (PB.cong (PB.sym E) PB.refl))')
    A('  where')
    A('  B₀ = %s' % B0(ctor, h, b, pG, T))
    A('  Xc = [ gate₁ {%d} X-gate ]ʷ' % T)
    A('  E = PB.trans (PB.cong PB.refl (PB.cong (emb (move (g%s))) PB.refl))' % ups(T-1))
    A('        (slide (PB.sym (apart%s Xc (Z g))) (PB.sym (apart%s Xc (Z⁻ g))))' % (sub, sub))
    A('  IH = subst-C (CTRL₁-⇓ (g%s))' % ups(T-1))
    A('         (%s f ((g ↧)%s) (Eq.subst (_≤ f) (Eq.sym (pos-↧ (g%s))) p))' % (fn, ups(T), ups(T)))

# dispatcher
D = []
B = D.append
B('')
B('opp : (g g′ : Gen (₄₊ m)) → Opp g g′')
B('opp (gate₀ ()) g′')
for (nm, ctor, h, b, pG, T) in shapes:
    if pG == 0:
        B('opp (%s %s) g′ = opp-%s (pos g′) g′ ≤-refl' % (ctor, h, nm))
B('opp (gate₀ () ↥) g′')
for (nm, ctor, h, b, pG, T) in shapes:
    if pG == 1:
        B('opp (%s %s ↥) g′ = opp-%s (pos g′) g′ ≤-refl' % (ctor, h, nm))
B('opp (g ↥ ↥) (gate₀ ())')
for (nm, ctor, h, b, pG, T) in shapes:
    if pG == 0:
        B('opp (g ↥ ↥) (%s %s) =' % (ctor, h)); B('  opp-sym {g = %s %s} {g′ = g ↥ ↥} (opp-%s (pos (g ↥ ↥)) (g ↥ ↥) ≤-refl)' % (ctor, h, nm))
B('opp (g ↥ ↥) (gate₀ () ↥)')
for (nm, ctor, h, b, pG, T) in shapes:
    if pG == 1:
        B('opp (g ↥ ↥) (%s %s ↥) =' % (ctor, h)); B('  opp-sym {g = %s %s ↥} {g′ = g ↥ ↥} (opp-%s (pos (g ↥ ↥)) (g ↥ ↥) ≤-refl)' % (ctor, h, nm))
B('opp {zero} (g ↥ ↥) (g′ ↥ ↥) =')
B('  complete≤ (le (suc (₄₊ zero)) tt)')
B('    {u = ctrl {₄₊ zero} [ g ↥ ↥ ]ʷ • ctrl⁻ {₄₊ zero} [ g′ ↥ ↥ ]ʷ}')
B('    {v = ctrl⁻ {₄₊ zero} [ g′ ↥ ↥ ]ʷ • ctrl {₄₊ zero} [ g ↥ ↥ ]ʷ}')
B('    (opposite-sem {zero} [ g ↥ ↥ ]ʷ [ g′ ↥ ↥ ]ʷ)')
B('opp {suc m} (g ↥ ↥) (g′ ↥ ↥) =')
B('  PB.trans (PB.cong (emb (fullmove g)) E′)')
B('  (PB.trans (conj-comm (emb (K⁻K (₃₊ m))) (top-cong (opp {m} (g ↥) (g′ ↥))))')
B('    (PB.sym (PB.cong E′ (emb (fullmove g)))))')
B('  where')
B('  E′ = PB.trans (PB.cong PB.refl (PB.cong (emb (fullmove g′)) PB.refl))')
B('         (slide (PB.sym (apart₂ X₂ (cy (₃₊ m)))) (PB.sym (apart₂ X₂ (cy⁻ (₃₊ m)))))')

src = open(out_path, encoding='utf-8').read()
src = src.replace('-- GENERATED-OPP --', '\n'.join(lines) + '\n' + '\n'.join(D))
open(out_path, 'w', encoding='utf-8').write(src)
