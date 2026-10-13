"""Generates Examples/Groups/Qutrit-Clifford/Uniqueness.agda.  The box
actions are computed by pauli_act.py and asserted before emitting."""
import os
ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from pauli_act import act_inv, box
N = ['𝟎', '𝟏', '𝟐']
S = '₀₁₂'
I, Z, X = (0, 0), (0, 1), (1, 0)

def L(p):
    return {I: '𝐈', Z: '𝐙', X: '𝐗'}.get(p, '(%s , %s)' % (N[p[0]], N[p[1]]))

AS = [(a, b) for a in range(3) for b in range(3) if (a, b) != (0, 0)]
BS = [(a, b) for a in range(3) for b in range(3)]
nm = lambda k, ix: k + ''.join(S[i] for i in ix)

# check the actions before stating them
for a in AS:
    assert act_inv(box('A', a), (0, [Z, I])) == (0, [a, I])
for b in BS:
    assert act_inv(box('B', b), (0, [I, Z, I])) == (0, [Z, b, I])
    for i in range(3):
        assert act_inv(box('D', b), (0, [(1, i), I, I])) == (0, [b, (1, i), I])
    assert act_inv(box('D', b), (0, [Z, I, I])) == (0, [I, Z, I])
for c in range(3):
    assert act_inv(box('C', (c,)), (0, [Z])) == (c, [Z])
for e in range(3):
    assert act_inv(box('E', (e,)), (0, [X])) == (0, [(1, e)])
    assert act_inv(box('E', (e,)), (0, [Z])) == (0, [Z])
for f in range(3):
    assert act_inv(box('F', (f,)), (0, [X])) == (f, [X])
    assert act_inv(box('F', (f,)), (0, [Z])) == (0, [Z])

out = []
w = out.append
w('''------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal forms that act alike on Pauli operators are equal, but for
-- their scalar (the uniqueness half of the paper's Proposition 3.9)
--
-- A normal form W = N ↑ • M • L acts on Pauli operators by conjugation
-- (Pauli).  N ↑ fixes Z₀, the operator Z on wire 0, and the X-normal
-- circuit M moves Z from the top wire to wire 0 (Lemma 3.7), so W⁻¹
-- sends Z₀ to L⁻¹ Z_top L, which determines the Z-normal circuit L
-- (QZ-inj, the uniqueness half of Lemma 3.5); then (N ↑ • M)⁻¹ sends X₀
-- to M⁻¹ X₀ M, which determines M (QX-inj, Lemma 3.6); and N ↑ acts on
-- the wires above as N.  The scalar acts trivially; the matrix
-- semantics tells it.  The paper's first tensor factor is the top wire
-- here, its last one wire 0.
--
-- The boxes act on Pauli operators as Figure 8 requires, and with no
-- phase but C's and F's: read backwards, A_ab sends Z to X^a Z^b, B_ab
-- sends I below and Z above to Z below and X^a Z^b above, C_c
-- multiplies Z by ω^c, D_ab sends X Z^i below and I above to X^a Z^b
-- below and X Z^i above (and Z below to Z above), E_e sends X to X Z^e
-- and F_f multiplies X by ω^f.  So the letters a ladder leaves behind
-- tell its boxes apart, the phase tells C and F, and the letter on the
-- top wire E.  (The tables are generated: scratchpad qt/gen_uniq.py,
-- which checks every action against the Python model first.)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Uniqueness where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head ; tail)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)

open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₀ ; ₁₊ ; ₂₊)

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Engine using (⟪_⟫)
open import Examples.Groups.Qutrit-Clifford.NormalForm
open import Examples.Groups.Qutrit-Clifford.Pauli

private
  variable
    n m : ℕ

------------------------------------------------------------------------
-- Circuits that act alike

infix 4 _≗ᵃ_
_≗ᵃ_ : Circuit n → Circuit n → Set
w ≗ᵃ v = ∀ P → act w P ≡ act v P

-- Their inverses act alike.
≗ᵃ-inv : {w v : Circuit n} → w ≗ᵃ v → ∀ P → act⁻ w P ≡ act⁻ v P
≗ᵃ-inv {w = w} {v} e P = begin
  act⁻ w P                         ≡⟨ Eq.cong (act⁻ w) (Eq.sym (act-act⁻ v P)) ⟩
  act⁻ w (act v (act⁻ v P))        ≡⟨ Eq.cong (act⁻ w) (Eq.sym (e (act⁻ v P))) ⟩
  act⁻ w (act w (act⁻ v P))        ≡⟨ act⁻-act w (act⁻ v P) ⟩
  act⁻ v P                         ∎
  where open Eq.≡-Reasoning

-- A common last factor cancels.
≗ᵃ-cancel : {w v : Circuit n} (u : Circuit n) → (w • u) ≗ᵃ (v • u) → w ≗ᵃ v
≗ᵃ-cancel {w = w} {v} u e P = begin
  act w P                         ≡⟨ Eq.cong (act w) (Eq.sym (act-act⁻ u P)) ⟩
  act w (act u (act⁻ u P))        ≡⟨ e (act⁻ u P) ⟩
  act v (act u (act⁻ u P))        ≡⟨ Eq.cong (act v) (act-act⁻ u P) ⟩
  act v P                         ∎
  where open Eq.≡-Reasoning

-- Circuits one wire up act alike only if they do one wire down.
≗ᵃ-↑ : (w v : Circuit n) → (w ↑) ≗ᵃ (v ↑) → w ≗ᵃ v
≗ᵃ-↑ w v e (σ , ps) = Eq.cong (λ P → proj₁ P , tail (proj₂ P))
  (Eq.trans (Eq.sym (act-↑ w σ 𝐈 ps)) (Eq.trans (e (σ , 𝐈 ∷ ps)) (act-↑ v σ 𝐈 ps)))

-- The inverse of a circuit one wire up fixes wire 0 when the wires
-- above carry I.
fix-↑ : (w : Circuit n) (σ : Z3) (p : Letter) → act⁻ (w ↑) (σ , p ∷ I^ n) ≡ (σ , p ∷ I^ n)
fix-↑ w σ p = Eq.trans (act⁻-↑ w σ p (I^ _))
  (Eq.cong (λ P → proj₁ P , p ∷ proj₂ P) (act⁻-I w σ))

------------------------------------------------------------------------
-- Pauli operators on wire 0 and on the top wire

Z₀ X₀ : (n : ℕ) → Pauli (₁₊ n)
Z₀ n = 𝟎 , 𝐙 ∷ I^ n
X₀ n = 𝟎 , 𝐗 ∷ I^ n

ztop : (n : ℕ) → Vec Letter (₁₊ n)
ztop zero    = 𝐙 ∷ []
ztop (suc n) = 𝐈 ∷ ztop n

-- X Z^i.
xz : Z3 → Letter
xz i = 𝟏 , i

------------------------------------------------------------------------
-- The boxes on Pauli operators (Figure 8), read backwards

''')

def table(name, ty, rows):
    w('%s : %s\n' % (name, ty))
    for l, r in rows:
        w('%s %s = %s\n' % (name, l, r))
    w('\n')

table('ℓA', 'AT → Letter', [(nm('A', a), L(a)) for a in AS])
table('ℓB', 'BT → Letter', [(nm('B', b), L(b)) for b in BS])
table('ℓD', 'DT → Letter', [(nm('D', b), L(b)) for b in BS])
table('cx', 'CT → Z3', [(nm('C', (c,)), N[c]) for c in range(3)])
table('ex', 'ET → Z3', [(nm('E', (e,)), N[e]) for e in range(3)])
table('fx', 'FT → Z3', [(nm('F', (f,)), N[f]) for f in range(3)])

w('A-act : (a : AT) (σ : Z3) (R : Vec Letter n) →\n'
  '        act⁻ ⟪ Al a ⟫ (σ , 𝐙 ∷ R) ≡ (σ , ℓA a ∷ R)\n')
for a in AS:
    for s in range(3):
        w('A-act %s %s R = refl\n' % (nm('A', a), N[s]))
w('\nB-act : (b : BT) (σ : Z3) (R : Vec Letter n) →\n'
  '        act⁻ ⟪ Bl b ⟫ (σ , 𝐈 ∷ 𝐙 ∷ R) ≡ (σ , 𝐙 ∷ ℓB b ∷ R)\n')
for b in BS:
    for s in range(3):
        w('B-act %s %s R = refl\n' % (nm('B', b), N[s]))
w('\nC-act : (c : CT) → act⁻ ⟪ Cl c ⟫ (𝟎 , 𝐙 ∷ []) ≡ (cx c , 𝐙 ∷ [])\n')
for c in range(3):
    w('C-act %s = refl\n' % nm('C', (c,)))
w('\nD-act : (d : DT) (i σ : Z3) (R : Vec Letter n) →\n'
  '        act⁻ ⟪ Dl d ⟫ (σ , xz i ∷ 𝐈 ∷ R) ≡ (σ , ℓD d ∷ xz i ∷ R)\n')
for b in BS:
    for i in range(3):
        for s in range(3):
            w('D-act %s %s %s R = refl\n' % (nm('D', b), N[i], N[s]))
w('\nD-Z : (d : DT) (R : Vec Letter n) →\n'
  '      act⁻ ⟪ Dl d ⟫ (𝟎 , 𝐙 ∷ 𝐈 ∷ R) ≡ (𝟎 , 𝐈 ∷ 𝐙 ∷ R)\n')
for b in BS:
    w('D-Z %s R = refl\n' % nm('D', b))

w('''
------------------------------------------------------------------------
-- Reading the boxes back

pickA : Letter → AT
''')
for a in AS:
    w('pickA %s = %s\n' % (L(a), nm('A', a)))
w('pickA 𝐈 = A₀₁\n\npickA-ok : (a : AT) → pickA (ℓA a) ≡ a\n')
for a in AS:
    w('pickA-ok %s = refl\n' % nm('A', a))
w('\n𝐈≢ℓA : (a : AT) → 𝐈 ≢ ℓA a\n')
for a in AS:
    w('𝐈≢ℓA %s ()\n' % nm('A', a))
for k in 'BD':
    w('\npick%s : Letter → %sT\n' % (k, k))
    for b in BS:
        w('pick%s %s = %s\n' % (k, L(b), nm(k, b)))
    w('\npick%s-ok : (x : %sT) → pick%s (ℓ%s x) ≡ x\n' % (k, k, k, k))
    for b in BS:
        w('pick%s-ok %s = refl\n' % (k, nm(k, b)))
for k, ty in (('cx', 'CT'), ('ex', 'ET'), ('fx', 'FT')):
    w('\n%s-inj : (x y : %s) → %s x ≡ %s y → x ≡ y\n' % (k, ty, k, k))
    for c in range(3):
        w('%s-inj %s %s _ = refl\n' % (k, nm(ty[0], (c,)), nm(ty[0], (c,))))
    for c in range(3):
        for d in range(3):
            if c != d:
                w('%s-inj %s %s ()\n' % (k, nm(ty[0], (c,)), nm(ty[0], (d,))))

w('''
------------------------------------------------------------------------
-- X-normal circuits

-- A D-ladder, inverted, on X Z^i on wire 0.
QD : DL (₁₊ n) → Z3 → Z3 → Pauli (₁₊ n)
QD dl i σ = act⁻ ⟦ dl ⟧ᴰ (σ , xz i ∷ I^ _)

QD-step : (d : DT) (dl : DL (₁₊ n)) (i σ : Z3) →
          QD (d ∷ᴰ dl) i σ ≡ (proj₁ (QD dl i σ) , ℓD d ∷ proj₂ (QD dl i σ))
QD-step d dl i σ = Eq.trans (Eq.cong (act⁻ (⟦ dl ⟧ᴰ ↑)) (D-act d i σ (I^ _)))
  (act⁻-↑ ⟦ dl ⟧ᴰ σ (ℓD d) (xz i ∷ I^ _))

QD-inj : (dl dl' : DL (₁₊ n)) (i i' σ σ' : Z3) →
         QD dl i σ ≡ QD dl' i' σ' → dl ≡ dl' × i ≡ i' × σ ≡ σ'
QD-inj []ᴰ []ᴰ i i' σ σ' e = refl , Eq.cong (proj₂ ∘ head ∘ proj₂) e , Eq.cong proj₁ e
QD-inj (d ∷ᴰ dl) (d' ∷ᴰ dl') i i' σ σ' e
  with e' ← Eq.trans (Eq.sym (QD-step d dl i σ)) (Eq.trans e (QD-step d' dl' i' σ'))
  with refl ← Eq.trans (Eq.sym (pickD-ok d)) (Eq.trans (Eq.cong (pickD ∘ head ∘ proj₂) e') (pickD-ok d'))
  with (p , q , r) ← QD-inj dl dl' i i' σ σ' (Eq.cong (λ P → proj₁ P , tail (proj₂ P)) e')
  = Eq.cong (d ∷ᴰ_) p , q , r

-- An X-normal circuit, inverted, on X₀.
QX : Xc (₁₊ n) → Pauli (₁₊ n)
QX M = act⁻ ⟦ M ⟧ˣ (X₀ _)

QX-def : (e : ET) (f : FT) (dl : DL (₁₊ n)) → QX (xc e f dl) ≡ QD dl (ex e) (fx f)
''')
for e in range(3):
    for f in range(3):
        w('QX-def %s %s dl = refl\n' % (nm('E', (e,)), nm('F', (f,))))
w('''
QX-inj : (M M' : Xc (₁₊ n)) → QX M ≡ QX M' → M ≡ M'
QX-inj (xc e f dl) (xc e' f' dl') h
  with (p , q , r) ← QD-inj dl dl' (ex e) (ex e') (fx f) (fx f')
                       (Eq.trans (Eq.sym (QX-def e f dl)) (Eq.trans h (QX-def e' f' dl')))
  with refl ← p
  with refl ← ex-inj e e' q
  with refl ← fx-inj f f' r
  = refl

QD-Z : (dl : DL (₁₊ n)) → act⁻ ⟦ dl ⟧ᴰ (Z₀ n) ≡ (𝟎 , ztop n)
QD-Z []ᴰ       = refl
QD-Z (d ∷ᴰ dl) = Eq.trans (Eq.cong (act⁻ (⟦ dl ⟧ᴰ ↑)) (D-Z d (I^ _)))
  (Eq.trans (act⁻-↑ ⟦ dl ⟧ᴰ 𝟎 𝐈 (𝐙 ∷ I^ _))
            (Eq.cong (λ P → proj₁ P , 𝐈 ∷ proj₂ P) (QD-Z dl)))

-- Lemma 3.7, read backwards: an X-normal circuit moves Z from wire 0
-- to the top.
QX-Z : (M : Xc (₁₊ n)) → act⁻ ⟦ M ⟧ˣ (Z₀ n) ≡ (𝟎 , ztop n)
''')
for e in range(3):
    for f in range(3):
        w('QX-Z (xc %s %s dl) = QD-Z dl\n' % (nm('E', (e,)), nm('F', (f,))))
w('''
------------------------------------------------------------------------
-- Z-normal circuits

-- A ladder, inverted, on Z on the top wire.
QL : Lad (₁₊ n) → Pauli (₁₊ n)
QL lad = act⁻ ⟦ lad ⟧ᴸ (𝟎 , ztop _)

QL-up : (b : BT) (lad : Lad (₁₊ n)) →
        QL (b ∷ᴮ lad) ≡ act⁻ ⟪ Bl b ⟫ (proj₁ (QL lad) , 𝐈 ∷ proj₂ (QL lad))
QL-up b lad = Eq.cong (act⁻ ⟪ Bl b ⟫) (act⁻-↑ ⟦ lad ⟧ᴸ 𝟎 𝐈 (ztop _))

QL-head : (lad : Lad (₁₊ n)) → QL lad ≡ (proj₁ (QL lad) , 𝐙 ∷ tail (proj₂ (QL lad)))
QL-step : (b : BT) (lad : Lad (₁₊ n)) →
          QL (b ∷ᴮ lad) ≡ (proj₁ (QL lad) , 𝐙 ∷ ℓB b ∷ tail (proj₂ (QL lad)))

QL-step b lad = Eq.trans (QL-up b lad)
  (Eq.trans (Eq.cong (λ P → act⁻ ⟪ Bl b ⟫ (proj₁ P , 𝐈 ∷ proj₂ P)) (QL-head lad))
            (B-act b (proj₁ (QL lad)) (tail (proj₂ (QL lad)))))

QL-head (top c) = Eq.trans (C-act c) (Eq.sym (Eq.cong (λ P → proj₁ P , 𝐙 ∷ tail (proj₂ P)) (C-act c)))
QL-head (b ∷ᴮ lad) = Eq.trans (QL-step b lad)
  (Eq.sym (Eq.cong (λ P → proj₁ P , 𝐙 ∷ tail (proj₂ P)) (QL-step b lad)))

-- Equal phases and equal letters above the bottom wire, which carries Z.
QL-from : (lad lad' : Lad (₁₊ n)) → proj₁ (QL lad) ≡ proj₁ (QL lad') →
          tail (proj₂ (QL lad)) ≡ tail (proj₂ (QL lad')) → QL lad ≡ QL lad'
QL-from lad lad' p t =
  Eq.trans (QL-head lad) (Eq.trans (Eq.cong₂ (λ σ R → σ , 𝐙 ∷ R) p t) (Eq.sym (QL-head lad')))

QL-inj : (lad lad' : Lad (₁₊ n)) → QL lad ≡ QL lad' → lad ≡ lad'
QL-inj (top c) (top c') e =
  Eq.cong top (cx-inj c c' (Eq.cong proj₁ (Eq.trans (Eq.sym (C-act c)) (Eq.trans e (C-act c')))))
QL-inj (b ∷ᴮ lad) (b' ∷ᴮ lad') e
  with e' ← Eq.trans (Eq.sym (QL-step b lad)) (Eq.trans e (QL-step b' lad'))
  with refl ← Eq.trans (Eq.sym (pickB-ok b))
                (Eq.trans (Eq.cong (pickB ∘ head ∘ tail ∘ proj₂) e') (pickB-ok b'))
  = Eq.cong (b ∷ᴮ_) (QL-inj lad lad' (QL-from lad lad'
      (Eq.cong proj₁ e') (Eq.cong (tail ∘ tail ∘ proj₂) e')))

-- A Z-normal circuit, inverted, on Z on the top wire.
QZ : Zc (₁₊ n) → Pauli (₁₊ n)
QZ L = act⁻ ⟦ L ⟧ᶻ (𝟎 , ztop _)

QZ-up : (L : Zc (₁₊ n)) → QZ (up L) ≡ (proj₁ (QZ L) , 𝐈 ∷ proj₂ (QZ L))
QZ-up L = act⁻-↑ ⟦ L ⟧ᶻ 𝟎 𝐈 (ztop _)

QZ-at : (a : AT) (lad : Lad (₁₊ n)) →
        QZ (at a lad) ≡ (proj₁ (QL lad) , ℓA a ∷ tail (proj₂ (QL lad)))
QZ-at a lad = Eq.trans (Eq.cong (act⁻ ⟪ Al a ⟫) (QL-head lad))
  (A-act a (proj₁ (QL lad)) (tail (proj₂ (QL lad))))

QZ-inj : (L L' : Zc (₁₊ n)) → QZ L ≡ QZ L' → L ≡ L'
QZ-inj (up L) (up L') e = Eq.cong up (QZ-inj L L'
  (Eq.cong (λ P → proj₁ P , tail (proj₂ P)) (Eq.trans (Eq.sym (QZ-up L)) (Eq.trans e (QZ-up L')))))
QZ-inj (up L) (at a lad) e = ⊥-elim (𝐈≢ℓA a
  (Eq.cong (head ∘ proj₂) (Eq.trans (Eq.sym (QZ-up L)) (Eq.trans e (QZ-at a lad)))))
QZ-inj (at a lad) (up L) e = ⊥-elim (𝐈≢ℓA a
  (Eq.cong (head ∘ proj₂) (Eq.trans (Eq.sym (QZ-up L)) (Eq.trans (Eq.sym e) (QZ-at a lad)))))
QZ-inj (at a lad) (at a' lad') e
  with e' ← Eq.trans (Eq.sym (QZ-at a lad)) (Eq.trans e (QZ-at a' lad'))
  with refl ← Eq.trans (Eq.sym (pickA-ok a)) (Eq.trans (Eq.cong (pickA ∘ head ∘ proj₂) e') (pickA-ok a'))
  = Eq.cong (at a) (QL-inj lad lad' (QL-from lad lad'
      (Eq.cong proj₁ e') (Eq.cong (tail ∘ proj₂) e')))

------------------------------------------------------------------------
-- Normal forms

-- The scalar, and the normal form with scalar 1.
phase : NF n → Fin 6
phase (nf₀ t)     = t
phase (nfₛ _ _ N) = phase N

unphase : NF n → NF n
unphase (nf₀ _)     = nf₀ ₀
unphase (nfₛ L M N) = nfₛ L M (unphase N)

-- A normal form is its scalar and the rest.
unphase-phase : (nf nf' : NF n) → unphase nf ≡ unphase nf' → phase nf ≡ phase nf' → nf ≡ nf'
unphase-phase (nf₀ t)     (nf₀ t')       _ e' = Eq.cong nf₀ e'
unphase-phase (nfₛ L M N) (nfₛ L' M' N') e e' =
  Eq.cong₂ (λ p N → nfₛ (proj₁ p) (proj₂ p) N) (Eq.cong heads e) (unphase-phase N N' (Eq.cong rest e) e')
  where
  heads : NF (₁₊ m) → Zc (₁₊ m) × Xc (₁₊ m)
  heads (nfₛ L M _) = L , M
  rest : NF (₁₊ m) → NF m
  rest (nfₛ _ _ N) = N

-- The inverse of a normal form on Z₀, and of its last two parts on X₀.
nf-Z : (L : Zc (₁₊ n)) (M : Xc (₁₊ n)) (N : NF n) → act⁻ ⟦ nfₛ L M N ⟧ⁿ (Z₀ n) ≡ QZ L
nf-Z L M N = Eq.cong (act⁻ ⟦ L ⟧ᶻ)
  (Eq.trans (Eq.cong (act⁻ ⟦ M ⟧ˣ) (fix-↑ ⟦ N ⟧ⁿ 𝟎 𝐙)) (QX-Z M))

nf-X : (M : Xc (₁₊ n)) (N : NF n) → act⁻ (⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ) (X₀ n) ≡ QX M
nf-X M N = Eq.cong (act⁻ ⟦ M ⟧ˣ) (fix-↑ ⟦ N ⟧ⁿ 𝟎 𝐗)

act-unique : (nf nf' : NF n) → ⟦ nf ⟧ⁿ ≗ᵃ ⟦ nf' ⟧ⁿ → unphase nf ≡ unphase nf'
act-unique (nf₀ _) (nf₀ _) e = refl
act-unique (nfₛ L M N) (nfₛ L' M' N') e
  with refl ← QZ-inj L L' (Eq.trans (Eq.sym (nf-Z L M N))
                (Eq.trans (≗ᵃ-inv {w = ⟦ nfₛ L M N ⟧ⁿ} {v = ⟦ nfₛ L' M' N' ⟧ⁿ} e (Z₀ _))
                          (nf-Z L' M' N')))
  with e₂ ← ≗ᵃ-cancel {w = ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ} {v = ⟦ N' ⟧ⁿ ↑ • ⟦ M' ⟧ˣ} ⟦ L ⟧ᶻ e
  with refl ← QX-inj M M' (Eq.trans (Eq.sym (nf-X M N))
                (Eq.trans (≗ᵃ-inv {w = ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ} {v = ⟦ N' ⟧ⁿ ↑ • ⟦ M' ⟧ˣ} e₂ (X₀ _))
                          (nf-X M' N')))
  = Eq.cong (nfₛ L M) (act-unique N N' (≗ᵃ-↑ ⟦ N ⟧ⁿ ⟦ N' ⟧ⁿ
      (≗ᵃ-cancel {w = ⟦ N ⟧ⁿ ↑} {v = ⟦ N' ⟧ⁿ ↑} ⟦ M ⟧ˣ e₂)))
''')
open(ROOT + '/Uniqueness.agda', 'w',
     encoding='utf-8', newline='\n').write(''.join(out))
print('written')
