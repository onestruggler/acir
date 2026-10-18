------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness for affine circuits, given completeness on at most
-- eight wires, in the calculus with the schema.
--
-- An affine circuit is a word in X, CX and the swap (`AGen`).  Two
-- affine circuits with the same matrix are equal (`affine-complete`).
-- The proof borrows the completeness of Amy, Chen and Ross's
-- CNOT-dihedral relations (`CNOT+Dihedral.Completeness`): erasing T
-- and ω (`E`) carries their derivations into this calculus, since every
-- one of their relations, erased, is an equation of affine circuits on
-- at most four wires (proved here by evaluation), a swap rule, or a
-- structural rule.  Their CNOT is our CX (control on wire 1), and both
-- developments read wire 0 as the first bit.  An affine word read in
-- their semantics picks up no phase, and its permutation is the
-- classical action of GeneralN/Classical, which the matrix determines
-- column by column.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Schema as S
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)

module Examples.Groups.CCX+HH.NaturalP.Affine
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  where

open import Data.Bool.Base using (Bool ; true ; false ; T ; not ; _xor_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat.Base using (zero ; suc ; _≤ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec ; _∷_ ; lookup ; tabulate)
open import Data.Vec.Properties using (tabulate∘lookup ; tabulate-cong)
open import Relation.Binary.PropositionalEquality as Eq
  using (refl ; sym ; trans ; cong ; cong₂ ; subst₂ ; _≢_)
open import Relation.Nullary.Decidable using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap ; _^_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ)
open import Examples.Groups.CCX+HH.Decide using (by-eq)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (col ; δ-refl ; δ-≢ ; _!_)
import Examples.Groups.CCX+HH.Semantics as Sem
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (ket ; physical-column)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (idx ; bits ; bits-idx ; idx-injective)
open import Examples.Groups.CCX+HH.GeneralN.BasisVectors using (basis ; basis-!)

import Examples.Groups.CNOT+Dihedral.Syntactics as CD
import Examples.Groups.CNOT+Dihedral.Semantics as CDS
import Examples.Groups.CNOT+Dihedral.Evaluation as CDE
import Examples.Groups.CNOT+Dihedral.Interpretation as CDI
open import Examples.Groups.CNOT+Dihedral.Completeness using () renaming (complete to cd-complete)

private
  variable
    n : ℕ

  le : ∀ a → T (a ≤ᵇ 8) → a ≤ 8
  le a p = ≤ᵇ⇒≤ a 8 p

------------------------------------------------------------------------
-- Affine words

infixl 9 _↥ₐ
data AGen : ℕ → Set where
  ax      : AGen (₁₊ n)
  acx asw : AGen (₂₊ n)
  _↥ₐ     : AGen n → AGen (₁₊ n)

-- In this calculus, in CNOT+Dihedral's, and as a classical circuit.
ιP : AGen n → Gen n
ιP ax       = gate₁ X-gate
ιP acx      = gate₂ CX-gate
ιP asw      = gate₂ SW-gate
ιP (g ↥ₐ)   = ιP g ↥

ιD : AGen n → CD.Gen n
ιD ax       = CD.gate₁ CD.X-gate
ιD acx      = CD.gate₂ CD.CNOT-gate
ιD asw      = CD.gate₂ CD.SWAP-gate
ιD (g ↥ₐ)   = ιD g CD.↥

ιC : AGen n → C.Gen n
ιC ax       = C.gate₁ C.X-gate
ιC acx      = C.gate₂ C.CX-gate
ιC asw      = C.gate₂ C.SWAP-gate
ιC (g ↥ₐ)   = ιC g C.↥

⌈_⌉ : Word (AGen n) → Circuit n
⌈_⌉ = wmap ιP

------------------------------------------------------------------------
-- Erasing T and ω

E : CD.Gen n → Circuit n
E (CD.gate₀ CD.ω-gate)    = ε
E (CD.gate₁ CD.X-gate)    = X
E (CD.gate₁ CD.T-gate)    = ε
E (CD.gate₂ CD.CNOT-gate) = CX
E (CD.gate₂ CD.SWAP-gate) = σ
E (g CD.↥)                = E g ↑

E-↑ : (w : CD.Circuit n) → (E ʷ) (w CD.↑) ≡ (E ʷ) w ↑
E-↑ [ g ]ʷ  = refl
E-↑ ε       = refl
E-↑ (u • v) = cong₂ _•_ (E-↑ u) (E-↑ v)

E-ι : (a : Word (AGen n)) → (E ʷ) (wmap ιD a) ≡ ⌈ a ⌉
E-ι [ g ]ʷ  = E-g g
  where
  E-g : (g : AGen n) → E (ιD g) ≡ [ ιP g ]ʷ
  E-g ax     = refl
  E-g acx    = refl
  E-g asw    = refl
  E-g (g ↥ₐ) = cong _↑ (E-g g)
E-ι ε       = refl
E-ι (u • v) = cong₂ _•_ (E-ι u) (E-ι v)

-- The relations of Amy, Chen and Ross, erased, on their own wires.
private
  opaque
    unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

    R₂₀ : 2 ⊢ (E ʷ) (CD.CNOT • CD.X • CD.CNOT) ≈ (E ʷ) CD.X
    R₂₀ = complete≤ (le 2 tt) {u = (E ʷ) (CD.CNOT • CD.X • CD.CNOT)} {v = (E ʷ) CD.X}
      (by-eq tt)

    R₃₀ : 2 ⊢ (E ʷ) (CD.CNOT • CD.X CD.↑ • CD.CNOT) ≈ (E ʷ) (CD.X CD.↑ • CD.X)
    R₃₀ = complete≤ (le 2 tt) {u = (E ʷ) (CD.CNOT • CD.X CD.↑ • CD.CNOT)}
      {v = (E ʷ) (CD.X CD.↑ • CD.X)} (by-eq tt)

    R₅₀ : 2 ⊢ (E ʷ) CD.SWAP ≈ (E ʷ) (CD.CNOT • CD.SWAP • CD.CNOT • CD.SWAP • CD.CNOT)
    R₅₀ = complete≤ (le 2 tt) {u = (E ʷ) CD.SWAP}
      {v = (E ʷ) (CD.CNOT • CD.SWAP • CD.CNOT • CD.SWAP • CD.CNOT)} (by-eq tt)

    R₆₀ : 3 ⊢ (E ʷ) CD.CNOT₂₀ ≈ (E ʷ) (CD.CNOT • CD.CNOT CD.↑ • CD.CNOT • CD.CNOT CD.↑)
    R₆₀ = complete≤ (le 3 tt) {u = (E ʷ) CD.CNOT₂₀}
      {v = (E ʷ) (CD.CNOT • CD.CNOT CD.↑ • CD.CNOT • CD.CNOT CD.↑)} (by-eq tt)

    R₇₀ : 1 ⊢ (E ʷ) (CD.T ^ 8) ≈ ε
    R₇₀ = complete≤ (le 1 tt) {u = (E ʷ) (CD.T ^ 8)} {v = ε} (by-eq tt)

    R₈₀ : 2 ⊢ (E ʷ) (CD.U ^ 4) ≈ (E ʷ) (CD.T ^ 4 • (CD.T CD.↑) ^ 4)
    R₈₀ = complete≤ (le 2 tt) {u = (E ʷ) (CD.U ^ 4)}
      {v = (E ʷ) (CD.T ^ 4 • (CD.T CD.↑) ^ 4)} (by-eq tt)

    R₉₀ : 3 ⊢ (E ʷ) (CD.V ^ 2) ≈
      (E ʷ) (CD.T ^ 6 • (CD.T CD.↑) ^ 6 • (CD.T CD.↑ CD.↑) ^ 6 • (CD.U CD.↑) ^ 2 •
             CD.U₀₂ ^ 2 • CD.U ^ 2)
    R₉₀ = complete≤ (le 3 tt) {u = (E ʷ) (CD.V ^ 2)}
      {v = (E ʷ) (CD.T ^ 6 • (CD.T CD.↑) ^ 6 • (CD.T CD.↑ CD.↑) ^ 6 • (CD.U CD.↑) ^ 2 •
             CD.U₀₂ ^ 2 • CD.U ^ 2)} (by-eq tt)

    R₁₀₀ : 0 ⊢ (E ʷ) (CD.ω ^ 8) ≈ ε
    R₁₀₀ = complete≤ (le 0 tt) {u = (E ʷ) (CD.ω ^ 8)} {v = ε} (by-eq tt)

    R₁₁₀ : 1 ⊢ (E ʷ) (CD.X • CD.T • CD.X) ≈ (E ʷ) (CD.ω • CD.T ^ 7)
    R₁₁₀ = complete≤ (le 1 tt) {u = (E ʷ) (CD.X • CD.T • CD.X)}
      {v = (E ʷ) (CD.ω • CD.T ^ 7)} (by-eq tt)

    R₁₂₀ : 2 ⊢ (E ʷ) (CD.CNOT • CD.T CD.↑ • CD.CNOT) ≈ (E ʷ) (CD.T CD.↑)
    R₁₂₀ = complete≤ (le 2 tt) {u = (E ʷ) (CD.CNOT • CD.T CD.↑ • CD.CNOT)}
      {v = (E ʷ) (CD.T CD.↑)} (by-eq tt)

    R₁₃₀ : 4 ⊢ (E ʷ) (CD.CNOT CD.↑ CD.↑ • CD.V • CD.CNOT CD.↑ CD.↑) ≈
      (E ʷ) (CD.T ^ 5 • (CD.T CD.↑) ^ 5 • (CD.T CD.↑ CD.↑) ^ 5 • (CD.T CD.↑ CD.↑ CD.↑) ^ 5 •
        (CD.U CD.↑ CD.↑) ^ 3 • CD.U₁₃ ^ 3 • CD.U₀₃ ^ 3 • (CD.U CD.↑) ^ 3 • CD.U₀₂ ^ 3 •
        CD.U ^ 3 • CD.V CD.↑ • CD.V₀₂₃ • CD.V₀₁₃ • CD.V)
    R₁₃₀ = complete≤ (le 4 tt)
      {u = (E ʷ) (CD.CNOT CD.↑ CD.↑ • CD.V • CD.CNOT CD.↑ CD.↑)}
      {v = (E ʷ) (CD.T ^ 5 • (CD.T CD.↑) ^ 5 • (CD.T CD.↑ CD.↑) ^ 5 • (CD.T CD.↑ CD.↑ CD.↑) ^ 5 •
        (CD.U CD.↑ CD.↑) ^ 3 • CD.U₁₃ ^ 3 • CD.U₀₃ ^ 3 • (CD.U CD.↑) ^ 3 • CD.U₀₂ ^ 3 •
        CD.U ^ 3 • CD.V CD.↑ • CD.V₀₂₃ • CD.V₀₁₃ • CD.V)} (by-eq tt)

  XX : (₁₊ n) ⊢ X • X ≈ ε
  XX = emb (PB.axiom (P.srel (P.srel P.X²)))

  CXCX : (₂₊ n) ⊢ CX • CX ≈ ε
  CXCX = emb (PB.axiom (P.srel (P.srel P.CX²)))

  unit-comm : ∀ {w : Circuit n} → n ⊢ w • ε ≈ ε • w
  unit-comm = PB.trans PB.right-unit (PB.sym PB.left-unit)

erase-ax : ∀ {w v} → n CD.VRel, w === v → n ⊢ (E ʷ) w ≈ (E ʷ) v
erase-ax (CD.srel (CD.σrel CD.σ-inv))                  = PB.axiom (srel (σrel σ-inv))
erase-ax (CD.srel (CD.σrel (CD.σ-nat₁ CD.X-gate)))     = PB.axiom (srel (σrel (σ-nat₁ X-gate)))
erase-ax (CD.srel (CD.σrel (CD.σ-nat₁ CD.T-gate)))     = PB.sym unit-comm
erase-ax (CD.srel (CD.σrel (CD.σ-nat₂ CD.CNOT-gate)))  = PB.axiom (srel (σrel (σ-nat₂ CX-gate)))
erase-ax (CD.srel (CD.σrel (CD.σ-nat₂ CD.SWAP-gate)))  = PB.axiom (srel (σrel (σ-nat₂ SW-gate)))
erase-ax (CD.srel (CD.srel CD.R₁))                     = XX
erase-ax {₂₊ m} (CD.srel (CD.srel CD.R₂))              = widen m R₂₀
erase-ax {₂₊ m} (CD.srel (CD.srel CD.R₃))              = widen m R₃₀
erase-ax (CD.srel (CD.srel CD.R₄))                     = CXCX
erase-ax {₂₊ m} (CD.srel (CD.srel CD.R₅))              = widen m R₅₀
erase-ax {₃₊ m} (CD.srel (CD.srel CD.R₆))              = widen m R₆₀
erase-ax {₁₊ m} (CD.srel (CD.srel CD.R₇))              = widen m R₇₀
erase-ax {₂₊ m} (CD.srel (CD.srel CD.R₈))              = widen m R₈₀
erase-ax {₃₊ m} (CD.srel (CD.srel CD.R₉))              = widen m R₉₀
erase-ax {m} (CD.srel (CD.srel CD.R₁₀))                = widen m R₁₀₀
erase-ax {₁₊ m} (CD.srel (CD.srel CD.R₁₁))             = widen m R₁₁₀
erase-ax {₂₊ m} (CD.srel (CD.srel CD.R₁₂))             = widen m R₁₂₀
erase-ax {₄₊ m} (CD.srel (CD.srel CD.R₁₃))             = widen m R₁₃₀
erase-ax (CD.cong↑ {w = w} {v = v} x) =
  subst₂ (λ x y → _ ⊢ x ≈ y) (sym (E-↑ w)) (sym (E-↑ v)) (lemma-cong↑ _ _ (erase-ax x))
erase-ax (CD.comm₁ CD.X-gate g)    = comm-gate₁-w↑ X-gate (E g)
erase-ax (CD.comm₁ CD.T-gate g)    = unit-comm
erase-ax (CD.comm₂ CD.CNOT-gate g) = comm-gate₂-w↑↑ CX-gate (E g)
erase-ax (CD.comm₂ CD.SWAP-gate g) = comm-gate₂-w↑↑ SW-gate (E g)
erase-ax (CD.ω↑=ω CD.ω-gate)       = PB.refl

erase : ∀ {w v} → n CD.⊢ w ≈ v → n ⊢ (E ʷ) w ≈ (E ʷ) v
erase PB.refl        = PB.refl
erase (PB.sym p)     = PB.sym (erase p)
erase (PB.trans p q) = PB.trans (erase p) (erase q)
erase (PB.cong p q)  = PB.cong (erase p) (erase q)
erase PB.assoc       = PB.assoc
erase PB.left-unit   = PB.left-unit
erase PB.right-unit  = PB.right-unit
erase (PB.axiom x)   = erase-ax x

------------------------------------------------------------------------
-- The two semantics

-- The matrix of an affine word is that of its classical circuit.
τ-aff : (a : Word (AGen n)) → τ ⌈ a ⌉ ≡ C.physical (wmap ιC a)
τ-aff [ g ]ʷ  = τ-g g
  where
  τ-g : (g : AGen n) → τ [ ιP g ]ʷ ≡ C.physical₀ (ιC g)
  τ-g ax     = refl
  τ-g acx    = refl
  τ-g asw    = refl
  τ-g (g ↥ₐ) = cong H._↑ (τ-g g)
τ-aff ε       = refl
τ-aff (u • v) = cong₂ _•_ (τ-aff u) (τ-aff v)

private
  1≢0 : ∀ {m} {p q : Fin m} → p ≢ q → basis p ≢ basis q
  1≢0 {p = p} {q} p≢q e
    with trans (sym (δ-refl p)) (trans (sym (basis-! p p))
           (trans (cong (_! p) e) (trans (basis-! q p) (δ-≢ p≢q))))
  ... | ()

  basis-inj : ∀ {m} {p q : Fin m} → basis p ≡ basis q → p ≡ q
  basis-inj {p = p} {q} e with p ≟ q
  ... | yes pq  = pq
  ... | no p≢q  = ⊥-elim (1≢0 p≢q e)

-- Affine words with the same matrix have the same classical action.
act-same : (a a′ : Word (AGen n)) → interpret ⌈ a ⌉ ≡ interpret ⌈ a′ ⌉ →
  ∀ s → C.act (wmap ιC a) s C.≈s C.act (wmap ιC a′) s
act-same {n} a a′ e s i =
  trans (C.act-cong (wmap ιC a) (λ j → sym (bits-idx n s j)) i)
  (trans (at (idx n s) i)
    (C.act-cong (wmap ιC a′) (bits-idx n s) i))
  where
  e′ : Sem.interpret (C.physical (wmap ιC a)) ≡ Sem.interpret (C.physical (wmap ιC a′))
  e′ = trans (cong Sem.interpret (sym (τ-aff a))) (trans e (cong Sem.interpret (τ-aff a′)))
  at : ∀ k → C.act (wmap ιC a) (bits n k) C.≈s C.act (wmap ιC a′) (bits n k)
  at k = idx-injective n (basis-inj
    (trans (sym (physical-column (wmap ιC a) k))
      (trans (cong (λ M → col M k) e′) (physical-column (wmap ιC a′) k))))

-- Read in CNOT+Dihedral's semantics: the classical action, no phase.
private
  xor-not : ∀ b → not b ≡ b xor true
  xor-not true  = refl
  xor-not false = refl

  fn-g : (g : AGen n) (x : CDS.Bits n) (i : Fin n) →
    lookup (CDE.fn [ ιD g ]ʷ x) i ≡ C.act₀ (ιC g) (lookup x) i
  fn-g ax (b ∷ x) zero    = trans (cong (λ y → lookup y zero) (CDE.fn-X b x)) (xor-not b)
  fn-g ax (b ∷ x) (suc i) = cong (λ y → lookup y (suc i)) (CDE.fn-X b x)
  fn-g acx (t ∷ c ∷ x) zero =
    trans (cong (λ y → lookup y zero) (CDE.fn-CNOT t c x)) (BoolP.xor-comm c t)
  fn-g acx (t ∷ c ∷ x) (suc i) = cong (λ y → lookup y (suc i)) (CDE.fn-CNOT t c x)
  fn-g asw (a ∷ b ∷ x) zero          = cong (λ y → lookup y zero) (CDE.fn-SWAP a b x)
  fn-g asw (a ∷ b ∷ x) (suc zero)    = cong (λ y → lookup y (suc zero)) (CDE.fn-SWAP a b x)
  fn-g asw (a ∷ b ∷ x) (suc (suc i)) = cong (λ y → lookup y (suc (suc i))) (CDE.fn-SWAP a b x)
  fn-g (g ↥ₐ) (b ∷ x) zero    = cong (λ y → lookup y zero) (CDE.fn-↑ [ ιD g ]ʷ b x)
  fn-g (g ↥ₐ) (b ∷ x) (suc i) =
    trans (cong (λ y → lookup y (suc i)) (CDE.fn-↑ [ ιD g ]ʷ b x)) (fn-g g x i)

  ph-g : (g : AGen n) (x : CDS.Bits n) → CDE.ph [ ιD g ]ʷ x ≡ CDS.0₈
  ph-g ax (b ∷ x)          = CDE.ph-X b x
  ph-g acx (t ∷ c ∷ x)     = CDE.ph-CNOT t c x
  ph-g asw (a ∷ b ∷ x)     = CDE.ph-SWAP a b x
  ph-g (g ↥ₐ) (b ∷ x)      = trans (CDE.ph-↑ [ ιD g ]ʷ b x) (ph-g g x)

fn-aff : (a : Word (AGen n)) (x : CDS.Bits n) (i : Fin n) →
  lookup (CDE.fn (wmap ιD a) x) i ≡ C.act (wmap ιC a) (lookup x) i
fn-aff [ g ]ʷ x i = fn-g g x i
fn-aff ε x i = cong (λ y → lookup y i) (CDE.fn-ε x)
fn-aff (u • v) x i =
  trans (cong (λ y → lookup y i) (CDE.fn-• (wmap ιD u) (wmap ιD v) x))
  (trans (fn-aff u (CDE.fn (wmap ιD v) x) i)
    (C.act-cong (wmap ιC u) (fn-aff v x) i))

ph-aff : (a : Word (AGen n)) (x : CDS.Bits n) → CDE.ph (wmap ιD a) x ≡ CDS.0₈
ph-aff [ g ]ʷ x = ph-g g x
ph-aff ε x = CDE.ph-ε x
ph-aff (u • v) x =
  trans (CDE.ph-• (wmap ιD u) (wmap ιD v) x)
  (trans (cong₂ CDS._+_ (ph-aff v x) (ph-aff u (CDE.fn (wmap ιD v) x)))
    (CDS.+-identityʳ CDS.0₈))

cd-same : (a a′ : Word (AGen n)) → interpret ⌈ a ⌉ ≡ interpret ⌈ a′ ⌉ →
  CDI.⟦ wmap ιD a ⟧ CDS.≐ CDI.⟦ wmap ιD a′ ⟧
cd-same a a′ e x = cong₂ _,_ fn-eq (trans (ph-aff a x) (sym (ph-aff a′ x)))
  where
  fn-eq : CDE.fn (wmap ιD a) x ≡ CDE.fn (wmap ιD a′) x
  fn-eq = trans (sym (tabulate∘lookup _))
    (trans (tabulate-cong (λ i → trans (fn-aff a x i)
              (trans (act-same a a′ e (lookup x) i) (sym (fn-aff a′ x i)))))
      (tabulate∘lookup _))

------------------------------------------------------------------------
-- Completeness

affine-complete : (a a′ : Word (AGen n)) → interpret ⌈ a ⌉ ≡ interpret ⌈ a′ ⌉ →
  n ⊢ ⌈ a ⌉ ≈ ⌈ a′ ⌉
affine-complete a a′ e =
  subst₂ (λ x y → _ ⊢ x ≈ y) (E-ι a) (E-ι a′) (erase (cd-complete (cd-same a a′ e)))
