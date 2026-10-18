------------------------------------------------------------------------
-- Presentations of groups
--
-- Affine circuits: words in X, CX and the swap (`AGen`), read in this
-- calculus (`⌈_⌉`), in CNOT+Dihedral's (`ιD`) and as classical
-- circuits (`ιC`).  Erasing T and ω (`E`) sends CNOT+Dihedral's words
-- to circuits here.  An affine word read in CNOT+Dihedral's semantics
-- picks up no phase, and its permutation is the classical action of
-- GeneralN/Classical, which the matrix determines column by column
-- (`cd-same`).  An affine word followed by its reverse is ε (`inv-r`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.AffineWords where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using (Vec ; _∷_ ; lookup ; tabulate)
open import Data.Vec.Properties using (tabulate∘lookup ; tabulate-cong)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; _≢_)
open import Relation.Nullary.Decidable using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ ; interpret)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (col ; δ-refl ; δ-≢ ; _!_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
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

private
  variable
    n : ℕ

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

XX : (₁₊ n) ⊢ X • X ≈ ε
XX = emb (PB.axiom (P.srel (P.srel P.X²)))

CXCX : (₂₊ n) ⊢ CX • CX ≈ ε
CXCX = emb (PB.axiom (P.srel (P.srel P.CX²)))

unit-comm : ∀ {w : Circuit n} → n ⊢ w • ε ≈ ε • w
unit-comm = PB.trans PB.right-unit (PB.sym PB.left-unit)


------------------------------------------------------------------------
-- Inverses

-- The reverse of an affine word; every letter is an involution.
inv : Word (AGen n) → Word (AGen n)
inv [ g ]ʷ  = [ g ]ʷ
inv ε       = ε
inv (u • v) = inv v • inv u

private
  letter-invol : (g : AGen n) → n ⊢ [ ιP g ]ʷ • [ ιP g ]ʷ ≈ ε
  letter-invol ax     = XX
  letter-invol acx    = CXCX
  letter-invol asw    = PB.axiom (srel (σrel σ-inv))
  letter-invol (g ↥ₐ) = lemma-cong↑ ([ ιP g ]ʷ • [ ιP g ]ʷ) ε (letter-invol g)

inv-r : (w : Word (AGen n)) → n ⊢ ⌈ w ⌉ • ⌈ inv w ⌉ ≈ ε
inv-r [ g ]ʷ  = letter-invol g
inv-r ε       = PB.left-unit
inv-r (u • v) =
  PB.trans PB.assoc
  (PB.trans (PB.cong PB.refl (PB.trans (PB.sym PB.assoc)
              (PB.trans (PB.cong (inv-r v) PB.refl) PB.left-unit)))
    (inv-r u))

inv-l : (w : Word (AGen n)) → n ⊢ ⌈ inv w ⌉ • ⌈ w ⌉ ≈ ε
inv-l [ g ]ʷ  = letter-invol g
inv-l ε       = PB.left-unit
inv-l (u • v) =
  PB.trans PB.assoc
  (PB.trans (PB.cong PB.refl (PB.trans (PB.sym PB.assoc)
              (PB.trans (PB.cong (inv-l u) PB.refl) PB.left-unit)))
    (inv-l v))

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

-- The implicit arguments of tabulate-cong are given: inferred, they made
-- Agda run out of memory.
fn-same : (a a′ : Word (AGen n)) → interpret ⌈ a ⌉ ≡ interpret ⌈ a′ ⌉ →
  (x : CDS.Bits n) → CDE.fn (wmap ιD a) x ≡ CDE.fn (wmap ιD a′) x
fn-same a a′ e x =
  trans (sym (tabulate∘lookup (CDE.fn (wmap ιD a) x)))
  (trans (tabulate-cong {f = lookup (CDE.fn (wmap ιD a) x)} {g = lookup (CDE.fn (wmap ιD a′) x)}
            (λ i → trans (fn-aff a x i)
              (trans (act-same a a′ e (lookup x) i) (sym (fn-aff a′ x i)))))
    (tabulate∘lookup (CDE.fn (wmap ιD a′) x)))

cd-same : (a a′ : Word (AGen n)) → interpret ⌈ a ⌉ ≡ interpret ⌈ a′ ⌉ →
  CDI.⟦ wmap ιD a ⟧ CDS.≐ CDI.⟦ wmap ιD a′ ⟧
cd-same a a′ e x =
  cong₂ _,_ (fn-same a a′ e x) (trans (ph-aff a x) (sym (ph-aff a′ x)))
