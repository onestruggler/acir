------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness: circuits with the same matrix are equal
--
-- Over a nontrivial commutative ring with s s + s s = 1, two circuits
-- with the same matrix act alike on Pauli operators (act-of-mat: the
-- matrix of a circuit conjugates Pauli matrices as Pauli.act says, it
-- is invertible, and Pauli matrices are determined by their entries).
-- So their normal forms differ at most in the sign (Uniqueness), and
-- not even there, since −U ≠ U for an invertible U.  Each circuit
-- equals its normal form (Normalise), hence they are equal.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Instances using (Ring ; _+_ ; _*_ ; -_ ; 0# ; 1#)

module Examples.Groups.Real-Clifford.Semantics.Completeness
  {A : Set} {{RA : Ring A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (s : A) (s-half : s * s + s * s ≡ 1#)
  (nontrivial : 1# ≢ 0#)
  where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (refl)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊)

open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Engine using (invol)
open import Examples.Groups.Real-Clifford.Reasoning using (module Width ; lift ; neg↑)
open import Examples.Groups.Real-Clifford.NormalForm using (NF ; nf₀ ; nfₛ ; ⟦_⟧ⁿ ; ⟦_⟧ˣ ; ⟦_⟧ᶻ ; sgn)
open import Examples.Groups.Real-Clifford.Normalise using (normalise ; normalise-ok)
open import Examples.Groups.Real-Clifford.Pauli using (act ; inv)
open import Examples.Groups.Real-Clifford.Uniqueness using (_≗ᵃ_ ; sign ; unsign ; unsign-sign ; act-unique)
open import Examples.Groups.Real-Clifford.Semantics.Laws isCR
open import Examples.Groups.Real-Clifford.Semantics.Interpretation isCR s s-half using (valA ; ⟦_⟧ᴬ)
open import Examples.Groups.Real-Clifford.Semantics.Soundness isCR s s-half using (sound)
open import Examples.Groups.Real-Clifford.Semantics.PauliMatrix isCR s s-half
  using (sg ; pmat ; pmat-act)
  renaming (sg-inj to sg-inj′ ; pmat-injective to pmat-injective′)

private
  variable
    n : ℕ

  sg-inj = sg-inj′ nontrivial
  pmat-injective = pmat-injective′ nontrivial

------------------------------------------------------------------------
-- Inverses

-- A circuit followed by its letters in reverse is the identity, every
-- letter being an involution.
inv-r : (w : Circuit n) → n ⊢ w • inv w ≈ ε
inv-r {n} [ g ]ʷ  = invol g
inv-r {n} ε       = Width.left-unit
inv-r {n} (w • v) = begin
  (w • v) • (inv v • inv w)   ≈⟨ assoc ⟩
  w • v • inv v • inv w       ≈⟨ back w (sym assoc) ⟩
  w • (v • inv v) • inv w     ≈⟨ back w (front (inv w) (inv-r v)) ⟩
  w • ε • inv w               ≈⟨ back w left-unit ⟩
  w • inv w                   ≈⟨ inv-r w ⟩
  ε                           ∎
  where open Width n

⟦inv⟧ : (w : Circuit n) → (⟦ w ⟧ᴬ ⊙ ⟦ inv w ⟧ᴬ) ≐ Idₒ
⟦inv⟧ w = sound (inv-r w)

------------------------------------------------------------------------
-- Circuits with the same matrix act alike on Pauli operators

act-of-mat : {w v : Circuit n} → ⟦ w ⟧ᴬ ≐ ⟦ v ⟧ᴬ → w ≗ᵃ v
act-of-mat {w = w} {v} e P = pmat-injective (act w P) (act v P) λ x y → begin
  pmat (act w P) x y                         ≡⟨ ⊙-identityʳ (pmat (act w P)) x y ⟨
  (pmat (act w P) ⊙ Idₒ) x y                 ≡⟨ ⊙-cong (≐-refl (pmat (act w P))) (⟦inv⟧ w) x y ⟨
  (pmat (act w P) ⊙ (W ⊙ W⁻)) x y            ≡⟨ ⊙-assoc (pmat (act w P)) W W⁻ x y ⟨
  ((pmat (act w P) ⊙ W) ⊙ W⁻) x y            ≡⟨ ⊙-cong (pmat-act w P) (≐-refl W⁻) x y ⟨
  ((W ⊙ pmat P) ⊙ W⁻) x y                    ≡⟨ ⊙-cong (⊙-cong e (≐-refl (pmat P))) (≐-refl W⁻) x y ⟩
  ((⟦ v ⟧ᴬ ⊙ pmat P) ⊙ W⁻) x y               ≡⟨ ⊙-cong (pmat-act v P) (≐-refl W⁻) x y ⟩
  ((pmat (act v P) ⊙ ⟦ v ⟧ᴬ) ⊙ W⁻) x y       ≡⟨ ⊙-cong (⊙-cong (≐-refl (pmat (act v P))) e) (≐-refl W⁻) x y ⟨
  ((pmat (act v P) ⊙ W) ⊙ W⁻) x y            ≡⟨ ⊙-assoc (pmat (act v P)) W W⁻ x y ⟩
  (pmat (act v P) ⊙ (W ⊙ W⁻)) x y            ≡⟨ ⊙-cong (≐-refl (pmat (act v P))) (⟦inv⟧ w) x y ⟩
  (pmat (act v P) ⊙ Idₒ) x y                 ≡⟨ ⊙-identityʳ (pmat (act v P)) x y ⟩
  pmat (act v P) x y                         ∎
  where
  open Eq.≡-Reasoning
  W  = ⟦ w ⟧ᴬ
  W⁻ = ⟦ inv w ⟧ᴬ

------------------------------------------------------------------------
-- The sign

-- A normal form is its sign times its unsigned form.
sgn↑ : (σ : Bool) → (₁₊ n) ⊢ sgn σ ↑ ≈ sgn σ
sgn↑ {n} false = Width.refl
sgn↑     true  = neg↑

nf-sign : (nf : NF n) → n ⊢ ⟦ nf ⟧ⁿ ≈ sgn (sign nf) • ⟦ unsign nf ⟧ⁿ
nf-sign {n} (nf₀ false) = Width.sym (Width.left-unit)
nf-sign {n} (nf₀ true)  = Width.sym (Width.right-unit)
nf-sign {n} (nfₛ L M N) = begin
  ⟦ N ⟧ⁿ ↑ • M' • L'                                  ≈⟨ front (M' • L') (lift (nf-sign N)) ⟩
  (sgn (sign N) ↑ • ⟦ unsign N ⟧ⁿ ↑) • M' • L'        ≈⟨ front (M' • L') (front (⟦ unsign N ⟧ⁿ ↑) (sgn↑ (sign N))) ⟩
  (sgn (sign N) • ⟦ unsign N ⟧ⁿ ↑) • M' • L'          ≈⟨ assoc ⟩
  sgn (sign N) • ⟦ unsign N ⟧ⁿ ↑ • M' • L'            ∎
  where
  open Width n
  M' = ⟦ M ⟧ˣ
  L' = ⟦ L ⟧ᶻ

private
  δb-refl : (x : Bits n) → δb x x ≡ 1#
  δb-refl []          = refl
  δb-refl (true  ∷ x) = δb-refl x
  δb-refl (false ∷ x) = δb-refl x

  sgn-diag : (σ : Bool) (x : Bits n) → ⟦ sgn σ ⟧ᴬ x x ≡ sg σ
  sgn-diag false x = δb-refl x
  sgn-diag true  x = Eq.trans (Eq.cong (- 1# *_) (δb-refl x)) (AR.*-identityʳ (- 1#))

-- The sign is seen by the matrix: −U ≠ U for U invertible.
sgn-cancel : (σ τ : Bool) (u : Circuit n) → ⟦ sgn σ • u ⟧ᴬ ≐ ⟦ sgn τ • u ⟧ᴬ → σ ≡ τ
sgn-cancel {n} σ τ u e = sg-inj σ τ (begin
  sg σ                                  ≡⟨ sgn-diag σ x ⟨
  ⟦ sgn σ ⟧ᴬ x x                        ≡⟨ strip σ x x ⟩
  (⟦ sgn σ • u ⟧ᴬ ⊙ ⟦ inv u ⟧ᴬ) x x     ≡⟨ ⊙-cong e (≐-refl ⟦ inv u ⟧ᴬ) x x ⟩
  (⟦ sgn τ • u ⟧ᴬ ⊙ ⟦ inv u ⟧ᴬ) x x     ≡⟨ strip τ x x ⟨
  ⟦ sgn τ ⟧ᴬ x x                        ≡⟨ sgn-diag τ x ⟩
  sg τ                                  ∎)
  where
  open Eq.≡-Reasoning
  x : Bits n
  x = replicate n false
  strip : (σ : Bool) → ⟦ sgn σ ⟧ᴬ ≐ (⟦ sgn σ • u ⟧ᴬ ⊙ ⟦ inv u ⟧ᴬ)
  strip σ = ≐-trans (≐-sym (⊙-identityʳ ⟦ sgn σ ⟧ᴬ))
    (≐-trans (⊙-cong (≐-refl ⟦ sgn σ ⟧ᴬ) (≐-sym (⟦inv⟧ u)))
             (≐-sym (⊙-assoc ⟦ sgn σ ⟧ᴬ ⟦ u ⟧ᴬ ⟦ inv u ⟧ᴬ)))

sign-of-mat : (nf nf' : NF n) → unsign nf ≡ unsign nf' →
              ⟦ ⟦ nf ⟧ⁿ ⟧ᴬ ≐ ⟦ ⟦ nf' ⟧ⁿ ⟧ᴬ → sign nf ≡ sign nf'
sign-of-mat nf nf' eu e = sgn-cancel (sign nf) (sign nf') ⟦ unsign nf ⟧ⁿ
  (≐-trans (≐-sym (sound (nf-sign nf)))
  (≐-trans e
  (≐-trans (sound (nf-sign nf'))
           (λ x y → Eq.cong (λ u → ⟦ sgn (sign nf') • ⟦ u ⟧ⁿ ⟧ᴬ x y) (Eq.sym eu)))))

------------------------------------------------------------------------
-- Completeness

completeness : {w v : Circuit n} → ⟦ w ⟧ᴬ ≐ ⟦ v ⟧ᴬ → n ⊢ w ≈ v
completeness {n} {w} {v} e = begin
  w                    ≈⟨ normalise-ok n w ⟩
  ⟦ normalise n w ⟧ⁿ   ≡⟨ Eq.cong ⟦_⟧ⁿ nf≡ ⟩
  ⟦ normalise n v ⟧ⁿ   ≈⟨ normalise-ok n v ⟨
  v                    ∎
  where
  open Width n
  nw = normalise n w
  nv = normalise n v
  e' : ⟦ ⟦ nw ⟧ⁿ ⟧ᴬ ≐ ⟦ ⟦ nv ⟧ⁿ ⟧ᴬ
  e' = ≐-trans (≐-sym (sound (normalise-ok n w))) (≐-trans e (sound (normalise-ok n v)))
  eu = act-unique nw nv (act-of-mat {w = ⟦ nw ⟧ⁿ} {v = ⟦ nv ⟧ⁿ} e')
  nf≡ = unsign-sign nw nv eu (sign-of-mat nw nv eu e')
