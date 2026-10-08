------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness: circuits with the same matrix are equal
--
-- Over a nontrivial commutative ring with s s + s s = 1 and i i = −1,
-- two circuits with the same matrix act alike on Pauli operators
-- (act-of-mat: the matrix of a circuit conjugates Pauli matrices as
-- Pauli.act says, it is invertible, and Pauli matrices are determined
-- by their entries).  So their normal forms differ at most in the
-- scalar ω^p (Uniqueness, and Proposition 5.5 of the paper), and not
-- even there, since the eight powers of ω = s (1 + i) are distinct:
-- ω ω = i, so a power ω^d = 1 with 0 < d < 8 would give i^d = 1, which
-- forces d = 4, and ω⁴ = −1 ≠ 1.  Each circuit equals its normal form
-- (Normalise), hence they are equal.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Instances using (Ring ; _+_ ; _*_ ; -_ ; 0# ; 1#)

module Examples.Groups.Qubit-Clifford.Semantics.Completeness
  {A : Set} {{RA : Ring A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (s : A) (s-half : s * s + s * s ≡ 1#)
  (i : A) (i² : i * i ≡ - 1#)
  (nontrivial : 1# ≢ 0#)
  where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Vec.Base using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (refl)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_) renaming (_^_ to _^ʷ_)
open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇ ; ₁₊ ; ₂₊)

open import Examples.Groups.Qubit-Clifford.Syntactics
open import Examples.Groups.Qubit-Clifford.Reasoning using (module Width ; lift ; ω↑)
open import Examples.Groups.Qubit-Clifford.NormalForm using (NF ; nf₀ ; nfₛ ; ⟦_⟧ⁿ ; ⟦_⟧ˣ ; ⟦_⟧ᶻ)
open import Examples.Groups.Qubit-Clifford.Normalise using (normalise ; normalise-ok)
open import Examples.Groups.Qubit-Clifford.Inverse using (inv ; inv-r)
open import Examples.Groups.Qubit-Clifford.Pauli using (Ph ; p0 ; p1 ; p2 ; p3 ; _⊕_ ; act)
open import Examples.Groups.Qubit-Clifford.Uniqueness using (_≗ᵃ_ ; phase ; unphase ; unphase-phase ; act-unique)
open import Examples.Groups.Qubit-Clifford.Semantics.Gauss using (ιᵍ ; iᵍ)
open import Examples.Groups.Qubit-Clifford.Semantics.Interpretation isCR s s-half i i²
  using ( module AR ; Op ; Bits ; Idₒ ; scal ; δb ; _⊙_ ; _≐_ ; ≐-refl ; ≐-sym ; ≐-trans ; ⊙-cong ; ⊙-assoc
        ; ⊙-identityʳ ; scal-1 ; scal-⊙ ; valA ; ⟦_⟧ᴬ ; ω̂ ; _^_ ; ^-+ ; ιᵍ-1 ; ιᵍ-i
        ; module ZS )
open ZS using (solve ; _:=_ ; _:+_ ; _:*_ ; con)
open import Examples.Groups.Qubit-Clifford.Semantics.Soundness isCR s s-half i i² using (sound)
open import Examples.Groups.Qubit-Clifford.Semantics.PauliMatrix isCR s s-half i i²
  using (iph ; iph-⊕ ; iph-p2 ; pmat ; pmat-act)
  renaming (one≢-one to one≢-one′ ; iph-inj to iph-inj′ ; pmat-injective to pmat-injective′)

private
  variable
    n : ℕ

  one≢-one = one≢-one′ nontrivial
  iph-inj = iph-inj′ nontrivial
  pmat-injective = pmat-injective′ nontrivial

------------------------------------------------------------------------
-- Circuits with the same matrix act alike on Pauli operators

⟦inv⟧ : (w : Circuit n) → (⟦ w ⟧ᴬ ⊙ ⟦ inv w ⟧ᴬ) ≐ Idₒ
⟦inv⟧ w = sound (inv-r w)

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
-- The powers of ω are distinct

private
  -- ω ω = i.
  ω̂² : ω̂ * ω̂ ≡ i
  ω̂² = begin
    (s * (1# + i)) * (s * (1# + i))       ≡⟨ solve 2 (λ s i → (s :* (con (+ 1) :+ i)) :* (s :* (con (+ 1) :+ i))
                                                := (s :* s :+ s :* s) :* i :+ (s :* s) :* (i :* i :+ con (+ 1)))
                                               refl s i ⟩
    (s * s + s * s) * i + (s * s) * (i * i + 1#)
                                          ≡⟨ Eq.cong₂ (λ a b → a * i + (s * s) * b) s-half i²+1 ⟩
    1# * i + (s * s) * 0#                 ≡⟨ solve 2 (λ s i → con (+ 1) :* i :+ (s :* s) :* con (+ 0) := i) refl s i ⟩
    i                                     ∎
    where
    open Eq.≡-Reasoning
    open import Data.Integer.Base using (+_)
    i²+1 : i * i + 1# ≡ 0#
    i²+1 = Eq.trans (Eq.cong (_+ 1#) i²) (AR.-‿inverseˡ 1#)

  pow-mul : (a b : A) (k : ℕ) → (a * b) ^ k ≡ (a ^ k) * (b ^ k)
  pow-mul a b zero    = Eq.sym (AR.*-identityˡ 1#)
  pow-mul a b (suc k) = Eq.trans (Eq.cong ((a * b) *_) (pow-mul a b k)) (cross a b (a ^ k) (b ^ k))
    where
    cross : (a b c d : A) → (a * b) * (c * d) ≡ (a * c) * (b * d)
    cross a b c d = solve 4 (λ a b c d → (a :* b) :* (c :* d) := (a :* c) :* (b :* d)) refl a b c d

  -- i^k as a phase.
  phOf : ℕ → Ph
  phOf zero    = p0
  phOf (suc k) = phOf k ⊕ p1

  i^ : (k : ℕ) → i ^ k ≡ iph (phOf k)
  i^ zero    = Eq.sym ιᵍ-1
  i^ (suc k) = begin
    i * i ^ k                     ≡⟨ Eq.cong (i *_) (i^ k) ⟩
    i * iph (phOf k)              ≡⟨ AR.*-comm i (iph (phOf k)) ⟩
    iph (phOf k) * i              ≡⟨ Eq.cong (iph (phOf k) *_) (Eq.sym ιᵍ-i) ⟩
    iph (phOf k) * iph p1         ≡⟨ Eq.sym (iph-⊕ (phOf k) p1) ⟩
    iph (phOf k ⊕ p1)             ∎
    where open Eq.≡-Reasoning

  ω̂-even : (k : ℕ) → ω̂ ^ (k +ℕ k) ≡ iph (phOf k)
  ω̂-even k = Eq.trans (^-+ ω̂ k k) (Eq.trans (Eq.sym (pow-mul ω̂ ω̂ k))
               (Eq.trans (Eq.cong (_^ k) ω̂²) (i^ k)))

  -- A power ω^d = 1 gives i^d = 1.
  sq-root : (d : ℕ) → ω̂ ^ d ≡ 1# → phOf d ≡ p0
  sq-root d e = iph-inj (phOf d) p0 (begin
    iph (phOf d)        ≡⟨ Eq.sym (ω̂-even d) ⟩
    ω̂ ^ (d +ℕ d)        ≡⟨ ^-+ ω̂ d d ⟩
    ω̂ ^ d * ω̂ ^ d       ≡⟨ Eq.cong₂ _*_ e e ⟩
    1# * 1#             ≡⟨ AR.*-identityˡ 1# ⟩
    1#                  ≡⟨ Eq.sym ιᵍ-1 ⟩
    iph p0              ∎)
    where open Eq.≡-Reasoning

  p1≢p0 : p1 ≢ p0
  p1≢p0 ()
  p2≢p0 : p2 ≢ p0
  p2≢p0 ()
  p3≢p0 : p3 ≢ p0
  p3≢p0 ()

  no-root1 : ω̂ ^ 1 ≢ 1#
  no-root1 e = p1≢p0 (sq-root 1 e)
  no-root2 : ω̂ ^ 2 ≢ 1#
  no-root2 e = p2≢p0 (sq-root 2 e)
  no-root3 : ω̂ ^ 3 ≢ 1#
  no-root3 e = p3≢p0 (sq-root 3 e)
  no-root4 : ω̂ ^ 4 ≢ 1#
  no-root4 e = one≢-one (Eq.sym (Eq.trans (Eq.sym iph-p2) (Eq.trans (Eq.sym (ω̂-even 2)) e)))
  no-root5 : ω̂ ^ 5 ≢ 1#
  no-root5 e = p1≢p0 (sq-root 5 e)
  no-root6 : ω̂ ^ 6 ≢ 1#
  no-root6 e = p2≢p0 (sq-root 6 e)
  no-root7 : ω̂ ^ 7 ≢ 1#
  no-root7 e = p3≢p0 (sq-root 7 e)

  -- ω is invertible, as ω⁸ = 1.
  ω̂⁸ : ω̂ ^ 7 * ω̂ ≡ 1#
  ω̂⁸ = Eq.trans (AR.*-comm (ω̂ ^ 7) ω̂) (Eq.trans (ω̂-even 4) ιᵍ-1)

  cancel1 : (x y : A) → ω̂ * x ≡ ω̂ * y → x ≡ y
  cancel1 x y e = begin
    x                      ≡⟨ Eq.sym (AR.*-identityˡ x) ⟩
    1# * x                 ≡⟨ Eq.cong (_* x) (Eq.sym ω̂⁸) ⟩
    (ω̂ ^ 7 * ω̂) * x        ≡⟨ AR.*-assoc (ω̂ ^ 7) ω̂ x ⟩
    ω̂ ^ 7 * (ω̂ * x)        ≡⟨ Eq.cong (ω̂ ^ 7 *_) e ⟩
    ω̂ ^ 7 * (ω̂ * y)        ≡⟨ Eq.sym (AR.*-assoc (ω̂ ^ 7) ω̂ y) ⟩
    (ω̂ ^ 7 * ω̂) * y        ≡⟨ Eq.cong (_* y) ω̂⁸ ⟩
    1# * y                 ≡⟨ AR.*-identityˡ y ⟩
    y                      ∎
    where open Eq.≡-Reasoning

  cancel : (a d : ℕ) → ω̂ ^ a ≡ ω̂ ^ (a +ℕ d) → ω̂ ^ d ≡ 1#
  cancel zero    d e = Eq.sym e
  cancel (suc a) d e = cancel a d (cancel1 _ _ e)

ωpow-inj : (p q : Fin 8) → ω̂ ^ toℕ p ≡ ω̂ ^ toℕ q → p ≡ q
ωpow-inj ₀ ₀ e = refl
ωpow-inj ₀ ₁ e = ⊥-elim (no-root1 (cancel 0 1 e))
ωpow-inj ₀ ₂ e = ⊥-elim (no-root2 (cancel 0 2 e))
ωpow-inj ₀ ₃ e = ⊥-elim (no-root3 (cancel 0 3 e))
ωpow-inj ₀ ₄ e = ⊥-elim (no-root4 (cancel 0 4 e))
ωpow-inj ₀ ₅ e = ⊥-elim (no-root5 (cancel 0 5 e))
ωpow-inj ₀ ₆ e = ⊥-elim (no-root6 (cancel 0 6 e))
ωpow-inj ₀ ₇ e = ⊥-elim (no-root7 (cancel 0 7 e))
ωpow-inj ₁ ₀ e = ⊥-elim (no-root1 (cancel 0 1 (Eq.sym e)))
ωpow-inj ₁ ₁ e = refl
ωpow-inj ₁ ₂ e = ⊥-elim (no-root1 (cancel 1 1 e))
ωpow-inj ₁ ₃ e = ⊥-elim (no-root2 (cancel 1 2 e))
ωpow-inj ₁ ₄ e = ⊥-elim (no-root3 (cancel 1 3 e))
ωpow-inj ₁ ₅ e = ⊥-elim (no-root4 (cancel 1 4 e))
ωpow-inj ₁ ₆ e = ⊥-elim (no-root5 (cancel 1 5 e))
ωpow-inj ₁ ₇ e = ⊥-elim (no-root6 (cancel 1 6 e))
ωpow-inj ₂ ₀ e = ⊥-elim (no-root2 (cancel 0 2 (Eq.sym e)))
ωpow-inj ₂ ₁ e = ⊥-elim (no-root1 (cancel 1 1 (Eq.sym e)))
ωpow-inj ₂ ₂ e = refl
ωpow-inj ₂ ₃ e = ⊥-elim (no-root1 (cancel 2 1 e))
ωpow-inj ₂ ₄ e = ⊥-elim (no-root2 (cancel 2 2 e))
ωpow-inj ₂ ₅ e = ⊥-elim (no-root3 (cancel 2 3 e))
ωpow-inj ₂ ₆ e = ⊥-elim (no-root4 (cancel 2 4 e))
ωpow-inj ₂ ₇ e = ⊥-elim (no-root5 (cancel 2 5 e))
ωpow-inj ₃ ₀ e = ⊥-elim (no-root3 (cancel 0 3 (Eq.sym e)))
ωpow-inj ₃ ₁ e = ⊥-elim (no-root2 (cancel 1 2 (Eq.sym e)))
ωpow-inj ₃ ₂ e = ⊥-elim (no-root1 (cancel 2 1 (Eq.sym e)))
ωpow-inj ₃ ₃ e = refl
ωpow-inj ₃ ₄ e = ⊥-elim (no-root1 (cancel 3 1 e))
ωpow-inj ₃ ₅ e = ⊥-elim (no-root2 (cancel 3 2 e))
ωpow-inj ₃ ₆ e = ⊥-elim (no-root3 (cancel 3 3 e))
ωpow-inj ₃ ₇ e = ⊥-elim (no-root4 (cancel 3 4 e))
ωpow-inj ₄ ₀ e = ⊥-elim (no-root4 (cancel 0 4 (Eq.sym e)))
ωpow-inj ₄ ₁ e = ⊥-elim (no-root3 (cancel 1 3 (Eq.sym e)))
ωpow-inj ₄ ₂ e = ⊥-elim (no-root2 (cancel 2 2 (Eq.sym e)))
ωpow-inj ₄ ₃ e = ⊥-elim (no-root1 (cancel 3 1 (Eq.sym e)))
ωpow-inj ₄ ₄ e = refl
ωpow-inj ₄ ₅ e = ⊥-elim (no-root1 (cancel 4 1 e))
ωpow-inj ₄ ₆ e = ⊥-elim (no-root2 (cancel 4 2 e))
ωpow-inj ₄ ₇ e = ⊥-elim (no-root3 (cancel 4 3 e))
ωpow-inj ₅ ₀ e = ⊥-elim (no-root5 (cancel 0 5 (Eq.sym e)))
ωpow-inj ₅ ₁ e = ⊥-elim (no-root4 (cancel 1 4 (Eq.sym e)))
ωpow-inj ₅ ₂ e = ⊥-elim (no-root3 (cancel 2 3 (Eq.sym e)))
ωpow-inj ₅ ₃ e = ⊥-elim (no-root2 (cancel 3 2 (Eq.sym e)))
ωpow-inj ₅ ₄ e = ⊥-elim (no-root1 (cancel 4 1 (Eq.sym e)))
ωpow-inj ₅ ₅ e = refl
ωpow-inj ₅ ₆ e = ⊥-elim (no-root1 (cancel 5 1 e))
ωpow-inj ₅ ₇ e = ⊥-elim (no-root2 (cancel 5 2 e))
ωpow-inj ₆ ₀ e = ⊥-elim (no-root6 (cancel 0 6 (Eq.sym e)))
ωpow-inj ₆ ₁ e = ⊥-elim (no-root5 (cancel 1 5 (Eq.sym e)))
ωpow-inj ₆ ₂ e = ⊥-elim (no-root4 (cancel 2 4 (Eq.sym e)))
ωpow-inj ₆ ₃ e = ⊥-elim (no-root3 (cancel 3 3 (Eq.sym e)))
ωpow-inj ₆ ₄ e = ⊥-elim (no-root2 (cancel 4 2 (Eq.sym e)))
ωpow-inj ₆ ₅ e = ⊥-elim (no-root1 (cancel 5 1 (Eq.sym e)))
ωpow-inj ₆ ₆ e = refl
ωpow-inj ₆ ₇ e = ⊥-elim (no-root1 (cancel 6 1 e))
ωpow-inj ₇ ₀ e = ⊥-elim (no-root7 (cancel 0 7 (Eq.sym e)))
ωpow-inj ₇ ₁ e = ⊥-elim (no-root6 (cancel 1 6 (Eq.sym e)))
ωpow-inj ₇ ₂ e = ⊥-elim (no-root5 (cancel 2 5 (Eq.sym e)))
ωpow-inj ₇ ₃ e = ⊥-elim (no-root4 (cancel 3 4 (Eq.sym e)))
ωpow-inj ₇ ₄ e = ⊥-elim (no-root3 (cancel 4 3 (Eq.sym e)))
ωpow-inj ₇ ₅ e = ⊥-elim (no-root2 (cancel 5 2 (Eq.sym e)))
ωpow-inj ₇ ₆ e = ⊥-elim (no-root1 (cancel 6 1 (Eq.sym e)))
ωpow-inj ₇ ₇ e = refl

------------------------------------------------------------------------
-- The scalar

private
  ω^↑ : (k : ℕ) → (₁₊ n) ⊢ (ω ^ʷ k) ↑ ≈ ω ^ʷ k
  ω^↑ zero          = Width.refl
  ω^↑ (suc zero)    = ω↑
  ω^↑ (suc (suc k)) = Width.cong ω↑ (ω^↑ (suc k))

-- A normal form is its scalar times the rest.
nf-phase : (nf : NF n) → n ⊢ ⟦ nf ⟧ⁿ ≈ ω ^ʷ toℕ (phase nf) • ⟦ unphase nf ⟧ⁿ
nf-phase {n} (nf₀ p)     = Width.sym Width.right-unit
nf-phase {n} (nfₛ L M N) = begin
  ⟦ N ⟧ⁿ ↑ • M' • L'                                        ≈⟨ front (M' • L') (lift (nf-phase N)) ⟩
  (Ω ↑ • ⟦ unphase N ⟧ⁿ ↑) • M' • L'                        ≈⟨ front (M' • L') (front (⟦ unphase N ⟧ⁿ ↑) (ω^↑ (toℕ (phase N)))) ⟩
  (Ω • ⟦ unphase N ⟧ⁿ ↑) • M' • L'                          ≈⟨ assoc ⟩
  Ω • ⟦ unphase N ⟧ⁿ ↑ • M' • L'                            ∎
  where
  open Width n
  M' = ⟦ M ⟧ˣ
  L' = ⟦ L ⟧ᶻ
  Ω : {k : ℕ} → Circuit k
  Ω = ω ^ʷ toℕ (phase N)

-- The matrix of ω^k.
⟦ω^⟧ : (k : ℕ) → ⟦ ω {n} ^ʷ k ⟧ᴬ ≐ scal (ω̂ ^ k)
⟦ω^⟧ zero          = ≐-sym scal-1
⟦ω^⟧ (suc zero)    x y = Eq.cong (_* δb x y) (Eq.sym (AR.*-identityʳ ω̂))
⟦ω^⟧ (suc (suc k)) = ≐-trans (⊙-cong (≐-refl (scal ω̂)) (⟦ω^⟧ (suc k))) (scal-⊙ ω̂ (ω̂ ^ suc k))

private
  δb-refl : (x : Bits n) → δb x x ≡ 1#
  δb-refl []          = refl
  δb-refl (true  ∷ x) = δb-refl x
  δb-refl (false ∷ x) = δb-refl x

-- The scalar is seen by the matrix: ω^p U ≠ ω^q U for U invertible.
phase-cancel : (p q : Fin 8) (u : Circuit n) → ⟦ ω ^ʷ toℕ p • u ⟧ᴬ ≐ ⟦ ω ^ʷ toℕ q • u ⟧ᴬ → p ≡ q
phase-cancel {n} p q u e = ωpow-inj p q (begin
  ω̂ ^ toℕ p                               ≡⟨ diag (toℕ p) ⟨
  ⟦ ω ^ʷ toℕ p ⟧ᴬ x x                       ≡⟨ strip (toℕ p) x x ⟩
  (⟦ ω ^ʷ toℕ p • u ⟧ᴬ ⊙ ⟦ inv u ⟧ᴬ) x x    ≡⟨ ⊙-cong e (≐-refl ⟦ inv u ⟧ᴬ) x x ⟩
  (⟦ ω ^ʷ toℕ q • u ⟧ᴬ ⊙ ⟦ inv u ⟧ᴬ) x x    ≡⟨ strip (toℕ q) x x ⟨
  ⟦ ω ^ʷ toℕ q ⟧ᴬ x x                       ≡⟨ diag (toℕ q) ⟩
  ω̂ ^ toℕ q                               ∎)
  where
  open Eq.≡-Reasoning
  x : Bits n
  x = replicate n false
  diag : (k : ℕ) → ⟦ ω ^ʷ k ⟧ᴬ x x ≡ ω̂ ^ k
  diag k = Eq.trans (⟦ω^⟧ k x x) (Eq.trans (Eq.cong ((ω̂ ^ k) *_) (δb-refl x)) (AR.*-identityʳ _))
  strip : (k : ℕ) → ⟦ ω ^ʷ k ⟧ᴬ ≐ (⟦ ω ^ʷ k • u ⟧ᴬ ⊙ ⟦ inv u ⟧ᴬ)
  strip k = ≐-trans (≐-sym (⊙-identityʳ ⟦ ω ^ʷ k ⟧ᴬ))
    (≐-trans (⊙-cong (≐-refl ⟦ ω ^ʷ k ⟧ᴬ) (≐-sym (⟦inv⟧ u)))
             (≐-sym (⊙-assoc ⟦ ω ^ʷ k ⟧ᴬ ⟦ u ⟧ᴬ ⟦ inv u ⟧ᴬ)))

phase-of-mat : (nf nf' : NF n) → unphase nf ≡ unphase nf' →
               ⟦ ⟦ nf ⟧ⁿ ⟧ᴬ ≐ ⟦ ⟦ nf' ⟧ⁿ ⟧ᴬ → phase nf ≡ phase nf'
phase-of-mat nf nf' eu e = phase-cancel (phase nf) (phase nf') ⟦ unphase nf ⟧ⁿ
  (≐-trans (≐-sym (sound (nf-phase nf)))
  (≐-trans e
  (≐-trans (sound (nf-phase nf'))
           (λ x y → Eq.cong (λ u → ⟦ ω ^ʷ toℕ (phase nf') • ⟦ u ⟧ⁿ ⟧ᴬ x y) (Eq.sym eu)))))

------------------------------------------------------------------------
-- Completeness

-- Normal forms with the same matrix are equal.
nf-injective : (nf nf' : NF n) → ⟦ ⟦ nf ⟧ⁿ ⟧ᴬ ≐ ⟦ ⟦ nf' ⟧ⁿ ⟧ᴬ → nf ≡ nf'
nf-injective nf nf' e = unphase-phase nf nf' eu (phase-of-mat nf nf' eu e)
  where
  eu = act-unique nf nf' (act-of-mat {w = ⟦ nf ⟧ⁿ} {v = ⟦ nf' ⟧ⁿ} e)

completeness : {w v : Circuit n} → ⟦ w ⟧ᴬ ≐ ⟦ v ⟧ᴬ → n ⊢ w ≈ v
completeness {n} {w} {v} e = begin
  w                    ≈⟨ normalise-ok n w ⟩
  ⟦ normalise n w ⟧ⁿ   ≡⟨ Eq.cong ⟦_⟧ⁿ nf≡ ⟩
  ⟦ normalise n v ⟧ⁿ   ≈⟨ normalise-ok n v ⟨
  v                    ∎
  where
  open Width n
  nf≡ = nf-injective (normalise n w) (normalise n v)
    (≐-trans (≐-sym (sound (normalise-ok n w))) (≐-trans e (sound (normalise-ok n v))))
