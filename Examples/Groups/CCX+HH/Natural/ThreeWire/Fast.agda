------------------------------------------------------------------------
-- Presentations of groups
--
-- Deciding equations between three-wire circuits fast.
--
-- A circuit acts on a column of integers with a power of two as scale:
-- (k , v) stands for 2⁻ᵏ v over 𝔻.  A classical gate permutes the
-- entries, HH replaces four entries a, b, c, d by a ± b ± c ± d and
-- adds one to the scale (`act`).  That is the vector action of the
-- circuit (`quantum`) read through 2⁻ᵏ ι (`bridge`): the classical
-- gates by computation, HH by the ring solver.  The columns of the
-- matrix are the actions on the basis vectors, so two circuits whose
-- integer columns agree up to scale have one matrix (`fast-sound`).
-- One check costs integer arithmetic only, where comparing the dyadic
-- matrices multiplies them out.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.ThreeWire.Fast where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; _-_)
import Data.Integer.Properties as ℤP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open import Relation.Nullary.Decidable using (does)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (D ; ι ; ι-+ ; ι-neg ; ι-* ; ½ᴰ ; 2ᴰ ; ½*2 ; commutativeRing-D ; module DR ; _*ᴰ_ ; 1ᴰ)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH.Semantics as Q
open import Examples.Groups.CCX+HH.Syntactics using (Circuit ; Gen ; gate₀ ; _↥)
open import Examples.Groups.CCX+HH.Natural.Axioms using (x₀ ; x₁ ; x₂ ; cx₀ ; cx₁ ; hh₀ ; hh₁ ; ccx₀)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum ; quantum-column)
open import Examples.Groups.CCX+HH.GeneralN.BasisVectors using (basis)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fin8 using (allFin ; allFin-sound)
open import Quantum.Synthesis.Ring.Properties.Common using (module ZSolver)
open import Algebra.Bundles using (CommutativeRing)

private
  module S = ZSolver commutativeRing-D
  module R = CommutativeRing commutativeRing-D

------------------------------------------------------------------------
-- Scaled integer columns

Col : Set
Col = Vec ℤ 8

-- 2⁻ᵏ
p2 : ℕ → D
p2 zero    = R.1#
p2 (suc k) = ½ᴰ R.* p2 k

emb : ℕ → Col → Vec D 8
emb k = map (λ z → p2 k R.* ι z)

-- The four rows of H ⊗ H, unscaled.
rA rB rC rD : ℤ → ℤ → ℤ → ℤ → ℤ
rA a b c d = a ℤ.+ b ℤ.+ c ℤ.+ d
rB a b c d = a - b ℤ.+ c - d
rC a b c d = a ℤ.+ b - c - d
rD a b c d = a - b - c ℤ.+ d

act : Gen 3 → Col → Col
act x₀   (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = b ∷ a ∷ d ∷ c ∷ f ∷ e ∷ h ∷ g ∷ []
act x₁   (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = c ∷ d ∷ a ∷ b ∷ g ∷ h ∷ e ∷ f ∷ []
act x₂   (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = e ∷ f ∷ g ∷ h ∷ a ∷ b ∷ c ∷ d ∷ []
act cx₀  (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = a ∷ b ∷ d ∷ c ∷ e ∷ f ∷ h ∷ g ∷ []
act cx₁  (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = a ∷ b ∷ c ∷ d ∷ g ∷ h ∷ e ∷ f ∷ []
act ccx₀ (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ h ∷ g ∷ []
act hh₀  (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
  rA a b c d ∷ rB a b c d ∷ rC a b c d ∷ rD a b c d ∷ rA e f g h ∷ rB e f g h ∷ rC e f g h ∷ rD e f g h ∷ []
act hh₁  (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
  rA a c e g ∷ rA b d f h ∷ rB a c e g ∷ rB b d f h ∷ rC a c e g ∷ rC b d f h ∷ rD a c e g ∷ rD b d f h ∷ []
act (gate₀ ())
act (gate₀ () ↥)
act (gate₀ () ↥ ↥)
act (gate₀ () ↥ ↥ ↥)

hs : Gen 3 → ℕ
hs hh₀ = 1
hs hh₁ = 1
hs _   = 0

run : Circuit 3 → ℕ × Col → ℕ × Col
run [ g ]ʷ  (k , v) = hs g ℕ.+ k , act g v
run ε       x       = x
run (u • w) x       = run u (run w x)

------------------------------------------------------------------------
-- The bridge

private
  ⟦_⟧ : ℕ × Col → Vec D 8
  ⟦ k , v ⟧ = emb k v

  -- One entry of H ⊗ H.
  row : ∀ (p σ₂ σ₃ σ₄ u₁ u₂ u₃ u₄ : D) →
        ½ᴰ R.* (R.1# R.* (p R.* u₁) R.+ σ₂ R.* (p R.* u₂) R.+ σ₃ R.* (p R.* u₃) R.+ σ₄ R.* (p R.* u₄)) ≡
        (½ᴰ R.* p) R.* (u₁ R.+ σ₂ R.* u₂ R.+ σ₃ R.* u₃ R.+ σ₄ R.* u₄)
  row p σ₂ σ₃ σ₄ u₁ u₂ u₃ u₄ = S.solve 9 (λ h p y₂ y₃ y₄ u₁ u₂ u₃ u₄ →
      h S.:* (S.con (+ 1) S.:* (p S.:* u₁) S.:+ y₂ S.:* (p S.:* u₂) S.:+ y₃ S.:* (p S.:* u₃) S.:+ y₄ S.:* (p S.:* u₄))
      S.:= (h S.:* p) S.:* (u₁ S.:+ y₂ S.:* u₂ S.:+ y₃ S.:* u₃ S.:+ y₄ S.:* u₄))
    Eq.refl ½ᴰ p σ₂ σ₃ σ₄ u₁ u₂ u₃ u₄

  ι-sum : ∀ s₂ s₃ s₄ a b c d →
          ι a R.+ ι s₂ R.* ι b R.+ ι s₃ R.* ι c R.+ ι s₄ R.* ι d ≡
          ι (a ℤ.+ s₂ ℤ.* b ℤ.+ s₃ ℤ.* c ℤ.+ s₄ ℤ.* d)
  ι-sum s₂ s₃ s₄ a b c d = sym (trans (ι-+ _ _) (cong₂ R._+_
    (trans (ι-+ _ _) (cong₂ R._+_ (trans (ι-+ _ _) (cong (ι a R.+_) (ι-* s₂ b))) (ι-* s₃ c)))
    (ι-* s₄ d)))

  pm : ℤ
  pm = ℤ.- (+ 1)

  e₊ : ι (+ 1) ≡ R.1#
  e₊ = refl

  e₋ : ι pm ≡ R.- R.1#
  e₋ = ι-neg (+ 1)

  neg : ∀ x → ℤ.- x ≡ pm ℤ.* x
  neg x = sym (ℤP.-1*i≡-i x)

  one : ∀ x → x ≡ + 1 ℤ.* x
  one x = sym (ℤP.*-identityˡ x)

  sA : ∀ a b c d → rA a b c d ≡ a ℤ.+ + 1 ℤ.* b ℤ.+ + 1 ℤ.* c ℤ.+ + 1 ℤ.* d
  sA a b c d = cong₂ ℤ._+_ (cong₂ ℤ._+_ (cong (λ z → a ℤ.+ z) (one b)) (one c)) (one d)

  sB : ∀ a b c d → rB a b c d ≡ a ℤ.+ pm ℤ.* b ℤ.+ + 1 ℤ.* c ℤ.+ pm ℤ.* d
  sB a b c d = cong₂ ℤ._+_ (cong₂ ℤ._+_ (cong (λ z → a ℤ.+ z) (neg b)) (one c)) (neg d)

  sC : ∀ a b c d → rC a b c d ≡ a ℤ.+ + 1 ℤ.* b ℤ.+ pm ℤ.* c ℤ.+ pm ℤ.* d
  sC a b c d = cong₂ ℤ._+_ (cong₂ ℤ._+_ (cong (λ z → a ℤ.+ z) (one b)) (neg c)) (neg d)

  sD : ∀ a b c d → rD a b c d ≡ a ℤ.+ pm ℤ.* b ℤ.+ pm ℤ.* c ℤ.+ + 1 ℤ.* d
  sD a b c d = cong₂ ℤ._+_ (cong₂ ℤ._+_ (cong (λ z → a ℤ.+ z) (neg b)) (neg c)) (one d)

  entry : ∀ k (s₂ s₃ s₄ : ℤ) {σ₂ σ₃ σ₄ : D} → ι s₂ ≡ σ₂ → ι s₃ ≡ σ₃ → ι s₄ ≡ σ₄ → ∀ a b c d (t : ℤ) →
          t ≡ a ℤ.+ s₂ ℤ.* b ℤ.+ s₃ ℤ.* c ℤ.+ s₄ ℤ.* d →
          ½ᴰ R.* (R.1# R.* (p2 k R.* ι a) R.+ σ₂ R.* (p2 k R.* ι b) R.+ σ₃ R.* (p2 k R.* ι c) R.+ σ₄ R.* (p2 k R.* ι d)) ≡
          p2 (suc k) R.* ι t
  entry k s₂ s₃ s₄ refl refl refl a b c d t e = trans (row (p2 k) (ι s₂) (ι s₃) (ι s₄) (ι a) (ι b) (ι c) (ι d))
    (cong ((½ᴰ R.* p2 k) R.*_) (trans (ι-sum s₂ s₃ s₄ a b c d) (cong ι (sym e))))

  v8 : ∀ {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : D} →
       a₀ ≡ b₀ → a₁ ≡ b₁ → a₂ ≡ b₂ → a₃ ≡ b₃ → a₄ ≡ b₄ → a₅ ≡ b₅ → a₆ ≡ b₆ → a₇ ≡ b₇ →
       (a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ a₄ ∷ a₅ ∷ a₆ ∷ a₇ ∷ []) ≡ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ [])
  v8 refl refl refl refl refl refl refl refl = refl

  eA = λ k → entry k (+ 1) (+ 1) (+ 1) e₊ e₊ e₊
  eB = λ k → entry k pm (+ 1) pm e₋ e₊ e₋
  eC = λ k → entry k (+ 1) pm pm e₊ e₋ e₋
  eD = λ k → entry k pm pm (+ 1) e₋ e₋ e₊

gate-bridge : ∀ g k v → Q.gate-action g (emb k v) ≡ emb (hs g ℕ.+ k) (act g v)
gate-bridge x₀   k (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
gate-bridge x₁   k (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
gate-bridge x₂   k (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
gate-bridge cx₀  k (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
gate-bridge cx₁  k (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
gate-bridge ccx₀ k (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
gate-bridge hh₀  k (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = v8
  (eA k a b c d _ (sA a b c d)) (eB k a b c d _ (sB a b c d))
  (eC k a b c d _ (sC a b c d)) (eD k a b c d _ (sD a b c d))
  (eA k e f g h _ (sA e f g h)) (eB k e f g h _ (sB e f g h))
  (eC k e f g h _ (sC e f g h)) (eD k e f g h _ (sD e f g h))
gate-bridge hh₁  k (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = v8
  (eA k a c e g _ (sA a c e g)) (eA k b d f h _ (sA b d f h))
  (eB k a c e g _ (sB a c e g)) (eB k b d f h _ (sB b d f h))
  (eC k a c e g _ (sC a c e g)) (eC k b d f h _ (sC b d f h))
  (eD k a c e g _ (sD a c e g)) (eD k b d f h _ (sD b d f h))
gate-bridge (gate₀ ())
gate-bridge (gate₀ () ↥)
gate-bridge (gate₀ () ↥ ↥)
gate-bridge (gate₀ () ↥ ↥ ↥)

bridge : ∀ (w : Circuit 3) x → quantum w ⟦ x ⟧ ≡ ⟦ run w x ⟧
bridge [ g ]ʷ  (k , v) = gate-bridge g k v
bridge ε       x       = refl
bridge (u • w) x       = trans (cong (quantum u) (bridge w x)) (bridge u (run w x))

------------------------------------------------------------------------
-- Comparing scaled columns

pow2 : ℕ → ℤ
pow2 zero    = + 1
pow2 (suc k) = + 2 ℤ.* pow2 k

eqZ : ℤ → ℤ → Bool
eqZ x y = does (x ℤP.≟ y)

eqV : ∀ {m} → ℤ → ℤ → Vec ℤ m → Vec ℤ m → Bool
eqV m n []       []       = true
eqV m n (x ∷ xs) (y ∷ ys) = eqZ (m ℤ.* x) (n ℤ.* y) ∧ eqV m n xs ys

eqKV : ℕ × Col → ℕ × Col → Bool
eqKV (k , a) (l , b) = eqV (pow2 l) (pow2 k) a b

private
  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true} _ = refl

  ∧-r : ∀ a {b} → a ∧ b ≡ true → b ≡ true
  ∧-r true h = h

  eqZ-sound : ∀ x y → eqZ x y ≡ true → x ≡ y
  eqZ-sound x y h with x ℤP.≟ y
  ... | Relation.Nullary.Decidable.yes e = e
    where import Relation.Nullary.Decidable

  inv2 : ∀ k → p2 k R.* ι (pow2 k) ≡ R.1#
  inv2 zero    = R.*-identityˡ R.1#
  inv2 (suc k) = begin
    (½ᴰ R.* p2 k) R.* ι (+ 2 ℤ.* pow2 k)       ≡⟨ cong ((½ᴰ R.* p2 k) R.*_) (ι-* (+ 2) (pow2 k)) ⟩
    (½ᴰ R.* p2 k) R.* (2ᴰ R.* ι (pow2 k))       ≡⟨ S.solve 4 (λ h p t q → (h S.:* p) S.:* (t S.:* q) S.:= (h S.:* t) S.:* (p S.:* q))
                                                      refl ½ᴰ (p2 k) 2ᴰ (ι (pow2 k)) ⟩
    (½ᴰ R.* 2ᴰ) R.* (p2 k R.* ι (pow2 k))       ≡⟨ cong₂ R._*_ ½*2 (inv2 k) ⟩
    R.1# R.* R.1#                               ≡⟨ R.*-identityˡ R.1# ⟩
    R.1#                                        ∎
    where open Eq.≡-Reasoning

  scale-eq : ∀ k l x y → pow2 l ℤ.* x ≡ pow2 k ℤ.* y → p2 k R.* ι x ≡ p2 l R.* ι y
  scale-eq k l x y e = begin
    p2 k R.* ι x                                      ≡⟨ S.solve 4 (λ p q t u → p S.:* u S.:= (p S.:* u) S.:* (S.con (+ 1)))
                                                          refl (p2 k) (p2 l) (ι (pow2 l)) (ι x) ⟩
    (p2 k R.* ι x) R.* R.1#                           ≡⟨ cong ((p2 k R.* ι x) R.*_) (sym (inv2 l)) ⟩
    (p2 k R.* ι x) R.* (p2 l R.* ι (pow2 l))          ≡⟨ S.solve 4 (λ p q t u → (p S.:* u) S.:* (q S.:* t) S.:= (p S.:* q) S.:* (t S.:* u))
                                                          refl (p2 k) (p2 l) (ι (pow2 l)) (ι x) ⟩
    (p2 k R.* p2 l) R.* (ι (pow2 l) R.* ι x)          ≡⟨ cong ((p2 k R.* p2 l) R.*_) (sym (ι-* (pow2 l) x)) ⟩
    (p2 k R.* p2 l) R.* ι (pow2 l ℤ.* x)              ≡⟨ cong (λ z → (p2 k R.* p2 l) R.* ι z) e ⟩
    (p2 k R.* p2 l) R.* ι (pow2 k ℤ.* y)              ≡⟨ cong ((p2 k R.* p2 l) R.*_) (ι-* (pow2 k) y) ⟩
    (p2 k R.* p2 l) R.* (ι (pow2 k) R.* ι y)          ≡⟨ S.solve 4 (λ p q t u → (p S.:* q) S.:* (t S.:* u) S.:= (q S.:* u) S.:* (p S.:* t))
                                                          refl (p2 k) (p2 l) (ι (pow2 k)) (ι y) ⟩
    (p2 l R.* ι y) R.* (p2 k R.* ι (pow2 k))          ≡⟨ cong ((p2 l R.* ι y) R.*_) (inv2 k) ⟩
    (p2 l R.* ι y) R.* R.1#                           ≡⟨ R.*-identityʳ _ ⟩
    p2 l R.* ι y                                      ∎
    where open Eq.≡-Reasoning

  eqV-sound : ∀ k l (a b : Vec ℤ 8) → eqV (pow2 l) (pow2 k) a b ≡ true → emb k a ≡ emb l b
  eqV-sound k l a b h = go a b h
    where
    go : ∀ {m} (a b : Vec ℤ m) → eqV (pow2 l) (pow2 k) a b ≡ true →
         map (λ z → p2 k R.* ι z) a ≡ map (λ z → p2 l R.* ι z) b
    go []       []       _ = refl
    go (x ∷ xs) (y ∷ ys) h = cong₂ _∷_
      (scale-eq k l x y (eqZ-sound _ _ (∧-l h))) (go xs ys (∧-r (eqZ (pow2 l ℤ.* x) (pow2 k ℤ.* y)) h))

------------------------------------------------------------------------
-- Basis columns

eZ : Fin 8 → Col
eZ ₀ = + 1 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ []
eZ ₁ = + 0 ∷ + 1 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ []
eZ ₂ = + 0 ∷ + 0 ∷ + 1 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ []
eZ ₃ = + 0 ∷ + 0 ∷ + 0 ∷ + 1 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ []
eZ ₄ = + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 1 ∷ + 0 ∷ + 0 ∷ + 0 ∷ []
eZ ₅ = + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 1 ∷ + 0 ∷ + 0 ∷ []
eZ ₆ = + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 1 ∷ + 0 ∷ []
eZ ₇ = + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 0 ∷ + 1 ∷ []

private
  emb0 : ∀ {m} (v : Vec ℤ m) → map (λ z → p2 0 R.* ι z) v ≡ map ι v
  emb0 []      = refl
  emb0 (z ∷ v) = cong₂ _∷_ (R.*-identityˡ (ι z)) (emb0 v)

  basis-ι : ∀ i → basis i ≡ map ι (eZ i)
  basis-ι ₀ = refl
  basis-ι ₁ = refl
  basis-ι ₂ = refl
  basis-ι ₃ = refl
  basis-ι ₄ = refl
  basis-ι ₅ = refl
  basis-ι ₆ = refl
  basis-ι ₇ = refl

  basis-emb : ∀ i → basis i ≡ emb 0 (eZ i)
  basis-emb i = trans (basis-ι i) (sym (emb0 (eZ i)))

------------------------------------------------------------------------
-- The check

fastCheck : Circuit 3 → Circuit 3 → Bool
fastCheck u v = allFin 8 (λ i → eqKV (run u (0 , eZ i)) (run v (0 , eZ i)))

fast-sound : ∀ (u v : Circuit 3) → fastCheck u v ≡ true → Q.interpret u ≡ Q.interpret v
fast-sound u v h = A.col-ext λ i → begin
  A.col (Q.interpret u) i            ≡⟨ quantum-column u i ⟩
  quantum u (basis i)                ≡⟨ cong (quantum u) (basis-emb i) ⟩
  quantum u ⟦ 0 , eZ i ⟧             ≡⟨ bridge u (0 , eZ i) ⟩
  ⟦ run u (0 , eZ i) ⟧               ≡⟨ same i ⟩
  ⟦ run v (0 , eZ i) ⟧               ≡⟨ sym (bridge v (0 , eZ i)) ⟩
  quantum v ⟦ 0 , eZ i ⟧             ≡⟨ cong (quantum v) (sym (basis-emb i)) ⟩
  quantum v (basis i)                ≡⟨ sym (quantum-column v i) ⟩
  A.col (Q.interpret v) i            ∎
  where
  open Eq.≡-Reasoning
  sameKV : ∀ x y → eqKV x y ≡ true → ⟦ x ⟧ ≡ ⟦ y ⟧
  sameKV (k , a) (l , b) ok = eqV-sound k l a b ok
  same : ∀ i → ⟦ run u (0 , eZ i) ⟧ ≡ ⟦ run v (0 , eZ i) ⟧
  same i = sameKV (run u (0 , eZ i)) (run v (0 , eZ i))
    (allFin-sound 8 (λ j → eqKV (run u (0 , eZ j)) (run v (0 , eZ j))) h i)
