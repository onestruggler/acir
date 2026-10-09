------------------------------------------------------------------------
-- Presentations of groups
--
-- Unit vectors over ℤ[1/2].  A unit vector v = w / 2ᵏ has Σₓ wₓ² = 4ᵏ
-- (unit-norm).  An odd square is 1 and an even one 0 modulo 4, so
--
-- * if k > 0, the number of odd wₓ is a multiple of 4 (nodd-mod4,
--   the existence of four odd entries in Algorithm 1, as in the proof
--   of Lemma 3.2);
-- * if k = 0, exactly one wₓ is nonzero, and it is ±1 (Lemma 3.3,
--   lde0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Norm where

open import Data.Bool.Base using (Bool ; true ; false ; not ; if_then_else_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_] ; ∣_∣)
import Data.Integer.Properties as ℤP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; _%_)
import Data.Nat.DivMod as ℕD
import Data.Nat.Properties as ℕP
import Data.Nat.Solver as ℕSolver
open import Data.Product.Base using (∃ ; _×_ ; _,_)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import Examples.Groups.CCX+HH-TwoLevel.Ring
open import Examples.Groups.CCX+HH-TwoLevel.Scale
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (_!_ ; scV ; scV-!)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics hiding (_!_)

private
  variable
    n : ℕ
  module ℕS = ℕSolver.+-*-Solver

------------------------------------------------------------------------
-- Squares

sq : ℤ → ℕ
sq x = ∣ x ∣ ℕ.* ∣ x ∣

+sq : ∀ x → + sq x ≡ x ℤ.* x
+sq (+ m) = ℤP.pos-* m m
+sq -[1+ m ] = refl

-- The indicator of oddness.
ind : Bool → ℕ
ind b = if b then 1 else 0

private
  sqℕ-mod4 : ∀ m → (m ℕ.* m) % 4 ≡ ind (oddℕ m)
  sqℕ-mod4 zero = refl
  sqℕ-mod4 (suc zero) = refl
  sqℕ-mod4 (suc (suc m)) = begin
    (suc (suc m) ℕ.* suc (suc m)) % 4      ≡⟨ cong (_% 4) (ℕS.solve 1 (λ m → (con 2 :+ m) :* (con 2 :+ m)
                                                  := m :* m :+ (con 1 :+ m) :* con 4) refl m) ⟩
    (m ℕ.* m ℕ.+ suc m ℕ.* 4) % 4          ≡⟨ ℕD.[m+kn]%n≡m%n (m ℕ.* m) (suc m) 4 ⟩
    (m ℕ.* m) % 4                          ≡⟨ sqℕ-mod4 m ⟩
    ind (oddℕ m)                           ≡⟨ cong ind (sym (BoolP.not-involutive (oddℕ m))) ⟩
    ind (not (not (oddℕ m)))               ∎
    where
    open ≡-Reasoning
    open ℕS using (_:+_ ; _:*_ ; _:=_ ; con)

sq-mod4 : ∀ x → sq x % 4 ≡ ind (oddℤ x)
sq-mod4 x = sqℕ-mod4 ∣ x ∣

------------------------------------------------------------------------
-- Sums

Σℕ : (Fin n → ℕ) → ℕ
Σℕ {zero} f = 0
Σℕ {suc n} f = f zero ℕ.+ Σℕ (f ∘ suc)

Σℤ : (Fin n → ℤ) → ℤ
Σℤ {zero} f = + 0
Σℤ {suc n} f = f zero ℤ.+ Σℤ (f ∘ suc)

private
  ind%4 : ∀ b → ind b % 4 ≡ ind b
  ind%4 true  = refl
  ind%4 false = refl

-- Σₓ wₓ² ≡ (number of odd wₓ) modulo 4.
Σsq-mod4 : (w : Vec ℤ n) → Σℕ (λ x → sq (w ! x)) % 4 ≡ count (λ x → oddℤ (w ! x)) % 4
Σsq-mod4 [] = refl
Σsq-mod4 (z ∷ zs) = begin
  (sq z ℕ.+ S) % 4                             ≡⟨ ℕD.%-distribˡ-+ (sq z) S 4 ⟩
  (sq z % 4 ℕ.+ S % 4) % 4                     ≡⟨ cong₂ (λ a b → (a ℕ.+ b) % 4) (trans (sq-mod4 z) (sym (ind%4 (oddℤ z))))
                                                                                 (Σsq-mod4 zs) ⟩
  (ind (oddℤ z) % 4 ℕ.+ C % 4) % 4             ≡⟨ sym (ℕD.%-distribˡ-+ (ind (oddℤ z)) C 4) ⟩
  (ind (oddℤ z) ℕ.+ C) % 4                     ∎
  where
  open ≡-Reasoning
  S = Σℕ (λ x → sq (zs ! x))
  C = count (λ x → oddℤ (zs ! x))

-- If Σₓ wₓ² = 4ᵏ with k > 0, the number of odd wₓ is a multiple of 4.
nodd-mod4 : ∀ k (w : Vec ℤ n) → Σℕ (λ x → sq (w ! x)) ≡ 4 ℕ.^ suc k → count (λ x → oddℤ (w ! x)) % 4 ≡ 0
nodd-mod4 k w eq = begin
  count (λ x → oddℤ (w ! x)) % 4          ≡⟨ sym (Σsq-mod4 w) ⟩
  Σℕ (λ x → sq (w ! x)) % 4                ≡⟨ cong (_% 4) eq ⟩
  (4 ℕ.* 4 ℕ.^ k) % 4                      ≡⟨ cong (_% 4) (ℕP.*-comm 4 (4 ℕ.^ k)) ⟩
  (0 ℕ.+ 4 ℕ.^ k ℕ.* 4) % 4                ≡⟨ ℕD.[m+kn]%n≡m%n 0 (4 ℕ.^ k) 4 ⟩
  0                                        ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- k = 0

private
  Σℕ≡0 : (f : Fin n → ℕ) → Σℕ f ≡ 0 → ∀ x → f x ≡ 0
  Σℕ≡0 {suc n} f eq zero = ℕP.m+n≡0⇒m≡0 (f zero) eq
  Σℕ≡0 {suc n} f eq (suc x) = Σℕ≡0 (f ∘ suc) (ℕP.m+n≡0⇒n≡0 (f zero) eq) x

  Σℕ≡1 : (f : Fin n → ℕ) → Σℕ f ≡ 1 → ∃ λ m → f m ≡ 1 × (∀ y → y ≢ m → f y ≡ 0)
  Σℕ≡1 {suc n} f eq with f zero in e
  ... | 0 = let (m , fm , rest) = Σℕ≡1 (f ∘ suc) eq in
            suc m , fm , λ { zero _ → e ; (suc y) y≢m → rest y (y≢m ∘ cong suc) }
  ... | 1 = zero , e , λ { zero z≢z → ⊥-elim (z≢z refl) ; (suc y) _ → Σℕ≡0 (f ∘ suc) (ℕP.suc-injective eq) y }
  ... | suc (suc m′) = ⊥-elim (big eq)
    where big : suc (suc m′) ℕ.+ Σℕ (f ∘ suc) ≢ 1
          big ()

  sq0 : ∀ x → sq x ≡ 0 → x ≡ + 0
  sq0 x e = ℤP.∣i∣≡0⇒i≡0 (m*m≡0 ∣ x ∣ e)
    where
    m*m≡0 : ∀ m → m ℕ.* m ≡ 0 → m ≡ 0
    m*m≡0 zero _ = refl

  sq1 : ∀ x → sq x ≡ 1 → x ≡ + 1 ⊎ x ≡ -[1+ 0 ]
  sq1 (+ 1) _ = inj₁ refl
  sq1 -[1+ 0 ] _ = inj₂ refl
  sq1 (+ 0) ()
  sq1 (+ suc (suc m)) ()
  sq1 -[1+ suc m ] ()

-- "lde0": if Σₓ wₓ² = 1, a single wₓ is nonzero, and it is ±1.
lde0 : (w : Vec ℤ n) → Σℕ (λ x → sq (w ! x)) ≡ 1 →
       ∃ λ m → (w ! m ≡ + 1 ⊎ w ! m ≡ -[1+ 0 ]) × (∀ y → y ≢ m → w ! y ≡ + 0)
lde0 w eq with Σℕ≡1 (λ x → sq (w ! x)) eq
... | m , Nm , rest = m , sq1 (w ! m) Nm , λ y y≢m → sq0 (w ! y) (rest y y≢m)

------------------------------------------------------------------------
-- From ⟨ v , v ⟩ = 1 to Σₓ wₓ² = 4ᵏ

private
  -- 1/4 = (1/2)², and 4 · 1/4 = 1.
  ε : D
  ε = ½ᴰ DR.* ½ᴰ

  opaque
    unfolding _*ᴰ_

    ε*4 : ε DR.* ι (+ 4) ≡ DR.1#
    ε*4 = refl

-- (a/2ᵏ)(b/2ᵏ) = a b εᵏ, conjugation being the identity.
adj-sc*sc : ∀ k a b → adjᴰ (sc k a) DR.* sc k b ≡ ι (a ℤ.* b) DR.* (ε ^ᴰ k)
adj-sc*sc k a b = begin
  adjᴰ (sc k a) DR.* sc k b
    ≡⟨ cong (DR._* sc k b) (adjᴰ-id (sc k a)) ⟩
  sc k a DR.* sc k b
    ≡⟨ cong₂ DR._*_ (sc-def k a) (sc-def k b) ⟩
  (ι a DR.* (½ᴰ ^ᴰ k)) DR.* (ι b DR.* (½ᴰ ^ᴰ k))
    ≡⟨ DA.*-4 (ι a) (½ᴰ ^ᴰ k) (ι b) (½ᴰ ^ᴰ k) ⟩
  (ι a DR.* ι b) DR.* ((½ᴰ ^ᴰ k) DR.* (½ᴰ ^ᴰ k))
    ≡⟨ cong₂ DR._*_ (sym (ι-* a b)) (sym (DA.^-*-distrib ½ᴰ ½ᴰ k)) ⟩
  ι (a ℤ.* b) DR.* (ε ^ᴰ k) ∎
  where open ≡-Reasoning

private
  ι-Σ : (f : Fin n → ℤ) → sum (λ x → ι (f x)) ≡ ι (Σℤ f)
  ι-Σ {zero} f = refl
  ι-Σ {suc n} f = trans (cong (ι (f zero) DR.+_) (ι-Σ (f ∘ suc))) (sym (ι-+ (f zero) (Σℤ (f ∘ suc))))

  ι-^ : ∀ a k → ι (a ℤ.^ k) ≡ ι a ^ᴰ k
  ι-^ a zero = refl
  ι-^ a (suc k) = trans (ι-* a (a ℤ.^ k)) (cong (ι a DR.*_) (ι-^ a k))

-- ⟨ w/2ᵏ , w/2ᵏ ⟩ = (Σₓ wₓ²) εᵏ.
ip-scV : ∀ k (w : Vec ℤ n) → ⟨ scV k w , scV k w ⟩ ≡ ι (Σℤ (λ x → (w ! x) ℤ.* (w ! x))) DR.* (ε ^ᴰ k)
ip-scV k w = begin
  sum (λ x → adjᴰ (scV k w ! x) DR.* (scV k w ! x))
    ≡⟨ sum-cong-≗ (λ x → cong (λ a → adjᴰ a DR.* a) (scV-! k w x)) ⟩
  sum (λ x → adjᴰ (sc k (w ! x)) DR.* sc k (w ! x))
    ≡⟨ sum-cong-≗ (λ x → adj-sc*sc k (w ! x) (w ! x)) ⟩
  sum (λ x → ι ((w ! x) ℤ.* (w ! x)) DR.* (ε ^ᴰ k))
    ≡⟨ sym (*-distribʳ-sum (ε ^ᴰ k) (λ x → ι ((w ! x) ℤ.* (w ! x)))) ⟩
  sum (λ x → ι ((w ! x) ℤ.* (w ! x))) DR.* (ε ^ᴰ k)
    ≡⟨ cong (DR._* (ε ^ᴰ k)) (ι-Σ (λ x → (w ! x) ℤ.* (w ! x))) ⟩
  ι (Σℤ (λ x → (w ! x) ℤ.* (w ! x))) DR.* (ε ^ᴰ k) ∎
  where open ≡-Reasoning

-- A unit vector w/2ᵏ has Σₓ wₓ² = 4ᵏ, in ℤ.
unit-normℤ : ∀ k (w : Vec ℤ n) → ⟨ scV k w , scV k w ⟩ ≡ DR.1# →
             Σℤ (λ x → (w ! x) ℤ.* (w ! x)) ≡ (+ 4) ℤ.^ k
unit-normℤ k w eq = ι-injective (begin
  ι S                                               ≡⟨ sym (DR.*-identityʳ (ι S)) ⟩
  ι S DR.* DR.1#                                    ≡⟨ cong (ι S DR.*_) (sym (DA.^-inverse ε (ι (+ 4)) k ε*4)) ⟩
  ι S DR.* ((ε ^ᴰ k) DR.* (ι (+ 4) ^ᴰ k))           ≡⟨ sym (DR.*-assoc (ι S) (ε ^ᴰ k) (ι (+ 4) ^ᴰ k)) ⟩
  (ι S DR.* (ε ^ᴰ k)) DR.* (ι (+ 4) ^ᴰ k)           ≡⟨ cong (DR._* (ι (+ 4) ^ᴰ k)) (trans (sym (ip-scV k w)) eq) ⟩
  DR.1# DR.* (ι (+ 4) ^ᴰ k)                         ≡⟨ DR.*-identityˡ (ι (+ 4) ^ᴰ k) ⟩
  ι (+ 4) ^ᴰ k                                      ≡⟨ sym (ι-^ (+ 4) k) ⟩
  ι ((+ 4) ℤ.^ k)                                     ∎)
  where
  open ≡-Reasoning
  S = Σℤ (λ x → (w ! x) ℤ.* (w ! x))

private
  pos-Σ : (f : Fin n → ℕ) → + Σℕ f ≡ Σℤ (λ x → + f x)
  pos-Σ {zero} f = refl
  pos-Σ {suc n} f = trans (ℤP.pos-+ (f zero) (Σℕ (f ∘ suc))) (cong (λ z → + f zero ℤ.+ z) (pos-Σ (f ∘ suc)))

  Σℤ-cong : (f g : Fin n → ℤ) → (∀ x → f x ≡ g x) → Σℤ f ≡ Σℤ g
  Σℤ-cong {zero} f g eq = refl
  Σℤ-cong {suc n} f g eq = cong₂ ℤ._+_ (eq zero) (Σℤ-cong (f ∘ suc) (g ∘ suc) (eq ∘ suc))

  pos-^ : ∀ m k → + (m ℕ.^ k) ≡ (+ m) ℤ.^ k
  pos-^ m zero = refl
  pos-^ m (suc k) = trans (ℤP.pos-* m (m ℕ.^ k)) (cong (+ m ℤ.*_) (pos-^ m k))

-- Σₓ wₓ² = 4ᵏ.
unit-norm : ∀ k (w : Vec ℤ n) → ⟨ scV k w , scV k w ⟩ ≡ DR.1# → Σℕ (λ x → sq (w ! x)) ≡ 4 ℕ.^ k
unit-norm k w eq = ℤP.+-injective (begin
  + Σℕ (λ x → sq (w ! x))                    ≡⟨ pos-Σ (λ x → sq (w ! x)) ⟩
  Σℤ (λ x → + sq (w ! x))                    ≡⟨ Σℤ-cong _ _ (λ x → +sq (w ! x)) ⟩
  Σℤ (λ x → (w ! x) ℤ.* (w ! x))             ≡⟨ unit-normℤ k w eq ⟩
  (+ 4) ℤ.^ k                                  ≡⟨ sym (pos-^ 4 k) ⟩
  + (4 ℕ.^ k)                                ∎)
  where open ≡-Reasoning
