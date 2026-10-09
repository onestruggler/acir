------------------------------------------------------------------------
-- Presentations of groups
--
-- Unit vectors over ℤ[1/√2].  For w = a + b√2 in ℤ[√2],
--
--   w² = A + 2B √2,   A = a² + 2b²,   B = ab,
--
-- and A ≡ a (mod 2) is odd iff w is.  A unit vector v = w / √2ᵏ has
-- Σₓ wₓ² = 2ᵏ, so Σₓ Aₓ = 2ᵏ and Σₓ Bₓ = 0.  Hence:
--
-- * if k > 0, an even number of the wₓ are odd (evenodd), and an even
--   number are ≡ 1 + √2 (mod 2), i.e. odd with an odd √2-coefficient
--   (evenclass): every residue class of odd entries has an even size
--   (the existence of i₂ in Algorithm 1, after [Amy et al. 2020]);
-- * if k = 0, exactly one wₓ is nonzero, and it is ±1 (lde0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Norm where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _xor_ ; _∧_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_] ; ∣_∣)
import Data.Integer.Properties as ℤP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
import Data.Integer.Solver as ℤSolver

open import Quantum.Synthesis.Ring using (RootTwo)

open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (oddℕ-+ ; oddℕ-*)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Scale
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde
  using (_!_ ; scV ; scV-! ; Odd ; Even)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
  hiding (_!_)

private
  variable
    n : ℕ
  module ℤS = ℤSolver.+-*-Solver

------------------------------------------------------------------------
-- Squares in ℤ[√2]

private
  sq : ℤ → ℕ
  sq x = ∣ x ∣ ℕ.* ∣ x ∣

  +sq : ∀ x → + sq x ≡ x ℤ.* x
  +sq (+ m) = ℤP.pos-* m m
  +sq -[1+ m ] = refl

NA : Z → ℕ
NA (RootTwo a b) = sq a ℕ.+ (sq b ℕ.+ sq b)

NB : Z → ℤ
NB (RootTwo a b) = a ℤ.* b

-- w² = A + 2B √2.
sq-mul : ∀ w → w ZR.* w ≡ RootTwo (+ NA w) (NB w ℤ.+ NB w)
sq-mul (RootTwo a b) = cong₂ RootTwo ea eb
  where
  open ℤS using (_:+_ ; _:*_ ; _:=_)
  ea : a ℤ.* a ℤ.+ (b ℤ.* b ℤ.+ b ℤ.* b) ≡ + (sq a ℕ.+ (sq b ℕ.+ sq b))
  ea = sym (trans (ℤP.pos-+ (sq a) (sq b ℕ.+ sq b))
                  (cong₂ ℤ._+_ (+sq a) (trans (ℤP.pos-+ (sq b) (sq b)) (cong₂ ℤ._+_ (+sq b) (+sq b)))))
  eb : a ℤ.* b ℤ.+ a ℤ.* b ≡ a ℤ.* b ℤ.+ a ℤ.* b
  eb = refl

private
  oddℕ-sq : ∀ x → oddℕ (sq x) ≡ oddℤ x
  oddℕ-sq x = trans (oddℕ-* ∣ x ∣ ∣ x ∣) (∧-idem (oddℤ x))
    where
    ∧-idem : ∀ b → b ∧ b ≡ b
    ∧-idem true  = refl
    ∧-idem false = refl

  oddℕ-double : ∀ m → oddℕ (m ℕ.+ m) ≡ false
  oddℕ-double m = trans (oddℕ-+ m m) (lemma (oddℕ m))
    where
    lemma : ∀ b → b xor b ≡ false
    lemma true  = refl
    lemma false = refl

  xor-false : ∀ b → b xor false ≡ b
  xor-false true  = refl
  xor-false false = refl

oddℕ-NA : ∀ w → oddℕ (NA w) ≡ oddᶻ w
oddℕ-NA (RootTwo a b) =
  trans (oddℕ-+ (sq a) (sq b ℕ.+ sq b)) (trans (cong₂ _xor_ (oddℕ-sq a) (oddℕ-double (sq b))) (xor-false (oddℤ a)))

-- B is odd iff w is odd with an odd √2-coefficient.
oddℤ-NB : ∀ w → oddℤ (NB w) ≡ oddᶻ w ∧ rbit w
oddℤ-NB (RootTwo a b) = oddℤ-* a b

------------------------------------------------------------------------
-- Sums

Σℕ : (Fin n → ℕ) → ℕ
Σℕ {zero} f = 0
Σℕ {suc n} f = f zero ℕ.+ Σℕ (f ∘ suc)

Σℤ : (Fin n → ℤ) → ℤ
Σℤ {zero} f = + 0
Σℤ {suc n} f = f zero ℤ.+ Σℤ (f ∘ suc)

Σᶻ : (Fin n → Z) → Z
Σᶻ {zero} f = ZR.0#
Σᶻ {suc n} f = f zero ZR.+ Σᶻ (f ∘ suc)

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

  NA≡0 : ∀ w → NA w ≡ 0 → w ≡ ZR.0#
  NA≡0 (RootTwo a b) eq =
    cong₂ RootTwo (sq0 a (ℕP.m+n≡0⇒m≡0 (sq a) eq))
                  (sq0 b (ℕP.m+n≡0⇒m≡0 (sq b) (ℕP.m+n≡0⇒n≡0 (sq a) eq)))

  -- A ±1 coordinate, the other 0.
  NA≡1 : ∀ w → NA w ≡ 1 → w ≡ ZR.1# ⊎ w ≡ ZR.- ZR.1#
  NA≡1 (RootTwo a b) eq with sq b in eb
  ... | 0 with sq1 a (trans (sym (ℕP.+-identityʳ (sq a))) eq)
  ...   | inj₁ refl = inj₁ (cong (RootTwo (+ 1)) (sq0 b eb))
  ...   | inj₂ refl = inj₂ (cong (RootTwo -[1+ 0 ]) (sq0 b eb))
  NA≡1 (RootTwo a b) eq | suc m = ⊥-elim (big (sq a) m eq)
    where
    big : ∀ x m → x ℕ.+ (suc m ℕ.+ suc m) ≢ 1
    big x m e = ℕP.<⇒≢ (ℕP.<-≤-trans (ℕP.n<1+n 1) (ℕP.≤-trans two (ℕP.m≤n+m _ x))) (sym e)
      where
      two : 2 ℕ.≤ suc m ℕ.+ suc m
      two = ℕ.s≤s (subst (1 ℕ.≤_) (sym (ℕP.+-suc m m)) (ℕ.s≤s ℕ.z≤n))

  odd-ind : ∀ b → oddℕ (if b then 1 else 0) ≡ b
  odd-ind true  = refl
  odd-ind false = refl

-- The parity of Σₓ Aₓ is the parity of the number of odd wₓ.
parity-count : (w : Vec Z n) →
               oddℕ (Σℕ (λ x → NA (w ! x))) ≡ oddℕ (count (λ x → oddᶻ (w ! x)))
parity-count [] = refl
parity-count (z ∷ zs) = begin
  oddℕ (NA z ℕ.+ Σℕ (λ x → NA (zs ! x)))
    ≡⟨ oddℕ-+ (NA z) (Σℕ (λ x → NA (zs ! x))) ⟩
  oddℕ (NA z) xor oddℕ (Σℕ (λ x → NA (zs ! x)))
    ≡⟨ cong₂ _xor_ (trans (oddℕ-NA z) (sym (odd-ind (oddᶻ z)))) (parity-count zs) ⟩
  oddℕ (if oddᶻ z then 1 else 0) xor oddℕ (count (λ x → oddᶻ (zs ! x)))
    ≡⟨ sym (oddℕ-+ (if oddᶻ z then 1 else 0) (count (λ x → oddᶻ (zs ! x)))) ⟩
  oddℕ ((if oddᶻ z then 1 else 0) ℕ.+ count (λ x → oddᶻ (zs ! x))) ∎
  where open ≡-Reasoning

-- The parity of Σₓ Bₓ is the parity of the number of wₓ ≡ 1 + √2.
parity-countB : (w : Vec Z n) →
                oddℤ (Σℤ (λ x → NB (w ! x))) ≡ oddℕ (count (λ x → oddᶻ (w ! x) ∧ rbit (w ! x)))
parity-countB [] = refl
parity-countB (z ∷ zs) = begin
  oddℤ (NB z ℤ.+ Σℤ (λ x → NB (zs ! x)))
    ≡⟨ oddℤ-+ (NB z) (Σℤ (λ x → NB (zs ! x))) ⟩
  oddℤ (NB z) xor oddℤ (Σℤ (λ x → NB (zs ! x)))
    ≡⟨ cong₂ _xor_ (trans (oddℤ-NB z) (sym (odd-ind (oddᶻ z ∧ rbit z)))) (parity-countB zs) ⟩
  oddℕ (if oddᶻ z ∧ rbit z then 1 else 0) xor oddℕ (count (λ x → oddᶻ (zs ! x) ∧ rbit (zs ! x)))
    ≡⟨ sym (oddℕ-+ (if oddᶻ z ∧ rbit z then 1 else 0) (count (λ x → oddᶻ (zs ! x) ∧ rbit (zs ! x)))) ⟩
  oddℕ ((if oddᶻ z ∧ rbit z then 1 else 0) ℕ.+ count (λ x → oddᶻ (zs ! x) ∧ rbit (zs ! x))) ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Powers of 2

2ᶻ : Z
2ᶻ = RootTwo (+ 2) (+ 0)

2^ᶻ : ∀ k → 2ᶻ ^ᶻ k ≡ RootTwo (+ (2 ℕ.^ k)) (+ 0)
2^ᶻ zero = refl
2^ᶻ (suc k) = trans (cong (2ᶻ ZR.*_) (2^ᶻ k)) (cong₂ RootTwo ea eb)
  where
  open ℤS using (_:+_ ; _:*_ ; _:=_ ; con)
  p = + (2 ℕ.^ k)
  ea : + 2 ℤ.* p ℤ.+ (+ 0 ℤ.* + 0 ℤ.+ + 0 ℤ.* + 0) ≡ + (2 ℕ.^ suc k)
  ea = trans (ℤS.solve 1 (λ p → con (+ 2) :* p :+ (con (+ 0) :* con (+ 0) :+ con (+ 0) :* con (+ 0))
                              := con (+ 2) :* p) refl p)
             (sym (ℤP.pos-* 2 (2 ℕ.^ k)))
  eb : + 2 ℤ.* + 0 ℤ.+ p ℤ.* + 0 ≡ + 0
  eb = ℤS.solve 1 (λ p → con (+ 2) :* con (+ 0) :+ p :* con (+ 0) := con (+ 0)) refl p

------------------------------------------------------------------------
-- The two lemmas

-- "evenodd": if Σₓ Aₓ = 2ᵏ with k > 0, an even number of wₓ are odd.
evenodd : ∀ k (w : Vec Z n) → Σℕ (λ x → NA (w ! x)) ≡ 2 ℕ.^ suc k →
          oddℕ (count (λ x → oddᶻ (w ! x))) ≡ false
evenodd k w eq = trans (sym (parity-count w)) (trans (cong oddℕ eq) (oddℕ-* 2 (2 ℕ.^ k)))

-- "evenclass": if Σₓ Bₓ = 0, an even number of wₓ are ≡ 1 + √2.
evenclass : (w : Vec Z n) → Σℤ (λ x → NB (w ! x)) ≡ + 0 →
            oddℕ (count (λ x → oddᶻ (w ! x) ∧ rbit (w ! x))) ≡ false
evenclass w eq = trans (sym (parity-countB w)) (cong oddℤ eq)

-- "lde0": if Σₓ Aₓ = 1, a single wₓ is nonzero, and it is ±1.
lde0 : (w : Vec Z n) → Σℕ (λ x → NA (w ! x)) ≡ 1 →
       ∃ λ m → (w ! m ≡ ZR.1# ⊎ w ! m ≡ ZR.- ZR.1#) × (∀ y → y ≢ m → w ! y ≡ ZR.0#)
lde0 w eq with Σℕ≡1 (λ x → NA (w ! x)) eq
... | m , Nm , rest = m , NA≡1 (w ! m) Nm , λ y y≢m → NA≡0 (w ! y) (rest y y≢m)

------------------------------------------------------------------------
-- From ⟨ v , v ⟩ = 1 to Σₓ wₓ² = 2ᵏ

private
  -- ½ = (1/√2)², and 2 · ½ = 1.
  ε : D
  ε = √½ DR.* √½

  opaque
    unfolding _*ᴰ_

    ε*2 : ε DR.* emb 2ᶻ ≡ DR.1#
    ε*2 = refl

-- (w/√2ᵏ)(w′/√2ᵏ) = w w′ εᵏ, conjugation being the identity.
adj-sc*sc : ∀ k w w′ → adjᴰ (sc k w) DR.* sc k w′ ≡ emb (w ZR.* w′) DR.* (ε ^ᴰ k)
adj-sc*sc k w w′ = begin
  adjᴰ (sc k w) DR.* sc k w′
    ≡⟨ cong (DR._* sc k w′) (adjᴰ-id (sc k w)) ⟩
  sc k w DR.* sc k w′
    ≡⟨ cong₂ DR._*_ (sc-def k w) (sc-def k w′) ⟩
  (emb w DR.* (√½ ^ᴰ k)) DR.* (emb w′ DR.* (√½ ^ᴰ k))
    ≡⟨ DA.*-4 (emb w) (√½ ^ᴰ k) (emb w′) (√½ ^ᴰ k) ⟩
  (emb w DR.* emb w′) DR.* ((√½ ^ᴰ k) DR.* (√½ ^ᴰ k))
    ≡⟨ cong₂ DR._*_ (sym (emb-* w w′)) (sym (DA.^-*-distrib √½ √½ k)) ⟩
  emb (w ZR.* w′) DR.* (ε ^ᴰ k) ∎
  where open ≡-Reasoning

private
  emb-Σ : (f : Fin n → Z) → sum (λ x → emb (f x)) ≡ emb (Σᶻ f)
  emb-Σ {zero} f = refl
  emb-Σ {suc n} f = trans (cong (emb (f zero) DR.+_) (emb-Σ (f ∘ suc))) (sym (emb-+ (f zero) (Σᶻ (f ∘ suc))))

-- ⟨ w/√2ᵏ , w/√2ᵏ ⟩ = (Σₓ wₓ²) εᵏ.
ip-scV : ∀ k (w : Vec Z n) → ⟨ scV k w , scV k w ⟩ ≡ emb (Σᶻ (λ x → (w ! x) ZR.* (w ! x))) DR.* (ε ^ᴰ k)
ip-scV k w = begin
  sum (λ x → adjᴰ (scV k w ! x) DR.* (scV k w ! x))
    ≡⟨ sum-cong-≗ (λ x → cong (λ a → adjᴰ a DR.* a) (scV-! k w x)) ⟩
  sum (λ x → adjᴰ (sc k (w ! x)) DR.* sc k (w ! x))
    ≡⟨ sum-cong-≗ (λ x → adj-sc*sc k (w ! x) (w ! x)) ⟩
  sum (λ x → emb ((w ! x) ZR.* (w ! x)) DR.* (ε ^ᴰ k))
    ≡⟨ sym (*-distribʳ-sum (ε ^ᴰ k) (λ x → emb ((w ! x) ZR.* (w ! x)))) ⟩
  sum (λ x → emb ((w ! x) ZR.* (w ! x))) DR.* (ε ^ᴰ k)
    ≡⟨ cong (DR._* (ε ^ᴰ k)) (emb-Σ (λ x → (w ! x) ZR.* (w ! x))) ⟩
  emb (Σᶻ (λ x → (w ! x) ZR.* (w ! x))) DR.* (ε ^ᴰ k) ∎
  where open ≡-Reasoning

-- A unit vector w/√2ᵏ has Σₓ wₓ² = 2ᵏ.
unit-normᶻ : ∀ k (w : Vec Z n) → ⟨ scV k w , scV k w ⟩ ≡ DR.1# →
             Σᶻ (λ x → (w ! x) ZR.* (w ! x)) ≡ 2ᶻ ^ᶻ k
unit-normᶻ k w eq = emb-injective (begin
  emb S                                             ≡⟨ sym (DR.*-identityʳ (emb S)) ⟩
  emb S DR.* DR.1#                                  ≡⟨ cong (emb S DR.*_) (sym (DA.^-inverse ε (emb 2ᶻ) k ε*2)) ⟩
  emb S DR.* ((ε ^ᴰ k) DR.* (emb 2ᶻ ^ᴰ k))          ≡⟨ sym (DR.*-assoc (emb S) (ε ^ᴰ k) (emb 2ᶻ ^ᴰ k)) ⟩
  (emb S DR.* (ε ^ᴰ k)) DR.* (emb 2ᶻ ^ᴰ k)          ≡⟨ cong (DR._* (emb 2ᶻ ^ᴰ k)) (trans (sym (ip-scV k w)) eq) ⟩
  DR.1# DR.* (emb 2ᶻ ^ᴰ k)                          ≡⟨ DR.*-identityˡ (emb 2ᶻ ^ᴰ k) ⟩
  emb 2ᶻ ^ᴰ k                                       ≡⟨ sym (emb-^ 2ᶻ k) ⟩
  emb (2ᶻ ^ᶻ k)                                     ∎)
  where
  open ≡-Reasoning
  S = Σᶻ (λ x → (w ! x) ZR.* (w ! x))

private
  -- The coordinates of x + y √2.
  rcoord icoord : Z → ℤ
  rcoord (RootTwo a _) = a
  icoord (RootTwo _ b) = b

  rcoord-Σ : (f : Fin n → Z) → rcoord (Σᶻ f) ≡ Σℤ (rcoord ∘ f)
  rcoord-Σ {zero} f = refl
  rcoord-Σ {suc n} f = cong (λ z → rcoord (f zero) ℤ.+ z) (rcoord-Σ (f ∘ suc))

  icoord-Σ : (f : Fin n → Z) → icoord (Σᶻ f) ≡ Σℤ (icoord ∘ f)
  icoord-Σ {zero} f = refl
  icoord-Σ {suc n} f = cong (λ z → icoord (f zero) ℤ.+ z) (icoord-Σ (f ∘ suc))

  pos-Σ : (f : Fin n → ℕ) → + Σℕ f ≡ Σℤ (λ x → + f x)
  pos-Σ {zero} f = refl
  pos-Σ {suc n} f = trans (ℤP.pos-+ (f zero) (Σℕ (f ∘ suc))) (cong (λ z → + f zero ℤ.+ z) (pos-Σ (f ∘ suc)))

  Σℤ-cong : (f g : Fin n → ℤ) → (∀ x → f x ≡ g x) → Σℤ f ≡ Σℤ g
  Σℤ-cong {zero} f g eq = refl
  Σℤ-cong {suc n} f g eq = cong₂ ℤ._+_ (eq zero) (Σℤ-cong (f ∘ suc) (g ∘ suc) (eq ∘ suc))

  Σℤ-double : (f : Fin n → ℤ) → Σℤ (λ x → f x ℤ.+ f x) ≡ Σℤ f ℤ.+ Σℤ f
  Σℤ-double {zero} f = refl
  Σℤ-double {suc n} f = trans (cong (λ z → (f zero ℤ.+ f zero) ℤ.+ z) (Σℤ-double (f ∘ suc)))
    (ℤS.solve 2 (λ a s → (a :+ a) :+ (s :+ s) := (a :+ s) :+ (a :+ s)) refl (f zero) (Σℤ (f ∘ suc)))
    where open ℤS using (_:+_ ; _:=_)

  half0 : ∀ x → x ℤ.+ x ≡ + 0 → x ≡ + 0
  half0 x e = ℤP.*-cancelˡ-≡ (+ 2) x (+ 0) (trans (ℤS.solve 1 (λ x → con (+ 2) :* x := x :+ x) refl x) e)
    where open ℤS using (_:+_ ; _:*_ ; _:=_ ; con)

-- Σₓ Aₓ = 2ᵏ.
unit-norm : ∀ k (w : Vec Z n) → ⟨ scV k w , scV k w ⟩ ≡ DR.1# → Σℕ (λ x → NA (w ! x)) ≡ 2 ℕ.^ k
unit-norm k w eq = ℤP.+-injective (begin
  + Σℕ (λ x → NA (w ! x))                                ≡⟨ pos-Σ (λ x → NA (w ! x)) ⟩
  Σℤ (λ x → + NA (w ! x))                                ≡⟨ Σℤ-cong _ _ (λ x → cong rcoord (sym (sq-mul (w ! x)))) ⟩
  Σℤ (λ x → rcoord ((w ! x) ZR.* (w ! x)))               ≡⟨ sym (rcoord-Σ (λ x → (w ! x) ZR.* (w ! x))) ⟩
  rcoord (Σᶻ (λ x → (w ! x) ZR.* (w ! x)))               ≡⟨ cong rcoord (trans (unit-normᶻ k w eq) (2^ᶻ k)) ⟩
  + (2 ℕ.^ k)                                            ∎)
  where open ≡-Reasoning

-- Σₓ Bₓ = 0.
unit-normB : ∀ k (w : Vec Z n) → ⟨ scV k w , scV k w ⟩ ≡ DR.1# → Σℤ (λ x → NB (w ! x)) ≡ + 0
unit-normB k w eq = half0 _ (begin
  Σℤ (λ x → NB (w ! x)) ℤ.+ Σℤ (λ x → NB (w ! x))        ≡⟨ sym (Σℤ-double (λ x → NB (w ! x))) ⟩
  Σℤ (λ x → NB (w ! x) ℤ.+ NB (w ! x))                   ≡⟨ Σℤ-cong _ _ (λ x → cong icoord (sym (sq-mul (w ! x)))) ⟩
  Σℤ (λ x → icoord ((w ! x) ZR.* (w ! x)))               ≡⟨ sym (icoord-Σ (λ x → (w ! x) ZR.* (w ! x))) ⟩
  icoord (Σᶻ (λ x → (w ! x) ZR.* (w ! x)))               ≡⟨ cong icoord (trans (unit-normᶻ k w eq) (2^ᶻ k)) ⟩
  + 0                                                    ∎)
  where open ≡-Reasoning
