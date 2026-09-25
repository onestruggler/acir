------------------------------------------------------------------------
-- Presentations of groups
--
-- Unit vectors (Lemmas 2.9 and 2.10).  For w = aω³ + bω² + cω + d in
-- ℤ[ω],
--
--   w† w = A + B √2,   A = a² + b² + c² + d²,   B = ab + bc + cd - ad,
--
-- and A ≡ a + b + c + d (mod 2) is odd iff w is.  A column of a
-- column-orthonormal matrix has ⟨ v , v ⟩ = 1; writing v = w / δᵏ, as
-- δ† δ = 2 + √2 this says Σₓ wₓ† wₓ = (2 + √2)ᵏ = Pₖ + Qₖ √2, so
-- Σₓ Aₓ = Pₖ and Σₓ Bₓ = Qₖ.  Since P₀ = 1 and Pₖ is even for k > 0:
--
-- * "evenodd": if k > 0, an even number of the wₓ are odd;
-- * "lde0": if k = 0, exactly one wₓ is nonzero, and it is a power
--   of ω.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Norm where

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

open import Quantum.Synthesis.Ring using (Omega)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Scale
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Lde
  using (_!_ ; scV ; scV-! ; Odd ; Even)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics
  hiding (_!_)

private
  variable
    n : ℕ
  module ℤS = ℤSolver.+-*-Solver
  module Adjᴰ = IsInvolutiveRingEndo {{ring-D}} adj-D

  cong₄ : ∀ {A B C E F : Set} (f : A → B → C → E → F) {a a′ b b′ c c′ e e′} →
          a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ → f a b c e ≡ f a′ b′ c′ e′
  cong₄ f refl refl refl refl = refl

------------------------------------------------------------------------
-- Norms in ℤ[ω]

-- The complex conjugate: ω† = ω⁷ = -ω³, (ω²)† = -ω², (ω³)† = -ω.
conjᶻ : Z → Z
conjᶻ (Omega a b c d) = Omega (ℤ.- c) (ℤ.- b) (ℤ.- a) d

-- x + y √2, with √2 = ω - ω³.
re2 : ℤ → ℤ → Z
re2 x y = Omega (ℤ.- y) (+ 0) y x

sq : ℤ → ℕ
sq a = ∣ a ∣ ℕ.* ∣ a ∣

-- A = a² + b² + c² + d² and B = ab + bc + cd - ad.
NA : Z → ℕ
NA (Omega a b c d) = sq a ℕ.+ (sq b ℕ.+ (sq c ℕ.+ (sq d ℕ.+ 0)))

NB : Z → ℤ
NB (Omega a b c d) = a ℤ.* b ℤ.+ b ℤ.* c ℤ.+ c ℤ.* d ℤ.- a ℤ.* d

private
  sq-abs : ∀ a → a ℤ.* a ≡ + sq a
  sq-abs (+ n) = sym (ℤP.pos-* n n)
  sq-abs -[1+ n ] = refl

-- w† w = A + B √2.
adj-mul : ∀ w → conjᶻ w ZR.* w ≡ re2 (+ NA w) (NB w)
adj-mul (Omega a b c d) = cong₄ Omega ea eb ec ed
  where
  open ℤS using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)
  ea : (ℤ.- c) ℤ.* d ℤ.+ (ℤ.- b) ℤ.* c ℤ.+ (ℤ.- a) ℤ.* b ℤ.+ d ℤ.* a ≡ ℤ.- NB (Omega a b c d)
  ea = ℤS.solve 4 (λ a b c d → (:- c) :* d :+ (:- b) :* c :+ (:- a) :* b :+ d :* a
                               := :- (a :* b :+ b :* c :+ c :* d :- a :* d)) refl a b c d
  eb : (ℤ.- b) ℤ.* d ℤ.+ (ℤ.- a) ℤ.* c ℤ.+ d ℤ.* b ℤ.+ ℤ.- ((ℤ.- c) ℤ.* a) ≡ + 0
  eb = ℤS.solve 4 (λ a b c d → (:- b) :* d :+ (:- a) :* c :+ d :* b :+ :- ((:- c) :* a) := con (+ 0)) refl a b c d
  ec : (ℤ.- a) ℤ.* d ℤ.+ d ℤ.* c ℤ.+ ℤ.- ((ℤ.- c) ℤ.* b) ℤ.+ ℤ.- ((ℤ.- b) ℤ.* a) ≡ NB (Omega a b c d)
  ec = ℤS.solve 4 (λ a b c d → (:- a) :* d :+ d :* c :+ :- ((:- c) :* b) :+ :- ((:- b) :* a)
                               := a :* b :+ b :* c :+ c :* d :- a :* d) refl a b c d
  ed : d ℤ.* d ℤ.+ ℤ.- ((ℤ.- c) ℤ.* c) ℤ.+ ℤ.- ((ℤ.- b) ℤ.* b) ℤ.+ ℤ.- ((ℤ.- a) ℤ.* a) ≡ + NA (Omega a b c d)
  ed = begin
    d ℤ.* d ℤ.+ ℤ.- ((ℤ.- c) ℤ.* c) ℤ.+ ℤ.- ((ℤ.- b) ℤ.* b) ℤ.+ ℤ.- ((ℤ.- a) ℤ.* a)
      ≡⟨ ℤS.solve 4 (λ a b c d → d :* d :+ :- ((:- c) :* c) :+ :- ((:- b) :* b) :+ :- ((:- a) :* a)
                                 := a :* a :+ (b :* b :+ (c :* c :+ (d :* d :+ con (+ 0))))) refl a b c d ⟩
    a ℤ.* a ℤ.+ (b ℤ.* b ℤ.+ (c ℤ.* c ℤ.+ (d ℤ.* d ℤ.+ + 0)))
      ≡⟨ cong₄ (λ x y z t → x ℤ.+ (y ℤ.+ (z ℤ.+ (t ℤ.+ + 0)))) (sq-abs a) (sq-abs b) (sq-abs c) (sq-abs d) ⟩
    + sq a ℤ.+ (+ sq b ℤ.+ (+ sq c ℤ.+ (+ sq d ℤ.+ + 0)))
      ≡⟨ sym (trans (ℤP.pos-+ (sq a) _) (cong (λ z → + sq a ℤ.+ z) (trans (ℤP.pos-+ (sq b) _)
               (cong (λ z → + sq b ℤ.+ z) (ℤP.pos-+ (sq c) _))))) ⟩
    + NA (Omega a b c d)
      ∎
    where open ≡-Reasoning

private
  xor-false : ∀ b → b xor false ≡ b
  xor-false true  = refl
  xor-false false = refl

  xor-assoc : ∀ p q r → (p xor q) xor r ≡ p xor (q xor r)
  xor-assoc true  true  r = sym (trans (cong (true xor_) (xor-true r)) (not-not r))
    where
    xor-true : ∀ r → true xor r ≡ Data.Bool.Base.not r
    xor-true r = refl
    not-not : ∀ r → true xor Data.Bool.Base.not r ≡ r
    not-not true  = refl
    not-not false = refl
  xor-assoc true  false r = refl
  xor-assoc false q     r = refl

-- A is odd iff w is.
oddℕ-NA : ∀ w → oddℕ (NA w) ≡ oddᶻ w
oddℕ-NA (Omega a b c d) = begin
  oddℕ (sq a ℕ.+ (sq b ℕ.+ (sq c ℕ.+ (sq d ℕ.+ 0))))
    ≡⟨ oddℕ-+ (sq a) _ ⟩
  oddℕ (sq a) xor oddℕ (sq b ℕ.+ (sq c ℕ.+ (sq d ℕ.+ 0)))
    ≡⟨ cong (oddℕ (sq a) xor_) (trans (oddℕ-+ (sq b) _) (cong (oddℕ (sq b) xor_) (trans (oddℕ-+ (sq c) _)
         (cong (oddℕ (sq c) xor_) (trans (oddℕ-+ (sq d) 0) (xor-false (oddℕ (sq d)))))))) ⟩
  oddℕ (sq a) xor (oddℕ (sq b) xor (oddℕ (sq c) xor oddℕ (sq d)))
    ≡⟨ cong₄ (λ x y z t → x xor (y xor (z xor t))) (sq-odd a) (sq-odd b) (sq-odd c) (sq-odd d) ⟩
  oddℤ a xor (oddℤ b xor (oddℤ c xor oddℤ d))
    ≡⟨ sym (trans (xor-assoc (oddℤ a xor oddℤ b) (oddℤ c) (oddℤ d)) (xor-assoc (oddℤ a) (oddℤ b) _)) ⟩
  ((oddℤ a xor oddℤ b) xor oddℤ c) xor oddℤ d
    ≡⟨ sym (trans (oddℤ-+ (a ℤ.+ b ℤ.+ c) d) (cong (_xor oddℤ d) (trans (oddℤ-+ (a ℤ.+ b) c)
             (cong (_xor oddℤ c) (oddℤ-+ a b))))) ⟩
  oddℤ (a ℤ.+ b ℤ.+ c ℤ.+ d) ∎
  where
  open ≡-Reasoning
  sq-odd : ∀ x → oddℕ (sq x) ≡ oddℤ x
  sq-odd x = trans (oddℕ-* ∣ x ∣ ∣ x ∣) (∧-idem (oddℕ ∣ x ∣))
    where
    ∧-idem : ∀ b → b ∧ b ≡ b
    ∧-idem true  = refl
    ∧-idem false = refl

------------------------------------------------------------------------
-- Units

-- The units of norm 1 are the powers of ω.
Unit : Z → Set
Unit u = ∃ λ t → t ℕ.< 8 × u ≡ ωᶻ ^ᶻ t

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

  -- The squares of the coordinates.
  coords : Z → Fin 4 → ℕ
  coords (Omega a b c d) zero = sq a
  coords (Omega a b c d) (suc zero) = sq b
  coords (Omega a b c d) (suc (suc zero)) = sq c
  coords (Omega a b c d) (suc (suc (suc zero))) = sq d

  NA≡0 : ∀ w → NA w ≡ 0 → w ≡ ZR.0#
  NA≡0 w@(Omega a b c d) eq =
    cong₄ Omega (sq0 a (z zero)) (sq0 b (z (suc zero))) (sq0 c (z (suc (suc zero)))) (sq0 d (z (suc (suc (suc zero)))))
    where
    z = Σℕ≡0 (coords w) eq

  -- A single coordinate ±1, the others 0.
  NA≡1 : ∀ w → NA w ≡ 1 → Unit w
  NA≡1 w@(Omega a b c d) eq with Σℕ≡1 (coords w) eq
  ... | zero , e , rest with sq1 a e
  ...   | inj₁ refl = 3 , ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))) ,
                      cong₄ Omega refl (sq0 b (rest (suc zero) λ ())) (sq0 c (rest (suc (suc zero)) λ ()))
                                       (sq0 d (rest (suc (suc (suc zero))) λ ()))
  ...   | inj₂ refl = 7 , ℕP.≤-refl ,
                      cong₄ Omega refl (sq0 b (rest (suc zero) λ ())) (sq0 c (rest (suc (suc zero)) λ ()))
                                       (sq0 d (rest (suc (suc (suc zero))) λ ()))
  NA≡1 w@(Omega a b c d) eq | suc zero , e , rest with sq1 b e
  ...   | inj₁ refl = 2 , ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) ,
                      cong₄ Omega (sq0 a (rest zero λ ())) refl (sq0 c (rest (suc (suc zero)) λ ()))
                                  (sq0 d (rest (suc (suc (suc zero))) λ ()))
  ...   | inj₂ refl = 6 , ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))))) ,
                      cong₄ Omega (sq0 a (rest zero λ ())) refl (sq0 c (rest (suc (suc zero)) λ ()))
                                  (sq0 d (rest (suc (suc (suc zero))) λ ()))
  NA≡1 w@(Omega a b c d) eq | suc (suc zero) , e , rest with sq1 c e
  ...   | inj₁ refl = 1 , ℕ.s≤s (ℕ.s≤s ℕ.z≤n) ,
                      cong₄ Omega (sq0 a (rest zero λ ())) (sq0 b (rest (suc zero) λ ())) refl
                                  (sq0 d (rest (suc (suc (suc zero))) λ ()))
  ...   | inj₂ refl = 5 , ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))))) ,
                      cong₄ Omega (sq0 a (rest zero λ ())) (sq0 b (rest (suc zero) λ ())) refl
                                  (sq0 d (rest (suc (suc (suc zero))) λ ()))
  NA≡1 w@(Omega a b c d) eq | suc (suc (suc zero)) , e , rest with sq1 d e
  ...   | inj₁ refl = 0 , ℕ.s≤s ℕ.z≤n ,
                      cong₄ Omega (sq0 a (rest zero λ ())) (sq0 b (rest (suc zero) λ ()))
                                  (sq0 c (rest (suc (suc zero)) λ ())) refl
  ...   | inj₂ refl = 4 , ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))) ,
                      cong₄ Omega (sq0 a (rest zero λ ())) (sq0 b (rest (suc zero) λ ()))
                                  (sq0 c (rest (suc (suc zero)) λ ())) refl

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

------------------------------------------------------------------------
-- (2 + √2)ᵏ = Pₖ + Qₖ √2

P Q : ℕ → ℤ
P zero = + 1
P (suc k) = + 2 ℤ.* (P k ℤ.+ Q k)
Q zero = + 0
Q (suc k) = P k ℤ.+ + 2 ℤ.* Q k

-- δ† δ = 2 + √2.
δ†δ : Z
δ†δ = conjᶻ δᶻ ZR.* δᶻ

δ†δ^ : ∀ k → δ†δ ^ᶻ k ≡ re2 (P k) (Q k)
δ†δ^ zero = refl
δ†δ^ (suc k) = trans (cong (δ†δ ZR.*_) (δ†δ^ k)) (cong₄ Omega ea eb ec ed)
  where
  open ℤS using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)
  p = P k
  q = Q k
  ea : -[1+ 0 ] ℤ.* p ℤ.+ + 0 ℤ.* q ℤ.+ + 1 ℤ.* + 0 ℤ.+ + 2 ℤ.* ℤ.- q ≡ ℤ.- (p ℤ.+ + 2 ℤ.* q)
  ea = ℤS.solve 2 (λ p q → con -[1+ 0 ] :* p :+ con (+ 0) :* q :+ con (+ 1) :* con (+ 0) :+ con (+ 2) :* (:- q)
                           := :- (p :+ con (+ 2) :* q)) refl p q
  eb : + 0 ℤ.* p ℤ.+ + 1 ℤ.* q ℤ.+ + 2 ℤ.* + 0 ℤ.+ ℤ.- (-[1+ 0 ] ℤ.* ℤ.- q) ≡ + 0
  eb = ℤS.solve 2 (λ p q → con (+ 0) :* p :+ con (+ 1) :* q :+ con (+ 2) :* con (+ 0) :+ :- (con -[1+ 0 ] :* (:- q))
                           := con (+ 0)) refl p q
  ec : + 1 ℤ.* p ℤ.+ + 2 ℤ.* q ℤ.+ ℤ.- (-[1+ 0 ] ℤ.* + 0) ℤ.+ ℤ.- (+ 0 ℤ.* ℤ.- q) ≡ p ℤ.+ + 2 ℤ.* q
  ec = ℤS.solve 2 (λ p q → con (+ 1) :* p :+ con (+ 2) :* q :+ :- (con -[1+ 0 ] :* con (+ 0)) :+ :- (con (+ 0) :* (:- q))
                           := p :+ con (+ 2) :* q) refl p q
  ed : + 2 ℤ.* p ℤ.+ ℤ.- (-[1+ 0 ] ℤ.* q) ℤ.+ ℤ.- (+ 0 ℤ.* + 0) ℤ.+ ℤ.- (+ 1 ℤ.* ℤ.- q) ≡ + 2 ℤ.* (p ℤ.+ q)
  ed = ℤS.solve 2 (λ p q → con (+ 2) :* p :+ :- (con -[1+ 0 ] :* q) :+ :- (con (+ 0) :* con (+ 0)) :+ :- (con (+ 1) :* (:- q))
                           := con (+ 2) :* (p :+ q)) refl p q

------------------------------------------------------------------------
-- The two lemmas

-- "evenodd": if Σₓ Aₓ = Pₖ with k > 0, an even number of wₓ are odd.
evenodd : ∀ k (w : Vec Z n) → + Σℕ (λ x → NA (w ! x)) ≡ P (suc k) →
          oddℕ (count (λ x → oddᶻ (w ! x))) ≡ false
evenodd k w eq = trans (sym (parity-count w)) (trans (cong oddℤ eq) (oddℤ-* (+ 2) (P k ℤ.+ Q k)))

-- "lde0": if Σₓ Aₓ = 1, a single wₓ is nonzero, and it is a unit.
lde0 : (w : Vec Z n) → + Σℕ (λ x → NA (w ! x)) ≡ + 1 →
       ∃ λ m → Unit (w ! m) × (∀ y → y ≢ m → w ! y ≡ ZR.0#)
lde0 w eq with Σℕ≡1 (λ x → NA (w ! x)) (ℤP.+-injective eq)
... | m , Nm , rest = m , NA≡1 (w ! m) Nm , λ y y≢m → NA≡0 (w ! y) (rest y y≢m)

------------------------------------------------------------------------
-- From ⟨ v , v ⟩ = 1 to Σₓ wₓ† wₓ = (δ† δ)ᵏ

private
  opaque
    unfolding adjᴰ

    adj-emb : ∀ z → adjᴰ (emb z) ≡ emb (conjᶻ z)
    adj-emb (Omega a b c d) = cong₄ Omega (sym (ι₀-neg c)) (sym (ι₀-neg b)) (sym (ι₀-neg a)) refl

  adj-^ : ∀ x k → adjᴰ (x ^ᴰ k) ≡ adjᴰ x ^ᴰ k
  adj-^ x zero = Adjᴰ.f-1
  adj-^ x (suc k) = trans (Adjᴰ.f-* x (x ^ᴰ k)) (cong (adjᴰ x DR.*_) (adj-^ x k))

  -- ε = 1 / (δ† δ).
  ε : D
  ε = adjᴰ δ⁻ DR.* δ⁻

  opaque
    unfolding _*ᴰ_ adjᴰ

    ε*δ†δ : ε DR.* emb δ†δ ≡ DR.1#
    ε*δ†δ = refl

-- (w/δᵏ)† w′/δᵏ = w† w′ εᵏ.
adj-sc*sc : ∀ k w w′ → adjᴰ (sc k w) DR.* sc k w′ ≡ emb (conjᶻ w ZR.* w′) DR.* (ε ^ᴰ k)
adj-sc*sc k w w′ = begin
  adjᴰ (sc k w) DR.* sc k w′
    ≡⟨ cong₂ (λ a b → adjᴰ a DR.* b) (sc-def k w) (sc-def k w′) ⟩
  adjᴰ (emb w DR.* (δ⁻ ^ᴰ k)) DR.* (emb w′ DR.* (δ⁻ ^ᴰ k))
    ≡⟨ cong (DR._* (emb w′ DR.* (δ⁻ ^ᴰ k))) (Adjᴰ.f-* (emb w) (δ⁻ ^ᴰ k)) ⟩
  (adjᴰ (emb w) DR.* adjᴰ (δ⁻ ^ᴰ k)) DR.* (emb w′ DR.* (δ⁻ ^ᴰ k))
    ≡⟨ cong₂ (λ a b → (a DR.* b) DR.* (emb w′ DR.* (δ⁻ ^ᴰ k))) (adj-emb w) (adj-^ δ⁻ k) ⟩
  (emb (conjᶻ w) DR.* (adjᴰ δ⁻ ^ᴰ k)) DR.* (emb w′ DR.* (δ⁻ ^ᴰ k))
    ≡⟨ DA.*-4 (emb (conjᶻ w)) (adjᴰ δ⁻ ^ᴰ k) (emb w′) (δ⁻ ^ᴰ k) ⟩
  (emb (conjᶻ w) DR.* emb w′) DR.* ((adjᴰ δ⁻ ^ᴰ k) DR.* (δ⁻ ^ᴰ k))
    ≡⟨ cong₂ DR._*_ (sym (emb-* (conjᶻ w) w′)) (sym (DA.^-*-distrib (adjᴰ δ⁻) δ⁻ k)) ⟩
  emb (conjᶻ w ZR.* w′) DR.* (ε ^ᴰ k) ∎
  where open ≡-Reasoning

private
  emb-Σ : (f : Fin n → Z) → sum (λ x → emb (f x)) ≡ emb (Σᶻ f)
  emb-Σ {zero} f = refl
  emb-Σ {suc n} f = trans (cong (emb (f zero) DR.+_) (emb-Σ (f ∘ suc))) (sym (emb-+ (f zero) (Σᶻ (f ∘ suc))))

-- ⟨ w/δᵏ , w/δᵏ ⟩ = (Σₓ wₓ† wₓ) εᵏ.
ip-scV : ∀ k (w : Vec Z n) → ⟨ scV k w , scV k w ⟩ ≡ emb (Σᶻ (λ x → conjᶻ (w ! x) ZR.* (w ! x))) DR.* (ε ^ᴰ k)
ip-scV k w = begin
  sum (λ x → adjᴰ (scV k w ! x) DR.* (scV k w ! x))
    ≡⟨ sum-cong-≗ (λ x → cong (λ a → adjᴰ a DR.* a) (scV-! k w x)) ⟩
  sum (λ x → adjᴰ (sc k (w ! x)) DR.* sc k (w ! x))
    ≡⟨ sum-cong-≗ (λ x → adj-sc*sc k (w ! x) (w ! x)) ⟩
  sum (λ x → emb (conjᶻ (w ! x) ZR.* (w ! x)) DR.* (ε ^ᴰ k))
    ≡⟨ sym (*-distribʳ-sum (ε ^ᴰ k) (λ x → emb (conjᶻ (w ! x) ZR.* (w ! x)))) ⟩
  sum (λ x → emb (conjᶻ (w ! x) ZR.* (w ! x))) DR.* (ε ^ᴰ k)
    ≡⟨ cong (DR._* (ε ^ᴰ k)) (emb-Σ (λ x → conjᶻ (w ! x) ZR.* (w ! x))) ⟩
  emb (Σᶻ (λ x → conjᶻ (w ! x) ZR.* (w ! x))) DR.* (ε ^ᴰ k) ∎
  where open ≡-Reasoning

-- A unit vector w/δᵏ has Σₓ wₓ† wₓ = (δ† δ)ᵏ.
unit-normᶻ : ∀ k (w : Vec Z n) → ⟨ scV k w , scV k w ⟩ ≡ DR.1# →
             Σᶻ (λ x → conjᶻ (w ! x) ZR.* (w ! x)) ≡ δ†δ ^ᶻ k
unit-normᶻ k w eq = emb-injective (begin
  emb S                                             ≡⟨ sym (DR.*-identityʳ (emb S)) ⟩
  emb S DR.* DR.1#                                  ≡⟨ cong (emb S DR.*_) (sym (DA.^-inverse ε (emb δ†δ) k ε*δ†δ)) ⟩
  emb S DR.* ((ε ^ᴰ k) DR.* (emb δ†δ ^ᴰ k))         ≡⟨ sym (DR.*-assoc (emb S) (ε ^ᴰ k) (emb δ†δ ^ᴰ k)) ⟩
  (emb S DR.* (ε ^ᴰ k)) DR.* (emb δ†δ ^ᴰ k)         ≡⟨ cong (DR._* (emb δ†δ ^ᴰ k)) (trans (sym (ip-scV k w)) eq) ⟩
  DR.1# DR.* (emb δ†δ ^ᴰ k)                         ≡⟨ DR.*-identityˡ (emb δ†δ ^ᴰ k) ⟩
  emb δ†δ ^ᴰ k                                      ≡⟨ sym (emb-^ δ†δ k) ⟩
  emb (δ†δ ^ᶻ k)                                    ∎)
  where
  open ≡-Reasoning
  S = Σᶻ (λ x → conjᶻ (w ! x) ZR.* (w ! x))

private
  -- The coordinates of x + y √2.
  dcoord ccoord : Z → ℤ
  dcoord (Omega _ _ _ d) = d
  ccoord (Omega _ _ c _) = c

  dcoord-Σ : (f : Fin n → Z) → dcoord (Σᶻ f) ≡ Σℤ (dcoord ∘ f)
  dcoord-Σ {zero} f = refl
  dcoord-Σ {suc n} f = cong (λ z → dcoord (f zero) ℤ.+ z) (dcoord-Σ (f ∘ suc))

  ccoord-Σ : (f : Fin n → Z) → ccoord (Σᶻ f) ≡ Σℤ (ccoord ∘ f)
  ccoord-Σ {zero} f = refl
  ccoord-Σ {suc n} f = cong (λ z → ccoord (f zero) ℤ.+ z) (ccoord-Σ (f ∘ suc))

  pos-Σ : (f : Fin n → ℕ) → + Σℕ f ≡ Σℤ (λ x → + f x)
  pos-Σ {zero} f = refl
  pos-Σ {suc n} f = trans (ℤP.pos-+ (f zero) (Σℕ (f ∘ suc))) (cong (λ z → + f zero ℤ.+ z) (pos-Σ (f ∘ suc)))

  Σℤ-cong : (f g : Fin n → ℤ) → (∀ x → f x ≡ g x) → Σℤ f ≡ Σℤ g
  Σℤ-cong {zero} f g eq = refl
  Σℤ-cong {suc n} f g eq = cong₂ ℤ._+_ (eq zero) (Σℤ-cong (f ∘ suc) (g ∘ suc) (eq ∘ suc))

-- Σₓ Aₓ = Pₖ.
unit-norm : ∀ k (w : Vec Z n) → ⟨ scV k w , scV k w ⟩ ≡ DR.1# → + Σℕ (λ x → NA (w ! x)) ≡ P k
unit-norm k w eq = begin
  + Σℕ (λ x → NA (w ! x))                                ≡⟨ pos-Σ (λ x → NA (w ! x)) ⟩
  Σℤ (λ x → + NA (w ! x))                                ≡⟨ Σℤ-cong _ _ (λ x → cong dcoord (sym (adj-mul (w ! x)))) ⟩
  Σℤ (λ x → dcoord (conjᶻ (w ! x) ZR.* (w ! x)))         ≡⟨ sym (dcoord-Σ (λ x → conjᶻ (w ! x) ZR.* (w ! x))) ⟩
  dcoord (Σᶻ (λ x → conjᶻ (w ! x) ZR.* (w ! x)))         ≡⟨ cong dcoord (trans (unit-normᶻ k w eq) (δ†δ^ k)) ⟩
  P k                                                    ∎
  where open ≡-Reasoning

-- Σₓ Bₓ = Qₖ.
unit-normB : ∀ k (w : Vec Z n) → ⟨ scV k w , scV k w ⟩ ≡ DR.1# → Σℤ (λ x → NB (w ! x)) ≡ Q k
unit-normB k w eq = begin
  Σℤ (λ x → NB (w ! x))                                  ≡⟨ Σℤ-cong _ _ (λ x → cong ccoord (sym (adj-mul (w ! x)))) ⟩
  Σℤ (λ x → ccoord (conjᶻ (w ! x) ZR.* (w ! x)))         ≡⟨ sym (ccoord-Σ (λ x → conjᶻ (w ! x) ZR.* (w ! x))) ⟩
  ccoord (Σᶻ (λ x → conjᶻ (w ! x) ZR.* (w ! x)))         ≡⟨ cong ccoord (trans (unit-normᶻ k w eq) (δ†δ^ k)) ⟩
  Q k                                                    ∎
  where open ≡-Reasoning
