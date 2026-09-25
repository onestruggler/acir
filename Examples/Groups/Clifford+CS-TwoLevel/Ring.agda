------------------------------------------------------------------------
-- Presentations of groups
--
-- The rings of Bian–Selinger, "Generators and relations for
-- Uₙ(ℤ[½,i])" (QPL 2021): the Gaussian integers ℤ[i] ⊆ 𝔻[i] = ℤ[½,i],
-- taken from EucDomain (ZComplex, DComplex), the prime γ = 1 + i, and
-- parity, i.e. divisibility by γ (Definition "even/odd" of §2.1).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Ring where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_ ; _∧_)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_] ; ∣_∣)
import Data.Integer.Properties as ℤP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
import Data.Integer.Solver as ℤSolver
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

open import Instances using (SemiRing ; Ring)
open import Quantum.Synthesis.Ring
  using (Dyadic ; Dyadic' ; _[i] ; Cplx ; DComplex ; ZComplex ; dyadic ; shiftL ; pow2
        ; SemiRingDyadic ; RingDyadic ; SemiRingCplx ; RingCplx)
open import Quantum.Synthesis.Ring.Properties
  using (commutativeRing-𝔻 ; commutativeRing-DComplex ; commutativeRing-ZComplex ; shiftL≡)
import Quantum.Synthesis.Ring.Properties.Common as Common
import Examples.Groups.Clifford+CS-TwoLevel.Algebra as Algebra

------------------------------------------------------------------------
-- The two rings

-- 𝔻[i] = ℤ[½,i], the ring of the matrix entries.
D : Set
D = DComplex

-- ℤ[i], the Gaussian integers.
Z : Set
Z = ZComplex

-- Their ring structures, with the operations of EucDomain's instances
-- (so that terms built by EucDomain, e.g. by its matrix product, are
-- definitionally terms of these rings).
module 𝔻R = CommutativeRing commutativeRing-𝔻
module DR = CommutativeRing commutativeRing-DComplex
module ZR = CommutativeRing commutativeRing-ZComplex

-- Ring solvers with integer coefficients.
module DS = Common.ZSolver commutativeRing-DComplex
module ZS = Common.ZSolver commutativeRing-ZComplex

-- Identities in 𝔻[i], proved over an abstract ring (see Algebra).
module DA = Algebra commutativeRing-DComplex (λ p → p)

private
  module ℤS = ℤSolver.+-*-Solver

------------------------------------------------------------------------
-- Constants

-- The imaginary unit, in both rings.
ⅈ : D
ⅈ = Cplx (Dyadic' (+ 0) 0 _) (Dyadic' (+ 1) 0 _)

ⅈᶻ : Z
ⅈᶻ = Cplx (+ 0) (+ 1)

-- γ = 1 + i, its inverse γ⁻ = (1 - i)/2 in 𝔻[i], and ½.
γ γ⁻ ½ : D
γ = Cplx (Dyadic' (+ 1) 0 _) (Dyadic' (+ 1) 0 _)
γ⁻ = Cplx (Dyadic' (+ 1) 1 _) (Dyadic' -[1+ 0 ] 1 _)
½ = Cplx (Dyadic' (+ 1) 1 _) (Dyadic' (+ 0) 0 _)

γᶻ 2ᶻ : Z
γᶻ = Cplx (+ 1) (+ 1)
2ᶻ = Cplx (+ 2) (+ 0)

γ*γ⁻ : γ DR.* γ⁻ ≡ DR.1#
γ*γ⁻ = refl

γ⁻*γ : γ⁻ DR.* γ ≡ DR.1#
γ⁻*γ = refl

ⅈ*ⅈ : ⅈ DR.* ⅈ ≡ DR.- DR.1#
ⅈ*ⅈ = refl

------------------------------------------------------------------------
-- Powers
--
-- EucDomain's _^_ computes by repeated squaring; for reasoning we use
-- the naive power.

infixr 8 _^ᴰ_ _^ᶻ_

_^ᴰ_ : D → ℕ → D
_^ᴰ_ = DA._^_

_^ᶻ_ : Z → ℕ → Z
x ^ᶻ zero  = ZR.1#
x ^ᶻ suc k = x ZR.* (x ^ᶻ k)


^ᶻ-+ : ∀ x m n → x ^ᶻ (m ℕ.+ n) ≡ (x ^ᶻ m) ZR.* (x ^ᶻ n)
^ᶻ-+ x zero n = sym (ZR.*-identityˡ _)
^ᶻ-+ x (suc m) n = trans (cong (x ZR.*_) (^ᶻ-+ x m n)) (sym (ZR.*-assoc x (x ^ᶻ m) (x ^ᶻ n)))

------------------------------------------------------------------------
-- The embedding ℤ[i] → 𝔻[i]

-- Integers as dyadic fractions.
ι₀ : ℤ → Dyadic
ι₀ a = Dyadic' a 0 _

-- The smart constructor at exponent 0 is the plain constructor.
dyadic-0 : ∀ a → dyadic a 0 ≡ ι₀ a
dyadic-0 (+ zero)  = refl
dyadic-0 (+ suc n) = refl
dyadic-0 -[1+ n ]  = refl

shiftL-0 : ∀ a → shiftL a 0 ≡ a
shiftL-0 a = trans (shiftL≡ a 0) (ℤP.*-identityʳ a)

ι₀-+ : ∀ a b → ι₀ (a ℤ.+ b) ≡ ι₀ a 𝔻R.+ ι₀ b
ι₀-+ a b = sym (trans (dyadic-0 (shiftL a 0 ℤ.+ b))
                     (cong (λ z → ι₀ (z ℤ.+ b)) (shiftL-0 a)))

ι₀-* : ∀ a b → ι₀ (a ℤ.* b) ≡ ι₀ a 𝔻R.* ι₀ b
ι₀-* a b = sym (dyadic-0 (a ℤ.* b))

ι₀-neg : ∀ a → ι₀ (ℤ.- a) ≡ 𝔻R.- ι₀ a
ι₀-neg a = sym (dyadic-0 (ℤ.- a))

ι₀-injective : ∀ {a b} → ι₀ a ≡ ι₀ b → a ≡ b
ι₀-injective refl = refl

-- Gaussian integers as Gaussian dyadic fractions.
emb : Z → D
emb (Cplx a b) = Cplx (ι₀ a) (ι₀ b)

emb-injective : ∀ {x y} → emb x ≡ emb y → x ≡ y
emb-injective {Cplx a b} {Cplx c d} eq =
  cong₂ Cplx (ι₀-injective (cong re eq)) (ι₀-injective (cong im eq))
  where
  re im : D → Dyadic
  re (Cplx u _) = u
  im (Cplx _ v) = v

emb-+ : ∀ x y → emb (x ZR.+ y) ≡ emb x DR.+ emb y
emb-+ (Cplx a b) (Cplx c d) = cong₂ Cplx (ι₀-+ a c) (ι₀-+ b d)

emb-neg : ∀ x → emb (ZR.- x) ≡ DR.- emb x
emb-neg (Cplx a b) = cong₂ Cplx (ι₀-neg a) (ι₀-neg b)

emb-* : ∀ x y → emb (x ZR.* y) ≡ emb x DR.* emb y
emb-* (Cplx a b) (Cplx c d) = cong₂ Cplx
  (trans (ι₀-+ (a ℤ.* c) (ℤ.- (b ℤ.* d)))
         (cong₂ 𝔻R._+_ (ι₀-* a c) (trans (ι₀-neg (b ℤ.* d)) (cong 𝔻R.-_ (ι₀-* b d)))))
  (trans (ι₀-+ (a ℤ.* d) (b ℤ.* c)) (cong₂ 𝔻R._+_ (ι₀-* a d) (ι₀-* b c)))

emb-0 : emb ZR.0# ≡ DR.0#
emb-0 = refl

emb-1 : emb ZR.1# ≡ DR.1#
emb-1 = refl

emb-ⅈ : emb ⅈᶻ ≡ ⅈ
emb-ⅈ = refl

emb-γ : emb γᶻ ≡ γ
emb-γ = refl

emb-^ : ∀ x k → emb (x ^ᶻ k) ≡ emb x ^ᴰ k
emb-^ x zero = refl
emb-^ x (suc k) = trans (emb-* x (x ^ᶻ k)) (cong (emb x DR.*_) (emb-^ x k))

------------------------------------------------------------------------
-- Parity of natural numbers and integers

oddℕ : ℕ → Bool
oddℕ zero    = false
oddℕ (suc n) = not (oddℕ n)

private
  not-xor : ∀ a b → not (a xor b) ≡ not a xor b
  not-xor true  true  = refl
  not-xor true  false = refl
  not-xor false b     = refl

  xor-∧ : ∀ a b → b xor (a ∧ b) ≡ not a ∧ b
  xor-∧ true  true  = refl
  xor-∧ true  false = refl
  xor-∧ false true  = refl
  xor-∧ false false = refl

  xor-cancelʳ : ∀ a b → (a xor b) xor b ≡ a
  xor-cancelʳ true  true  = refl
  xor-cancelʳ true  false = refl
  xor-cancelʳ false true  = refl
  xor-cancelʳ false false = refl

  xor-comm : ∀ a b → a xor b ≡ b xor a
  xor-comm true  true  = refl
  xor-comm true  false = refl
  xor-comm false true  = refl
  xor-comm false false = refl

oddℕ-+ : ∀ m n → oddℕ (m ℕ.+ n) ≡ oddℕ m xor oddℕ n
oddℕ-+ zero n = refl
oddℕ-+ (suc m) n = trans (cong not (oddℕ-+ m n)) (not-xor (oddℕ m) (oddℕ n))

oddℕ-* : ∀ m n → oddℕ (m ℕ.* n) ≡ oddℕ m ∧ oddℕ n
oddℕ-* zero n = refl
oddℕ-* (suc m) n = begin
  oddℕ (n ℕ.+ m ℕ.* n)            ≡⟨ oddℕ-+ n (m ℕ.* n) ⟩
  oddℕ n xor oddℕ (m ℕ.* n)       ≡⟨ cong (oddℕ n xor_) (oddℕ-* m n) ⟩
  oddℕ n xor (oddℕ m ∧ oddℕ n)    ≡⟨ xor-∧ (oddℕ m) (oddℕ n) ⟩
  not (oddℕ m) ∧ oddℕ n           ∎
  where open ≡-Reasoning

-- m ∸ n and n + (m ∸ n) have the parities one expects.
oddℕ-∸ : ∀ m n → n ℕ.≤ m → oddℕ (m ℕ.∸ n) ≡ oddℕ m xor oddℕ n
oddℕ-∸ m n n≤m = begin
  oddℕ (m ℕ.∸ n)                          ≡⟨ sym (xor-cancelʳ _ (oddℕ n)) ⟩
  (oddℕ (m ℕ.∸ n) xor oddℕ n) xor oddℕ n  ≡⟨ cong (_xor oddℕ n) (sym (oddℕ-+ (m ℕ.∸ n) n)) ⟩
  oddℕ (m ℕ.∸ n ℕ.+ n) xor oddℕ n         ≡⟨ cong (λ k → oddℕ k xor oddℕ n) (ℕP.m∸n+n≡m n≤m) ⟩
  oddℕ m xor oddℕ n                       ∎
  where open ≡-Reasoning

oddℤ : ℤ → Bool
oddℤ x = oddℕ ∣ x ∣

oddℤ-neg : ∀ x → oddℤ (ℤ.- x) ≡ oddℤ x
oddℤ-neg x = cong oddℕ (ℤP.∣-i∣≡∣i∣ x)

oddℤ-* : ∀ x y → oddℤ (x ℤ.* y) ≡ oddℤ x ∧ oddℤ y
oddℤ-* x y = trans (cong oddℕ (ℤP.abs-* x y)) (oddℕ-* ∣ x ∣ ∣ y ∣)

private
  odd-⊖ : ∀ m n → oddℕ ∣ m ℤ.⊖ n ∣ ≡ oddℕ m xor oddℕ n
  odd-⊖ m n with ℕP.≤-total n m
  ... | inj₁ n≤m = trans (cong (λ z → oddℕ ∣ z ∣) (ℤP.⊖-≥ n≤m)) (oddℕ-∸ m n n≤m)
  ... | inj₂ m≤n = trans (cong oddℕ (ℤP.∣⊖∣-≤ m≤n))
                         (trans (oddℕ-∸ n m m≤n) (xor-comm (oddℕ n) (oddℕ m)))

oddℤ-+ : ∀ x y → oddℤ (x ℤ.+ y) ≡ oddℤ x xor oddℤ y
oddℤ-+ (+ m) (+ n) = oddℕ-+ m n
oddℤ-+ (+ m) -[1+ n ] = odd-⊖ m (suc n)
oddℤ-+ -[1+ m ] (+ n) = trans (odd-⊖ n (suc m)) (xor-comm (oddℕ n) (oddℕ (suc m)))
oddℤ-+ -[1+ m ] -[1+ n ] = begin
  not (not (oddℕ (m ℕ.+ n)))            ≡⟨ cong (λ b → not (not b)) (oddℕ-+ m n) ⟩
  not (not (oddℕ m xor oddℕ n))         ≡⟨ cong not (not-xor (oddℕ m) (oddℕ n)) ⟩
  not (not (oddℕ m) xor oddℕ n)         ≡⟨ sym (lemma (oddℕ m) (oddℕ n)) ⟩
  not (oddℕ m) xor not (oddℕ n)         ∎
  where
  open ≡-Reasoning
  lemma : ∀ a b → not a xor not b ≡ not (not a xor b)
  lemma true  true  = refl
  lemma true  false = refl
  lemma false true  = refl
  lemma false false = refl

-- Even integers are doubles.
evenℕ-half : ∀ n → oddℕ n ≡ false → ∃ λ m → n ≡ m ℕ.+ m
evenℕ-half n e = proj₁ (half n) e
  where
  half : ∀ n → (oddℕ n ≡ false → ∃ λ m → n ≡ m ℕ.+ m)
             × (oddℕ n ≡ true → ∃ λ m → n ≡ suc (m ℕ.+ m))
  half zero = (λ _ → 0 , refl) , λ ()
  half (suc n) with oddℕ n in eq
  ... | true  = (λ _ → let (m , p) = proj₂ (half n) eq
                       in suc m , cong suc (trans p (sym (ℕP.+-suc m m))))
              , λ ()
  ... | false = (λ ()) , (λ _ → let (m , p) = proj₁ (half n) eq in m , cong suc p)

evenℤ-half : ∀ x → oddℤ x ≡ false → ∃ λ y → x ≡ y ℤ.+ y
evenℤ-half (+ n) e = let (m , p) = evenℕ-half n e in + m , cong +_ p
evenℤ-half -[1+ n ] e =
  let (m , p) = evenℕ-half (suc n) e in
  ℤ.- (+ m) , (begin
    -[1+ n ]                     ≡⟨⟩
    ℤ.- (+ suc n)                ≡⟨ cong (λ k → ℤ.- (+ k)) p ⟩
    ℤ.- (+ (m ℕ.+ m))            ≡⟨ cong ℤ.-_ (ℤP.pos-+ m m) ⟩
    ℤ.- (+ m ℤ.+ + m)            ≡⟨ ℤP.neg-distrib-+ (+ m) (+ m) ⟩
    ℤ.- (+ m) ℤ.+ ℤ.- (+ m)      ∎)
  where open ≡-Reasoning

oddℤ-double : ∀ y → oddℤ (y ℤ.+ y) ≡ false
oddℤ-double y = trans (oddℤ-+ y y) (lemma (oddℤ y))
  where
  lemma : ∀ b → b xor b ≡ false
  lemma true  = refl
  lemma false = refl

------------------------------------------------------------------------
-- Parity of Gaussian integers

-- A Gaussian integer a + bi is odd iff a + b is odd, i.e. iff it is
-- not divisible by γ (Definition in §2.1).
oddᶻ : Z → Bool
oddᶻ (Cplx a b) = oddℤ (a ℤ.+ b)

-- Parity is a ring homomorphism ℤ[i] → 𝔽₂ (with xor as addition).
oddᶻ-+ : ∀ x y → oddᶻ (x ZR.+ y) ≡ oddᶻ x xor oddᶻ y
oddᶻ-+ (Cplx a b) (Cplx c d) = begin
  oddℤ ((a ℤ.+ c) ℤ.+ (b ℤ.+ d))        ≡⟨ cong oddℤ (lemma a b c d) ⟩
  oddℤ ((a ℤ.+ b) ℤ.+ (c ℤ.+ d))        ≡⟨ oddℤ-+ (a ℤ.+ b) (c ℤ.+ d) ⟩
  oddℤ (a ℤ.+ b) xor oddℤ (c ℤ.+ d)     ∎
  where
  open ≡-Reasoning
  lemma : ∀ a b c d → (a ℤ.+ c) ℤ.+ (b ℤ.+ d) ≡ (a ℤ.+ b) ℤ.+ (c ℤ.+ d)
  lemma = ℤS.solve 4 (λ a b c d → (a ℤS.:+ c) ℤS.:+ (b ℤS.:+ d) ℤS.:= (a ℤS.:+ b) ℤS.:+ (c ℤS.:+ d)) refl

oddᶻ-neg : ∀ x → oddᶻ (ZR.- x) ≡ oddᶻ x
oddᶻ-neg (Cplx a b) = trans (cong oddℤ (sym (ℤP.neg-distrib-+ a b))) (oddℤ-neg (a ℤ.+ b))

oddᶻ-* : ∀ x y → oddᶻ (x ZR.* y) ≡ oddᶻ x ∧ oddᶻ y
oddᶻ-* (Cplx a b) (Cplx c d) = begin
  oddℤ ((a ℤ.* c ℤ.+ ℤ.- (b ℤ.* d)) ℤ.+ (a ℤ.* d ℤ.+ b ℤ.* c))
    ≡⟨ cong oddℤ (lemma a b c d) ⟩
  oddℤ ((a ℤ.+ b) ℤ.* (c ℤ.+ d) ℤ.+ ((ℤ.- (b ℤ.* d)) ℤ.+ (ℤ.- (b ℤ.* d))))
    ≡⟨ oddℤ-+ ((a ℤ.+ b) ℤ.* (c ℤ.+ d)) _ ⟩
  oddℤ ((a ℤ.+ b) ℤ.* (c ℤ.+ d)) xor oddℤ ((ℤ.- (b ℤ.* d)) ℤ.+ (ℤ.- (b ℤ.* d)))
    ≡⟨ cong₂ _xor_ (oddℤ-* (a ℤ.+ b) (c ℤ.+ d)) (oddℤ-double (ℤ.- (b ℤ.* d))) ⟩
  (oddℤ (a ℤ.+ b) ∧ oddℤ (c ℤ.+ d)) xor false
    ≡⟨ xor-false _ ⟩
  oddℤ (a ℤ.+ b) ∧ oddℤ (c ℤ.+ d) ∎
  where
  open ≡-Reasoning
  open ℤS using (_:+_ ; _:*_ ; :-_ ; _:=_)
  lemma : ∀ a b c d → (a ℤ.* c ℤ.+ ℤ.- (b ℤ.* d)) ℤ.+ (a ℤ.* d ℤ.+ b ℤ.* c)
                    ≡ (a ℤ.+ b) ℤ.* (c ℤ.+ d) ℤ.+ ((ℤ.- (b ℤ.* d)) ℤ.+ (ℤ.- (b ℤ.* d)))
  lemma = ℤS.solve 4 (λ a b c d → (a :* c :+ :- (b :* d)) :+ (a :* d :+ b :* c)
                               := (a :+ b) :* (c :+ d) :+ ((:- (b :* d)) :+ (:- (b :* d)))) refl
  xor-false : ∀ b → b xor false ≡ b
  xor-false true  = refl
  xor-false false = refl

oddᶻ-ⅈ : oddᶻ ⅈᶻ ≡ true
oddᶻ-ⅈ = refl

oddᶻ-γ : oddᶻ γᶻ ≡ false
oddᶻ-γ = refl

oddᶻ-1 : oddᶻ ZR.1# ≡ true
oddᶻ-1 = refl

oddᶻ-0 : oddᶻ ZR.0# ≡ false
oddᶻ-0 = refl

------------------------------------------------------------------------
-- Divisibility by γ and by 2

infix 4 γ∣_ 2∣_

γ∣_ : Z → Set
γ∣ w = ∃ λ y → w ≡ γᶻ ZR.* y

2∣_ : Z → Set
2∣ w = ∃ λ y → w ≡ 2ᶻ ZR.* y

-- A Gaussian integer is even iff it is divisible by γ.
γ∣⇒even : ∀ {w} → γ∣ w → oddᶻ w ≡ false
γ∣⇒even {w} (y , refl) = oddᶻ-* γᶻ y

even⇒γ∣ : ∀ w → oddᶻ w ≡ false → γ∣ w
even⇒γ∣ (Cplx a b) e =
  let (u , p) = evenℤ-half (a ℤ.+ b) e in
  Cplx u (u ℤ.- a) , cong₂ Cplx (re-eq u p) (im-eq u p)
  where
  open ℤS using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)
  -- γ (u + (u - a) i) = (u - (u - a)) + (u + (u - a)) i.
  re-eq : ∀ u → a ℤ.+ b ≡ u ℤ.+ u →
          a ≡ (+ 1) ℤ.* u ℤ.+ ℤ.- ((+ 1) ℤ.* (u ℤ.- a))
  re-eq u _ = ℤS.solve 2 (λ a u → a := con (+ 1) :* u :+ :- (con (+ 1) :* (u :- a))) refl a u
  im-eq : ∀ u → a ℤ.+ b ≡ u ℤ.+ u →
          b ≡ (+ 1) ℤ.* (u ℤ.- a) ℤ.+ (+ 1) ℤ.* u
  im-eq u p = begin
    b                                      ≡⟨ ℤS.solve 2 (λ a b → b := (a :+ b) :- a) refl a b ⟩
    (a ℤ.+ b) ℤ.- a                        ≡⟨ cong (ℤ._- a) p ⟩
    (u ℤ.+ u) ℤ.- a                        ≡⟨ ℤS.solve 2 (λ a u → (u :+ u) :- a
                                                 := con (+ 1) :* (u :- a) :+ con (+ 1) :* u) refl a u ⟩
    (+ 1) ℤ.* (u ℤ.- a) ℤ.+ (+ 1) ℤ.* u    ∎
    where open ≡-Reasoning

-- 2 = -i γ².
2ᶻ≡ : 2ᶻ ≡ (ZR.- ⅈᶻ) ZR.* (γᶻ ZR.* γᶻ)
2ᶻ≡ = refl

2∣⇒γ∣ : ∀ {w} → 2∣ w → ∃ λ y → w ≡ γᶻ ZR.* (γᶻ ZR.* y)
2∣⇒γ∣ {w} (y , refl) = (ZR.- ⅈᶻ) ZR.* y ,
  trans (cong (ZR._* y) 2ᶻ≡)
        (ZS.solve 3 (λ a g y → (a ZS.:* (g ZS.:* g)) ZS.:* y
                            ZS.:= g ZS.:* (g ZS.:* (a ZS.:* y))) refl (ZR.- ⅈᶻ) γᶻ y)
