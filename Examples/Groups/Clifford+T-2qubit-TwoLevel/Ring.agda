------------------------------------------------------------------------
-- Presentations of groups
--
-- The rings of Greylyn, "Generators and relations for the group
-- U₄(ℤ[1/√2,i])" (M.Sc. thesis, Dalhousie 2014, arXiv:1408.6204):
-- the cyclotomic integers ℤ[ω] ⊆ 𝔻[ω] = ℤ[1/√2,i], ω = e^{iπ/4},
-- taken from EucDomain (ZOmega, DOmega); the prime δ = 1 + ω, and
-- parity, i.e. divisibility by δ (the δ-residue of Definition 2.7).
--
-- An element aω³ + bω² + cω + d is written Omega a b c d.
--
-- The operations of 𝔻[ω] are opaque.  EucDomain's are transparent,
-- and 𝔻[ω] is a record of dyadic fractions, again records, whose
-- arithmetic goes through a normalising smart constructor.  So the
-- type checker, asked to compare two different but convertible
-- expressions (a product and a module-copied alias of it, say),
-- unfolds both into dyadic arithmetic on stuck terms, which does not
-- terminate in practice: even DR.*-assoc, checked against its own
-- type as a client writes it, did not.  With the operations opaque,
-- every comparison stops at _*ᴰ_; computations that need the
-- arithmetic go in `opaque unfolding` blocks.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring where

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_ ; _∧_)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Integer.Solver as ℤSolver
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec)

open import Algebra.Solver.Ring.AlmostCommutativeRing using (fromCommutativeRing)
import Algebra.Solver.Ring.Simple
open import Instances
  using (_≟_ ; DEℤ ; SemiRing ; Ring ; Adjoint ; _+_ ; _*_ ; -_ ; 0# ; 1# ; fromℕ ; adj)
open import Quantum.Synthesis.Ring
  using (Dyadic ; Dyadic' ; _[ω] ; Omega ; DOmega ; ZOmega
        ; SemiRingDyadic ; RingDyadic ; AdjointDyadic ; DecEqDyadic ; SemiRingOmega ; RingOmega ; AdjointOmega ; DecEqOmega)
open import Quantum.Synthesis.Ring.Properties
  using (commutativeRing-𝔻 ; isCommutativeRing-DOmega ; commutativeRing-ZOmega
        ; IsInvolutiveRingEndo ; adj-DOmega)
import Quantum.Synthesis.Ring.Properties.Common as Common
import Examples.Groups.Clifford+CS-TwoLevel.Algebra as Algebra

-- Parity of integers, and integers as dyadic fractions.
open import Examples.Groups.Clifford+CS-TwoLevel.Ring public
  using (oddℕ ; oddℕ-+ ; oddℕ-* ; oddℤ ; oddℤ-+ ; oddℤ-neg ; oddℤ-* ; oddℤ-double ; evenℤ-half
        ; ι₀ ; ι₀-+ ; ι₀-* ; ι₀-neg ; ι₀-injective)

------------------------------------------------------------------------
-- The two rings

-- 𝔻[ω] = ℤ[1/√2,i], the ring of the matrix entries.
D : Set
D = DOmega

-- ℤ[ω], the cyclotomic integers of degree 8.
Z : Set
Z = ZOmega

-- The operations of 𝔻[ω]: EucDomain's, made opaque, and complex
-- conjugation.
opaque
  infixl 6 _+ᴰ_
  infixl 7 _*ᴰ_
  infix 8 -ᴰ_

  _+ᴰ_ _*ᴰ_ : D → D → D
  x +ᴰ y = x + y
  x *ᴰ y = x * y

  -ᴰ_ : D → D
  -ᴰ x = - x

  adjᴰ : D → D
  adjᴰ x = adj x

0ᴰ 1ᴰ : D
0ᴰ = 0#
1ᴰ = 1#

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  isCommutativeRing-D : IsCommutativeRing _≡_ _+ᴰ_ _*ᴰ_ -ᴰ_ 0ᴰ 1ᴰ
  isCommutativeRing-D = isCommutativeRing-DOmega

commutativeRing-D : CommutativeRing 0ℓ 0ℓ
commutativeRing-D = record { isCommutativeRing = isCommutativeRing-D }

-- The ring structures: 𝔻[ω]'s opaque one, and EucDomain's for the
-- dyadic fractions and for ℤ[ω].
module 𝔻R = CommutativeRing commutativeRing-𝔻
module DR = CommutativeRing commutativeRing-D
module ZR = CommutativeRing commutativeRing-ZOmega

-- Ring solvers with integer coefficients.
module DS = Common.ZSolver commutativeRing-D
module ZS = Common.ZSolver commutativeRing-ZOmega

-- A ring solver over ℤ[ω] with coefficients in ℤ[ω]: constants such
-- as ω and δ multiply out by computation.
module ZG = Algebra.Solver.Ring.Simple (fromCommutativeRing commutativeRing-ZOmega) (λ x y → x ≟ y)

-- Identities in 𝔻[ω], proved over an abstract ring (see Algebra).
module DA = Algebra commutativeRing-D (λ p → p)

private
  module ℤS = ℤSolver.+-*-Solver

  cong₄ : ∀ {A B C E F : Set} (f : A → B → C → E → F) {a a′ b b′ c c′ e e′} →
          a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ → f a b c e ≡ f a′ b′ c′ e′
  cong₄ f refl refl refl refl = refl

------------------------------------------------------------------------
-- Constants

private
  d0 d1 h -h : Dyadic
  d0 = Dyadic' (+ 0) 0 _
  d1 = Dyadic' (+ 1) 0 _
  h = Dyadic' (+ 1) 1 _
  -h = Dyadic' -[1+ 0 ] 1 _

-- ω = e^{iπ/4}, in both rings.
ωᴰ : D
ωᴰ = Omega d0 d0 d1 d0

ωᶻ : Z
ωᶻ = Omega (+ 0) (+ 0) (+ 1) (+ 0)

-- δ = 1 + ω, and its inverse δ⁻ = (1 - ω + ω² - ω³)/2 in 𝔻[ω].
δᴰ δ⁻ : D
δᴰ = Omega d0 d0 d1 d1
δ⁻ = Omega -h h -h h

δᶻ : Z
δᶻ = Omega (+ 0) (+ 0) (+ 1) (+ 1)

-- 1/√2 = (ω - ω³)/2, the scalar of the Hadamard matrix.
√½ : D
√½ = Omega -h d0 h d0

-- √2 = ω - ω³, λ = 1 + √2, and 2, in ℤ[ω].
√2ᶻ λᶻ 2ᶻ : Z
√2ᶻ = Omega -[1+ 0 ] (+ 0) (+ 1) (+ 0)
λᶻ = Omega -[1+ 0 ] (+ 0) (+ 1) (+ 1)
2ᶻ = Omega (+ 0) (+ 0) (+ 0) (+ 2)

opaque
  unfolding _*ᴰ_

  δ*δ⁻ : δᴰ DR.* δ⁻ ≡ DR.1#
  δ*δ⁻ = refl

  δ⁻*δ : δ⁻ DR.* δᴰ ≡ DR.1#
  δ⁻*δ = refl

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
-- The embedding ℤ[ω] → 𝔻[ω]

emb : Z → D
emb (Omega a b c d) = Omega (ι₀ a) (ι₀ b) (ι₀ c) (ι₀ d)

emb-injective : ∀ {x y} → emb x ≡ emb y → x ≡ y
emb-injective {Omega a b c d} {Omega a′ b′ c′ d′} eq =
  cong₄ Omega (ι₀-injective (cong pa eq)) (ι₀-injective (cong pb eq))
              (ι₀-injective (cong pc eq)) (ι₀-injective (cong pd eq))
  where
  pa pb pc pd : D → Dyadic
  pa (Omega x _ _ _) = x
  pb (Omega _ x _ _) = x
  pc (Omega _ _ x _) = x
  pd (Omega _ _ _ x) = x

private
  ι₀-- : ∀ x y → ι₀ (x ℤ.+ ℤ.- y) ≡ ι₀ x 𝔻R.+ 𝔻R.- ι₀ y
  ι₀-- x y = trans (ι₀-+ x (ℤ.- y)) (cong (ι₀ x 𝔻R.+_) (ι₀-neg y))

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  emb-+ : ∀ x y → emb (x ZR.+ y) ≡ emb x DR.+ emb y
  emb-+ (Omega a b c d) (Omega a′ b′ c′ d′) = cong₄ Omega (ι₀-+ a a′) (ι₀-+ b b′) (ι₀-+ c c′) (ι₀-+ d d′)

  emb-neg : ∀ x → emb (ZR.- x) ≡ DR.- emb x
  emb-neg (Omega a b c d) = cong₄ Omega (ι₀-neg a) (ι₀-neg b) (ι₀-neg c) (ι₀-neg d)

private
  -- With EucDomain's product, transparent.
  emb-*′ : ∀ x y → emb (x ZR.* y) ≡ emb x * emb y
  emb-*′ (Omega a b c d) (Omega a′ b′ c′ d′) = cong₄ Omega ea eb ec ed
    where
    +₂ = cong₂ 𝔻R._+_
    -₂ = cong₂ (λ x y → x 𝔻R.+ 𝔻R.- y)
    ea = trans (ι₀-+ (a ℤ.* d′ ℤ.+ b ℤ.* c′ ℤ.+ c ℤ.* b′) (d ℤ.* a′))
           (+₂ (trans (ι₀-+ (a ℤ.* d′ ℤ.+ b ℤ.* c′) (c ℤ.* b′))
                 (+₂ (trans (ι₀-+ (a ℤ.* d′) (b ℤ.* c′)) (+₂ (ι₀-* a d′) (ι₀-* b c′))) (ι₀-* c b′)))
               (ι₀-* d a′))
    eb = trans (ι₀-- (b ℤ.* d′ ℤ.+ c ℤ.* c′ ℤ.+ d ℤ.* b′) (a ℤ.* a′))
           (-₂ (trans (ι₀-+ (b ℤ.* d′ ℤ.+ c ℤ.* c′) (d ℤ.* b′))
                 (+₂ (trans (ι₀-+ (b ℤ.* d′) (c ℤ.* c′)) (+₂ (ι₀-* b d′) (ι₀-* c c′))) (ι₀-* d b′)))
               (ι₀-* a a′))
    ec = trans (ι₀-- (c ℤ.* d′ ℤ.+ d ℤ.* c′ ℤ.+ ℤ.- (a ℤ.* b′)) (b ℤ.* a′))
           (-₂ (trans (ι₀-- (c ℤ.* d′ ℤ.+ d ℤ.* c′) (a ℤ.* b′))
                 (-₂ (trans (ι₀-+ (c ℤ.* d′) (d ℤ.* c′)) (+₂ (ι₀-* c d′) (ι₀-* d c′))) (ι₀-* a b′)))
               (ι₀-* b a′))
    ed = trans (ι₀-- (d ℤ.* d′ ℤ.+ ℤ.- (a ℤ.* c′) ℤ.+ ℤ.- (b ℤ.* b′)) (c ℤ.* a′))
           (-₂ (trans (ι₀-- (d ℤ.* d′ ℤ.+ ℤ.- (a ℤ.* c′)) (b ℤ.* b′))
                 (-₂ (trans (ι₀-- (d ℤ.* d′) (a ℤ.* c′)) (-₂ (ι₀-* d d′) (ι₀-* a c′))) (ι₀-* b b′)))
               (ι₀-* c a′))

opaque
  unfolding _*ᴰ_

  emb-* : ∀ x y → emb (x ZR.* y) ≡ emb x DR.* emb y
  emb-* = emb-*′

emb-0 : emb ZR.0# ≡ DR.0#
emb-0 = refl

emb-1 : emb ZR.1# ≡ DR.1#
emb-1 = refl

emb-ω : emb ωᶻ ≡ ωᴰ
emb-ω = refl

emb-δ : emb δᶻ ≡ δᴰ
emb-δ = refl

emb-^ : ∀ x k → emb (x ^ᶻ k) ≡ emb x ^ᴰ k
emb-^ x zero = refl
emb-^ x (suc k) = trans (emb-* x (x ^ᶻ k)) (cong (emb x DR.*_) (emb-^ x k))

------------------------------------------------------------------------
-- Parity: the δ-residue of Definition 2.7
--
-- Since ω ≡ 1 (mod δ) and 2 ≡ 0 (mod δ), aω³ + bω² + cω + d ≡ a + b +
-- c + d (mod δ), and the residue is its parity.

oddᶻ : Z → Bool
oddᶻ (Omega a b c d) = oddℤ (a ℤ.+ b ℤ.+ c ℤ.+ d)

private
  open ℤS using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

  xor-false : ∀ b → b xor false ≡ b
  xor-false true  = refl
  xor-false false = refl

-- Parity is a ring homomorphism ℤ[ω] → 𝔽₂ (with xor as addition).
oddᶻ-+ : ∀ x y → oddᶻ (x ZR.+ y) ≡ oddᶻ x xor oddᶻ y
oddᶻ-+ (Omega a b c d) (Omega a′ b′ c′ d′) =
  trans (cong oddℤ (lemma a b c d a′ b′ c′ d′))
        (oddℤ-+ (a ℤ.+ b ℤ.+ c ℤ.+ d) (a′ ℤ.+ b′ ℤ.+ c′ ℤ.+ d′))
  where
  lemma : ∀ a b c d a′ b′ c′ d′ → (a ℤ.+ a′) ℤ.+ (b ℤ.+ b′) ℤ.+ (c ℤ.+ c′) ℤ.+ (d ℤ.+ d′)
                                ≡ (a ℤ.+ b ℤ.+ c ℤ.+ d) ℤ.+ (a′ ℤ.+ b′ ℤ.+ c′ ℤ.+ d′)
  lemma = ℤS.solve 8 (λ a b c d a′ b′ c′ d′ → (a :+ a′) :+ (b :+ b′) :+ (c :+ c′) :+ (d :+ d′)
                                          := (a :+ b :+ c :+ d) :+ (a′ :+ b′ :+ c′ :+ d′)) refl

oddᶻ-neg : ∀ x → oddᶻ (ZR.- x) ≡ oddᶻ x
oddᶻ-neg (Omega a b c d) = trans (cong oddℤ (lemma a b c d)) (oddℤ-neg (a ℤ.+ b ℤ.+ c ℤ.+ d))
  where
  lemma : ∀ a b c d → ℤ.- a ℤ.+ ℤ.- b ℤ.+ ℤ.- c ℤ.+ ℤ.- d ≡ ℤ.- (a ℤ.+ b ℤ.+ c ℤ.+ d)
  lemma = ℤS.solve 4 (λ a b c d → :- a :+ :- b :+ :- c :+ :- d := :- (a :+ b :+ c :+ d)) refl

oddᶻ-* : ∀ x y → oddᶻ (x ZR.* y) ≡ oddᶻ x ∧ oddᶻ y
oddᶻ-* (Omega a b c d) (Omega a′ b′ c′ d′) = begin
  oddℤ (A ℤ.+ B ℤ.+ C ℤ.+ E)
    ≡⟨ cong oddℤ (lemma a b c d a′ b′ c′ d′) ⟩
  oddℤ (P ℤ.+ (M ℤ.+ M))
    ≡⟨ oddℤ-+ P (M ℤ.+ M) ⟩
  oddℤ P xor oddℤ (M ℤ.+ M)
    ≡⟨ cong₂ _xor_ (oddℤ-* (a ℤ.+ b ℤ.+ c ℤ.+ d) (a′ ℤ.+ b′ ℤ.+ c′ ℤ.+ d′)) (oddℤ-double M) ⟩
  (oddℤ (a ℤ.+ b ℤ.+ c ℤ.+ d) ∧ oddℤ (a′ ℤ.+ b′ ℤ.+ c′ ℤ.+ d′)) xor false
    ≡⟨ xor-false _ ⟩
  oddℤ (a ℤ.+ b ℤ.+ c ℤ.+ d) ∧ oddℤ (a′ ℤ.+ b′ ℤ.+ c′ ℤ.+ d′) ∎
  where
  open ≡-Reasoning
  A = a ℤ.* d′ ℤ.+ b ℤ.* c′ ℤ.+ c ℤ.* b′ ℤ.+ d ℤ.* a′
  B = b ℤ.* d′ ℤ.+ c ℤ.* c′ ℤ.+ d ℤ.* b′ ℤ.+ ℤ.- (a ℤ.* a′)
  C = c ℤ.* d′ ℤ.+ d ℤ.* c′ ℤ.+ ℤ.- (a ℤ.* b′) ℤ.+ ℤ.- (b ℤ.* a′)
  E = d ℤ.* d′ ℤ.+ ℤ.- (a ℤ.* c′) ℤ.+ ℤ.- (b ℤ.* b′) ℤ.+ ℤ.- (c ℤ.* a′)
  P = (a ℤ.+ b ℤ.+ c ℤ.+ d) ℤ.* (a′ ℤ.+ b′ ℤ.+ c′ ℤ.+ d′)
  M = ℤ.- (a ℤ.* a′ ℤ.+ a ℤ.* b′ ℤ.+ b ℤ.* a′ ℤ.+ a ℤ.* c′ ℤ.+ c ℤ.* a′ ℤ.+ b ℤ.* b′)
  lemma : ∀ a b c d a′ b′ c′ d′ →
          (a ℤ.* d′ ℤ.+ b ℤ.* c′ ℤ.+ c ℤ.* b′ ℤ.+ d ℤ.* a′)
          ℤ.+ (b ℤ.* d′ ℤ.+ c ℤ.* c′ ℤ.+ d ℤ.* b′ ℤ.+ ℤ.- (a ℤ.* a′))
          ℤ.+ (c ℤ.* d′ ℤ.+ d ℤ.* c′ ℤ.+ ℤ.- (a ℤ.* b′) ℤ.+ ℤ.- (b ℤ.* a′))
          ℤ.+ (d ℤ.* d′ ℤ.+ ℤ.- (a ℤ.* c′) ℤ.+ ℤ.- (b ℤ.* b′) ℤ.+ ℤ.- (c ℤ.* a′))
          ≡ (a ℤ.+ b ℤ.+ c ℤ.+ d) ℤ.* (a′ ℤ.+ b′ ℤ.+ c′ ℤ.+ d′)
            ℤ.+ (ℤ.- (a ℤ.* a′ ℤ.+ a ℤ.* b′ ℤ.+ b ℤ.* a′ ℤ.+ a ℤ.* c′ ℤ.+ c ℤ.* a′ ℤ.+ b ℤ.* b′)
                 ℤ.+ ℤ.- (a ℤ.* a′ ℤ.+ a ℤ.* b′ ℤ.+ b ℤ.* a′ ℤ.+ a ℤ.* c′ ℤ.+ c ℤ.* a′ ℤ.+ b ℤ.* b′))
  lemma = ℤS.solve 8 (λ a b c d a′ b′ c′ d′ →
            (a :* d′ :+ b :* c′ :+ c :* b′ :+ d :* a′)
            :+ (b :* d′ :+ c :* c′ :+ d :* b′ :+ :- (a :* a′))
            :+ (c :* d′ :+ d :* c′ :+ :- (a :* b′) :+ :- (b :* a′))
            :+ (d :* d′ :+ :- (a :* c′) :+ :- (b :* b′) :+ :- (c :* a′))
            := (a :+ b :+ c :+ d) :* (a′ :+ b′ :+ c′ :+ d′)
               :+ (:- (a :* a′ :+ a :* b′ :+ b :* a′ :+ a :* c′ :+ c :* a′ :+ b :* b′)
                   :+ :- (a :* a′ :+ a :* b′ :+ b :* a′ :+ a :* c′ :+ c :* a′ :+ b :* b′))) refl

oddᶻ-ω : oddᶻ ωᶻ ≡ true
oddᶻ-ω = refl

oddᶻ-δ : oddᶻ δᶻ ≡ false
oddᶻ-δ = refl

oddᶻ-1 : oddᶻ ZR.1# ≡ true
oddᶻ-1 = refl

oddᶻ-0 : oddᶻ ZR.0# ≡ false
oddᶻ-0 = refl

------------------------------------------------------------------------
-- Divisibility by δ

infix 4 δ∣_

δ∣_ : Z → Set
δ∣ w = ∃ λ y → w ≡ δᶻ ZR.* y

-- δ (p ω³ + q ω² + r ω + s) = (q + p) ω³ + (r + q) ω² + (s + r) ω + (s - p).
δ*≡ : ∀ p q r s → δᶻ ZR.* Omega p q r s ≡ Omega (q ℤ.+ p) (r ℤ.+ q) (s ℤ.+ r) (s ℤ.+ ℤ.- p)
δ*≡ p q r s = cong₄ Omega
  (ℤS.solve 4 (λ p q r s → con (+ 0) :* s :+ con (+ 0) :* r :+ con (+ 1) :* q :+ con (+ 1) :* p := q :+ p) refl p q r s)
  (ℤS.solve 4 (λ p q r s → con (+ 0) :* s :+ con (+ 1) :* r :+ con (+ 1) :* q :+ :- (con (+ 0) :* p) := r :+ q)
              refl p q r s)
  (ℤS.solve 4 (λ p q r s → con (+ 1) :* s :+ con (+ 1) :* r :+ :- (con (+ 0) :* q) :+ :- (con (+ 0) :* p) := s :+ r)
              refl p q r s)
  (ℤS.solve 4 (λ p q r s → con (+ 1) :* s :+ :- (con (+ 0) :* r) :+ :- (con (+ 0) :* q) :+ :- (con (+ 1) :* p)
                          := s :+ :- p) refl p q r s)

-- An element of ℤ[ω] is even iff it is divisible by δ.
δ∣⇒even : ∀ {w} → δ∣ w → oddᶻ w ≡ false
δ∣⇒even {w} (y , refl) = oddᶻ-* δᶻ y

even⇒δ∣ : ∀ w → oddᶻ w ≡ false → δ∣ w
even⇒δ∣ (Omega a b c d) e = go (evenℤ-half (a ℤ.+ b ℤ.+ c ℤ.+ d) e)
  where
  go : (∃ λ s → a ℤ.+ b ℤ.+ c ℤ.+ d ≡ s ℤ.+ s) → δ∣ Omega a b c d
  go (s , p) = y , sym (trans (δ*≡ (s ℤ.- b ℤ.- d) (s ℤ.- c) (s ℤ.- a ℤ.- d) (s ℤ.- b))
                             (cong₄ Omega ea eb ec ed))
    where
    y = Omega (s ℤ.- b ℤ.- d) (s ℤ.- c) (s ℤ.- a ℤ.- d) (s ℤ.- b)
    -- Each entry is (s + s) minus the other three.
    via : ∀ {x t} → t ≡ (s ℤ.+ s) ℤ.- (a ℤ.+ b ℤ.+ c ℤ.+ d ℤ.- x) → t ≡ x
    via {x} {t} q = trans q (trans (cong (λ z → z ℤ.- (a ℤ.+ b ℤ.+ c ℤ.+ d ℤ.- x)) (sym p))
                                    (ℤS.solve 5 (λ a b c d x → (a :+ b :+ c :+ d) :- (a :+ b :+ c :+ d :- x) := x)
                                                refl a b c d x))
    ea = via (ℤS.solve 5 (λ s a b c d → (s :- c) :+ (s :- b :- d) := (s :+ s) :- (a :+ b :+ c :+ d :- a))
                         refl s a b c d)
    eb = via (ℤS.solve 5 (λ s a b c d → (s :- a :- d) :+ (s :- c) := (s :+ s) :- (a :+ b :+ c :+ d :- b))
                         refl s a b c d)
    ec = via (ℤS.solve 5 (λ s a b c d → (s :- b) :+ (s :- a :- d) := (s :+ s) :- (a :+ b :+ c :+ d :- c))
                         refl s a b c d)
    ed = ℤS.solve 3 (λ s b d → (s :- b) :+ :- (s :- b :- d) := d) refl s b d

------------------------------------------------------------------------
-- 𝔻[ω] as an EucDomain ring with conjugation
--
-- Instances, so that EucDomain's matrices over 𝔻[ω] (and the generic
-- modules of Clifford+CS-TwoLevel) use the opaque operations.  A
-- client must not also have EucDomain's instances for 𝔻[ω] in scope
-- (SemiRingOmega with RingDyadic): instance search at 𝔻[ω] would be
-- ambiguous.

-- Decidable equality.
infix 4 _≟ᴰ_ _≟ᶻ_

_≟ᴰ_ : (x y : D) → Dec (x ≡ y)
_≟ᴰ_ = _≟_

_≟ᶻ_ : (x y : Z) → Dec (x ≡ y)
_≟ᶻ_ = _≟_

semiRing-D : SemiRing D
semiRing-D = record { _+_ = _+ᴰ_ ; _*_ = _*ᴰ_ ; 0# = 0ᴰ ; 1# = 1ᴰ ; fromℕ = fromℕ }

ring-D : Ring D
ring-D = record { sra = semiRing-D ; -_ = -ᴰ_ }

adjoint-D : Adjoint D
adjoint-D = record { adj = adjᴰ }

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_ adjᴰ

  -- Conjugation is an involutive ring automorphism.
  adj-D : IsInvolutiveRingEndo {{ring-D}} adjᴰ
  adj-D = adj-DOmega

instance
  SemiRingD : SemiRing D
  SemiRingD = semiRing-D

  RingD : Ring D
  RingD = ring-D

  AdjointD : Adjoint D
  AdjointD = adjoint-D
