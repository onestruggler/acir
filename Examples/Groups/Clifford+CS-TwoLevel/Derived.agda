------------------------------------------------------------------------
-- Presentations of groups
--
-- Consequences of the relations of Figure 1: the inverses of the
-- generators, the two ways of writing K†, and the relations of
-- Figure 2 that the proof of the Main Lemma uses.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Examples.Groups.Clifford+CS-TwoLevel.Derived {n : ℕ} where

open import Data.Fin.Base using (Fin ; _<_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Unit.Base using (⊤)
import Data.Fin.Properties as FinP
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; ≢-sym) renaming (sym to ≡-sym)
open import Relation.Nullary.Decidable using (recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  variable
    j k l : Fin n

  <⇒≢ : .(j < k) → j ≢ k
  <⇒≢ {j = j} {k} p j≡k = FinP.<-irrefl j≡k (recompute (j FinP.<? k) p)

  -- Generators with distinct indices i_[j], i_[k] commute.
  ii : j ≢ k → i j • i k ≈ i k • i j
  ii j≢k = axiom (comm-ii j≢k)

------------------------------------------------------------------------
-- Orders and inverses

i⁴ : i j ^ 4 ≈ ε
i⁴ = axiom order-i

i-i³ : i j • i j ^ 3 ≈ ε
i-i³ = i⁴

i³-i : i j ^ 3 • i j ≈ ε
i³-i {j} = trans (sym (^-+ (i j) 3 1)) i⁴

X-X : .(p : j < k) → X j k p • X j k p ≈ ε
X-X p = axiom (order-X p)

K-K† : .(p : j < k) → K j k p • K† j k p ≈ ε
K-K† p = axiom (order-K p)

K†-K : .(p : j < k) → K† j k p • K j k p ≈ ε
K†-K {j} {k} p = trans (sym (^-+ (K j k p) 7 1)) (axiom (order-K p))

------------------------------------------------------------------------
-- K† = K i_[j] i_[k] = i_[j] i_[k] K (from (15) and (16))

K†≈Kii : .(p : j < k) → K† j k p ≈ K j k p • i j • i k
K†≈Kii {j} {k} p = begin
  K† j k p                                              ≈⟨ sym right-unit ⟩
  K† j k p • ε                                          ≈⟨ cright sym (axiom (rel-16 p)) ⟩
  K† j k p • (K j k p ^ 2 • i j • i k)                  ≈⟨ by-assoc auto ⟩
  (K† j k p • K j k p) • (K j k p • i j • i k)          ≈⟨ cleft K†-K p ⟩
  ε • (K j k p • i j • i k)                             ≈⟨ left-unit ⟩
  K j k p • i j • i k                                   ∎

K†≈iiK : .(p : j < k) → K† j k p ≈ i j • i k • K j k p
K†≈iiK p = trans (K†≈Kii p) (axiom (rel-15 p))

------------------------------------------------------------------------
-- Figure 2

-- K_[j,k] = i_[j]³ i_[k]³ K†_[j,k]
K≈i³i³K† : .(p : j < k) → K j k p ≈ i j ^ 3 • i k ^ 3 • K† j k p
K≈i³i³K† {j} {k} p = sym (begin
  i j ^ 3 • i k ^ 3 • K† j k p                          ≈⟨ cright cright K†≈iiK p ⟩
  i j ^ 3 • i k ^ 3 • (i j • i k • K j k p)             ≈⟨ by-assoc auto ⟩
  i j ^ 3 • (i k ^ 3 • i j) • i k • K j k p             ≈⟨ cright cleft comm⇒pow-comm 3 1 (ii (λ e → <⇒≢ p (≡-sym e))) ⟩
  i j ^ 3 • (i j • i k ^ 3) • i k • K j k p             ≈⟨ by-assoc auto ⟩
  (i j ^ 3 • i j) • (i k ^ 3 • i k) • K j k p           ≈⟨ cong i³-i (cleft i³-i) ⟩
  ε • ε • K j k p                                       ≈⟨ by-assoc auto ⟩
  K j k p                                               ∎)

------------------------------------------------------------------------
-- Consequences of (13)–(15) for K_[j,k] and i_[j], i_[k]

private
  k≢j : .(j < k) → k ≢ j
  k≢j p e = <⇒≢ p (≡-sym e)

-- K i_[j] = X i_[j] i_[k] K i_[k]
KI≈XILKL : .(p : j < k) → K j k p • i j ≈ X j k p • i j • i k • K j k p • i k
KI≈XILKL {j} {k} p = sym (begin
  X j k p • i j • i k • K j k p • i k         ≈⟨ by-assoc auto ⟩
  X j k p • (i j • i k • K j k p) • i k       ≈⟨ cright cleft sym (axiom (rel-15 p)) ⟩
  X j k p • (K j k p • i j • i k) • i k       ≈⟨ by-assoc auto ⟩
  (X j k p • K j k p) • i j • i k • i k       ≈⟨ cleft sym (axiom (rel-13 p)) ⟩
  (K j k p • i k ^ 2) • i j • i k • i k       ≈⟨ by-assoc auto ⟩
  K j k p • (i k ^ 2 • i j) • i k • i k       ≈⟨ cright cleft comm⇒pow-comm 2 1 (ii (k≢j p)) ⟩
  K j k p • (i j • i k ^ 2) • i k • i k       ≈⟨ by-assoc auto ⟩
  K j k p • i j • i k ^ 4                     ≈⟨ cright cright i⁴ ⟩
  K j k p • i j • ε                           ≈⟨ by-assoc auto ⟩
  K j k p • i j                               ∎)

-- K i_[k] K = i_[k]³ K i_[k]³, from (14).
KLK : .(p : j < k) → K j k p • i k • K j k p ≈ i k ^ 3 • K j k p • i k ^ 3
KLK {j} {k} p = sym (begin
  i k ^ 3 • K j k p • i k ^ 3                  ≈⟨ cright axiom (rel-14 p) ⟩
  i k ^ 3 • i k • K j k p • i k • K j k p      ≈⟨ by-assoc auto ⟩
  (i k ^ 3 • i k) • K j k p • i k • K j k p    ≈⟨ cleft i³-i ⟩
  ε • K j k p • i k • K j k p                  ≈⟨ left-unit ⟩
  K j k p • i k • K j k p                      ∎)

-- i_[j] K i_[k]³ = i_[k]³ K i_[j]
IKL³≈L³KI : .(p : j < k) → i j • K j k p • i k ^ 3 ≈ i k ^ 3 • K j k p • i j
IKL³≈L³KI {j} {k} p = sym (begin
  i k ^ 3 • K j k p • i j                      ≈⟨ cright cright sym (trans (cright i⁴) right-unit) ⟩
  i k ^ 3 • K j k p • i j • i k ^ 4            ≈⟨ by-assoc auto ⟩
  i k ^ 3 • (K j k p • i j • i k) • i k ^ 3    ≈⟨ cright cleft axiom (rel-15 p) ⟩
  i k ^ 3 • (i j • i k • K j k p) • i k ^ 3    ≈⟨ by-assoc auto ⟩
  (i k ^ 3 • i j) • i k • K j k p • i k ^ 3    ≈⟨ cleft comm⇒pow-comm 3 1 (ii (k≢j p)) ⟩
  (i j • i k ^ 3) • i k • K j k p • i k ^ 3    ≈⟨ by-assoc auto ⟩
  i j • (i k ^ 3 • i k) • K j k p • i k ^ 3    ≈⟨ cright cleft i³-i ⟩
  i j • ε • K j k p • i k ^ 3                  ≈⟨ by-assoc auto ⟩
  i j • K j k p • i k ^ 3                      ∎)

------------------------------------------------------------------------
-- Figure 2, continued

-- K†_[j,k] i_[j] = i_[j] i_[k] X_[j,k] K†_[j,k] i_[k]
K†I≈ILXK†L : .(p : j < k) → K† j k p • i j ≈ i j • i k • X j k p • K† j k p • i k
K†I≈ILXK†L {j} {k} p = begin
  K† j k p • i j                                      ≈⟨ cleft K†≈iiK p ⟩
  (i j • i k • K j k p) • i j                         ≈⟨ by-assoc auto ⟩
  i j • i k • (K j k p • i j)                         ≈⟨ cright cright KI≈XILKL p ⟩
  i j • i k • (X j k p • i j • i k • K j k p • i k)   ≈⟨ by-assoc auto ⟩
  i j • i k • X j k p • (i j • i k • K j k p) • i k   ≈⟨ cright cright cright cleft sym (K†≈iiK p) ⟩
  i j • i k • X j k p • K† j k p • i k                ∎

-- K†_[j,k] i_[k] K_[j,k] = i_[k]³ X_[j,k] K†_[j,k] i_[k]
K†LK≈L³XK†L : .(p : j < k) → K† j k p • i k • K j k p ≈ i k ^ 3 • X j k p • K† j k p • i k
K†LK≈L³XK†L {j} {k} p = begin
  K† j k p • i k • K j k p                            ≈⟨ cleft K†≈iiK p ⟩
  (i j • i k • K j k p) • i k • K j k p               ≈⟨ by-assoc auto ⟩
  i j • i k • (K j k p • i k • K j k p)               ≈⟨ cright cright KLK p ⟩
  i j • i k • (i k ^ 3 • K j k p • i k ^ 3)           ≈⟨ by-assoc auto ⟩
  i j • (i k • i k ^ 3) • K j k p • i k ^ 3           ≈⟨ cright cleft i-i³ ⟩
  i j • ε • K j k p • i k ^ 3                         ≈⟨ by-assoc auto ⟩
  i j • K j k p • i k ^ 3                             ≈⟨ IKL³≈L³KI p ⟩
  i k ^ 3 • K j k p • i j                             ≈⟨ cright KI≈XILKL p ⟩
  i k ^ 3 • X j k p • i j • i k • K j k p • i k       ≈⟨ by-assoc auto ⟩
  i k ^ 3 • X j k p • (i j • i k • K j k p) • i k     ≈⟨ cright cright cleft sym (K†≈iiK p) ⟩
  i k ^ 3 • X j k p • K† j k p • i k                  ∎

------------------------------------------------------------------------
-- Conjugating powers

-- u w = w v gives uᵉ w = w vᵉ.
conj-^ : {u v w : Word (Gen n)} → u • w ≈ w • v → ∀ e → u ^ e • w ≈ w • v ^ e
conj-^ h ℕ.zero = trans left-unit (sym right-unit)
conj-^ h (ℕ.suc ℕ.zero) = h
conj-^ {u} {v} {w} h (ℕ.suc (ℕ.suc e)) = begin
  (u • u ^ ℕ.suc e) • w      ≈⟨ assoc ⟩
  u • (u ^ ℕ.suc e • w)      ≈⟨ cright conj-^ h (ℕ.suc e) ⟩
  u • (w • v ^ ℕ.suc e)      ≈⟨ sym assoc ⟩
  (u • w) • v ^ ℕ.suc e      ≈⟨ cleft h ⟩
  (w • v) • v ^ ℕ.suc e      ≈⟨ assoc ⟩
  w • (v • v ^ ℕ.suc e)      ∎

------------------------------------------------------------------------
-- X_[j,k] and the i's

-- X i_[k] X = i_[j], and i_[j] X = X i_[k].
XLX≈I : .(p : j < k) → X j k p • i k • X j k p ≈ i j
XLX≈I {j} {k} p = begin
  X j k p • i k • X j k p       ≈⟨ cright axiom (swap-iX p) ⟩
  X j k p • X j k p • i j       ≈⟨ sym assoc ⟩
  (X j k p • X j k p) • i j     ≈⟨ cleft X-X p ⟩
  ε • i j                       ≈⟨ left-unit ⟩
  i j                           ∎

IX≈XL : .(p : j < k) → i j • X j k p ≈ X j k p • i k
IX≈XL {j} {k} p = begin
  i j • X j k p                         ≈⟨ cleft sym (XLX≈I p) ⟩
  (X j k p • i k • X j k p) • X j k p   ≈⟨ by-assoc auto ⟩
  X j k p • i k • (X j k p • X j k p)   ≈⟨ cright cright X-X p ⟩
  X j k p • i k • ε                     ≈⟨ by-assoc auto ⟩
  X j k p • i k                         ∎

-- K X = i_[k]² K
KX≈L²K : .(p : j < k) → K j k p • X j k p ≈ i k ^ 2 • K j k p
KX≈L²K {j} {k} p = begin
  K j k p • X j k p                               ≈⟨ sym right-unit ⟩
  (K j k p • X j k p) • ε                         ≈⟨ cright sym (K-K† p) ⟩
  (K j k p • X j k p) • (K j k p • K† j k p)      ≈⟨ by-assoc auto ⟩
  K j k p • (X j k p • K j k p) • K† j k p        ≈⟨ cright cleft sym (axiom (rel-13 p)) ⟩
  K j k p • (K j k p • i k ^ 2) • K† j k p        ≈⟨ cright cright K†≈iiK p ⟩
  K j k p • (K j k p • i k ^ 2) • (i j • i k • K j k p)   ≈⟨ by-assoc auto ⟩
  K j k p • K j k p • (i k ^ 2 • i j) • i k • K j k p     ≈⟨ cright cright cleft comm⇒pow-comm 2 1 (ii (k≢j p)) ⟩
  K j k p • K j k p • (i j • i k ^ 2) • i k • K j k p     ≈⟨ by-assoc auto ⟩
  (K j k p ^ 2 • i j • i k) • i k • i k • K j k p         ≈⟨ cleft axiom (rel-16 p) ⟩
  ε • i k • i k • K j k p                                 ≈⟨ by-assoc auto ⟩
  i k ^ 2 • K j k p                                       ∎

------------------------------------------------------------------------
-- Figure 2, continued: three indices j < k < l

module _ (p : j < k) (q : k < l) where

  private
    jl = FinP.<-trans p q

  -- X_[j,l] i_[j]ᵉ X_[k,l] = X_[j,k] X_[j,l] i_[j]ᵉ
  XIX≈XXI : ∀ e → X j l jl • i j ^ e • X k l q ≈ X j k p • X j l jl • i j ^ e
  XIX≈XXI e = begin
    X j l jl • i j ^ e • X k l q      ≈⟨ cright conj-^ (axiom (comm-iX q (<⇒≢ p) (<⇒≢ jl))) e ⟩
    X j l jl • X k l q • i j ^ e      ≈⟨ sym assoc ⟩
    (X j l jl • X k l q) • i j ^ e    ≈⟨ cleft axiom (swap-XX′ p q) ⟩
    (X k l q • X j k p) • i j ^ e     ≈⟨ cleft axiom (swap-XX p q) ⟩
    (X j k p • X j l jl) • i j ^ e    ≈⟨ assoc ⟩
    X j k p • X j l jl • i j ^ e      ∎

  -- X_[k,l] i_[k]ᵉ X_[j,k] = X_[j,k] X_[j,l] i_[j]ᵉ
  XIX≈XXI′ : ∀ e → X k l q • i k ^ e • X j k p ≈ X j k p • X j l jl • i j ^ e
  XIX≈XXI′ e = begin
    X k l q • i k ^ e • X j k p       ≈⟨ cright conj-^ (axiom (swap-iX p)) e ⟩
    X k l q • X j k p • i j ^ e       ≈⟨ sym assoc ⟩
    (X k l q • X j k p) • i j ^ e     ≈⟨ cleft axiom (swap-XX p q) ⟩
    (X j k p • X j l jl) • i j ^ e    ≈⟨ assoc ⟩
    X j k p • X j l jl • i j ^ e      ∎

  -- K_[j,l]ᵈ i_[l]ᵉ X_[k,l] = X_[k,l] K_[j,k]ᵈ i_[k]ᵉ, for K (d = 1)
  -- and K† (d = 7) alike.
  KIX≈XKI : ∀ d e → K j l jl ^ d • i l ^ e • X k l q ≈ X k l q • K j k p ^ d • i k ^ e
  KIX≈XKI d e = begin
    K j l jl ^ d • i l ^ e • X k l q      ≈⟨ cright conj-^ (axiom (swap-iX q)) e ⟩
    K j l jl ^ d • X k l q • i k ^ e      ≈⟨ sym assoc ⟩
    (K j l jl ^ d • X k l q) • i k ^ e    ≈⟨ cleft conj-^ (axiom (swap-KX′ p q)) d ⟩
    (X k l q • K j k p ^ d) • i k ^ e     ≈⟨ assoc ⟩
    X k l q • K j k p ^ d • i k ^ e       ∎

------------------------------------------------------------------------
-- Figure 2, continued: K†_[j,k] i_[k] X_[j,k] = X_[j,k] i_[j]³ i_[k] K†_[j,k] i_[k]

K†LX≈XI³LK†L : .(p : j < k) → K† j k p • i k • X j k p ≈ X j k p • i j ^ 3 • i k • K† j k p • i k
K†LX≈XI³LK†L {j} {k} p = begin
  K† j k p • i k • X j k p                            ≈⟨ cleft K†≈iiK p ⟩
  (i j • i k • K j k p) • i k • X j k p               ≈⟨ cright axiom (swap-iX p) ⟩
  (i j • i k • K j k p) • X j k p • i j               ≈⟨ by-assoc auto ⟩
  i j • i k • (K j k p • X j k p) • i j               ≈⟨ cright cright cleft KX≈L²K p ⟩
  i j • i k • (i k ^ 2 • K j k p) • i j               ≈⟨ by-assoc auto ⟩
  i j • i k ^ 3 • K j k p • i j                       ≈⟨ cright sym (IKL³≈L³KI p) ⟩
  i j • i j • K j k p • i k ^ 3                       ≈⟨ by-assoc auto ⟩
  i j ^ 2 • (K j k p • i k ^ 2) • i k                 ≈⟨ cright cleft axiom (rel-13 p) ⟩
  i j ^ 2 • (X j k p • K j k p) • i k                 ≈⟨ by-assoc auto ⟩
  (i j ^ 2 • X j k p) • K j k p • i k                 ≈⟨ cleft conj-^ (IX≈XL p) 2 ⟩
  (X j k p • i k ^ 2) • K j k p • i k                 ≈⟨ by-assoc auto ⟩
  X j k p • ε • i k ^ 2 • K j k p • i k               ≈⟨ cright cleft sym i⁴ ⟩
  X j k p • i j ^ 4 • i k ^ 2 • K j k p • i k         ≈⟨ by-assoc auto ⟩
  X j k p • i j ^ 3 • (i j • i k) • i k • K j k p • i k   ≈⟨ cright cright cleft ii (<⇒≢ p) ⟩
  X j k p • i j ^ 3 • (i k • i j) • i k • K j k p • i k   ≈⟨ by-assoc auto ⟩
  X j k p • i j ^ 3 • i k • (i j • i k • K j k p) • i k   ≈⟨ cright cright cright cleft sym (K†≈iiK p) ⟩
  X j k p • i j ^ 3 • i k • K† j k p • i k            ∎

------------------------------------------------------------------------
-- Inverses of words
--
-- Every generator has an inverse: X⁻¹ = X, K⁻¹ = K† and i⁻¹ = i³.

grouplike : Grouplike (_===_ {n})
grouplike (X-gen a b p) = X a b p , X-X p
grouplike (K-gen a b p) = K† a b p , K†-K p
grouplike (i-gen a)     = i a ^ 3 , i³-i

open Group-Lemmas (_===_ {n}) grouplike public
  using (_⁻¹ ; inverseˡ ; inverseʳ ; •-cancelˡ ; •-cancelʳ ; ⁻¹-cong)

-- An X-conjugation read backwards: A X = X B gives B X = X A.
flip-X : ∀ {A B : Word (Gen n)} .(p : j < k) →
         A • X j k p ≈ X j k p • B → B • X j k p ≈ X j k p • A
flip-X {A = A} {B} p h = begin
  B • X′                        ≈⟨ sym left-unit ⟩
  ε • B • X′                    ≈⟨ cleft sym (X-X p) ⟩
  (X′ • X′) • B • X′            ≈⟨ assoc ⟩
  X′ • X′ • B • X′              ≈⟨ cright sym assoc ⟩
  X′ • (X′ • B) • X′            ≈⟨ cright cleft sym h ⟩
  X′ • (A • X′) • X′            ≈⟨ cright assoc ⟩
  X′ • A • (X′ • X′)            ≈⟨ cright cright X-X p ⟩
  X′ • A • ε                    ≈⟨ cright right-unit ⟩
  X′ • A                        ∎
  where X′ = X _ _ p

------------------------------------------------------------------------
-- Figure 2, continued: four indices j < l < j′ < l′
--
-- X_[l,j′] commutes with K†_[l,l′] K†_[j,j′] K†_[j′,l′] K†_[j,l]: it
-- swaps l and j′, which turns this word into the inverse of the other
-- side of (17).

module _ {j l j′ l′ : Fin n} (p₁ : j < l) (p₂ : l < j′) (p₃ : j′ < l′) where

  private
    jj′ = FinP.<-trans p₁ p₂
    ll′ = FinP.<-trans p₂ p₃
    X′ = X l j′ p₂
    Kjl  = K† j l p₁
    Kjj′ = K† j j′ jj′
    Kll′ = K† l l′ ll′
    Kj′l′ = K† j′ l′ p₃

    -- The letters, conjugated by X_[l,j′].
    swap-jj′ : Kjj′ • X′ ≈ X′ • Kjl
    swap-jj′ = conj-^ (axiom (swap-KX′ p₁ p₂)) 7

    swap-j′l′ : Kj′l′ • X′ ≈ X′ • Kll′
    swap-j′l′ = conj-^ (axiom (swap-KX p₂ p₃)) 7

    swap-jl : Kjl • X′ ≈ X′ • Kjj′
    swap-jl = conj-^ (flip-X p₂ (axiom (swap-KX′ p₁ p₂))) 7

    swap-ll′ : Kll′ • X′ ≈ X′ • Kj′l′
    swap-ll′ = conj-^ (flip-X p₂ (axiom (swap-KX p₂ p₃))) 7

    -- (17), inverted.
    rel-17⁻¹ : Kj′l′ • Kjl • Kll′ • Kjj′ ≈ Kll′ • Kjj′ • Kj′l′ • Kjl
    rel-17⁻¹ = by-assoc-and (sym (⁻¹-cong (axiom (rel-17 p₁ p₃ jj′ ll′ (<⇒≢ p₂))))) auto auto

  K†⁴X≈XK†⁴ : Kll′ • Kjj′ • Kj′l′ • Kjl • X′ ≈ X′ • Kll′ • Kjj′ • Kj′l′ • Kjl
  K†⁴X≈XK†⁴ = begin
    Kll′ • Kjj′ • Kj′l′ • Kjl • X′        ≈⟨ cright cright cright swap-jl ⟩
    Kll′ • Kjj′ • Kj′l′ • X′ • Kjj′       ≈⟨ by-assoc auto ⟩
    Kll′ • Kjj′ • (Kj′l′ • X′) • Kjj′     ≈⟨ cright cright cleft swap-j′l′ ⟩
    Kll′ • Kjj′ • (X′ • Kll′) • Kjj′      ≈⟨ by-assoc auto ⟩
    Kll′ • (Kjj′ • X′) • Kll′ • Kjj′      ≈⟨ cright cleft swap-jj′ ⟩
    Kll′ • (X′ • Kjl) • Kll′ • Kjj′       ≈⟨ by-assoc auto ⟩
    (Kll′ • X′) • Kjl • Kll′ • Kjj′       ≈⟨ cleft swap-ll′ ⟩
    (X′ • Kj′l′) • Kjl • Kll′ • Kjj′      ≈⟨ assoc ⟩
    X′ • Kj′l′ • Kjl • Kll′ • Kjj′        ≈⟨ cright rel-17⁻¹ ⟩
    X′ • Kll′ • Kjj′ • Kj′l′ • Kjl        ∎

------------------------------------------------------------------------
-- Generators with disjoint indices commute ((4)–(9)), and so do words

-- The indices a generator acts on.
idx : Gen n → List (Fin n)
idx (X-gen a b _) = a ∷ b ∷ []
idx (K-gen a b _) = a ∷ b ∷ []
idx (i-gen a)     = a ∷ []

Apart : Gen n → Gen n → Set
Apart g h = All (λ x → All (x ≢_) (idx h)) (idx g)

comm-gen : (g h : Gen n) → Apart g h → [ g ]ʷ • [ h ]ʷ ≈ [ h ]ʷ • [ g ]ʷ
comm-gen (i-gen a) (i-gen c) ((ac ∷ []) ∷ []) = axiom (comm-ii ac)
comm-gen (i-gen a) (X-gen c d q) ((ac ∷ ad ∷ []) ∷ []) = axiom (comm-iX q ac ad)
comm-gen (i-gen a) (K-gen c d q) ((ac ∷ ad ∷ []) ∷ []) = axiom (comm-iK q ac ad)
comm-gen (X-gen a b p) (i-gen c) ((ac ∷ []) ∷ (bc ∷ []) ∷ []) =
  sym (axiom (comm-iX p (≢-sym ac) (≢-sym bc)))
comm-gen (X-gen a b p) (X-gen c d q) ((ac ∷ ad ∷ []) ∷ (bc ∷ bd ∷ []) ∷ []) =
  axiom (comm-XX p q ac ad bc bd)
comm-gen (X-gen a b p) (K-gen c d q) ((ac ∷ ad ∷ []) ∷ (bc ∷ bd ∷ []) ∷ []) =
  axiom (comm-XK p q ac ad bc bd)
comm-gen (K-gen a b p) (i-gen c) ((ac ∷ []) ∷ (bc ∷ []) ∷ []) =
  sym (axiom (comm-iK p (≢-sym ac) (≢-sym bc)))
comm-gen (K-gen a b p) (X-gen c d q) ((ac ∷ ad ∷ []) ∷ (bc ∷ bd ∷ []) ∷ []) =
  sym (axiom (comm-XK q p (≢-sym ac) (≢-sym bc) (≢-sym ad) (≢-sym bd)))
comm-gen (K-gen a b p) (K-gen c d q) ((ac ∷ ad ∷ []) ∷ (bc ∷ bd ∷ []) ∷ []) =
  axiom (comm-KK p q ac ad bc bd)

-- Every letter of u is apart from h.
Apartʷ : Word (Gen n) → Gen n → Set
Apartʷ [ g ]ʷ h = Apart g h
Apartʷ ε h = ⊤
Apartʷ (u • v) h = Apartʷ u h × Apartʷ v h

comm-word : (u : Word (Gen n)) (h : Gen n) → Apartʷ u h → u • [ h ]ʷ ≈ [ h ]ʷ • u
comm-word [ g ]ʷ h ap = comm-gen g h ap
comm-word ε h _ = trans left-unit (sym right-unit)
comm-word (u • v) h (au , av) = begin
  (u • v) • [ h ]ʷ      ≈⟨ assoc ⟩
  u • (v • [ h ]ʷ)      ≈⟨ cright comm-word v h av ⟩
  u • ([ h ]ʷ • v)      ≈⟨ sym assoc ⟩
  (u • [ h ]ʷ) • v      ≈⟨ cleft comm-word u h au ⟩
  ([ h ]ʷ • u) • v      ≈⟨ assoc ⟩
  [ h ]ʷ • (u • v)      ∎

-- Every letter of u is apart from every letter of v.
Apartʷʷ : Word (Gen n) → Word (Gen n) → Set
Apartʷʷ u [ h ]ʷ = Apartʷ u h
Apartʷʷ u ε = ⊤
Apartʷʷ u (v • v′) = Apartʷʷ u v × Apartʷʷ u v′

comm-words : (u v : Word (Gen n)) → Apartʷʷ u v → u • v ≈ v • u
comm-words u [ h ]ʷ ap = comm-word u h ap
comm-words u ε _ = trans right-unit (sym left-unit)
comm-words u (v • v′) (a , a′) = begin
  u • (v • v′)          ≈⟨ sym assoc ⟩
  (u • v) • v′          ≈⟨ cleft comm-words u v a ⟩
  (v • u) • v′          ≈⟨ assoc ⟩
  v • (u • v′)          ≈⟨ cright comm-words u v′ a′ ⟩
  v • (v′ • u)          ≈⟨ sym assoc ⟩
  (v • v′) • u          ∎

------------------------------------------------------------------------
-- The basic generators (Lemma 3.3): X_[j,j+1], K_[0,1] and i_[0]
-- give the others by conjugation.

-- A X = X B gives B = X A X.
conj-X : ∀ {A B : Word (Gen n)} .(p : j < k) → A • X j k p ≈ X j k p • B → B ≈ X j k p • A • X j k p
conj-X {A = A} {B} p h = begin
  B                       ≈⟨ sym left-unit ⟩
  ε • B                   ≈⟨ cleft sym (X-X p) ⟩
  (X′ • X′) • B           ≈⟨ assoc ⟩
  X′ • (X′ • B)           ≈⟨ cright sym h ⟩
  X′ • (A • X′)           ∎
  where X′ = X _ _ p

-- A X = X B gives A = X B X.
conj-X′ : ∀ {A B : Word (Gen n)} .(p : j < k) → A • X j k p ≈ X j k p • B → A ≈ X j k p • B • X j k p
conj-X′ {A = A} {B} p h = begin
  A                       ≈⟨ sym right-unit ⟩
  A • ε                   ≈⟨ cright sym (X-X p) ⟩
  A • (X′ • X′)           ≈⟨ sym assoc ⟩
  (A • X′) • X′           ≈⟨ cleft h ⟩
  (X′ • B) • X′           ≈⟨ assoc ⟩
  X′ • B • X′             ∎
  where X′ = X _ _ p

-- i_[k] = X_[j,k] i_[j] X_[j,k]
i≈XiX : .(p : j < k) → i k ≈ X j k p • i j • X j k p
i≈XiX p = conj-X′ p (axiom (swap-iX p))

-- K_[k,l] = X_[j,k] K_[j,l] X_[j,k]
K≈XKX : (p : j < k) (q : k < l) → K k l q ≈ X j k p • K j l (FinP.<-trans p q) • X j k p
K≈XKX p q = conj-X′ p (axiom (swap-KX p q))

-- K_[j,l] = X_[k,l] K_[j,k] X_[k,l]
K≈XKX′ : (p : j < k) (q : k < l) → K j l (FinP.<-trans p q) ≈ X k l q • K j k p • X k l q
K≈XKX′ p q = conj-X′ q (axiom (swap-KX′ p q))

-- X_[j,l] = X_[j,k] X_[k,l] X_[j,k]
X≈XXX : (p : j < k) (q : k < l) → X j l (FinP.<-trans p q) ≈ X j k p • X k l q • X j k p
X≈XXX p q = conj-X p (axiom (swap-XX p q))

------------------------------------------------------------------------
-- Exponents of i, taken modulo 4

i^-+ : ∀ e f → i j ^ e • i j ^ f ≈ i j ^ (e ℕ.+ f)
i^-+ {j} e f = sym (^-+ (i j) e f)

i^+4 : ∀ e → i j ^ (e ℕ.+ 4) ≈ i j ^ e
i^+4 {j} e = begin
  i j ^ (e ℕ.+ 4)        ≈⟨ ^-+ (i j) e 4 ⟩
  i j ^ e • i j ^ 4      ≈⟨ cright i⁴ ⟩
  i j ^ e • ε            ≈⟨ right-unit ⟩
  i j ^ e                ∎

------------------------------------------------------------------------
-- (q″): K†_[j,k] i_[k]² = X_[j,k] K†_[j,k], from K X = i_[k]² K

K†L²≈XK† : .(p : j < k) → K† j k p • i k ^ 2 ≈ X j k p • K† j k p
K†L²≈XK† {j} {k} p = begin
  K† j k p • i k ^ 2                              ≈⟨ sym right-unit ⟩
  (K† j k p • i k ^ 2) • ε                        ≈⟨ cright sym (K-K† p) ⟩
  (K† j k p • i k ^ 2) • (K j k p • K† j k p)     ≈⟨ by-assoc auto ⟩
  K† j k p • (i k ^ 2 • K j k p) • K† j k p       ≈⟨ cright cleft sym (KX≈L²K p) ⟩
  K† j k p • (K j k p • X j k p) • K† j k p       ≈⟨ by-assoc auto ⟩
  (K† j k p • K j k p) • X j k p • K† j k p       ≈⟨ cleft K†-K p ⟩
  ε • X j k p • K† j k p                          ≈⟨ left-unit ⟩
  X j k p • K† j k p                              ∎
