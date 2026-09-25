------------------------------------------------------------------------
-- Presentations of groups
--
-- Consequences of the relations of Table 1: the inverses of the
-- generators, commutation of words with disjoint indices, the
-- conjugations by X that give the basic generators (Lemma 3.8), and
-- the relations of Table 2 (Lemma 3.6) that the proof of the Main
-- Lemma uses.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Derived {n : ℕ} where

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
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  variable
    j k l : Fin n

  <⇒≢ : .(j < k) → j ≢ k
  <⇒≢ {j = j} {k} p j≡k = FinP.<-irrefl j≡k (recompute (j FinP.<? k) p)

  >⇒≢ : .(j < k) → k ≢ j
  >⇒≢ p e = <⇒≢ p (≡-sym e)

  -- Generators with distinct indices ω_[j], ω_[k] commute.
  ωω : j ≢ k → ω j • ω k ≈ ω k • ω j
  ωω j≢k = axiom (comm-ωω j≢k)

------------------------------------------------------------------------
-- Orders and inverses

ω⁸ : ω j ^ 8 ≈ ε
ω⁸ = axiom order-ω

ω-ω⁷ : ω j • ω j ^ 7 ≈ ε
ω-ω⁷ = ω⁸

ω⁷-ω : ω j ^ 7 • ω j ≈ ε
ω⁷-ω {j} = trans (sym (^-+ (ω j) 7 1)) ω⁸

X-X : .(p : j < k) → X j k p • X j k p ≈ ε
X-X p = axiom (order-X p)

H-H : .(p : j < k) → H j k p • H j k p ≈ ε
H-H p = axiom (order-H p)

grouplike : Grouplike (_===_ {n})
grouplike (X-gen a b p) = X a b p , X-X p
grouplike (H-gen a b p) = H a b p , H-H p
grouplike (ω-gen a)     = ω a ^ 7 , ω⁷-ω

open Group-Lemmas (_===_ {n}) grouplike public
  using (_⁻¹ ; inverseˡ ; inverseʳ ; •-cancelˡ ; •-cancelʳ ; ⁻¹-cong)

------------------------------------------------------------------------
-- Exponents of ω, taken modulo 8

ω^-+ : ∀ e f → ω j ^ e • ω j ^ f ≈ ω j ^ (e ℕ.+ f)
ω^-+ {j} e f = sym (^-+ (ω j) e f)

ω^+8 : ∀ e → ω j ^ (e ℕ.+ 8) ≈ ω j ^ e
ω^+8 {j} e = begin
  ω j ^ (e ℕ.+ 8)        ≈⟨ ^-+ (ω j) e 8 ⟩
  ω j ^ e • ω j ^ 8      ≈⟨ cright ω⁸ ⟩
  ω j ^ e • ε            ≈⟨ right-unit ⟩
  ω j ^ e                ∎

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
-- Conjugation by X

-- A X = X B gives B X = X A.
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

------------------------------------------------------------------------
-- X_[j,k] and the ω's: (10) and (11) read both ways

-- ω_[k] X = X ω_[j], and ω_[j] X = X ω_[k].
ωX≈Xω : .(p : j < k) → ω k • X j k p ≈ X j k p • ω j
ωX≈Xω p = sym (axiom (swap-Xω′ p))

ωX≈Xω′ : .(p : j < k) → ω j • X j k p ≈ X j k p • ω k
ωX≈Xω′ p = sym (axiom (swap-Xω p))

------------------------------------------------------------------------
-- The basic generators (Lemma 3.8): X_[j,j+1], H_[0,1] and ω_[0]
-- give the others by conjugation.

-- ω_[k] = X_[j,k] ω_[j] X_[j,k]
ω≈XωX : .(p : j < k) → ω k ≈ X j k p • ω j • X j k p
ω≈XωX p = conj-X′ p (ωX≈Xω p)

-- H_[k,l] = X_[j,k] H_[j,l] X_[j,k]
H≈XHX : .(p : j < k) .(q : k < l) → H k l q ≈ X j k p • H j l (FinP.<-trans p q) • X j k p
H≈XHX p q = conj-X′ p (sym (axiom (swap-XH p q)))

-- H_[j,l] = X_[k,l] H_[j,k] X_[k,l]
H≈XHX′ : .(p : j < k) .(q : k < l) → H j l (FinP.<-trans p q) ≈ X k l q • H j k p • X k l q
H≈XHX′ p q = conj-X′ q (sym (axiom (swap-XH′ p q)))

-- X_[j,l] = X_[j,k] X_[k,l] X_[j,k]
X≈XXX : .(p : j < k) .(q : k < l) → X j l (FinP.<-trans p q) ≈ X j k p • X k l q • X j k p
X≈XXX p q = conj-X p (sym (axiom (swap-XX p q)))

------------------------------------------------------------------------
-- Table 2: (p), (o) and (m), the inverses of (14), (15) and (18)

-- (p) H_[j,l] X_[j,k] = X_[j,k] H_[k,l]
HX≈XH : .(p : j < k) .(q : k < l) → H j l (FinP.<-trans p q) • X j k p ≈ X j k p • H k l q
HX≈XH p q = flip-X p (sym (axiom (swap-XH p q)))

-- (o) H_[l,j] X_[j,k] = X_[j,k] H_[l,k]
HX≈XH′ : .(p : l < j) .(q : j < k) → H l j p • X j k q ≈ X j k q • H l k (FinP.<-trans p q)
HX≈XH′ p q = flip-X q (sym (axiom (swap-XH′ p q)))

-- (m) X_[j,k] H_[j,k] = H_[j,k] ω_[k]⁴
XH≈Hω⁴ : .(p : j < k) → X j k p • H j k p ≈ H j k p • ω k ^ 4
XH≈Hω⁴ {j} {k} p = begin
  X′ • H′                             ≈⟨ sym left-unit ⟩
  ε • X′ • H′                         ≈⟨ cleft sym (H-H p) ⟩
  (H′ • H′) • X′ • H′                 ≈⟨ by-assoc auto ⟩
  H′ • (H′ • X′) • H′                 ≈⟨ cright cleft axiom (rel-18 p) ⟩
  H′ • (ω k ^ 4 • H′) • H′            ≈⟨ by-assoc auto ⟩
  H′ • ω k ^ 4 • (H′ • H′)            ≈⟨ cright cright H-H p ⟩
  H′ • ω k ^ 4 • ε                    ≈⟨ cright right-unit ⟩
  H′ • ω k ^ 4                        ∎
  where
  X′ = X j k p
  H′ = H j k p

------------------------------------------------------------------------
-- Generators with disjoint indices commute ((4)–(9)), and so do words

-- The indices a generator acts on.
idx : Gen n → List (Fin n)
idx (X-gen a b _) = a ∷ b ∷ []
idx (H-gen a b _) = a ∷ b ∷ []
idx (ω-gen a)     = a ∷ []

Apart : Gen n → Gen n → Set
Apart g h = All (λ x → All (x ≢_) (idx h)) (idx g)

comm-gen : (g h : Gen n) → Apart g h → [ g ]ʷ • [ h ]ʷ ≈ [ h ]ʷ • [ g ]ʷ
comm-gen (ω-gen a) (ω-gen c) ((ac ∷ []) ∷ []) = axiom (comm-ωω ac)
comm-gen (ω-gen a) (X-gen c d q) ((ac ∷ ad ∷ []) ∷ []) = axiom (comm-ωX q ac ad)
comm-gen (ω-gen a) (H-gen c d q) ((ac ∷ ad ∷ []) ∷ []) = axiom (comm-ωH q ac ad)
comm-gen (X-gen a b p) (ω-gen c) ((ac ∷ []) ∷ (bc ∷ []) ∷ []) =
  sym (axiom (comm-ωX p (≢-sym ac) (≢-sym bc)))
comm-gen (X-gen a b p) (X-gen c d q) ((ac ∷ ad ∷ []) ∷ (bc ∷ bd ∷ []) ∷ []) =
  axiom (comm-XX p q ac ad bc bd)
comm-gen (X-gen a b p) (H-gen c d q) ((ac ∷ ad ∷ []) ∷ (bc ∷ bd ∷ []) ∷ []) =
  sym (axiom (comm-HX q p (≢-sym ac) (≢-sym bc) (≢-sym ad) (≢-sym bd)))
comm-gen (H-gen a b p) (ω-gen c) ((ac ∷ []) ∷ (bc ∷ []) ∷ []) =
  sym (axiom (comm-ωH p (≢-sym ac) (≢-sym bc)))
comm-gen (H-gen a b p) (X-gen c d q) ((ac ∷ ad ∷ []) ∷ (bc ∷ bd ∷ []) ∷ []) =
  axiom (comm-HX p q ac ad bc bd)
comm-gen (H-gen a b p) (H-gen c d q) ((ac ∷ ad ∷ []) ∷ (bc ∷ bd ∷ []) ∷ []) =
  axiom (comm-HH p q ac ad bc bd)

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
-- H_[j,k] ω_[j]⁴ = ω_[j]⁴ ω_[k]⁴ X_[j,k] H_[j,k]
--
-- (The thesis, Case 2, writes X_[j,k] H_[j,k]: that is (m) with ω⁴ on
-- k, and differs from H ω_[j]⁴ by the sign ω_[j]⁴ ω_[k]⁴.)  From (m),
-- and (17): ω_[j] ω_[k] is a scalar on the indices j and k.

Hω⁴≈ω⁴ω⁴XH : .(p : j < k) → H j k p • ω j ^ 4 ≈ ω j ^ 4 • ω k ^ 4 • X j k p • H j k p
Hω⁴≈ω⁴ω⁴XH {j} {k} p = begin
  H′ • ω j ^ 4                                  ≈⟨ sym right-unit ⟩
  (H′ • ω j ^ 4) • ε                            ≈⟨ cright sym ω⁸ ⟩
  (H′ • ω j ^ 4) • ω k ^ 8                      ≈⟨ cright ^-+ (ω k) 4 4 ⟩
  (H′ • ω j ^ 4) • (ω k ^ 4 • ω k ^ 4)          ≈⟨ by-assoc auto ⟩
  H′ • (ω j ^ 4 • ω k ^ 4) • ω k ^ 4            ≈⟨ cright cleft sym (^-• (ω j) (ω k) 4 jk) ⟩
  H′ • (ω j • ω k) ^ 4 • ω k ^ 4                ≈⟨ sym assoc ⟩
  (H′ • (ω j • ω k) ^ 4) • ω k ^ 4              ≈⟨ cleft sym (conj-^ sc 4) ⟩
  ((ω j • ω k) ^ 4 • H′) • ω k ^ 4              ≈⟨ assoc ⟩
  (ω j • ω k) ^ 4 • (H′ • ω k ^ 4)              ≈⟨ cright sym (XH≈Hω⁴ p) ⟩
  (ω j • ω k) ^ 4 • (X′ • H′)                   ≈⟨ cleft ^-• (ω j) (ω k) 4 jk ⟩
  (ω j ^ 4 • ω k ^ 4) • (X′ • H′)               ≈⟨ by-assoc auto ⟩
  ω j ^ 4 • ω k ^ 4 • X′ • H′                   ∎
  where
  H′ = H j k p
  X′ = X j k p
  jk : ω j • ω k ≈ ω k • ω j
  jk = ωω (<⇒≢ p)
  sc : (ω j • ω k) • H′ ≈ H′ • (ω j • ω k)
  sc = trans assoc (axiom (scalar-H p))

------------------------------------------------------------------------
-- Table 2, (r): H_[j,k] ω_[j]² H_[j,k] = X_[j,k] ω_[k]⁷ ω_[j] H_[j,k] ω_[j]²
--
-- Both sides are ω_[j] ω_[k]³ H_[j,k] ω_[k]², moving the scalars
-- (ω_[j] ω_[k])ᵉ through H by (17).

private
  -- Powers of ω_[j] and ω_[k] commute.
  ωω^ : j ≢ k → ∀ e f → ω j ^ e • ω k ^ f ≈ ω k ^ f • ω j ^ e
  ωω^ jk e f = comm⇒pow-comm e f (ωω jk)

  -- (ω_[j] ω_[k])ᵉ commutes with H_[j,k].
  scH^ : .(p : j < k) → ∀ e → (ω j • ω k) ^ e • H j k p ≈ H j k p • (ω j • ω k) ^ e
  scH^ p e = conj-^ (trans assoc (axiom (scalar-H p))) e

  -- H_[j,k] ω_[j]² = ω_[j]² ω_[k]² H_[j,k] ω_[k]⁶.
  Hω²ⱼ : .(p : j < k) → H j k p • ω j ^ 2 ≈ ω j ^ 2 • ω k ^ 2 • H j k p • ω k ^ 6
  Hω²ⱼ {j} {k} p = begin
    H′ • ω j ^ 2                                  ≈⟨ cright sym (trans (cright ω⁸) right-unit) ⟩
    H′ • (ω j ^ 2 • ω k ^ 8)                      ≈⟨ by-assoc auto ⟩
    H′ • (ω j ^ 2 • ω k ^ 2) • ω k ^ 6            ≈⟨ cright cleft sym (^-• (ω j) (ω k) 2 (ωω (<⇒≢ p))) ⟩
    H′ • (ω j • ω k) ^ 2 • ω k ^ 6                ≈⟨ sym assoc ⟩
    (H′ • (ω j • ω k) ^ 2) • ω k ^ 6              ≈⟨ cleft sym (scH^ p 2) ⟩
    ((ω j • ω k) ^ 2 • H′) • ω k ^ 6              ≈⟨ cleft cleft ^-• (ω j) (ω k) 2 (ωω (<⇒≢ p)) ⟩
    ((ω j ^ 2 • ω k ^ 2) • H′) • ω k ^ 6          ≈⟨ by-assoc auto ⟩
    ω j ^ 2 • ω k ^ 2 • H′ • ω k ^ 6              ∎
    where H′ = H j k p

  -- The left side.
  rL : .(p : j < k) → H j k p • ω j ^ 2 • H j k p ≈ ω j • ω k ^ 3 • H j k p • ω k ^ 2
  rL {j} {k} p = begin
    H′ • ω j ^ 2 • H′                                        ≈⟨ axiom (rel-19 p) ⟩
    ω j ^ 6 • H′ • ω j ^ 3 • ω k ^ 5                         ≈⟨ by-assoc auto ⟩
    ω j ^ 6 • H′ • (ω j ^ 3 • ω k ^ 3) • ω k ^ 2             ≈⟨ cright cright cleft sym (^-• (ω j) (ω k) 3 (ωω (<⇒≢ p))) ⟩
    ω j ^ 6 • H′ • (ω j • ω k) ^ 3 • ω k ^ 2                 ≈⟨ cright sym assoc ⟩
    ω j ^ 6 • (H′ • (ω j • ω k) ^ 3) • ω k ^ 2               ≈⟨ cright cleft sym (scH^ p 3) ⟩
    ω j ^ 6 • ((ω j • ω k) ^ 3 • H′) • ω k ^ 2               ≈⟨ cright cleft cleft ^-• (ω j) (ω k) 3 (ωω (<⇒≢ p)) ⟩
    ω j ^ 6 • ((ω j ^ 3 • ω k ^ 3) • H′) • ω k ^ 2           ≈⟨ by-assoc auto ⟩
    ω j ^ 9 • ω k ^ 3 • H′ • ω k ^ 2                         ≈⟨ cleft ω^+8 1 ⟩
    ω j • ω k ^ 3 • H′ • ω k ^ 2                             ∎
    where H′ = H j k p

  -- The right side.
  rR : .(p : j < k) → X j k p • ω k ^ 7 • ω j • H j k p • ω j ^ 2 ≈ ω j • ω k ^ 3 • H j k p • ω k ^ 2
  rR {j} {k} p = begin
    X′ • ω k ^ 7 • ω j • H′ • ω j ^ 2                              ≈⟨ cright cright cright Hω²ⱼ p ⟩
    X′ • ω k ^ 7 • ω j • ω j ^ 2 • ω k ^ 2 • H′ • ω k ^ 6          ≈⟨ by-assoc auto ⟩
    X′ • (ω k ^ 7 • ω j ^ 3) • ω k ^ 2 • H′ • ω k ^ 6              ≈⟨ cright cleft ωω^ (>⇒≢ p) 7 3 ⟩
    X′ • (ω j ^ 3 • ω k ^ 7) • ω k ^ 2 • H′ • ω k ^ 6              ≈⟨ by-assoc auto ⟩
    (X′ • ω j ^ 3) • ω k ^ 9 • H′ • ω k ^ 6                        ≈⟨ cong (sym (conj-^ (ωX≈Xω p) 3)) (cleft ω^+8 1) ⟩
    (ω k ^ 3 • X′) • ω k • H′ • ω k ^ 6                            ≈⟨ by-assoc auto ⟩
    ω k ^ 3 • (X′ • ω k) • H′ • ω k ^ 6                            ≈⟨ cright cleft axiom (swap-Xω p) ⟩
    ω k ^ 3 • (ω j • X′) • H′ • ω k ^ 6                            ≈⟨ by-assoc auto ⟩
    ω k ^ 3 • ω j • (X′ • H′) • ω k ^ 6                            ≈⟨ cright cright cleft XH≈Hω⁴ p ⟩
    ω k ^ 3 • ω j • (H′ • ω k ^ 4) • ω k ^ 6                       ≈⟨ by-assoc auto ⟩
    (ω k ^ 3 • ω j) • H′ • ω k ^ 10                                ≈⟨ cong (ωω^ (>⇒≢ p) 3 1) (cright ω^+8 2) ⟩
    (ω j • ω k ^ 3) • H′ • ω k ^ 2                                 ≈⟨ assoc ⟩
    ω j • ω k ^ 3 • H′ • ω k ^ 2                                   ∎
    where
    X′ = X j k p
    H′ = H j k p

Hω²H≈Xω⁷ωHω² : .(p : j < k) → H j k p • ω j ^ 2 • H j k p ≈ X j k p • ω k ^ 7 • ω j • H j k p • ω j ^ 2
Hω²H≈Xω⁷ωHω² p = trans (rL p) (sym (rR p))

------------------------------------------------------------------------
-- Table 2, (z₁)–(z₃): H_[j,k] ω_[j]ᵉ X_[j,k] = ω_[j]^(4+e) ω_[k]ᵉ X_[j,k] H_[j,k] ω_[j]^(4-e)
--
-- H ω_[j]ᵉ X = ω_[k]⁴ H ω_[k]ᵉ = ω_[k]⁴ X H ω_[k]^(4+e) by (10), (18)
-- and (m); then ω_[k]^(4+e) = (ω_[j] ω_[k])^(4+e) ω_[j]^(4-e), whose
-- scalar part moves out through H and X by (16) and (17).

private
  -- (ω_[j] ω_[k])ᵉ commutes with X_[j,k].
  scX^ : .(p : j < k) → ∀ e → (ω j • ω k) ^ e • X j k p ≈ X j k p • (ω j • ω k) ^ e
  scX^ p e = conj-^ (trans assoc (axiom (scalar-X p))) e

  -- H = X H ω_[k]⁴.
  H≈XHω⁴ : .(p : j < k) → H j k p ≈ X j k p • (H j k p • ω k ^ 4)
  H≈XHω⁴ p = trans (sym left-unit) (trans (cleft sym (X-X p)) (trans assoc (cright XH≈Hω⁴ p)))

  -- The scalar part moves out: X H (ω_[j]ᵐ ω_[k]ᵐ) ω_[j]ᶠ = ω_[j]ᵐ ω_[k]ᵐ X H ω_[j]ᶠ.
  sc-out : .(p : j < k) → ∀ m f →
           X j k p • H j k p • (ω j ^ m • ω k ^ m) • ω j ^ f ≈ (ω j ^ m • ω k ^ m) • X j k p • H j k p • ω j ^ f
  sc-out {j} {k} p m f = begin
    X′ • H′ • (ω j ^ m • ω k ^ m) • ω j ^ f        ≈⟨ cright cright cleft sym (^-• (ω j) (ω k) m jk) ⟩
    X′ • H′ • (ω j • ω k) ^ m • ω j ^ f            ≈⟨ cright sym assoc ⟩
    X′ • (H′ • (ω j • ω k) ^ m) • ω j ^ f          ≈⟨ cright cleft sym (scH^ p m) ⟩
    X′ • ((ω j • ω k) ^ m • H′) • ω j ^ f          ≈⟨ cright assoc ⟩
    X′ • (ω j • ω k) ^ m • H′ • ω j ^ f            ≈⟨ sym assoc ⟩
    (X′ • (ω j • ω k) ^ m) • H′ • ω j ^ f          ≈⟨ cleft sym (scX^ p m) ⟩
    ((ω j • ω k) ^ m • X′) • H′ • ω j ^ f          ≈⟨ assoc ⟩
    (ω j • ω k) ^ m • X′ • H′ • ω j ^ f            ≈⟨ cleft ^-• (ω j) (ω k) m jk ⟩
    (ω j ^ m • ω k ^ m) • X′ • H′ • ω j ^ f        ∎
    where
    X′ = X j k p
    H′ = H j k p
    jk = ωω (<⇒≢ p)

  -- H ω_[j]ᵉ X = ω_[k]⁴ X H ω_[k]⁴ ω_[k]ᵉ.
  HωX-core : .(p : j < k) → ∀ e → H j k p • ω j ^ e • X j k p ≈ ω k ^ 4 • X j k p • H j k p • ω k ^ 4 • ω k ^ e
  HωX-core {j} {k} p e = begin
    H′ • ω j ^ e • X′                                  ≈⟨ cright conj-^ (ωX≈Xω′ p) e ⟩
    H′ • X′ • ω k ^ e                                  ≈⟨ sym assoc ⟩
    (H′ • X′) • ω k ^ e                                ≈⟨ cleft axiom (rel-18 p) ⟩
    (ω k ^ 4 • H′) • ω k ^ e                           ≈⟨ cleft cright H≈XHω⁴ p ⟩
    (ω k ^ 4 • X′ • H′ • ω k ^ 4) • ω k ^ e            ≈⟨ assoc ⟩
    ω k ^ 4 • ((X′ • H′ • ω k ^ 4) • ω k ^ e)          ≈⟨ cright assoc ⟩
    ω k ^ 4 • X′ • ((H′ • ω k ^ 4) • ω k ^ e)          ≈⟨ cright cright assoc ⟩
    ω k ^ 4 • X′ • H′ • ω k ^ 4 • ω k ^ e              ∎
    where
    X′ = X j k p
    H′ = H j k p

-- (z₁): H ω_[j]³ X = ω_[j]⁷ ω_[k]³ X H ω_[j].
Hω³X : .(p : j < k) → H j k p • ω j ^ 3 • X j k p ≈ ω j ^ 7 • ω k ^ 3 • X j k p • H j k p • ω j
Hω³X {j} {k} p = begin
  H′ • ω j ^ 3 • X′                                      ≈⟨ HωX-core p 3 ⟩
  ω k ^ 4 • X′ • H′ • ω k ^ 4 • ω k ^ 3                  ≈⟨ cright cright cright sym (trans (cleft ω⁸) left-unit) ⟩
  ω k ^ 4 • X′ • H′ • ω j ^ 8 • ω k ^ 4 • ω k ^ 3        ≈⟨ cright cright cright by-assoc auto ⟩
  ω k ^ 4 • X′ • H′ • ω j ^ 7 • (ω j • ω k ^ 7)          ≈⟨ cright cright cright cright ωω^ (<⇒≢ p) 1 7 ⟩
  ω k ^ 4 • X′ • H′ • ω j ^ 7 • (ω k ^ 7 • ω j)          ≈⟨ cright by-assoc auto ⟩
  ω k ^ 4 • X′ • H′ • (ω j ^ 7 • ω k ^ 7) • ω j          ≈⟨ cright sc-out p 7 1 ⟩
  ω k ^ 4 • (ω j ^ 7 • ω k ^ 7) • X′ • H′ • ω j          ≈⟨ by-assoc auto ⟩
  (ω k ^ 4 • ω j ^ 7) • ω k ^ 7 • X′ • H′ • ω j          ≈⟨ cleft ωω^ (>⇒≢ p) 4 7 ⟩
  (ω j ^ 7 • ω k ^ 4) • ω k ^ 7 • X′ • H′ • ω j          ≈⟨ by-assoc auto ⟩
  ω j ^ 7 • ω k ^ 11 • X′ • H′ • ω j                     ≈⟨ cright cleft ω^+8 3 ⟩
  ω j ^ 7 • ω k ^ 3 • X′ • H′ • ω j                      ∎
  where
  X′ = X j k p
  H′ = H j k p

-- (z₂): H ω_[j]² X = ω_[j]⁶ ω_[k]² X H ω_[j]².
Hω²X : .(p : j < k) → H j k p • ω j ^ 2 • X j k p ≈ ω j ^ 6 • ω k ^ 2 • X j k p • H j k p • ω j ^ 2
Hω²X {j} {k} p = begin
  H′ • ω j ^ 2 • X′                                      ≈⟨ HωX-core p 2 ⟩
  ω k ^ 4 • X′ • H′ • ω k ^ 4 • ω k ^ 2                  ≈⟨ cright cright cright sym (trans (cleft ω⁸) left-unit) ⟩
  ω k ^ 4 • X′ • H′ • ω j ^ 8 • ω k ^ 4 • ω k ^ 2        ≈⟨ cright cright cright by-assoc auto ⟩
  ω k ^ 4 • X′ • H′ • ω j ^ 6 • (ω j ^ 2 • ω k ^ 6)      ≈⟨ cright cright cright cright ωω^ (<⇒≢ p) 2 6 ⟩
  ω k ^ 4 • X′ • H′ • ω j ^ 6 • (ω k ^ 6 • ω j ^ 2)      ≈⟨ cright by-assoc auto ⟩
  ω k ^ 4 • X′ • H′ • (ω j ^ 6 • ω k ^ 6) • ω j ^ 2      ≈⟨ cright sc-out p 6 2 ⟩
  ω k ^ 4 • (ω j ^ 6 • ω k ^ 6) • X′ • H′ • ω j ^ 2      ≈⟨ by-assoc auto ⟩
  (ω k ^ 4 • ω j ^ 6) • ω k ^ 6 • X′ • H′ • ω j ^ 2      ≈⟨ cleft ωω^ (>⇒≢ p) 4 6 ⟩
  (ω j ^ 6 • ω k ^ 4) • ω k ^ 6 • X′ • H′ • ω j ^ 2      ≈⟨ by-assoc auto ⟩
  ω j ^ 6 • ω k ^ 10 • X′ • H′ • ω j ^ 2                 ≈⟨ cright cleft ω^+8 2 ⟩
  ω j ^ 6 • ω k ^ 2 • X′ • H′ • ω j ^ 2                  ∎
  where
  X′ = X j k p
  H′ = H j k p

-- (z₃): H ω_[j] X = ω_[j]⁵ ω_[k] X H ω_[j]³.
Hω¹X : .(p : j < k) → H j k p • ω j • X j k p ≈ ω j ^ 5 • ω k • X j k p • H j k p • ω j ^ 3
Hω¹X {j} {k} p = begin
  H′ • ω j • X′                                          ≈⟨ HωX-core p 1 ⟩
  ω k ^ 4 • X′ • H′ • ω k ^ 4 • ω k                      ≈⟨ cright cright cright sym (trans (cleft ω⁸) left-unit) ⟩
  ω k ^ 4 • X′ • H′ • ω j ^ 8 • ω k ^ 4 • ω k            ≈⟨ cright cright cright by-assoc auto ⟩
  ω k ^ 4 • X′ • H′ • ω j ^ 5 • (ω j ^ 3 • ω k ^ 5)      ≈⟨ cright cright cright cright ωω^ (<⇒≢ p) 3 5 ⟩
  ω k ^ 4 • X′ • H′ • ω j ^ 5 • (ω k ^ 5 • ω j ^ 3)      ≈⟨ cright by-assoc auto ⟩
  ω k ^ 4 • X′ • H′ • (ω j ^ 5 • ω k ^ 5) • ω j ^ 3      ≈⟨ cright sc-out p 5 3 ⟩
  ω k ^ 4 • (ω j ^ 5 • ω k ^ 5) • X′ • H′ • ω j ^ 3      ≈⟨ by-assoc auto ⟩
  (ω k ^ 4 • ω j ^ 5) • ω k ^ 5 • X′ • H′ • ω j ^ 3      ≈⟨ cleft ωω^ (>⇒≢ p) 4 5 ⟩
  (ω j ^ 5 • ω k ^ 4) • ω k ^ 5 • X′ • H′ • ω j ^ 3      ≈⟨ by-assoc auto ⟩
  ω j ^ 5 • ω k ^ 9 • X′ • H′ • ω j ^ 3                  ≈⟨ cright cleft ω^+8 1 ⟩
  ω j ^ 5 • ω k • X′ • H′ • ω j ^ 3                      ∎
  where
  X′ = X j k p
  H′ = H j k p

------------------------------------------------------------------------
-- Table 2, (s) and (t): four indices a < b < c < d
--
-- (s) H_[c,d] H_[a,b] X_[b,c] H_[a,b] H_[c,d] = H_[a,c] H_[b,d] X_[b,c] H_[b,d] H_[a,c]
-- (t) H_[c,d] H_[a,b] X_[b,c] H_[a,b] H_[c,d] = H_[b,c] H_[a,d] X_[b,d] H_[a,d] H_[b,c]
--
-- (s) is (20) with X_[b,c] passed through, by (14) and (15); (t) is
-- (s) conjugated by X_[c,d], after writing H_[c,d] = X_[c,d] H_[c,d]
-- ω_[d]⁴ by (18) and (m).

module _ {a b c d : Fin n} (ab : a < b) (bc : b < c) (cd : c < d) where

  private
    ac = FinP.<-trans ab bc
    bd = FinP.<-trans bc cd
    ad = FinP.<-trans ac cd
    a≢b = <⇒≢ ab
    a≢c = <⇒≢ ac
    a≢d = <⇒≢ ad
    b≢c = <⇒≢ bc
    b≢d = <⇒≢ bd
    c≢d = <⇒≢ cd
    Hab = H a b ab
    Hcd = H c d cd
    Hac = H a c ac
    Hbd = H b d bd
    Xbc = X b c bc

    -- Past a letter: x a = a′ x gives x (a r) = a′ (x r).
    pass : ∀ {x a′ a r : Word (Gen n)} → x • a ≈ a′ • x → x • (a • r) ≈ a′ • (x • r)
    pass h = trans (sym assoc) (trans (cleft h) assoc)

    -- X_[b,c] H_[a,b] H_[c,d] = H_[a,c] H_[b,d] X_[b,c].
    XHH : Xbc • (Hab • Hcd) ≈ (Hac • Hbd) • Xbc
    XHH = begin
      Xbc • (Hab • Hcd)            ≈⟨ pass (axiom (swap-XH′ ab bc)) ⟩
      Hac • (Xbc • Hcd)            ≈⟨ cright sym (HX≈XH bc cd) ⟩
      Hac • (Hbd • Xbc)            ≈⟨ sym assoc ⟩
      (Hac • Hbd) • Xbc            ∎

    -- H_[a,b] H_[c,d] X_[b,c] = X_[b,c] H_[a,c] H_[b,d].
    HHX : (Hab • Hcd) • Xbc ≈ Xbc • (Hac • Hbd)
    HHX = flip-X bc (sym XHH)

    commHH : ∀ {w x y z : Fin n} .(p : w < x) .(q : y < z) → w ≢ y → w ≢ z → x ≢ y → x ≢ z →
             H w x p • H y z q ≈ H y z q • H w x p
    commHH p q e₁ e₂ e₃ e₄ = axiom (comm-HH p q e₁ e₂ e₃ e₄)

  Hs : Hcd • Hab • Xbc • Hab • Hcd ≈ Hac • Hbd • Xbc • Hbd • Hac
  Hs = begin
    Hcd • Hab • Xbc • Hab • Hcd                    ≈⟨ cright cright XHH ⟩
    Hcd • Hab • ((Hac • Hbd) • Xbc)                ≈⟨ by-assoc auto ⟩
    (Hcd • Hab) • (Hac • Hbd) • Xbc                ≈⟨ cleft commHH cd ab (≢-sym a≢c) (≢-sym b≢c) (≢-sym a≢d) (≢-sym b≢d) ⟩
    (Hab • Hcd) • (Hac • Hbd) • Xbc                ≈⟨ by-assoc auto ⟩
    (Hab • Hcd • Hac • Hbd) • Xbc                  ≈⟨ cleft axiom (rel-20 ab bc cd) ⟩
    (Hac • Hbd • Hab • Hcd) • Xbc                  ≈⟨ by-assoc auto ⟩
    (Hac • Hbd) • ((Hab • Hcd) • Xbc)              ≈⟨ cright HHX ⟩
    (Hac • Hbd) • (Xbc • (Hac • Hbd))              ≈⟨ cright cright commHH ac bd a≢b a≢d (≢-sym b≢c) c≢d ⟩
    (Hac • Hbd) • (Xbc • (Hbd • Hac))              ≈⟨ by-assoc auto ⟩
    Hac • Hbd • Xbc • Hbd • Hac                    ∎

  Ht : Hcd • Hab • Xbc • Hab • Hcd ≈ H b c bc • H a d ad • X b d bd • H a d ad • H b c bc
  Ht = begin
    Hcd • Hab • Xbc • Hab • Hcd                    ≈⟨ sym right-unit ⟩
    (Hcd • Hab • Xbc • Hab • Hcd) • ε              ≈⟨ cright sym (X-X cd) ⟩
    (Hcd • Hab • Xbc • Hab • Hcd) • (Xcd • Xcd)    ≈⟨ by-assoc auto ⟩
    Hcd • M • (Hcd • Xcd) • Xcd                    ≈⟨ cright cright cleft axiom (rel-18 cd) ⟩
    Hcd • M • (ω d ^ 4 • Hcd) • Xcd                ≈⟨ cright sym assoc ⟩
    Hcd • (M • (ω d ^ 4 • Hcd)) • Xcd              ≈⟨ cright cleft sym assoc ⟩
    Hcd • ((M • ω d ^ 4) • Hcd) • Xcd              ≈⟨ cright cleft cleft sym (comm-words (ω d ^ 4) M apM) ⟩
    Hcd • ((ω d ^ 4 • M) • Hcd) • Xcd              ≈⟨ by-assoc auto ⟩
    (Hcd • ω d ^ 4) • M • Hcd • Xcd                ≈⟨ cleft sym (XH≈Hω⁴ cd) ⟩
    (Xcd • Hcd) • M • Hcd • Xcd                    ≈⟨ by-assoc auto ⟩
    Xcd • (Hcd • Hab • Xbc • Hab • Hcd) • Xcd      ≈⟨ cright cleft Hs ⟩
    Xcd • (Hac • Hbd • Xbc • Hbd • Hac) • Xcd      ≈⟨ cright cleft swap-ends ⟩
    Xcd • (Hbd • Hac • Xbc • Hac • Hbd) • Xcd      ≈⟨ sym assoc ⟩
    (Xcd • (Hbd • Hac • Xbc • Hac • Hbd)) • Xcd    ≈⟨ cleft conj ⟩
    ((Hbc • Had • Xbd • Had • Hbc) • Xcd) • Xcd    ≈⟨ assoc ⟩
    (Hbc • Had • Xbd • Had • Hbc) • (Xcd • Xcd)    ≈⟨ cright X-X cd ⟩
    (Hbc • Had • Xbd • Had • Hbc) • ε              ≈⟨ right-unit ⟩
    Hbc • Had • Xbd • Had • Hbc                    ∎
    where
    Xcd = X c d cd
    Hbc = H b c bc
    Had = H a d ad
    Xbd = X b d bd
    M = Hab • Xbc • Hab
    -- ω_[d] commutes with H_[a,b] and X_[b,c].
    apM : Apartʷʷ (ω d ^ 4) M
    apM = ap (H-gen a b ab) ((≢-sym a≢d ∷ ≢-sym b≢d ∷ []) ∷ []) ,
          (ap (X-gen b c bc) ((≢-sym b≢d ∷ ≢-sym c≢d ∷ []) ∷ []) ,
           ap (H-gen a b ab) ((≢-sym a≢d ∷ ≢-sym b≢d ∷ []) ∷ []))
      where
      ap : (g : Gen n) → Apart (ω-gen d) g → Apartʷ (ω d ^ 4) g
      ap g h = h , h , h , h
    swap-ends : Hac • Hbd • Xbc • Hbd • Hac ≈ Hbd • Hac • Xbc • Hac • Hbd
    swap-ends = begin
      Hac • Hbd • Xbc • Hbd • Hac                  ≈⟨ by-assoc auto ⟩
      (Hac • Hbd) • Xbc • (Hbd • Hac)              ≈⟨ cong (commHH ac bd a≢b a≢d (≢-sym b≢c) c≢d)
                                                          (cright commHH bd ac (≢-sym a≢b) b≢c (≢-sym a≢d) (≢-sym c≢d)) ⟩
      (Hbd • Hac) • Xbc • (Hac • Hbd)              ≈⟨ by-assoc auto ⟩
      Hbd • Hac • Xbc • Hac • Hbd                  ∎
    -- X_[c,d] swaps c and d.
    x-bd : Xcd • Hbd ≈ Hbc • Xcd
    x-bd = sym (HX≈XH′ bc cd)
    x-ac : Xcd • Hac ≈ Had • Xcd
    x-ac = axiom (swap-XH′ ac cd)
    x-bc : Xcd • Xbc ≈ Xbd • Xcd
    x-bc = axiom (swap-XX′ bc cd)
    conj : Xcd • (Hbd • Hac • Xbc • Hac • Hbd) ≈ (Hbc • Had • Xbd • Had • Hbc) • Xcd
    conj = begin
      Xcd • (Hbd • Hac • Xbc • Hac • Hbd)          ≈⟨ pass x-bd ⟩
      Hbc • Xcd • (Hac • Xbc • Hac • Hbd)          ≈⟨ cright pass x-ac ⟩
      Hbc • Had • Xcd • (Xbc • Hac • Hbd)          ≈⟨ cright cright pass x-bc ⟩
      Hbc • Had • Xbd • Xcd • (Hac • Hbd)          ≈⟨ cright cright cright pass x-ac ⟩
      Hbc • Had • Xbd • Had • Xcd • Hbd            ≈⟨ cright cright cright cright x-bd ⟩
      Hbc • Had • Xbd • Had • Hbc • Xcd            ≈⟨ by-assoc auto ⟩
      (Hbc • Had • Xbd • Had • Hbc) • Xcd          ∎
