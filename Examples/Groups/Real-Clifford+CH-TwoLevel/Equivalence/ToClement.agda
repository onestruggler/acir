------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations of Figure 6 derive Clément's (1)–(19), for every order
-- of the indices (Clement).  (1)–(18) are conjugations by X and the
-- local relations; (19) is (f1) (Pairings) for increasing indices, and
-- conjugation by Xs relabels it to the other orders (SortP).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence.ToClement {n : ℕ} where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
import Data.List.Base as L
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_ ; ≢-sym)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric {n}
import Examples.Groups.Real-Clifford+CH-TwoLevel.Pairings {n} as Pairings
open import Data.Product.Base using (_×_)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  variable
    a b j k l t : Fin n

  rc : .(a < b) → a < b
  rc {a = a} {b} lt = recompute (a FinP.<? b) lt

  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

  <⇒≢ : .(a < b) → a ≢ b
  <⇒≢ lt e = FinP.<-irrefl e (rc lt)

  by-order : ∀ {A : Set} → a ≢ b → (.(a < b) → A) → (.(b < a) → A) → A
  by-order {a = a} {b} a≢b f g with FinP.<-cmp a b
  ... | tri< lt _ _ = f lt
  ... | tri≈ _ e _ = ⊥-elim (a≢b e)
  ... | tri> _ _ gt = g gt

------------------------------------------------------------------------
-- The transposition is symmetric

τ-sym : ∀ (p q x : Fin n) → p ≢ q → τ q p x ≡ τ p q x
τ-sym p q x p≢q = go (x FinP.≟ p) (x FinP.≟ q)
  where
  go : Dec (x ≡ p) → Dec (x ≡ q) → τ q p x ≡ τ p q x
  go (yes x≡p) _ =
    ≡.trans (≡.cong (τ q p) x≡p) (≡.trans (τ-q q p (p≢q ∘ ≡.sym)) (≡.sym (≡.trans (≡.cong (τ p q) x≡p) (τ-p p q))))
  go (no x≢p) (yes x≡q) =
    ≡.trans (≡.cong (τ q p) x≡q) (≡.trans (τ-p q p) (≡.sym (≡.trans (≡.cong (τ p q) x≡q) (τ-q p q p≢q))))
  go (no x≢p) (no x≢q) = ≡.trans (τ-o q p x x≢q x≢p) (≡.sym (τ-o p q x x≢p x≢q))

------------------------------------------------------------------------
-- Conjugation by Xs j k relabels along (j k)

module Conj {j k : Fin n} (jk : j ≢ k) where

  σ : Fin n → Fin n
  σ = τ j k

  σ-j : σ j ≡ k
  σ-j = τ-p j k

  σ-k : σ k ≡ j
  σ-k = τ-q j k jk

  σ-o : ∀ {x} → x ≢ j → x ≢ k → σ x ≡ x
  σ-o {x} xj xk = τ-o j k x xj xk

  σ-inj : ∀ {x y} → x ≢ y → σ x ≢ σ y
  σ-inj x≢y e = x≢y (τ-inj j k jk e)

  private
    Xs≈ : .(lt : j < k) → Xs j k ≈ X j k lt
    Xs≈ lt = refl′ (Xs-< lt)
    Xs≈′ : .(gt : k < j) → Xs j k ≈ X k j gt
    Xs≈′ gt = refl′ (Xs-> gt)

    -- Turning X p q relabelling into Xs j k relabelling.
    via : ∀ {A B} → (.(lt : j < k) → X j k lt • A • X j k lt ≈ B) →
                    (.(gt : k < j) → X k j gt • A • X k j gt ≈ B) → Xs j k • A • Xs j k ≈ B
    via f g = by-order jk
      (λ lt → trans (cong (Xs≈ lt) (cright Xs≈ lt)) (f lt))
      (λ gt → trans (cong (Xs≈′ gt) (cright Xs≈′ gt)) (g gt))

  conjZ : ∀ x → Xs j k • Z x • Xs j k ≈ Z (σ x)
  conjZ x = via (λ lt → relabel-Z (rc lt) x)
                (λ gt → trans (relabel-Z (rc gt) x) (refl′ (≡.cong Z (τ-sym j k x jk))))

  conjXs : ∀ {x y} → x ≢ y → Xs j k • Xs x y • Xs j k ≈ Xs (σ x) (σ y)
  conjXs {x} {y} xy = via (λ lt → relabel-Xs (rc lt) xy)
    (λ gt → trans (relabel-Xs (rc gt) xy) (refl′ (≡.cong₂ Xs (τ-sym j k x jk) (τ-sym j k y jk))))

  conjHs : ∀ {x y} → x ≢ y → Xs j k • Hs x y • Xs j k ≈ Hs (σ x) (σ y)
  conjHs {x} {y} xy = via (λ lt → relabel-Hs (rc lt) xy)
    (λ gt → trans (relabel-Hs (rc gt) xy) (refl′ (≡.cong₂ Hs (τ-sym j k x jk) (τ-sym j k y jk))))

  XX : Xs j k • Xs j k ≈ ε
  XX = Xs-Xs jk

  -- From conjugation to commutation: Xs A Xs ≈ B gives Xs A ≈ B Xs.
  c⇒ : ∀ {A B} → Xs j k • A • Xs j k ≈ B → Xs j k • A ≈ B • Xs j k
  c⇒ {A} {B} h = begin
    Xs j k • A                          ≈⟨ sym right-unit ⟩
    (Xs j k • A) • ε                    ≈⟨ cright sym XX ⟩
    (Xs j k • A) • (Xs j k • Xs j k)    ≈⟨ assoc ⟩
    Xs j k • (A • (Xs j k • Xs j k))    ≈⟨ cright sym assoc ⟩
    Xs j k • ((A • Xs j k) • Xs j k)    ≈⟨ sym assoc ⟩
    (Xs j k • A • Xs j k) • Xs j k      ≈⟨ cleft h ⟩
    B • Xs j k                          ∎

  -- Conjugation distributes over products.
  conj-•ˢ : ∀ u v → Xs j k • (u • v) • Xs j k ≈ (Xs j k • u • Xs j k) • (Xs j k • v • Xs j k)
  conj-•ˢ u v = sym (begin
    (X′ • u • X′) • (X′ • v • X′)       ≈⟨ assoc ⟩
    X′ • ((u • X′) • (X′ • v • X′))     ≈⟨ cright assoc ⟩
    X′ • u • (X′ • (X′ • v • X′))       ≈⟨ cright cright sym assoc ⟩
    X′ • u • (X′ • X′) • v • X′         ≈⟨ cright cright cleft XX ⟩
    X′ • u • ε • v • X′                 ≈⟨ cright cright left-unit ⟩
    X′ • u • v • X′                     ≈⟨ cright sym assoc ⟩
    X′ • (u • v) • X′                   ∎)
    where X′ = Xs j k

------------------------------------------------------------------------
-- (1)–(18)

e1′ : Z j • Z j ≈ ε
e1′ = Z-Z

e2′ : j ≢ k → Hs j k • Hs j k ≈ ε
e2′ = Hs-Hs

e3′ : j ≢ k → Xs j k • Xs j k ≈ ε
e3′ = Xs-Xs

e4′ : j ≢ k → Z j • Z k ≈ Z k • Z j
e4′ jk = axiom (b1 jk)

e5′ : j ≢ k → l ≢ j → l ≢ k → Z l • Hs j k ≈ Hs j k • Z l
e5′ {j = j} {k} {l} jk lj lk = by-order jk
  (λ lt → trans (cright refl′ (Hs-< lt)) (trans (axiom (b4 lt lj lk)) (cleft refl′ (≡.sym (Hs-< lt)))))
  (λ gt → trans (cright refl′ (Hs-> gt))
     (trans (sym (comm-word (X k j gt • H k j gt • X k j gt) (Z-gen l)
                   (Z-apart gt , (H-apart gt , Z-apart gt))))
            (cleft refl′ (≡.sym (Hs-> gt)))))
  where
  Z-apart : .(gt : k < j) → Apart (X-gen k j gt) (Z-gen l)
  Z-apart gt = ((lk ∘ ≡.sym) ∷ []) ∷ ((lj ∘ ≡.sym) ∷ []) ∷ []
  H-apart : .(gt : k < j) → Apart (H-gen k j gt) (Z-gen l)
  H-apart gt = ((lk ∘ ≡.sym) ∷ []) ∷ ((lj ∘ ≡.sym) ∷ []) ∷ []

e6′ : j ≢ k → l ≢ j → l ≢ k → Z l • Xs j k ≈ Xs j k • Z l
e6′ {j = j} {k} {l} jk lj lk = by-order jk
  (λ lt → trans (cright refl′ (Xs-< lt)) (trans (axiom (b2 lt lj lk)) (cleft refl′ (≡.sym (Xs-< lt)))))
  (λ gt → trans (cright refl′ (Xs-> gt)) (trans (axiom (b2 gt lk lj)) (cleft refl′ (≡.sym (Xs-> gt)))))

-- Disjoint symmetric generators commute: conjugate by one of them.
private
  -- Conjugation by Xs j k fixes words on other indices.
  module Apart {j k : Fin n} (jk : j ≢ k) where
    open Conj jk

    fixHs : ∀ {x y} → x ≢ y → x ≢ j → x ≢ k → y ≢ j → y ≢ k → Xs j k • Hs x y • Xs j k ≈ Hs x y
    fixHs xy xj xk yj yk = trans (conjHs xy) (refl′ (≡.cong₂ Hs (σ-o xj xk) (σ-o yj yk)))

    fixXs : ∀ {x y} → x ≢ y → x ≢ j → x ≢ k → y ≢ j → y ≢ k → Xs j k • Xs x y • Xs j k ≈ Xs x y
    fixXs xy xj xk yj yk = trans (conjXs xy) (refl′ (≡.cong₂ Xs (σ-o xj xk) (σ-o yj yk)))

e9′ : j ≢ k → l ≢ t → j ≢ l → j ≢ t → k ≢ l → k ≢ t → Xs j k • Xs l t ≈ Xs l t • Xs j k
e9′ jk lt jl jt kl kt = Conj.c⇒ jk (Apart.fixXs jk lt (jl ∘ ≡.sym) (kl ∘ ≡.sym) (jt ∘ ≡.sym) (kt ∘ ≡.sym))

e8′ : j ≢ k → l ≢ t → j ≢ l → j ≢ t → k ≢ l → k ≢ t → Hs j k • Xs l t ≈ Xs l t • Hs j k
e8′ jk lt jl jt kl kt = sym (Conj.c⇒ lt (Apart.fixHs lt jk jl jt kl kt))

-- Disjoint Hs words: in each order they are words with disjoint letters.
private
  -- The indices of a letter on two indices x, y, apart from z.
  ap2 : ∀ {x y z : Fin n} → z ≢ x → z ≢ y → All (z ≢_) (x L.∷ y L.∷ L.[])
  ap2 zx zy = zx ∷ zy ∷ []

e7′ : j ≢ k → l ≢ t → j ≢ l → j ≢ t → k ≢ l → k ≢ t → Hs j k • Hs l t ≈ Hs l t • Hs j k
e7′ {j = j} {k} {l} {t} jk lt jl jt kl kt = by-order jk
  (λ p → by-order lt
    (λ q → trans (cong (refl′ (Hs-< p)) (refl′ (Hs-< q)))
             (trans (comm-words (H j k p) (H l t q) ((ap2 jl jt ∷ ap2 kl kt ∷ [])))
                    (cong (refl′ (≡.sym (Hs-< q))) (refl′ (≡.sym (Hs-< p))))))
    (λ q → trans (cong (refl′ (Hs-< p)) (refl′ (Hs-> q)))
             (trans (comm-words (H j k p) (X t l q • H t l q • X t l q)
                       (a₁ , (a₁ , a₁)))
                    (cong (refl′ (≡.sym (Hs-> q))) (refl′ (≡.sym (Hs-< p)))))))
  (λ p → by-order lt
    (λ q → trans (cong (refl′ (Hs-> p)) (refl′ (Hs-< q)))
             (trans (comm-words (X k j p • H k j p • X k j p) (H l t q) a₂)
                    (cong (refl′ (≡.sym (Hs-< q))) (refl′ (≡.sym (Hs-> p))))))
    (λ q → trans (cong (refl′ (Hs-> p)) (refl′ (Hs-> q)))
             (trans (comm-words (X k j p • H k j p • X k j p) (X t l q • H t l q • X t l q)
                       (a₃ , (a₃ , a₃)))
                    (cong (refl′ (≡.sym (Hs-> q))) (refl′ (≡.sym (Hs-> p)))))))
  where
  jt′ = ap2 jt jl
  kt′ = ap2 kt kl
  a₁ = jt′ ∷ kt′ ∷ []
  a₂′ = ap2 kl kt ∷ ap2 jl jt ∷ []
  a₂ = (a₂′ , (a₂′ , a₂′))
  a₃′ = ap2 kt kl ∷ ap2 jt jl ∷ []
  a₃ = (a₃′ , (a₃′ , a₃′))

e10′ : j ≢ k → Xs j k • Z k ≈ Z j • Xs j k
e10′ jk = Conj.c⇒ jk (trans (Conj.conjZ jk _) (refl′ (≡.cong Z (Conj.σ-k jk))))

e11′ : j ≢ k → Xs j k • Z j ≈ Z k • Xs j k
e11′ jk = Conj.c⇒ jk (trans (Conj.conjZ jk _) (refl′ (≡.cong Z (Conj.σ-j jk))))

e12′ : j ≢ k → j ≢ l → k ≢ l → Xs j k • Xs j l ≈ Xs k l • Xs j k
e12′ jk jl kl = Conj.c⇒ jk (trans (Conj.conjXs jk jl)
  (refl′ (≡.cong₂ Xs (Conj.σ-j jk) (Conj.σ-o jk (jl ∘ ≡.sym) (kl ∘ ≡.sym)))))

e13′ : j ≢ k → l ≢ j → k ≢ l → Xs j k • Xs l j ≈ Xs l k • Xs j k
e13′ jk lj kl = Conj.c⇒ jk (trans (Conj.conjXs jk lj)
  (refl′ (≡.cong₂ Xs (Conj.σ-o jk lj (kl ∘ ≡.sym)) (Conj.σ-j jk))))

e14′ : j ≢ k → j ≢ l → k ≢ l → Xs j k • Hs j l ≈ Hs k l • Xs j k
e14′ jk jl kl = Conj.c⇒ jk (trans (Conj.conjHs jk jl)
  (refl′ (≡.cong₂ Hs (Conj.σ-j jk) (Conj.σ-o jk (jl ∘ ≡.sym) (kl ∘ ≡.sym)))))

e15′ : j ≢ k → l ≢ j → k ≢ l → Xs j k • Hs l j ≈ Hs l k • Xs j k
e15′ jk lj kl = Conj.c⇒ jk (trans (Conj.conjHs jk lj)
  (refl′ (≡.cong₂ Hs (Conj.σ-o jk lj (kl ∘ ≡.sym)) (Conj.σ-j jk))))

-- Z_[j] Z_[k] is fixed by conjugation by Xs j k.
private
  ZZ-fix : (jk : j ≢ k) → Xs j k • (Z j • Z k) • Xs j k ≈ Z j • Z k
  ZZ-fix {j = j} {k} jk = begin
    Xs j k • (Z j • Z k) • Xs j k                     ≈⟨ Conj.conj-•ˢ jk (Z j) (Z k) ⟩
    (Xs j k • Z j • Xs j k) • (Xs j k • Z k • Xs j k) ≈⟨ cong (Conj.conjZ jk j) (Conj.conjZ jk k) ⟩
    Z (Conj.σ jk j) • Z (Conj.σ jk k)                 ≈⟨ cong (refl′ (≡.cong Z (Conj.σ-j jk))) (refl′ (≡.cong Z (Conj.σ-k jk))) ⟩
    Z k • Z j                                         ≈⟨ axiom (b1 (jk ∘ ≡.sym)) ⟩
    Z j • Z k                                         ∎

e16′ : j ≢ k → Z j • Z k • Xs j k ≈ Xs j k • Z j • Z k
e16′ jk = trans (sym assoc) (sym (Conj.c⇒ jk (ZZ-fix jk)))

e17′ : j ≢ k → Z j • Z k • Hs j k ≈ Hs j k • Z j • Z k
e17′ {j = j} {k} jk = by-order jk
  (λ lt → trans (cright cright refl′ (Hs-< lt)) (trans (axiom (d1 lt)) (cleft refl′ (≡.sym (Hs-< lt)))))
  (λ gt → trans (cright cright refl′ (Hs-> gt)) (trans (core gt) (cleft refl′ (≡.sym (Hs-> gt)))))
  where
  core : .(gt : k < j) → Z j • Z k • (X k j gt • H k j gt • X k j gt) ≈ (X k j gt • H k j gt • X k j gt) • Z j • Z k
  core gt = begin
    Z j • Z k • (X′ • H′ • X′)                ≈⟨ by-assoc auto ⟩
    ((Z j • Z k) • X′) • H′ • X′              ≈⟨ cleft xz ⟩
    (X′ • (Z k • Z j)) • H′ • X′              ≈⟨ by-assoc auto ⟩
    X′ • ((Z k • Z j) • H′) • X′              ≈⟨ cright cleft trans assoc (axiom (d1 gt)) ⟩
    X′ • (H′ • Z k • Z j) • X′                ≈⟨ by-assoc auto ⟩
    X′ • H′ • ((Z k • Z j) • X′)              ≈⟨ cright cright xz′ ⟩
    X′ • H′ • (X′ • (Z j • Z k))              ≈⟨ by-assoc auto ⟩
    (X′ • H′ • X′) • Z j • Z k                ∎
    where
    X′ = X k j gt
    H′ = H k j gt
    -- Z_j Z_k X = X Z_k Z_j and back, by (c1) twice.
    xz : (Z j • Z k) • X′ ≈ X′ • (Z k • Z j)
    xz = begin
      (Z j • Z k) • X′            ≈⟨ assoc ⟩
      Z j • Z k • X′              ≈⟨ cright axiom (c1 gt) ⟩
      Z j • X′ • Z j              ≈⟨ sym assoc ⟩
      (Z j • X′) • Z j            ≈⟨ cleft flip-X gt (axiom (c1 gt)) ⟩
      (X′ • Z k) • Z j            ≈⟨ assoc ⟩
      X′ • (Z k • Z j)            ∎
    xz′ : (Z k • Z j) • X′ ≈ X′ • (Z j • Z k)
    xz′ = begin
      (Z k • Z j) • X′            ≈⟨ cleft axiom (b1 (jk ∘ ≡.sym)) ⟩
      (Z j • Z k) • X′            ≈⟨ xz ⟩
      X′ • (Z k • Z j)            ≈⟨ cright axiom (b1 (jk ∘ ≡.sym)) ⟩
      X′ • (Z j • Z k)            ∎

e18′ : j ≢ k → Hs j k • Xs j k ≈ Z k • Hs j k
e18′ {j = j} {k} jk = by-order jk
  (λ lt → trans (cong (refl′ (Hs-< lt)) (refl′ (Xs-< lt))) (trans (sym (axiom (d2 lt))) (cright refl′ (≡.sym (Hs-< lt)))))
  (λ gt → trans (cong (refl′ (Hs-> gt)) (refl′ (Xs-> gt))) (trans (core gt) (cright refl′ (≡.sym (Hs-> gt)))))
  where
  core : .(gt : k < j) → (X k j gt • H k j gt • X k j gt) • X k j gt ≈ Z k • (X k j gt • H k j gt • X k j gt)
  core gt = begin
    (X′ • H′ • X′) • X′           ≈⟨ by-assoc auto ⟩
    X′ • H′ • (X′ • X′)           ≈⟨ cright cright X-X gt ⟩
    X′ • H′ • ε                   ≈⟨ cright right-unit ⟩
    X′ • H′                       ≈⟨ cright sym right-unit ⟩
    X′ • H′ • ε                   ≈⟨ cright cright sym (X-X gt) ⟩
    X′ • H′ • (X′ • X′)           ≈⟨ cright sym assoc ⟩
    X′ • (H′ • X′) • X′           ≈⟨ cright cleft sym (axiom (d2 gt)) ⟩
    X′ • (Z j • H′) • X′          ≈⟨ by-assoc auto ⟩
    (X′ • Z j) • H′ • X′          ≈⟨ cleft sym (axiom (c1 gt)) ⟩
    (Z k • X′) • H′ • X′          ≈⟨ assoc ⟩
    Z k • (X′ • H′ • X′)          ∎
    where
    X′ = X k j gt
    H′ = H k j gt

------------------------------------------------------------------------
-- (19), for every order of the indices

-- (19) at j, k, l, t.
P : Fin n → Fin n → Fin n → Fin n → Set
P j k l t = Hs j k • Hs l t • Hs j l • Hs k t ≈ Hs j l • Hs k t • Hs j k • Hs l t

-- Four distinct indices.
record D4 (j k l t : Fin n) : Set where
  constructor d4
  field
    jk : j ≢ k
    jl : j ≢ l
    jt : j ≢ t
    kl : k ≢ l
    kt : k ≢ t
    lt : l ≢ t

private
  sy : ∀ {x y : Fin n} → x ≢ y → y ≢ x
  sy ne = ne ∘ ≡.sym

  P-cong : ∀ {j k l t j′ k′ l′ t′} → j ≡ j′ → k ≡ k′ → l ≡ l′ → t ≡ t′ → P j k l t → P j′ k′ l′ t′
  P-cong ≡.refl ≡.refl ≡.refl ≡.refl h = h

  -- Conjugation of a word of four letters.
  conj4 : ∀ {p q} (pq : p ≢ q) (A B C D : Word (Gen n)) →
          Xs p q • (A • B • C • D) • Xs p q ≈
          (Xs p q • A • Xs p q) • (Xs p q • B • Xs p q) • (Xs p q • C • Xs p q) • (Xs p q • D • Xs p q)
  conj4 pq A B C D = begin
    Xs′ • (A • B • C • D) • Xs′                               ≈⟨ Conj.conj-•ˢ pq A (B • C • D) ⟩
    c A • (Xs′ • (B • C • D) • Xs′)                           ≈⟨ cright Conj.conj-•ˢ pq B (C • D) ⟩
    c A • c B • (Xs′ • (C • D) • Xs′)                         ≈⟨ cright cright Conj.conj-•ˢ pq C D ⟩
    c A • c B • c C • c D                                     ∎
    where
    Xs′ = Xs _ _
    c : Word (Gen n) → Word (Gen n)
    c W = Xs _ _ • W • Xs _ _

-- Conjugation by Xs p q relabels (19) along (p q).
R : ∀ {p q j k l t} (pq : p ≢ q) → D4 j k l t → P j k l t →
    P (τ p q j) (τ p q k) (τ p q l) (τ p q t)
R {p} {q} {j} {k} {l} {t} pq (d4 jk jl jt kl kt lt) h = begin
  Hs (σ j) (σ k) • Hs (σ l) (σ t) • Hs (σ j) (σ l) • Hs (σ k) (σ t)
    ≈⟨ sym (cong (cH jk) (cong (cH lt) (cong (cH jl) (cH kt)))) ⟩
  _ ≈⟨ sym (conj4 pq (Hs j k) (Hs l t) (Hs j l) (Hs k t)) ⟩
  Xs p q • (Hs j k • Hs l t • Hs j l • Hs k t) • Xs p q
    ≈⟨ cright cleft h ⟩
  Xs p q • (Hs j l • Hs k t • Hs j k • Hs l t) • Xs p q
    ≈⟨ conj4 pq (Hs j l) (Hs k t) (Hs j k) (Hs l t) ⟩
  _ ≈⟨ cong (cH jl) (cong (cH kt) (cong (cH jk) (cH lt))) ⟩
  Hs (σ j) (σ l) • Hs (σ k) (σ t) • Hs (σ j) (σ k) • Hs (σ l) (σ t) ∎
  where
  σ = τ p q
  cH : ∀ {x y} → x ≢ y → Xs p q • Hs x y • Xs p q ≈ Hs (σ x) (σ y)
  cH = Conj.conjHs pq

-- Swapping two entries of the tuple.
private
  module Sw {j k l t : Fin n} (d : D4 j k l t) where
    open D4 d

    swap01 : P k j l t → P j k l t
    swap01 h = P-cong (τ-q j k jk) (τ-p j k) (τ-o j k l (sy jl) (sy kl)) (τ-o j k t (sy jt) (sy kt))
      (R jk (d4 (sy jk) kl kt jl jt lt) h)

    swap12 : P j l k t → P j k l t
    swap12 h = P-cong (τ-o k l j jk jl) (τ-q k l kl) (τ-p k l) (τ-o k l t (sy kt) (sy lt))
      (R kl (d4 jl jk jt (sy kl) lt kt) h)

    swap23 : P j k t l → P j k l t
    swap23 h = P-cong (τ-o l t j jl jt) (τ-o l t k kl kt) (τ-q l t lt) (τ-p l t)
      (R lt (d4 jk jt jl kt kl (sy lt)) h)

-- Increasing indices: (f1).
P-sorted : ∀ {j k l t} → j < k → k < l → l < t → P j k l t
P-sorted {j} {k} {l} {t} p q r = begin
  Hs j k • Hs l t • Hs j l • Hs k t
    ≈⟨ cong (refl′ (Hs-< p)) (cong (refl′ (Hs-< r)) (cong (refl′ (Hs-< (S.ac))) (refl′ (Hs-< S.bd)))) ⟩
  H j k p • H l t r • H j l S.ac • H k t S.bd     ≈⟨ by-assoc auto ⟩
  S.ΠA • S.ΠB                                       ≈⟨ S.f1 ⟩
  S.ΠB • S.ΠA                                       ≈⟨ by-assoc auto ⟩
  H j l S.ac • H k t S.bd • H j k p • H l t r
    ≈⟨ sym (cong (refl′ (Hs-< (S.ac))) (cong (refl′ (Hs-< S.bd)) (cong (refl′ (Hs-< p)) (refl′ (Hs-< r))))) ⟩
  Hs j l • Hs k t • Hs j k • Hs l t ∎
  where module S = Pairings.Sorted p q r

-- Insertion sort.  (The comparisons are arguments, not with-clauses:
-- abstracting <-cmp would rewrite it inside Hs.)
private
  -- j < k < l: insert t.
  ins3 : ∀ {j k l t} → D4 j k l t → j < k → k < l → P j k l t
  ins3 {j} {k} {l} {t} d p q = go₀ (FinP.<-cmp l t)
    where
    open D4 d
    go₀ : Tri (l < t) (l ≡ t) (t < l) → P j k l t
    go₀ (tri< r _ _) = P-sorted p q r
    go₀ (tri≈ _ e _) = ⊥-elim (lt e)
    go₀ (tri> _ _ r) = Sw.swap23 d (go (FinP.<-cmp k t))
      where
      -- P j k t l, t < l.
      go : Tri (k < t) (k ≡ t) (t < k) → P j k t l
      go (tri< s _ _) = P-sorted p s r
      go (tri≈ _ e _) = ⊥-elim (kt e)
      go (tri> _ _ s) = Sw.swap12 (d4 jk jt jl kt kl (sy lt)) (go′ (FinP.<-cmp j t))
        where
        -- P j t k l, t < k.
        go′ : Tri (j < t) (j ≡ t) (t < j) → P j t k l
        go′ (tri< u _ _) = P-sorted u s q
        go′ (tri≈ _ e _) = ⊥-elim (jt e)
        go′ (tri> _ _ u) = Sw.swap01 (d4 jt jk jl (sy kt) (sy lt) kl) (P-sorted u p q)

  sort4 : ∀ {j k l t} → D4 j k l t → P j k l t
  sort4 {j} {k} {l} {t} d = c₀ (FinP.<-cmp j k)
    where
    open D4 d
    c₀ : Tri (j < k) (j ≡ k) (k < j) → P j k l t
    c₀ (tri≈ _ e _) = ⊥-elim (jk e)
    c₀ (tri< p _ _) = c₁ (FinP.<-cmp k l)
      where
      c₁ : Tri (k < l) (k ≡ l) (l < k) → P j k l t
      c₁ (tri< q _ _) = ins3 d p q
      c₁ (tri≈ _ e _) = ⊥-elim (kl e)
      c₁ (tri> _ _ q) = c₂ (FinP.<-cmp j l)
        where
        c₂ : Tri (j < l) (j ≡ l) (l < j) → P j k l t
        c₂ (tri< r _ _) = Sw.swap12 d (ins3 (d4 jl jk jt (sy kl) lt kt) r q)
        c₂ (tri≈ _ e _) = ⊥-elim (jl e)
        c₂ (tri> _ _ r) = Sw.swap12 d (Sw.swap01 (d4 jl jk jt (sy kl) lt kt)
                            (ins3 (d4 (sy jl) (sy kl) lt jk jt kt) r p))
    c₀ (tri> _ _ p) = c₁ (FinP.<-cmp j l)
      where
      c₁ : Tri (j < l) (j ≡ l) (l < j) → P j k l t
      c₁ (tri< q _ _) = Sw.swap01 d (ins3 (d4 (sy jk) kl kt jl jt lt) p q)
      c₁ (tri≈ _ e _) = ⊥-elim (jl e)
      c₁ (tri> _ _ q) = c₂ (FinP.<-cmp k l)
        where
        c₂ : Tri (k < l) (k ≡ l) (l < k) → P j k l t
        c₂ (tri< r _ _) = Sw.swap01 d (Sw.swap12 (d4 (sy jk) kl kt jl jt lt)
                            (ins3 (d4 kl (sy jk) kt (sy jl) lt jt) r q))
        c₂ (tri≈ _ e _) = ⊥-elim (kl e)
        c₂ (tri> _ _ r) = Sw.swap01 d (Sw.swap12 (d4 (sy jk) kl kt jl jt lt)
                            (Sw.swap01 (d4 kl (sy jk) kt (sy jl) lt jt)
                              (ins3 (d4 (sy kl) (sy jl) lt (sy jk) kt jt) r p)))

e19′ : j ≢ k → l ≢ t → j ≢ l → k ≢ t → j ≢ t →
       Hs j k • Hs l t • Hs j l • Hs k t ≈ Hs j l • Hs k t • Hs j k • Hs l t
e19′ {j} {k} {l} {t} jk lt jl kt jt = go (k FinP.≟ l)
  where
  go : Dec (k ≡ l) → P j k l t
  go (yes ≡.refl) = refl
  go (no kl) = sort4 (d4 jk jl jt kl kt lt)
