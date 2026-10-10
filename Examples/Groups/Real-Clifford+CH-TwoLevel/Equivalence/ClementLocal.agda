------------------------------------------------------------------------
-- Presentations of groups
--
-- In Clément's relations (Clement): the local relations (a1)–(d2) of
-- Figure 6, and conjugation by Xs p q, which relabels words of
-- symmetric generators along the transposition (p q) (his Lemma 3.14).
-- For p = q, Xs p p is ε and the transposition is the identity, so a
-- list of transpositions relabels without case distinctions.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence.ClementLocal {n : ℕ} where

open import Data.Bool.Base using (if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_ ; map ; foldr ; _++_)
open import Data.Product.Base using (_×_ ; _,_)
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute ; does ; dec-true ; dec-false)
import Relation.Binary.Reasoning.Setoid as SR

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric {n}
  using (Hs ; Xs ; HsT ; XsT ; Hs-< ; Hs-> ; Xs-< ; Xs-> ; τ ; τ-p ; τ-q ; τ-o)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Local as L
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Clement
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Embedding using (Emb ; ι ; mono ; gen ; word)
import Presentation.Tactics.Words as TW
module AW = TW.Associative

open PB (_===ᶜ_ {n}) renaming (_≈_ to _≈ᶜ_)
open PP (_===ᶜ_ {n})
open SR word-setoid

private
  variable
    a b c p q x y : Fin n

  rc : .(a < b) → a < b
  rc {a = a} {b} lt = recompute (a FinP.<? b) lt

  <⇒≢ : .(a < b) → a ≢ b
  <⇒≢ lt e = FinP.<-irrefl e (rc lt)

  sy : a ≢ b → b ≢ a
  sy ne = ne ∘ ≡.sym

refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ᶜ v
refl′ ≡.refl = refl

------------------------------------------------------------------------
-- The local relations

private
  H≈ : .(lt : a < b) → Hs a b ≈ᶜ H a b lt
  H≈ lt = refl′ (Hs-< lt)
  X≈ : .(lt : a < b) → Xs a b ≈ᶜ X a b lt
  X≈ lt = refl′ (Xs-< lt)
  X≈′ : .(gt : b < a) → Xs a b ≈ᶜ X b a gt
  X≈′ gt = refl′ (Xs-> gt)

c-local : ∀ {u v} → u L.===ˡ v → u ≈ᶜ v
c-local L.a1 = axiom e1
c-local (L.a2 p) = trans (sym (cong (X≈ p) (X≈ p))) (axiom (e3 (<⇒≢ p)))
c-local (L.a3 p) = trans (sym (cong (H≈ p) (H≈ p))) (axiom (e2 (<⇒≢ p)))
c-local (L.b1 ab) = axiom (e4 ab)
c-local (L.b2 p ab ac) = trans (cright sym (X≈ p)) (trans (axiom (e6 (<⇒≢ p) ab ac)) (cleft X≈ p))
c-local (L.b3 p q ac ad bc bd) =
  trans (sym (cong (X≈ p) (X≈ q))) (trans (axiom (e9 (<⇒≢ p) (<⇒≢ q) ac ad bc bd)) (cong (X≈ q) (X≈ p)))
c-local (L.b4 p ab ac) = trans (cright sym (H≈ p)) (trans (axiom (e5 (<⇒≢ p) ab ac)) (cleft H≈ p))
c-local (L.b5 p q ac ad bc bd) =
  trans (sym (cong (X≈ p) (H≈ q)))
        (trans (sym (axiom (e8 (<⇒≢ q) (<⇒≢ p) (sy ac) (sy bc) (sy ad) (sy bd)))) (cong (H≈ q) (X≈ p)))
c-local (L.b6 p q ac ad bc bd) =
  trans (sym (cong (H≈ p) (H≈ q))) (trans (axiom (e7 (<⇒≢ p) (<⇒≢ q) ac ad bc bd)) (cong (H≈ q) (H≈ p)))
c-local (L.c1 p) = trans (cright sym (X≈ p)) (trans (sym (axiom (e10 (<⇒≢ p)))) (cleft X≈ p))
c-local (L.c2 p q) =
  trans (sym (cong (X≈ q) (X≈ p)))
        (trans (sym (axiom (e12 (<⇒≢ p) (<⇒≢ (FinP.<-trans p q)) (<⇒≢ q)))) (cong (X≈ p) (X≈ (FinP.<-trans p q))))
c-local (L.c3 p q) =
  trans (sym (cong (X≈ (FinP.<-trans p q)) (X≈ q)))
        (trans (sym (axiom (e13 (<⇒≢ q) (<⇒≢ p) (sy (<⇒≢ (FinP.<-trans p q)))))) (cong (X≈ q) (X≈ p)))
c-local (L.c4 p q) =
  trans (sym (cong (H≈ q) (X≈ p)))
        (trans (sym (axiom (e14 (<⇒≢ p) (<⇒≢ (FinP.<-trans p q)) (<⇒≢ q)))) (cong (X≈ p) (H≈ (FinP.<-trans p q))))
c-local (L.c5 p q) =
  trans (sym (cong (H≈ (FinP.<-trans p q)) (X≈ q)))
        (trans (sym (axiom (e15 (<⇒≢ q) (<⇒≢ p) (sy (<⇒≢ (FinP.<-trans p q)))))) (cong (X≈ q) (H≈ p)))
c-local (L.d1 p) = trans (cright cright sym (H≈ p)) (trans (axiom (e17 (<⇒≢ p))) (cleft H≈ p))
c-local (L.d2 p) = trans (cright sym (H≈ p)) (trans (sym (axiom (e18 (<⇒≢ p)))) (cong (H≈ p) (X≈ p)))

------------------------------------------------------------------------
-- Words of symmetric generators

data Sym : Set where
  hs xs : Fin n → Fin n → Sym
  zs    : Fin n → Sym

⟦_⟧ˢ : Sym → Word (Gen n)
⟦ hs a b ⟧ˢ = Hs a b
⟦ xs a b ⟧ˢ = Xs a b
⟦ zs a ⟧ˢ   = Z a

-- Right-nested, without a trailing ε.
⟦_⟧ : List Sym → Word (Gen n)
⟦ [] ⟧          = ε
⟦ s ∷ [] ⟧      = ⟦ s ⟧ˢ
⟦ s ∷ s′ ∷ ss ⟧ = ⟦ s ⟧ˢ • ⟦ s′ ∷ ss ⟧

relabelˢ : (Fin n → Fin n) → Sym → Sym
relabelˢ f (hs a b) = hs (f a) (f b)
relabelˢ f (xs a b) = xs (f a) (f b)
relabelˢ f (zs a)   = zs (f a)

relabel : (Fin n → Fin n) → List Sym → List Sym
relabel f = map (relabelˢ f)

------------------------------------------------------------------------
-- Xs p q for any p, q

-- Xs is symmetric as a word.
Xs-swap : ∀ p q → Xs p q ≡ Xs q p
Xs-swap p q = go (FinP.<-cmp p q)
  where
  go : Tri (p < q) (p ≡ q) (q < p) → Xs p q ≡ Xs q p
  go (tri< lt _ _) = ≡.trans (Xs-< lt) (≡.sym (Xs-> lt))
  go (tri≈ _ ≡.refl _) = ≡.refl
  go (tri> _ _ gt) = ≡.trans (Xs-> gt) (≡.sym (Xs-< gt))

Xs-refl : ∀ p → Xs p p ≡ ε
Xs-refl p with FinP.<-cmp p p
... | tri< lt _ _ = ⊥-elim (FinP.<-irrefl ≡.refl lt)
... | tri≈ _ _ _ = ≡.refl
... | tri> _ _ gt = ⊥-elim (FinP.<-irrefl ≡.refl gt)

Hs-refl : ∀ p → Hs p p ≡ ε
Hs-refl p with FinP.<-cmp p p
... | tri< lt _ _ = ⊥-elim (FinP.<-irrefl ≡.refl lt)
... | tri≈ _ _ _ = ≡.refl
... | tri> _ _ gt = ⊥-elim (FinP.<-irrefl ≡.refl gt)

τ-refl : ∀ p x → τ p p x ≡ x
τ-refl p x with x FinP.≟ p
... | yes ≡.refl = ≡.refl
... | no _ = ≡.refl

XX : ∀ p q → Xs p q • Xs p q ≈ᶜ ε
XX p q with p FinP.≟ q
... | yes ≡.refl = trans (cong (refl′ (Xs-refl p)) (refl′ (Xs-refl p))) left-unit
... | no pq = axiom (e3 pq)

-- From Xs A ≈ B Xs: Xs A Xs ≈ B.
c⇐ : ∀ p q {A B} → Xs p q • A ≈ᶜ B • Xs p q → Xs p q • A • Xs p q ≈ᶜ B
c⇐ p q {A} {B} h = begin
  Xs p q • A • Xs p q          ≈⟨ sym assoc ⟩
  (Xs p q • A) • Xs p q        ≈⟨ cleft h ⟩
  (B • Xs p q) • Xs p q        ≈⟨ assoc ⟩
  B • (Xs p q • Xs p q)        ≈⟨ cright XX p q ⟩
  B • ε                        ≈⟨ right-unit ⟩
  B                            ∎

-- Fixed words commute with Xs.
fix⇒ : ∀ p q {A} → A • Xs p q ≈ᶜ Xs p q • A → Xs p q • A • Xs p q ≈ᶜ A
fix⇒ p q {A} h = c⇐ p q (sym h)

conj-• : ∀ p q u v → Xs p q • (u • v) • Xs p q ≈ᶜ (Xs p q • u • Xs p q) • (Xs p q • v • Xs p q)
conj-• p q u v = sym (begin
  (X′ • u • X′) • (X′ • v • X′)       ≈⟨ assoc ⟩
  X′ • ((u • X′) • (X′ • v • X′))     ≈⟨ cright assoc ⟩
  X′ • u • (X′ • (X′ • v • X′))       ≈⟨ cright cright sym assoc ⟩
  X′ • u • (X′ • X′) • v • X′         ≈⟨ cright cright cleft XX p q ⟩
  X′ • u • ε • v • X′                 ≈⟨ cright cright left-unit ⟩
  X′ • u • v • X′                     ≈⟨ cright sym assoc ⟩
  X′ • (u • v) • X′                   ∎)
  where X′ = Xs p q

private
  conj-ε : ∀ p q → Xs p q • ε • Xs p q ≈ᶜ ε
  conj-ε p q = trans (cright left-unit) (XX p q)

  -- On p = q, conjugation is trivial.
  conj-same : ∀ p {A} → Xs p p • A • Xs p p ≈ᶜ A
  conj-same p {A} = trans (cong (refl′ (Xs-refl p)) (cright refl′ (Xs-refl p))) (trans left-unit right-unit)

  dec-p : ∀ (p q x : Fin n) → x ≡ p → τ p q x ≡ q
  dec-p p q x ≡.refl = τ-p p q

  dec-q : ∀ (p q x : Fin n) → p ≢ q → x ≡ q → τ p q x ≡ p
  dec-q p q x pq ≡.refl = τ-q p q pq

------------------------------------------------------------------------
-- Relabelling letters

conjZᶜ : ∀ p q x → Xs p q • Z x • Xs p q ≈ᶜ Z (τ p q x)
conjZᶜ p q x with p FinP.≟ q
... | yes ≡.refl = trans (conj-same p) (refl′ (≡.cong Z (≡.sym (τ-refl p x))))
... | no pq = go (x FinP.≟ p) (x FinP.≟ q)
  where
  go : Dec (x ≡ p) → Dec (x ≡ q) → Xs p q • Z x • Xs p q ≈ᶜ Z (τ p q x)
  go (yes ≡.refl) _ = trans (c⇐ p q (axiom (e11 pq))) (refl′ (≡.cong Z (≡.sym (τ-p p q))))
  go (no xp) (yes ≡.refl) = trans (c⇐ p q (axiom (e10 pq))) (refl′ (≡.cong Z (≡.sym (τ-q p q pq))))
  go (no xp) (no xq) = trans (fix⇒ p q (axiom (e6 pq xp xq))) (refl′ (≡.cong Z (≡.sym (τ-o p q x xp xq))))

-- Hs q p = Xs p q Hs p q Xs p q, for p ≢ q.
Hs-flipᶜ : ∀ {p q} → p ≢ q → Xs p q • Hs p q • Xs p q ≈ᶜ Hs q p
Hs-flipᶜ {p} {q} pq = go (FinP.<-cmp p q)
  where
  go : Tri (p < q) (p ≡ q) (q < p) → Xs p q • Hs p q • Xs p q ≈ᶜ Hs q p
  go (tri< lt _ _) = trans (cong (refl′ (Xs-< lt)) (cong (refl′ (Hs-< lt)) (refl′ (Xs-< lt)))) (refl′ (≡.sym (Hs-> lt)))
  go (tri≈ _ e _) = ⊥-elim (pq e)
  go (tri> _ _ gt) = begin
    Xs p q • Hs p q • Xs p q                     ≈⟨ cong (refl′ (Xs-> gt)) (cong (refl′ (Hs-> gt)) (refl′ (Xs-> gt))) ⟩
    X′ • (X′ • H′ • X′) • X′                     ≈⟨ by-assoc auto ⟩
    (X′ • X′) • H′ • (X′ • X′)                   ≈⟨ cong (c-local (L.a2 gt)) (cright c-local (L.a2 gt)) ⟩
    ε • H′ • ε                                   ≈⟨ trans left-unit right-unit ⟩
    H′                                           ≈⟨ refl′ (≡.sym (Hs-< gt)) ⟩
    Hs q p                                       ∎
    where
    X′ = X q p gt
    H′ = H q p gt

conjHsᶜ : ∀ p q x y → Xs p q • Hs x y • Xs p q ≈ᶜ Hs (τ p q x) (τ p q y)
conjHsᶜ p q x y with p FinP.≟ q
... | yes ≡.refl = trans (conj-same p) (refl′ (≡.cong₂ Hs (≡.sym (τ-refl p x)) (≡.sym (τ-refl p y))))
... | no pq with x FinP.≟ y
...   | yes ≡.refl = trans (cright cleft refl′ (Hs-refl x))
                       (trans (conj-ε p q) (refl′ (≡.sym (Hs-refl (τ p q x)))))
...   | no xy = go (x FinP.≟ p) (x FinP.≟ q) (y FinP.≟ p) (y FinP.≟ q)
  where
  swapX : Xs q p ≡ Xs p q
  swapX = Xs-swap q p
  go : Dec (x ≡ p) → Dec (x ≡ q) → Dec (y ≡ p) → Dec (y ≡ q) →
       Xs p q • Hs x y • Xs p q ≈ᶜ Hs (τ p q x) (τ p q y)
  go (yes ≡.refl) _ _ (yes ≡.refl) =
    trans (Hs-flipᶜ pq) (refl′ (≡.cong₂ Hs (≡.sym (τ-p p q)) (≡.sym (τ-q p q pq))))
  go (yes ≡.refl) _ (yes e) _ = ⊥-elim (xy (≡.sym e))
  go (yes ≡.refl) _ (no yp) (no yq) =
    trans (c⇐ p q (axiom (e14 pq (sy yp) (sy yq))))
          (refl′ (≡.cong₂ Hs (≡.sym (τ-p p q)) (≡.sym (τ-o p q y yp yq))))
  go (no xp) (yes ≡.refl) (yes ≡.refl) _ =
    trans (cong (refl′ (≡.sym swapX)) (cright refl′ (≡.sym swapX)))
          (trans (Hs-flipᶜ (sy pq))
                 (refl′ (≡.cong₂ Hs (≡.sym (τ-q p q pq)) (≡.sym (τ-p p q)))))
  go (no xp) (yes ≡.refl) (no yp) (yes e) = ⊥-elim (xy (≡.sym e))
  go (no xp) (yes ≡.refl) (no yp) (no yq) =
    trans (cong (refl′ (≡.sym swapX)) (cright refl′ (≡.sym swapX)))
          (trans (c⇐ q p (axiom (e14 (sy pq) (sy yq) (sy yp))))
                 (refl′ (≡.cong₂ Hs (≡.sym (τ-q p q pq)) (≡.sym (τ-o p q y yp yq)))))
  go (no xp) (no xq) (yes ≡.refl) _ =
    trans (c⇐ p q (axiom (e15 pq xp (sy xq))))
          (refl′ (≡.cong₂ Hs (≡.sym (τ-o p q x xp xq)) (≡.sym (τ-p p q))))
  go (no xp) (no xq) (no yp) (yes ≡.refl) =
    trans (cong (refl′ (≡.sym swapX)) (cright refl′ (≡.sym swapX)))
          (trans (c⇐ q p (axiom (e15 (sy pq) xq (sy xp))))
                 (refl′ (≡.cong₂ Hs (≡.sym (τ-o p q x xp xq)) (≡.sym (τ-q p q pq)))))
  go (no xp) (no xq) (no yp) (no yq) =
    trans (fix⇒ p q (axiom (e8 xy pq xp xq yp yq)))
          (refl′ (≡.cong₂ Hs (≡.sym (τ-o p q x xp xq)) (≡.sym (τ-o p q y yp yq))))

conjXsᶜ : ∀ p q x y → Xs p q • Xs x y • Xs p q ≈ᶜ Xs (τ p q x) (τ p q y)
conjXsᶜ p q x y with p FinP.≟ q
... | yes ≡.refl = trans (conj-same p) (refl′ (≡.cong₂ Xs (≡.sym (τ-refl p x)) (≡.sym (τ-refl p y))))
... | no pq with x FinP.≟ y
...   | yes ≡.refl = trans (cright cleft refl′ (Xs-refl x))
                       (trans (conj-ε p q) (refl′ (≡.sym (Xs-refl (τ p q x)))))
...   | no xy = go (x FinP.≟ p) (x FinP.≟ q) (y FinP.≟ p) (y FinP.≟ q)
  where
  swapX : Xs q p ≡ Xs p q
  swapX = Xs-swap q p
  -- Xs p q Xs p q Xs p q = Xs p q.
  XXX : Xs p q • Xs p q • Xs p q ≈ᶜ Xs p q
  XXX = trans (sym assoc) (trans (cleft XX p q) left-unit)
  go : Dec (x ≡ p) → Dec (x ≡ q) → Dec (y ≡ p) → Dec (y ≡ q) →
       Xs p q • Xs x y • Xs p q ≈ᶜ Xs (τ p q x) (τ p q y)
  go (yes ≡.refl) _ _ (yes ≡.refl) =
    trans XXX (trans (refl′ (Xs-swap p q)) (refl′ (≡.cong₂ Xs (≡.sym (τ-p p q)) (≡.sym (τ-q p q pq)))))
  go (yes ≡.refl) _ (yes e) _ = ⊥-elim (xy (≡.sym e))
  go (yes ≡.refl) _ (no yp) (no yq) =
    trans (c⇐ p q (axiom (e12 pq (sy yp) (sy yq))))
          (refl′ (≡.cong₂ Xs (≡.sym (τ-p p q)) (≡.sym (τ-o p q y yp yq))))
  go (no xp) (yes ≡.refl) (yes ≡.refl) _ =
    trans (cright cleft refl′ swapX) (trans XXX (refl′ (≡.cong₂ Xs (≡.sym (τ-q p q pq)) (≡.sym (τ-p p q)))))
  go (no xp) (yes ≡.refl) (no yp) (yes e) = ⊥-elim (xy (≡.sym e))
  go (no xp) (yes ≡.refl) (no yp) (no yq) =
    trans (cong (refl′ (≡.sym swapX)) (cright refl′ (≡.sym swapX)))
          (trans (c⇐ q p (axiom (e12 (sy pq) (sy yq) (sy yp))))
                 (refl′ (≡.cong₂ Xs (≡.sym (τ-q p q pq)) (≡.sym (τ-o p q y yp yq)))))
  go (no xp) (no xq) (yes ≡.refl) _ =
    trans (c⇐ p q (axiom (e13 pq xp (sy xq))))
          (refl′ (≡.cong₂ Xs (≡.sym (τ-o p q x xp xq)) (≡.sym (τ-p p q))))
  go (no xp) (no xq) (no yp) (yes ≡.refl) =
    trans (cong (refl′ (≡.sym swapX)) (cright refl′ (≡.sym swapX)))
          (trans (c⇐ q p (axiom (e13 (sy pq) xq (sy xp))))
                 (refl′ (≡.cong₂ Xs (≡.sym (τ-o p q x xp xq)) (≡.sym (τ-q p q pq)))))
  go (no xp) (no xq) (no yp) (no yq) =
    trans (fix⇒ p q (axiom (e9 xy pq xp xq yp yq)))
          (refl′ (≡.cong₂ Xs (≡.sym (τ-o p q x xp xq)) (≡.sym (τ-o p q y yp yq))))

conjˢ : ∀ p q s → Xs p q • ⟦ s ⟧ˢ • Xs p q ≈ᶜ ⟦ relabelˢ (τ p q) s ⟧ˢ
conjˢ p q (hs a b) = conjHsᶜ p q a b
conjˢ p q (xs a b) = conjXsᶜ p q a b
conjˢ p q (zs a)   = conjZᶜ p q a

conj⟦⟧ : ∀ p q ss → Xs p q • ⟦ ss ⟧ • Xs p q ≈ᶜ ⟦ relabel (τ p q) ss ⟧
conj⟦⟧ p q [] = conj-ε p q
conj⟦⟧ p q (s ∷ []) = conjˢ p q s
conj⟦⟧ p q (s ∷ s′ ∷ ss) = trans (conj-• p q ⟦ s ⟧ˢ ⟦ s′ ∷ ss ⟧) (cong (conjˢ p q s) (conj⟦⟧ p q (s′ ∷ ss)))

-- Equations relabel along (p q).
relabel-eq : ∀ p q {ss ss′} → ⟦ ss ⟧ ≈ᶜ ⟦ ss′ ⟧ → ⟦ relabel (τ p q) ss ⟧ ≈ᶜ ⟦ relabel (τ p q) ss′ ⟧
relabel-eq p q {ss} {ss′} h =
  trans (sym (conj⟦⟧ p q ss)) (trans (cright cleft h) (conj⟦⟧ p q ss′))

------------------------------------------------------------------------
-- Templates: equations on labels Fin m, placed by ℓ : Fin m → Fin n

data Symᵗ (m : ℕ) : Set where
  hᵗ xᵗ : Fin m → Fin m → Symᵗ m
  zᵗ    : Fin m → Symᵗ m

placeˢ : ∀ {m} → (Fin m → Fin n) → Symᵗ m → Sym
placeˢ ℓ (hᵗ i j) = hs (ℓ i) (ℓ j)
placeˢ ℓ (xᵗ i j) = xs (ℓ i) (ℓ j)
placeˢ ℓ (zᵗ i)   = zs (ℓ i)

place : ∀ {m} → (Fin m → Fin n) → List (Symᵗ m) → List Sym
place ℓ = map (placeˢ ℓ)

private
  relabel-place : ∀ {m} (f : Fin n → Fin n) (ℓ : Fin m → Fin n) T → relabel f (place ℓ T) ≡ place (f ∘ ℓ) T
  relabel-place f ℓ [] = ≡.refl
  relabel-place f ℓ (hᵗ i j ∷ T) = ≡.cong (hs (f (ℓ i)) (f (ℓ j)) ∷_) (relabel-place f ℓ T)
  relabel-place f ℓ (xᵗ i j ∷ T) = ≡.cong (xs (f (ℓ i)) (f (ℓ j)) ∷_) (relabel-place f ℓ T)
  relabel-place f ℓ (zᵗ i ∷ T) = ≡.cong (zs (f (ℓ i)) ∷_) (relabel-place f ℓ T)

place-ext : ∀ {m} {ℓ ℓ₁ : Fin m → Fin n} → (∀ i → ℓ i ≡ ℓ₁ i) → ∀ T → place ℓ T ≡ place ℓ₁ T
place-ext e [] = ≡.refl
place-ext e (hᵗ i j ∷ T) = ≡.cong₂ _∷_ (≡.cong₂ hs (e i) (e j)) (place-ext e T)
place-ext e (xᵗ i j ∷ T) = ≡.cong₂ _∷_ (≡.cong₂ xs (e i) (e j)) (place-ext e T)
place-ext e (zᵗ i ∷ T) = ≡.cong₂ _∷_ (≡.cong zs (e i)) (place-ext e T)

-- A list of transpositions, applied from the last.
τs : List (Fin n × Fin n) → Fin n → Fin n
τs [] x = x
τs ((p , q) ∷ ps) x = τ p q (τs ps x)

τs-++ : ∀ ps qs x → τs (ps ++ qs) x ≡ τs ps (τs qs x)
τs-++ [] qs x = ≡.refl
τs-++ ((p , q) ∷ ps) qs x = ≡.cong (τ p q) (τs-++ ps qs x)

-- A template equation placed by ℓ moves to any ℓ₁ that a list of
-- transpositions takes ℓ to.
move : ∀ {m} (ps : List (Fin n × Fin n)) {ℓ ℓ₁ : Fin m → Fin n} → (∀ i → τs ps (ℓ i) ≡ ℓ₁ i) →
       ∀ {T T₁} → ⟦ place ℓ T ⟧ ≈ᶜ ⟦ place ℓ T₁ ⟧ → ⟦ place ℓ₁ T ⟧ ≈ᶜ ⟦ place ℓ₁ T₁ ⟧
move [] {ℓ} {ℓ₁} e {T} {T₁} h =
  trans (refl′ (≡.cong ⟦_⟧ (place-ext (≡.sym ∘ e) T))) (trans h (refl′ (≡.cong ⟦_⟧ (place-ext e T₁))))
move ((p , q) ∷ ps) {ℓ} {ℓ₁} e {T} {T₁} h =
  trans (refl′ (≡.cong ⟦_⟧ (≡.trans (place-ext (≡.sym ∘ e) T) (≡.sym (relabel-place (τ p q) (τs ps ∘ ℓ) T)))))
        (trans (relabel-eq p q {place (τs ps ∘ ℓ) T} {place (τs ps ∘ ℓ) T₁} (move ps {ℓ} {τs ps ∘ ℓ} (λ i → ≡.refl) {T} {T₁} h))
               (refl′ (≡.cong ⟦_⟧ (≡.trans (relabel-place (τ p q) (τs ps ∘ ℓ) T₁) (place-ext e T₁)))))

------------------------------------------------------------------------
-- Templates from letter lists, and back along an embedding

ofGen : ∀ {m} → Gen m → Symᵗ m
ofGen (X-gen i j _) = xᵗ i j
ofGen (K-gen i j _) = hᵗ i j
ofGen (i-gen i)     = zᵗ i

private
  rcm : ∀ {m} {a b : Fin m} → .(a < b) → a < b
  rcm {a = a} {b} lt = recompute (a FinP.<? b) lt

-- The letters, one by one.
letter : ∀ {m} (e : Emb m n) (g : Gen m) → ⟦ placeˢ (ι e) (ofGen g) ⟧ˢ ≈ᶜ [ gen e g ]ʷ
letter e (X-gen i j p) = refl′ (Xs-< (mono e (rcm p)))
letter e (K-gen i j p) = refl′ (Hs-< (mono e (rcm p)))
letter e (i-gen i)     = refl

-- A list of letters on m indices, placed by an increasing map, is its
-- image (with the trailing ε of the list word).
placeW : ∀ {m} (e : Emb m n) (L : List (Gen m)) →
         ⟦ place (ι e) (map ofGen L) ⟧ ≈ᶜ word e (AW.word-of-list L)
placeW e [] = refl
placeW e (g ∷ []) = trans (letter e g) (sym right-unit)
placeW e (g ∷ g′ ∷ L) = cong (letter e g) (placeW e (g′ ∷ L))

