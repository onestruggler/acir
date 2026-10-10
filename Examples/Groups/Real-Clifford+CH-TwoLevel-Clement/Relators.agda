------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations of the routes, in the relations of Figure 6.
--
-- Clément's diagrams (20) and (30) hold on the first four and six
-- indices in his relations, whose (20) and (21) are axioms there
-- (Diagram20, Diagram30).  A list of transpositions takes the first
-- indices to any others (transport), and conjugation by it moves the
-- diagrams there (ClementLocal.move); his relations and Figure 6
-- generate the same congruence (Equivalence), so the diagrams hold in
-- Figure 6 at any injective placement (core20, core30).
--
-- A route that starts with signs Z on indices other than a, and ends
-- with the letters that undo them, has the relation of its core
-- (decorate): Z x commutes with Hs a b for x ∉ {a, b}, and
-- Xs a b • Hs a b • Z b = Hs a b.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Relators where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_ ; _↑ˡ_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat.Base as ℕ using (ℕ ; z≤n ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Function.Base using (_∘_)
import Function.Bundles as Fun
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Clement
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Embedding using (Emb ; word ; incl+ ; module Pull)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric as Sym
import Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence as EQ
import Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence.ClementLocal as CLm
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check using (Let ; Hˡ ; Xˡ ; Zˡ ; Route)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Placed as Placed
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Diagram30 as D30
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Diagram20 as D20

private
  ⟪_⟫ : ∀ {m} → List (Gen m) → Word (Gen m)
  ⟪_⟫ = TW.Associative.word-of-list
    where import Presentation.Tactics.Words as TW

------------------------------------------------------------------------
-- Transpositions take one injective placement to any other

module _ {n : ℕ} where

  open CLm {n} using (τs ; τs-++ ; τ-refl)
  open Sym {n} using (τ ; τ-p ; τ-q ; τ-o ; τ-τ ; τ-inj)

  private
    τ-self : ∀ (p q x : Fin n) → τ p q (τ p q x) ≡ x
    τ-self p q x with p FinP.≟ q
    ... | yes ≡.refl = ≡.trans (τ-refl p (τ p p x)) (τ-refl p x)
    ... | no p≢q = τ-τ p q x p≢q

    τ-at-q : ∀ (p q : Fin n) → τ p q q ≡ p
    τ-at-q p q with p FinP.≟ q
    ... | yes ≡.refl = τ-refl p p
    ... | no p≢q = τ-q p q p≢q

    τ-injective : ∀ (p q : Fin n) {x y} → τ p q x ≡ τ p q y → x ≡ y
    τ-injective p q {x} {y} e = ≡.trans (≡.sym (τ-self p q x)) (≡.trans (≡.cong (τ p q) e) (τ-self p q y))

  transport : ∀ {m} (s t : Fin m → Fin n) → (∀ {i j} → s i ≡ s j → i ≡ j) → (∀ {i j} → t i ≡ t j → i ≡ j) →
              Σ (List (Fin n × Fin n)) λ ps → (∀ i → τs ps (s i) ≡ t i) ×
                                               (∀ x → (∀ i → s i ≢ x) → (∀ i → t i ≢ x) → τs ps x ≡ x)
  transport {ℕ.zero} s t _ _ = [] , (λ ()) , (λ x _ _ → ≡.refl)
  transport {ℕ.suc m} s t s-inj t-inj = ps′ ++ ((s zero , t zero) ∷ []) , at , fixed
    where
    q : Fin n → Fin n
    q = τ (s zero) (t zero)
    s′ t′ : Fin m → Fin n
    s′ i = q (s (suc i))
    t′ i = t (suc i)
    s′-inj : ∀ {i j} → s′ i ≡ s′ j → i ≡ j
    s′-inj e = FinP.suc-injective (s-inj (τ-injective (s zero) (t zero) e))
    t′-inj : ∀ {i j} → t′ i ≡ t′ j → i ≡ j
    t′-inj e = FinP.suc-injective (t-inj e)
    rec = transport s′ t′ s′-inj t′-inj
    ps′ = proj₁ rec
    -- t zero lies outside both images.
    out-s : ∀ i → s′ i ≢ t zero
    out-s i e with s-inj (≡.trans (≡.sym (τ-self (s zero) (t zero) (s (suc i))))
                          (≡.trans (≡.cong q e) (τ-at-q (s zero) (t zero))))
    ... | ()
    out-t : ∀ i → t′ i ≢ t zero
    out-t i e with t-inj e
    ... | ()
    at : ∀ i → τs (ps′ ++ ((s zero , t zero) ∷ [])) (s i) ≡ t i
    at zero = ≡.trans (τs-++ ps′ _ (s zero))
                (≡.trans (≡.cong (τs ps′) (τ-p (s zero) (t zero))) (proj₂ (proj₂ rec) (t zero) out-s out-t))
    at (suc i) = ≡.trans (τs-++ ps′ _ (s (suc i))) (proj₁ (proj₂ rec) i)
    fixed : ∀ x → (∀ i → s i ≢ x) → (∀ i → t i ≢ x) → τs (ps′ ++ ((s zero , t zero) ∷ [])) x ≡ x
    fixed x xs xt =
      ≡.trans (τs-++ ps′ _ x)
        (≡.trans (≡.cong (τs ps′) qx) (proj₂ (proj₂ rec) x out′ (λ i → xt (suc i))))
      where
      qx : q x ≡ x
      qx = τ-o (s zero) (t zero) x (λ e → xs zero (≡.sym e)) (λ e → xt zero (≡.sym e))
      out′ : ∀ i → s′ i ≢ x
      out′ i e = xs (suc i) (≡.trans (≡.sym (τ-self (s zero) (t zero) (s (suc i)))) (≡.trans (≡.cong q e) qx))

------------------------------------------------------------------------
-- Routes from letter lists, and their words as placed templates

toLet : ∀ {m} → Gen m → Let m
toLet (H-gen i j _) = Hˡ i j
toLet (X-gen i j _) = Xˡ i j
toLet (Z-gen i) = Zˡ i

-- The route of a word given as a list in operator order.
fromGens : ∀ {m} → List (Gen m) → Route m
fromGens [] = []
fromGens (g ∷ L) = fromGens L ++ (toLet g ∷ [])

module Words {n m : ℕ} (Γ : WRel (Gen n)) (ι : Fin m → Fin n) where

  open PB Γ
  open Placed ι using (wordL ; wordR)
  open CLm {n} using (⟦_⟧ ; ⟦_⟧ˢ ; place ; placeˢ ; ofGen)

  wordR-++ : ∀ xs ys → wordR (xs ++ ys) ≈ wordR ys • wordR xs
  wordR-++ [] ys = sym right-unit
  wordR-++ (x ∷ xs) ys = trans (cleft wordR-++ xs ys) assoc

  -- The letters agree.
  letter≡ : ∀ g → wordL (toLet g) ≡ ⟦ placeˢ ι (ofGen g) ⟧ˢ
  letter≡ (H-gen i j _) = ≡.refl
  letter≡ (X-gen i j _) = ≡.refl
  letter≡ (Z-gen i) = ≡.refl

  as-template : ∀ L → wordR (fromGens L) ≈ ⟦ place ι (map ofGen L) ⟧
  as-template [] = refl
  as-template (g ∷ []) = trans (wordR-++ [] (toLet g ∷ [])) (trans right-unit (trans left-unit (refl′ (letter≡ g))))
    where
    refl′ : ∀ {u v} → u ≡ v → u ≈ v
    refl′ ≡.refl = refl
  as-template (g ∷ g′ ∷ L) =
    trans (wordR-++ (fromGens (g′ ∷ L)) (toLet g ∷ []))
      (cong (trans left-unit (refl′ (letter≡ g))) (as-template (g′ ∷ L)))
    where
    refl′ : ∀ {u v} → u ≡ v → u ≈ v
    refl′ ≡.refl = refl

------------------------------------------------------------------------
-- The diagrams on the first indices, in Clément's relations

module Base6 (k : ℕ) where

  e : Emb 6 (6 ℕ.+ k)
  e = incl+ 6 k

  open PB (_===ᶜ_ {6 ℕ.+ k}) hiding (_===_)
  open PP (_===ᶜ_ {6 ℕ.+ k})
  module P = Pull e (_===ᶜ_ {6 ℕ.+ k})
  open CLm {6 ℕ.+ k} using (⟦_⟧ ; place ; ofGen ; placeW ; c-local)

  private
    f0 f1 f2 f3 f4 f5 : Fin (6 ℕ.+ k)
    f0 = zero
    f1 = suc zero
    f2 = suc (suc zero)
    f3 = suc (suc (suc zero))
    f4 = suc (suc (suc (suc zero)))
    f5 = suc (suc (suc (suc (suc zero))))
    l01 : f0 < f1
    l01 = s≤s z≤n
    l02 : f0 < f2
    l02 = s≤s z≤n
    l04 : f0 < f4
    l04 = s≤s z≤n
    l13 : f1 < f3
    l13 = s≤s (s≤s z≤n)
    l15 : f1 < f5
    l15 = s≤s (s≤s z≤n)

  r21w : word e ⟪ D30.L21 ⟫ ≈ word e ⟪ D30.R21 ⟫
  r21w = trans (by-assoc auto)
    (trans (axiom (e21 ≡.refl ≡.refl ≡.refl ≡.refl ≡.refl ≡.refl l01 l02 l13 l04 l15)) (by-assoc auto))

  d30₀ : word e ⟪ D30.Route ⟫ ≈ word e ⟪ D30.C0w ⟫
  d30₀ = P.push (D30.From.d30 P.pull (P.pull-local c-local) (P.hyp r21w))

  base : ⟦ place (_↑ˡ k) (map ofGen D30.Route) ⟧ ≈ ⟦ place (_↑ˡ k) (map ofGen D30.C0w) ⟧
  base = trans (placeW e D30.Route) (trans d30₀ (sym (placeW e D30.C0w)))

module Base4 (k : ℕ) where

  e : Emb 4 (4 ℕ.+ k)
  e = incl+ 4 k

  open PB (_===ᶜ_ {4 ℕ.+ k}) hiding (_===_)
  open PP (_===ᶜ_ {4 ℕ.+ k})
  module P = Pull e (_===ᶜ_ {4 ℕ.+ k})
  open CLm {4 ℕ.+ k} using (⟦_⟧ ; place ; ofGen ; placeW ; c-local)

  private
    f0 f1 f2 f3 : Fin (4 ℕ.+ k)
    f0 = zero
    f1 = suc zero
    f2 = suc (suc zero)
    f3 = suc (suc (suc zero))
    l01 : f0 < f1
    l01 = s≤s z≤n
    l02 : f0 < f2
    l02 = s≤s z≤n
    l13 : f1 < f3
    l13 = s≤s (s≤s z≤n)

  r20w : word e ⟪ D20.L20 ⟫ ≈ word e ⟪ D20.R20 ⟫
  r20w = trans (by-assoc auto) (trans (axiom (e20 ≡.refl ≡.refl ≡.refl ≡.refl l01 l02 l13)) (by-assoc auto))

  d20₀ : word e ⟪ D20.Route ⟫ ≈ word e ⟪ D20.C0w ⟫
  d20₀ = P.push (D20.From.d20 P.pull (P.pull-local c-local) (P.hyp r20w))

  base : ⟦ place (_↑ˡ k) (map ofGen D20.Route) ⟧ ≈ ⟦ place (_↑ˡ k) (map ofGen D20.C0w) ⟧
  base = trans (placeW e D20.Route) (trans d20₀ (sym (placeW e D20.C0w)))

------------------------------------------------------------------------
-- The diagrams at any injective placement, in Figure 6

private
  split : ∀ {m n} → m ℕ.≤ n → Σ ℕ λ k → n ≡ m ℕ.+ k
  split le = let (k , e) = ℕP.m≤n⇒∃[o]m+o≡n le in k , ≡.sym e

  ↑ˡ-inj : ∀ {m} (k : ℕ) {i j : Fin m} → i ↑ˡ k ≡ j ↑ˡ k → i ≡ j
  ↑ˡ-inj k {i} {j} = FinP.↑ˡ-injective k i j

core30 : ∀ {n} (ℓ : Fin 6 → Fin n) → (∀ {i j} → ℓ i ≡ ℓ j → i ≡ j) →
         PB._≈_ (_===_ {n}) (Placed.wordR ℓ (fromGens D30.Route)) (Sym.Hs (ℓ zero) (ℓ (suc zero)))
core30 {n} ℓ inj with split {6} {n} (FinP.injective⇒≤ inj)
... | k , ≡.refl =
  PB.trans (Words.as-template (_===_ {6 ℕ.+ k}) ℓ D30.Route)
    (Fun.Equivalence.from EQ.equivalent
      (CLm.move {6 ℕ.+ k} (proj₁ tr) {_↑ˡ k} {ℓ} (proj₁ (proj₂ tr)) {map CLm.ofGen D30.Route} {map CLm.ofGen D30.C0w} (Base6.base k)))
  where
  tr = transport (_↑ˡ k) ℓ (↑ˡ-inj k) inj

core20 : ∀ {n} (ℓ : Fin 4 → Fin n) → (∀ {i j} → ℓ i ≡ ℓ j → i ≡ j) →
         PB._≈_ (_===_ {n}) (Placed.wordR ℓ (fromGens D20.Route)) (Sym.Hs (ℓ zero) (ℓ (suc zero)))
core20 {n} ℓ inj with split {4} {n} (FinP.injective⇒≤ inj)
... | k , ≡.refl =
  PB.trans (Words.as-template (_===_ {4 ℕ.+ k}) ℓ D20.Route)
    (Fun.Equivalence.from EQ.equivalent
      (CLm.move {4 ℕ.+ k} (proj₁ tr) {_↑ˡ k} {ℓ} (proj₁ (proj₂ tr)) {map CLm.ofGen D20.Route} {map CLm.ofGen D20.C0w} (Base4.base k)))
  where
  tr = transport (_↑ˡ k) ℓ (↑ˡ-inj k) inj

------------------------------------------------------------------------
-- Decorated routes

-- The letter that undoes a sign Z at l after the core H a b.
undo : ∀ {m} (a b l : Fin m) → Let m
undo a b l with l FinP.≟ b
... | yes _ = Xˡ a b
... | no _ = Zˡ l

signs : ∀ {m} → List (Fin m) → Route m
signs = map Zˡ

closing : ∀ {m} (a b : Fin m) → List (Fin m) → Route m
closing a b [] = []
closing a b (l ∷ Q) = closing a b Q ++ (undo a b l ∷ [])

-- Signs, then the core, then the letters that undo the signs.
decorate : ∀ {m} (a b : Fin m) (Q : List (Fin m)) (core : Route m) → Route m
decorate a b Q core = signs Q ++ (core ++ closing a b Q)

-- With the indices of the core H exchanged, the letters that turn
-- Hs a b into Hs b a.
flipped : ∀ {m} (a b : Fin m) → Route m
flipped a b = Zˡ b ∷ Xˡ a b ∷ []

module Deco {n : ℕ} where

  open PB (_===ᶜ_ {n}) hiding (_===_)
  open PP (_===ᶜ_ {n})
  open Sym {n} using (Hs ; Xs)
  open import Relation.Binary.Reasoning.Setoid word-setoid

  Z-Z : ∀ {x : Fin n} → Z x • Z x ≈ ε
  Z-Z = axiom e1

  -- Z x past Hs a b.
  ZHZ : ∀ {a b x : Fin n} → a ≢ b → x ≢ a → x ≢ b → Z x • Hs a b • Z x ≈ Hs a b
  ZHZ {a} {b} {x} ab xa xb = begin
    Z x • Hs a b • Z x      ≈⟨ cright sym (axiom (e5 ab xa xb)) ⟩
    Z x • Z x • Hs a b      ≈⟨ sym assoc ⟩
    (Z x • Z x) • Hs a b    ≈⟨ cleft Z-Z ⟩
    ε • Hs a b              ≈⟨ left-unit ⟩
    Hs a b                  ∎

  -- Xs a b • Hs a b = Hs a b • Z b, from (18).
  XH : ∀ {a b : Fin n} → a ≢ b → Xs a b • Hs a b ≈ Hs a b • Z b
  XH {a} {b} ab = begin
    Xs a b • Hs a b                        ≈⟨ sym left-unit ⟩
    ε • Xs a b • Hs a b                    ≈⟨ cleft sym (axiom (e2 ab)) ⟩
    (Hs a b • Hs a b) • Xs a b • Hs a b    ≈⟨ assoc ⟩
    Hs a b • Hs a b • Xs a b • Hs a b      ≈⟨ cright sym assoc ⟩
    Hs a b • (Hs a b • Xs a b) • Hs a b    ≈⟨ cright cleft axiom (e18 ab) ⟩
    Hs a b • (Z b • Hs a b) • Hs a b       ≈⟨ cright assoc ⟩
    Hs a b • Z b • (Hs a b • Hs a b)       ≈⟨ cright cright axiom (e2 ab) ⟩
    Hs a b • Z b • ε                       ≈⟨ cright right-unit ⟩
    Hs a b • Z b                           ∎

  XHZ : ∀ {a b : Fin n} → a ≢ b → Xs a b • Hs a b • Z b ≈ Hs a b
  XHZ {a} {b} ab = begin
    Xs a b • Hs a b • Z b      ≈⟨ sym assoc ⟩
    (Xs a b • Hs a b) • Z b    ≈⟨ cleft XH ab ⟩
    (Hs a b • Z b) • Z b       ≈⟨ assoc ⟩
    Hs a b • Z b • Z b         ≈⟨ cright Z-Z ⟩
    Hs a b • ε                 ≈⟨ right-unit ⟩
    Hs a b                     ∎

  -- Xs a b • Z b • Hs a b = Hs b a.
  XZH : ∀ {a b : Fin n} → a ≢ b → Xs a b • Z b • Hs a b ≈ Hs b a
  XZH {a} {b} ab = trans (cright sym (axiom (e18 ab))) (CLm.Hs-flipᶜ ab)

  module Placed-at {m : ℕ} (ι : Fin m → Fin n) (inj : ∀ {i j} → ι i ≡ ι j → i ≡ j) where

    open Placed ι using (wordL ; wordR)
    open Words (_===ᶜ_ {n}) ι using (wordR-++)

    private
      ι≢ : ∀ {i j} → i ≢ j → ι i ≢ ι j
      ι≢ ne e = ne (inj e)

      undo-rel : ∀ (a b l : Fin m) → a ≢ b → l ≢ a → wordL (undo a b l) • Hs (ι a) (ι b) • Z (ι l) ≈ Hs (ι a) (ι b)
      undo-rel a b l ab la with l FinP.≟ b
      ... | yes ≡.refl = XHZ (ι≢ ab)
      ... | no lb = ZHZ (ι≢ ab) (ι≢ la) (ι≢ lb)

    -- Decorating a core keeps its relation.
    decorate-rel : ∀ (a b : Fin m) → a ≢ b → (Q : List (Fin m)) → All (_≢ a) Q → ∀ core →
                   wordR core ≈ Hs (ι a) (ι b) → wordR (decorate a b Q core) ≈ Hs (ι a) (ι b)
    decorate-rel a b ab [] [] core h = trans (wordR-++ core []) (trans left-unit h)
    decorate-rel a b ab (l ∷ Q) (la ∷ ok) core h = begin
      wordR (signs Q ++ (core ++ (closing a b Q ++ u ∷ []))) • Z (ι l)
        ≈⟨ cleft refl′ (≡.cong wordR (reassoc (signs Q) core (closing a b Q))) ⟩
      wordR (decorate a b Q core ++ u ∷ []) • Z (ι l)
        ≈⟨ cleft wordR-++ (decorate a b Q core) (u ∷ []) ⟩
      ((ε • wordL u) • wordR (decorate a b Q core)) • Z (ι l)
        ≈⟨ cleft cong left-unit (decorate-rel a b ab Q ok core h) ⟩
      (wordL u • Hs (ι a) (ι b)) • Z (ι l)
        ≈⟨ assoc ⟩
      wordL u • Hs (ι a) (ι b) • Z (ι l)
        ≈⟨ undo-rel a b l ab la ⟩
      Hs (ι a) (ι b) ∎
      where
      u = undo a b l
      refl′ : ∀ {w v} → w ≡ v → w ≈ v
      refl′ ≡.refl = refl
      reassoc : ∀ (xs ys zs : Route m) → xs ++ (ys ++ (zs ++ u ∷ [])) ≡ (xs ++ (ys ++ zs)) ++ u ∷ []
      reassoc xs ys zs = ≡.trans (≡.cong (xs ++_) (≡.sym (LP.++-assoc ys zs (u ∷ [])))) (≡.sym (LP.++-assoc xs (ys ++ zs) (u ∷ [])))
        where import Data.List.Properties as LP

    -- And flipping the core H.
    flipped-rel : ∀ (a b : Fin m) → a ≢ b → ∀ r → wordR r ≈ Hs (ι a) (ι b) → wordR (r ++ flipped a b) ≈ Hs (ι b) (ι a)
    flipped-rel a b ab r h = begin
      wordR (r ++ flipped a b)                          ≈⟨ wordR-++ r (flipped a b) ⟩
      ((ε • Xs (ι a) (ι b)) • Z (ι b)) • wordR r         ≈⟨ cong (cleft left-unit) h ⟩
      (Xs (ι a) (ι b) • Z (ι b)) • Hs (ι a) (ι b)        ≈⟨ assoc ⟩
      Xs (ι a) (ι b) • Z (ι b) • Hs (ι a) (ι b)          ≈⟨ XZH (ι≢ ab) ⟩
      Hs (ι b) (ι a)                                    ∎

------------------------------------------------------------------------
-- The routes of the case analysis, and their relations in Figure 6

-- Relabelling the indices of a route.
relabelL : ∀ {m m′} → (Fin m → Fin m′) → Let m → Let m′
relabelL f (Hˡ i j) = Hˡ (f i) (f j)
relabelL f (Xˡ i j) = Xˡ (f i) (f j)
relabelL f (Zˡ i) = Zˡ (f i)

relabelR : ∀ {m m′} → (Fin m → Fin m′) → Route m → Route m′
relabelR f = map (relabelL f)

private
  wordR-relabel : ∀ {n m m′} (ι : Fin m′ → Fin n) (f : Fin m → Fin m′) (r : Route m) →
                  Placed.wordR ι (relabelR f r) ≡ Placed.wordR (ι ∘ f) r
  wordR-relabel ι f [] = ≡.refl
  wordR-relabel ι f (Hˡ i j ∷ r) = ≡.cong (_• _) (wordR-relabel ι f r)
  wordR-relabel ι f (Xˡ i j ∷ r) = ≡.cong (_• _) (wordR-relabel ι f r)
  wordR-relabel ι f (Zˡ i ∷ r) = ≡.cong (_• _) (wordR-relabel ι f r)

-- The diagrams at any injective placement, in Clément's relations.
core30ᶜ : ∀ {n} (ℓ : Fin 6 → Fin n) → (∀ {i j} → ℓ i ≡ ℓ j → i ≡ j) →
          PB._≈_ (_===ᶜ_ {n}) (Placed.wordR ℓ (fromGens D30.Route)) (Sym.Hs (ℓ zero) (ℓ (suc zero)))
core30ᶜ {n} ℓ inj with split {6} {n} (FinP.injective⇒≤ inj)
... | k , ≡.refl =
  PB.trans (Words.as-template (_===ᶜ_ {6 ℕ.+ k}) ℓ D30.Route)
    (CLm.move {6 ℕ.+ k} (proj₁ tr) {_↑ˡ k} {ℓ} (proj₁ (proj₂ tr)) {map CLm.ofGen D30.Route} {map CLm.ofGen D30.C0w} (Base6.base k))
  where
  tr = transport (_↑ˡ k) ℓ (↑ˡ-inj k) inj

core20ᶜ : ∀ {n} (ℓ : Fin 4 → Fin n) → (∀ {i j} → ℓ i ≡ ℓ j → i ≡ j) →
          PB._≈_ (_===ᶜ_ {n}) (Placed.wordR ℓ (fromGens D20.Route)) (Sym.Hs (ℓ zero) (ℓ (suc zero)))
core20ᶜ {n} ℓ inj with split {4} {n} (FinP.injective⇒≤ inj)
... | k , ≡.refl =
  PB.trans (Words.as-template (_===ᶜ_ {4 ℕ.+ k}) ℓ D20.Route)
    (CLm.move {4 ℕ.+ k} (proj₁ tr) {_↑ˡ k} {ℓ} (proj₁ (proj₂ tr)) {map CLm.ofGen D20.Route} {map CLm.ofGen D20.C0w} (Base4.base k))
  where
  tr = transport (_↑ˡ k) ℓ (↑ˡ-inj k) inj

-- A route built on a diagram: signs Q (on local indices other than
-- lab 0), the diagram relabelled by lab, the letters undoing the signs, and
-- with flip the letters exchanging the two indices of its H.
module Leaf {n m : ℕ} (ι : Fin m → Fin n) (inj : ∀ {i j} → ι i ≡ ι j → i ≡ j) where

  open Placed ι using (wordR)

  private
    ∘-inj : ∀ {k} (f : Fin k → Fin m) → (∀ {i j} → f i ≡ f j → i ≡ j) → ∀ {i j} → ι (f i) ≡ ι (f j) → i ≡ j
    ∘-inj f f-inj e = f-inj (inj e)

    0≢1 : ∀ {k} (f : Fin (ℕ.suc (ℕ.suc k)) → Fin m) → (∀ {i j} → f i ≡ f j → i ≡ j) → f zero ≢ f (suc zero)
    0≢1 f f-inj e with f-inj e
    ... | ()

    module Gen-route {k : ℕ} (core : Route (ℕ.suc (ℕ.suc k)))
        (core-rel : ∀ (ℓ : Fin (ℕ.suc (ℕ.suc k)) → Fin n) → (∀ {i j} → ℓ i ≡ ℓ j → i ≡ j) →
                    PB._≈_ (_===ᶜ_ {n}) (Placed.wordR ℓ core) (Sym.Hs (ℓ zero) (ℓ (suc zero)))) where

      route : (lab : Fin (ℕ.suc (ℕ.suc k)) → Fin m) → List (Fin m) → Bool → Route m
      route lab Q false = decorate (lab zero) (lab (suc zero)) Q (relabelR lab core)
      route lab Q true = route lab Q false ++ flipped (lab zero) (lab (suc zero))

      relᶜ : (lab : Fin (ℕ.suc (ℕ.suc k)) → Fin m) → (∀ {i j} → lab i ≡ lab j → i ≡ j) →
             (Q : List (Fin m)) → All (_≢ lab zero) Q →
             PB._≈_ (_===ᶜ_ {n}) (wordR (route lab Q false)) (Sym.Hs (ι (lab zero)) (ι (lab (suc zero))))
      relᶜ lab lab-inj Q ok =
        Deco.Placed-at.decorate-rel ι inj (lab zero) (lab (suc zero)) (0≢1 lab lab-inj) Q ok (relabelR lab core)
          (≡.subst (λ w → PB._≈_ (_===ᶜ_ {n}) w (Sym.Hs (ι (lab zero)) (ι (lab (suc zero)))))
                   (≡.sym (wordR-relabel ι lab core)) (core-rel (ι ∘ lab) (∘-inj lab lab-inj)))

      rel : (lab : Fin (ℕ.suc (ℕ.suc k)) → Fin m) → (∀ {i j} → lab i ≡ lab j → i ≡ j) →
            (Q : List (Fin m)) → All (_≢ lab zero) Q →
            PB._≈_ (_===_ {n}) (wordR (route lab Q false)) (Sym.Hs (ι (lab zero)) (ι (lab (suc zero))))
      rel lab lab-inj Q ok = Fun.Equivalence.from EQ.equivalent (relᶜ lab lab-inj Q ok)

      rel-flip : (lab : Fin (ℕ.suc (ℕ.suc k)) → Fin m) → (∀ {i j} → lab i ≡ lab j → i ≡ j) →
                 (Q : List (Fin m)) → All (_≢ lab zero) Q →
                 PB._≈_ (_===_ {n}) (wordR (route lab Q true)) (Sym.Hs (ι (lab (suc zero))) (ι (lab zero)))
      rel-flip lab lab-inj Q ok =
        Fun.Equivalence.from EQ.equivalent
          (Deco.Placed-at.flipped-rel ι inj (lab zero) (lab (suc zero)) (0≢1 lab lab-inj) (route lab Q false) (relᶜ lab lab-inj Q ok))

  open Gen-route (fromGens D30.Route) core30ᶜ public
    renaming (route to route30 ; relᶜ to route30-relᶜ ; rel to route30-rel ; rel-flip to route30-flip)
  open Gen-route (fromGens D20.Route) core20ᶜ public
    renaming (route to route20 ; relᶜ to route20-relᶜ ; rel to route20-rel ; rel-flip to route20-flip)
