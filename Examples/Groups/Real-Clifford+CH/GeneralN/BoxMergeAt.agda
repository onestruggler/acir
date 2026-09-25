------------------------------------------------------------------------
-- Presentations of groups
--
-- A black and a white control merge, on any control wire (Clément,
-- Lemma D.10, Equation (309), all other controls black)
--
-- At width 5 + k: the box times the box with its control on wire c
-- white, in either order, is the box without that control — the box of
-- one control fewer placed around wire c.  On wire 2 it is (301)/(302);
-- the swap of the wires c, c + 1 passes the box (SymAt), carries X from
-- wire c to wire c + 1 (PlaceAt.X-step) and the idle wire of a
-- placement likewise (PlaceAt.placeAt-step), so the statement moves one
-- wire at a time (`conj-merge`, word algebra).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BoxMergeAt
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (<-trans ; n<1+n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex²)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat ; swapAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt
  using (placeAt ; placeAt-place ; placeAt-step ; X-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxMerge complete₂ complete₃ using (eq301 ; eq302)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (SymAt)

-- A swap is an involution (the identity out of range).
swapAt² : ∀ {n} c → n ⊢ swapAt c • swapAt c ≈ ε
swapAt² {zero}        c       = PB.left-unit
swapAt² {suc zero}    zero    = PB.left-unit
swapAt² {suc (suc n)} zero    = Ex²
swapAt² {suc n}       (suc c) = lemma-cong↑ (swapAt c • swapAt c) ε (swapAt² {n} c)

-- (309) on wire c, in both orders.
Merge Merge′ : ℕ → ℕ → Set
Merge  k c = (₁₊ (₄₊ k)) ⊢ Λ□ (₄₊ k) • (Xat c • Λ□ (₄₊ k) • Xat c) ≈ placeAt c (Λ□ (₃₊ k))
Merge′ k c = (₁₊ (₄₊ k)) ⊢ (Xat c • Λ□ (₄₊ k) • Xat c) • Λ□ (₄₊ k) ≈ placeAt c (Λ□ (₃₊ k))

module _ (k : ℕ) (complete : Complete (₁₊ k)) (symAt : SymAt (₁₊ k)) where

  private
    open Tools ((₁₊ (₄₊ k)) VRel,_===_)

    Λ : Circuit (₁₊ (₄₊ k))
    Λ = Λ□ (₄₊ k)

    u : Circuit (₄₊ k)
    u = Λ□ (₃₊ k)

    ≡⇒≈ : ∀ {a b : Circuit (₁₊ (₄₊ k))} → a ≡ b → (₁₊ (₄₊ k)) ⊢ a ≈ b
    ≡⇒≈ Eq.refl = refl

    -- Conjugating a merge by a swap S that passes the box.
    conj-merge : ∀ {S X P : Circuit (₁₊ (₄₊ k))} → (₁₊ (₄₊ k)) ⊢ S • S ≈ ε →
                 (₁₊ (₄₊ k)) ⊢ S • Λ ≈ Λ • S → (₁₊ (₄₊ k)) ⊢ Λ • (X • Λ • X) ≈ P →
                 (₁₊ (₄₊ k)) ⊢ Λ • ((S • X • S) • Λ • (S • X • S)) ≈ S • P • S
    conj-merge {S} {X} {P} SS SΛ e = begin
      Λ • ((S • X • S) • Λ • (S • X • S))
        ≈⟨ by-passoc (□ • ((□ • □ • □) • □ • (□ • □ • □))) ((□ • □) • □ • (□ • □ • □) • □ • □) Eq.refl ⟩
      (Λ • S) • X • (S • Λ • S) • X • S
        ≈⟨ cong (sym SΛ) (back _ (front _ SΛS)) ⟩
      (S • Λ) • X • Λ • X • S
        ≈⟨ by-passoc ((□ • □) • □ • □ • □ • □) (□ • (□ • (□ • □ • □)) • □) Eq.refl ⟩
      S • (Λ • (X • Λ • X)) • S
        ≈⟨ back _ (front _ e) ⟩
      S • P • S ∎
      where
      SΛS : (₁₊ (₄₊ k)) ⊢ S • Λ • S ≈ Λ
      SΛS = begin
        S • Λ • S       ≈⟨ sym assoc ⟩
        (S • Λ) • S     ≈⟨ front _ SΛ ⟩
        (Λ • S) • S     ≈⟨ trans assoc (trans (back _ SS) right-unit) ⟩
        Λ ∎

    -- The same with the box on the other side.
    conj-merge′ : ∀ {S X P : Circuit (₁₊ (₄₊ k))} → (₁₊ (₄₊ k)) ⊢ S • S ≈ ε →
                  (₁₊ (₄₊ k)) ⊢ S • Λ ≈ Λ • S → (₁₊ (₄₊ k)) ⊢ (X • Λ • X) • Λ ≈ P →
                  (₁₊ (₄₊ k)) ⊢ ((S • X • S) • Λ • (S • X • S)) • Λ ≈ S • P • S
    conj-merge′ {S} {X} {P} SS SΛ e = begin
      ((S • X • S) • Λ • (S • X • S)) • Λ
        ≈⟨ by-passoc (((□ • □ • □) • □ • (□ • □ • □)) • □) (□ • □ • (□ • □ • □) • □ • (□ • □)) Eq.refl ⟩
      S • X • (S • Λ • S) • X • (S • Λ)
        ≈⟨ back _ (back _ (cong SΛS (back _ SΛ))) ⟩
      S • X • Λ • X • (Λ • S)
        ≈⟨ by-passoc (□ • □ • □ • □ • (□ • □)) (□ • ((□ • □ • □) • □) • □) Eq.refl ⟩
      S • ((X • Λ • X) • Λ) • S
        ≈⟨ back _ (front _ e) ⟩
      S • P • S ∎
      where
      SΛS : (₁₊ (₄₊ k)) ⊢ S • Λ • S ≈ Λ
      SΛS = begin
        S • Λ • S       ≈⟨ sym assoc ⟩
        (S • Λ) • S     ≈⟨ front _ SΛ ⟩
        (Λ • S) • S     ≈⟨ trans assoc (trans (back _ SS) right-unit) ⟩
        Λ ∎

    swap² : ∀ c → (₁₊ (₄₊ k)) ⊢ swapAt c • swapAt c ≈ ε
    swap² = swapAt²

    -- The swaps and X on the controls, one wire up.
    -- Conjugating by an involution both ways.
    unconj : ∀ {S a b : Circuit (₁₊ (₄₊ k))} → (₁₊ (₄₊ k)) ⊢ S • S ≈ ε →
             (₁₊ (₄₊ k)) ⊢ S • a • S ≈ b → (₁₊ (₄₊ k)) ⊢ a ≈ S • b • S
    unconj {S} {a} {b} SS e = begin
      a                       ≈⟨ sym left-unit ⟩
      ε • a                   ≈⟨ front _ (sym SS) ⟩
      (S • S) • a             ≈⟨ assoc ⟩
      S • (S • a)             ≈⟨ back _ (sym right-unit) ⟩
      S • ((S • a) • ε)       ≈⟨ back _ (back _ (sym SS)) ⟩
      S • ((S • a) • (S • S)) ≈⟨ back _ (by-passoc ((□ • □) • (□ • □)) ((□ • □ • □) • □) Eq.refl) ⟩
      S • ((S • a • S) • S)   ≈⟨ back _ (front _ e) ⟩
      S • (b • S) ∎

    -- X and the idle wire of a placement, one wire down.
    X-down : ∀ c → c < ₄₊ k → (₁₊ (₄₊ k)) ⊢ Xat c ≈ swapAt c • Xat (suc c) • swapAt c
    X-down c b = unconj (swap² c) (X-step c b)

    place-down : ∀ c → c < ₄₊ k → (₁₊ (₄₊ k)) ⊢ placeAt c u ≈ swapAt c • placeAt (suc c) u • swapAt c
    place-down c b = unconj (swap² c) (sym (placeAt-step c u b))

    -- Carrying a merge on wire c + 1 to wire c, or on wire c to c + 1.
    down : ∀ c → c < ₄₊ k → (₁₊ (₄₊ k)) ⊢ swapAt c • Λ ≈ Λ • swapAt c → Merge k (suc c) → Merge k c
    down c b SΛ m = begin
      Λ • (Xat c • Λ • Xat c)
        ≈⟨ back _ (cong (X-down c b) (back _ (X-down c b))) ⟩
      Λ • ((swapAt c • Xat (suc c) • swapAt c) • Λ • (swapAt c • Xat (suc c) • swapAt c))
        ≈⟨ conj-merge (swap² c) SΛ m ⟩
      swapAt c • placeAt (suc c) u • swapAt c
        ≈⟨ sym (place-down c b) ⟩
      placeAt c u ∎

    down′ : ∀ c → c < ₄₊ k → (₁₊ (₄₊ k)) ⊢ swapAt c • Λ ≈ Λ • swapAt c → Merge′ k (suc c) → Merge′ k c
    down′ c b SΛ m = begin
      (Xat c • Λ • Xat c) • Λ
        ≈⟨ front _ (cong (X-down c b) (back _ (X-down c b))) ⟩
      ((swapAt c • Xat (suc c) • swapAt c) • Λ • (swapAt c • Xat (suc c) • swapAt c)) • Λ
        ≈⟨ conj-merge′ (swap² c) SΛ m ⟩
      swapAt c • placeAt (suc c) u • swapAt c
        ≈⟨ sym (place-down c b) ⟩
      placeAt c u ∎

    up : ∀ c → c < ₄₊ k → (₁₊ (₄₊ k)) ⊢ swapAt c • Λ ≈ Λ • swapAt c → Merge k c → Merge k (suc c)
    up c b SΛ m = begin
      Λ • (Xat (suc c) • Λ • Xat (suc c))
        ≈⟨ back _ (sym (cong (X-step c b) (back _ (X-step c b)))) ⟩
      Λ • ((swapAt c • Xat c • swapAt c) • Λ • (swapAt c • Xat c • swapAt c))
        ≈⟨ conj-merge (swap² c) SΛ m ⟩
      swapAt c • placeAt c u • swapAt c
        ≈⟨ sym (placeAt-step c u b) ⟩
      placeAt (suc c) u ∎

    up′ : ∀ c → c < ₄₊ k → (₁₊ (₄₊ k)) ⊢ swapAt c • Λ ≈ Λ • swapAt c → Merge′ k c → Merge′ k (suc c)
    up′ c b SΛ m = begin
      (Xat (suc c) • Λ • Xat (suc c)) • Λ
        ≈⟨ front _ (sym (cong (X-step c b) (back _ (X-step c b)))) ⟩
      ((swapAt c • Xat c • swapAt c) • Λ • (swapAt c • Xat c • swapAt c)) • Λ
        ≈⟨ conj-merge′ (swap² c) SΛ m ⟩
      swapAt c • placeAt c u • swapAt c
        ≈⟨ sym (placeAt-step c u b) ⟩
      placeAt (suc c) u ∎

    -- On wire 2: (301) and (302).
    merge₂ : Merge k 2
    merge₂ = trans (eq301 (₁₊ k) complete) (≡⇒≈ (Eq.sym (placeAt-place 2 u)))

    merge₂′ : Merge′ k 2
    merge₂′ = trans (eq302 (₁₊ k) complete) (≡⇒≈ (Eq.sym (placeAt-place 2 u)))

    b₁ : 1 < ₄₊ k
    b₁ = s≤s (s≤s z≤n)

  -- (309) on every control wire 1 … 4 + k.
  merge-at : ∀ c → c < ₄₊ k → Merge k (suc c)
  merge-at zero          b = down 1 b₁ (symAt 0) merge₂
  merge-at (suc zero)    b = merge₂
  merge-at (suc (suc c)) b = up (suc (suc c)) b (symAt (suc c))
                                (merge-at (suc c) (<-trans (n<1+n (suc c)) b))

  merge-at′ : ∀ c → c < ₄₊ k → Merge′ k (suc c)
  merge-at′ zero          b = down′ 1 b₁ (symAt 0) merge₂′
  merge-at′ (suc zero)    b = merge₂′
  merge-at′ (suc (suc c)) b = up′ (suc (suc c)) b (symAt (suc c))
                                 (merge-at′ (suc c) (<-trans (n<1+n (suc c)) b))
