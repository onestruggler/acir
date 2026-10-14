------------------------------------------------------------------------
-- Presentations of groups
--
-- The encoding preserves the semantics of the scalar, S and CS
--
-- The letters of E(S on wire p) are the phases i_[x] on the basis
-- vectors x with bit p set, each vector once; as diagonal operators
-- their product is the phase i where bit p is set, which is S on wire
-- p up to the scale γ.  For CS the vectors have bits p and p + 1 set,
-- and for the scalar every vector carries a letter.
--
-- After Real-Clifford+CH.EncodingSemantics.Diagonal.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.EncodingSemantics.Diagonal (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List)
open import Data.Nat using (suc ; _<_ ; _≤_ ; s≤s)
open import Data.Nat.Properties using (≤-pred ; ≤-refl ; n≤1+n ; ≤-trans)
open import Data.Product using (proj₁ ; proj₂ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word)

import Data.Fin.Properties as FinP

open import Notations using (₂₊ ; ₃₊)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Encoding m
open import Examples.Groups.Clifford+CS.BridgeGray n
  using (⟦_⟧Y ; coefℤ ; δᶠ ; δᶠ-refl ; δᶠ-≢ ; ci-a ; ci-≢)
open import Examples.Groups.Clifford+CS.EncodingSemantics.Diag
open import Examples.Groups.Clifford+CS.EncodingSemantics.Products n
open import Examples.Groups.Clifford+CS.EncodingSemantics.WireForms m using (sph ; csph)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL

private
  true≢false : true ≢ false
  true≢false ()

------------------------------------------------------------------------
-- The phase letters

-- The phase i at the basis vector s.
phs : Bits n → Bits n → 𝔽
phs s x = if eqB x s then ⅈ else 1#

private
  phs-hit : ∀ s x → x ≡ s → phs s x ≡ ⅈ
  phs-hit s x e = Eq.cong (λ b → if b then ⅈ else 1#) (eqB-complete x s e)

  phs-miss : ∀ s x → x ≢ s → phs s x ≡ 1#
  phs-miss s x ne = Eq.cong (λ b → if b then ⅈ else 1#) (eqB-false x s ne)

  -- δ at two indices is δ at their vectors.
  δᶠ-idx : ∀ (x y : Bits n) → δᶠ (idx x) (idx y) ≡ δb x y
  δᶠ-idx x y = go (idx x FinP.≟ idx y)
    where
    go : Dec (idx x ≡ idx y) → δᶠ (idx x) (idx y) ≡ δb x y
    go (yes e) = Eq.subst (λ y → δᶠ (idx x) (idx y) ≡ δb x y) (idx-inj e)
                   (Eq.trans (δᶠ-refl (idx x)) (Eq.sym (δb-refl x)))
    go (no ne) = Eq.trans (δᶠ-≢ ne) (Eq.sym (δb-≢ x y (λ e → ne (Eq.cong idx e))))

  -- The letter i_[s], read on bit vectors.
  i-M : ∀ (s : Bits n) → proj₂ ⟦ TL.i (idx s) ⟧Y ≐ diag (phs s)
  i-M s x y = go (idx x FinP.≟ idx s)
    where
    go : Dec (idx x ≡ idx s) → coefℤ (TL.i-gen (idx s)) (idx x) (idx y) ≡ phs s x * δb x y
    go (yes e) = begin
      coefℤ (TL.i-gen (idx s)) (idx x) (idx y)
        ≡⟨ Eq.cong (λ a → coefℤ (TL.i-gen a) (idx x) (idx y)) (Eq.sym e) ⟩
      coefℤ (TL.i-gen (idx x)) (idx x) (idx y)
        ≡⟨ ci-a (idx x) (idx y) ⟩
      δᶠ (idx x) (idx y) * ⅈ
        ≡⟨ Eq.cong (_* ⅈ) (δᶠ-idx x y) ⟩
      δb x y * ⅈ
        ≡⟨ *-comm (δb x y) ⅈ ⟩
      ⅈ * δb x y
        ≡⟨ Eq.cong (_* δb x y) (Eq.sym (phs-hit s x (idx-inj e))) ⟩
      phs s x * δb x y ∎
      where open Eq.≡-Reasoning
    go (no ne) = begin
      coefℤ (TL.i-gen (idx s)) (idx x) (idx y)
        ≡⟨ ci-≢ (idx s) ne (idx y) ⟩
      δᶠ (idx x) (idx y)
        ≡⟨ δᶠ-idx x y ⟩
      δb x y
        ≡⟨ Eq.sym (*-identityˡ (δb x y)) ⟩
      1# * δb x y
        ≡⟨ Eq.cong (_* δb x y) (Eq.sym (phs-miss s x (λ e → ne (Eq.cong idx e)))) ⟩
      phs s x * δb x y ∎
      where open Eq.≡-Reasoning

  -- The diagonal reading of a product of phase letters over contexts.
  diag-letters : ∀ {j} (cs : List (Bits j)) (s : Bits j → Bits n) →
                 proj₂ ⟦ ∏ cs (λ c → TL.i (idx (s c))) ⟧Y ≐ diag (∏ᶠ cs (λ c x → phs (s c) x))
  diag-letters cs s =
    ≐-trans (∏-M cs (λ c → TL.i (idx (s c))))
      (≐-trans (fold-cong cs (λ c → i-M (s c))) (diag-fold cs (λ c x → phs (s c) x)))

  ℓ-letters : ∀ {j} (cs : List (Bits j)) (s : Bits j → Bits n) →
              proj₁ ⟦ ∏ cs (λ c → TL.i (idx (s c))) ⟧Y ≡ 0
  ℓ-letters cs s =
    Eq.trans (∏-ℓ cs (λ c → TL.i (idx (s c)))) (sum-zero cs (λ c → TL.i (idx (s c))) (λ c → Eq.refl))

  -- From a diagonal reading to the semantic equivalence with a gate
  -- (1 , γ · diag f).
  γ^1 : γ^ 1 ≡ γ
  γ^1 = Eq.trans (γ^-def 1) (*-identityʳ γ)

  diag-sem : (u : Word (TL.Gen N)) (f : Bits n → 𝔽) → proj₁ ⟦ u ⟧Y ≡ 0 → proj₂ ⟦ u ⟧Y ≐ diag f →
             ⟦ u ⟧Y ~ (1 , γ · diag f)
  diag-sem u f ℓ M =
    ≐-trans (·-cong γ^1 M)
      (≐-sym (≐-trans (·-cong (Eq.cong γ^_ ℓ) (≐-refl (γ · diag f))) (·-1 (γ · diag f))))

------------------------------------------------------------------------
-- The scalar

private
  ∏gI : ∀ x → ∏ᶠ (allBits n) (λ c x → phs c x) x ≡ ⅈ
  ∏gI x =
    Eq.trans (∏ᶠ-unique (allBits n) (λ c x → phs c x) x x (allBits-nodup n) (∈-allBits x)
               (λ c ne → phs-miss c x (λ e → true≢false (Eq.trans (Eq.sym (eqB-complete c x (Eq.sym e))) ne))))
             (phs-hit x x Eq.refl)

E-I-sem : ⟦ E-I ⟧Y ~ (1 , scal γⅈ)
E-I-sem =
  ~-trans {s = ⟦ E-I ⟧Y} {1 , γ · diag (λ _ → ⅈ)} {1 , scal γⅈ}
    (diag-sem E-I (λ _ → ⅈ) (ℓ-letters (allBits n) (λ x → x))
      (≐-trans (diag-letters (allBits n) (λ x → x)) (diag-cong ∏gI)))
    (~-reflexive {l = 1} {1} {γ · diag (λ _ → ⅈ)} {scal γⅈ} Eq.refl (λ x y → Eq.sym (*-assoc γ ⅈ (δb x y))))

------------------------------------------------------------------------
-- S on wire p

private
  gS : ℕ → Bits (₃₊ m) → Bits n → 𝔽
  gS p c x = phs (str₁ p c true) x

  -- The product of the phases at a basis vector: i when bit p is set.
  ∏gS : ∀ p x → p < n → ∏ᶠ (allBits (₃₊ m)) (gS p) x ≡ sph p x
  ∏gS p x (s≤s q) with lookupℕ p x in bit
  ... | false = ∏ᶠ-one (allBits (₃₊ m)) (gS p) x (λ c _ → phs-miss _ x (miss c))
    where
    -- No letter is at x: the letters have bit p set.
    miss : ∀ c → x ≢ str₁ p c true
    miss c e = true≢false (Eq.trans (Eq.sym (lookup-insert p true c q))
                                    (Eq.trans (Eq.cong (lookupℕ p) (Eq.sym e)) bit))
  ... | true  =
    Eq.trans (∏ᶠ-unique (allBits (₃₊ m)) (gS p) x (removeℕ p x) (allBits-nodup (₃₊ m))
               (∈-allBits (removeℕ p x)) others)
             (phs-hit _ x x≡)
    where
    -- x is the vector of its own context.
    x≡ : x ≡ str₁ p (removeℕ p x) true
    x≡ = Eq.sym (Eq.trans (Eq.cong (λ b → insertℕ p b (removeℕ p x)) (Eq.sym bit))
                          (insert-lookup-remove p x q))
    -- Only the context of x carries a letter at x.
    others : ∀ c → eqB c (removeℕ p x) ≡ false → gS p c x ≡ 1#
    others c ne = phs-miss _ x (λ e → true≢false (Eq.trans (Eq.sym (eqB-refl c))
      (Eq.trans (Eq.cong (eqB c) (Eq.sym (remove-insert p true c q)))
        (Eq.trans (Eq.cong (λ v → eqB c (removeℕ p v)) (Eq.sym e)) ne))))

E-S-sem : ∀ p → p < n → ⟦ E-S p ⟧Y ~ (1 , γ · diag (sph p))
E-S-sem p q =
  diag-sem (E-S p) (sph p)
    (ℓ-letters (allBits (₃₊ m)) (λ c → str₁ p c true))
    (≐-trans (diag-letters (allBits (₃₊ m)) (λ c → str₁ p c true))
             (diag-cong (λ x → ∏gS p x q)))

------------------------------------------------------------------------
-- CS on wires p and p + 1

private
  gCS : ℕ → Bits (₂₊ m) → Bits n → 𝔽
  gCS p c x = phs (str₂ p c true true) x

  ∏gCS : ∀ p x → suc p < n → ∏ᶠ (allBits (₂₊ m)) (gCS p) x ≡ csph p x
  ∏gCS p x (s≤s q) with lookupℕ p x in bit | lookupℕ (suc p) x in ctl
  ... | false | _ = ∏ᶠ-one (allBits (₂₊ m)) (gCS p) x (λ c _ → phs-miss _ x (miss c))
    where
    -- The letters have bit p set.
    miss : ∀ c → x ≢ str₂ p c true true
    miss c e = true≢false (Eq.trans (Eq.sym (Eq.trans
                 (lookup-insert-below (suc p) p true (insertℕ p true c) ≤-refl q)
                 (lookup-insert p true c (≤-pred q))))
               (Eq.trans (Eq.cong (lookupℕ p) (Eq.sym e)) bit))
  ... | true | false = ∏ᶠ-one (allBits (₂₊ m)) (gCS p) x (λ c _ → phs-miss _ x (miss c))
    where
    -- The letters have bit p + 1 set.
    miss : ∀ c → x ≢ str₂ p c true true
    miss c e = true≢false (Eq.trans (Eq.sym (lookup-insert (suc p) true (insertℕ p true c) q))
                                    (Eq.trans (Eq.cong (lookupℕ (suc p)) (Eq.sym e)) ctl))
  ... | true | true =
    Eq.trans (∏ᶠ-unique (allBits (₂₊ m)) (gCS p) x c₀ (allBits-nodup (₂₊ m)) (∈-allBits c₀) others)
             (phs-hit _ x x≡)
    where
    c₀ : Bits (₂₊ m)
    c₀ = removeℕ p (removeℕ (suc p) x)

    -- x is the vector of its own context.
    x≡ : x ≡ str₂ p c₀ true true
    x≡ = Eq.sym (begin
      insertℕ (suc p) true (insertℕ p true c₀)
        ≡⟨ Eq.cong₂ (λ u t → insertℕ (suc p) u (insertℕ p t c₀)) (Eq.sym ctl)
             (Eq.sym (Eq.trans (lookup-remove-below (suc p) p x ≤-refl q) bit)) ⟩
      insertℕ (suc p) (lookupℕ (suc p) x) (insertℕ p (lookupℕ p (removeℕ (suc p) x)) c₀)
        ≡⟨ Eq.cong (insertℕ (suc p) (lookupℕ (suc p) x)) (insert-lookup-remove p (removeℕ (suc p) x) (≤-pred q)) ⟩
      insertℕ (suc p) (lookupℕ (suc p) x) (removeℕ (suc p) x)
        ≡⟨ insert-lookup-remove (suc p) x q ⟩
      x ∎)
      where open Eq.≡-Reasoning

    -- Only the context of x carries a letter at x.
    others : ∀ c → eqB c c₀ ≡ false → gCS p c x ≡ 1#
    others c ne = phs-miss _ x (λ e → true≢false (Eq.trans (Eq.sym (eqB-refl c))
      (Eq.trans (Eq.cong (eqB c) (Eq.sym (Eq.trans
                   (Eq.cong (removeℕ p) (remove-insert (suc p) true (insertℕ p true c) q))
                   (remove-insert p true c (≤-pred q)))))
        (Eq.trans (Eq.cong (λ v → eqB c (removeℕ p (removeℕ (suc p) v))) (Eq.sym e)) ne))))

E-CS-sem : ∀ p → suc p < n → ⟦ E-CS p ⟧Y ~ (1 , γ · diag (csph p))
E-CS-sem p q =
  diag-sem (E-CS p) (csph p)
    (ℓ-letters (allBits (₂₊ m)) (λ c → str₂ p c true true))
    (≐-trans (diag-letters (allBits (₂₊ m)) (λ c → str₂ p c true true))
             (diag-cong (λ x → ∏gCS p x q)))
