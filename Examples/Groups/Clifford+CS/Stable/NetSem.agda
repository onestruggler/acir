------------------------------------------------------------------------
-- Presentations of groups
--
-- A swap network denotes the permutation of its bit map
--
-- The decoding's affine circuits are placed letters, pl σ g, and a
-- placement conjugates by the swap network `net σ` (PermCalc).  Read on
-- bit vectors a network is a bit map `nb σ`, letter by letter: the
-- exchange of the bits at j and j + 1 for the generator σ ↑ʲ (`nbg`),
-- composed in the order of the word.  Its semantics is the permutation
-- operator of that map, at every width (`net-sem`): the exchange of the
-- two bottom wires is Lambda.Checks' two-wire evaluation with idle wires
-- added on top — `top` of the exchange is the exchange one wire wider,
-- and a permutation with an idle top wire is the permutation acting on
-- all but the last bit (`topS-perm`) — and with idle wires below
-- (`up-perm`), and products compose the maps (`perm-⊙`).  The first
-- step of the affine circuits' semantics at symbolic width.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.NetSem where

open import Algebra.Bundles using (Monoid)
open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_ ; _∷ʳ_ ; initLast)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁₊ ; ₂₊)

import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Semantics.Control using (blk ; sel ; permOp ; up-perm ; upS ; upS-~ ; swapL)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; Swap ; _↑)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.PermCalc using (net ; φ)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (⟦•⟧ ; ⟦↑⟧ ; ⟦top⟧ ; topS ; topS-~ ; ⟦ε⟧ ; ∙-cong′)
open import Examples.Groups.Clifford+CS.Lambda.Checks using (Swap-perm)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqᵇ)

private
  variable
    n : ℕ

  module R (n : ℕ) = SetoidR (Monoid.setoid (Scaled-monoid n))

------------------------------------------------------------------------
-- Bit maps

-- The exchange of the two bottom bits.
sw01 : Bits (₂₊ n) → Bits (₂₊ n)
sw01 (a ∷ b ∷ x) = b ∷ a ∷ x

nbg : S.Gen n → Bits n → Bits n
nbg (S.gate₀ ())
nbg (S.gate₁ ())
nbg (S.gate₂ S.σ-gate) = sw01
nbg (g S.↥) (a ∷ x)    = a ∷ nbg g x

-- The bit map of a network, the letters in their order.
nb : Word (S.Gen n) → Bits n → Bits n
nb [ g ]ʷ  = nbg g
nb ε       = λ x → x
nb (u • v) = λ x → nb v (nb u x)

------------------------------------------------------------------------
-- Permutation operators

-- Products compose the maps.
perm-⊙ : (π ρ : Bits n → Bits n) → (permOp π ⊙ permOp ρ) ≐ permOp (λ x → ρ (π x))
perm-⊙ π ρ x y = Σ-δˡ (π x) (λ z → δb (ρ z) y)

private
  blk-snoc : ∀ {n} (P M : Op n) (x y : Bits n) (a b : Bool) →
             blk P M (x ∷ʳ a) (y ∷ʳ b) ≡ sel a b (P x y) (M x y)
  blk-snoc {₀}    P M []      []      a b = Eq.refl
  blk-snoc {₁₊ n} P M (u ∷ x) (v ∷ y) a b =
    blk-snoc {n} (λ s t → P (u ∷ s) (v ∷ t)) (λ s t → M (u ∷ s) (v ∷ t)) x y a b

  if-same : ∀ (c : Bool) (z : 𝔽) → (if c then z else z) ≡ z
  if-same true  z = Eq.refl
  if-same false z = Eq.refl

  δb-snoc : ∀ {n} (x y : Bits n) (a b : Bool) → δb (x ∷ʳ a) (y ∷ʳ b) ≡ (if eqᵇ a b then δb x y else 0#)
  δb-snoc []          []          true  true  = Eq.refl
  δb-snoc []          []          false false = Eq.refl
  δb-snoc []          []          true  false = Eq.refl
  δb-snoc []          []          false true  = Eq.refl
  δb-snoc (true ∷ x)  (true ∷ y)  a b = δb-snoc x y a b
  δb-snoc (false ∷ x) (false ∷ y) a b = δb-snoc x y a b
  δb-snoc (true ∷ x)  (false ∷ y) a b = Eq.sym (if-same (eqᵇ a b) 0#)
  δb-snoc (false ∷ x) (true ∷ y)  a b = Eq.sym (if-same (eqᵇ a b) 0#)

  sel-same : ∀ (a b : Bool) (z : 𝔽) → sel a b z z ≡ (if eqᵇ a b then z else 0#)
  sel-same true  true  z = Eq.refl
  sel-same false false z = Eq.refl
  sel-same true  false z = Eq.refl
  sel-same false true  z = Eq.refl

-- With an idle top wire a permutation acts on all but the last bit.
topS-perm : (π : Bits n → Bits n) (σ : Bits (₁₊ n) → Bits (₁₊ n)) →
            (∀ x a → σ (x ∷ʳ a) ≡ π x ∷ʳ a) → blk (permOp π) (permOp π) ≐ permOp σ
topS-perm π σ e x y with initLast x | initLast y
... | x′ , a , Eq.refl | y′ , b , Eq.refl =
  Eq.trans (blk-snoc (permOp π) (permOp π) x′ y′ a b)
    (Eq.trans (sel-same a b (δb (π x′) y′))
      (Eq.sym (Eq.trans (Eq.cong (λ z → δb z (y′ ∷ʳ b)) (e x′ a)) (δb-snoc (π x′) y′ a b))))

------------------------------------------------------------------------
-- Networks

private
  sw-two : ∀ (x : Bits 2) → swapL {₀} x ≡ sw01 x
  sw-two (a ∷ b ∷ []) = Eq.refl

  sw-snoc : ∀ (x : Bits (₂₊ n)) (a : Bool) → sw01 (x ∷ʳ a) ≡ sw01 x ∷ʳ a
  sw-snoc (u ∷ v ∷ x) a = Eq.refl

-- The exchange of the two bottom wires, with any idle wires on top.
swap-sem : ∀ r → ⟦ Swap {r} ⟧ ~ (0 , permOp (sw01 {r}))
swap-sem zero =
  ~-trans {s = ⟦ Swap {0} ⟧} {0 , permOp swapL} {0 , permOp sw01} Swap-perm
    (~-reflexive {l = 0} {0} Eq.refl (λ x y → Eq.cong (λ z → δb z y) (sw-two x)))
swap-sem (suc r) = begin
  ⟦ top (Swap {r}) ⟧                 ≈⟨ ⟦top⟧ (Swap {r}) ⟩
  topS ⟦ Swap {r} ⟧                  ≈⟨ topS-~ {s = ⟦ Swap {r} ⟧} {0 , permOp sw01} (swap-sem r) ⟩
  (0 , blk (permOp sw01) (permOp sw01))   ≈⟨ ~-reflexive {l = 0} {0} Eq.refl (topS-perm sw01 sw01 sw-snoc) ⟩
  (0 , permOp (sw01 {suc r}))        ∎
  where open R (₂₊ (suc r))

-- A generator.
φ-sem : ∀ (g : S.Gen n) → ⟦ φ g ⟧ ~ (0 , permOp (nbg g))
φ-sem (S.gate₀ ())
φ-sem (S.gate₁ ())
φ-sem (S.gate₂ S.σ-gate) = swap-sem _
φ-sem {suc n} (g S.↥) = begin
  ⟦ φ g ↑ ⟧                          ≈⟨ ⟦↑⟧ (φ g) ⟩
  upS ⟦ φ g ⟧                        ≈⟨ upS-~ {s = ⟦ φ g ⟧} {0 , permOp (nbg g)} (φ-sem g) ⟩
  upS (0 , permOp (nbg g))           ≈⟨ ~-reflexive {l = 0} {0} Eq.refl (up-perm (nbg g) (nbg (g S.↥)) (λ a x → Eq.refl)) ⟩
  (0 , permOp (nbg (g S.↥)))         ∎
  where open R (suc n)

-- A network denotes the permutation of its bit map.
net-sem : ∀ (σ : Word (S.Gen n)) → ⟦ net σ ⟧ ~ (0 , permOp (nb σ))
net-sem [ g ]ʷ  = φ-sem g
net-sem {n} ε   = ~-trans {s = ⟦ net {n} ε ⟧} {ε∙} {0 , permOp (nb {n} ε)} ⟦ε⟧
                    (~-reflexive {l = 0} {0} Eq.refl (λ x y → Eq.refl))
net-sem {n} (u • v) = begin
  ⟦ net u • net v ⟧                          ≈⟨ ⟦•⟧ (net u) (net v) ⟩
  ⟦ net u ⟧ ∙ ⟦ net v ⟧                      ≈⟨ ∙-cong′ ⟦ net u ⟧ (0 , permOp (nb u)) ⟦ net v ⟧ (0 , permOp (nb v))
                                                  (net-sem u) (net-sem v) ⟩
  (0 , permOp (nb u)) ∙ (0 , permOp (nb v))  ≈⟨ ~-reflexive {l = 0} {0} Eq.refl (perm-⊙ (nb u) (nb v)) ⟩
  (0 , permOp (nb (u • v)))                  ∎
  where open R n
