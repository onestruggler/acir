------------------------------------------------------------------------
-- Presentations of groups
--
-- K_[a,b,c,d] on a column whose rows come out even.
--
-- Write the four entries as εᵢ + 2uᵢ with εᵢ ∈ {0, 1}.  A row of 2K at
-- them is the row at the ε's plus twice the row at the u's; when the
-- rows at the ε's are even, 2cᵢ say, the column after K is the column
-- after 2K halved, with entries cᵢ + rowᵢ(u) at a, b, c, d and the old
-- entries elsewhere (the exponent does not rise).  Its parities are
-- those of the cᵢ, each shifted by the parity Σ of u₁ + u₂ + u₃ + u₄.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.KHalf where

open import Data.Bool.Base using (Bool ; _xor_)
open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_)
import Data.Integer.Solver as ℤSolver
open import Data.Nat.Base using (ℕ ; suc)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (oddℤ ; oddℤ-+)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (scV)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim)
open import Examples.Groups.CCX+HH-TwoLevel.ColumnAction
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
open import Examples.Groups.CCX+HH-TwoLevel.Step using (scV-2map)

private
  variable
    n : ℕ
  module ℤS = ℤSolver.+-*-Solver
  open ℤS using (_:+_ ; _:*_ ; _:=_ ; con)

------------------------------------------------------------------------
-- Rows are linear

lin-split : ∀ s₁ s₂ s₃ s₄ e₁ e₂ e₃ e₄ u₁ u₂ u₃ u₄ →
            linℤ s₁ s₂ s₃ s₄ (e₁ ℤ.+ + 2 ℤ.* u₁) (e₂ ℤ.+ + 2 ℤ.* u₂) (e₃ ℤ.+ + 2 ℤ.* u₃) (e₄ ℤ.+ + 2 ℤ.* u₄)
            ≡ linℤ s₁ s₂ s₃ s₄ e₁ e₂ e₃ e₄ ℤ.+ + 2 ℤ.* linℤ s₁ s₂ s₃ s₄ u₁ u₂ u₃ u₄
lin-split = ℤS.solve 12 (λ s₁ s₂ s₃ s₄ e₁ e₂ e₃ e₄ u₁ u₂ u₃ u₄ →
  s₁ :* (e₁ :+ con (+ 2) :* u₁) :+ s₂ :* (e₂ :+ con (+ 2) :* u₂) :+ s₃ :* (e₃ :+ con (+ 2) :* u₃)
    :+ s₄ :* (e₄ :+ con (+ 2) :* u₄)
  := (s₁ :* e₁ :+ s₂ :* e₂ :+ s₃ :* e₃ :+ s₄ :* e₄)
       :+ con (+ 2) :* (s₁ :* u₁ :+ s₂ :* u₂ :+ s₃ :* u₃ :+ s₄ :* u₄)) refl

-- 2c + 2r = 2 (c + r).
private
  two-+ : ∀ c r → + 2 ℤ.* c ℤ.+ + 2 ℤ.* r ≡ + 2 ℤ.* (c ℤ.+ r)
  two-+ = ℤS.solve 2 (λ c r → con (+ 2) :* c :+ con (+ 2) :* r := con (+ 2) :* (c :+ r)) refl

------------------------------------------------------------------------
-- The halved column

module Half {n : ℕ} (W : Vec ℤ n) {a b c d : Fin n} .(ab : a < b) .(bc : b < c) .(cd : c < d)
  (e₁ e₂ e₃ e₄ u₁ u₂ u₃ u₄ : ℤ)
  (wa : W ! a ≡ e₁ ℤ.+ + 2 ℤ.* u₁) (wb : W ! b ≡ e₂ ℤ.+ + 2 ℤ.* u₂)
  (wc : W ! c ≡ e₃ ℤ.+ + 2 ℤ.* u₃) (wd : W ! d ≡ e₄ ℤ.+ + 2 ℤ.* u₄)
  (cA cB cC cD : ℤ)
  (hA : rowAᶻ e₁ e₂ e₃ e₄ ≡ + 2 ℤ.* cA) (hB : rowBᶻ e₁ e₂ e₃ e₄ ≡ + 2 ℤ.* cB)
  (hC : rowCᶻ e₁ e₂ e₃ e₄ ≡ + 2 ℤ.* cC) (hD : rowDᶻ e₁ e₂ e₃ e₄ ≡ + 2 ℤ.* cD) where

  private
    D₄ = distinct₄ ab bc cd
    open Distinct₄ D₄

  -- The new entries.
  vA vB vC vD : ℤ
  vA = cA ℤ.+ rowAᶻ u₁ u₂ u₃ u₄
  vB = cB ℤ.+ rowBᶻ u₁ u₂ u₃ u₄
  vC = cC ℤ.+ rowCᶻ u₁ u₂ u₃ u₄
  vD = cD ℤ.+ rowDᶻ u₁ u₂ u₃ u₄

  Wh : Vec ℤ n
  Wh = set₄ a b c d vA vB vC vD W

  Wh-a : Wh ! a ≡ vA
  Wh-a = set₄-a D₄ vA vB vC vD W
  Wh-b : Wh ! b ≡ vB
  Wh-b = set₄-b D₄ vA vB vC vD W
  Wh-c : Wh ! c ≡ vC
  Wh-c = set₄-c D₄ vA vB vC vD W
  Wh-d : Wh ! d ≡ vD
  Wh-d = set₄-d D₄ vA vB vC vD W
  Wh-≢ : ∀ {x} → x ≢ a → x ≢ b → x ≢ c → x ≢ d → Wh ! x ≡ W ! x
  Wh-≢ xa xb xc xd = set₄-≢ D₄ vA vB vC vD W xa xb xc xd

  private
    ents : ∀ (r : ℤ → ℤ → ℤ → ℤ → ℤ) → r (W ! a) (W ! b) (W ! c) (W ! d)
           ≡ r (e₁ ℤ.+ + 2 ℤ.* u₁) (e₂ ℤ.+ + 2 ℤ.* u₂) (e₃ ℤ.+ + 2 ℤ.* u₃) (e₄ ℤ.+ + 2 ℤ.* u₄)
    ents r = trans (cong (λ z → r z (W ! b) (W ! c) (W ! d)) wa)
               (trans (cong (λ z → r _ z (W ! c) (W ! d)) wb)
                 (trans (cong (λ z → r _ _ z (W ! d)) wc) (cong (λ z → r _ _ _ z) wd)))

    row : ∀ s₁ s₂ s₃ s₄ (cX : ℤ) → linℤ s₁ s₂ s₃ s₄ e₁ e₂ e₃ e₄ ≡ + 2 ℤ.* cX →
          linℤ s₁ s₂ s₃ s₄ (W ! a) (W ! b) (W ! c) (W ! d) ≡ + 2 ℤ.* (cX ℤ.+ linℤ s₁ s₂ s₃ s₄ u₁ u₂ u₃ u₄)
    row s₁ s₂ s₃ s₄ cX h =
      trans (ents (linℤ s₁ s₂ s₃ s₄))
        (trans (lin-split s₁ s₂ s₃ s₄ e₁ e₂ e₃ e₄ u₁ u₂ u₃ u₄)
          (trans (cong (ℤ._+ + 2 ℤ.* linℤ s₁ s₂ s₃ s₄ u₁ u₂ u₃ u₄) h) (two-+ cX _)))

  -- 2K on W is twice Wh.
  K-half : Kᶻ a b c d W ≡ Vec.map (+ 2 ℤ.*_) Wh
  K-half = vec-ext λ x → dec-elim (x FinP.≟ a)
    (λ { refl → trans (set₄-a D₄ _ _ _ _ dW) (trans (row p1ᶻ p1ᶻ p1ᶻ p1ᶻ cA hA) (sym (two x Wh-a))) })
    (λ xa → dec-elim (x FinP.≟ b)
      (λ { refl → trans (set₄-b D₄ _ _ _ _ dW) (trans (row p1ᶻ m1ᶻ p1ᶻ m1ᶻ cB hB) (sym (two x Wh-b))) })
      (λ xb → dec-elim (x FinP.≟ c)
        (λ { refl → trans (set₄-c D₄ _ _ _ _ dW) (trans (row p1ᶻ p1ᶻ m1ᶻ m1ᶻ cC hC) (sym (two x Wh-c))) })
        (λ xc → dec-elim (x FinP.≟ d)
          (λ { refl → trans (set₄-d D₄ _ _ _ _ dW) (trans (row p1ᶻ m1ᶻ m1ᶻ p1ᶻ cD hD) (sym (two x Wh-d))) })
          (λ xd → trans (set₄-≢ D₄ _ _ _ _ dW xa xb xc xd)
                    (trans (VecP.lookup-map x (+ 2 ℤ.*_) W)
                      (trans (cong (+ 2 ℤ.*_) (sym (Wh-≢ xa xb xc xd))) (sym (VecP.lookup-map x (+ 2 ℤ.*_) Wh))))))))
    where
    dW = Vec.map (+ 2 ℤ.*_) W
    two : ∀ x {v} → Wh ! x ≡ v → Vec.map (+ 2 ℤ.*_) Wh ! x ≡ + 2 ℤ.* v
    two x e = trans (VecP.lookup-map x (+ 2 ℤ.*_) Wh) (cong (+ 2 ℤ.*_) e)

  -- The column after K, at the same exponent.
  K-col : ∀ k → scV (suc k) (Kᶻ a b c d W) ≡ scV k Wh
  K-col k = trans (cong (scV (suc k)) K-half) (scV-2map k Wh)

  -- The parity of u₁ + u₂ + u₃ + u₄.
  Σu : Bool
  Σu = ((oddℤ u₁ xor oddℤ u₂) xor oddℤ u₃) xor oddℤ u₄

  odd-vA : oddℤ vA ≡ oddℤ cA xor Σu
  odd-vA = trans (oddℤ-+ cA _) (cong (oddℤ cA xor_) (odd-rowA u₁ u₂ u₃ u₄))
  odd-vB : oddℤ vB ≡ oddℤ cB xor Σu
  odd-vB = trans (oddℤ-+ cB _) (cong (oddℤ cB xor_) (odd-rowB u₁ u₂ u₃ u₄))
  odd-vC : oddℤ vC ≡ oddℤ cC xor Σu
  odd-vC = trans (oddℤ-+ cC _) (cong (oddℤ cC xor_) (odd-rowC u₁ u₂ u₃ u₄))
  odd-vD : oddℤ vD ≡ oddℤ cD xor Σu
  odd-vD = trans (oddℤ-+ cD _) (cong (oddℤ cD xor_) (odd-rowD u₁ u₂ u₃ u₄))
