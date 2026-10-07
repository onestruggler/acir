------------------------------------------------------------------------
-- Presentations of groups
--
-- CS past translations, and diagonals one wire up past CX
--
-- CS = (x₀ choose 2) x₁ moves past X on wire 0 into CZ, and past X on
-- wire 1 into S:
--
--     CS • X ≈ X • CZ • CS          (CS-X₀)
--     CS • X ↑ ≈ S • X ↑ • CS        (CS-X₁)
--
-- The first by pushing X through the definition: the two conjugates of
-- T by CX leave the conjugates of S, CZ leaves Z ↑, and these make CZ.
-- Conjugated by SWAP it moves SC past X ↑ (SC-X₁); with the gadget of
-- T, which X ↑ passes leaving P (PT-X₁), it gives the second.  A
-- diagonal one wire up passes CX, the rows of its atoms being fixed
-- (cx∥↑).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Trans
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 3 ≤ lv) (gt3 : 2 ≤ p-2) where

import Data.Integer.Base as ℤ
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Fin using (#_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using ( F ; p ; 0F ; 1F ; 2F ; _+_ ; _*_ ; -_ ; binom2 ; binom3 ; half ; module FR
        ; solve ; _:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con )
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (module Inv ; CX-order)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv using (CX-invˡ ; CX-invʳ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv using (↑ᶠ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (⌊^⌋)
open import Examples.Groups.Qupit-Phase-Affine.Affine p-2 p-prime lv using (CX-X ; CX-X↑ᶠ ; sX)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Gates p-2 p-prime lv h gt3
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Mono p-2 p-prime lv h gt3
  using (Gen₃ ; gen₃ ; term ; vec ; by-labels ; term-++ ; term-^ᶠ ; scaleᵗ ; fix)

private
  variable
    n : ℕ

  h₂ : 2 ≤ lv
  h₂ = quad₃ h

  h₁ : 1 ≤ lv
  h₁ = lin₃ h

------------------------------------------------------------------------
-- Residues of iterates

module _ {m : ℕ} where

  open Width m

  -- If g passes a leaving r, which g passes, then g ^ k leaves r ^ k.
  res^ : {g a r : Circuit m} → m ⊢ g • a ≈ a • g • r → m ⊢ r ∥ g → (k : ℕ) → m ⊢ g ^ k • a ≈ a • g ^ k • r ^ k
  res^ e rg zero = trans left-unit (sym (trans (back _ left-unit) right-unit))
  res^ e rg (suc zero) = e
  res^ {g} {a} {r} e rg (suc (suc k)) = begin
    (g • g ^ suc k) • a                 ≈⟨ trans assoc (back _ (res^ e rg (suc k))) ⟩
    g • a • g ^ suc k • r ^ suc k       ≈⟨ trans (sym assoc) (trans (front _ e) (by-passoc ((□ • □ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl)) ⟩
    a • g • (r • g ^ suc k) • r ^ suc k ≈⟨ back _ (back _ (front _ (sym (∥-^ (suc k) (∥-sym rg))))) ⟩
    a • g • (g ^ suc k • r) • r ^ suc k ≈⟨ back _ (by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl) ⟩
    a • (g • g ^ suc k) • r • r ^ suc k ∎

------------------------------------------------------------------------
-- The conjugates of T and S by CX past X

module _ {n : ℕ} where

  open Width (₂₊ n)

  -- T^k on x₀ ± x₁, and S^k.
  ta tb sa sb : F → Circuit (₂₊ n)
  ta k = CX • T h ^ᶠ k • CX ^ᶠ (- 1F)
  tb k = CX ^ᶠ (- 1F) • T h ^ᶠ k • CX
  sa k = CX • S h₂ ^ᶠ k • CX ^ᶠ (- 1F)
  sb k = CX ^ᶠ (- 1F) • S h₂ ^ᶠ k • CX

  private
    Ci : Circuit (₂₊ n)
    Ci = CX ^ᶠ (- 1F)

    Ci-X : (₂₊ n) ⊢ Ci • X ≈ X • Ci
    Ci-X = Pow.pow-comm (₂₊ n) (toℕ (- 1F)) CX-X

  ta-X : (k : F) → (₂₊ n) ⊢ ta k • X ≈ X • ta k • sa k
  ta-X k = begin
    (CX • T h ^ᶠ k • Ci) • X                     ≈⟨ trans assoc (back _ (trans assoc (back _ Ci-X))) ⟩
    CX • T h ^ᶠ k • X • Ci                       ≈⟨ back _ (trans (sym assoc) (front _ (Tᶠ-X k))) ⟩
    CX • (X • T h ^ᶠ k • S h₂ ^ᶠ k) • Ci         ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
    (CX • X) • T h ^ᶠ k • S h₂ ^ᶠ k • Ci         ≈⟨ trans (front _ CX-X) assoc ⟩
    X • CX • T h ^ᶠ k • S h₂ ^ᶠ k • Ci           ≈⟨ back _ (back _ (back _ (trans (sym left-unit) (front _ (sym (CX-invˡ 1F)))))) ⟩
    X • CX • T h ^ᶠ k • (Ci • CX) • S h₂ ^ᶠ k • Ci
      ≈⟨ back _ (by-passoc (□ • □ • (□ • □) • □ • □) ((□ • □ • □) • □ • □ • □) Eq.refl) ⟩
    X • ta k • sa k ∎

  tb-X : (k : F) → (₂₊ n) ⊢ tb k • X ≈ X • tb k • sb k
  tb-X k = begin
    (Ci • T h ^ᶠ k • CX) • X                     ≈⟨ trans assoc (back _ (trans assoc (back _ CX-X))) ⟩
    Ci • T h ^ᶠ k • X • CX                       ≈⟨ back _ (trans (sym assoc) (front _ (Tᶠ-X k))) ⟩
    Ci • (X • T h ^ᶠ k • S h₂ ^ᶠ k) • CX         ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
    (Ci • X) • T h ^ᶠ k • S h₂ ^ᶠ k • CX         ≈⟨ trans (front _ Ci-X) assoc ⟩
    X • Ci • T h ^ᶠ k • S h₂ ^ᶠ k • CX           ≈⟨ back _ (back _ (back _ (trans (sym left-unit) (front _ (sym (CX-invʳ 1F)))))) ⟩
    X • Ci • T h ^ᶠ k • (CX • Ci) • S h₂ ^ᶠ k • CX
      ≈⟨ back _ (by-passoc (□ • □ • (□ • □) • □ • □) ((□ • □ • □) • □ • □ • □) Eq.refl) ⟩
    X • tb k • sb k ∎

  -- They are diagonal.
  Diag₃-ta : (k : F) → Diag₃ (₂₊ n) (ta k)
  Diag₃-ta k = Diag₃-≈ (back _ (back _ (refl' (Eq.sym (⌊^⌋ [ cx ]ʷ (toℕ (- 1F)))))))
                 (Diag₃-conj (Diag₃-^ᶠ Diag₃-T k) ([ cx ]ʷ ^ toℕ (- 1F))
                   (trans (back _ (refl' (⌊^⌋ [ cx ]ʷ (toℕ (- 1F))))) (CX-invʳ 1F)))

  Diag₃-tb : (k : F) → Diag₃ (₂₊ n) (tb k)
  Diag₃-tb k = Diag₃-conj (Diag₃-^ᶠ Diag₃-T k) [ cx ]ʷ (CX-invˡ 1F)

  Diag₃-sa : (k : F) → Diag₃ (₂₊ n) (sa k)
  Diag₃-sa k = Diag₃-≈ (back _ (back _ (refl' (Eq.sym (⌊^⌋ [ cx ]ʷ (toℕ (- 1F)))))))
                 (Diag₃-conj (Diag₃-2 (Diag-^ᶠ Diag-S k)) ([ cx ]ʷ ^ toℕ (- 1F))
                   (trans (back _ (refl' (⌊^⌋ [ cx ]ʷ (toℕ (- 1F))))) (CX-invʳ 1F)))

  Diag₃-sb : (k : F) → Diag₃ (₂₊ n) (sb k)
  Diag₃-sb k = Diag₃-conj (Diag₃-2 (Diag-^ᶠ Diag-S k)) [ cx ]ʷ (CX-invˡ 1F)

------------------------------------------------------------------------
-- CS past X on wire 0

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    Q : Circuit (₂₊ n)
    Q = (S h₂ ^ᶠ (- 1F)) ↑ • (T h ^ᶠ (- 1F)) ↑ • (Z h₁ ^ᶠ (- half)) ↑ • CZ h₂ ^ᶠ half

    W₁ : Circuit (₁₊ n)
    W₁ = S h₂ ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • Z h₁ ^ᶠ (- half)

    -- CZ^k past X leaves Z ↑ ^ k.
    CZᶠ-X : (k : F) → (₂₊ n) ⊢ CZ h₂ ^ᶠ k • X ≈ X • CZ h₂ ^ᶠ k • (Z h₁ ↑) ^ᶠ k
    CZᶠ-X k = res^ CZ-X Z↑∥CZ (toℕ k)

    Q-X : (₂₊ n) ⊢ Q • X ≈ X • Q • (Z h₁ ↑) ^ᶠ half
    Q-X = begin
      Q • X                                       ≈⟨ trans (front _ (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl)) assoc ⟩
      W₁ ↑ • CZ h₂ ^ᶠ half • X                    ≈⟨ back _ (CZᶠ-X half) ⟩
      W₁ ↑ • X • CZ h₂ ^ᶠ half • (Z h₁ ↑) ^ᶠ half  ≈⟨ trans (sym assoc) (trans (front _ (comm-gate₁-w↑ X-gate W₁)) assoc) ⟩
      X • W₁ ↑ • CZ h₂ ^ᶠ half • (Z h₁ ↑) ^ᶠ half  ≈⟨ back _ (by-passoc ((□ • □ • □) • □ • □) ((□ • □ • □ • □) • □) Eq.refl) ⟩
      X • Q • (Z h₁ ↑) ^ᶠ half ∎

    CS-split : (₂₊ n) ⊢ CS h ≈ ta (- half) • tb half • Q
    CS-split = by-passoc (□ • □ • □ • □ • □ • □ • □) ((□ • □ • □) • (□ • □ • □) • □) Eq.refl

    Diag₃-Q : Diag₃ (₂₊ n) Q
    Diag₃-Q = Diag₃-Q₁

    -- The conjugates of S by CX on two wires.
    Gs : Vec (Gen₃ (₂₊ n)) 4
    Gs = gen₃ (S h₂) (Diag₃-2 Diag-S) ∷ gen₃ (S h₂ ↑) (Diag₃-↑ (Diag₃-2 Diag-S))
       ∷ gen₃ (Z h₁ ↑) (Diag₃-↑ (Diag₃-2 Diag-Z)) ∷ gen₃ (CZ h₂) (Diag₃-2 Diag-CZ) ∷ []

    L′ L₊ L₁ L₂ : List (Fin 4 × F)
    L′ = (# 0 , 1F) ∷ (# 1 , - 1F * - 1F) ∷ (# 2 , binom2 (- 1F)) ∷ (# 3 , - 1F) ∷ []
    L₊ = (# 0 , 1F) ∷ (# 1 , 1F) ∷ (# 2 , 0F) ∷ (# 3 , 1F) ∷ []
    L₁ = scaleᵗ (- half) L′ ++ scaleᵗ half L₊ ++ ((# 2 , half) ∷ [])
    L₂ = (# 3 , 1F) ∷ []

    module OCX = Pow.Order (₂₊ n) {CX} CX-order
    module OCZ = Pow.Order (₂₊ n) {CZ h₂} CZ-order

    -- S on x₀ - x₁ and on x₀ + x₁.
    Pm : Circuit (₂₊ n)
    Pm = CX • S h₂ • CX ^ᶠ (- 1F)

    Pm≈ : (₂₊ n) ⊢ Pm ≈ term Gs L′
    Pm≈ = begin
      CX • S h₂ • CX ^ᶠ (- 1F)
        ≈⟨ front _ (OCX.^ᶠ-≡ (Eq.sym (solve 0 (:- (:- con (ℤ.+ 1)) := con (ℤ.+ 1)) Eq.refl))) ⟩
      CX ^ᶠ (- (- 1F)) • S h₂ • CX ^ᶠ (- 1F)
        ≈⟨ S-conj (- 1F) ⟩
      S h₂ • SZ (- 1F * - 1F) (binom2 (- 1F)) ↑ • CZ h₂ ^ᶠ (- 1F)
        ≈⟨ back _ (trans assoc (cong (refl' (↑ᶠ (S h₂) _)) (cong (refl' (↑ᶠ (Z h₁) _)) (sym right-unit)))) ⟩
      term Gs L′ ∎

    P≈ : (₂₊ n) ⊢ P • ε ≈ term Gs L₊
    P≈ = trans right-unit (trans P-SZ (back _ (trans assoc (cong (refl' (↑ᶠ (S h₂) _)) (cong (refl' (↑ᶠ (Z h₁) _)) (sym right-unit))))))

    sa≈ : (₂₊ n) ⊢ sa (- half) ≈ term Gs (scaleᵗ (- half) L′)
    sa≈ = trans (sym (conj-pow (CX-invʳ 1F) (CX-invˡ 1F) (toℕ (- half))))
                (trans (Pow.pow-cong (₂₊ n) (toℕ (- half)) Pm≈) (term-^ᶠ Gs L′ (- half)))

    sb≈ : (₂₊ n) ⊢ sb half ≈ term Gs (scaleᵗ half L₊)
    sb≈ = trans (sym (P^ (toℕ half)))
                (trans (Pow.pow-cong (₂₊ n) (toℕ half) (trans (sym right-unit) P≈)) (term-^ᶠ Gs L₊ half))

    labels₁ : vec L₁ ≡ vec L₂
    labels₁ = Eq.cong₂ _∷_ (solve 3 (λ h B2 B3 → (((con (ℤ.+ 1)) :* (:- h)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (((con (ℤ.+ 1)) :* h) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0))))))))))) := ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
      (Eq.cong₂ _∷_ (solve 3 (λ h B2 B3 → ((con (ℤ.+ 0)) :+ ((((:- (con (ℤ.+ 1))) :* (:- (con (ℤ.+ 1)))) :* (:- h)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (((con (ℤ.+ 1)) :* h) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0))))))))))) := ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
      (Eq.cong₂ _∷_ (Eq.trans (solve 3 (λ h B2 B3 → ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((B2 :* (:- h)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (((con (ℤ.+ 0)) :* h) :+ ((con (ℤ.+ 0)) :+ (h :+ (con (ℤ.+ 0))))))))))) := ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0))) :+ ((con (ℤ.+ 0)) :* ((h :+ h) :- con (ℤ.+ 1)) :+ (((:- (con (ℤ.+ 1))) :* h) :* (B2 :- con (ℤ.+ 1)) :+ (con (ℤ.+ 0)) :* (B3 :+ con (ℤ.+ 1))))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
            (fix _ _ _ _))
      (Eq.cong₂ _∷_ (Eq.trans (solve 3 (λ h B2 B3 → ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (((:- (con (ℤ.+ 1))) :* (:- h)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (((con (ℤ.+ 1)) :* h) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0))))))))))) := ((con (ℤ.+ 1)) :+ (con (ℤ.+ 0))) :+ ((con (ℤ.+ 1)) :* ((h :+ h) :- con (ℤ.+ 1)) :+ ((con (ℤ.+ 0)) :* (B2 :- con (ℤ.+ 1)) :+ (con (ℤ.+ 0)) :* (B3 :+ con (ℤ.+ 1))))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
            (fix _ _ _ _))
      (Eq.refl))))

    res≈ : (₂₊ n) ⊢ sa (- half) • sb half • (Z h₁ ↑) ^ᶠ half ≈ CZ h₂
    res≈ = begin
      sa (- half) • sb half • (Z h₁ ↑) ^ᶠ half
        ≈⟨ cong sa≈ (cong sb≈ (sym right-unit)) ⟩
      term Gs (scaleᵗ (- half) L′) • term Gs (scaleᵗ half L₊) • term Gs ((# 2 , half) ∷ [])
        ≈⟨ sym (trans (term-++ Gs (scaleᵗ (- half) L′) (scaleᵗ half L₊ ++ ((# 2 , half) ∷ [])))
                      (back _ (term-++ Gs (scaleᵗ half L₊) ((# 2 , half) ∷ [])))) ⟩
      term Gs L₁
        ≈⟨ by-labels Gs L₁ L₂ labels₁ ⟩
      CZ h₂ • ε
        ≈⟨ right-unit ⟩
      CZ h₂ ∎

  CS-X₀ : (₂₊ n) ⊢ CS h • X ≈ X • CZ h₂ • CS h
  CS-X₀ = begin
    CS h • X
      ≈⟨ trans (front _ CS-split) assoc ⟩
    ta a • (tb b • Q) • X
      ≈⟨ back _ (trans assoc (back _ Q-X)) ⟩
    ta a • tb b • X • Q • Zb
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (tb-X b)) assoc)) ⟩
    ta a • X • (tb b • sb b) • Q • Zb
      ≈⟨ trans (sym assoc) (trans (front _ (ta-X a)) assoc) ⟩
    X • (ta a • sa a) • (tb b • sb b) • Q • Zb
      ≈⟨ back _ (by-passoc ((□ • □) • (□ • □) • □ • □) (□ • (□ • □) • □ • □ • □) Eq.refl) ⟩
    X • ta a • (sa a • tb b) • sb b • Q • Zb
      ≈⟨ back _ (back _ (front _ (diag₃∥ (Diag₃-sa a) (Diag₃-tb b)))) ⟩
    X • ta a • (tb b • sa a) • sb b • Q • Zb
      ≈⟨ back _ (back _ (by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □) • □ • □) Eq.refl)) ⟩
    X • ta a • tb b • (sa a • sb b) • Q • Zb
      ≈⟨ back _ (back _ (back _ (trans (sym assoc) (trans (front _ (diag₃∥ (Diag₃-• (Diag₃-sa a) (Diag₃-sb b)) Diag₃-Q)) assoc)))) ⟩
    X • ta a • tb b • Q • (sa a • sb b) • Zb
      ≈⟨ back _ (by-passoc (□ • □ • □ • (□ • □) • □) ((□ • □ • □) • □ • □ • □) Eq.refl) ⟩
    X • (ta a • tb b • Q) • sa a • sb b • Zb
      ≈⟨ back _ (cong (sym CS-split) res≈) ⟩
    X • CS h • CZ h₂
      ≈⟨ back _ (diag₃∥ Diag₃-CS (Diag₃-2 Diag-CZ)) ⟩
    X • CZ h₂ • CS h ∎
    where
    a b : F
    a = - half
    b = half
    Zb : Circuit (₂₊ n)
    Zb = (Z h₁ ↑) ^ᶠ half

------------------------------------------------------------------------
-- SC and the gadget of T past X on wire 1

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    ss : (₂₊ n) ⊢ SWAP • SWAP ≈ ε
    ss = ax swap-order

  SC-X₁ : (₂₊ n) ⊢ SC • X ↑ ≈ X ↑ • CZ h₂ • SC
  SC-X₁ = begin
    (SWAP • CS h • SWAP) • X ↑         ≈⟨ trans assoc (back _ (trans assoc (back _ (sym (ax swap-X))))) ⟩
    SWAP • CS h • X • SWAP             ≈⟨ back _ (trans (sym assoc) (trans (front _ CS-X₀) assoc)) ⟩
    SWAP • X • (CZ h₂ • CS h) • SWAP   ≈⟨ trans (sym assoc) (trans (front _ sX) assoc) ⟩
    X ↑ • SWAP • (CZ h₂ • CS h) • SWAP ≈⟨ back _ (trans (back _ assoc) (trans (sym assoc) (front _ CZ-sym))) ⟩
    X ↑ • (CZ h₂ • SWAP) • CS h • SWAP ≈⟨ back _ assoc ⟩
    X ↑ • CZ h₂ • SWAP • CS h • SWAP   ∎

  private
    Ci : Circuit (₂₊ n)
    Ci = CX ^ᶠ (- 1F)

    -- X ↑ past CX leaves X, and X X ↑ past CX⁻¹ is X ↑.
    CX-X₁ : (₂₊ n) ⊢ CX • X ↑ ≈ (X • X ↑) • CX
    CX-X₁ = CX-X↑ᶠ 1F

    Ci-XX₁ : (₂₊ n) ⊢ Ci • X • X ↑ ≈ X ↑ • Ci
    Ci-XX₁ = begin
      Ci • X • X ↑                       ≈⟨ sym (trans assoc (cancel-at (CX-invʳ 1F) _)) ⟩
      ((Ci • X • X ↑) • CX) • Ci         ≈⟨ front _ (trans assoc (back _ (sym CX-X₁))) ⟩
      (Ci • CX • X ↑) • Ci               ≈⟨ front _ (cancel-in (CX-invˡ 1F) _) ⟩
      X ↑ • Ci ∎

    TS∥X₁ : (₂₊ n) ⊢ (T h • S h₂) ∥ X ↑
    TS∥X₁ = •-∥ (sym (comm-gate₁-w↑ (T-gate h) X)) (sym (comm-gate₁-w↑ (S-gate h₂) X))

  PT-X₁ : (₂₊ n) ⊢ PT • X ↑ ≈ X ↑ • PT • P
  PT-X₁ = begin
    (Ci • T h • CX) • X ↑                   ≈⟨ trans assoc (back _ (trans assoc (back _ CX-X₁))) ⟩
    Ci • T h • (X • X ↑) • CX               ≈⟨ back _ (by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl) ⟩
    Ci • (T h • X) • X ↑ • CX               ≈⟨ back _ (front _ (Tᶠ-X 1F)) ⟩
    Ci • (X • T h • S h₂) • X ↑ • CX        ≈⟨ back _ (by-passoc ((□ • □ • □) • □ • □) (□ • (□ • □) • □ • □) Eq.refl) ⟩
    Ci • X • (T h • S h₂) • X ↑ • CX        ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ TS∥X₁) assoc))) ⟩
    Ci • X • X ↑ • (T h • S h₂) • CX        ≈⟨ trans (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) (front _ Ci-XX₁) ⟩
    (X ↑ • Ci) • (T h • S h₂) • CX          ≈⟨ by-passoc ((□ • □) • (□ • □) • □) (□ • □ • □ • □ • □) Eq.refl ⟩
    X ↑ • Ci • T h • S h₂ • CX              ≈⟨ back _ (back _ (back _ (trans (sym left-unit) (front _ (sym (CX-invʳ 1F)))))) ⟩
    X ↑ • Ci • T h • (CX • Ci) • S h₂ • CX  ≈⟨ back _ (by-passoc (□ • □ • (□ • □) • □ • □) ((□ • □ • □) • □ • □ • □) Eq.refl) ⟩
    X ↑ • PT • P                            ∎

  private
    S↑i : Circuit (₂₊ n)
    S↑i = (S h₂ ↑) ^ᶠ (- 1F)

    module OS↑ = Pow.Order (₂₊ n) {S h₂ ↑} (trans (refl' (Eq.sym (↑-pow (S h₂) p))) (lift S-order))
    module OCZ′ = Pow.Order (₂₊ n) {CZ h₂} CZ-order

    -- T ↑ past X ↑ leaves S ↑, so X ↑ past T ↑ leaves its inverse.
    X₁-T₁ : (₂₊ n) ⊢ X ↑ • T h ↑ ≈ T h ↑ • X ↑ • S↑i
    X₁-T₁ = begin
      X ↑ • T h ↑                        ≈⟨ sym (back _ (cancel-at OS↑.inverseʳ _)) ⟩
      X ↑ • T h ↑ • S h₂ ↑ • S↑i         ≈⟨ trans (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl)
                                               (trans (front _ (sym (lift (Tᶠ-X 1F)))) assoc) ⟩
      T h ↑ • X ↑ • S↑i                  ∎

    Tg : Circuit (₂₊ n)
    Tg = T h • T h ↑

    X₁-G : (₂₊ n) ⊢ X ↑ • Tg ≈ Tg • X ↑ • S↑i
    X₁-G = begin
      X ↑ • T h • T h ↑                  ≈⟨ trans (sym assoc) (trans (front _ (comm-gate₁-w↑ (T-gate h) X)) assoc) ⟩
      T h • X ↑ • T h ↑                  ≈⟨ back _ X₁-T₁ ⟩
      T h • T h ↑ • X ↑ • S↑i            ≈⟨ sym assoc ⟩
      Tg • X ↑ • S↑i                      ∎

    Y : Circuit (₂₊ n)
    Y = CS h • SC

    DY : Diag₃ (₂₊ n) Y
    DY = Diag₃-• Diag₃-CS Diag₃-SC

    DS↑i : Diag₃ (₂₊ n) S↑i
    DS↑i = Diag₃-^ᶠ (Diag₃-↑ (Diag₃-2 Diag-S)) (- 1F)

    DP : Diag₃ (₂₊ n) P
    DP = Diag₃-≈ P-SZ (Diag₃-2 (Diag-• Diag-S (Diag-• (Diag-↑ (Diag-SZ 1F 0F)) Diag-CZ)))

    GY : (₂₊ n) ⊢ Tg • Y ≈ PT
    GY = trans assoc (sym PT-dec)

    Y-X₁ : (₂₊ n) ⊢ Y • X ↑ ≈ X ↑ • Y • S↑i • P
    Y-X₁ = Inv.•-cancelˡ (₂₊ n) (begin
      Tg • Y • X ↑                       ≈⟨ trans (sym assoc) (front _ GY) ⟩
      PT • X ↑                          ≈⟨ PT-X₁ ⟩
      X ↑ • PT • P                      ≈⟨ back _ (front _ (sym GY)) ⟩
      X ↑ • (Tg • Y) • P                 ≈⟨ trans (sym assoc) (trans (front _ (trans (sym assoc) (front _ X₁-G))) assoc) ⟩
      (Tg • X ↑ • S↑i) • Y • P           ≈⟨ trans assoc (back _ (trans assoc (back _ (trans (sym assoc) (trans (front _ (diag₃∥ DS↑i DY)) assoc))))) ⟩
      Tg • X ↑ • Y • S↑i • P             ∎)

    -- The leftover: S↑⁻¹ P CZ⁻¹ is S.
    Gs′ : Vec (Gen₃ (₂₊ n)) 4
    Gs′ = gen₃ (S h₂) (Diag₃-2 Diag-S) ∷ gen₃ (S h₂ ↑) (Diag₃-↑ (Diag₃-2 Diag-S))
        ∷ gen₃ (Z h₁ ↑) (Diag₃-↑ (Diag₃-2 Diag-Z)) ∷ gen₃ (CZ h₂) (Diag₃-2 Diag-CZ) ∷ []

    K₊ K₃ K₄ : List (Fin 4 × F)
    K₊ = (# 0 , 1F) ∷ (# 1 , 1F) ∷ (# 2 , 0F) ∷ (# 3 , 1F) ∷ []
    K₃ = ((# 1 , - 1F) ∷ []) ++ K₊ ++ ((# 3 , - 1F) ∷ [])
    K₄ = (# 0 , 1F) ∷ []

    labels₂ : vec K₃ ≡ vec K₄
    labels₂ = Eq.cong₂ _∷_ (solve 3 (λ h B2 B3 → ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 1)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))))))) := ((con (ℤ.+ 1)) :+ (con (ℤ.+ 0)))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
      (Eq.cong₂ _∷_ (solve 3 (λ h B2 B3 → ((:- (con (ℤ.+ 1))) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 1)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))))))) := ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
      (Eq.cong₂ _∷_ (solve 3 (λ h B2 B3 → ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))))))) := ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
      (Eq.cong₂ _∷_ (solve 3 (λ h B2 B3 → ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 0)) :+ ((con (ℤ.+ 1)) :+ ((:- (con (ℤ.+ 1))) :+ (con (ℤ.+ 0)))))))) := ((con (ℤ.+ 0)) :+ (con (ℤ.+ 0)))) Eq.refl half (binom2 (- 1F)) (binom3 (- 1F)))
      (Eq.refl))))

    R≈S : (₂₊ n) ⊢ S↑i • P • CZ h₂ ^ᶠ (- 1F) ≈ S h₂
    R≈S = begin
      S↑i • P • CZ h₂ ^ᶠ (- 1F)
        ≈⟨ cong (sym right-unit) (cong P≈ (sym right-unit)) ⟩
      term Gs′ ((# 1 , - 1F) ∷ []) • term Gs′ K₊ • term Gs′ ((# 3 , - 1F) ∷ [])
        ≈⟨ sym (trans (term-++ Gs′ ((# 1 , - 1F) ∷ []) (K₊ ++ ((# 3 , - 1F) ∷ []))) (back _ (term-++ Gs′ K₊ ((# 3 , - 1F) ∷ [])))) ⟩
      term Gs′ K₃
        ≈⟨ by-labels Gs′ K₃ K₄ labels₂ ⟩
      S h₂ • ε
        ≈⟨ right-unit ⟩
      S h₂ ∎
      where
      P≈ : (₂₊ n) ⊢ P ≈ term Gs′ K₊
      P≈ = trans P-SZ (back _ (trans assoc (cong (refl' (↑ᶠ (S h₂) _)) (cong (refl' (↑ᶠ (Z h₁) _)) (sym right-unit)))))

  CS-X₁ : (₂₊ n) ⊢ CS h • X ↑ ≈ S h₂ • X ↑ • CS h
  CS-X₁ = begin
    CS h • X ↑
      ≈⟨ Inv.•-cancelʳ (₂₊ n) {h = CZ h₂ • SC} lhs≈rhs ⟩
    X ↑ • CS h • S↑i • P • CZ h₂ ^ᶠ (- 1F)
      ≈⟨ back _ (back _ R≈S) ⟩
    X ↑ • CS h • S h₂
      ≈⟨ back _ (sym (diag₃∥ (Diag₃-2 Diag-S) Diag₃-CS)) ⟩
    X ↑ • S h₂ • CS h
      ≈⟨ trans (sym assoc) (trans (front _ (comm-gate₁-w↑ (S-gate h₂) X)) assoc) ⟩
    S h₂ • X ↑ • CS h ∎
    where
    lhs≈rhs : (₂₊ n) ⊢ (CS h • X ↑) • CZ h₂ • SC ≈ (X ↑ • CS h • S↑i • P • CZ h₂ ^ᶠ (- 1F)) • CZ h₂ • SC
    lhs≈rhs = begin
      (CS h • X ↑) • CZ h₂ • SC
        ≈⟨ trans assoc (back _ (sym SC-X₁)) ⟩
      CS h • SC • X ↑
        ≈⟨ sym assoc ⟩
      Y • X ↑
        ≈⟨ Y-X₁ ⟩
      X ↑ • Y • S↑i • P
        ≈⟨ back _ (trans assoc (back _ (diag₃∥ Diag₃-SC (Diag₃-• DS↑i DP)))) ⟩
      X ↑ • CS h • (S↑i • P) • SC
        ≈⟨ back _ (back _ (front _ (sym (trans assoc (back _ (trans assoc (cancel-at (OCZ′.^ᶠ-inverseˡ 1F) _))))))) ⟩
      X ↑ • CS h • ((S↑i • P • CZ h₂ ^ᶠ (- 1F)) • CZ h₂) • SC
        ≈⟨ by-passoc (□ • □ • ((□ • □ • □) • □) • □) ((□ • □ • □ • □ • □) • □ • □) Eq.refl ⟩
      (X ↑ • CS h • S↑i • P • CZ h₂ ^ᶠ (- 1F)) • CZ h₂ • SC ∎

------------------------------------------------------------------------
-- A diagonal one wire up passes CX

private
  ats-cx : (as : Atoms (₁₊ n)) → ats⋆ (lift-ats as) cx ≡ lift-ats as
  ats-cx []             = Eq.refl
  ats-cx ((ℓ , k) ∷ as) = Eq.cong ((small ℓ , k) ∷_) (ats-cx as)

  lift-cx : (d : DE₃ (₁₊ n)) → lift-d₃ d ⋆ˡ³ cx ≡ lift-d₃ d
  lift-cx (de s (c ∷ cs) as ∣ ts) =
    Eq.cong₂ _∣_ (Eq.cong₂ (de s) (Eq.cong (λ t → 0F ∷ t ∷ cs) (FR.+-identityʳ c)) (ats-cx as)) (ats-cx ts)

cx∥↑ : {D : Circuit (₁₊ n)} → Diag₃ (₁₊ n) D → (₂₊ n) ⊢ CX ∥ (D ↑)
cx∥↑ {n} {D} (d , e) = begin
  CX • D ↑                       ≈⟨ back _ (trans (lift e) (lift₃-sound d)) ⟩
  CX • ⟦ lift-d₃ d ⟧³            ≈⟨ back _ (refl' (Eq.cong ⟦_⟧³ (Eq.sym (lift-cx d)))) ⟩
  CX • ⟦ lift-d₃ d ⋆ˡ³ cx ⟧³     ≈⟨ sym (⋆ˡ³-sound (lift-d₃ d) cx) ⟩
  ⟦ lift-d₃ d ⟧³ • CX            ≈⟨ front _ (sym (trans (lift e) (lift₃-sound d))) ⟩
  D ↑ • CX                       ∎
  where open Width (₂₊ n)
