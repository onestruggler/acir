------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations of the hard subcase of Case 3 (case 3.2.2.2 with w_β
-- odd), for j < ℓ < j′ < ℓ′.  With D the powers of i at the four
-- indices that make the four odd entries ≡ 1 (mod γ³), and D′ the
-- same with the exponents at ℓ and j′ swapped:
--
-- * the left and right faces: K†_[j,ℓ] D = V K†_[j,ℓ] i_[ℓ]ᑫ for a
--   word V of transpositions and powers of i;
-- * the middle face: X_[ℓ,j′] D = D′ X_[ℓ,j′];
-- * the bottom face: K†_[j,ℓ] X_[ℓ,j′] = B K†_[j,ℓ], with B the path
--   of (case 3.2.2.2.1), from (17);
--
-- and so the square of the paper's outer perimeter.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; _+_ ; _*_ ; z≤n ; s≤s)

module Examples.Groups.Clifford+CS-TwoLevel.HardRel {n : ℕ} where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.List.Relation.Unary.All using ([] ; _∷_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_ ; ≢-sym)
import Relation.Binary.Reasoning.Setoid as SR

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Derived {n}
  using (K-K† ; K†≈Kii ; K†L²≈XK† ; IX≈XL ; K†⁴X≈XK†⁴ ; conj-^ ; comm-words ; Apartʷ ; Apartʷʷ ;
         _⁻¹ ; inverseˡ)
open import Examples.Groups.Clifford+CS-TwoLevel.Basic {n} using (Letters≤)
open import Examples.Groups.Clifford+CS-TwoLevel.MainTools {n} using (Apartʷ-^)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

------------------------------------------------------------------------
-- Powers and inverses

Apartʷʷ-^ : (u w : Word (Gen n)) → Apartʷʷ u w → ∀ e → Apartʷʷ u (w ^ e)
Apartʷʷ-^ u w a zero = tt
Apartʷʷ-^ u w a (suc zero) = a
Apartʷʷ-^ u w a (suc (suc e)) = a , Apartʷʷ-^ u w a (suc e)

Letters≤-^ : ∀ {b : Fin n} (w : Word (Gen n)) → Letters≤ b w → ∀ e → Letters≤ b (w ^ e)
Letters≤-^ w h zero = tt
Letters≤-^ w h (suc zero) = h
Letters≤-^ w h (suc (suc e)) = h , Letters≤-^ w h (suc e)

Letters≤-⁻¹ : ∀ {b : Fin n} (w : Word (Gen n)) → Letters≤ b w → Letters≤ b (w ⁻¹)
Letters≤-⁻¹ [ X-gen a c p ]ʷ h = h
Letters≤-⁻¹ [ K-gen a c p ]ʷ ()
Letters≤-⁻¹ [ i-gen c ]ʷ h = h , h , h
Letters≤-⁻¹ ε _ = tt
Letters≤-⁻¹ (u • v) (hu , hv) = Letters≤-⁻¹ v hv , Letters≤-⁻¹ u hu

-- Powers of i at distinct indices commute.
comm-ii^ : ∀ {x y : Fin n} → x ≢ y → ∀ e f → i x ^ e • i y ^ f ≈ i y ^ f • i x ^ e
comm-ii^ {x} {y} x≢y e f =
  comm-words (i x ^ e) (i y ^ f) (Apartʷʷ-^ (i x ^ e) (i y) (Apartʷ-^ (i x) (i-gen y) ((x≢y ∷ []) ∷ []) e) f)

private
  -- Past a letter: X a ≈ a′ X gives X (a r) ≈ a′ (X r).
  pass : ∀ {x a a′ r : Word (Gen n)} → x • a ≈ a′ • x → x • (a • r) ≈ a′ • (x • r)
  pass h = trans (sym assoc) (trans (cleft h) assoc)

------------------------------------------------------------------------
-- The relations

module _ {j ℓ j′ ℓ′ : Fin n} (jℓ : j < ℓ) (ℓj′ : ℓ < j′) (j′ℓ′ : j′ < ℓ′) where

  private
    jj′ = ℕP.<-trans jℓ ℓj′
    ℓℓ′ = ℕP.<-trans ℓj′ j′ℓ′
    jℓ′ = ℕP.<-trans jj′ j′ℓ′
    j≢ℓ = FinP.<⇒≢ jℓ
    j≢j′ = FinP.<⇒≢ jj′
    j≢ℓ′ = FinP.<⇒≢ jℓ′
    ℓ≢j′ = FinP.<⇒≢ ℓj′
    ℓ≢ℓ′ = FinP.<⇒≢ ℓℓ′
    j′≢ℓ′ = FinP.<⇒≢ j′ℓ′
    K†′ = K† j ℓ jℓ
    Xm = X ℓ j′ ℓj′

  -- K†_[j,ℓ] commutes with i_[j]ᶜ i_[ℓ]ᶜ, by (15).
  K†-ii : ∀ c → K†′ • (i j ^ c • i ℓ ^ c) ≈ (i j ^ c • i ℓ ^ c) • K†′
  K†-ii zero = trans (trans (cright left-unit) right-unit) (sym (trans (cleft left-unit) left-unit))
  K†-ii (suc c) = begin
    K†′ • (i j ^ suc c • i ℓ ^ suc c)             ≈⟨ cright Q-suc ⟩
    K†′ • ((i j • i ℓ) • Q)                       ≈⟨ sym assoc ⟩
    (K†′ • (i j • i ℓ)) • Q                       ≈⟨ cleft one ⟩
    ((i j • i ℓ) • K†′) • Q                       ≈⟨ assoc ⟩
    (i j • i ℓ) • (K†′ • Q)                       ≈⟨ cright K†-ii c ⟩
    (i j • i ℓ) • (Q • K†′)                       ≈⟨ sym assoc ⟩
    ((i j • i ℓ) • Q) • K†′                       ≈⟨ cleft sym Q-suc ⟩
    (i j ^ suc c • i ℓ ^ suc c) • K†′             ∎
    where
    Q = i j ^ c • i ℓ ^ c
    one : K†′ • (i j • i ℓ) ≈ (i j • i ℓ) • K†′
    one = conj-^ (trans (axiom (rel-15 jℓ)) (sym assoc)) 7
    Q-suc : i j ^ suc c • i ℓ ^ suc c ≈ (i j • i ℓ) • Q
    Q-suc = begin
      i j ^ suc c • i ℓ ^ suc c                   ≈⟨ cong (^-+ (i j) 1 c) (^-+ (i ℓ) 1 c) ⟩
      (i j • i j ^ c) • (i ℓ • i ℓ ^ c)           ≈⟨ assoc ⟩
      i j • (i j ^ c • (i ℓ • i ℓ ^ c))           ≈⟨ cright sym assoc ⟩
      i j • ((i j ^ c • i ℓ) • i ℓ ^ c)           ≈⟨ cright cleft comm-ii^ j≢ℓ c 1 ⟩
      i j • ((i ℓ • i j ^ c) • i ℓ ^ c)           ≈⟨ cright assoc ⟩
      i j • (i ℓ • (i j ^ c • i ℓ ^ c))           ≈⟨ sym assoc ⟩
      (i j • i ℓ) • Q                             ∎

  -- K†_[j,ℓ] i_[ℓ]^(2h) = X_[j,ℓ]ʰ K†_[j,ℓ], by (q″).
  K†-ii² : ∀ h q → h ℕ.≤ 1 → K†′ • (i ℓ ^ (2 * h) • i ℓ ^ q) ≈ X j ℓ jℓ ^ h • (K†′ • i ℓ ^ q)
  K†-ii² zero q _ = trans (cright left-unit) (sym left-unit)
  K†-ii² (suc zero) q _ = trans (sym assoc) (trans (cleft K†L²≈XK† jℓ) assoc)
  K†-ii² (suc (suc h)) q (s≤s ())

  -- The left and right faces.
  face : ∀ c h q e′ e″ → h ℕ.≤ 1 →
         K†′ • (i j ^ c • i ℓ ^ (c + (2 * h + q)) • i j′ ^ e′ • i ℓ′ ^ e″) ≈
         ((i j′ ^ e′ • i ℓ′ ^ e″) • ((i j ^ c • i ℓ ^ c) • X j ℓ jℓ ^ h)) • (K†′ • i ℓ ^ q)
  face c h q e′ e″ h≤1 = begin
    K†′ • (i j ^ c • i ℓ ^ (c + (2 * h + q)) • R)       ≈⟨ cright D≈ ⟩
    K†′ • (R • (P • E))                                  ≈⟨ sym assoc ⟩
    (K†′ • R) • (P • E)                                  ≈⟨ cleft comm-words K†′ R apK ⟩
    (R • K†′) • (P • E)                                  ≈⟨ assoc ⟩
    R • (K†′ • (P • E))                                  ≈⟨ cright sym assoc ⟩
    R • ((K†′ • P) • E)                                  ≈⟨ cright cleft K†-ii c ⟩
    R • ((P • K†′) • E)                                  ≈⟨ cright assoc ⟩
    R • (P • (K†′ • E))                                  ≈⟨ cright cright K†-ii² h q h≤1 ⟩
    R • (P • (X j ℓ jℓ ^ h • (K†′ • i ℓ ^ q)))           ≈⟨ cright sym assoc ⟩
    R • ((P • X j ℓ jℓ ^ h) • (K†′ • i ℓ ^ q))           ≈⟨ sym assoc ⟩
    (R • (P • X j ℓ jℓ ^ h)) • (K†′ • i ℓ ^ q)           ∎
    where
    R = i j′ ^ e′ • i ℓ′ ^ e″
    P = i j ^ c • i ℓ ^ c
    E = i ℓ ^ (2 * h) • i ℓ ^ q
    -- Apart from R.
    apR : ∀ (u : Word (Gen n)) → Apartʷ u (i-gen j′) → Apartʷ u (i-gen ℓ′) → Apartʷʷ u R
    apR u a₁ a₂ = Apartʷʷ-^ u (i j′) a₁ e′ , Apartʷʷ-^ u (i ℓ′) a₂ e″
    apK : Apartʷʷ K†′ R
    apK = apR K†′ (Apartʷ-^ (K j ℓ jℓ) (i-gen j′) ((j≢j′ ∷ []) ∷ (ℓ≢j′ ∷ []) ∷ []) 7)
                  (Apartʷ-^ (K j ℓ jℓ) (i-gen ℓ′) ((j≢ℓ′ ∷ []) ∷ (ℓ≢ℓ′ ∷ []) ∷ []) 7)
    ap-ij : ∀ e (y : Fin n) → j ≢ y → Apartʷ (i j ^ e) (i-gen y)
    ap-ij e y ne = Apartʷ-^ (i j) (i-gen y) ((ne ∷ []) ∷ []) e
    ap-iℓ : ∀ e (y : Fin n) → ℓ ≢ y → Apartʷ (i ℓ ^ e) (i-gen y)
    ap-iℓ e y ne = Apartʷ-^ (i ℓ) (i-gen y) ((ne ∷ []) ∷ []) e
    apPE : Apartʷʷ (P • E) R
    apPE = apR (P • E) ((ap-ij c j′ j≢j′ , ap-iℓ c j′ ℓ≢j′) , (ap-iℓ (2 * h) j′ ℓ≢j′ , ap-iℓ q j′ ℓ≢j′))
                       ((ap-ij c ℓ′ j≢ℓ′ , ap-iℓ c ℓ′ ℓ≢ℓ′) , (ap-iℓ (2 * h) ℓ′ ℓ≢ℓ′ , ap-iℓ q ℓ′ ℓ≢ℓ′))
    D≈ : i j ^ c • i ℓ ^ (c + (2 * h + q)) • R ≈ R • (P • E)
    D≈ = begin
      i j ^ c • i ℓ ^ (c + (2 * h + q)) • R           ≈⟨ sym assoc ⟩
      (i j ^ c • i ℓ ^ (c + (2 * h + q))) • R         ≈⟨ cleft cright trans (^-+ (i ℓ) c (2 * h + q))
                                                                          (cright ^-+ (i ℓ) (2 * h) q) ⟩
      (i j ^ c • (i ℓ ^ c • E)) • R                    ≈⟨ cleft sym assoc ⟩
      (P • E) • R                                      ≈⟨ comm-words (P • E) R apPE ⟩
      R • (P • E)                                      ∎

  -- The middle face.
  middle : ∀ e₁ e₂ e₃ e₄ → Xm • (i j ^ e₁ • i ℓ ^ e₂ • i j′ ^ e₃ • i ℓ′ ^ e₄) ≈
                           (i j ^ e₁ • i ℓ ^ e₃ • i j′ ^ e₂ • i ℓ′ ^ e₄) • Xm
  middle e₁ e₂ e₃ e₄ = begin
    Xm • (i j ^ e₁ • i ℓ ^ e₂ • i j′ ^ e₃ • i ℓ′ ^ e₄)     ≈⟨ pass xj ⟩
    i j ^ e₁ • (Xm • (i ℓ ^ e₂ • i j′ ^ e₃ • i ℓ′ ^ e₄))   ≈⟨ cright pass xℓ ⟩
    i j ^ e₁ • (i j′ ^ e₂ • (Xm • (i j′ ^ e₃ • i ℓ′ ^ e₄))) ≈⟨ cright cright pass xj′ ⟩
    i j ^ e₁ • (i j′ ^ e₂ • (i ℓ ^ e₃ • (Xm • i ℓ′ ^ e₄))) ≈⟨ cright cright cright xℓ′ ⟩
    i j ^ e₁ • (i j′ ^ e₂ • (i ℓ ^ e₃ • (i ℓ′ ^ e₄ • Xm))) ≈⟨ cright swap ⟩
    i j ^ e₁ • (i ℓ ^ e₃ • (i j′ ^ e₂ • (i ℓ′ ^ e₄ • Xm))) ≈⟨ cright cright sym assoc ⟩
    i j ^ e₁ • (i ℓ ^ e₃ • ((i j′ ^ e₂ • i ℓ′ ^ e₄) • Xm)) ≈⟨ cright sym assoc ⟩
    i j ^ e₁ • ((i ℓ ^ e₃ • (i j′ ^ e₂ • i ℓ′ ^ e₄)) • Xm) ≈⟨ sym assoc ⟩
    (i j ^ e₁ • i ℓ ^ e₃ • i j′ ^ e₂ • i ℓ′ ^ e₄) • Xm     ∎
    where
    xj : Xm • i j ^ e₁ ≈ i j ^ e₁ • Xm
    xj = sym (conj-^ (axiom (comm-iX ℓj′ j≢ℓ j≢j′)) e₁)
    xℓ : Xm • i ℓ ^ e₂ ≈ i j′ ^ e₂ • Xm
    xℓ = sym (conj-^ (axiom (swap-iX ℓj′)) e₂)
    xj′ : Xm • i j′ ^ e₃ ≈ i ℓ ^ e₃ • Xm
    xj′ = sym (conj-^ (IX≈XL ℓj′) e₃)
    xℓ′ : Xm • i ℓ′ ^ e₄ ≈ i ℓ′ ^ e₄ • Xm
    xℓ′ = sym (conj-^ (axiom (comm-iX ℓj′ (≢-sym ℓ≢ℓ′) (≢-sym j′≢ℓ′))) e₄)
    swap : i j′ ^ e₂ • (i ℓ ^ e₃ • (i ℓ′ ^ e₄ • Xm)) ≈ i ℓ ^ e₃ • (i j′ ^ e₂ • (i ℓ′ ^ e₄ • Xm))
    swap = trans (sym assoc) (trans (cleft comm-ii^ (≢-sym ℓ≢j′) e₂ e₃) assoc)

  -- The path of (case 3.2.2.2.1), with each K† written K i i.
  B : Word (Gen n)
  B = K j′ ℓ′ j′ℓ′ • K j j′ jj′ • K ℓ ℓ′ ℓℓ′ • Xm •
      (K ℓ ℓ′ ℓℓ′ • i ℓ • i ℓ′) • (K j j′ jj′ • i j • i j′) • (K j′ ℓ′ j′ℓ′ • i j′ • i ℓ′)

  -- The bottom face, from (17).
  bottom : K†′ • Xm ≈ B • K†′
  bottom = begin
    K†′ • Xm                                                  ≈⟨ sym left-unit ⟩
    ε • (K†′ • Xm)                                            ≈⟨ cleft sym undo ⟩
    (Kinv • A) • (K†′ • Xm)                                   ≈⟨ by-assoc auto ⟩
    Kinv • (K† ℓ ℓ′ ℓℓ′ • K† j j′ jj′ • K† j′ ℓ′ j′ℓ′ • K†′ • Xm)
                                                              ≈⟨ cright K†⁴X≈XK†⁴ jℓ ℓj′ j′ℓ′ ⟩
    Kinv • (Xm • K† ℓ ℓ′ ℓℓ′ • K† j j′ jj′ • K† j′ ℓ′ j′ℓ′ • K†′)
                                                              ≈⟨ cright cright cong (K†≈Kii ℓℓ′)
                                                                   (cong (K†≈Kii jj′) (cleft K†≈Kii j′ℓ′)) ⟩
    Kinv • (Xm • (K ℓ ℓ′ ℓℓ′ • i ℓ • i ℓ′) • (K j j′ jj′ • i j • i j′) • (K j′ ℓ′ j′ℓ′ • i j′ • i ℓ′) • K†′)
                                                              ≈⟨ by-assoc auto ⟩
    B • K†′                                                   ∎
    where
    A = K† ℓ ℓ′ ℓℓ′ • K† j j′ jj′ • K† j′ ℓ′ j′ℓ′
    Kinv = K j′ ℓ′ j′ℓ′ • K j j′ jj′ • K ℓ ℓ′ ℓℓ′
    undo : Kinv • A ≈ ε
    undo = begin
      Kinv • A                                                ≈⟨ by-assoc auto ⟩
      K j′ ℓ′ j′ℓ′ • K j j′ jj′ • (K ℓ ℓ′ ℓℓ′ • K† ℓ ℓ′ ℓℓ′) • K† j j′ jj′ • K† j′ ℓ′ j′ℓ′
                                                              ≈⟨ cright cright cleft K-K† ℓℓ′ ⟩
      K j′ ℓ′ j′ℓ′ • K j j′ jj′ • ε • K† j j′ jj′ • K† j′ ℓ′ j′ℓ′
                                                              ≈⟨ cright cright left-unit ⟩
      K j′ ℓ′ j′ℓ′ • K j j′ jj′ • K† j j′ jj′ • K† j′ ℓ′ j′ℓ′ ≈⟨ cright sym assoc ⟩
      K j′ ℓ′ j′ℓ′ • (K j j′ jj′ • K† j j′ jj′) • K† j′ ℓ′ j′ℓ′
                                                              ≈⟨ cright cleft K-K† jj′ ⟩
      K j′ ℓ′ j′ℓ′ • ε • K† j′ ℓ′ j′ℓ′                        ≈⟨ cright left-unit ⟩
      K j′ ℓ′ j′ℓ′ • K† j′ ℓ′ j′ℓ′                            ≈⟨ K-K† j′ℓ′ ⟩
      ε                                                       ∎

  ----------------------------------------------------------------------
  -- The square, for exponents c (at j), c + 2 h₂ + q (at ℓ),
  -- c + 2 h₃ + q′ (at j′) and e₄ (at ℓ′)

  module Hard (c h₂ q h₃ q′ e₄ : ℕ) (h₂≤1 : h₂ ℕ.≤ 1) (h₃≤1 : h₃ ℕ.≤ 1) where

    E₂ E₃ : ℕ
    E₂ = c + (2 * h₂ + q)
    E₃ = c + (2 * h₃ + q′)

    D D′ Vs Vr G′ : Word (Gen n)
    D = i j ^ c • i ℓ ^ E₂ • i j′ ^ E₃ • i ℓ′ ^ e₄
    D′ = i j ^ c • i ℓ ^ E₃ • i j′ ^ E₂ • i ℓ′ ^ e₄
    Vs = (i j′ ^ E₃ • i ℓ′ ^ e₄) • ((i j ^ c • i ℓ ^ c) • X j ℓ jℓ ^ h₂)
    Vr = (i j′ ^ E₂ • i ℓ′ ^ e₄) • ((i j ^ c • i ℓ ^ c) • X j ℓ jℓ ^ h₃)
    G′ = Vr ⁻¹ • (B • Vs)

    -- The normal edge from D s is K†_[j,ℓ]: V_s t = K†_[j,ℓ] D s.
    T₀-rel : Vs • (K†′ • i ℓ ^ q) ≈ (K j ℓ jℓ • i j • i ℓ) • D
    T₀-rel = trans (sym (face c h₂ q E₃ e₄ h₂≤1)) (cleft K†≈Kii jℓ)

    rel : (K†′ • i ℓ ^ q′) • Xm ≈ G′ • (K†′ • i ℓ ^ q)
    rel = sym (begin
      (Vr ⁻¹ • (B • Vs)) • (K†′ • i ℓ ^ q)          ≈⟨ assoc ⟩
      Vr ⁻¹ • ((B • Vs) • (K†′ • i ℓ ^ q))          ≈⟨ cright assoc ⟩
      Vr ⁻¹ • (B • (Vs • (K†′ • i ℓ ^ q)))          ≈⟨ cright cright sym (face c h₂ q E₃ e₄ h₂≤1) ⟩
      Vr ⁻¹ • (B • (K†′ • D))                       ≈⟨ cright sym assoc ⟩
      Vr ⁻¹ • ((B • K†′) • D)                       ≈⟨ cright cleft sym bottom ⟩
      Vr ⁻¹ • ((K†′ • Xm) • D)                      ≈⟨ cright assoc ⟩
      Vr ⁻¹ • (K†′ • (Xm • D))                      ≈⟨ cright cright middle c E₂ E₃ e₄ ⟩
      Vr ⁻¹ • (K†′ • (D′ • Xm))                     ≈⟨ cright sym assoc ⟩
      Vr ⁻¹ • ((K†′ • D′) • Xm)                     ≈⟨ cright cleft face c h₃ q′ E₂ e₄ h₃≤1 ⟩
      Vr ⁻¹ • ((Vr • (K†′ • i ℓ ^ q′)) • Xm)        ≈⟨ cright assoc ⟩
      Vr ⁻¹ • (Vr • ((K†′ • i ℓ ^ q′) • Xm))        ≈⟨ sym assoc ⟩
      (Vr ⁻¹ • Vr) • ((K†′ • i ℓ ^ q′) • Xm)        ≈⟨ cleft inverseˡ ⟩
      ε • ((K†′ • i ℓ ^ q′) • Xm)                   ≈⟨ left-unit ⟩
      (K†′ • i ℓ ^ q′) • Xm                         ∎)

    -- The transpositions and powers of i of V_s and V_r⁻¹ act on
    -- indices ≤ ℓ′.
    Vs-letters : Letters≤ ℓ′ Vs
    Vs-letters = (Letters≤-^ (i j′) (ℕP.<⇒≤ j′ℓ′) E₃ , Letters≤-^ (i ℓ′) ℕP.≤-refl e₄) ,
                 (Letters≤-^ (i j) (ℕP.<⇒≤ jℓ′) c , Letters≤-^ (i ℓ) (ℕP.<⇒≤ ℓℓ′) c) ,
                 Letters≤-^ (X j ℓ jℓ) (ℕP.<⇒≤ ℓℓ′) h₂

    Vr⁻¹-letters : Letters≤ ℓ′ (Vr ⁻¹)
    Vr⁻¹-letters = Letters≤-⁻¹ Vr
      ((Letters≤-^ (i j′) (ℕP.<⇒≤ j′ℓ′) E₂ , Letters≤-^ (i ℓ′) ℕP.≤-refl e₄) ,
       (Letters≤-^ (i j) (ℕP.<⇒≤ jℓ′) c , Letters≤-^ (i ℓ) (ℕP.<⇒≤ ℓℓ′) c) ,
       Letters≤-^ (X j ℓ jℓ) (ℕP.<⇒≤ ℓℓ′) h₃)
