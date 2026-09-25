------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations of the hard subcase of Cases 3–5 (the first two odd
-- entries are j < α, and w_β is odd, β = α + 1), for j < α < β < ℓ′.
-- With D_s the powers of ω at the four indices that make the four odd
-- entries ≡ 1 (mod δ³), and D_r the same with the exponents at α and β
-- swapped:
--
-- * the left and right faces: H_[j,α] D = V H_[j,α] ω_[j]ᶻ for a word
--   V of powers of ω, by (17);
-- * the middle face: X_[α,β] D_s = D_r X_[α,β];
-- * the bottom face: H_[j,α] X_[α,β] = B H_[j,α], with B either path
--   of the thesis, from (s) or (t);
--
-- and so the square of the outer perimeter.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; _+_ ; _∸_)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.HardRel {n : ℕ} where

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
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Derived {n}
  using (H-H ; ωX≈Xω ; ωX≈Xω′ ; ω^-+ ; ω^+8 ; conj-^ ; comm-words ; Apartʷ ; Apartʷʷ ; Hs ; Ht ;
         _⁻¹ ; inverseˡ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Basic {n} using (Letters≤)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.MainTools {n} using (Apartʷ-^)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

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
Letters≤-⁻¹ [ H-gen a c p ]ʷ ()
Letters≤-⁻¹ [ ω-gen c ]ʷ h = h , h , h , h , h , h , h
Letters≤-⁻¹ ε _ = tt
Letters≤-⁻¹ (u • v) (hu , hv) = Letters≤-⁻¹ v hv , Letters≤-⁻¹ u hu

-- Powers of ω at distinct indices commute.
comm-ωω^ : ∀ {x y : Fin n} → x ≢ y → ∀ e f → ω x ^ e • ω y ^ f ≈ ω y ^ f • ω x ^ e
comm-ωω^ x≢y e f = comm⇒pow-comm e f (axiom (comm-ωω x≢y))

private
  -- Past a letter: x a ≈ a′ x gives x (a r) ≈ a′ (x r).
  pass : ∀ {x a a′ r : Word (Gen n)} → x • a ≈ a′ • x → x • (a • r) ≈ a′ • (x • r)
  pass h = trans (sym assoc) (trans (cleft h) assoc)

------------------------------------------------------------------------
-- The relations

module _ {j α β ℓ′ : Fin n} (jα : j < α) (αβ : α < β) (βℓ′ : β < ℓ′) where

  private
    jβ = FinP.<-trans jα αβ
    αℓ′ = FinP.<-trans αβ βℓ′
    jℓ′ = FinP.<-trans jβ βℓ′
    j≢α = FinP.<⇒≢ jα
    j≢β = FinP.<⇒≢ jβ
    j≢ℓ′ = FinP.<⇒≢ jℓ′
    α≢β = FinP.<⇒≢ αβ
    α≢ℓ′ = FinP.<⇒≢ αℓ′
    β≢ℓ′ = FinP.<⇒≢ βℓ′
    Hjα = H j α jα
    Xαβ = X α β αβ
    Hβℓ′ = H β ℓ′ βℓ′

  -- H_[j,α] commutes with ω_[j]ᶜ ω_[α]ᶜ, by (17).
  H-ωω : ∀ c → Hjα • (ω j ^ c • ω α ^ c) ≈ (ω j ^ c • ω α ^ c) • Hjα
  H-ωω zero = trans (trans (cright left-unit) right-unit) (sym (trans (cleft left-unit) left-unit))
  H-ωω (suc c) = begin
    Hjα • (ω j ^ suc c • ω α ^ suc c)             ≈⟨ cright Q-suc ⟩
    Hjα • ((ω j • ω α) • Q)                       ≈⟨ sym assoc ⟩
    (Hjα • (ω j • ω α)) • Q                       ≈⟨ cleft one ⟩
    ((ω j • ω α) • Hjα) • Q                       ≈⟨ assoc ⟩
    (ω j • ω α) • (Hjα • Q)                       ≈⟨ cright H-ωω c ⟩
    (ω j • ω α) • (Q • Hjα)                       ≈⟨ sym assoc ⟩
    ((ω j • ω α) • Q) • Hjα                       ≈⟨ cleft sym Q-suc ⟩
    (ω j ^ suc c • ω α ^ suc c) • Hjα             ∎
    where
    Q = ω j ^ c • ω α ^ c
    one : Hjα • (ω j • ω α) ≈ (ω j • ω α) • Hjα
    one = sym (trans assoc (axiom (scalar-H jα)))
    Q-suc : ω j ^ suc c • ω α ^ suc c ≈ (ω j • ω α) • Q
    Q-suc = begin
      ω j ^ suc c • ω α ^ suc c                   ≈⟨ cong (^-+ (ω j) 1 c) (^-+ (ω α) 1 c) ⟩
      (ω j • ω j ^ c) • (ω α • ω α ^ c)           ≈⟨ assoc ⟩
      ω j • (ω j ^ c • (ω α • ω α ^ c))           ≈⟨ cright sym assoc ⟩
      ω j • ((ω j ^ c • ω α) • ω α ^ c)           ≈⟨ cright cleft comm-ωω^ j≢α c 1 ⟩
      ω j • ((ω α • ω j ^ c) • ω α ^ c)           ≈⟨ cright assoc ⟩
      ω j • (ω α • (ω j ^ c • ω α ^ c))           ≈⟨ sym assoc ⟩
      (ω j • ω α) • Q                             ∎

  -- The left and right faces.
  face : ∀ c z e₃ e₄ →
         Hjα • (ω j ^ (c + z) • ω α ^ c • ω β ^ e₃ • ω ℓ′ ^ e₄) ≈
         ((ω β ^ e₃ • ω ℓ′ ^ e₄) • (ω j ^ c • ω α ^ c)) • (Hjα • ω j ^ z)
  face c z e₃ e₄ = begin
    Hjα • (ω j ^ (c + z) • ω α ^ c • R)                  ≈⟨ cright D≈ ⟩
    Hjα • (R • (P • ω j ^ z))                            ≈⟨ sym assoc ⟩
    (Hjα • R) • (P • ω j ^ z)                            ≈⟨ cleft comm-words Hjα R apH ⟩
    (R • Hjα) • (P • ω j ^ z)                            ≈⟨ assoc ⟩
    R • (Hjα • (P • ω j ^ z))                            ≈⟨ cright sym assoc ⟩
    R • ((Hjα • P) • ω j ^ z)                            ≈⟨ cright cleft H-ωω c ⟩
    R • ((P • Hjα) • ω j ^ z)                            ≈⟨ cright assoc ⟩
    R • (P • (Hjα • ω j ^ z))                            ≈⟨ sym assoc ⟩
    (R • P) • (Hjα • ω j ^ z)                            ∎
    where
    R = ω β ^ e₃ • ω ℓ′ ^ e₄
    P = ω j ^ c • ω α ^ c
    -- Apart from R.
    apR : ∀ (u : Word (Gen n)) → Apartʷ u (ω-gen β) → Apartʷ u (ω-gen ℓ′) → Apartʷʷ u R
    apR u a₁ a₂ = Apartʷʷ-^ u (ω β) a₁ e₃ , Apartʷʷ-^ u (ω ℓ′) a₂ e₄
    apH : Apartʷʷ Hjα R
    apH = apR Hjα ((j≢β ∷ []) ∷ (α≢β ∷ []) ∷ []) ((j≢ℓ′ ∷ []) ∷ (α≢ℓ′ ∷ []) ∷ [])
    ap-ωj : ∀ e (y : Fin n) → j ≢ y → Apartʷ (ω j ^ e) (ω-gen y)
    ap-ωj e y ne = Apartʷ-^ (ω j) (ω-gen y) ((ne ∷ []) ∷ []) e
    ap-ωα : ∀ e (y : Fin n) → α ≢ y → Apartʷ (ω α ^ e) (ω-gen y)
    ap-ωα e y ne = Apartʷ-^ (ω α) (ω-gen y) ((ne ∷ []) ∷ []) e
    apPZ : Apartʷʷ (P • ω j ^ z) R
    apPZ = apR (P • ω j ^ z) ((ap-ωj c β j≢β , ap-ωα c β α≢β) , ap-ωj z β j≢β)
                             ((ap-ωj c ℓ′ j≢ℓ′ , ap-ωα c ℓ′ α≢ℓ′) , ap-ωj z ℓ′ j≢ℓ′)
    D≈ : ω j ^ (c + z) • ω α ^ c • R ≈ R • (P • ω j ^ z)
    D≈ = begin
      ω j ^ (c + z) • ω α ^ c • R                        ≈⟨ cleft sym (ω^-+ c z) ⟩
      (ω j ^ c • ω j ^ z) • ω α ^ c • R                  ≈⟨ trans assoc (cright sym assoc) ⟩
      ω j ^ c • (ω j ^ z • ω α ^ c) • R                  ≈⟨ cright cleft comm-ωω^ j≢α z c ⟩
      ω j ^ c • (ω α ^ c • ω j ^ z) • R                  ≈⟨ trans (sym assoc) (cleft sym assoc) ⟩
      (P • ω j ^ z) • R                                  ≈⟨ comm-words (P • ω j ^ z) R apPZ ⟩
      R • (P • ω j ^ z)                                  ∎

  -- The middle face.
  middle : ∀ e₁ e₂ e₃ e₄ → Xαβ • (ω j ^ e₁ • ω α ^ e₂ • ω β ^ e₃ • ω ℓ′ ^ e₄) ≈
                           (ω j ^ e₁ • ω α ^ e₃ • ω β ^ e₂ • ω ℓ′ ^ e₄) • Xαβ
  middle e₁ e₂ e₃ e₄ = begin
    Xαβ • (ω j ^ e₁ • ω α ^ e₂ • ω β ^ e₃ • ω ℓ′ ^ e₄)      ≈⟨ pass xj ⟩
    ω j ^ e₁ • (Xαβ • (ω α ^ e₂ • ω β ^ e₃ • ω ℓ′ ^ e₄))    ≈⟨ cright pass xα ⟩
    ω j ^ e₁ • (ω β ^ e₂ • (Xαβ • (ω β ^ e₃ • ω ℓ′ ^ e₄)))  ≈⟨ cright cright pass xβ ⟩
    ω j ^ e₁ • (ω β ^ e₂ • (ω α ^ e₃ • (Xαβ • ω ℓ′ ^ e₄)))  ≈⟨ cright cright cright xℓ′ ⟩
    ω j ^ e₁ • (ω β ^ e₂ • (ω α ^ e₃ • (ω ℓ′ ^ e₄ • Xαβ)))  ≈⟨ cright swap ⟩
    ω j ^ e₁ • (ω α ^ e₃ • (ω β ^ e₂ • (ω ℓ′ ^ e₄ • Xαβ)))  ≈⟨ trans (cright cright sym assoc) (trans (cright sym assoc) (sym assoc)) ⟩
    (ω j ^ e₁ • ω α ^ e₃ • ω β ^ e₂ • ω ℓ′ ^ e₄) • Xαβ      ∎
    where
    xj : Xαβ • ω j ^ e₁ ≈ ω j ^ e₁ • Xαβ
    xj = sym (conj-^ (axiom (comm-ωX αβ j≢α j≢β)) e₁)
    xα : Xαβ • ω α ^ e₂ ≈ ω β ^ e₂ • Xαβ
    xα = sym (conj-^ (ωX≈Xω αβ) e₂)
    xβ : Xαβ • ω β ^ e₃ ≈ ω α ^ e₃ • Xαβ
    xβ = sym (conj-^ (ωX≈Xω′ αβ) e₃)
    xℓ′ : Xαβ • ω ℓ′ ^ e₄ ≈ ω ℓ′ ^ e₄ • Xαβ
    xℓ′ = sym (conj-^ (axiom (comm-ωX αβ (≢-sym α≢ℓ′) (≢-sym β≢ℓ′))) e₄)
    swap : ω β ^ e₂ • (ω α ^ e₃ • (ω ℓ′ ^ e₄ • Xαβ)) ≈ ω α ^ e₃ • (ω β ^ e₂ • (ω ℓ′ ^ e₄ • Xαβ))
    swap = trans (sym assoc) (trans (cleft comm-ωω^ (≢-sym α≢β) e₂ e₃) assoc)

  -- The bottom face, from H_[β,ℓ′] H_[j,α] X_[α,β] H_[j,α] H_[β,ℓ′] = M.
  bottom-from : ∀ {M : Word (Gen n)} → Hβℓ′ • Hjα • Xαβ • Hjα • Hβℓ′ ≈ M → Hjα • Xαβ ≈ (Hβℓ′ • M • Hβℓ′) • Hjα
  bottom-from {M} eq = sym (begin
    (Hβℓ′ • M • Hβℓ′) • Hjα                                  ≈⟨ cleft cright cleft sym eq ⟩
    (Hβℓ′ • (Hβℓ′ • Hjα • Xαβ • Hjα • Hβℓ′) • Hβℓ′) • Hjα    ≈⟨ by-assoc auto ⟩
    (Hβℓ′ • Hβℓ′) • Hjα • Xαβ • Hjα • (Hβℓ′ • Hβℓ′) • Hjα    ≈⟨ cong (H-H βℓ′) (cright cright cright cleft H-H βℓ′) ⟩
    ε • Hjα • Xαβ • Hjα • ε • Hjα                            ≈⟨ left-unit ⟩
    Hjα • Xαβ • Hjα • ε • Hjα                                ≈⟨ cright cright cright left-unit ⟩
    Hjα • Xαβ • Hjα • Hjα                                    ≈⟨ cright cright H-H jα ⟩
    Hjα • Xαβ • ε                                            ≈⟨ cright right-unit ⟩
    Hjα • Xαβ                                                ∎)

  -- The two paths, for Σ c ≡ 0 and Σ c ≡ δ (mod δ²), from (s) and (t).
  B₀ B₁ : Word (Gen n)
  B₀ = Hβℓ′ • (H j β jβ • H α ℓ′ αℓ′ • Xαβ • H α ℓ′ αℓ′ • H j β jβ) • Hβℓ′
  B₁ = Hβℓ′ • (H α β αβ • H j ℓ′ jℓ′ • X α ℓ′ αℓ′ • H j ℓ′ jℓ′ • H α β αβ) • Hβℓ′

  bottom₀ : Hjα • Xαβ ≈ B₀ • Hjα
  bottom₀ = bottom-from (Hs jα αβ βℓ′)

  bottom₁ : Hjα • Xαβ ≈ B₁ • Hjα
  bottom₁ = bottom-from (Ht jα αβ βℓ′)

  ----------------------------------------------------------------------
  -- The square, for a path B, with exponents f + z (at j), f (at α), g
  -- (at β) and m (at ℓ′), where g + z′ = f + z + 8

  module Hard (B : Word (Gen n)) (bottom : Hjα • Xαβ ≈ B • Hjα) (f z z′ m : ℕ) (z′≤8 : z′ ℕ.≤ 8) where

    g : ℕ
    g = f + z + (8 ∸ z′)

    Ds Dr Vs Vr G′ : Word (Gen n)
    Ds = ω j ^ (f + z) • ω α ^ f • ω β ^ g • ω ℓ′ ^ m
    Dr = ω j ^ (f + z) • ω α ^ g • ω β ^ f • ω ℓ′ ^ m
    Vs = (ω β ^ g • ω ℓ′ ^ m) • (ω j ^ f • ω α ^ f)
    Vr = (ω β ^ f • ω ℓ′ ^ m) • (ω j ^ g • ω α ^ g)
    G′ = Vr ⁻¹ • (B • Vs)

    g+z′ : g + z′ ≡ (f + z) + 8
    g+z′ = ≡.trans (ℕP.+-assoc (f + z) (8 ∸ z′) z′) (≡.cong ((f + z) +_) (ℕP.m∸n+n≡m z′≤8))

    face-s : Hjα • Ds ≈ Vs • (Hjα • ω j ^ z)
    face-s = face f z g m

    face-r : Hjα • Dr ≈ Vr • (Hjα • ω j ^ z′)
    face-r = trans (cright cleft trans (sym (ω^+8 (f + z))) (refl′ (≡.cong (ω j ^_) (≡.sym g+z′))))
                   (face g z′ f m)

    -- The normal edge from D_s s is H_[j,α]: V_s t = H_[j,α] D_s s.
    T₀-rel : Vs • (Hjα • ω j ^ z) ≈ Hjα • Ds
    T₀-rel = sym face-s

    rel : (Hjα • ω j ^ z′) • Xαβ ≈ G′ • (Hjα • ω j ^ z)
    rel = sym (begin
      (Vr ⁻¹ • (B • Vs)) • (Hjα • ω j ^ z)          ≈⟨ assoc ⟩
      Vr ⁻¹ • ((B • Vs) • (Hjα • ω j ^ z))          ≈⟨ cright assoc ⟩
      Vr ⁻¹ • (B • (Vs • (Hjα • ω j ^ z)))          ≈⟨ cright cright T₀-rel ⟩
      Vr ⁻¹ • (B • (Hjα • Ds))                      ≈⟨ cright sym assoc ⟩
      Vr ⁻¹ • ((B • Hjα) • Ds)                      ≈⟨ cright cleft sym bottom ⟩
      Vr ⁻¹ • ((Hjα • Xαβ) • Ds)                    ≈⟨ cright assoc ⟩
      Vr ⁻¹ • (Hjα • (Xαβ • Ds))                    ≈⟨ cright cright middle (f + z) f g m ⟩
      Vr ⁻¹ • (Hjα • (Dr • Xαβ))                    ≈⟨ cright sym assoc ⟩
      Vr ⁻¹ • ((Hjα • Dr) • Xαβ)                    ≈⟨ cright cleft face-r ⟩
      Vr ⁻¹ • ((Vr • (Hjα • ω j ^ z′)) • Xαβ)       ≈⟨ cright assoc ⟩
      Vr ⁻¹ • (Vr • ((Hjα • ω j ^ z′) • Xαβ))       ≈⟨ sym assoc ⟩
      (Vr ⁻¹ • Vr) • ((Hjα • ω j ^ z′) • Xαβ)       ≈⟨ cleft inverseˡ ⟩
      ε • ((Hjα • ω j ^ z′) • Xαβ)                  ≈⟨ left-unit ⟩
      (Hjα • ω j ^ z′) • Xαβ                        ∎)

    -- The powers of ω of V_s and V_r⁻¹ act on indices ≤ ℓ′.
    Vs-letters : Letters≤ ℓ′ Vs
    Vs-letters = (Letters≤-^ (ω β) (ℕP.<⇒≤ βℓ′) g , Letters≤-^ (ω ℓ′) ℕP.≤-refl m) ,
                 (Letters≤-^ (ω j) (ℕP.<⇒≤ jℓ′) f , Letters≤-^ (ω α) (ℕP.<⇒≤ αℓ′) f)

    Vr⁻¹-letters : Letters≤ ℓ′ (Vr ⁻¹)
    Vr⁻¹-letters = Letters≤-⁻¹ Vr
      ((Letters≤-^ (ω β) (ℕP.<⇒≤ βℓ′) f , Letters≤-^ (ω ℓ′) ℕP.≤-refl m) ,
       (Letters≤-^ (ω j) (ℕP.<⇒≤ jℓ′) g , Letters≤-^ (ω α) (ℕP.<⇒≤ αℓ′) g))
