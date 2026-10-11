------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma A.1: (d3) and (d4) at every tuple of distinct indices
-- (Clément, Appendix A.2)
--
-- "By proceeding similarly to the proofs of Equations (b1) to (b6), we
-- can rename the indices arbitrarily": the instances at the literals,
-- LemmaA1.D3 and LemmaA1.D4, are carried to any distinct indices by a
-- product of exchanges (LemmaA1.Rename.move), as (b1), (b4), (b6) are
-- in LemmaA1.Moves.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.General where

open import Data.Fin using (Fin)
open import Data.Product using (_,_)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup)
open import Data.Vec.Relation.Unary.All using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (_•_ ; _^_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₂₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics using (X ; H ; Xᵖ ; Hᵖ)
import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.Rename as Rename
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.Moves using (_⊢ᴳ_≈_ ; Wide ; wide ; fits)
import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.D3 as D3
import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.D4 as D4

private
  subst₄ : ∀ {A : Set} (P : A → A → A → A → Set) {a b c d a′ b′ c′ d′} →
           a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → P a b c d → P a′ b′ c′ d′
  subst₄ P Eq.refl Eq.refl Eq.refl Eq.refl p = p

  subst₆ : ∀ {A : Set} (P : A → A → A → A → A → A → Set) {a b c d e f a′ b′ c′ d′ e′ f′} →
           a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → e ≡ e′ → f ≡ f′ →
           P a b c d e f → P a′ b′ c′ d′ e′ f′
  subst₆ P Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl p = p

------------------------------------------------------------------------
-- (d3)

private
  d3′ : ∀ {N} → Wide 4 N → (a b c d : Fin N) →
        a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
        N ⊢ᴳ (H c d • H a c • H b d) ^ 4 ≈ H a b • H c d
  d3′ (wide m) a b c d ab ac ad bc bd cd =
    subst₄ (λ p q r s → ₄₊ m ⊢ᴳ (H r s • H p r • H q s) ^ 4 ≈ H p q • H r s)
      (ok ₀) (ok ₁) (ok ₂) (ok ₃)
      (move ts (w , w , w , w) (Hᵖ (λ ()) , Hᵖ (λ ())) (D3.d3₀ m))
    where
    open Rename (₄₊ m)
    ls is : Vec (Fin (₄₊ m)) 4
    ls = ₀ ∷ ₁ ∷ ₂ ∷ ₃ ∷ []
    is = a ∷ b ∷ c ∷ d ∷ []
    ts = build ls is
    ok : ∀ j → σ ts (lookup ls j) ≡ lookup is j
    ok = build-ok ls is
           (((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ᵈ (((λ ()) ∷ (λ ()) ∷ []) ∷ᵈ
             (((λ ()) ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ))))
           ((ab ∷ ac ∷ ad ∷ []) ∷ᵈ ((bc ∷ bd ∷ []) ∷ᵈ ((cd ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ))))
    w = Hᵖ (λ ()) , Hᵖ (λ ()) , Hᵖ (λ ())

d3 : ∀ {N} {a b c d : Fin N} → a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
     N ⊢ᴳ (H c d • H a c • H b d) ^ 4 ≈ H a b • H c d
d3 {N} {a} {b} {c} {d} ab ac ad bc bd cd =
  d3′ (fits (a ∷ b ∷ c ∷ d ∷ [])
            ((ab ∷ ac ∷ ad ∷ []) ∷ᵈ ((bc ∷ bd ∷ []) ∷ᵈ ((cd ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ)))))
      a b c d ab ac ad bc bd cd
  where open Rename N using (_∷ᵈ_ ; []ᵈ)

------------------------------------------------------------------------
-- (d4)

private
  d4′ : ∀ {N} → Wide 6 N → (a b c d e f : Fin N) →
        a ≢ b → a ≢ c → a ≢ d → a ≢ e → a ≢ f → b ≢ c → b ≢ d → b ≢ e → b ≢ f →
        c ≢ d → c ≢ e → c ≢ f → d ≢ e → d ≢ f → e ≢ f →
        N ⊢ᴳ (H a c • H b d • H a b • H a c • H b d • X c e • X d f) ^ 3 ≈
             H c e • H d f • H e f • H c e • H d f • X c e • X d f
  d4′ (wide m) a b c d e f ab ac ad ae af bc bd be bf cd ce cf de df ef =
    subst₆ (λ p q r s t u → ₂₊ (₄₊ m) ⊢ᴳ
              (H p r • H q s • H p q • H p r • H q s • X r t • X s u) ^ 3 ≈
              H r t • H s u • H t u • H r t • H s u • X r t • X s u)
      (ok ₀) (ok ₁) (ok ₂) (ok ₃) (ok ₄) (ok ₅)
      (move ts (w , w , w) (Hᵖ (λ ()) , Hᵖ (λ ()) , Hᵖ (λ ()) , Hᵖ (λ ()) , Hᵖ (λ ()) ,
                            Xᵖ (λ ()) , Xᵖ (λ ()))
            (D4.d4₀ m))
    where
    open Rename (₂₊ (₄₊ m))
    ls is : Vec (Fin (₂₊ (₄₊ m))) 6
    ls = ₀ ∷ ₁ ∷ ₄ ∷ ₅ ∷ ₂ ∷ ₃ ∷ []
    is = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []
    ts = build ls is
    ok : ∀ j → σ ts (lookup ls j) ≡ lookup is j
    ok = build-ok ls is
           (((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ᵈ
            (((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ᵈ
             (((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ᵈ
              (((λ ()) ∷ (λ ()) ∷ []) ∷ᵈ (((λ ()) ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ))))))
           ((ab ∷ ac ∷ ad ∷ ae ∷ af ∷ []) ∷ᵈ ((bc ∷ bd ∷ be ∷ bf ∷ []) ∷ᵈ
             ((cd ∷ ce ∷ cf ∷ []) ∷ᵈ ((de ∷ df ∷ []) ∷ᵈ ((ef ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ))))))
    w = Hᵖ (λ ()) , Hᵖ (λ ()) , Hᵖ (λ ()) , Hᵖ (λ ()) , Hᵖ (λ ()) , Xᵖ (λ ()) , Xᵖ (λ ())

d4 : ∀ {N} {a b c d e f : Fin N} →
     a ≢ b → a ≢ c → a ≢ d → a ≢ e → a ≢ f → b ≢ c → b ≢ d → b ≢ e → b ≢ f →
     c ≢ d → c ≢ e → c ≢ f → d ≢ e → d ≢ f → e ≢ f →
     N ⊢ᴳ (H a c • H b d • H a b • H a c • H b d • X c e • X d f) ^ 3 ≈
          H c e • H d f • H e f • H c e • H d f • X c e • X d f
d4 {N} {a} {b} {c} {d} {e} {f} ab ac ad ae af bc bd be bf cd ce cf de df ef =
  d4′ (fits (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])
            ((ab ∷ ac ∷ ad ∷ ae ∷ af ∷ []) ∷ᵈ ((bc ∷ bd ∷ be ∷ bf ∷ []) ∷ᵈ
              ((cd ∷ ce ∷ cf ∷ []) ∷ᵈ ((de ∷ df ∷ []) ∷ᵈ ((ef ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ)))))))
      a b c d e f ab ac ad ae af bc bd be bf cd ce cf de df ef
  where open Rename N using (_∷ᵈ_ ; []ᵈ)
