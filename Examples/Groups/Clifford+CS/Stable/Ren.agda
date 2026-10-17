------------------------------------------------------------------------
-- Presentations of groups
--
-- Renaming words over P′ from 4 + m wires to 5 + m
--
-- Five.Ren at every width: an injective map σ that keeps the order of
-- the indices renames every letter of P′ (`renX`; the orderings a < b go
-- along) and every gadget (`renG`), and the decomposition of a letter
-- into gadgets (Five.Decode) commutes with the renaming (`gl-ren`,
-- `GL-ren`): its case splits compare indices, and σ keeps the
-- comparisons.  The two halves of the Gray numbering are such maps
-- (Stable.GrayHalves).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin using (Fin ; _<_)
open import Data.Nat using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.Clifford+CS.Encoding as Encoding

module Examples.Groups.Clifford+CS.Stable.Ren
  (m : ℕ)
  (σ : Fin (Encoding.N m) → Fin (Encoding.N (suc m)))
  (σ-inj : ∀ {a b} → σ a ≡ σ b → a ≡ b)
  (σ-mono : ∀ {a b} → a < b → σ a < σ b)
  where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.List.Properties using (map-++)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; ki)
import Examples.Groups.Clifford+CS.Five.Decode m as D0
import Examples.Groups.Clifford+CS.Five.Decode (suc m) as D1

------------------------------------------------------------------------
-- Letters, words and gadgets

renX : GenP (Encoding.N m) → GenP (Encoding.N (suc m))
renX (pp a b)         = pp (σ a) (σ b)
renX (px c a b p)     = px (σ c) (σ a) (σ b) (σ-mono p)
renX (dx a b c d p q) = dx (σ a) (σ b) (σ c) (σ d) (σ-mono p) (σ-mono q)
renX (ki a b s p)     = ki (σ a) (σ b) (σ s) (σ-mono p)

renʷ : Word (GenP (Encoding.N m)) → Word (GenP (Encoding.N (suc m)))
renʷ = (λ x → [ renX x ]ʷ) ʷ

renG : D0.Gd → D1.Gd
renG (D0.gd V a b) = D1.gd V (σ a) (σ b)

------------------------------------------------------------------------
-- The decomposition commutes with the renaming

private
  ppL-ren : ∀ a b (e : Dec (a ≡ b)) (e′ : Dec (σ a ≡ σ b)) →
            D1.ppL (σ a) (σ b) e′ ≡ map renG (D0.ppL a b e)
  ppL-ren a b (yes _)  (yes _)  = refl
  ppL-ren a b (yes ab) (no ne)  = ⊥-elim (ne (Eq.cong σ ab))
  ppL-ren a b (no ne)  (yes ab) = ⊥-elim (ne (σ-inj ab))
  ppL-ren a b (no _)   (no _)   = refl

  pxL-ren : ∀ c a b (e₁ : Dec (c ≡ a)) (e₂ : Dec (c ≡ b))
            (e₁′ : Dec (σ c ≡ σ a)) (e₂′ : Dec (σ c ≡ σ b)) →
            D1.pxL (σ c) (σ a) (σ b) e₁′ e₂′ ≡ map renG (D0.pxL c a b e₁ e₂)
  pxL-ren c a b (yes _)  _        (yes _)  _        = refl
  pxL-ren c a b (yes ca) _        (no ne)  _        = ⊥-elim (ne (Eq.cong σ ca))
  pxL-ren c a b (no ne)  _        (yes ca) _        = ⊥-elim (ne (σ-inj ca))
  pxL-ren c a b (no _)   (yes _)  (no _)   (yes _)  = refl
  pxL-ren c a b (no _)   (yes cb) (no _)   (no ne)  = ⊥-elim (ne (Eq.cong σ cb))
  pxL-ren c a b (no _)   (no ne)  (no _)   (yes cb) = ⊥-elim (ne (σ-inj cb))
  pxL-ren c a b (no _)   (no _)   (no _)   (no _)   = refl

  kiL-ren : ∀ a b s (e : Dec (s ≡ a)) (e′ : Dec (σ s ≡ σ a)) →
            D1.kiL (σ a) (σ b) (σ s) e′ ≡ map renG (D0.kiL a b s e)
  kiL-ren a b s (yes _)  (yes _)  = refl
  kiL-ren a b s (yes sa) (no ne)  = ⊥-elim (ne (Eq.cong σ sa))
  kiL-ren a b s (no ne)  (yes sa) = ⊥-elim (ne (σ-inj sa))
  kiL-ren a b s (no _)   (no _)   = refl

gl-ren : ∀ x → D1.gl (renX x) ≡ map renG (D0.gl x)
gl-ren (pp a b)         = ppL-ren a b (a ≟ b) (σ a ≟ σ b)
gl-ren (px c a b _)     = pxL-ren c a b (c ≟ a) (c ≟ b) (σ c ≟ σ a) (σ c ≟ σ b)
gl-ren (dx a b c d _ _) =
  Eq.cong (D1.gd _ (σ a) (σ b) ∷_) (pxL-ren b c d (b ≟ c) (b ≟ d) (σ b ≟ σ c) (σ b ≟ σ d))
gl-ren (ki a b s _)     = kiL-ren a b s (s ≟ a) (σ s ≟ σ a)

GL-ren : ∀ u → D1.GL (renʷ u) ≡ map renG (D0.GL u)
GL-ren [ x ]ʷ  = gl-ren x
GL-ren ε       = refl
GL-ren (u • v) =
  Eq.trans (Eq.cong₂ _++_ (GL-ren u) (GL-ren v)) (Eq.sym (map-++ renG (D0.GL u) (D0.GL v)))
