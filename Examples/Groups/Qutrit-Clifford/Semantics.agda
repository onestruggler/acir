------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics of qutrit Clifford circuits (Definitions 2.1
-- and 2.4 of the paper), and its soundness
--
-- The gates have entries in ℤ[1/3, ω], ω = e^{2πi/3}.  They are read in
-- ℤ[ζ] = ℤ[x]/(x⁴ − x² + 1), ζ = x = e^{iπ/6}, with the factor 1/√3 of
-- H taken out, as the scaled values of Examples.Independence: a value
-- (h , M) is M / √3^h, √3 = 2ζ − ζ³, and values are compared exactly
-- (Scaled.Phases at the phases x^0 only).  So ω = ζ⁴, −ω = ζ^10, and
-- since ω² − ω = −i√3 and i = ζ³,
--
--   H = (ω² − ω)⁻¹ [ω^{jk}]  is  (1 , ζ³ [ω^{jk}]),
--   S = diag(ω , ω , 1),     CZ = diag(ω^{xy}),     −ω = ζ^10.
--
-- A basis vector lists its digits wire 0 first, and CZ's matrix is
-- symmetric in its two wires.  A word is in operator order, so it is
-- read as the product of its letters in the opposite (diagram) order of
-- Scaled's _∙_: ⟦ w • v ⟧ = ⟦ v ⟧ ∙ ⟦ w ⟧.
--
-- Soundness: each rule of Figure 1 is checked by evaluation on its own
-- wires; a gate on the bottom wires of a wider circuit is its matrix
-- tensored with the identity, and shifting commutes with reading, so
-- the rules hold at every width, and the structural rules are the
-- tensor calculus.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Qutrit-Clifford.Semantics where

open import Algebra.Bundles using (Monoid)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
import Presentation.Base as PB

open import Examples.Independence.Semantics.Qutrit public
  using (module Zζ ; √3 ; √3-cancel ; ζ¹²≡1)
open import Data.Integer.Base using (+_ ; -[1+_])
open import Examples.Independence.Semantics.Scaled 3 (+ 1) (-[1+ 0 ]) √3 √3-cancel 11 ζ¹²≡1 public
  renaming (_^_ to _^q_)

open import Examples.Groups.Qutrit-Clifford.Syntactics

private
  variable
    k n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The gates

private
  -- Addition and multiplication modulo 3.
  _⊞_ : Fin 3 → Fin 3 → Fin 3
  zero           ⊞ b              = b
  suc zero       ⊞ zero           = suc zero
  suc zero       ⊞ suc zero       = suc (suc zero)
  suc zero       ⊞ suc (suc zero) = zero
  suc (suc zero) ⊞ zero           = suc (suc zero)
  suc (suc zero) ⊞ suc zero       = zero
  suc (suc zero) ⊞ suc (suc zero) = suc zero

  _⊠_ : Fin 3 → Fin 3 → Fin 3
  zero           ⊠ _ = zero
  suc zero       ⊠ b = b
  suc (suc zero) ⊠ b = b ⊞ b

  -- ω^j = ζ^{4 j}.
  ω^ : Fin 3 → Q
  ω^ zero             = 1#
  ω^ (suc zero)       = x ^q 4
  ω^ (suc (suc zero)) = x ^q 8

  -- The phase of S on |b⟩.
  sph : Fin 3 → Q
  sph (suc (suc zero)) = 1#
  sph _                = x ^q 4

νᵍ : Sc 0
νᵍ = 0 , mat (x ^q 10)

Hᵍ Sᵍ : Sc 1
Hᵍ = 1 , matOf λ { (a ∷ []) (b ∷ []) → x ^q 3 * ω^ (a ⊠ b) }
Sᵍ = 0 , matOf λ { (a ∷ []) (b ∷ []) → δ₁ a b * sph b }

CZᵍ : Sc 2
CZᵍ = 0 , matOf λ { (a₀ ∷ a₁ ∷ []) (b₀ ∷ b₁ ∷ []) →
                    δ₁ a₀ b₀ * (δ₁ a₁ b₁ * ω^ (b₀ ⊠ b₁)) }

val : Gate k → Sc k
val ν-gate  = νᵍ
val H-gate  = Hᵍ
val S-gate  = Sᵍ
val CZ-gate = CZᵍ

------------------------------------------------------------------------
-- Reading circuits

⟦_⟧₀ : Gen n → Sc n
⟦ gate₀ g ⟧₀ = proj₁ (val g) , scalM (entries (proj₂ (val g)))
⟦ gate₁ g ⟧₀ = embs (val g)
⟦ gate₂ g ⟧₀ = embs (val g)
⟦ g ↥ ⟧₀     = ↑s ⟦ g ⟧₀

⟦_⟧ : Circuit n → Sc n
⟦ [ g ]ʷ ⟧ = ⟦ g ⟧₀
⟦ ε ⟧      = εs
⟦ w • v ⟧  = ⟦ v ⟧ ∙ ⟦ w ⟧

------------------------------------------------------------------------
-- Exact comparison

open Phases (λ k → k ≡ 0) refl (λ { refl refl → refl }) (λ { refl → ℕP.*-zeroʳ 11 }) public
open Decide (λ k → k ≡ 0) refl (λ { refl refl → refl }) (λ { refl → ℕP.*-zeroʳ 11 }) public

private
  ≈-trans' : {s₁ s₂ s₃ : Sc n} → s₁ ≈ s₂ → s₂ ≈ s₃ → s₁ ≈ s₃
  ≈-trans' {s₁ = s₁} {s₂} {s₃} = ≈-trans {s₁ = s₁} {s₂} {s₃}

  ≈-sym' : {s s' : Sc n} → s ≈ s' → s' ≈ s
  ≈-sym' {s = s} {s'} = ≈-sym {s = s} {s'}

------------------------------------------------------------------------
-- Localisation

⟦↧⟧₀ : (g : Gen k) (n : ℕ) → ⟦ g ↧ᵏ n ⟧₀ ≈ embs {k} {n} ⟦ g ⟧₀
⟦↧⟧₀ {k} (gate₀ g) n =
  ≐→≈ {s = ⟦ gate₀ {k +ℕ n} g ⟧₀} {embs {k} {n} ⟦ gate₀ g ⟧₀} refl
    (≐-trans (ix-scalM {k +ℕ n} c)
    (≐-trans (scal-emb {k} {n} c)
    (≐-trans (emb-cong {k} {n} (≐-sym (ix-scalM {k} c)))
             (≐-sym (ix-emb {k} {n} (scalM c))))))
  where c = entries (proj₂ (val g))
⟦↧⟧₀ {suc k} (gate₁ g) n =
  ≐→≈ {s = ⟦ gate₁ {k +ℕ n} g ⟧₀} {embs {suc k} {n} ⟦ gate₁ g ⟧₀} refl
    (≐-trans (ix-emb {1} {k +ℕ n} M)
    (≐-trans (emb-pad₁ {k} {n} (ix M))
    (≐-trans (emb-cong {suc k} {n} (≐-sym (ix-emb {1} {k} M)))
             (≐-sym (ix-emb {suc k} {n} (tenM M (idM {k})))))))
  where M = proj₂ (val g)
⟦↧⟧₀ {suc (suc k)} (gate₂ g) n =
  ≐→≈ {s = ⟦ gate₂ {k +ℕ n} g ⟧₀} {embs {suc (suc k)} {n} ⟦ gate₂ g ⟧₀} refl
    (≐-trans (ix-emb {2} {k +ℕ n} M)
    (≐-trans (emb-pad₂ {k} {n} (ix M))
    (≐-trans (emb-cong {suc (suc k)} {n} (≐-sym (ix-emb {2} {k} M)))
             (≐-sym (ix-emb {suc (suc k)} {n} (tenM M (idM {k})))))))
  where M = proj₂ (val g)
⟦↧⟧₀ {suc k} (g ↥) n =
  ≈-trans' {s₁ = ↑s ⟦ g ↧ᵏ n ⟧₀} {↑s (embs {k} {n} ⟦ g ⟧₀)} {embs {suc k} {n} (↑s ⟦ g ⟧₀)}
    (↑s-cong {s = ⟦ g ↧ᵏ n ⟧₀} {embs {k} {n} ⟦ g ⟧₀} (⟦↧⟧₀ g n))
    (≐→≈ {s = ↑s (embs {k} {n} ⟦ g ⟧₀)} {embs {suc k} {n} (↑s ⟦ g ⟧₀)} refl
      (≐-trans (ix-up (tenM G (idM {n})))
      (≐-trans (up-cong (ix-emb {k} {n} G))
      (≐-trans (up-emb {k} {n} (ix G))
      (≐-trans (emb-cong {suc k} {n} (≐-sym (ix-up G)))
               (≐-sym (ix-emb {suc k} {n} (tenM (idM {1}) G))))))))
  where G = proj₂ ⟦ g ⟧₀

⟦↓⟧ : (w : Circuit k) (n : ℕ) → ⟦ w ↓ᵏ n ⟧ ≈ embs {k} {n} ⟦ w ⟧
⟦↓⟧ [ g ]ʷ  n = ⟦↧⟧₀ g n
⟦↓⟧ {k} ε   n = ≈-sym' {s = embs {k} {n} εs} {εs} (embs-ε {k} {n})
⟦↓⟧ {k} (w • v) n =
  ≈-trans' {s₁ = ⟦ v ↓ᵏ n ⟧ ∙ ⟦ w ↓ᵏ n ⟧} {embs {k} {n} ⟦ v ⟧ ∙ embs ⟦ w ⟧}
           {embs {k} {n} (⟦ v ⟧ ∙ ⟦ w ⟧)}
    (∙-cong {s₁ = ⟦ v ↓ᵏ n ⟧} {embs {k} {n} ⟦ v ⟧} {⟦ w ↓ᵏ n ⟧} {embs {k} {n} ⟦ w ⟧}
            (⟦↓⟧ v n) (⟦↓⟧ w n))
    (≈-sym' {s = embs {k} {n} (⟦ v ⟧ ∙ ⟦ w ⟧)} {embs {k} {n} ⟦ v ⟧ ∙ embs ⟦ w ⟧}
            (embs-∙ {k} {n} ⟦ v ⟧ ⟦ w ⟧))

-- The same, for the circuit spelled at the wider width: the two are
-- compared as words, which is cheap, rather than as values.
⟦↓≡⟧ : (w : Circuit k) {n : ℕ} {w' : Circuit (k +ℕ n)} → w ↓ᵏ n ≡ w' →
       ⟦ w' ⟧ ≈ embs {k} {n} ⟦ w ⟧
⟦↓≡⟧ w {n} refl = ⟦↓⟧ w n

⟦↑⟧ : (w : Circuit n) → ⟦ w ↑ ⟧ ≈ ↑s ⟦ w ⟧
⟦↑⟧ [ g ]ʷ  = ≈-refl {s = ↑s ⟦ g ⟧₀}
⟦↑⟧ {n} ε   = ≈-sym' {s = ↑s (εs {n})} {εs} (↑s-ε {n})
⟦↑⟧ (w • v) =
  ≈-trans' {s₁ = ⟦ v ↑ ⟧ ∙ ⟦ w ↑ ⟧} {↑s ⟦ v ⟧ ∙ ↑s ⟦ w ⟧} {↑s (⟦ v ⟧ ∙ ⟦ w ⟧)}
    (∙-cong {s₁ = ⟦ v ↑ ⟧} {↑s ⟦ v ⟧} {⟦ w ↑ ⟧} {↑s ⟦ w ⟧} (⟦↑⟧ v) (⟦↑⟧ w))
    (≈-sym' {s = ↑s (⟦ v ⟧ ∙ ⟦ w ⟧)} {↑s ⟦ v ⟧ ∙ ↑s ⟦ w ⟧} (↑s-∙ ⟦ v ⟧ ⟦ w ⟧))

-- An equation on k wires holds on the bottom wires of k + n.
lift : (l r : Circuit k) {n : ℕ} {w v : Circuit (k +ℕ n)} →
       l ↓ᵏ n ≡ w → r ↓ᵏ n ≡ v → ⟦ l ⟧ ≈ ⟦ r ⟧ → ⟦ w ⟧ ≈ ⟦ v ⟧
lift {k} l r {n} {w} {v} el er e =
  ≈-trans' {s₁ = ⟦ w ⟧} {embs {k} {n} ⟦ l ⟧} {⟦ v ⟧} (⟦↓≡⟧ l el)
    (≈-trans' {s₁ = embs {k} {n} ⟦ l ⟧} {embs {k} {n} ⟦ r ⟧} {⟦ v ⟧}
      (embs-cong {k} {n} {s = ⟦ l ⟧} {⟦ r ⟧} e)
      (≈-sym' {s = ⟦ v ⟧} {embs {k} {n} ⟦ r ⟧} (⟦↓≡⟧ r er)))

------------------------------------------------------------------------
-- The structural rules of Circuit.Base

cong↑-sound : ⟦ w ⟧ ≈ ⟦ v ⟧ → ⟦ w ↑ ⟧ ≈ ⟦ v ↑ ⟧
cong↑-sound {w = w} {v} e =
  ≈-trans' {s₁ = ⟦ w ↑ ⟧} {↑s ⟦ w ⟧} {⟦ v ↑ ⟧} (⟦↑⟧ w)
    (≈-trans' {s₁ = ↑s ⟦ w ⟧} {↑s ⟦ v ⟧} {⟦ v ↑ ⟧}
      (↑s-cong {s = ⟦ w ⟧} {⟦ v ⟧} e)
      (≈-sym' {s = ⟦ v ↑ ⟧} {↑s ⟦ v ⟧} (⟦↑⟧ v)))

comm₁-sound : (h : Gate 1) (g : Gen n) →
              ⟦ [ gate₁ h ]ʷ • [ g ↥ ]ʷ ⟧ ≈ ⟦ [ g ↥ ]ʷ • [ gate₁ h ]ʷ ⟧
comm₁-sound {n} h g =
  ≐→≈ {s = ↑s ⟦ g ⟧₀ ∙ embs (val h)} {embs (val h) ∙ ↑s ⟦ g ⟧₀}
      (ℕP.+-comm (proj₁ ⟦ g ⟧₀) (proj₁ (val h)))
    (≐-trans (ix-mul E U)
    (≐-trans (⊙-cong (ix-emb {1} {n} V) (ix-up G))
    (≐-trans (emb-up-comm {1} {n} (ix V) (ix G))
    (≐-trans (⊙-cong (≐-sym (ix-up G)) (≐-sym (ix-emb {1} {n} V)))
             (≐-sym (ix-mul U E))))))
  where
  V = proj₂ (val h)
  G = proj₂ ⟦ g ⟧₀
  E = tenM V (idM {n})
  U = tenM (idM {1}) G

comm₂-sound : (h : Gate 2) (g : Gen n) →
              ⟦ [ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ ⟧ ≈ ⟦ [ g ↥ ↥ ]ʷ • [ gate₂ h ]ʷ ⟧
comm₂-sound {n} h g =
  ≐→≈ {s = ↑s (↑s ⟦ g ⟧₀) ∙ embs (val h)} {embs (val h) ∙ ↑s (↑s ⟦ g ⟧₀)}
      (ℕP.+-comm (proj₁ ⟦ g ⟧₀) (proj₁ (val h)))
    (≐-trans (ix-mul E U)
    (≐-trans (⊙-cong (ix-emb {2} {n} V) UU)
    (≐-trans (emb-up-comm {2} {n} (ix V) (ix G))
    (≐-trans (⊙-cong (≐-sym UU) (≐-sym (ix-emb {2} {n} V)))
             (≐-sym (ix-mul U E))))))
  where
  V = proj₂ (val h)
  G = proj₂ ⟦ g ⟧₀
  E = tenM V (idM {n})
  U = tenM (idM {1}) (tenM (idM {1}) G)
  UU : ix U ≐ upk 2 (ix G)
  UU = ≐-trans (ix-up (tenM (idM {1}) G))
         (≐-trans (up-cong (ix-up G)) (up-up (ix G)))

ω↑=ω-sound : (h : Gate 0) → ⟦ [ gate₀ {n} h ]ʷ ↑ ⟧ ≈ ⟦ [ gate₀ h ]ʷ ⟧
ω↑=ω-sound {n} h =
  ≐→≈ {s = ↑s ⟦ gate₀ {n} h ⟧₀} {⟦ gate₀ {suc n} h ⟧₀} refl
    (≐-trans (ix-up (scalM c))
    (≐-trans (up-cong (ix-scalM {n} c))
    (≐-trans (up-scal c) (≐-sym (ix-scalM {suc n} c)))))
  where c = entries (proj₂ (val h))

------------------------------------------------------------------------
-- The rules of Figure 1, by evaluation on their own wires

rule-sound : n QRel, w === v → ⟦ w ⟧ ≈ ⟦ v ⟧
rule-sound C₁  = lift {0} (ν ^ 6) ε refl refl (check 0 refl _ _ tt)
rule-sound C₂  = lift {1} (H ^ 4) ε refl refl (check 0 refl _ _ tt)
rule-sound C₃  = lift {1} (S ^ 3) ε refl refl (check 0 refl _ _ tt)
rule-sound C₄  = lift {1} (H • S • S • H • S • S • H • S • S) ν refl refl (check 0 refl _ _ tt)
rule-sound C₅  = lift {1} (S′ • S) (S • S′) refl refl (check 0 refl _ _ tt)
rule-sound C₆  = lift {2} (CZ ^ 3) ε refl refl (check 0 refl _ _ tt)
rule-sound C₇  = lift {2} (SWAP • SWAP) ε refl refl (check 0 refl _ _ tt)
rule-sound C₈  = lift {2} (CZ • S ↑) (S ↑ • CZ) refl refl (check 0 refl _ _ tt)
rule-sound C₉  = lift {2} (CZ • CZ • H ↑ • H ↑) (H ↑ • H ↑ • CZ) refl refl (check 0 refl _ _ tt)
rule-sound C₁₀ = lift {2} (SWAP • S ↑) (S • SWAP) refl refl (check 0 refl _ _ tt)
rule-sound C₁₁ = lift {2} (SWAP • H ↑) (H • SWAP) refl refl (check 0 refl _ _ tt)
rule-sound C₁₂ = lift {2} (SWAP • CZ) (CZ • SWAP) refl refl (check 0 refl _ _ tt)
rule-sound C₁₃ = lift {2} (XC • S ↑) (ωˢ • ωˢ • S′ • S ↑ • CZ • XC) refl refl (check 0 refl _ _ tt)
rule-sound C₁₄ = lift {2} (XC • CZ) (ωˢ • S • S′ • CZ • XC) refl refl (check 0 refl _ _ tt)
rule-sound C₁₅ = lift {3} (CZ ↑ • CZ) (CZ • CZ ↑) refl refl (check 0 refl _ _ tt)
rule-sound C₁₆ = lift {3} (SWAP ↑ • SWAP • SWAP ↑) (SWAP • SWAP ↑ • SWAP) refl refl (check 0 refl _ _ tt)
rule-sound C₁₇ = lift {3} (SWAP • SWAP ↑ • CZ) (CZ ↑ • SWAP • SWAP ↑) refl refl (check 0 refl _ _ tt)
rule-sound C₁₈ = lift {3} (CZ • CX ↑) (CZ₀₂ • CX ↑ • CZ) refl refl (check 0 refl _ _ tt)

------------------------------------------------------------------------
-- Soundness

vrel-sound : n VRel, w === v → ⟦ w ⟧ ≈ ⟦ v ⟧
vrel-sound (srel r)                  = rule-sound r
vrel-sound (cong↑ {w = w} {v = v} a) = cong↑-sound {w = w} {v} (vrel-sound a)
vrel-sound (comm₁ h g)               = ≈-sym' {s = ⟦ [ gate₁ h ]ʷ • [ g ↥ ]ʷ ⟧}
                                         {⟦ [ g ↥ ]ʷ • [ gate₁ h ]ʷ ⟧} (comm₁-sound h g)
vrel-sound (comm₂ h g)               = ≈-sym' {s = ⟦ [ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ ⟧}
                                         {⟦ [ g ↥ ↥ ]ʷ • [ gate₂ h ]ʷ ⟧} (comm₂-sound h g)
vrel-sound (ω↑=ω h)                  = ω↑=ω-sound h

-- Every derivable equation holds.
sound : n ⊢ w ≈ v → ⟦ w ⟧ ≈ ⟦ v ⟧
sound {w = w} PB.refl          = ≈-refl {s = ⟦ w ⟧}
sound {w = w} {v} (PB.sym e)   = ≈-sym' {s = ⟦ v ⟧} {⟦ w ⟧} (sound e)
sound {w = w} {v} (PB.trans {v = u} e f) =
  ≈-trans' {s₁ = ⟦ w ⟧} {⟦ u ⟧} {⟦ v ⟧} (sound e) (sound f)
sound (PB.cong {w = w} {w' = w'} {v = v} {v' = v'} e f) =
  ∙-cong {s₁ = ⟦ v ⟧} {⟦ v' ⟧} {⟦ w ⟧} {⟦ w' ⟧} (sound f) (sound e)
sound (PB.assoc {w = w} {v = v} {u = u}) =
  ≈-sym' {s = (⟦ u ⟧ ∙ ⟦ v ⟧) ∙ ⟦ w ⟧} {⟦ u ⟧ ∙ (⟦ v ⟧ ∙ ⟦ w ⟧)}
    (Monoid.assoc (monoid _) ⟦ u ⟧ ⟦ v ⟧ ⟦ w ⟧)
sound (PB.left-unit {w = w})  = proj₂ (Monoid.identity (monoid _)) ⟦ w ⟧
sound (PB.right-unit {w = w}) = proj₁ (Monoid.identity (monoid _)) ⟦ w ⟧
sound (PB.axiom a)            = vrel-sound a
