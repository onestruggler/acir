------------------------------------------------------------------------
-- Presentations of groups
--
-- The scaled four-state auxiliary presentation at any positive half
-- dimension.  The explicit pair of levels lets circuit clients retain
-- the definitionally even dimension used by their physical semantics.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; zero ; suc ; _*_ ; _<_)
open import Data.Fin.Base using (Fin ; toℕ)

module Examples.Groups.CCX+H.GeneralN.PresentationAt
  (k : ℕ) (positive : 0 < k)
  (a b : Fin (k * 2)) .(a<b : toℕ a < toℕ b) where

open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Presentation.GroupLike using (Grouplike)
import Presentation.Base as PB
import Examples.Groups.CCX+HH-TwoLevel.Derived as UD
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as Sem
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness as Complete
import Examples.Groups.CCX+HH.Subgroup.Schreier as Schreier
open import Examples.Groups.CCX+H.GeneralN.Action

N : ℕ
N = k * 2

open At N public using (state ; state-relations ; state-cong)

source-grouplike : Grouplike (T._===ᴸ_ {N})
source-grouplike T.⌊ g ⌋ = [ T.⌊ g ⌋ ]ʷ , T.⌊⌋-cong (UD.gen-gen g)
source-grouplike T.IH = T.H , PB.axiom T.r7a

rep : Coset → Word (T.Genᴸ N)
rep c00 = ε
rep c10 = T.Mᴸ a
rep c11 = T.Xᴸ a b a<b
rep c01 = T.Mᴸ a • T.Xᴸ a b a<b

rep-state : ∀ c → state c00 (rep c) ≡ c
rep-state c00 = Eq.refl
rep-state c10 = Eq.refl
rep-state c11 = Eq.refl
rep-state c01 = Eq.refl

module Theory = Schreier (T._===ᴸ_ {N}) source-grouplike c00
  step state-relations rep PB.refl rep-state

open Theory public using
  (Edge ; e ; encode ; decode ; _===_ ; _≈_ ; roundtrip ; translated
  ; encode-injective ; encode-cong ; encode-closed ; edge-closed
  ; factor-word ; decode-loop ; grouplike)

private
  module M = Sem.Dim k

  source-complete : ∀ m → 0 < m → ∀ {u v : Word (T.Genᴸ (m * 2))} →
    Sem.Dim.⟦_⟧ᴸ m u ≡ Sem.Dim.⟦_⟧ᴸ m v → PB._≈_ T._===ᴸ_ u v
  source-complete zero ()
  source-complete (suc m) p = Complete.completeness m

completeness : ∀ {u v : Word Edge} →
  M.⟦ encode u ⟧ᴸ ≡ M.⟦ encode v ⟧ᴸ → u ≈ v
completeness {u} {v} eq = encode-injective
  (source-complete k positive {encode u} {encode v} eq)

soundness : ∀ {u v : Word Edge} → u ≈ v →
  M.⟦ encode u ⟧ᴸ ≡ M.⟦ encode v ⟧ᴸ
soundness eq = Sem.soundness k (encode-cong eq)

state-semantic : ∀ c {u v : Word (T.Genᴸ N)} →
  M.⟦ u ⟧ᴸ ≡ M.⟦ v ⟧ᴸ → state c u ≡ state c v
state-semantic c {u} {v} eq = state-cong c
  (source-complete k positive {u} {v} eq)

stabilizer-generated : ∀ w → state c00 w ≡ c00 →
  M.⟦ encode (decode c00 w) ⟧ᴸ ≡ M.⟦ w ⟧ᴸ
stabilizer-generated w closed = Sem.soundness k (decode-loop {w} closed)
