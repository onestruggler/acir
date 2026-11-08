{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.DecodingMatrices where

open import Data.Nat.Base as ℕ using (ℕ ; suc ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Matrix using (⟦_⟧ᴹ ; matrix-• ; matrix-ε ; matrix-sound)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Encoding using (decode)
import Examples.Groups.CCX+HH-3qubit.Repaired.EncodingMatrices as EM
import Examples.Groups.CCX+HH-3qubit.FrameWords as F
import Examples.Groups.CCX+HH-3qubit.TwoLevel as TwoLevel
import Presentation.Base as PB
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1
open import Examples.Groups.CCX+HH-TwoLevel.Reduction {8} using () renaming (sound-act to sound-act₁)
import Examples.Groups.CCX+HH-TwoLevel.Conjugation {8} as Conj
  using (Basic ; size ; decompose ; Step ; module Step)
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SS
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R
module Dim = SS.Dim 4
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.M0 as CM0
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X01 as CX01
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X12 as CX12
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X23 as CX23
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X34 as CX34
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X45 as CX45
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X56 as CX56
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.X67 as CX67
import Examples.Groups.CCX+HH-3qubit.DecodeMatrices.K0123 as CK0123

-- The basic letters, from their matrix certificates.
basic : ∀ g → Conj.Basic g → Dim.⟦ [ L.⌊ g ⌋ ]ʷ ⟧ᴸ ≡ ⟦ F.decode g ⟧ᴹ
basic (T.M-gen (zero)) _ = CM0.proved
basic (T.M-gen (suc _)) ()
basic (T.X-gen (zero) (zero) _) ()
basic (T.X-gen (zero) (suc (zero)) _) _ = CX01.proved
basic (T.X-gen (zero) (suc (suc (zero))) _) ()
basic (T.X-gen (zero) (suc (suc (suc (zero)))) _) ()
basic (T.X-gen (zero) (suc (suc (suc (suc (zero))))) _) ()
basic (T.X-gen (zero) (suc (suc (suc (suc (suc (zero)))))) _) ()
basic (T.X-gen (zero) (suc (suc (suc (suc (suc (suc (zero))))))) _) ()
basic (T.X-gen (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) _) ()
basic (T.X-gen (zero) (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _) _
basic (T.X-gen (suc (zero)) (zero) _) ()
basic (T.X-gen (suc (zero)) (suc (zero)) _) ()
basic (T.X-gen (suc (zero)) (suc (suc (zero))) _) _ = CX12.proved
basic (T.X-gen (suc (zero)) (suc (suc (suc (zero)))) _) ()
basic (T.X-gen (suc (zero)) (suc (suc (suc (suc (zero))))) _) ()
basic (T.X-gen (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) _) ()
basic (T.X-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) _) ()
basic (T.X-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) _) ()
basic (T.X-gen (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _) _
basic (T.X-gen (suc (suc (zero))) (zero) _) ()
basic (T.X-gen (suc (suc (zero))) (suc (zero)) _) ()
basic (T.X-gen (suc (suc (zero))) (suc (suc (zero))) _) ()
basic (T.X-gen (suc (suc (zero))) (suc (suc (suc (zero)))) _) _ = CX23.proved
basic (T.X-gen (suc (suc (zero))) (suc (suc (suc (suc (zero))))) _) ()
basic (T.X-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) _) ()
basic (T.X-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) _) ()
basic (T.X-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) _) ()
basic (T.X-gen (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _) _
basic (T.X-gen (suc (suc (suc (zero)))) (zero) _) ()
basic (T.X-gen (suc (suc (suc (zero)))) (suc (zero)) _) ()
basic (T.X-gen (suc (suc (suc (zero)))) (suc (suc (zero))) _) ()
basic (T.X-gen (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) _) ()
basic (T.X-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) _) _ = CX34.proved
basic (T.X-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) _) ()
basic (T.X-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) _) ()
basic (T.X-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) _) ()
basic (T.X-gen (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _) _
basic (T.X-gen (suc (suc (suc (suc (zero))))) (zero) _) ()
basic (T.X-gen (suc (suc (suc (suc (zero))))) (suc (zero)) _) ()
basic (T.X-gen (suc (suc (suc (suc (zero))))) (suc (suc (zero))) _) ()
basic (T.X-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (zero)))) _) ()
basic (T.X-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (zero))))) _) ()
basic (T.X-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) _) _ = CX45.proved
basic (T.X-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) _) ()
basic (T.X-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) _) ()
basic (T.X-gen (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _) _
basic (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (zero) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) _) _ = CX56.proved
basic (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _) _
basic (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (zero) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) _) _ = CX67.proved
basic (T.X-gen (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _) _
basic (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) _) ()
basic (T.X-gen (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _) _
basic (T.X-gen (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _ _) _
basic (T.K-gen (suc _) _ _ _ _ _ _) (() , _)
basic (T.K-gen (zero) (zero) _ _ _ _ _) (_ , () , _)
basic (T.K-gen (zero) (suc (suc _)) _ _ _ _ _) (_ , () , _)
basic (T.K-gen (zero) (suc (zero)) (zero) _ _ _ _) (_ , _ , () , _)
basic (T.K-gen (zero) (suc (zero)) (suc (zero)) _ _ _ _) (_ , _ , () , _)
basic (T.K-gen (zero) (suc (zero)) (suc (suc (suc _))) _ _ _ _) (_ , _ , () , _)
basic (T.K-gen (zero) (suc (zero)) (suc (suc (zero))) (zero) _ _ _) (_ , _ , _ , ())
basic (T.K-gen (zero) (suc (zero)) (suc (suc (zero))) (suc (zero)) _ _ _) (_ , _ , _ , ())
basic (T.K-gen (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (zero))) _ _ _) (_ , _ , _ , ())
basic (T.K-gen (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) _ _ _) _ = CK0123.proved
basic (T.K-gen (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc _)))) _ _ _) (_ , _ , _ , ())

-- Every other letter is a basic one conjugated by adjacent X's, and both
-- readings respect that conjugation: the two-level one by the soundness
-- of Table 1 (two-level), the circuit one by TwoLevel.decode-cong and
-- soundness (circuit).
private
  module _ (g g′ : T.Gen 8) (x y : Fin 8) .(xy : x < y)
           (rel : PB._≈_ (T._===_ {8}) [ g ]ʷ ([ T.X-gen x y xy ]ʷ • ([ g′ ]ʷ • [ T.X-gen x y xy ]ʷ))) where

    -- The words are written out in the types, not abbreviated: two
    -- spellings of one reading are compared by unfolding it.
    two-level : Dim.⟦ [ L.⌊ g ⌋ ]ʷ ⟧ᴸ ≡ _·*·_ {{R.RingD}} Dim.⟦ [ L.⌊ T.X-gen x y xy ⌋ ]ʷ ⟧ᴸ
                  (_·*·_ {{R.RingD}} Dim.⟦ [ L.⌊ g′ ⌋ ]ʷ ⟧ᴸ Dim.⟦ [ L.⌊ T.X-gen x y xy ⌋ ]ʷ ⟧ᴸ)
    two-level = Eq.trans (SS.⟦⌊⌋⟧ 4 [ g ]ʷ)
      (Eq.trans (Eq.cong SS.mapM (sound-act₁ rel S1.𝕀))
        (Eq.trans (Eq.sym (SS.⟦⌊⌋⟧ 4 w))
          (Eq.trans (Dim.⟦•⟧ᴸ [ ⌊X⌋ ]ʷ ([ L.⌊ g′ ⌋ ]ʷ • [ ⌊X⌋ ]ʷ))
            (Eq.cong (_·*·_ {{R.RingD}} Dim.⟦ [ ⌊X⌋ ]ʷ ⟧ᴸ) (Dim.⟦•⟧ᴸ [ L.⌊ g′ ⌋ ]ʷ [ ⌊X⌋ ]ʷ)))))
      where
      ⌊X⌋ = L.⌊ T.X-gen x y xy ⌋
      w = [ T.X-gen x y xy ]ʷ • ([ g′ ]ʷ • [ T.X-gen x y xy ]ʷ)

    circuit : _·*·_ {{R.RingD}} ⟦ F.decode (T.X-gen x y xy) ⟧ᴹ
                (_·*·_ {{R.RingD}} ⟦ F.decode g′ ⟧ᴹ ⟦ F.decode (T.X-gen x y xy) ⟧ᴹ) ≡ ⟦ F.decode g ⟧ᴹ
    circuit = Eq.trans (Eq.cong (_·*·_ {{R.RingD}} ⟦ F.decode (T.X-gen x y xy) ⟧ᴹ)
                          (Eq.sym (matrix-• (F.decode g′) (F.decode (T.X-gen x y xy)))))
      (Eq.trans (Eq.sym (matrix-• (F.decode (T.X-gen x y xy)) (F.decode g′ • F.decode (T.X-gen x y xy))))
        (matrix-sound {F.decode (T.X-gen x y xy) • (F.decode g′ • F.decode (T.X-gen x y xy))} {F.decode g}
          (TwoLevel.decode-cong (PB.sym rel))))

mutual
  dyadic-letter′ : (k : ℕ) (g : T.Gen 8) → Conj.size g ℕ.< k → Dim.⟦ [ L.⌊ g ⌋ ]ʷ ⟧ᴸ ≡ ⟦ F.decode g ⟧ᴹ
  dyadic-letter′ (suc k) g (s≤s lt) = by k g lt (Conj.decompose g)

  by : (k : ℕ) (g : T.Gen 8) → Conj.size g ℕ.≤ k → Conj.Basic g ⊎ Conj.Step g →
       Dim.⟦ [ L.⌊ g ⌋ ]ʷ ⟧ᴸ ≡ ⟦ F.decode g ⟧ᴹ
  by k g lt (inj₁ b) = basic g b
  by k g lt (inj₂ s) =
    Eq.trans (two-level g g′ x y xy rel)
      (Eq.trans (Eq.cong₂ (_·*·_ {{R.RingD}}) bX (Eq.cong₂ (_·*·_ {{R.RingD}}) ih bX))
        (circuit g g′ x y xy rel))
    where
    open Conj.Step s using (x ; y ; xy ; g′ ; rel)
    bX = basic (T.X-gen x y xy) (Conj.Step.adj s)
    ih = dyadic-letter′ k g′ (ℕP.<-≤-trans (Conj.Step.small s) lt)

dyadic-letter : ∀ g → Dim.⟦ [ L.⌊ g ⌋ ]ʷ ⟧ᴸ ≡ ⟦ decode (L.⌊ g ⌋) ⟧ᴹ
dyadic-letter g = dyadic-letter′ (suc (Conj.size g)) g ℕP.≤-refl

letter-matrix : ∀ g → Dim.⟦ [ g ]ʷ ⟧ᴸ ≡ ⟦ decode g ⟧ᴹ
letter-matrix (L.⌊ g ⌋) = dyadic-letter g
letter-matrix L.IH = EM.gen-matrix H2-gen

-- Decoding every word preserves its matrix, including I ⊗ H.
decode-matrix : ∀ w → Dim.⟦ w ⟧ᴸ ≡ ⟦ (decode ʷ) w ⟧ᴹ
decode-matrix [ g ]ʷ = letter-matrix g
decode-matrix ε = Eq.sym matrix-ε
decode-matrix (w • v) = Eq.trans (Dim.⟦•⟧ᴸ w v)
  (Eq.trans (Eq.cong₂ (_·*·_ {{R.RingD}})
    (decode-matrix w) (decode-matrix v))
    (Eq.sym (matrix-• ((decode ʷ) w) ((decode ʷ) v))))
