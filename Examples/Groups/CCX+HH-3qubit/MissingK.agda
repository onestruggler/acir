{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.MissingK where

open import Data.Bool.Base using (true ; false)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using ([] ; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.MissingK.Model
open import Examples.Groups.CCX+HH-3qubit.MissingK.Evaluation
import Presentation.Base as PB

axiom-sound : ∀ {w v} → w ===ᴰ v → Ext.⟦ w ⟧ ≐ Ext.⟦ v ⟧
axiom-sound (r001 , _) = by-matrix {w = CZ01} {v = K12 • CX01 • K12} (Eq.trans e0 (Eq.trans Eq.refl (Eq.sym e4)))
axiom-sound (r002 , _) = by-matrix {w = X1} {v = CX01 • X0 • CX01 • X0} (Eq.trans e5 (Eq.trans Eq.refl (Eq.sym e9)))
axiom-sound (r003 , _) = by-matrix {w = Z0} {v = CZ01 • CX01 • CZ01 • CX01} (Eq.trans e10 (Eq.trans Eq.refl (Eq.sym e13)))
axiom-sound (r004 , _) = by-matrix {w = Z1} {v = K12 • X1 • K12} (Eq.trans e14 (Eq.trans Eq.refl (Eq.sym e16)))
axiom-sound (r005 , _) = by-matrix {w = CX20} {v = X1 • CCX12 • X1 • CCX12} (Eq.trans e17 (Eq.trans Eq.refl (Eq.sym e21)))
axiom-sound (r006 , _) = by-matrix {w = CX21} {v = CX20 • CX01 • CX20 • CX01} (Eq.trans e22 (Eq.trans Eq.refl (Eq.sym e25)))
axiom-sound (r007 , _) = by-matrix {w = CX12} {v = K12 • CX21 • K12} (Eq.trans e26 (Eq.trans Eq.refl (Eq.sym e28)))
axiom-sound (r008 , _) = by-matrix {w = SWAP12} {v = CX12 • CX21 • CX12} (Eq.trans e29 (Eq.trans Eq.refl (Eq.sym e31)))
axiom-sound (r009 , _) = by-matrix {w = CX02} {v = SWAP12 • CX01 • SWAP12} (Eq.trans e32 (Eq.trans Eq.refl (Eq.sym e34)))
axiom-sound (r010 , _) = by-matrix {w = SWAP02} {v = CX02 • CX20 • CX02} (Eq.trans e35 (Eq.trans Eq.refl (Eq.sym e37)))
axiom-sound (r011 , _) = by-matrix {w = K01} {v = SWAP02 • K12 • SWAP02} (Eq.trans e38 (Eq.trans Eq.refl (Eq.sym e40)))
axiom-sound (r012 , _) = by-matrix {w = CX10} {v = K01 • CX01 • K01} (Eq.trans e41 (Eq.trans Eq.refl (Eq.sym e43)))
axiom-sound (r013 , _) = by-matrix {w = SWAP01} {v = CX01 • CX10 • CX01} (Eq.trans e44 (Eq.trans Eq.refl (Eq.sym e46)))
axiom-sound (r014 , _) = by-matrix {w = CCX02} {v = SWAP01 • CCX12 • SWAP01} (Eq.trans e47 (Eq.trans Eq.refl (Eq.sym e49)))
axiom-sound (r015 , _) = by-matrix {w = X2} {v = SWAP02 • X0 • SWAP02} (Eq.trans e50 (Eq.trans Eq.refl (Eq.sym e52)))
axiom-sound (r016 , _) = by-matrix {w = Z2} {v = SWAP02 • Z0 • SWAP02} (Eq.trans e53 (Eq.trans Eq.refl (Eq.sym e55)))
axiom-sound (r017 , _) = by-matrix {w = CCX01} {v = K12 • CCX02 • K12} (Eq.trans e56 (Eq.trans Eq.refl (Eq.sym e58)))
axiom-sound (r018 , _) = by-matrix {w = CZ02} {v = SWAP12 • CZ01 • SWAP12} (Eq.trans e59 (Eq.trans Eq.refl (Eq.sym e61)))
axiom-sound (r019 , _) = by-matrix {w = CZ12} {v = SWAP01 • CZ02 • SWAP01} (Eq.trans e62 (Eq.trans Eq.refl (Eq.sym e64)))
axiom-sound (r020 , _) = by-matrix {w = SWAP12} {v = CZ12 • K12 • CZ12 • K12 • CZ12 • K12} (Eq.trans e29 (Eq.trans Eq.refl (Eq.sym e69)))
axiom-sound (r021 , _) = by-matrix {w = X0 • X0} {v = ε} (Eq.trans e70 (Eq.trans Eq.refl (Eq.sym e71)))
axiom-sound (r022 , _) = by-matrix {w = CX01 • CX01} {v = ε} (Eq.trans e72 (Eq.trans Eq.refl (Eq.sym e71)))
axiom-sound (r023 , _) = by-matrix {w = K12 • K12} {v = ε} (Eq.trans e73 (Eq.trans Eq.refl (Eq.sym e71)))
axiom-sound (r024 , _) = by-matrix {w = CCX12 • CCX12} {v = ε} (Eq.trans e74 (Eq.trans Eq.refl (Eq.sym e71)))
axiom-sound (r025 , _) = by-matrix {w = K01 • K01} {v = ε} (Eq.trans e75 (Eq.trans Eq.refl (Eq.sym e71)))
axiom-sound (r026 , _) = by-matrix {w = CX12 • X0} {v = X0 • CX12} (Eq.trans e76 (Eq.trans Eq.refl (Eq.sym e77)))
axiom-sound (r027 , _) = by-matrix {w = X0 • K12} {v = K12 • X0} (Eq.trans e78 (Eq.trans Eq.refl (Eq.sym e79)))
axiom-sound (r028 , _) = by-matrix {w = X1} {v = SWAP01 • X0 • SWAP01} (Eq.trans e5 (Eq.trans Eq.refl (Eq.sym e81)))
axiom-sound (r029 , _) = by-matrix {w = CX20} {v = SWAP02 • CX02 • SWAP02} (Eq.trans e17 (Eq.trans Eq.refl (Eq.sym e83)))
axiom-sound (r030 , _) = by-matrix {w = CX12} {v = SWAP01 • CX02 • SWAP01} (Eq.trans e26 (Eq.trans Eq.refl (Eq.sym e85)))
axiom-sound (r031 , _) = by-matrix {w = CX21} {v = SWAP01 • CX20 • SWAP01} (Eq.trans e22 (Eq.trans Eq.refl (Eq.sym e87)))
axiom-sound (r032 , _) = by-matrix {w = CCX01} {v = SWAP02 • CCX12 • SWAP02} (Eq.trans e56 (Eq.trans Eq.refl (Eq.sym e89)))
axiom-sound (r033 , _) = by-matrix {w = CCX01} {v = SWAP12 • CCX02 • SWAP12} (Eq.trans e56 (Eq.trans Eq.refl (Eq.sym e91)))
axiom-sound (r034 , _) = by-matrix {w = Z1} {v = SWAP01 • Z0 • SWAP01} (Eq.trans e14 (Eq.trans Eq.refl (Eq.sym e93)))
axiom-sound (r035 , _) = by-matrix {w = K01} {v = SWAP01 • K01 • SWAP01} (Eq.trans e38 (Eq.trans Eq.refl (Eq.sym e95)))
axiom-sound (r036 , _) = by-matrix {w = CCX12 • CX10} {v = CX10 • CCX12} (Eq.trans e96 (Eq.trans Eq.refl (Eq.sym e97)))
axiom-sound (r037 , _) = by-matrix {w = X0 • CCX12} {v = CCX12 • X0} (Eq.trans e98 (Eq.trans Eq.refl (Eq.sym e99)))
axiom-sound (r038 , _) = by-matrix {w = X0 • CX10} {v = CX10 • X0} (Eq.trans e100 (Eq.trans Eq.refl (Eq.sym e101)))
axiom-sound (r039 , _) = by-matrix {w = K01 • K12} {v = K12 • K01} (Eq.trans e102 (Eq.trans Eq.refl (Eq.sym e103)))
axiom-sound (r040 , _) = by-matrix {w = CZ01 • CZ12} {v = CZ12 • CZ01} (Eq.trans e104 (Eq.trans Eq.refl (Eq.sym e105)))
axiom-sound (r041 , _) = by-matrix {w = K01 • Z0} {v = X0 • K01} (Eq.trans e106 (Eq.trans Eq.refl (Eq.sym e107)))
axiom-sound (r042 , _) = by-matrix {w = X0 • CCX01} {v = CCX01 • CX12 • X0} (Eq.trans e108 (Eq.trans Eq.refl (Eq.sym e109)))
axiom-sound (r043 , _) = by-matrix {w = CX01 • CZ12} {v = CZ12 • CZ02 • CX01} (Eq.trans e110 (Eq.trans Eq.refl (Eq.sym e112)))
axiom-sound (r044 , _) = by-matrix {w = CX12 • CCX12} {v = CCX12 • CX10 • CX12} (Eq.trans e113 (Eq.trans Eq.refl (Eq.sym e115)))
axiom-sound (r045 , _) = by-matrix {w = CCX12 • CX01} {v = CX01 • CCX02 • CCX12 • CCX02} (Eq.trans e116 (Eq.trans Eq.refl (Eq.sym e119)))
axiom-sound (r046 , _) = by-matrix {w = CCX01 • CCX02} {v = CCX02 • CCX01 • CCX02 • CCX01} (Eq.trans e120 (Eq.trans Eq.refl (Eq.sym e123)))
axiom-sound (r083 , _) = by-matrix {w = m0 • m0} {v = ε} (Eq.trans e131 (Eq.trans Eq.refl (Eq.sym e71)))
axiom-sound (r084 , _) = by-matrix {w = NK • NK} {v = ε} (Eq.trans e133 (Eq.trans Eq.refl (Eq.sym e71)))
axiom-sound (r085 , _) = by-matrix {w = t12 • m0} {v = m0 • t12} (Eq.trans e138 (Eq.trans Eq.refl (Eq.sym e139)))
axiom-sound (r086 , _) = by-matrix {w = t23 • m0} {v = m0 • t23} (Eq.trans e141 (Eq.trans Eq.refl (Eq.sym e142)))
axiom-sound (r087 , _) = by-matrix {w = t34 • m0} {v = m0 • t34} (Eq.trans e153 (Eq.trans Eq.refl (Eq.sym e154)))
axiom-sound (r088 , _) = by-matrix {w = t45 • m0} {v = m0 • t45} (Eq.trans e157 (Eq.trans Eq.refl (Eq.sym e158)))
axiom-sound (r089 , _) = by-matrix {w = t56 • m0} {v = m0 • t56} (Eq.trans e159 (Eq.trans Eq.refl (Eq.sym e160)))
axiom-sound (r090 , _) = by-matrix {w = t67 • m0} {v = m0 • t67} (Eq.trans e161 (Eq.trans Eq.refl (Eq.sym e162)))
axiom-sound (r091 , _) = by-matrix {w = t45 • NK} {v = NK • t45} (Eq.trans e163 (Eq.trans Eq.refl (Eq.sym e164)))
axiom-sound (r092 , _) = by-matrix {w = t56 • NK} {v = NK • t56} (Eq.trans e165 (Eq.trans Eq.refl (Eq.sym e166)))
axiom-sound (r093 , _) = by-matrix {w = t67 • NK} {v = NK • t67} (Eq.trans e167 (Eq.trans Eq.refl (Eq.sym e168)))
axiom-sound (r094 , _) = by-matrix {w = m4 • NK} {v = NK • m4} (Eq.trans e171 (Eq.trans Eq.refl (Eq.sym e172)))
axiom-sound (r095 , _) = by-matrix {w = m0 • m4} {v = m4 • m0} (Eq.trans e173 (Eq.trans Eq.refl (Eq.sym e174)))
axiom-sound (r096 , _) = by-matrix {w = NK • k4567} {v = k4567 • NK} (Eq.trans e177 (Eq.trans Eq.refl (Eq.sym e178)))
axiom-sound (r097 , _) = by-matrix {w = t01 • NK} {v = NK • t13 • m1 • m3} (Eq.trans e182 (Eq.trans Eq.refl (Eq.sym e195)))
axiom-sound (r098 , _) = by-matrix {w = t12 • NK} {v = m0 • NK • m0 • NK • m0} (Eq.trans e196 (Eq.trans Eq.refl (Eq.sym e200)))
axiom-sound (r099 , _) = by-matrix {w = t23 • NK} {v = NK • t13} (Eq.trans e201 (Eq.trans Eq.refl (Eq.sym e202)))
axiom-sound (r100 , _) = by-matrix {w = NK • k1345} {v = k2345 • k0124} (Eq.trans e215 (Eq.trans Eq.refl (Eq.sym e228)))
axiom-sound (r101 , _) = by-matrix {w = m0 • m4 • t04 • rho} {v = rho • t04 • m4 • m0} (Eq.trans e239 (Eq.trans Eq.refl (Eq.sym e241)))
axiom-sound (r102 , ())
axiom-sound (r103 , ())
axiom-sound (r104 , ())
axiom-sound (r105 , ())
axiom-sound (r106 , ())
axiom-sound (r107 , ())
axiom-sound (r108 , ())

module Sound = Ext.Cong axiom-sound

-- This theorem is about Figures 4 and 7 only. It makes no claim about
-- independence in the extension by the seven H₂ relations.
K-definition-underivable :
  PB._≈_ _===ᴰ_ K12 (NK • X0 • NK • X0) → ⊥
K-definition-underivable e = bad (Eq.trans (read-Ext K12 x y)
  (Eq.trans (Sound.fʷ-cong e x y) (Eq.sym (read-Ext (NK • X0 • NK • X0) x y))))
  where
  x y : Bits 3
  x = (false ∷ false ∷ false ∷ [])
  y = (false ∷ false ∷ false ∷ [])
  unequal : Eq._≢_ {A = 𝔽} 4 9
  unequal ()
  bad : ix (readM K12) x y Eq.≢ ix (readM (NK • X0 • NK • X0)) x y
  bad eq = unequal (Eq.trans
    (Eq.sym (Eq.cong (λ M → ix M x y) e1))
    (Eq.trans eq (Eq.cong (λ M → ix M x y) e177)))
