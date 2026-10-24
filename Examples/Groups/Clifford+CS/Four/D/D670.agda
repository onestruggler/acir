{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD670 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D670 (W : Ws) (Sᴰ : SD670) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-hyb-sym-23 : St 1758
  lem-hyb-sym-23 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = sE 1758 lem-hyb-sym-23

-- respell hyb CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02  -> CS01 CS01 CK10 CS01 CX13 CS03 CS03 CS03 : 1 steps
lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- : ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠乀中中中乑业中中中中中中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄") ⟫ʷ
lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- = derive (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠乀中中中乑业中中中中中中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄")
  (rw 0 q1 ∷ []) Eq.refl
