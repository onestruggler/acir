{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D008 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00006 ; wn00007 ; wn00012 ; wn00014 ; wn00022 ; wn00023 ; wn00024 ; wn00025 ; wn00026 ; wn00027 ; wn00029 ; wn00030 ; wn00031 ; wn00039 ; wn00043 ; wn00047 ; wn00048 ; wn00056 ; wn00065 ; wn00074 ; wn00076 ; wn00084 ; wn00086 ; wn00093 ; wn00137 ; wn00139 ; wn00140 ; wn00142 ; wn00148 ; wn00149 ; wn00150 ; wn00151 ; wn00152 ; wn00153 ; wn00154 ; wn00155 ; wn00156 ; wn00157 ; wn00158 ; wn00159 ; wn00160 ; wn00161 ; wn00162 ; wn00163 ; wn00164 ; wn00165 ; wn00166 ; wn00167 ; wn00168 ; wn00169 ; wn00170 ; wn00171 ; wn00172 ; wn00173 ; wn00174 ; wn00175 ; wn00176 ; wn00177 ; wn00178 ; wn00179 ; wn00180 ; wn00181 ; wn00182 ; wn00183 ; wn00184 ; wn00185 ; wn00186)

-- PU: 117 steps
lem-PU : ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-PU = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (Toff012 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ [])
  b0 = at 6 0 (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) wn00148 ▸
       at 5 0 (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) wn00148 ▸
       at 4 0 (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) wn00148 ▸
       at 0 7 (Toff012 ∷ []) wn00149 ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 6 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸ done

  b1 : Chain (Toff012 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (Toff012 ∷ CK30 ∷ Sw23 ∷ CX20 ∷ S2 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ [])
  b1 = at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 1 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 2 7 (CK20 ∷ CX20 ∷ S2 ∷ []) wn00150 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CK30 ∷ Sw23 ∷ CX20 ∷ S2 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (Toff012 ∷ CK30 ∷ CX30 ∷ S3 ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ Sw23 ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ [])
  b2 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (S3 ∷ Sw23 ∷ []) wn00151 ▸
       at 4 2 [] wn00003 ▸
       at 4 7 (Toff012 ∷ []) wn00149 ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 10 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸ done

  b3 : Chain (Toff012 ∷ CK30 ∷ CX30 ∷ S3 ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ Sw23 ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ []) (Toff012 ∷ CK30 ∷ CX30 ∷ S3 ∷ Toff012 ∷ S3⁻ ∷ Sw23 ∷ CX20 ∷ CK20⁻ ∷ Sw23 ∷ [])
  b3 = at 9 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 6 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 6 7 (S2⁻ ∷ CX20 ∷ CK20⁻ ∷ []) wn00152 ▸
       at 5 2 (S3⁻ ∷ Sw23 ∷ []) wn00153 ▸ done

  b4 : Chain (Toff012 ∷ CK30 ∷ CX30 ∷ S3 ∷ Toff012 ∷ S3⁻ ∷ Sw23 ∷ CX20 ∷ CK20⁻ ∷ Sw23 ∷ []) (Toff012 ∷ CK30 ∷ CX30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b4 = at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 3 2 (Toff012 ∷ S3 ∷ []) (sym (low₃-comm (Toff) (S))) ▸
       at 4 2 [] wn00154 ▸
       at 3 1 (CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) wn00155 ▸ done

  b5 : Chain (Toff012 ∷ CK30 ∷ CX30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CK21⁻ ∷ CS12 ∷ CK21 ∷ Sw01 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b5 = at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (Sw01 ∷ CK21 ∷ []) wn00140 ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 3 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸
       at 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b6 : Chain (Toff012 ∷ CK30 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CK21⁻ ∷ CS12 ∷ CK21 ∷ Sw01 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b6 = at 3 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 3 4 (CK21⁻ ∷ CS12 ∷ CK21 ∷ CX31 ∷ []) wn00156 ▸
       at 2 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 4 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸
       at 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸ done

  b7 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b7 = at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 5 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX23 ∷ Sw12 ∷ []) wn00157 ▸
       at 7 2 (CX23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CX₀₁)) ▸ done

  b8 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CX30 ∷ Sw01 ∷ CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ Sw01 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b8 = at 6 2 (CX13 ∷ Sw12 ∷ []) wn00158 ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 9 2 (Sw01 ∷ CK21 ∷ []) wn00140 ▸
       at 8 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 7 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸ done

  b9 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CX30 ∷ Sw01 ∷ CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ Sw01 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ Sw01 ∷ CK21 ∷ CX31 ∷ Sw01 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b9 = at 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 7 4 (CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ CX31 ∷ []) wn00159 ▸
       at 6 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 7 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸ done

  b10 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ Sw01 ∷ CK21 ∷ CX31 ∷ Sw01 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b10 = at 8 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸
       at 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00031 ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CX30 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b11 = at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX23 ∷ Sw12 ∷ []) wn00157 ▸
       at 11 2 (CX23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CX₀₁)) ▸
       at 10 2 (CX13 ∷ Sw12 ∷ []) wn00158 ▸
       at 10 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 10 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CX30 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ Sw23 ∷ CS01 ∷ CK10 ∷ CX20 ∷ Sw23 ∷ CX30 ∷ CK30⁻ ∷ [])
  b12 = at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸
       at 12 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 11 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 10 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 11 4 (CK10⁻ ∷ CS01 ∷ CK10 ∷ CX20 ∷ []) wn00160 ▸
       at 10 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸ done

  b13 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ Sw23 ∷ CS01 ∷ CK10 ∷ CX20 ∷ Sw23 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CK30⁻ ∷ [])
  b13 = at 11 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 12 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] wn00003 ▸ done

  b14 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ [])
  b14 = at 13 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] wn00003 ▸
       at 14 2 [] wn00161 ▸
       at 13 2 [] wn00003 ▸
       at 2 11 (Toff012 ∷ []) wn00162 ▸ done

-- PUinv: 117 steps
lem-PUinv : ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-PUinv = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (K0⁻ ∷ S0 ∷ K0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ [])
  b0 = at 6 0 (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) wn00148 ▸
       at 5 0 (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) wn00148 ▸
       at 4 0 (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) wn00148 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 4 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K0⁻ ∷ S0 ∷ K0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (CK30 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ S2 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ [])
  b1 = at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 1 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 0 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 1 7 (CK20 ∷ CX20 ∷ S2 ∷ []) wn00150 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b2 : Chain (CK30 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ S2 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (CK30 ∷ CX30 ∷ S3 ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ [])
  b2 = at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (S3 ∷ Sw23 ∷ []) wn00151 ▸
       at 3 2 [] wn00003 ▸
       at 3 7 (Toff012 ∷ []) wn00149 ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 9 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸ done

  b3 : Chain (CK30 ∷ CX30 ∷ S3 ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (CK30 ∷ CX30 ∷ S3 ∷ Toff012 ∷ S3⁻ ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ [])
  b3 = at 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 4 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 5 7 (S2⁻ ∷ CX20 ∷ CK20⁻ ∷ []) wn00152 ▸
       at 4 2 (S3⁻ ∷ Sw23 ∷ []) wn00153 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b4 : Chain (CK30 ∷ CX30 ∷ S3 ∷ Toff012 ∷ S3⁻ ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (CK30 ∷ CX30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ [])
  b4 = at 5 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 7 7 (Toff012 ∷ []) wn00149 ▸
       at 2 2 (Toff012 ∷ S3 ∷ []) (sym (low₃-comm (Toff) (S))) ▸
       at 3 2 [] wn00154 ▸
       at 2 1 (CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) wn00155 ▸ done

  b5 : Chain (CK30 ∷ CX30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ []) (CK30 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CK21⁻ ∷ CS12 ∷ CK21 ∷ Sw01 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ [])
  b5 = at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ CK21 ∷ []) wn00140 ▸
       at 3 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 2 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸
       at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b6 : Chain (CK30 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CK21⁻ ∷ CS12 ∷ CK21 ∷ Sw01 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ []) (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ [])
  b6 = at 2 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 2 4 (CK21⁻ ∷ CS12 ∷ CK21 ∷ CX31 ∷ []) wn00156 ▸
       at 1 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸
       at 5 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸ done

  b7 : Chain (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ []) (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ [])
  b7 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX23 ∷ Sw12 ∷ []) wn00157 ▸
       at 6 2 (CX23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CX₀₁)) ▸ done

  b8 : Chain (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ []) (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CX30 ∷ Sw01 ∷ CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ Sw01 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ [])
  b8 = at 5 2 (CX13 ∷ Sw12 ∷ []) wn00158 ▸
       at 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (Sw01 ∷ CK21 ∷ []) wn00140 ▸
       at 7 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 6 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸ done

  b9 : Chain (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CX30 ∷ Sw01 ∷ CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ Sw01 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ []) (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ Sw01 ∷ CK21 ∷ CX31 ∷ Sw01 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ [])
  b9 = at 5 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CX21 ∷ []) wn00006 ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 6 4 (CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ CX31 ∷ []) wn00159 ▸
       at 5 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 6 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸ done

  b10 : Chain (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ Sw01 ∷ CK21 ∷ CX31 ∷ Sw01 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ []) (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ [])
  b10 = at 7 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸
       at 9 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 8 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ []) (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CX30 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ [])
  b11 = at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX23 ∷ Sw12 ∷ []) wn00157 ▸
       at 10 2 (CX23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CX₀₁)) ▸
       at 9 2 (CX13 ∷ Sw12 ∷ []) wn00158 ▸
       at 9 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CX30 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ []) (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ Sw23 ∷ CS01 ∷ CK10 ∷ CX20 ∷ Sw23 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ [])
  b12 = at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸
       at 11 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 10 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 9 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 10 4 (CK10⁻ ∷ CS01 ∷ CK10 ∷ CX20 ∷ []) wn00160 ▸
       at 9 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸ done

  b13 : Chain (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ Sw23 ∷ CS01 ∷ CK10 ∷ CX20 ∷ Sw23 ∷ CX30 ∷ CK30⁻ ∷ Toff012 ∷ []) (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ [])
  b13 = at 10 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 11 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] wn00003 ▸ done

  b14 : Chain (CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ []) (CK30 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ [])
  b14 = at 12 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 13 2 [] wn00161 ▸
       at 12 2 [] wn00003 ▸
       at 1 11 (Toff012 ∷ []) wn00162 ▸ done

-- comm CZ01 CCZ023: 83 steps
lem-comm-CZ01-CCZ023 : ⟪ (CZ01 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CZ01 ∷ []) ⟫ʷ
lem-comm-CZ01-CCZ023 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CZ01 ∷ CCZ023 ∷ []) (CZ01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CZ01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (CZ01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ [])
  b1 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b2 : Chain (CZ01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ []) (CZ01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ [])
  b2 = at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 3 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 1 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (CZ01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (CZ01 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ [])
  b3 = at 2 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) wn00163 ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 2 (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀)) ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 4 2 (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b4 : Chain (CZ01 ∷ CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CZ01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b4 = at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 0 2 (CS02 ∷ CZ01 ∷ []) wn00164 ▸
       at 1 2 (CX32 ∷ CZ01 ∷ []) (low-comm (CZ) (CX₁₀)) ▸
       at 2 2 (CS02⁻ ∷ CZ01 ∷ []) wn00165 ▸
       at 3 2 (CX32 ∷ CZ01 ∷ []) (low-comm (CZ) (CX₁₀)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b5 : Chain (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CZ01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ CZ01 ∷ [])
  b5 = at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 2 (Sw23 ∷ CZ01 ∷ []) (low-comm (CZ) (Swap)) ▸
       at 5 2 (CS02 ∷ CZ01 ∷ []) wn00164 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CZ01 ∷ Sw23 ∷ []) (sym (low-comm (CZ) (Swap))) ▸
       at 6 2 [] wn00003 ▸ done

  b6 : Chain (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ CZ01 ∷ []) (CS02 ∷ CX32 ∷ Sw01 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ Sw01 ∷ CZ01 ∷ [])
  b6 = at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CX32 ∷ []) (sym (low-comm (Swap) (CX₁₀))) ▸
       at 2 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸ done

  b7 : Chain (CS02 ∷ CX32 ∷ Sw01 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ Sw01 ∷ CZ01 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CZ01 ∷ [])
  b7 = at 1 2 (Sw01 ∷ CX32 ∷ []) (sym (low-comm (Swap) (CX₁₀))) ▸
       at 0 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 1 5 (CCZ123 ∷ []) wn00166 ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b8 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CZ01 ∷ []) (Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CZ01 ∷ [])
  b8 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b9 : Chain (Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CZ01 ∷ []) (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ01 ∷ [])
  b9 = at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b10 : Chain (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ01 ∷ []) (CCZ023 ∷ CZ01 ∷ [])
  b10 = at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- comm CZ01 CCZ123: 15 steps
lem-comm-CZ01-CCZ123 : ⟪ (CZ01 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CZ01 ∷ []) ⟫ʷ
lem-comm-CZ01-CCZ123 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ01 ∷ CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CZ01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) wn00163 ▸
       at 0 2 (CS12 ∷ CZ01 ∷ []) wn00167 ▸
       at 1 2 (CX32 ∷ CZ01 ∷ []) (low-comm (CZ) (CX₁₀)) ▸
       at 2 2 (CS12⁻ ∷ CZ01 ∷ []) wn00168 ▸
       at 3 2 (CX32 ∷ CZ01 ∷ []) (low-comm (CZ) (CX₁₀)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸ done

  b1 : Chain (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CZ01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ []) (CCZ123 ∷ CZ01 ∷ [])
  b1 = at 4 2 (Sw23 ∷ CZ01 ∷ []) (low-comm (CZ) (Swap)) ▸
       at 5 2 (CS12 ∷ CZ01 ∷ []) wn00167 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CZ01 ∷ Sw23 ∷ []) (sym (low-comm (CZ) (Swap))) ▸
       at 6 2 [] wn00003 ▸
       at 0 5 (CCZ123 ∷ []) wn00166 ▸ done

-- CCZ123 passes CKd10: 15 steps
lem-CCZ123-passes-CKd10 : ⟪ (CCZ123 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ123-passes-CKd10 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ123 ∷ CK10⁻ ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CK10⁻ ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) wn00163 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 5 2 (CK10⁻ ∷ CS12 ∷ []) wn00169 ▸
       at 4 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CK10⁻ ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (CK10⁻ ∷ CCZ123 ∷ [])
  b1 = at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 2 (CK10⁻ ∷ CX32 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (CX₁₀))) ▸
       at 2 2 (CK10⁻ ∷ CS12⁻ ∷ []) wn00170 ▸
       at 1 2 (CK10⁻ ∷ CX32 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (CX₁₀))) ▸
       at 0 2 (CK10⁻ ∷ CS12 ∷ []) wn00169 ▸
       at 1 5 (CCZ123 ∷ []) wn00166 ▸ done

-- SW12-PP: 17 steps
lem-SW12-PP : ⟪ (Sw12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-SW12-PP = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw12 ∷ []) (Toff012 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw12 ∷ CS03⁻ ∷ Sw12 ∷ [])
  b0 = at 4 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 0 3 (Toff012 ∷ []) wn00171 ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 3 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 4 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸ done

  b1 : Chain (Toff012 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw12 ∷ CS03⁻ ∷ Sw12 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw12 ∷ Sw12 ∷ [])
  b1 = at 1 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00014 ▸
       at 2 3 (Toff012 ∷ []) wn00171 ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 5 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 6 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 3 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw12 ∷ Sw12 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b2 = at 4 2 [] wn00014 ▸ done

-- pass [CCZ012] [CZ01]: 1 steps
lem-pass-CCZ012-vs-CZ01 : ⟪ (CCZ012 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CZ01 = run b0
  where
  b0 : Chain (CCZ012 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CZ01 ∷ CCZ012 ∷ []) wn00172 ▸ done

-- pass [CS03] [X3 TOFF013 X3]: 65 steps
lem-pass-CS03-vs-X3-TOFF013-X3 : ⟪ (CS03 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X3-TOFF013-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (CS03 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (CS03 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS03 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS03 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] wn00003 ▸ done

  b2 : Chain (CS03 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS03 ∷ X3 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b3 : Chain (CS03 ∷ X3 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ []) (Sw23 ∷ CS02 ∷ X2 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ [])
  b3 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

  b4 : Chain (Sw23 ∷ CS02 ∷ X2 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ CS02 ∷ Sw23 ∷ [])
  b4 = at 1 4 (X2 ∷ Toff012 ∷ X2 ∷ CS02 ∷ []) wn00174 ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b5 : Chain (X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ CS02 ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CS02 ∷ Sw23 ∷ [])
  b5 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b6 : Chain (X3 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CS02 ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CS02 ∷ Sw23 ∷ [])
  b6 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸ done

  b7 : Chain (X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CS02 ∷ Sw23 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b7 = at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ [])
  b8 = at 4 2 [] wn00003 ▸ done

-- pass [CSd03] [X3 TOFF013 X3]: 65 steps
lem-pass-CSd03-vs-X3-TOFF013-X3 : ⟪ (CS03⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-X3-TOFF013-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (CS03⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (CS03⁻ ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS03⁻ ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS03⁻ ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] wn00003 ▸ done

  b2 : Chain (CS03⁻ ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS03⁻ ∷ X3 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b3 : Chain (CS03⁻ ∷ X3 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ []) (Sw23 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ [])
  b3 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

  b4 : Chain (Sw23 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b4 = at 1 4 (X2 ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ []) wn00176 ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b5 : Chain (X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b5 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b6 : Chain (X3 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b6 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸ done

  b7 : Chain (X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b7 = at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS03⁻ ∷ [])
  b8 = at 4 2 [] wn00003 ▸ done

-- pass [CS12] [CS03]: 9 steps
lem-pass-CS12-vs-CS03 : ⟪ (CS12 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-CS03 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12 ∷ CS03 ∷ []) (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 2 2 (CS01 ∷ CS23 ∷ []) (sym (low-comm (CS) (CS))) ▸
       at 3 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ []) (CS03 ∷ CS12 ∷ [])
  b1 = at 0 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

-- pass [CS02] [CS03]: 15 steps
lem-pass-CS02-vs-CS03 : ⟪ (CS02 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-CS03 = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ CS03 ∷ []) (Sw01 ∷ CS13 ∷ CS12 ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 1 2 (CS13 ∷ CS12 ∷ []) wn00093 ▸ done

  b1 : Chain (Sw01 ∷ CS13 ∷ CS12 ∷ Sw01 ∷ []) (CS03 ∷ CS02 ∷ [])
  b1 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 2 [] wn00031 ▸ done

-- pass [CCZ012] [CS12]: 1 steps
lem-pass-CCZ012-vs-CS12 : ⟪ (CCZ012 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CS12 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS12 ∷ []) (CS12 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS12 ∷ CCZ012 ∷ []) wn00177 ▸ done

-- pass [CCZ012] [CZ12]: 1 steps
lem-pass-CCZ012-vs-CZ12 : ⟪ (CCZ012 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CZ12 = run b0
  where
  b0 : Chain (CCZ012 ∷ CZ12 ∷ []) (CZ12 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CZ12 ∷ CCZ012 ∷ []) wn00178 ▸ done

-- pass [CS02] [CSd03]: 15 steps
lem-pass-CS02-vs-CSd03 : ⟪ (CS02 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-CSd03 = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ CS03⁻ ∷ []) (Sw01 ∷ CS13⁻ ∷ CS12 ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 1 2 (CS13⁻ ∷ CS12 ∷ []) wn00086 ▸ done

  b1 : Chain (Sw01 ∷ CS13⁻ ∷ CS12 ∷ Sw01 ∷ []) (CS03⁻ ∷ CS02 ∷ [])
  b1 = at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 2 [] wn00031 ▸ done

-- pass [CSd12] [CS03]: 9 steps
lem-pass-CSd12-vs-CS03 : ⟪ (CS12⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-CS03 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12⁻ ∷ CS03 ∷ []) (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23⁻ ∷ []) wn00084 ▸
       at 2 2 (CS01 ∷ CS23⁻ ∷ []) (sym (low-comm (CS) ((CS • CS • CS)))) ▸
       at 3 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS12⁻ ∷ []) (CS03 ∷ CS12⁻ ∷ [])
  b1 = at 0 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

-- pass [CSd02] [CS03]: 15 steps
lem-pass-CSd02-vs-CS03 : ⟪ (CS02⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-CS03 = trans (run b0) (run b1)
  where
  b0 : Chain (CS02⁻ ∷ CS03 ∷ []) (Sw01 ∷ CS13 ∷ CS12⁻ ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 1 2 (CS13 ∷ CS12⁻ ∷ []) wn00179 ▸ done

  b1 : Chain (Sw01 ∷ CS13 ∷ CS12⁻ ∷ Sw01 ∷ []) (CS03 ∷ CS02⁻ ∷ [])
  b1 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 2 2 [] wn00031 ▸ done

-- pass [CCZ012] [CSd12]: 1 steps
lem-pass-CCZ012-vs-CSd12 : ⟪ (CCZ012 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CSd12 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ CCZ012 ∷ []) wn00180 ▸ done

-- pass [CSd02] [CSd03]: 15 steps
lem-pass-CSd02-vs-CSd03 : ⟪ (CS02⁻ ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-CSd03 = trans (run b0) (run b1)
  where
  b0 : Chain (CS02⁻ ∷ CS03⁻ ∷ []) (Sw01 ∷ CS13⁻ ∷ CS12⁻ ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 1 2 (CS13⁻ ∷ CS12⁻ ∷ []) wn00181 ▸ done

  b1 : Chain (Sw01 ∷ CS13⁻ ∷ CS12⁻ ∷ Sw01 ∷ []) (CS03⁻ ∷ CS02⁻ ∷ [])
  b1 = at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 2 2 [] wn00031 ▸ done

-- pass [TOFF012] [X2 TOFF012 X2]: 1 steps
lem-pass-TOFF012-vs-X2-TOFF012-X2 : ⟪ (Toff012 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-X2-TOFF012-X2 = run b0
  where
  b0 : Chain (Toff012 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ [])
  b0 = at 0 4 (X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ []) wn00182 ▸ done

-- pass [CCZ013] [CZ01]: 47 steps
lem-pass-CCZ013-vs-CZ01 : ⟪ (CCZ013 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CZ01 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CCZ013 ∷ CZ01 ∷ []) (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CZ01 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (Sw23 ∷ CZ01 ∷ []) (low-comm (CZ) (Swap)) ▸
       at 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CZ01 ∷ Sw23 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CZ01 ∷ Sw23 ∷ [])
  b1 = at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b2 : Chain (CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CZ01 ∷ Sw23 ∷ []) (Sw23 ∷ CZ01 ∷ CCZ012 ∷ Sw23 ∷ [])
  b2 = at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CZ01 ∷ CCZ012 ∷ []) wn00172 ▸ done

  b3 : Chain (Sw23 ∷ CZ01 ∷ CCZ012 ∷ Sw23 ∷ []) (CZ01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ [])
  b3 = at 0 2 (CZ01 ∷ Sw23 ∷ []) (sym (low-comm (CZ) (Swap))) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b4 : Chain (CZ01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ []) (CZ01 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b4 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸ done

  b5 : Chain (CZ01 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (CZ01 ∷ CCZ013 ∷ [])
  b5 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

-- pass [CS02] [X2 TOFF012 X2]: 1 steps
lem-pass-CS02-vs-X2-TOFF012-X2 : ⟪ (CS02 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-X2-TOFF012-X2 = run b0
  where
  b0 : Chain (CS02 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS02 ∷ [])
  b0 = at 0 4 (X2 ∷ Toff012 ∷ X2 ∷ CS02 ∷ []) wn00174 ▸ done

-- pass [CSd02] [X2 TOFF012 X2]: 1 steps
lem-pass-CSd02-vs-X2-TOFF012-X2 : ⟪ (CS02⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-X2-TOFF012-X2 = run b0
  where
  b0 : Chain (CS02⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ [])
  b0 = at 0 4 (X2 ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ []) wn00176 ▸ done

-- pass [S0] [CS03]: 9 steps
lem-pass-S0-vs-CS03 : ⟪ (S0 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CS03 = trans (run b0) (run b1)
  where
  b0 : Chain (S0 ∷ CS03 ∷ []) (CS03 ∷ S0 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 1 2 (CS02 ∷ S0 ∷ []) wn00183 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸ done

  b1 : Chain (CS03 ∷ S0 ∷ Sw23 ∷ Sw23 ∷ []) (CS03 ∷ S0 ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done

-- pass [S0] [CSd03]: 9 steps
lem-pass-S0-vs-CSd03 : ⟪ (S0 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CSd03 = trans (run b0) (run b1)
  where
  b0 : Chain (S0 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ S0 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 1 2 (CS02⁻ ∷ S0 ∷ []) wn00184 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸ done

  b1 : Chain (CS03⁻ ∷ S0 ∷ Sw23 ∷ Sw23 ∷ []) (CS03⁻ ∷ S0 ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done

-- pass [CSd13] [CS02]: 5 steps
lem-pass-CSd13-vs-CS02 : ⟪ (CS13⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-CS02 = run b0
  where
  b0 : Chain (CS13⁻ ∷ CS02 ∷ []) (CS02 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23⁻ ∷ []) wn00084 ▸
       at 1 2 (CS01 ∷ CS23⁻ ∷ []) (sym (low-comm (CS) ((CS • CS • CS)))) ▸
       at 2 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 0 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸ done

-- pass [CCZ013] [CSd13]: 49 steps
lem-pass-CCZ013-vs-CSd13 : ⟪ (CCZ013 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CSd13 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CCZ013 ∷ CS13⁻ ∷ []) (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b2 : Chain (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ CS12⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CCZ012 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b2 = at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ CCZ012 ∷ CS12⁻ ∷ Sw23 ∷ []) (CS13⁻ ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ [])
  b3 = at 1 2 (CS12⁻ ∷ CCZ012 ∷ []) wn00180 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b4 : Chain (CS13⁻ ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ []) (CS13⁻ ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b4 = at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b5 : Chain (CS13⁻ ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (CS13⁻ ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ [])
  b5 = at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CS13⁻ ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ []) (CS13⁻ ∷ CCZ013 ∷ [])
  b6 = at 2 2 [] wn00003 ▸ done

-- pass [CCZ013] [CZ13]: 49 steps
lem-pass-CCZ013-vs-CZ13 : ⟪ (CCZ013 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CZ13 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CCZ013 ∷ CZ13 ∷ []) (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ CZ12 ∷ Sw23 ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b2 : Chain (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ CZ12 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ012 ∷ CZ12 ∷ Sw23 ∷ [])
  b2 = at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ CCZ012 ∷ CZ12 ∷ Sw23 ∷ []) (CZ13 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ [])
  b3 = at 1 2 (CZ12 ∷ CCZ012 ∷ []) wn00178 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b4 : Chain (CZ13 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ []) (CZ13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b4 = at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b5 : Chain (CZ13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (CZ13 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ [])
  b5 = at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CZ13 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ []) (CZ13 ∷ CCZ013 ∷ [])
  b6 = at 2 2 [] wn00003 ▸ done

-- pass [Sd0] [CS03]: 9 steps
lem-pass-Sd0-vs-CS03 : ⟪ (S0⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ S0⁻ ∷ []) ⟫ʷ
lem-pass-Sd0-vs-CS03 = trans (run b0) (run b1)
  where
  b0 : Chain (S0⁻ ∷ CS03 ∷ []) (CS03 ∷ S0⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 1 2 (CS02 ∷ S0⁻ ∷ []) wn00185 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸ done

  b1 : Chain (CS03 ∷ S0⁻ ∷ Sw23 ∷ Sw23 ∷ []) (CS03 ∷ S0⁻ ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done

-- pass [Sd0] [CSd03]: 9 steps
lem-pass-Sd0-vs-CSd03 : ⟪ (S0⁻ ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-pass-Sd0-vs-CSd03 = trans (run b0) (run b1)
  where
  b0 : Chain (S0⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ S0⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 1 2 (CS02⁻ ∷ S0⁻ ∷ []) wn00186 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸ done

  b1 : Chain (CS03⁻ ∷ S0⁻ ∷ Sw23 ∷ Sw23 ∷ []) (CS03⁻ ∷ S0⁻ ∷ [])
  b1 = at 2 2 [] wn00003 ▸ done
