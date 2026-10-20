------------------------------------------------------------------------
-- Presentations of groups
--
-- The windows of the five-wire derivations, as trees
--
-- The derivations of FiveV.D take their windows as an argument (see
-- `scratchpad/five/winlib5.py`): `WsL` proves the literal windows and
-- the two-wire equations of FiveV.D.TR, `Ws` holds those (`lit`) and the
-- placed windows.  The statements are two Braun trees, `windowsL` and
-- `windowsP`, the n-th the statement of wlNNNN, resp. wpNNNN, for
-- n = NNNN, and `wl n W`, `wp n W` the n-th proofs; records of the
-- windows, as this module had, made a 5.2 MB interface that took 97 s
-- and 2.4 GB to check.  FiveV.WinInstL and FiveV.WinInst build them.
-- Written by `scratchpad/five/wintree5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


module Examples.Groups.Clifford+CS.FiveV.WinSig where

open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc ; _/_ ; _%_ ; _≡ᵇ_)
open import Data.Unit using (⊤ ; tt)

open import Examples.Groups.Clifford+CS.FiveV.Chain using (Mac ; ⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.FiveV.Letters

-- A Braun tree of statements: the n-th is at the root for n = 0, and
-- otherwise the ⌊(n − 1)/2⌋-th of the left subtree for n odd, of the
-- right one for n even.
data WTree : Set where
  wleaf : WTree
  wnode : WTree → List Mac → List Mac → WTree → WTree

WinT : WTree → ℕ → Set
WinT wleaf           _       = ⊤
WinT (wnode a l r b) zero    = ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
WinT (wnode a l r b) (suc n) = if n % 2 ≡ᵇ 0 then WinT a (n / 2) else WinT b (n / 2)

data WProofs : WTree → Set where
  pleaf : WProofs wleaf
  pnode : ∀ {a l r b} → WProofs a → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ → WProofs b → WProofs (wnode a l r b)

private
  pick : (c : Bool) {A B : Set} → A → B → if c then A else B
  pick true  x y = x
  pick false x y = y

wget : (t : WTree) → WProofs t → (n : ℕ) → WinT t n
wget wleaf           pleaf           n       = tt
wget (wnode a l r b) (pnode pa p pb) zero    = p
wget (wnode a l r b) (pnode pa p pb) (suc n) =
  pick (n % 2 ≡ᵇ 0) (wget a pa (n / 2)) (wget b pb (n / 2))

windowsL : WTree
windowsL =
  (wnode
    (wnode
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ [])
                        wleaf
                      )
                      (CX34 ∷ Toff312 ∷ []) (Toff312 ∷ Toff412 ∷ CX34 ∷ [])
                      (wnode
                        wleaf
                        (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CX23 ∷ Toff012 ∷ []) (Toff012 ∷ CX23 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ X4 ∷ CZ13 ∷ []) (X4 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CZ14 ∷ []) (Toff214 ∷ CCZ124 ∷ Toff214 ∷ [])
                      wleaf
                    )
                  )
                  (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CS23 ∷ []) (CS23 ∷ CCZ124 ∷ [])
                      (wnode
                        wleaf
                        (CX21 ∷ Toff423 ∷ []) (Toff423 ∷ CX21 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CX30 ∷ CCZ123 ∷ []) (CX30 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff012 ∷ Toff312 ∷ Toff023 ∷ []) (Toff023 ∷ Toff312 ∷ [])
                        wleaf
                      )
                      (CX23 ∷ Toff324 ∷ Toff214 ∷ []) (Toff214 ∷ CX23 ∷ Toff324 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ [])
                      (wnode
                        wleaf
                        (CCZ123 ∷ []) (CX10 ∷ CCZ123 ∷ CX10 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ CX31 ∷ []) (CX31 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ []) (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ [])
                      wleaf
                    )
                  )
                  (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX42 ∷ Toff314 ∷ Toff314 ∷ []) (CX42 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ013 ∷ [])
                      (wnode
                        wleaf
                        (Toff413 ∷ Toff423 ∷ []) (Toff423 ∷ Toff413 ∷ [])
                        wleaf
                      )
                    )
                    (CS12⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS12⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ CK01 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ K1 ∷ CK01 ∷ S0 ∷ [])
                        wleaf
                      )
                      (CX30 ∷ Toff213 ∷ Toff213 ∷ []) (CX30 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK43 ∷ CS14 ∷ []) (CS14 ∷ CK43 ∷ [])
                        wleaf
                      )
                      (CS14 ∷ Toff324 ∷ []) (Toff324 ∷ CS14 ∷ [])
                      (wnode
                        wleaf
                        (CCZ013 ∷ CX23 ∷ []) (CX23 ∷ CCZ012 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                    )
                    (Sw13 ∷ Sw13 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (Toff124 ∷ Toff324 ∷ Toff324 ∷ []) (Toff124 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (S0⁻ ∷ S0 ∷ []) []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX12 ∷ Toff314 ∷ []) (Toff314 ∷ CX12 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ013 ∷ [])
                      (wnode
                        wleaf
                        (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (Toff201 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ CS12 ∷ []) (CS12 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ [])
                        wleaf
                      )
                      (Sw03 ∷ Toff102 ∷ []) (Toff123 ∷ Sw03 ∷ [])
                      wleaf
                    )
                  )
                )
                (CK31 ∷ Sw12 ∷ []) (Sw12 ∷ CK32 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ023 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ [])
                      (wnode
                        wleaf
                        (CS12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS12 ∷ [])
                        wleaf
                      )
                    )
                    (S0⁻ ∷ Toff012 ∷ []) (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K2⁻ ∷ Toff013 ∷ []) (Toff013 ∷ K2⁻ ∷ [])
                        wleaf
                      )
                      (CX41 ∷ Toff324 ∷ Toff324 ∷ []) (CX41 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ124 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ []) (Toff324 ∷ CS12 ∷ CS13 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ K1 ∷ []) (K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ [])
                      wleaf
                    )
                    (CCZ013 ∷ []) (CX02 ∷ CCZ013 ∷ CX02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ []) (Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ012 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX30 ∷ CX31 ∷ Toff013 ∷ []) (Toff013 ∷ CX31 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ124 ∷ [])
                      (wnode
                        wleaf
                        (CX34 ∷ CX31 ∷ Toff413 ∷ []) (Toff413 ∷ CX31 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ []) (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ []) (S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (Toff314 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                  (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (S4 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ S4 ∷ [])
                      (wnode
                        wleaf
                        (CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ []) (CCZ012 ∷ [])
                        wleaf
                      )
                    )
                    (S1⁻ ∷ S1 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (X0 ∷ X0 ∷ []) []
                        wleaf
                      )
                      (CS03 ∷ CS13 ∷ CCZ013 ∷ CS13 ∷ CZ13 ∷ CCZ013 ∷ []) (CS03 ∷ [])
                      wleaf
                    )
                  )
                )
                (CZ03 ∷ Sw12 ∷ []) (Sw12 ∷ CZ03 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) []
                        wleaf
                      )
                      (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ [])
                      (wnode
                        wleaf
                        (CS34 ∷ Toff413 ∷ []) (Toff413 ∷ CS34 ∷ CS13 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                    )
                    (CX31 ∷ CX13 ∷ CX31 ∷ []) (Sw13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX01 ∷ Toff302 ∷ Toff302 ∷ []) (CX01 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ CZ24 ∷ Toff324 ∷ CCZ234 ∷ []) (Toff324 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw24 ∷ Toff314 ∷ []) (Toff312 ∷ Sw24 ∷ [])
                        wleaf
                      )
                      (CS34 ∷ X4 ∷ []) (X4 ∷ S3 ∷ CS34⁻ ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ CK02 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ [])
                        wleaf
                      )
                      (CX31 ∷ Toff134 ∷ X4 ∷ []) (X4 ∷ Toff134 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CZ23 ∷ []) (CZ23 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
                      (wnode
                        wleaf
                        (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff324 ∷ CCZ124 ∷ []) (Toff324 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ [])
                      wleaf
                    )
                  )
                  (K2⁻ ∷ K2 ∷ []) []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ [])
                      (wnode
                        wleaf
                        (CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ []) (CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ134 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS23 ∷ Sw23 ∷ []) (Sw23 ∷ CS23 ∷ [])
                        wleaf
                      )
                      (CX14 ∷ Toff213 ∷ Toff213 ∷ []) (CX14 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX13 ∷ Toff214 ∷ []) (Toff214 ∷ CX13 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CZ14 ∷ Toff214 ∷ CCZ124 ∷ []) (Toff214 ∷ [])
                      (wnode
                        wleaf
                        (CS34 ∷ CS24 ∷ CCZ234 ∷ CX23 ∷ []) (CX23 ∷ CS34 ∷ [])
                        wleaf
                      )
                    )
                    (K0⁻ ∷ CK10 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff201 ∷ Toff203 ∷ []) (Toff203 ∷ Toff201 ∷ [])
                        wleaf
                      )
                      (CS24 ∷ Toff312 ∷ []) (Toff312 ∷ CS24 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ CCZ234 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ123 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ S4 ∷ []) (S4 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) (CX10 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ Toff302 ∷ CS13 ∷ []) (Toff302 ∷ CS13 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ013 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ013 ∷ CZ01 ∷ [])
                      (wnode
                        wleaf
                        (CS13⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ CCZ124 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ [])
                        wleaf
                      )
                      (Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ Toff214 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ K1 ∷ []) (K1 ∷ Toff124 ∷ CCZ124 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff023 ∷ CCZ123 ∷ []) (Toff023 ∷ CCZ013 ∷ [])
                      (wnode
                        wleaf
                        (CCZ234 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ []) (Toff324 ∷ CS13 ∷ CS12 ∷ [])
                        wleaf
                      )
                      (CS02 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS02 ∷ [])
                      wleaf
                    )
                  )
                )
                (CX14 ∷ Sw23 ∷ []) (Sw23 ∷ CX14 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K4 ∷ CK34 ∷ ι ∷ X3 ∷ []) (X3 ∷ CK34⁻ ∷ [])
                        wleaf
                      )
                      (S2 ∷ CS24⁻ ∷ []) (X4 ∷ CS24 ∷ X4 ∷ [])
                      (wnode
                        wleaf
                        (CS13 ∷ Toff203 ∷ []) (Toff203 ∷ CS13 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX31 ∷ Toff203 ∷ []) (Toff203 ∷ CX31 ∷ [])
                        wleaf
                      )
                      (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ023 ∷ CS01 ∷ []) (CS01 ∷ CCZ023 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ Toff302 ∷ []) (Toff302 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (S1 ∷ CS14⁻ ∷ X4 ∷ []) (X4 ∷ CS14 ∷ [])
                      (wnode
                        wleaf
                        (CCZ013 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                    )
                    (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) (Toff423 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ CX21 ∷ []) (CX21 ∷ CCZ023 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CS12 ∷ CS13 ∷ CCZ123 ∷ CS13 ∷ CZ13 ∷ CCZ123 ∷ []) (CS12 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CK42 ∷ []) (CK42 ∷ CK41 ∷ [])
                        wleaf
                      )
                      (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ [])
                      (wnode
                        wleaf
                        (K3 ∷ CK03 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ []) (CX41 ∷ CCZ234 ∷ CX41 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ []) (CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ [])
                        wleaf
                      )
                      (CS34⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS34⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CX13 ∷ []) (CX13 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS13⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ [])
                      (wnode
                        wleaf
                        (CCZ012 ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CX14 ∷ CX41 ∷ CX14 ∷ []) (Sw14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff213 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff213 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ []) (CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ X4 ∷ CZ12 ∷ []) (X4 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Toff214 ∷ CCZ134 ∷ []) (Toff214 ∷ CCZ123 ∷ [])
                      (wnode
                        wleaf
                        (CCZ234 ∷ CZ24 ∷ []) (CX23 ∷ CCZ234 ∷ CX23 ∷ [])
                        wleaf
                      )
                    )
                    (CZ12 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CCZ124 ∷ []) (Toff312 ∷ CCZ234 ∷ Toff312 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ []) (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ []) (CZ14 ∷ CCZ134 ∷ CZ14 ∷ [])
                        wleaf
                      )
                      (K2 ∷ Toff013 ∷ []) (Toff013 ∷ K2 ∷ [])
                      wleaf
                    )
                    (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (Toff312 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ S4 ∷ []) (S4 ∷ CK41 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ234 ∷ CCZ124 ∷ [])
                      (wnode
                        wleaf
                        (S0 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ S0 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ []) (CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Toff302 ∷ []) (Toff302 ∷ CZ02 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (CZ13 ∷ Sw01 ∷ []) (Sw01 ∷ CZ03 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX32 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX32 ∷ [])
                        wleaf
                      )
                      (K2⁻ ∷ CCZ123 ∷ []) (Toff213 ∷ K2⁻ ∷ [])
                      (wnode
                        wleaf
                        (CS23⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS23⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ []) (CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (X0 ∷ S0 ∷ X0 ∷ []) (ι ∷ S0⁻ ∷ [])
                        wleaf
                      )
                      (CX03 ∷ Toff213 ∷ []) (Toff213 ∷ CX03 ∷ Toff201 ∷ [])
                      wleaf
                    )
                  )
                )
                (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
                        wleaf
                      )
                      (K0 ∷ CCZ023 ∷ []) (Toff023 ∷ K0 ∷ [])
                      (wnode
                        wleaf
                        (CX13 ∷ Toff301 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX13 ∷ Toff301 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX10 ∷ Toff302 ∷ []) (Toff302 ∷ CX10 ∷ Toff312 ∷ [])
                        wleaf
                      )
                      (Sw14 ∷ Toff324 ∷ []) (Toff312 ∷ Sw14 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ123 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ CZ02 ∷ Toff302 ∷ CCZ023 ∷ []) (Toff302 ∷ [])
                        wleaf
                      )
                      (S4 ∷ Toff213 ∷ []) (Toff213 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ CS34 ∷ []) (CS34 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CZ23 ∷ Toff423 ∷ CCZ234 ∷ []) (Toff423 ∷ [])
                        wleaf
                      )
                      (CS03 ∷ CS12 ∷ []) (CS12 ∷ CS03 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (Sw23 ∷ Sw34 ∷ []) (Sw24 ∷ Sw23 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) []
                        wleaf
                      )
                      (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ [])
                      (wnode
                        wleaf
                        (CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ []) (CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CS23 ∷ Toff023 ∷ []) (Toff023 ∷ CS23 ∷ [])
                      wleaf
                    )
                  )
                  (CZ02 ∷ Toff213 ∷ []) (Toff213 ∷ CZ02 ∷ CCZ013 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX30 ∷ Toff023 ∷ []) (Toff023 ∷ CX30 ∷ [])
                        wleaf
                      )
                      (CX41 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX41 ∷ [])
                      (wnode
                        wleaf
                        (CCZ012 ∷ Toff301 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ012 ∷ CCZ012 ∷ Toff301 ∷ [])
                        wleaf
                      )
                    )
                    (CS24⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS24⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ S4 ∷ CK41 ∷ []) []
                        wleaf
                      )
                      (CCZ012 ∷ []) (CZ01 ∷ CCZ012 ∷ CZ01 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw12 ∷ ι1 ∷ []) (ι1 ∷ Sw12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX41 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS03⁻ ∷ [])
                      (wnode
                        wleaf
                        (CX32 ∷ Toff301 ∷ []) (Toff301 ∷ CX32 ∷ Toff201 ∷ [])
                        wleaf
                      )
                    )
                    (CK20 ∷ []) (CS02⁻ ∷ K0⁻ ∷ CS02⁻ ∷ K0 ∷ CS02⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ CS12⁻ ∷ CZ12 ∷ CCZ123 ∷ []) (CS13⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ []) (CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                    (CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS13 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS13 ∷ [])
                        wleaf
                      )
                      (CS12 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS12 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (Sw23 ∷ Sw23 ∷ []) []
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX13 ∷ Toff314 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX13 ∷ Toff314 ∷ [])
                        wleaf
                      )
                      (Toff312 ∷ Toff423 ∷ []) (Toff423 ∷ Toff312 ∷ Toff412 ∷ [])
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ []) (Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ023 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CX23 ∷ Toff214 ∷ []) (Toff214 ∷ Toff314 ∷ CX23 ∷ [])
                      wleaf
                    )
                  )
                  (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (CCZ123 ∷ [])
                        wleaf
                      )
                      (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
                      (wnode
                        wleaf
                        (CCZ012 ∷ CX31 ∷ []) (CX31 ∷ CCZ023 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                    )
                    (S0 ∷ CS03⁻ ∷ []) (X3 ∷ CS03 ∷ X3 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ [])
                        wleaf
                      )
                      (CS02 ∷ CS13 ∷ []) (CS13 ∷ CS02 ∷ [])
                      wleaf
                    )
                  )
                )
                (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ X3 ∷ []) (X3 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CK41 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK41 ∷ [])
                      (wnode
                        wleaf
                        (CCZ124 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ124 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff301 ∷ CCZ012 ∷ CCZ012 ∷ []) (Toff301 ∷ [])
                        wleaf
                      )
                      (CX21 ∷ CX12 ∷ CX21 ∷ []) (Sw12 ∷ [])
                      wleaf
                    )
                  )
                  (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw24 ∷ Toff134 ∷ []) (Toff123 ∷ Sw24 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ []) (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ [])
                      (wnode
                        wleaf
                        (CX21 ∷ Toff413 ∷ []) (Toff413 ∷ CX21 ∷ Toff423 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                      (Sw03 ∷ Toff123 ∷ []) (Toff102 ∷ Sw03 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK43 ∷ CS24 ∷ []) (CS24 ∷ CK43 ∷ [])
                        wleaf
                      )
                      (CX34 ∷ CX43 ∷ CX34 ∷ []) (Sw34 ∷ [])
                      (wnode
                        wleaf
                        (CCZ124 ∷ []) (CZ12 ∷ CCZ124 ∷ CZ12 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ013 ∷ CZ13 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ Toff314 ∷ CZ14 ∷ []) (Toff314 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ Toff012 ∷ CZ12 ∷ []) (Toff012 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ CZ01 ∷ CX03 ∷ []) (CX03 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ []) (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ [])
                      (wnode
                        wleaf
                        (CS13 ∷ CS24 ∷ []) (CS24 ∷ CS13 ∷ [])
                        wleaf
                      )
                    )
                    (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK01 ∷ X0 ∷ []) (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ CZ01 ∷ Toff201 ∷ CCZ012 ∷ []) (Toff201 ∷ [])
                      wleaf
                    )
                  )
                )
                (CK41 ∷ Sw23 ∷ []) (Sw23 ∷ CK41 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw34 ∷ Toff213 ∷ []) (Toff214 ∷ Sw34 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ123 ∷ [])
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                    )
                    (CS01 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) (CS01 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff134 ∷ CZ12 ∷ Toff134 ∷ CCZ134 ∷ CZ12 ∷ []) (CCZ234 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CZ01 ∷ []) (Toff301 ∷ CCZ013 ∷ Toff301 ∷ [])
                      wleaf
                    )
                  )
                  (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (S1 ∷ CS14⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S1 ∷ CS14⁻ ∷ [])
                      wleaf
                    )
                    (CCZ013 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX31 ∷ Toff423 ∷ []) (Toff423 ∷ CX31 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ Toff214 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX12 ∷ Toff214 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                      (Sw02 ∷ Toff123 ∷ []) (Toff103 ∷ Sw02 ∷ [])
                      (wnode
                        wleaf
                        (CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                    )
                    (Toff012 ∷ Toff023 ∷ []) (Toff023 ∷ Toff012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS34 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CS34 ∷ [])
                        wleaf
                      )
                      (Toff302 ∷ Toff302 ∷ []) []
                      wleaf
                    )
                  )
                  (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS23 ∷ Toff012 ∷ []) (Toff012 ∷ CS23 ∷ [])
                        wleaf
                      )
                      (CK41 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ [])
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff423 ∷ []) (Toff423 ∷ CZ23 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                    )
                    (Toff102 ∷ Toff102 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ123 ∷ CZ13 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK42 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
                        wleaf
                      )
                      (Toff213 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff213 ∷ [])
                      (wnode
                        wleaf
                        (CS34⁻ ∷ CS13⁻ ∷ CCZ134 ∷ CS13⁻ ∷ CZ13 ∷ CCZ134 ∷ []) (CS34⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CZ12 ∷ []) (Toff012 ∷ CCZ012 ∷ Toff012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ []) (Toff201 ∷ [])
                        wleaf
                      )
                      (CX21 ∷ Toff324 ∷ []) (Toff324 ∷ CX21 ∷ [])
                      wleaf
                    )
                  )
                  (Toff324 ∷ X4 ∷ []) (X4 ∷ CX23 ∷ Toff324 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ CZ02 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CK41 ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ [])
                      wleaf
                    )
                    (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (Toff412 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CZ23 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (Toff134 ∷ Toff234 ∷ Toff234 ∷ []) (Toff134 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CX24 ∷ Sw12 ∷ []) (Sw12 ∷ CX14 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ []) (CZ03 ∷ CCZ123 ∷ CZ03 ∷ [])
                        wleaf
                      )
                      (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ [])
                      (wnode
                        wleaf
                        (CX23 ∷ Toff413 ∷ []) (Toff413 ∷ CX23 ∷ Toff412 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K2⁻ ∷ Toff301 ∷ []) (Toff301 ∷ K2⁻ ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Toff023 ∷ []) (Toff023 ∷ CZ23 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (S2⁻ ∷ S2 ∷ []) []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff324 ∷ CZ24 ∷ []) (Toff324 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CK41 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ [])
                      (wnode
                        wleaf
                        (K2 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ [])
                        wleaf
                      )
                    )
                    (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ [])
                        wleaf
                      )
                      (CX34 ∷ Toff213 ∷ []) (Toff213 ∷ CX34 ∷ [])
                      wleaf
                    )
                  )
                )
                (CX10 ∷ Sw01 ∷ []) (Sw01 ∷ CX01 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK41 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CZ03 ∷ []) (Toff203 ∷ CCZ023 ∷ Toff203 ∷ [])
                      (wnode
                        wleaf
                        (CCZ234 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ234 ∷ [])
                        wleaf
                      )
                    )
                    (CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) (CS02⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CS12 ∷ Toff312 ∷ []) (Toff312 ∷ CS12 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ [])
                        wleaf
                      )
                      (CX10 ∷ CX01 ∷ CX10 ∷ []) (Sw01 ∷ [])
                      wleaf
                    )
                    (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX24 ∷ Toff423 ∷ []) (Toff423 ∷ CX24 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CS13 ∷ Toff324 ∷ []) (CS13 ∷ Toff324 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ Toff312 ∷ CCZ124 ∷ []) (Toff312 ∷ CCZ234 ∷ [])
                      (wnode
                        wleaf
                        (CS12 ∷ Toff413 ∷ []) (Toff413 ∷ CS12 ∷ [])
                        wleaf
                      )
                    )
                    (Sw23 ∷ Toff103 ∷ []) (Toff102 ∷ Sw23 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ []) (CCZ134 ∷ [])
                        wleaf
                      )
                      (Toff312 ∷ Toff314 ∷ []) (Toff314 ∷ Toff312 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ Toff203 ∷ []) (Toff203 ∷ K1 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ [])
                      (wnode
                        wleaf
                        (CS12⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                    )
                    (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K3 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ [])
                        wleaf
                      )
                      (CS13⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS13⁻ ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw12 ∷ Sw23 ∷ []) (Sw13 ∷ Sw12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX21 ∷ Toff301 ∷ []) (Toff301 ∷ CX21 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (S2 ∷ CS24⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S2 ∷ CS24⁻ ∷ [])
                      (wnode
                        wleaf
                        (CX13 ∷ Toff412 ∷ []) (Toff412 ∷ CX13 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CCZ124 ∷ []) (Toff324 ∷ CCZ123 ∷ Toff324 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ CZ24 ∷ []) (Toff324 ∷ CCZ234 ∷ Toff324 ∷ [])
                      wleaf
                    )
                  )
                  (Toff023 ∷ Toff023 ∷ []) []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ []) (CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (S2 ∷ CS24⁻ ∷ Toff314 ∷ []) (Toff314 ∷ S2 ∷ CS24⁻ ∷ [])
                      (wnode
                        wleaf
                        (K3 ∷ CK03 ∷ S0 ∷ Toff203 ∷ []) (Toff203 ∷ K3 ∷ CK03 ∷ S0 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CZ13 ∷ []) (Toff413 ∷ CCZ134 ∷ Toff413 ∷ [])
                        wleaf
                      )
                      (CZ13 ∷ CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK42 ∷ CK43 ∷ []) (CK43 ∷ CK42 ∷ [])
                        wleaf
                      )
                      (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ [])
                      (wnode
                        wleaf
                        (CK03 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CK03 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ []) (CX14 ∷ CCZ123 ∷ CX14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff234 ∷ CCZ134 ∷ []) (Toff234 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CS03 ∷ CX32 ∷ []) (CX32 ∷ CS03 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ CS02 ∷ []) (CS02 ∷ CCZ123 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS13 ∷ CS01 ∷ CCZ013 ∷ CX03 ∷ []) (CX03 ∷ CS13 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CZ13 ∷ []) (Toff013 ∷ CCZ013 ∷ Toff013 ∷ [])
                      (wnode
                        wleaf
                        (CK02 ∷ CCZ023 ∷ CK02 ∷ S0 ∷ []) (Toff203 ∷ [])
                        wleaf
                      )
                    )
                    (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0⁻ ∷ []) (Toff013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S1 ∷ CS01⁻ ∷ X0 ∷ []) (X0 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (CX14 ∷ Toff234 ∷ []) (Toff234 ∷ CX14 ∷ Toff213 ∷ [])
                      wleaf
                    )
                  )
                )
                (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CX01 ∷ CX10 ∷ CX01 ∷ []) (Sw01 ∷ [])
                      (wnode
                        wleaf
                        (CS34⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ [])
                        wleaf
                      )
                    )
                    (CK10⁻ ∷ []) (CS01 ∷ K0⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K2⁻ ∷ []) (Toff201 ∷ [])
                        wleaf
                      )
                      (CX21 ∷ Toff023 ∷ Toff023 ∷ []) (CX21 ∷ [])
                      wleaf
                    )
                  )
                  (Toff134 ∷ X4 ∷ []) (X4 ∷ CX31 ∷ Toff134 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX14 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX14 ∷ [])
                        wleaf
                      )
                      (Toff213 ∷ Toff314 ∷ []) (Toff214 ∷ Toff314 ∷ Toff213 ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ CK01 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ K1 ∷ CK01 ∷ S0 ∷ [])
                        wleaf
                      )
                      (CX20 ∷ Toff023 ∷ []) (Toff023 ∷ CX20 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S4 ∷ [])
                        wleaf
                      )
                      (Sw02 ∷ Toff312 ∷ []) (Toff301 ∷ Sw02 ∷ [])
                      (wnode
                        wleaf
                        (CX23 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX23 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ023 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX12 ∷ Toff302 ∷ []) (Toff302 ∷ CX12 ∷ Toff301 ∷ [])
                        wleaf
                      )
                      (CS03 ∷ CS02 ∷ CCZ023 ∷ CX23 ∷ []) (CX23 ∷ CS03 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX12 ∷ Toff324 ∷ []) (Toff324 ∷ CX12 ∷ Toff314 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ023 ∷ [])
                      (wnode
                        wleaf
                        (CCZ124 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ124 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CX23 ∷ []) (CX23 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (Toff213 ∷ Toff301 ∷ [])
                        wleaf
                      )
                      (CX30 ∷ CX03 ∷ CX30 ∷ []) (Sw03 ∷ [])
                      wleaf
                    )
                  )
                )
                (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS14 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS14 ∷ [])
                        wleaf
                      )
                      (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ [])
                      (wnode
                        wleaf
                        (CCZ012 ∷ CX13 ∷ CCZ012 ∷ Toff301 ∷ []) (CX13 ∷ Toff301 ∷ [])
                        wleaf
                      )
                    )
                    (S0 ∷ Toff012 ∷ []) (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS24⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS24⁻ ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ013 ∷ CCZ012 ∷ [])
                      wleaf
                    )
                  )
                  (CS13⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS13⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ []) (X4 ∷ CCZ012 ∷ X4 ∷ [])
                        wleaf
                      )
                      (CK43 ∷ X4 ∷ []) (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ234 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ234 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CX13 ∷ Toff023 ∷ []) (Toff023 ∷ CX13 ∷ Toff012 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CX43 ∷ Sw23 ∷ []) (Sw23 ∷ CX42 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (X4 ∷ X4 ∷ []) []
                        wleaf
                      )
                      (S1 ∷ CS14⁻ ∷ []) (X4 ∷ CS14 ∷ X4 ∷ [])
                      (wnode
                        wleaf
                        (Sw23 ∷ Toff124 ∷ []) (Toff134 ∷ Sw23 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ []) (CX24 ∷ CCZ123 ∷ CX24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX01 ∷ Toff203 ∷ Toff203 ∷ []) (CX01 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ []) (CZ23 ∷ CCZ023 ∷ CZ23 ∷ [])
                      wleaf
                    )
                  )
                  (Toff314 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ Toff314 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ Sw03 ∷ []) (Sw03 ∷ CS13 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Toff012 ∷ CCZ123 ∷ []) (Toff012 ∷ CCZ023 ∷ [])
                      (wnode
                        wleaf
                        (CK02 ∷ []) (CS02⁻ ∷ K2⁻ ∷ CS02⁻ ∷ K2 ∷ CS02⁻ ∷ [])
                        wleaf
                      )
                    )
                    (Toff301 ∷ Toff301 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ []) (CX30 ∷ CCZ123 ∷ CX30 ∷ [])
                        wleaf
                      )
                      (CX03 ∷ Toff201 ∷ []) (Toff201 ∷ CX03 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ []) (CX42 ∷ [])
                        wleaf
                      )
                      (Toff203 ∷ Toff203 ∷ []) []
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ [])
                        wleaf
                      )
                    )
                    (K0 ∷ CK20⁻ ∷ []) (X2 ∷ CK20 ∷ X2 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff312 ∷ CZ12 ∷ []) (Toff312 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CCZ134 ∷ Toff214 ∷ CCZ134 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                  (CX13 ∷ Toff012 ∷ []) (Toff012 ∷ CX13 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CZ23 ∷ Toff301 ∷ []) (Toff301 ∷ CZ23 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CS01 ∷ []) (CS01 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                    (CCZ234 ∷ Toff412 ∷ CCZ123 ∷ []) (Toff412 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ [])
                        wleaf
                      )
                      (CX23 ∷ Toff012 ∷ Toff012 ∷ []) (CX23 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
      (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ [])
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff134 ∷ Toff213 ∷ []) (Toff213 ∷ Toff134 ∷ Toff234 ∷ [])
                        wleaf
                      )
                      (Toff312 ∷ Toff412 ∷ []) (Toff412 ∷ Toff312 ∷ [])
                      (wnode
                        wleaf
                        (K2 ∷ CK02 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ K2 ∷ CK02 ∷ S0 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ []) (CX23 ∷ CCZ124 ∷ CX23 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Toff314 ∷ CCZ124 ∷ []) (Toff314 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                  (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX34 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX34 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CZ03 ∷ Toff203 ∷ CCZ023 ∷ []) (Toff203 ∷ [])
                      (wnode
                        wleaf
                        (CCZ012 ∷ []) (CX13 ∷ CCZ012 ∷ CX13 ∷ [])
                        wleaf
                      )
                    )
                    (CK30 ∷ []) (CS03⁻ ∷ K0⁻ ∷ CS03⁻ ∷ K0 ∷ CS03⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ [])
                        wleaf
                      )
                      (CS02⁻ ∷ CS13 ∷ []) (CS13 ∷ CS02⁻ ∷ [])
                      wleaf
                    )
                  )
                )
                (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ []) (X3 ∷ CCZ124 ∷ X3 ∷ [])
                        wleaf
                      )
                      (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ [])
                      (wnode
                        wleaf
                        (CCZ123 ∷ CX01 ∷ []) (CX01 ∷ CCZ023 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ134 ∷ CCZ134 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff301 ∷ CCZ012 ∷ []) (Toff301 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (Toff013 ∷ Toff023 ∷ []) (Toff023 ∷ Toff013 ∷ [])
                      wleaf
                    )
                  )
                  (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw24 ∷ Toff312 ∷ []) (Toff314 ∷ Sw24 ∷ [])
                        wleaf
                      )
                      (CX23 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX23 ∷ [])
                      (wnode
                        wleaf
                        (CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ []) (CCZ023 ∷ [])
                        wleaf
                      )
                    )
                    (Toff012 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS13⁻ ∷ S4 ∷ Toff413 ∷ S4⁻ ∷ []) (Toff413 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CX03 ∷ CX30 ∷ CX03 ∷ []) (Sw03 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS24 ∷ CS34 ∷ []) (CS34 ∷ CS24 ∷ [])
                        wleaf
                      )
                      (CX43 ∷ Toff412 ∷ []) (Toff412 ∷ CX43 ∷ Toff312 ∷ [])
                      (wnode
                        wleaf
                        (CCZ124 ∷ CZ12 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ K1⁻ ∷ []) (Toff124 ∷ [])
                        wleaf
                      )
                      (CS02 ∷ Toff302 ∷ []) (Toff302 ∷ CS02 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CZ12 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX42 ∷ Toff314 ∷ []) (Toff314 ∷ CX42 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ []) (CX12 ∷ CCZ134 ∷ CX12 ∷ [])
                      (wnode
                        wleaf
                        (CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ [])
                        wleaf
                      )
                    )
                    (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (Toff234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ CK01 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ []) (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw03 ∷ Sw12 ∷ []) (Sw12 ∷ Sw03 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX43 ∷ Toff214 ∷ Toff214 ∷ []) (CX43 ∷ [])
                        wleaf
                      )
                      (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ [])
                      (wnode
                        wleaf
                        (K2 ∷ CK02⁻ ∷ []) (X0 ∷ CK02 ∷ X0 ∷ [])
                        wleaf
                      )
                    )
                    (S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) (S0⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ []) (CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (Sw14 ∷ Toff234 ∷ []) (Toff213 ∷ Sw14 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ CS02 ∷ []) (CS02 ∷ CCZ013 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ S4 ∷ []) (S4 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ K2 ∷ []) (K2 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ CX02 ∷ []) (CX02 ∷ CCZ013 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX31 ∷ Toff103 ∷ X0 ∷ []) (X0 ∷ Toff103 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CX31 ∷ CCZ234 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ [])
                        wleaf
                      )
                      (Sw02 ∷ Toff301 ∷ []) (Toff312 ∷ Sw02 ∷ [])
                      (wnode
                        wleaf
                        (CCZ023 ∷ CX31 ∷ CCZ023 ∷ Toff103 ∷ []) (CX31 ∷ Toff103 ∷ [])
                        wleaf
                      )
                    )
                    (CX31 ∷ Toff012 ∷ []) (Toff012 ∷ CX31 ∷ Toff023 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CS14⁻ ∷ S3 ∷ []) (S3 ∷ CS14⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CZ12 ∷ Sw01 ∷ []) (Sw01 ∷ CZ02 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX42 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS14 ∷ [])
                        wleaf
                      )
                      (CS24 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS24 ∷ [])
                      (wnode
                        wleaf
                        (Sw13 ∷ Toff234 ∷ []) (Toff214 ∷ Sw13 ∷ [])
                        wleaf
                      )
                    )
                    (CS02⁻ ∷ S1⁻ ∷ []) (S1⁻ ∷ CS02⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CZ13 ∷ []) (Toff213 ∷ CCZ123 ∷ Toff213 ∷ [])
                      wleaf
                    )
                  )
                )
                (CK30 ∷ Sw01 ∷ []) (Sw01 ∷ CK31 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) []
                        wleaf
                      )
                      (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ [])
                      (wnode
                        wleaf
                        (CS34 ∷ CS13 ∷ CCZ134 ∷ CS13 ∷ CZ13 ∷ CCZ134 ∷ []) (CS34 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) (CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CCZ234 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CX14 ∷ Toff324 ∷ []) (Toff324 ∷ CX14 ∷ Toff312 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX01 ∷ Toff302 ∷ []) (Toff302 ∷ CX01 ∷ [])
                        wleaf
                      )
                      (K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ []) (Toff214 ∷ K1 ∷ CK41 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ124 ∷ CZ12 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ K2 ∷ []) (K2 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) (Toff213 ∷ Toff134 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ []) (CZ23 ∷ CCZ013 ∷ CZ23 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ S0 ∷ []) (S0 ∷ CCZ023 ∷ [])
                      (wnode
                        wleaf
                        (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ CCZ234 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CS03 ∷ Toff201 ∷ []) (Toff201 ∷ CS03 ∷ [])
                        wleaf
                      )
                      (CS02⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CS13⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS13⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ Toff301 ∷ []) (Toff301 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ [])
                      (wnode
                        wleaf
                        (CK01 ∷ S0 ∷ CK01 ∷ []) []
                        wleaf
                      )
                    )
                    (CCZ234 ∷ CS13 ∷ []) (CS13 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ012 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                )
                (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw34 ∷ Toff214 ∷ []) (Toff213 ∷ Sw34 ∷ [])
                        wleaf
                      )
                      (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ [])
                      (wnode
                        wleaf
                        (CCZ234 ∷ CS24 ∷ []) (CS24 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                    )
                    (CS02 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) (CS02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ CX13 ∷ CCZ012 ∷ []) (CX13 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CS13 ∷ Toff312 ∷ []) (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                  (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CX10 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX10 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ CCZ234 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX23 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX23 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ []) (CCZ123 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX23 ∷ Toff324 ∷ [])
                        wleaf
                      )
                      (CX02 ∷ Toff301 ∷ []) (Toff301 ∷ CX02 ∷ [])
                      (wnode
                        wleaf
                        (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (Toff103 ∷ [])
                        wleaf
                      )
                    )
                    (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ []) (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (Toff214 ∷ Toff312 ∷ []) (Toff312 ∷ Toff214 ∷ Toff314 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ S4 ∷ []) (S4 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CX43 ∷ CX34 ∷ CX43 ∷ []) (Sw34 ∷ [])
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff412 ∷ CCZ123 ∷ []) (Toff412 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ134 ∷ CS12 ∷ []) (CS12 ∷ CCZ134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ [])
                      wleaf
                    )
                  )
                )
                (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CX12 ∷ CCZ134 ∷ []) (CX12 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
                      (wnode
                        wleaf
                        (CX23 ∷ Toff412 ∷ []) (Toff412 ∷ CX23 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CX31 ∷ CCZ023 ∷ []) (CX31 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ []) (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ [])
                        wleaf
                      )
                      (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ [])
                      wleaf
                    )
                  )
                  (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (Toff312 ∷ Toff214 ∷ [])
                        wleaf
                      )
                      (CS14 ∷ X4 ∷ []) (X4 ∷ S1 ∷ CS14⁻ ∷ [])
                      (wnode
                        wleaf
                        (CS13 ∷ Toff201 ∷ []) (Toff201 ∷ CS13 ∷ [])
                        wleaf
                      )
                    )
                    (Toff423 ∷ Toff423 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ []) (CCZ013 ∷ [])
                        wleaf
                      )
                      (CS13⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS13⁻ ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ []) (CZ01 ∷ CCZ123 ∷ CZ01 ∷ [])
                        wleaf
                      )
                      (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ [])
                      (wnode
                        wleaf
                        (CK03 ∷ X0 ∷ []) (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CX32 ∷ Toff213 ∷ []) (Toff213 ∷ CX32 ∷ [])
                      wleaf
                    )
                  )
                  (X2 ∷ CZ01 ∷ CZ01 ∷ []) (X2 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS01⁻ ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ []) (CCZ134 ∷ [])
                      (wnode
                        wleaf
                        (CCZ023 ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ []) (CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S0 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ S0 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ CZ34 ∷ Toff234 ∷ CCZ234 ∷ []) (Toff234 ∷ [])
                      wleaf
                    )
                  )
                )
                (CS13⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS03⁻ ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CZ12 ∷ []) (CZ12 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ [])
                      (wnode
                        wleaf
                        (Toff201 ∷ Toff312 ∷ []) (Toff312 ∷ Toff201 ∷ Toff301 ∷ [])
                        wleaf
                      )
                    )
                    (CX10 ∷ Toff012 ∷ []) (Toff012 ∷ CX10 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) (CCZ234 ∷ [])
                        wleaf
                      )
                      (CX21 ∷ Toff013 ∷ []) (Toff013 ∷ CX21 ∷ Toff023 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ []) (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CX14 ∷ CCZ123 ∷ []) (CX14 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CX13 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ [])
                      wleaf
                    )
                    (Toff312 ∷ Toff312 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CS12⁻ ∷ X0 ∷ []) (X0 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                      (CX23 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX23 ∷ Toff324 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK43 ∷ S4 ∷ []) (S4 ∷ CK43 ∷ [])
                        wleaf
                      )
                      (CX10 ∷ Toff312 ∷ []) (Toff312 ∷ CX10 ∷ [])
                      (wnode
                        wleaf
                        (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CX21 ∷ CCZ234 ∷ []) (CX21 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ CS02⁻ ∷ CZ02 ∷ CCZ023 ∷ []) (CS03⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ []) (CX43 ∷ [])
                        wleaf
                      )
                      (K2 ∷ CK42⁻ ∷ []) (X4 ∷ CK42 ∷ X4 ∷ [])
                      (wnode
                        wleaf
                        (CZ34 ∷ Toff312 ∷ []) (Toff312 ∷ CZ34 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                    )
                    (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0⁻ ∷ []) (Toff023 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (X0 ∷ CZ24 ∷ CZ24 ∷ []) (X0 ∷ [])
                        wleaf
                      )
                      (Toff201 ∷ Toff213 ∷ []) (Toff213 ∷ Toff201 ∷ [])
                      wleaf
                    )
                  )
                )
                (CX42 ∷ Sw12 ∷ []) (Sw12 ∷ CX41 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (K0 ∷ CCZ013 ∷ []) (Toff013 ∷ K0 ∷ [])
                      (wnode
                        wleaf
                        (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (Toff301 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ K0 ∷ []) (K0 ∷ Toff012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX10 ∷ Toff312 ∷ Toff312 ∷ []) (CX10 ∷ [])
                        wleaf
                      )
                      (Sw14 ∷ Toff213 ∷ []) (Toff234 ∷ Sw14 ∷ [])
                      wleaf
                    )
                  )
                  (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ123 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ CZ12 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ []) (CCZ123 ∷ [])
                        wleaf
                      )
                      (CS12⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS12⁻ ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ Toff013 ∷ []) (Toff013 ∷ CS01 ∷ CS13 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CK43 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK43 ∷ [])
                      (wnode
                        wleaf
                        (Sw23 ∷ Toff413 ∷ []) (Toff412 ∷ Sw23 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ Toff023 ∷ CCZ123 ∷ []) (Toff023 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX01 ∷ Toff213 ∷ []) (Toff213 ∷ CX01 ∷ Toff203 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CZ23 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS13⁻ ∷ CX30 ∷ []) (CX30 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ [])
                      (wnode
                        wleaf
                        (Toff103 ∷ Toff203 ∷ Toff213 ∷ []) (Toff213 ∷ Toff103 ∷ [])
                        wleaf
                      )
                    )
                    (S3⁻ ∷ S3 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ []) (CX03 ∷ CCZ012 ∷ CX03 ∷ [])
                        wleaf
                      )
                      (Toff213 ∷ CCZ013 ∷ CCZ013 ∷ []) (Toff213 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CK42 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CS14⁻ ∷ S2 ∷ []) (S2 ∷ CS14⁻ ∷ [])
                      (wnode
                        wleaf
                        (CX32 ∷ Toff201 ∷ Toff301 ∷ []) (Toff301 ∷ CX32 ∷ [])
                        wleaf
                      )
                    )
                    (S0 ∷ CS02⁻ ∷ []) (X2 ∷ CS02 ∷ X2 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX13 ∷ Toff203 ∷ []) (Toff203 ∷ CX13 ∷ Toff201 ∷ [])
                        wleaf
                      )
                      (CZ12 ∷ CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                  (CS23 ∷ []) (Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ [])
                        wleaf
                      )
                      (CS34 ∷ Toff214 ∷ []) (Toff214 ∷ CS34 ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ CZ12 ∷ []) (Toff312 ∷ CCZ123 ∷ Toff312 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (CS12⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS12⁻ ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ [])
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX10 ∷ Toff013 ∷ []) (Toff013 ∷ CX10 ∷ [])
                        wleaf
                      )
                      (Toff312 ∷ Toff412 ∷ Toff412 ∷ []) (Toff312 ∷ [])
                      (wnode
                        wleaf
                        (CX23 ∷ Toff302 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX23 ∷ Toff302 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ134 ∷ CX23 ∷ []) (CX23 ∷ CCZ124 ∷ CCZ134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CZ02 ∷ []) (CX23 ∷ CCZ023 ∷ CX23 ∷ [])
                      wleaf
                    )
                  )
                  (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX43 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX43 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ [])
                      (wnode
                        wleaf
                        (CCZ124 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                    )
                    (K0 ∷ CK30⁻ ∷ []) (X3 ∷ CK30 ∷ X3 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K3 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ K3⁻ ∷ []) (Toff324 ∷ [])
                        wleaf
                      )
                      (CS02⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS02⁻ ∷ [])
                      wleaf
                    )
                  )
                )
                (CX41 ∷ Sw12 ∷ []) (Sw12 ∷ CX42 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CK34 ∷ CCZ124 ∷ X3 ∷ []) (X3 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CK43 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK43 ∷ [])
                      (wnode
                        wleaf
                        (K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ []) (Toff413 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (Toff012 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX10 ∷ Toff203 ∷ []) (Toff203 ∷ CX10 ∷ Toff213 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ []) (CCZ234 ∷ [])
                      wleaf
                    )
                  )
                  (Toff213 ∷ Toff214 ∷ []) (Toff214 ∷ Toff213 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (X4 ∷ S4 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ [])
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff201 ∷ CCZ013 ∷ []) (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                    )
                    (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ []) (CX12 ∷ CCZ013 ∷ CX12 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CZ13 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK42 ∷ CS34 ∷ []) (CS34 ∷ CK42 ∷ [])
                        wleaf
                      )
                      (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ [])
                      (wnode
                        wleaf
                        (CK01 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ CX20 ∷ CCZ123 ∷ []) (CX20 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ123 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ X2 ∷ CZ01 ∷ []) (X2 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) (Toff324 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ CX21 ∷ CX12 ∷ []) (Sw12 ∷ [])
                      (wnode
                        wleaf
                        (CS13 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS13 ∷ [])
                        wleaf
                      )
                    )
                    (Toff201 ∷ Toff201 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (S0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ S0 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ CZ34 ∷ []) (Toff234 ∷ CCZ234 ∷ Toff234 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw34 ∷ Toff124 ∷ []) (Toff123 ∷ Sw34 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ023 ∷ [])
                      (wnode
                        wleaf
                        (CX23 ∷ Toff201 ∷ []) (Toff201 ∷ Toff301 ∷ CX23 ∷ [])
                        wleaf
                      )
                    )
                    (CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) (CS01⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff201 ∷ Toff301 ∷ Toff312 ∷ []) (Toff312 ∷ Toff201 ∷ [])
                        wleaf
                      )
                      (K3 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ K3⁻ ∷ []) (Toff312 ∷ [])
                      wleaf
                    )
                  )
                  (Toff013 ∷ Toff013 ∷ []) []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CZ14 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (K1 ∷ CK41 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ [])
                      wleaf
                    )
                    (Sw02 ∷ Sw02 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CS13 ∷ Toff423 ∷ []) (Toff423 ∷ CS13 ∷ [])
                        wleaf
                      )
                      (CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS24 ∷ S4 ∷ []) (S4 ∷ CS24 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ Toff412 ∷ []) (Toff412 ∷ CZ12 ∷ CCZ124 ∷ [])
                      (wnode
                        wleaf
                        (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ []) (CX31 ∷ CCZ234 ∷ CX31 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ ι ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CK43 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ [])
                      (wnode
                        wleaf
                        (CS24 ∷ CS23 ∷ CCZ234 ∷ CS23 ∷ CZ23 ∷ CCZ234 ∷ []) (CS24 ∷ [])
                        wleaf
                      )
                    )
                    (CX24 ∷ CX42 ∷ CX24 ∷ []) (Sw24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S3 ∷ Sw34 ∷ []) (Sw34 ∷ S4 ∷ [])
                        wleaf
                      )
                      (CX30 ∷ Toff213 ∷ []) (Toff213 ∷ CX30 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
                        wleaf
                      )
                      (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
                      (wnode
                        wleaf
                        (Toff103 ∷ Toff203 ∷ Toff203 ∷ []) (Toff103 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CCZ012 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ Toff314 ∷ []) (Toff314 ∷ K2 ∷ [])
                        wleaf
                      )
                      (CX14 ∷ Toff312 ∷ Toff312 ∷ []) (CX14 ∷ [])
                      wleaf
                    )
                  )
                  (CX23 ∷ Toff324 ∷ []) (Toff324 ∷ CX23 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ [])
                      wleaf
                    )
                    (CS03⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS03⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ []) (CZ23 ∷ CCZ234 ∷ CZ23 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ CS12 ∷ []) (CS12 ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CZ24 ∷ Sw12 ∷ []) (Sw12 ∷ CZ14 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS03⁻ ∷ CS03 ∷ []) []
                        wleaf
                      )
                      (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ [])
                      (wnode
                        wleaf
                        (Toff412 ∷ Toff413 ∷ []) (Toff413 ∷ Toff412 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ023 ∷ CZ23 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CCZ134 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ []) (CS02⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ CCZ123 ∷ []) []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX03 ∷ CX03 ∷ []) []
                        wleaf
                      )
                      (CK43 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK43 ∷ [])
                      (wnode
                        wleaf
                        (Toff213 ∷ CCZ134 ∷ CCZ134 ∷ []) (Toff213 ∷ [])
                        wleaf
                      )
                    )
                    (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (ι ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ CZ01 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ012 ∷ [])
                      wleaf
                    )
                  )
                )
                (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CS14 ∷ CS14 ∷ []) (CS14 ∷ CS14 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ [])
                      (wnode
                        wleaf
                        (CS24 ∷ Toff324 ∷ []) (Toff324 ∷ CS24 ∷ [])
                        wleaf
                      )
                    )
                    (CZ02 ∷ CZ12 ∷ CZ12 ∷ []) (CZ02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K3 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K3⁻ ∷ []) (Toff314 ∷ [])
                        wleaf
                      )
                      (CS13⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ S4 ∷ []) (S4 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ [])
                      wleaf
                    )
                    (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff302 ∷ X0 ∷ []) (X0 ∷ CX23 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (Toff134 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (Toff301 ∷ Toff312 ∷ []) (Toff312 ∷ Toff301 ∷ [])
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff103 ∷ CS12 ∷ []) (Toff103 ∷ CS12 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ []) (CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ []) (S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ134 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ134 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff013 ∷ CCZ123 ∷ []) (Toff013 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) (CCZ124 ∷ [])
                      (wnode
                        wleaf
                        (CX31 ∷ Toff412 ∷ []) (Toff412 ∷ CX31 ∷ Toff423 ∷ [])
                        wleaf
                      )
                    )
                    (CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ []) (Toff102 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (Toff301 ∷ Toff213 ∷ [])
                        wleaf
                      )
                      (CS03 ∷ Toff013 ∷ []) (Toff013 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                )
                (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX21 ∷ Toff302 ∷ Toff302 ∷ []) (CX21 ∷ [])
                        wleaf
                      )
                      (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ [])
                      (wnode
                        wleaf
                        (Sw23 ∷ Toff412 ∷ []) (Toff413 ∷ Sw23 ∷ [])
                        wleaf
                      )
                    )
                    (CX31 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX31 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX01 ∷ Toff312 ∷ []) (Toff312 ∷ CX01 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ []) (CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ023 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff312 ∷ CCZ012 ∷ []) (Toff312 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (S3 ∷ CS34⁻ ∷ X4 ∷ []) (X4 ∷ CS34 ∷ [])
                      wleaf
                    )
                    (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ134 ∷ CZ13 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CCZ124 ∷ CCZ124 ∷ Toff314 ∷ []) (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CZ23 ∷ CK43 ∷ CZ23 ∷ []) (CK43 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (X4 ∷ S4 ∷ X4 ∷ []) (ι ∷ S4⁻ ∷ [])
                      (wnode
                        wleaf
                        (K3 ∷ CK03 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CX02 ∷ CCZ013 ∷ []) (CX02 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ CX32 ∷ []) (CX32 ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ CS24 ∷ []) (CS24 ∷ CCZ123 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ CS01 ∷ []) (CS01 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
                      (wnode
                        wleaf
                        (K2⁻ ∷ Toff413 ∷ []) (Toff413 ∷ K2⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CS13 ∷ Toff234 ∷ []) (Toff234 ∷ CS13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ X0 ∷ []) (X0 ∷ S1 ∷ CS01⁻ ∷ [])
                        wleaf
                      )
                      (CX31 ∷ Toff234 ∷ []) (Toff234 ∷ CX31 ∷ [])
                      wleaf
                    )
                  )
                )
                (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX34 ∷ Toff214 ∷ []) (Toff214 ∷ CX34 ∷ Toff213 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CS12 ∷ []) (CS12 ∷ CCZ023 ∷ [])
                      (wnode
                        wleaf
                        (CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ CS24⁻ ∷ CZ24 ∷ CCZ234 ∷ []) (CS34⁻ ∷ [])
                        wleaf
                      )
                    )
                    (S0⁻ ∷ CS01 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX13 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX13 ∷ [])
                        wleaf
                      )
                      (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ [])
                      wleaf
                    )
                  )
                  (CX31 ∷ Toff134 ∷ []) (Toff134 ∷ CX31 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ K2 ∷ []) (K2 ∷ Toff234 ∷ CCZ234 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ134 ∷ CZ14 ∷ [])
                      wleaf
                    )
                    (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ []) (CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS13⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (CS13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS14 ∷ CS34 ∷ []) (CS34 ∷ CS14 ∷ [])
                        wleaf
                      )
                      (CX34 ∷ CX34 ∷ []) []
                      (wnode
                        wleaf
                        (CCZ013 ∷ []) (CX32 ∷ CCZ013 ∷ CX32 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ023 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff124 ∷ Toff324 ∷ Toff312 ∷ []) (Toff312 ∷ Toff124 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CS02 ∷ []) (CS02 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (K0⁻ ∷ K0 ∷ []) []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX12 ∷ Toff314 ∷ Toff314 ∷ []) (CX12 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ023 ∷ [])
                      (wnode
                        wleaf
                        (CX12 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS34 ∷ X0 ∷ []) (X0 ∷ CS34 ∷ [])
                        wleaf
                      )
                      (Sw03 ∷ Toff213 ∷ []) (Toff201 ∷ Sw03 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw12 ∷ Sw14 ∷ []) (Sw24 ∷ Sw12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS24 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ [])
                        wleaf
                      )
                      (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ [])
                      (wnode
                        wleaf
                        (CS12 ∷ CS34 ∷ []) (CS34 ∷ CS12 ∷ [])
                        wleaf
                      )
                    )
                    (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) []
                        wleaf
                      )
                      (CS02 ∷ Toff312 ∷ []) (Toff312 ∷ CS02 ∷ [])
                      wleaf
                    )
                  )
                  (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX42 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX42 ∷ [])
                        wleaf
                      )
                      (S3 ∷ CS34⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S3 ∷ CS34⁻ ∷ [])
                      wleaf
                    )
                    (CCZ013 ∷ []) (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (Toff302 ∷ [])
                        wleaf
                      )
                      (Sw13 ∷ Toff023 ∷ []) (Toff012 ∷ Sw13 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CZ23 ∷ Sw14 ∷ []) (Sw14 ∷ CZ23 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff012 ∷ Toff312 ∷ []) (Toff312 ∷ Toff012 ∷ [])
                        wleaf
                      )
                      (S1 ∷ CS14⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S1 ∷ CS14⁻ ∷ [])
                      (wnode
                        wleaf
                        (CCZ023 ∷ []) (CX01 ∷ CCZ023 ∷ CX01 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ134 ∷ CX24 ∷ []) (CX24 ∷ CCZ123 ∷ CCZ134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff312 ∷ CZ34 ∷ Toff312 ∷ CCZ123 ∷ CZ34 ∷ []) (CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ [])
                      wleaf
                    )
                  )
                  (CX13 ∷ Toff314 ∷ []) (Toff314 ∷ CX13 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ023 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CX23 ∷ CCZ012 ∷ []) (CX23 ∷ CCZ013 ∷ [])
                      (wnode
                        wleaf
                        (S0 ∷ Toff213 ∷ []) (Toff213 ∷ S0 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CX03 ∷ []) (CX03 ∷ CCZ012 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ Toff213 ∷ CCZ134 ∷ []) (Toff213 ∷ CCZ234 ∷ [])
                      wleaf
                    )
                  )
                )
                (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι1 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CX34 ∷ CCZ123 ∷ []) (CX34 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ [])
                      (wnode
                        wleaf
                        (CCZ023 ∷ []) (CX31 ∷ CCZ023 ∷ CX31 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CX03 ∷ []) (CX03 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ []) (CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                  (CX32 ∷ Toff013 ∷ Toff013 ∷ []) (CX32 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ134 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                    (CX02 ∷ CX20 ∷ CX02 ∷ []) (Sw02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff423 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff423 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    [] []
    (wnode
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ [])
                        wleaf
                      )
                      (CZ03 ∷ Toff312 ∷ []) (Toff312 ∷ CZ03 ∷ CCZ012 ∷ [])
                      (wnode
                        wleaf
                        (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CZ13 ∷ Toff302 ∷ []) (Toff302 ∷ CZ13 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ []) (CZ14 ∷ CCZ124 ∷ CZ14 ∷ [])
                      wleaf
                    )
                  )
                  (CS34⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS34⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CS13 ∷ []) (CS13 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ023 ∷ CZ03 ∷ [])
                      (wnode
                        wleaf
                        (CX13 ∷ Toff412 ∷ Toff412 ∷ []) (CX13 ∷ [])
                        wleaf
                      )
                    )
                    (CX30 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX30 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CCZ124 ∷ []) (Toff312 ∷ CCZ134 ∷ Toff312 ∷ [])
                        wleaf
                      )
                      (CS13 ∷ X4 ∷ []) (X4 ∷ CS13 ∷ [])
                      wleaf
                    )
                  )
                )
                (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (X3 ∷ CZ01 ∷ CZ01 ∷ []) (X3 ∷ [])
                        wleaf
                      )
                      (CS14 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS14 ∷ [])
                      (wnode
                        wleaf
                        (CCZ023 ∷ CX10 ∷ []) (CX10 ∷ CCZ123 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CCZ234 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CX31 ∷ Toff023 ∷ []) (Toff023 ∷ CX31 ∷ [])
                      wleaf
                    )
                  )
                  (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ Toff213 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ [])
                      (wnode
                        wleaf
                        (CX12 ∷ Toff413 ∷ Toff413 ∷ []) (CX12 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ013 ∷ CX12 ∷ []) (CX12 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (Toff413 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CZ14 ∷ Sw12 ∷ []) (Sw12 ∷ CZ24 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS14 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS14 ∷ [])
                        wleaf
                      )
                      (CX43 ∷ Toff324 ∷ []) (Toff324 ∷ CX43 ∷ [])
                      (wnode
                        wleaf
                        (CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ []) (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K1⁻ ∷ Toff302 ∷ []) (Toff302 ∷ K1⁻ ∷ [])
                        wleaf
                      )
                      (CS03 ∷ Toff302 ∷ []) (Toff302 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ CZ12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX21 ∷ Toff314 ∷ []) (Toff314 ∷ CX21 ∷ Toff324 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX12 ∷ [])
                      (wnode
                        wleaf
                        (Toff201 ∷ X0 ∷ []) (X0 ∷ CX12 ∷ Toff201 ∷ [])
                        wleaf
                      )
                    )
                    (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (Toff201 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ [])
                        wleaf
                      )
                      (Sw03 ∷ Sw03 ∷ []) []
                      wleaf
                    )
                  )
                )
                (Sw12 ∷ Sw13 ∷ []) (Sw23 ∷ Sw12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX43 ∷ Toff213 ∷ []) (Toff213 ∷ CX43 ∷ Toff214 ∷ [])
                        wleaf
                      )
                      (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ [])
                      (wnode
                        wleaf
                        (CK02⁻ ∷ []) (CS02 ∷ K2⁻ ∷ CS02 ∷ K2 ∷ CS02 ∷ [])
                        wleaf
                      )
                    )
                    (CS12⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS12⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ K2⁻ ∷ []) (Toff234 ∷ [])
                        wleaf
                      )
                      (Sw14 ∷ Toff312 ∷ []) (Toff324 ∷ Sw14 ∷ [])
                      wleaf
                    )
                  )
                  (CS12 ∷ []) (Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CK41 ∷ []) (CZ13 ∷ CK41 ∷ CZ13 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (K2 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CX20 ∷ CX02 ∷ CX20 ∷ []) (Sw02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CS13 ∷ Toff302 ∷ []) (CS13 ∷ Toff302 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ012 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX30 ∷ Toff013 ∷ []) (Toff013 ∷ CX30 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ013 ∷ [])
                      (wnode
                        wleaf
                        (CX34 ∷ Toff413 ∷ []) (Toff413 ∷ CX34 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ []) (CX13 ∷ CCZ124 ∷ CX13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ [])
                        wleaf
                      )
                      (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (Toff302 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX21 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX21 ∷ [])
                        wleaf
                      )
                      (CS14 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS14 ∷ [])
                      (wnode
                        wleaf
                        (Sw13 ∷ Toff412 ∷ []) (Toff423 ∷ Sw13 ∷ [])
                        wleaf
                      )
                    )
                    (CS02⁻ ∷ S1 ∷ []) (S1 ∷ CS02⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CZ13 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                )
                (CX30 ∷ Sw12 ∷ []) (Sw12 ∷ CX30 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) []
                        wleaf
                      )
                      (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ [])
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff413 ∷ []) (Toff413 ∷ CZ13 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ124 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CX41 ∷ Toff324 ∷ []) (Toff324 ∷ CX41 ∷ [])
                      wleaf
                    )
                  )
                  (X4 ∷ CZ01 ∷ CZ01 ∷ []) (X4 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw24 ∷ Toff123 ∷ []) (Toff134 ∷ Sw24 ∷ [])
                        wleaf
                      )
                      (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ CK02 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ K2 ∷ CK02 ∷ S0 ∷ [])
                        wleaf
                      )
                      (CX31 ∷ CX32 ∷ Toff213 ∷ []) (Toff213 ∷ CX31 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CZ23 ∷ CK43 ∷ CZ23 ∷ CZ23 ∷ []) (CZ23 ∷ CK43 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CX01 ∷ []) (CX01 ∷ CCZ023 ∷ [])
                      (wnode
                        wleaf
                        (CK02 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK02 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ123 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CS02 ∷ Sw23 ∷ []) (Sw23 ∷ CS03 ∷ [])
                      wleaf
                    )
                  )
                  (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS13 ∷ Toff301 ∷ []) (Toff301 ∷ CS13 ∷ CS01 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CS14 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS14 ∷ [])
                      (wnode
                        wleaf
                        (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ []) []
                        wleaf
                      )
                    )
                    (CCZ234 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ [])
                        wleaf
                      )
                      (CX14 ∷ Toff213 ∷ []) (Toff213 ∷ CX14 ∷ [])
                      wleaf
                    )
                  )
                )
                (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX34 ∷ Toff213 ∷ Toff213 ∷ []) (CX34 ∷ [])
                        wleaf
                      )
                      (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ [])
                      (wnode
                        wleaf
                        (CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ CX23 ∷ []) (CX23 ∷ CS34⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CS02 ∷ Toff012 ∷ []) (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX31 ∷ Toff203 ∷ Toff203 ∷ []) (CX31 ∷ [])
                        wleaf
                      )
                      (CX23 ∷ Toff312 ∷ []) (Toff312 ∷ CX23 ∷ [])
                      wleaf
                    )
                  )
                  (X4 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ []) (X4 ∷ CX31 ∷ CX31 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ Toff234 ∷ CCZ234 ∷ CZ23 ∷ CK42 ∷ CZ23 ∷ S4 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ123 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                    (CCZ234 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX23 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CX34 ∷ []) (CX34 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CS12 ∷ Toff134 ∷ []) (CS12 ∷ Toff134 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CZ01 ∷ Toff301 ∷ CCZ013 ∷ []) (Toff301 ∷ [])
                      (wnode
                        wleaf
                        (CS12⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ013 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff124 ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ [])
                        wleaf
                      )
                      (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ []) (Toff214 ∷ [])
                      wleaf
                    )
                  )
                  (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CK41 ∷ []) (CZ12 ∷ CK41 ∷ CZ12 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ []) (CX34 ∷ CCZ123 ∷ CX34 ∷ [])
                      (wnode
                        wleaf
                        (Sw13 ∷ Toff214 ∷ []) (Toff234 ∷ Sw13 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ134 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS12 ∷ []) (Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw12 ∷ Sw24 ∷ []) (Sw14 ∷ Sw12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ []) (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ [])
                      (wnode
                        wleaf
                        (Toff413 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff413 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX10 ∷ Toff213 ∷ Toff213 ∷ []) (CX10 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                  (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (Toff023 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS01⁻ ∷ [])
                        wleaf
                      )
                      (S1 ∷ CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ S1 ∷ CS14⁻ ∷ [])
                      (wnode
                        wleaf
                        (CX23 ∷ Toff302 ∷ Toff201 ∷ []) (Toff201 ∷ CX23 ∷ Toff302 ∷ [])
                        wleaf
                      )
                    )
                    (S4⁻ ∷ S4 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ CX12 ∷ []) (CX12 ∷ CCZ013 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CS12⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CK43 ∷ []) (CK43 ∷ CK41 ∷ [])
                        wleaf
                      )
                      (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ [])
                      (wnode
                        wleaf
                        (CCZ124 ∷ K3 ∷ []) (K3 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ Toff013 ∷ CCZ123 ∷ []) (Toff013 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CX03 ∷ CCZ012 ∷ []) (CX03 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ Toff301 ∷ []) (Toff301 ∷ CZ01 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ CCZ234 ∷ [])
                      (wnode
                        wleaf
                        (CK02 ∷ CCZ012 ∷ CK02 ∷ S0 ∷ []) (Toff201 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S0 ∷ X0 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ234 ∷ CZ34 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CZ12 ∷ Toff203 ∷ []) (Toff203 ∷ CZ12 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CX10 ∷ []) (CX10 ∷ CCZ123 ∷ [])
                      (wnode
                        wleaf
                        (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2⁻ ∷ []) (Toff201 ∷ [])
                        wleaf
                      )
                    )
                    (CZ01 ∷ CZ12 ∷ CZ12 ∷ []) (CZ01 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS12 ∷ Toff301 ∷ []) (Toff301 ∷ CS12 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ [])
                      wleaf
                    )
                  )
                  (CZ02 ∷ Toff013 ∷ []) (Toff013 ∷ CZ02 ∷ CCZ123 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (Toff301 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (K3 ∷ CK43 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS12 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS12 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK42 ∷ S4 ∷ []) (S4 ∷ CK42 ∷ [])
                        wleaf
                      )
                      (CX02 ∷ Toff312 ∷ []) (Toff312 ∷ CX02 ∷ Toff301 ∷ [])
                      (wnode
                        wleaf
                        (CK02 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CK02 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX21 ∷ Toff302 ∷ []) (Toff302 ∷ CX21 ∷ [])
                        wleaf
                      )
                      (CS02⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS02⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CK03 ∷ Sw01 ∷ []) (Sw01 ∷ CK13 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CS34 ∷ CS34 ∷ []) (CS34 ∷ CS34 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CK42⁻ ∷ []) (CS24 ∷ K2⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ [])
                      (wnode
                        wleaf
                        (CS24⁻ ∷ CS23⁻ ∷ CCZ234 ∷ CS23⁻ ∷ CZ23 ∷ CCZ234 ∷ []) (CS24⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ123 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CZ24 ∷ Toff213 ∷ []) (Toff213 ∷ CZ24 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CX10 ∷ Toff213 ∷ []) (Toff213 ∷ CX10 ∷ [])
                      wleaf
                    )
                  )
                )
                (CK30 ∷ Sw12 ∷ []) (Sw12 ∷ CK30 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        [] []
                        wleaf
                      )
                      (K0⁻ ∷ CCZ023 ∷ []) (Toff023 ∷ K0⁻ ∷ [])
                      (wnode
                        wleaf
                        (CX14 ∷ CX13 ∷ Toff413 ∷ []) (Toff413 ∷ CX13 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (CCZ023 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff312 ∷ CCZ124 ∷ []) (Toff312 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                  (X4 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) (X4 ∷ CX23 ∷ CX23 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CX24 ∷ CCZ123 ∷ []) (CX24 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CK42 ∷ X4 ∷ []) (X4 ∷ K2 ∷ CK42 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CX34 ∷ Toff412 ∷ []) (Toff412 ∷ CX34 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ134 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CS12⁻ ∷ X4 ∷ []) (X4 ∷ CS12⁻ ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (Sw23 ∷ Sw24 ∷ []) (Sw34 ∷ Sw23 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) []
                        wleaf
                      )
                      (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ [])
                      (wnode
                        wleaf
                        (CCZ124 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ134 ∷ []) (CX42 ∷ CCZ134 ∷ CX42 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ124 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CS02 ∷ CS23 ∷ CCZ023 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ []) (CS02 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS13 ∷ CX30 ∷ []) (CX30 ∷ CS13 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Toff201 ∷ CCZ013 ∷ []) (Toff201 ∷ CCZ123 ∷ [])
                      (wnode
                        wleaf
                        (CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                    )
                    (CS24⁻ ∷ S3 ∷ []) (S3 ∷ CS24⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CK41 ∷ S4 ∷ []) []
                        wleaf
                      )
                      (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (Toff213 ∷ [])
                      wleaf
                    )
                  )
                )
                (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι1 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK42 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ S2 ∷ []) (S2 ∷ CS03⁻ ∷ [])
                      (wnode
                        wleaf
                        (CS34 ∷ CX32 ∷ []) (CX32 ∷ CS34 ∷ [])
                        wleaf
                      )
                    )
                    (CK20⁻ ∷ []) (CS02 ∷ K0⁻ ∷ CS02 ∷ K0 ∷ CS02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX31 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX31 ∷ [])
                        wleaf
                      )
                      (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (Toff214 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ234 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ []) (Toff134 ∷ CS12 ∷ CS23 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ013 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (K3⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K3⁻ ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ CZ12 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS13⁻ ∷ X0 ∷ []) (X0 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (CS12⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS12⁻ ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (Sw34 ∷ Sw34 ∷ []) []
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX10 ∷ CX13 ∷ Toff013 ∷ []) (Toff013 ∷ CX13 ∷ [])
                        wleaf
                      )
                      (Toff412 ∷ Toff423 ∷ []) (Toff423 ∷ Toff412 ∷ [])
                      (wnode
                        wleaf
                        (CCZ023 ∷ CS12 ∷ Toff103 ∷ []) (CS12 ∷ Toff103 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ CX23 ∷ []) (CX23 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS13 ∷ Toff012 ∷ []) (Toff012 ∷ CS13 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CZ02 ∷ CX23 ∷ []) (CX23 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CX43 ∷ CCZ124 ∷ []) (CX43 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ []) (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ [])
                      (wnode
                        wleaf
                        (CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ []) (CCZ023 ∷ [])
                        wleaf
                      )
                    )
                    (S0⁻ ∷ CS03 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S1 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ [])
                        wleaf
                      )
                      (CS13⁻ ∷ X4 ∷ []) (X4 ∷ CS13⁻ ∷ [])
                      wleaf
                    )
                  )
                )
                (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K4 ∷ CK34 ∷ S3 ∷ X3 ∷ []) (X3 ∷ CK34 ∷ [])
                        wleaf
                      )
                      (CK42 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK42 ∷ [])
                      (wnode
                        wleaf
                        (CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ []) (CCZ123 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX01 ∷ Toff203 ∷ []) (Toff203 ∷ CX01 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ CX21 ∷ []) (CX21 ∷ CCZ234 ∷ [])
                      wleaf
                    )
                  )
                  (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CS24 ∷ []) (CS24 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
                      (wnode
                        wleaf
                        (CX21 ∷ Toff423 ∷ Toff423 ∷ []) (CX21 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ CS14 ∷ []) (CS14 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK01 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CK01 ∷ [])
                        wleaf
                      )
                      (CS12 ∷ Toff213 ∷ []) (Toff213 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CS34 ∷ []) (CS34 ∷ CK41 ∷ [])
                        wleaf
                      )
                      (Sw34 ∷ Toff412 ∷ []) (Toff312 ∷ Sw34 ∷ [])
                      (wnode
                        wleaf
                        (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ []) (CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ []) (Toff234 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ Toff314 ∷ []) (Toff314 ∷ CZ14 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ CZ01 ∷ []) (CX03 ∷ CCZ013 ∷ CX03 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ []) (CX21 ∷ CCZ234 ∷ CX21 ∷ [])
                      (wnode
                        wleaf
                        (CS24⁻ ∷ X0 ∷ []) (X0 ∷ CS24⁻ ∷ [])
                        wleaf
                      )
                    )
                    (Toff234 ∷ Toff234 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CK01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ CZ34 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ234 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw01 ∷ Sw12 ∷ []) (Sw02 ∷ Sw01 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) (CX01 ∷ CCZ123 ∷ [])
                      (wnode
                        wleaf
                        (CCZ013 ∷ CCZ123 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                    )
                    (CS01⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS01⁻ ∷ CS12⁻ ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (Toff301 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ []) (CZ01 ∷ CCZ013 ∷ CZ01 ∷ [])
                      wleaf
                    )
                  )
                  (CS13⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS13⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ Toff302 ∷ []) (Toff302 ∷ K1 ∷ [])
                        wleaf
                      )
                      (S3 ∷ CS34⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S3 ∷ CS34⁻ ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (Toff103 ∷ [])
                        wleaf
                      )
                      (Toff214 ∷ X4 ∷ []) (X4 ∷ CX12 ∷ Toff214 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS14 ∷ S4 ∷ []) (S4 ∷ CS14 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ Toff412 ∷ CZ12 ∷ []) (Toff412 ∷ CCZ124 ∷ [])
                      (wnode
                        wleaf
                        (S0 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ S0 ∷ [])
                        wleaf
                      )
                    )
                    (CX31 ∷ Toff023 ∷ Toff023 ∷ []) (CX31 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK34 ∷ CK34⁻ ∷ []) []
                        wleaf
                      )
                      (Toff314 ∷ Toff314 ∷ []) []
                      wleaf
                    )
                  )
                  (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK43 ∷ [])
                        wleaf
                      )
                      (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ [])
                      (wnode
                        wleaf
                        (CS23 ∷ Toff423 ∷ []) (Toff423 ∷ CS23 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S2 ∷ Sw23 ∷ []) (Sw23 ∷ S3 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CZ13 ∷ Toff213 ∷ CCZ123 ∷ []) (Toff213 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK43 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
                        wleaf
                      )
                      (S3 ∷ CS34⁻ ∷ []) (X4 ∷ CS34 ∷ X4 ∷ [])
                      (wnode
                        wleaf
                        (Toff103 ∷ Toff213 ∷ []) (Toff213 ∷ Toff103 ∷ Toff203 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ []) (CZ12 ∷ CCZ012 ∷ CZ12 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K2⁻ ∷ Toff314 ∷ []) (Toff314 ∷ K2⁻ ∷ [])
                        wleaf
                      )
                      (Toff312 ∷ Toff324 ∷ []) (Toff324 ∷ Toff312 ∷ [])
                      wleaf
                    )
                  )
                  (CS13 ∷ CX23 ∷ []) (CX23 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ CZ02 ∷ []) (Toff302 ∷ CCZ023 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (CK42 ∷ []) (CS24⁻ ∷ K2⁻ ∷ CS24⁻ ∷ K2 ∷ CS24⁻ ∷ [])
                      wleaf
                    )
                    (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (Toff412 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CZ23 ∷ []) (Toff423 ∷ CCZ234 ∷ Toff423 ∷ [])
                        wleaf
                      )
                      (CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK43 ∷ [])
                        wleaf
                      )
                      (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ [])
                      (wnode
                        wleaf
                        (CX12 ∷ Toff413 ∷ []) (Toff413 ∷ CX12 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ023 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ023 ∷ CZ23 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS14 ∷ Toff234 ∷ []) (Toff234 ∷ CS14 ∷ [])
                        wleaf
                      )
                      (CS23⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS23⁻ ∷ [])
                      wleaf
                    )
                  )
                  (Toff213 ∷ Toff213 ∷ []) []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff324 ∷ []) (Toff324 ∷ CZ24 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CK42 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK42 ∷ [])
                      (wnode
                        wleaf
                        (K3 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ [])
                        wleaf
                      )
                    )
                    (K3⁻ ∷ K3 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK01 ∷ [])
                        wleaf
                      )
                      (CX41 ∷ Toff234 ∷ Toff234 ∷ []) (CX41 ∷ [])
                      wleaf
                    )
                  )
                )
                (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CK41 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ []) (CZ03 ∷ CCZ023 ∷ CZ03 ∷ [])
                      (wnode
                        wleaf
                        (CS34 ∷ Toff324 ∷ []) (Toff324 ∷ CS34 ∷ CS24 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                    )
                    (CZ02 ∷ Toff012 ∷ []) (Toff012 ∷ CZ02 ∷ CZ12 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ234 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CS13 ∷ CS12 ∷ CCZ123 ∷ CS12 ∷ CZ12 ∷ CCZ123 ∷ []) (CS13 ∷ [])
                      wleaf
                    )
                  )
                  (CS12⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS12⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (S4 ∷ Toff312 ∷ []) (Toff312 ∷ S4 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ [])
                      wleaf
                    )
                    (CS01⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS01⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CX23 ∷ CCZ012 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (CX31 ∷ Toff134 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX31 ∷ Toff134 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ Toff301 ∷ []) (Toff301 ∷ CX12 ∷ [])
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ []) (CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (Toff214 ∷ Toff314 ∷ Toff314 ∷ []) (Toff214 ∷ [])
                      wleaf
                    )
                  )
                  (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ023 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ CCZ123 ∷ [])
                      (wnode
                        wleaf
                        (Toff412 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff412 ∷ [])
                        wleaf
                      )
                    )
                    (K1⁻ ∷ K1 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (K0 ∷ S0 ∷ S0 ∷ K0 ∷ ι ∷ []) (X0 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ []) (CS03⁻ ∷ [])
                      wleaf
                    )
                  )
                )
                (CZ02 ∷ Sw01 ∷ []) (Sw01 ∷ CZ12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff301 ∷ Toff302 ∷ []) (Toff302 ∷ Toff301 ∷ [])
                        wleaf
                      )
                      (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ [])
                      (wnode
                        wleaf
                        (CX32 ∷ Toff413 ∷ Toff413 ∷ []) (CX32 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ134 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ []) (CZ24 ∷ CCZ234 ∷ CZ24 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ023 ∷ CCZ023 ∷ []) []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX24 ∷ Toff314 ∷ []) (Toff314 ∷ CX24 ∷ Toff312 ∷ [])
                        wleaf
                      )
                      (CS24 ∷ X4 ∷ []) (X4 ∷ S2 ∷ CS24⁻ ∷ [])
                      wleaf
                    )
                    (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ []) (CZ13 ∷ CCZ134 ∷ CZ13 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CCZ124 ∷ Toff314 ∷ []) (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK42 ∷ Toff314 ∷ []) (Toff314 ∷ CK42 ∷ [])
                        wleaf
                      )
                      (Toff213 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff213 ∷ [])
                      (wnode
                        wleaf
                        (CK03 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CK03 ∷ [])
                        wleaf
                      )
                    )
                    (CX41 ∷ CX14 ∷ CX41 ∷ []) (Sw14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CX30 ∷ []) (CX30 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CX32 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ CX32 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ123 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ CX03 ∷ []) (CX03 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ []) (CZ13 ∷ CCZ013 ∷ CZ13 ∷ [])
                      (wnode
                        wleaf
                        (K2 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K2⁻ ∷ []) (Toff203 ∷ [])
                        wleaf
                      )
                    )
                    (CS13⁻ ∷ Toff234 ∷ []) (Toff234 ∷ CS13⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S1 ∷ CS01⁻ ∷ Toff213 ∷ []) (Toff213 ∷ S1 ∷ CS01⁻ ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (Toff213 ∷ CCZ012 ∷ [])
                      wleaf
                    )
                  )
                )
                (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX43 ∷ Toff214 ∷ []) (Toff214 ∷ CX43 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ023 ∷ [])
                      (wnode
                        wleaf
                        (CS24⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS24⁻ ∷ [])
                        wleaf
                      )
                    )
                    (S0 ∷ CS01⁻ ∷ []) (X1 ∷ CS01 ∷ X1 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CX13 ∷ CCZ124 ∷ []) (CX13 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ [])
                      wleaf
                    )
                  )
                  (CS12 ∷ CX31 ∷ []) (CX31 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS02 ∷ Toff301 ∷ []) (Toff301 ∷ CS02 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ Toff213 ∷ []) (Toff213 ∷ CX12 ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ CS34 ∷ []) (CS34 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CZ14 ∷ Toff423 ∷ []) (Toff423 ∷ CZ14 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CX23 ∷ CCZ124 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS14 ∷ CS24 ∷ []) (CS24 ∷ CS14 ∷ [])
                        wleaf
                      )
                      (Sw02 ∷ Toff103 ∷ []) (Toff123 ∷ Sw02 ∷ [])
                      (wnode
                        wleaf
                        (CCZ012 ∷ []) (CX23 ∷ CCZ012 ∷ CX23 ∷ [])
                        wleaf
                      )
                    )
                    (Sw13 ∷ Toff012 ∷ []) (Toff023 ∷ Sw13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX12 ∷ Toff301 ∷ Toff301 ∷ []) (CX12 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ CX23 ∷ []) (CX23 ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                  )
                  (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff314 ∷ Toff324 ∷ []) (Toff324 ∷ Toff314 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (CX12 ∷ CCZ023 ∷ [])
                      (wnode
                        wleaf
                        (CCZ124 ∷ CCZ123 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                    )
                    (Toff023 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff023 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff301 ∷ X0 ∷ []) (X0 ∷ CX13 ∷ Toff301 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                )
                (CK42 ∷ Sw12 ∷ []) (Sw12 ∷ CK41 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS24 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS24 ∷ [])
                        wleaf
                      )
                      (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ [])
                      (wnode
                        wleaf
                        (CS12⁻ ∷ CS34 ∷ []) (CS34 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff234 ∷ Toff234 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
                        wleaf
                      )
                      (CX41 ∷ Toff312 ∷ []) (Toff312 ∷ CX41 ∷ Toff324 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CX42 ∷ CCZ134 ∷ []) (CX42 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (S2 ∷ CS24⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S2 ∷ CS24⁻ ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ []) (CX20 ∷ CCZ123 ∷ CX20 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS13⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (CX13 ∷ Toff012 ∷ Toff012 ∷ []) (CX13 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff012 ∷ Toff312 ∷ Toff301 ∷ []) (Toff301 ∷ Toff012 ∷ [])
                        wleaf
                      )
                      (S1 ∷ Toff023 ∷ []) (Toff023 ∷ S1 ∷ [])
                      (wnode
                        wleaf
                        (CCZ124 ∷ []) (CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ [])
                        wleaf
                      )
                    )
                    (CX42 ∷ CX24 ∷ CX42 ∷ []) (Sw24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ [])
                        wleaf
                      )
                      (CX21 ∷ Toff023 ∷ []) (Toff023 ∷ CX21 ∷ [])
                      wleaf
                    )
                  )
                  (CS03 ∷ CX13 ∷ []) (CX13 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01⁻ ∷ Sw03 ∷ []) (Sw03 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
                      (wnode
                        wleaf
                        (K2 ∷ CK02 ∷ S0 ∷ Toff301 ∷ []) (Toff301 ∷ K2 ∷ CK02 ∷ S0 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ013 ∷ CX02 ∷ []) (CX02 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CX30 ∷ []) (CX30 ∷ CCZ123 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CX30 ∷ Toff201 ∷ []) (Toff201 ∷ CX30 ∷ Toff213 ∷ [])
                      wleaf
                    )
                  )
                )
                (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS34 ∷ [])
                        wleaf
                      )
                      (Toff214 ∷ Toff214 ∷ []) []
                      (wnode
                        wleaf
                        (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ [])
                        wleaf
                      )
                    )
                    (K0⁻ ∷ CK20 ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS34⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS34⁻ ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                  (Toff012 ∷ Toff013 ∷ []) (Toff013 ∷ Toff012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (X4 ∷ CZ23 ∷ CZ23 ∷ []) (X4 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ123 ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CK02 ∷ [])
                        wleaf
                      )
                      (CX32 ∷ CX23 ∷ CX32 ∷ []) (Sw23 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
      (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ [])
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CZ13 ∷ CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) (Toff312 ∷ [])
                      (wnode
                        wleaf
                        (K2 ∷ Toff413 ∷ []) (Toff413 ∷ K2 ∷ [])
                        wleaf
                      )
                    )
                    (CX23 ∷ CX32 ∷ CX23 ∷ []) (Sw23 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (X4 ∷ CZ13 ∷ CZ13 ∷ []) (X4 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                  (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ Toff203 ∷ []) (Toff203 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (Toff214 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff214 ∷ [])
                      (wnode
                        wleaf
                        (CCZ023 ∷ CX13 ∷ []) (CX13 ∷ CCZ012 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                    )
                    (CK30⁻ ∷ []) (CS03 ∷ K0⁻ ∷ CS03 ∷ K0 ∷ CS03 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S3 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ [])
                        wleaf
                      )
                      (CS13 ∷ Toff214 ∷ []) (Toff214 ∷ CS13 ∷ [])
                      wleaf
                    )
                  )
                )
                (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CK34 ∷ CCZ124 ∷ CCZ124 ∷ []) (CCZ124 ∷ CK34 ∷ [])
                        wleaf
                      )
                      (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ [])
                      (wnode
                        wleaf
                        (CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ [])
                        wleaf
                      )
                    )
                    (Sw24 ∷ Sw24 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ []) (Toff301 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ Toff013 ∷ Toff013 ∷ []) (CX12 ∷ [])
                      wleaf
                    )
                  )
                  (CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS14⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CX32 ∷ []) (CX32 ∷ CCZ013 ∷ [])
                      (wnode
                        wleaf
                        (Toff312 ∷ CCZ124 ∷ CCZ124 ∷ []) (Toff312 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff413 ∷ Toff413 ∷ []) []
                        wleaf
                      )
                      (Sw03 ∷ Toff201 ∷ []) (Toff213 ∷ Sw03 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CS24 ∷ []) (CS24 ∷ CK41 ∷ [])
                        wleaf
                      )
                      (CX43 ∷ Toff312 ∷ Toff412 ∷ []) (Toff412 ∷ CX43 ∷ [])
                      (wnode
                        wleaf
                        (CCZ124 ∷ CZ12 ∷ []) (Toff412 ∷ CCZ124 ∷ Toff412 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ CZ13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ234 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CS03 ∷ CS02 ∷ CCZ023 ∷ CS02 ∷ CZ02 ∷ CCZ023 ∷ []) (CS03 ∷ [])
                      wleaf
                    )
                  )
                  (Toff012 ∷ Toff012 ∷ []) []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX21 ∷ Toff324 ∷ Toff324 ∷ []) (CX21 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CX21 ∷ []) (CX21 ∷ CCZ023 ∷ [])
                      (wnode
                        wleaf
                        (CS13⁻ ∷ CS24 ∷ []) (CS24 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff201 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ CK01 ∷ S0 ∷ Toff201 ∷ []) (Toff201 ∷ K1 ∷ CK01 ∷ S0 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ012 ∷ CZ01 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw01 ∷ Sw13 ∷ []) (Sw03 ∷ Sw01 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ []) (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ [])
                      (wnode
                        wleaf
                        (Toff301 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Toff301 ∷ [])
                        wleaf
                      )
                    )
                    (CS01 ∷ Toff012 ∷ []) (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) []
                        wleaf
                      )
                      (CCZ013 ∷ CZ01 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                  (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ [])
                        wleaf
                      )
                      (K3 ∷ CK43 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX31 ∷ Toff103 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX31 ∷ Toff103 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ Toff214 ∷ X4 ∷ []) (X4 ∷ Toff214 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (Sw01 ∷ Sw01 ∷ []) []
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS12 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS12 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ123 ∷ [])
                      (wnode
                        wleaf
                        (CS12 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS12 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS24 ∷ CK42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ [])
                        wleaf
                      )
                      (CS14⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS14⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ013 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CS34 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS34 ∷ [])
                      (wnode
                        wleaf
                        (CS24 ∷ Toff423 ∷ []) (Toff423 ∷ CS24 ∷ CS23 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                    )
                    (Toff134 ∷ Toff134 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ []) (CZ13 ∷ CCZ123 ∷ CZ13 ∷ [])
                      wleaf
                    )
                  )
                )
                (CK30⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK31⁻ ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
                        wleaf
                      )
                      (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ [])
                      (wnode
                        wleaf
                        (CS34⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS34⁻ ∷ CS13⁻ ∷ CCZ134 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff201 ∷ CCZ013 ∷ []) (Toff201 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (Toff312 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ CZ12 ∷ Toff412 ∷ CCZ124 ∷ []) (Toff412 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK02 ∷ X0 ∷ []) (X0 ∷ K2 ∷ CK02 ∷ S0 ∷ [])
                        wleaf
                      )
                      (CX31 ∷ CX32 ∷ CX32 ∷ []) (CX31 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CX14 ∷ Sw12 ∷ []) (Sw12 ∷ CX24 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CZ03 ∷ Toff012 ∷ []) (Toff012 ∷ CZ03 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ S0 ∷ []) (S0 ∷ CCZ013 ∷ [])
                      (wnode
                        wleaf
                        (CX32 ∷ Toff413 ∷ []) (Toff413 ∷ CX32 ∷ [])
                        wleaf
                      )
                    )
                    (Sw14 ∷ Sw14 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CCZ012 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CS02⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (CS13⁻ ∷ S2 ∷ []) (S2 ∷ CS13⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS13 ∷ CS01 ∷ CCZ013 ∷ CS01 ∷ CZ01 ∷ CCZ013 ∷ []) (CS13 ∷ [])
                        wleaf
                      )
                      (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ [])
                      (wnode
                        wleaf
                        (CK01 ∷ CK01 ∷ S0 ∷ []) []
                        wleaf
                      )
                    )
                    (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (Toff301 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ [])
                        wleaf
                      )
                      (CX41 ∷ Toff213 ∷ []) (Toff213 ∷ CX41 ∷ Toff234 ∷ [])
                      wleaf
                    )
                  )
                )
                (CZ12 ∷ Sw12 ∷ []) (Sw12 ∷ CZ12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw34 ∷ Toff123 ∷ []) (Toff124 ∷ Sw34 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CZ03 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ023 ∷ [])
                      (wnode
                        wleaf
                        (CS24 ∷ CS34⁻ ∷ CS24⁻ ∷ []) (CS34⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CS02⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX13 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX13 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CZ12 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ Toff301 ∷ []) (Toff301 ∷ K2 ∷ [])
                        wleaf
                      )
                      (CS24 ∷ Toff314 ∷ []) (Toff314 ∷ CS24 ∷ [])
                      wleaf
                    )
                    (CCZ013 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX24 ∷ CX23 ∷ Toff423 ∷ []) (Toff423 ∷ CX23 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ []) (Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS13 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13 ∷ [])
                        wleaf
                      )
                      (CX20 ∷ Toff301 ∷ []) (Toff301 ∷ CX20 ∷ Toff312 ∷ [])
                      (wnode
                        wleaf
                        (CS23 ∷ Toff413 ∷ []) (Toff413 ∷ CS23 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ []) (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CCZ234 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
                        wleaf
                      )
                      (CS14⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS14⁻ ∷ [])
                      wleaf
                    )
                  )
                  (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ Toff124 ∷ CCZ124 ∷ CZ12 ∷ CK41 ∷ CZ12 ∷ S4 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CX34 ∷ []) (CX34 ∷ CCZ123 ∷ CCZ124 ∷ [])
                      (wnode
                        wleaf
                        (K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ []) (Toff412 ∷ [])
                        wleaf
                      )
                    )
                    (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S2 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CZ13 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw14 ∷ Sw23 ∷ []) (Sw23 ∷ Sw14 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX12 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX12 ∷ [])
                        wleaf
                      )
                      (S2 ∷ Toff013 ∷ []) (Toff013 ∷ S2 ∷ [])
                      (wnode
                        wleaf
                        (CX32 ∷ Toff412 ∷ []) (Toff412 ∷ CX32 ∷ Toff413 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CCZ013 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ CZ24 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ234 ∷ [])
                      wleaf
                    )
                  )
                  (CS14⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS14⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS02⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS02⁻ ∷ [])
                        wleaf
                      )
                      (S2 ∷ CS24⁻ ∷ X4 ∷ []) (X4 ∷ CS24 ∷ [])
                      (wnode
                        wleaf
                        (CS13⁻ ∷ Toff201 ∷ []) (Toff201 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ023 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CZ13 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ CS13⁻ ∷ CZ13 ∷ CCZ123 ∷ []) (CS12⁻ ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ [])
                        wleaf
                      )
                      (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ [])
                      (wnode
                        wleaf
                        (CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CK03 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX03 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX03 ∷ [])
                        wleaf
                      )
                      (CX32 ∷ Toff314 ∷ []) (Toff314 ∷ CX32 ∷ Toff214 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ134 ∷ []) (X2 ∷ CCZ134 ∷ X2 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ CS01⁻ ∷ CZ01 ∷ CCZ013 ∷ []) (CS13⁻ ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CZ13 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ [])
                      (wnode
                        wleaf
                        (CK03 ∷ CCZ023 ∷ CK03 ∷ S0 ∷ []) (Toff302 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ123 ∷ CCZ134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (CX41 ∷ Toff234 ∷ []) (Toff234 ∷ CX41 ∷ [])
                      wleaf
                    )
                  )
                )
                (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (X4 ∷ CZ12 ∷ CZ12 ∷ []) (X4 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ123 ∷ [])
                      (wnode
                        wleaf
                        (Toff201 ∷ Toff301 ∷ Toff301 ∷ []) (Toff201 ∷ [])
                        wleaf
                      )
                    )
                    (CK10 ∷ []) (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0 ∷ CS01⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff201 ∷ Toff301 ∷ []) (Toff301 ∷ Toff201 ∷ [])
                        wleaf
                      )
                      (CX32 ∷ Toff013 ∷ []) (Toff013 ∷ CX32 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ123 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ CX13 ∷ Toff213 ∷ []) (Toff213 ∷ CX13 ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ CS03 ∷ []) (CS03 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS12⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                      (CX20 ∷ CX23 ∷ Toff023 ∷ []) (Toff023 ∷ CX23 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S4 ∷ [])
                        wleaf
                      )
                      (CX02 ∷ Toff301 ∷ Toff301 ∷ []) (CX02 ∷ [])
                      (wnode
                        wleaf
                        (CCZ134 ∷ CX23 ∷ CCZ124 ∷ []) (CX23 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) (CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX21 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX21 ∷ [])
                        wleaf
                      )
                      (CX23 ∷ Toff314 ∷ []) (Toff314 ∷ CX23 ∷ [])
                      wleaf
                    )
                  )
                  (CK03 ∷ Sw12 ∷ []) (Sw12 ∷ CK03 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ [])
                        wleaf
                      )
                      (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff314 ∷ [])
                      (wnode
                        wleaf
                        (X0 ∷ CZ34 ∷ CZ34 ∷ []) (X0 ∷ [])
                        wleaf
                      )
                    )
                    (CS23⁻ ∷ Toff134 ∷ []) (Toff134 ∷ CS23⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX13 ∷ Toff301 ∷ X0 ∷ []) (X0 ∷ Toff301 ∷ [])
                        wleaf
                      )
                      (CX03 ∷ Toff201 ∷ Toff201 ∷ []) (CX03 ∷ [])
                      wleaf
                    )
                  )
                )
                (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                      (K0⁻ ∷ CCZ013 ∷ []) (Toff013 ∷ K0⁻ ∷ [])
                      (wnode
                        wleaf
                        (CX14 ∷ Toff413 ∷ []) (Toff413 ∷ CX14 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ K0⁻ ∷ []) (K0⁻ ∷ Toff012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ Toff301 ∷ CZ01 ∷ []) (Toff301 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CX14 ∷ Toff312 ∷ []) (Toff312 ∷ CX14 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX24 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX24 ∷ [])
                        wleaf
                      )
                      (K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ []) (Toff234 ∷ K3 ∷ CK43 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ CZ12 ∷ Toff312 ∷ CCZ123 ∷ []) (Toff312 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CZ24 ∷ Toff413 ∷ []) (Toff413 ∷ CZ24 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CS03 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS03 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CX42 ∷ Sw23 ∷ []) (Sw23 ∷ CX43 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ CS13 ∷ CCZ013 ∷ CS13 ∷ CZ13 ∷ CCZ013 ∷ []) (CS01 ∷ [])
                        wleaf
                      )
                      (Toff213 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff213 ∷ [])
                      (wnode
                        wleaf
                        (CCZ134 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff203 ∷ Toff213 ∷ []) (Toff213 ∷ Toff203 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CZ23 ∷ []) (Toff023 ∷ CCZ023 ∷ Toff023 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ [])
                      (wnode
                        wleaf
                        (CS12⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                    )
                    (Toff324 ∷ Toff324 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff423 ∷ CCZ123 ∷ []) (Toff423 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CS24 ∷ CS24 ∷ []) (CS24 ∷ CS24 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CS14⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS14⁻ ∷ [])
                      (wnode
                        wleaf
                        (CS34⁻ ∷ CX32 ∷ []) (CX32 ∷ CS34⁻ ∷ [])
                        wleaf
                      )
                    )
                    (S0⁻ ∷ CS02 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX13 ∷ Toff201 ∷ Toff201 ∷ []) (CX13 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Toff214 ∷ CCZ134 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                  (CX32 ∷ Toff012 ∷ []) (Toff012 ∷ CX32 ∷ Toff013 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ X4 ∷ CZ23 ∷ []) (X4 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (K3 ∷ Toff214 ∷ []) (Toff214 ∷ K3 ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ CZ12 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (CX23 ∷ Toff013 ∷ []) (Toff013 ∷ CX23 ∷ Toff012 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (Sw12 ∷ Sw12 ∷ []) []
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CX13 ∷ CCZ124 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ [])
                      (wnode
                        wleaf
                        (CS13 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ []) (CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ S4 ∷ []) (S4 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ []) (CZ02 ∷ CCZ023 ∷ CZ02 ∷ [])
                      wleaf
                    )
                  )
                  (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι1 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff203 ∷ CCZ013 ∷ []) (Toff203 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ []) (CX43 ∷ CCZ124 ∷ CX43 ∷ [])
                      (wnode
                        wleaf
                        (Sw13 ∷ Toff423 ∷ []) (Toff412 ∷ Sw13 ∷ [])
                        wleaf
                      )
                    )
                    (K0⁻ ∷ CK30 ∷ []) (X3 ∷ CK30⁻ ∷ X3 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS13 ∷ CS12 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CS13⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS13⁻ ∷ [])
                      wleaf
                    )
                  )
                )
                (CX41 ∷ Sw23 ∷ []) (Sw23 ∷ CX41 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ CCZ124 ∷ []) (CCZ124 ∷ CK34⁻ ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ S2 ∷ []) (S2 ∷ CCZ123 ∷ [])
                      (wnode
                        wleaf
                        (CS13⁻ ∷ Toff203 ∷ []) (Toff203 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ Toff213 ∷ CCZ134 ∷ []) (Toff213 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (Toff214 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (S4 ∷ X4 ∷ []) (X4 ∷ ι ∷ S4⁻ ∷ [])
                      (wnode
                        wleaf
                        (CCZ123 ∷ CCZ013 ∷ Toff201 ∷ CCZ013 ∷ []) (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                    )
                    (K4⁻ ∷ K4 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ []) (CX21 ∷ CCZ023 ∷ CX21 ∷ [])
                        wleaf
                      )
                      (CS13 ∷ Toff213 ∷ []) (Toff213 ∷ CS13 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS34 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS34 ∷ [])
                        wleaf
                      )
                      (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ [])
                      (wnode
                        wleaf
                        (K3 ∷ CK03 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CS23 ∷ []) (CS23 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX20 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX20 ∷ [])
                        wleaf
                      )
                      (CX23 ∷ CX23 ∷ []) []
                      wleaf
                    )
                  )
                  (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS12 ∷ Toff302 ∷ []) (Toff302 ∷ CS12 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CX21 ∷ []) (CX21 ∷ CCZ234 ∷ CCZ134 ∷ [])
                      (wnode
                        wleaf
                        (Toff203 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff203 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ012 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (X0 ∷ S0 ∷ []) (ι ∷ S0⁻ ∷ X0 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ []) (CZ34 ∷ CCZ234 ∷ CZ34 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ []) (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ [])
                        wleaf
                      )
                      (CX01 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX01 ∷ [])
                      (wnode
                        wleaf
                        (CCZ234 ∷ CZ24 ∷ CX23 ∷ []) (CX23 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                    )
                    (CZ01 ∷ Toff012 ∷ []) (Toff012 ∷ CZ01 ∷ CZ12 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CCZ124 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (Toff312 ∷ CCZ012 ∷ CCZ012 ∷ []) (Toff312 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ CCZ013 ∷ []) []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CZ14 ∷ []) (Toff314 ∷ CCZ134 ∷ Toff314 ∷ [])
                        wleaf
                      )
                      (K2 ∷ CK42 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff103 ∷ X0 ∷ []) (X0 ∷ CX31 ∷ Toff103 ∷ [])
                        wleaf
                      )
                      (CS02⁻ ∷ X4 ∷ []) (X4 ∷ CS02⁻ ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS34 ∷ S4 ∷ []) (S4 ∷ CS34 ∷ [])
                        wleaf
                      )
                      (CX20 ∷ Toff312 ∷ []) (Toff312 ∷ CX20 ∷ [])
                      (wnode
                        wleaf
                        (Toff423 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff423 ∷ [])
                        wleaf
                      )
                    )
                    (CX13 ∷ CX31 ∷ CX13 ∷ []) (Sw13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CS23 ∷ []) (CS23 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                  (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CX32 ∷ CCZ013 ∷ []) (CX32 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (K2 ∷ CCZ123 ∷ []) (Toff213 ∷ K2 ∷ [])
                      (wnode
                        wleaf
                        (CS24⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS24⁻ ∷ CS23⁻ ∷ CCZ234 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ123 ∷ CX24 ∷ []) (CX24 ∷ CCZ123 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff213 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff213 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ234 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                )
                (CZ12 ∷ Sw03 ∷ []) (Sw03 ∷ CZ12 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
                        wleaf
                      )
                      (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
                      (wnode
                        wleaf
                        (CZ13 ∷ CCZ134 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ013 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff201 ∷ CCZ013 ∷ CCZ013 ∷ []) (Toff201 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ234 ∷ [])
                      wleaf
                    )
                  )
                  (CS12 ∷ Toff324 ∷ []) (Toff324 ∷ CS12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ023 ∷ CZ02 ∷ [])
                        wleaf
                      )
                      (K2 ∷ CK42 ∷ S4 ∷ Toff314 ∷ []) (Toff314 ∷ K2 ∷ CK42 ∷ S4 ∷ [])
                      wleaf
                    )
                    (Toff412 ∷ Toff412 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ234 ∷ CZ23 ∷ [])
                        wleaf
                      )
                      (CS12 ∷ Toff314 ∷ []) (Toff314 ∷ CS12 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS03 ∷ CS03⁻ ∷ []) []
                        wleaf
                      )
                      (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ [])
                      (wnode
                        wleaf
                        (CX23 ∷ Toff412 ∷ Toff412 ∷ []) (CX23 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CCZ134 ∷ []) (Toff234 ∷ CCZ123 ∷ Toff234 ∷ [])
                        wleaf
                      )
                      (CS02 ∷ Toff023 ∷ []) (Toff023 ∷ CS02 ∷ CS23 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ123 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) (CX41 ∷ CCZ123 ∷ [])
                      (wnode
                        wleaf
                        (CCZ012 ∷ Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) (CCZ123 ∷ CCZ012 ∷ Toff301 ∷ [])
                        wleaf
                      )
                    )
                    (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ CZ01 ∷ []) (Toff201 ∷ CCZ012 ∷ Toff201 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw01 ∷ ι1 ∷ []) (ι1 ∷ Sw01 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ []) (CX41 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ [])
                      (wnode
                        wleaf
                        (CS34 ∷ CS24 ∷ CCZ234 ∷ CS24 ∷ CZ24 ∷ CCZ234 ∷ []) (CS34 ∷ [])
                        wleaf
                      )
                    )
                    (CX20 ∷ Toff012 ∷ []) (Toff012 ∷ CX20 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CX31 ∷ CCZ234 ∷ []) (CX31 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CS12⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS12⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ [])
                      wleaf
                    )
                    (CCZ012 ∷ []) (CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS13 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ [])
                        wleaf
                      )
                      (K1⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K1⁻ ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX31 ∷ Toff134 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX31 ∷ Toff134 ∷ [])
                        wleaf
                      )
                      (CX20 ∷ Toff312 ∷ Toff312 ∷ []) (CX20 ∷ [])
                      (wnode
                        wleaf
                        (CX31 ∷ Toff103 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX31 ∷ Toff103 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ []) (CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (Toff302 ∷ [])
                      wleaf
                    )
                  )
                  (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ CX21 ∷ CCZ023 ∷ []) (CX21 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
                      (wnode
                        wleaf
                        (CX31 ∷ Toff423 ∷ Toff423 ∷ []) (CX31 ∷ [])
                        wleaf
                      )
                    )
                    (CS34⁻ ∷ S1 ∷ Toff134 ∷ S1⁻ ∷ []) (Toff134 ∷ CCZ134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS01⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS01⁻ ∷ [])
                        wleaf
                      )
                      (CS13 ∷ Toff013 ∷ []) (Toff013 ∷ CS13 ∷ [])
                      wleaf
                    )
                  )
                )
                (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) []
                        wleaf
                      )
                      (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ [])
                      (wnode
                        wleaf
                        (Sw23 ∷ Toff134 ∷ []) (Toff124 ∷ Sw23 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff302 ∷ Toff312 ∷ []) (Toff312 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ234 ∷ CZ24 ∷ [])
                      wleaf
                    )
                  )
                  (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX24 ∷ Toff312 ∷ Toff312 ∷ []) (CX24 ∷ [])
                        wleaf
                      )
                      (S3 ∷ CS34⁻ ∷ Toff213 ∷ []) (Toff213 ∷ S3 ∷ CS34⁻ ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ []) (CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CZ13 ∷ Toff413 ∷ CCZ134 ∷ []) (Toff413 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CZ23 ∷ Toff201 ∷ []) (Toff201 ∷ CZ23 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
                      (wnode
                        wleaf
                        (CK03 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CK03 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX02 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX02 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ [])
                      wleaf
                    )
                  )
                  (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (Toff213 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ CS13⁻ ∷ CS01⁻ ∷ []) (CS13⁻ ∷ [])
                        wleaf
                      )
                      (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
                      (wnode
                        wleaf
                        (K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ []) (Toff203 ∷ [])
                        wleaf
                      )
                    )
                    (Toff013 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (Toff213 ∷ Toff234 ∷ []) (Toff234 ∷ Toff213 ∷ [])
                      wleaf
                    )
                  )
                )
                (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff213 ∷ CCZ013 ∷ []) (Toff213 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ124 ∷ CZ14 ∷ [])
                      (wnode
                        wleaf
                        (CX23 ∷ Toff301 ∷ []) (Toff301 ∷ CX23 ∷ [])
                        wleaf
                      )
                    )
                    (K0 ∷ CK10⁻ ∷ []) (X1 ∷ CK10 ∷ X1 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX31 ∷ Toff201 ∷ []) (Toff201 ∷ CX31 ∷ Toff203 ∷ [])
                        wleaf
                      )
                      (CS24⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS24⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CS23 ∷ Toff134 ∷ []) (Toff134 ∷ CS23 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CK42 ∷ []) (CZ23 ∷ CK42 ∷ CZ23 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CZ14 ∷ Toff314 ∷ CCZ134 ∷ []) (Toff314 ∷ [])
                      wleaf
                    )
                    (CCZ123 ∷ []) (CCZ134 ∷ Toff413 ∷ CZ24 ∷ Toff413 ∷ CCZ134 ∷ CZ24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ [])
                        wleaf
                      )
                      (CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS13⁻ ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK42 ∷ CS14 ∷ []) (CS14 ∷ CK42 ∷ [])
                        wleaf
                      )
                      (CS14⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS14⁻ ∷ [])
                      (wnode
                        wleaf
                        (CCZ012 ∷ CX32 ∷ []) (CX32 ∷ CCZ013 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                    )
                    (Sw13 ∷ Toff203 ∷ []) (Toff201 ∷ Sw13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1⁻ ∷ []) (Toff124 ∷ [])
                        wleaf
                      )
                      (CS02 ∷ CS03⁻ ∷ CS02⁻ ∷ []) (CS03⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (Toff314 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ [])
                      (wnode
                        wleaf
                        (CX12 ∷ Toff201 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX12 ∷ Toff201 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ234 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS34⁻ ∷ X0 ∷ []) (X0 ∷ CS34⁻ ∷ [])
                        wleaf
                      )
                      (CCZ123 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ012 ∷ [])
                      wleaf
                    )
                  )
                )
                (CK32 ∷ Sw12 ∷ []) (Sw12 ∷ CK31 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS34 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ [])
                        wleaf
                      )
                      (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ [])
                      (wnode
                        wleaf
                        (CS12⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                    )
                    (S0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) (S0 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K2⁻ ∷ []) (Toff234 ∷ [])
                        wleaf
                      )
                      (CX24 ∷ Toff312 ∷ []) (Toff312 ∷ CX24 ∷ [])
                      wleaf
                    )
                  )
                  (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff302 ∷ CCZ012 ∷ []) (Toff302 ∷ CCZ123 ∷ [])
                        wleaf
                      )
                      (K1 ∷ CK41 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CS13 ∷ Toff412 ∷ []) (Toff412 ∷ CS13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS13 ∷ Toff413 ∷ []) (Toff413 ∷ CS13 ∷ [])
                        wleaf
                      )
                      (Sw13 ∷ Toff201 ∷ []) (Toff203 ∷ Sw13 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CZ14 ∷ Sw23 ∷ []) (Sw23 ∷ CZ14 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ X3 ∷ CZ01 ∷ []) (X3 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
                      (wnode
                        wleaf
                        (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (Toff413 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ134 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ134 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ Toff023 ∷ []) (Toff023 ∷ CX12 ∷ Toff013 ∷ [])
                      wleaf
                    )
                  )
                  (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX42 ∷ Toff312 ∷ []) (Toff312 ∷ CX42 ∷ Toff314 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ []) (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ [])
                      (wnode
                        wleaf
                        (CX12 ∷ Toff423 ∷ []) (Toff423 ∷ CX12 ∷ Toff413 ∷ [])
                        wleaf
                      )
                    )
                    (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ [])
                        wleaf
                      )
                      (CX13 ∷ Toff201 ∷ []) (Toff201 ∷ CX13 ∷ [])
                      wleaf
                    )
                  )
                )
                (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ123 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ123 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ124 ∷ [])
                      (wnode
                        wleaf
                        (CX13 ∷ Toff423 ∷ []) (Toff423 ∷ CX13 ∷ Toff412 ∷ [])
                        wleaf
                      )
                    )
                    (CCZ012 ∷ CZ03 ∷ []) (CZ03 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CX23 ∷ Toff324 ∷ X4 ∷ []) (X4 ∷ Toff324 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ134 ∷ []) (CX32 ∷ CCZ134 ∷ CX32 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ Toff302 ∷ CCZ012 ∷ []) (Toff302 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CZ14 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                    (CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ []) (CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

windowsP : WTree
windowsP =
  (wnode
    (wnode
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CX24 ∷ []) (CX24 ∷ CCZ012 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                    (CK40 ∷ []) (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ []) (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ CX31 ∷ []) (CX31 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX30 ∷ Toff204 ∷ []) (Toff204 ∷ CX30 ∷ Toff234 ∷ [])
                        wleaf
                      )
                      (CS12⁻ ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS12⁻ ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) (CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX10 ∷ Toff413 ∷ []) (Toff413 ∷ CX10 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ134 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CX04 ∷ []) (CX04 ∷ CCZ012 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (CS04⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS02 ∷ Toff401 ∷ []) (Toff401 ∷ CS02 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                  (CX21 ∷ Toff024 ∷ []) (Toff024 ∷ CX21 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff234 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff234 ∷ [])
                        wleaf
                      )
                      (CS02⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS02⁻ ∷ [])
                      wleaf
                    )
                    (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS02⁻ ∷ Toff402 ∷ []) (Toff402 ∷ CS02⁻ ∷ [])
                        wleaf
                      )
                      (Sw34 ∷ Toff104 ∷ []) (Toff103 ∷ Sw34 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (X4 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) (X4 ∷ CX13 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX42 ∷ Toff304 ∷ []) (Toff304 ∷ CX42 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CS34 ∷ []) (CS34 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (CX41 ∷ Toff034 ∷ Toff034 ∷ []) (CX41 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX03 ∷ Toff402 ∷ []) (Toff402 ∷ CX03 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ CX12 ∷ Toff214 ∷ []) (CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ CZ14 ∷ []) (Toff014 ∷ CCZ014 ∷ Toff014 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS14⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS14⁻ ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                    (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ014 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CK40 ∷ []) (CZ02 ∷ CK40 ∷ CZ02 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                )
                (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ []) (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
                        wleaf
                      )
                      (CS03 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CS03 ∷ [])
                      wleaf
                    )
                    (Toff304 ∷ Toff304 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CS03⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS03⁻ ∷ [])
                        wleaf
                      )
                      (CS03 ∷ CS24 ∷ []) (CS24 ∷ CS03 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ S0⁻ ∷ []) (S0⁻ ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS14⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS14⁻ ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) (CX14 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                    (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ []) (CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CCZ134 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CX42 ∷ Toff034 ∷ Toff034 ∷ []) (CX42 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ [])
                        wleaf
                      )
                      (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) (Toff314 ∷ Toff013 ∷ [])
                      wleaf
                    )
                  )
                  (CX41 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX41 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX04 ∷ Toff201 ∷ []) (Toff201 ∷ CX04 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ []) (CX12 ∷ CCZ014 ∷ CX12 ∷ [])
                      wleaf
                    )
                    (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) (Toff413 ∷ Toff301 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) (CX34 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                )
                (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw04 ∷ Toff324 ∷ []) (Toff302 ∷ Sw04 ∷ [])
                        wleaf
                      )
                      (Toff024 ∷ Toff034 ∷ []) (Toff034 ∷ Toff024 ∷ [])
                      wleaf
                    )
                    (Toff401 ∷ Toff412 ∷ []) (Toff412 ∷ Toff401 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff402 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Toff402 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ S4 ∷ []) (S4 ∷ CS04 ∷ [])
                      wleaf
                    )
                  )
                  (Sw13 ∷ Toff034 ∷ []) (Toff014 ∷ Sw13 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ []) (CCZ014 ∷ [])
                        wleaf
                      )
                      (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ [])
                      wleaf
                    )
                    (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX31 ∷ CCZ034 ∷ Toff103 ∷ CCZ034 ∷ []) (CX31 ∷ Toff103 ∷ [])
                        wleaf
                      )
                      (CX41 ∷ Toff012 ∷ []) (Toff012 ∷ CX41 ∷ Toff024 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ023 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ023 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (Toff304 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                    (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (Toff401 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff402 ∷ CCZ023 ∷ []) (Toff402 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ023 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS34 ∷ Toff203 ∷ []) (Toff203 ∷ CS34 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CS04⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
                        wleaf
                      )
                      (Toff203 ∷ Toff204 ∷ []) (Toff204 ∷ Toff203 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ []) (CCZ034 ∷ CCZ024 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (S0 ∷ CS04⁻ ∷ Toff324 ∷ []) (Toff324 ∷ S0 ∷ CS04⁻ ∷ [])
                      wleaf
                    )
                    (CS13 ∷ Toff401 ∷ []) (Toff401 ∷ CS13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ034 ∷ CZ03 ∷ [])
                        wleaf
                      )
                      (CK42 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CK42 ∷ [])
                      wleaf
                    )
                  )
                  (CZ34 ∷ Toff034 ∷ []) (Toff034 ∷ CZ34 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K0 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ [])
                        wleaf
                      )
                      (K2⁻ ∷ Toff034 ∷ []) (Toff034 ∷ K2⁻ ∷ [])
                      wleaf
                    )
                    (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K3 ∷ CK03 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ [])
                        wleaf
                      )
                      (Toff302 ∷ Toff324 ∷ []) (Toff324 ∷ Toff302 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CCZ034 ∷ CCZ034 ∷ []) []
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ034 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CX43 ∷ Toff024 ∷ []) (Toff024 ∷ CX43 ∷ [])
                      wleaf
                    )
                    (CX24 ∷ Toff023 ∷ []) (Toff023 ∷ CX24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX13 ∷ Toff301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX13 ∷ Toff301 ∷ [])
                        wleaf
                      )
                      (CX03 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX03 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ024 ∷ CCZ024 ∷ []) []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ013 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (S4 ∷ Toff013 ∷ []) (Toff013 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ012 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ Toff412 ∷ []) (Toff412 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (Toff024 ∷ CCZ014 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ CX40 ∷ CCZ134 ∷ []) (CX40 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (Sw24 ∷ Toff014 ∷ []) (Toff012 ∷ Sw24 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CS03 ∷ []) (CS03 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (X0 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ023 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ023 ∷ CCZ234 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ124 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CX01 ∷ Toff204 ∷ Toff204 ∷ []) (CX01 ∷ [])
                      wleaf
                    )
                    (S2 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) (S2 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ CCZ023 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ023 ∷ CCZ234 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ234 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX30 ∷ Toff423 ∷ Toff423 ∷ []) (CX30 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CX34 ∷ CCZ013 ∷ []) (CX34 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX10 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX10 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ124 ∷ [])
                      wleaf
                    )
                    (CS14⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS14⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS02⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS02⁻ ∷ [])
                        wleaf
                      )
                      (K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ Toff104 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ S4 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                    (CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ CS13 ∷ []) (CS13 ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ124 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ Toff024 ∷ []) (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K3 ∷ Toff402 ∷ []) (Toff402 ∷ K3 ∷ [])
                        wleaf
                      )
                      (CX03 ∷ Toff024 ∷ []) (Toff024 ∷ Toff324 ∷ CX03 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CCZ024 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ024 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ []) (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
                        wleaf
                      )
                      (CS24 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) (CS24 ∷ [])
                      wleaf
                    )
                    (CCZ234 ∷ CS02 ∷ []) (CS02 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (CX31 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) (CX31 ∷ Toff134 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ013 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX30 ∷ Toff234 ∷ []) (Toff234 ∷ CX30 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ []) (CX10 ∷ CCZ124 ∷ CX10 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS34 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CS34 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CS01 ∷ []) (CS01 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (S4 ∷ Toff302 ∷ []) (Toff302 ∷ S4 ∷ [])
                        wleaf
                      )
                      (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                    (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (Toff304 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CK43 ∷ CS04 ∷ []) (CS04 ∷ CK43 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ014 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ []) (Toff014 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ []) (CX41 ∷ CCZ024 ∷ CX41 ∷ [])
                      wleaf
                    )
                    (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS01⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS01⁻ ∷ [])
                        wleaf
                      )
                      (CX23 ∷ Toff034 ∷ []) (Toff034 ∷ CX23 ∷ Toff024 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ []) (CX04 ∷ CCZ012 ∷ CX04 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                    (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff402 ∷ CCZ012 ∷ []) (Toff402 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CS34⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS34⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX01 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX01 ∷ [])
                        wleaf
                      )
                      (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ [])
                      wleaf
                    )
                    (CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS12⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ []) (Toff403 ∷ CCZ013 ∷ Toff403 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CK41 ∷ CCZ013 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK41 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ CZ34 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ []) (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ [])
                        wleaf
                      )
                      (CS13 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS13 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ []) (CZ03 ∷ CCZ034 ∷ CZ03 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ CZ03 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (Toff024 ∷ X3 ∷ []) (X3 ∷ Toff024 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CZ04 ∷ []) (CZ04 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ []) (CX30 ∷ CCZ134 ∷ CX30 ∷ [])
                      wleaf
                    )
                    (Toff204 ∷ Toff214 ∷ []) (Toff214 ∷ Toff204 ∷ [])
                    (wnode
                      wleaf
                      (Sw03 ∷ Toff014 ∷ []) (Toff314 ∷ Sw03 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ [])
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CS02 ∷ []) (CS02 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                    (K0 ∷ CK40⁻ ∷ []) (X4 ∷ CK40 ∷ X4 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S4 ∷ CS04⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ S4 ∷ CS04⁻ ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ024 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (S3 ∷ CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ S3 ∷ CS34⁻ ∷ [])
                      wleaf
                    )
                    (CS04 ∷ CS03 ∷ CCZ034 ∷ CS03 ∷ CZ03 ∷ CCZ034 ∷ []) (CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ CCZ034 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CX21 ∷ []) (CX21 ∷ CCZ024 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Sw04 ∷ []) (Sw04 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CS13 ∷ Toff014 ∷ []) (Toff014 ∷ CS13 ∷ [])
                      wleaf
                    )
                    (CS03⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS03⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS03 ∷ Toff423 ∷ []) (Toff423 ∷ CS03 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                  (Sw14 ∷ Toff024 ∷ []) (Toff012 ∷ Sw14 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CCZ034 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CX10 ∷ Toff214 ∷ []) (Toff214 ∷ CX10 ∷ [])
                      wleaf
                    )
                    (CS04⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS04⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S4 ∷ CS02 ∷ CCZ024 ∷ CS02 ∷ CZ02 ∷ CCZ024 ∷ []) (S4 ∷ [])
                        wleaf
                      )
                      (CX13 ∷ Toff014 ∷ []) (Toff014 ∷ CX13 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX02 ∷ Toff304 ∷ []) (Toff304 ∷ CX02 ∷ [])
                        wleaf
                      )
                      (CX42 ∷ Toff014 ∷ []) (Toff014 ∷ CX42 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ CCZ034 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX30 ∷ Toff402 ∷ []) (Toff402 ∷ CX30 ∷ Toff423 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ []) (CX12 ∷ Toff214 ∷ CCZ012 ∷ [])
                      wleaf
                    )
                  )
                  (CX42 ∷ Toff034 ∷ []) (Toff034 ∷ CX42 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS04 ∷ Toff201 ∷ []) (Toff201 ∷ CS04 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ CZ34 ∷ []) (CZ34 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CX40 ∷ [])
                      wleaf
                    )
                  )
                )
                (Toff034 ∷ Toff034 ∷ Toff134 ∷ []) (Toff134 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ []) (CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (K0 ∷ CK40 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ014 ∷ CZ01 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (Toff413 ∷ Toff103 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ CK41 ∷ []) (CK41 ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS04 ∷ Toff203 ∷ []) (Toff203 ∷ CS04 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ CCZ234 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ K0⁻ ∷ []) (K0⁻ ∷ Toff014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ CCZ023 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CS14⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS14⁻ ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (Toff204 ∷ Toff204 ∷ []) []
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
                        wleaf
                      )
                      (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ014 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ []) (Toff014 ∷ CCZ124 ∷ Toff014 ∷ [])
                      wleaf
                    )
                  )
                  (CX31 ∷ Toff034 ∷ []) (Toff034 ∷ CX31 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CX40 ∷ []) (CX40 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                    (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS34 ∷ Toff103 ∷ []) (Toff103 ∷ CS34 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ []) (CX43 ∷ CCZ014 ∷ CX43 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ024 ∷ CZ24 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ CK40 ∷ []) (CZ03 ∷ CK40 ∷ CZ03 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ K2 ∷ CK02 ∷ S0 ∷ []) (K2 ∷ CK02 ∷ S0 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ CS24 ∷ []) (CS24 ∷ CS04 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ024 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff034 ∷ CCZ234 ∷ []) (Toff034 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CX21 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX21 ∷ [])
                      wleaf
                    )
                    (Toff023 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff023 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS34⁻ ∷ K2 ∷ CK02 ∷ S0 ∷ []) (K2 ∷ CK02 ∷ S0 ∷ CS34⁻ ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ K3 ∷ []) (K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (Toff014 ∷ Toff014 ∷ []) []
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CK42 ∷ CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (Toff201 ∷ Toff204 ∷ []) (Toff204 ∷ Toff201 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff014 ∷ CZ03 ∷ Toff014 ∷ CCZ014 ∷ CZ03 ∷ []) (CCZ134 ∷ [])
                        wleaf
                      )
                      (K3 ∷ Toff014 ∷ []) (Toff014 ∷ K3 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ024 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ024 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS01⁻ ∷ [])
                        wleaf
                      )
                      (CS24 ∷ Toff304 ∷ []) (Toff304 ∷ CS24 ∷ [])
                      wleaf
                    )
                    (CS24 ∷ Toff024 ∷ []) (Toff024 ∷ CS24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff402 ∷ []) (Toff402 ∷ CZ02 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CX34 ∷ Toff204 ∷ []) (Toff204 ∷ CX34 ∷ Toff203 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ []) (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ []) (CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (S3 ∷ CS34⁻ ∷ Toff023 ∷ []) (Toff023 ∷ S3 ∷ CS34⁻ ∷ [])
                      wleaf
                    )
                    (Sw02 ∷ Toff124 ∷ []) (Toff104 ∷ Sw02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ CCZ014 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                  (CS04 ∷ Toff034 ∷ []) (Toff034 ∷ CS04 ∷ CS34 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ [])
                        wleaf
                      )
                      (CS02 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CS02 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ []) (CX01 ∷ CCZ034 ∷ CX01 ∷ [])
                    (wnode
                      wleaf
                      (CX30 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX30 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CCZ012 ∷ CS14 ∷ []) (CS14 ∷ CCZ012 ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ Toff304 ∷ []) (Toff304 ∷ K2 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CX34 ∷ []) (CX34 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                    (CX42 ∷ Toff023 ∷ []) (Toff023 ∷ CX42 ∷ Toff034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS34⁻ ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ []) (CCZ014 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw02 ∷ Toff423 ∷ []) (Toff403 ∷ Sw02 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CX43 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX43 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff103 ∷ CCZ034 ∷ []) (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS04 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX20 ∷ Toff324 ∷ []) (Toff324 ∷ CX20 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                    (CX02 ∷ Toff412 ∷ []) (Toff412 ∷ CX02 ∷ Toff401 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS02⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS02⁻ ∷ [])
                        wleaf
                      )
                      (Toff013 ∷ Toff134 ∷ []) (Toff034 ∷ Toff134 ∷ Toff013 ∷ [])
                      wleaf
                    )
                  )
                  (Toff014 ∷ Toff034 ∷ []) (Toff034 ∷ Toff014 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff203 ∷ CCZ034 ∷ []) (Toff203 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ [])
                      wleaf
                    )
                    (Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ Toff023 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ Toff014 ∷ Toff014 ∷ []) (CX12 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX14 ∷ Toff301 ∷ Toff301 ∷ []) (CX14 ∷ [])
                        wleaf
                      )
                      (Toff024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ Toff024 ∷ [])
                      wleaf
                    )
                    (CCZ013 ∷ CS14 ∷ []) (CS14 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff402 ∷ Toff402 ∷ []) []
                        wleaf
                      )
                      (CX43 ∷ Toff024 ∷ Toff024 ∷ []) (CX43 ∷ [])
                      wleaf
                    )
                  )
                  (CS13 ∷ Toff034 ∷ []) (Toff034 ∷ CS13 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS01⁻ ∷ [])
                        wleaf
                      )
                      (CS04 ∷ Toff214 ∷ []) (Toff214 ∷ CS04 ∷ [])
                      wleaf
                    )
                    (S0 ∷ CS14 ∷ CCZ014 ∷ CS14 ∷ CZ14 ∷ CCZ014 ∷ []) (S0 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CZ14 ∷ CCZ013 ∷ Toff403 ∷ []) (Toff403 ∷ CZ14 ∷ [])
                        wleaf
                      )
                      (CX34 ∷ Toff203 ∷ []) (Toff203 ∷ CX34 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
                      wleaf
                    )
                    (CCZ234 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff403 ∷ CCZ013 ∷ []) (Toff403 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                  (CS03⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX12 ∷ [])
                      wleaf
                    )
                    (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ014 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CS04 ∷ []) (CS04 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CCZ024 ∷ Toff204 ∷ CZ04 ∷ []) (Toff204 ∷ CCZ024 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff304 ∷ CCZ014 ∷ []) (Toff304 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                    (CX14 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CX13 ∷ []) (CX13 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ CS02 ∷ []) (CS02 ∷ CCZ014 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX03 ∷ Toff204 ∷ Toff204 ∷ []) (CX03 ∷ [])
                        wleaf
                      )
                      (Toff304 ∷ Toff314 ∷ []) (Toff314 ∷ Toff304 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ014 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CS01 ∷ Toff214 ∷ []) (Toff214 ∷ CS01 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX42 ∷ Toff014 ∷ Toff014 ∷ []) (CX42 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ X4 ∷ []) (X4 ∷ S0 ∷ CS04⁻ ∷ [])
                      wleaf
                    )
                    (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff304 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CZ24 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (CZ24 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ CS12 ∷ []) (CS12 ∷ CS04 ∷ [])
                      wleaf
                    )
                  )
                  (K0 ∷ CCZ034 ∷ []) (Toff034 ∷ K0 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ CCZ234 ∷ []) (Toff034 ∷ CCZ023 ∷ Toff034 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ [])
                      wleaf
                    )
                    (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S4 ∷ CS01 ∷ CCZ014 ∷ CS01 ∷ CZ01 ∷ CCZ014 ∷ []) (S4 ∷ [])
                        wleaf
                      )
                      (Sw23 ∷ Toff402 ∷ []) (Toff403 ∷ Sw23 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CZ14 ∷ CCZ014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ []) (CX40 ∷ CCZ124 ∷ CX40 ∷ [])
                        wleaf
                      )
                      (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                    (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (Toff403 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CZ01 ∷ []) (Toff401 ∷ CCZ014 ∷ Toff401 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                  (CX41 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX41 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CX43 ∷ Toff013 ∷ []) (Toff013 ∷ CX43 ∷ Toff014 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw02 ∷ Toff324 ∷ []) (Toff304 ∷ Sw02 ∷ [])
                        wleaf
                      )
                      (K2 ∷ CK42 ∷ S4 ∷ Toff024 ∷ []) (Toff024 ∷ K2 ∷ CK42 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CS14 ∷ Toff301 ∷ []) (Toff301 ∷ CS14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX10 ∷ Toff403 ∷ []) (Toff403 ∷ CX10 ∷ Toff413 ∷ [])
                        wleaf
                      )
                      (K4 ∷ CK34 ∷ S3 ∷ []) (K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ S3 ∷ [])
                      wleaf
                    )
                  )
                  (CS14 ∷ Toff034 ∷ []) (Toff034 ∷ CS14 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ []) (Toff201 ∷ CCZ014 ∷ Toff201 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CCZ134 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ CCZ134 ∷ [])
                    (wnode
                      wleaf
                      (CCZ012 ∷ []) (CX24 ∷ CCZ012 ∷ CX24 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
      (CCZ034 ∷ CS01 ∷ []) (CS01 ∷ CCZ034 ∷ [])
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (Toff302 ∷ Toff024 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CS24 ∷ []) (CS24 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (S0 ∷ CS04⁻ ∷ []) (X4 ∷ CS04 ∷ X4 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S4 ∷ CS04⁻ ∷ []) (X0 ∷ CS04 ∷ X0 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff204 ∷ Toff234 ∷ []) (Toff234 ∷ Toff204 ∷ [])
                        wleaf
                      )
                      (CS12 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS12 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ Toff403 ∷ []) (Toff403 ∷ CS04 ∷ CS03 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX30 ∷ Toff413 ∷ []) (Toff413 ∷ CX30 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ Toff301 ∷ []) (Toff301 ∷ CS04 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Sw04 ∷ []) (Sw04 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CX24 ∷ Toff014 ∷ []) (Toff014 ∷ CX24 ∷ Toff012 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ CX40 ∷ []) (CX40 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K3 ∷ Toff401 ∷ []) (Toff401 ∷ K3 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                  (CX14 ∷ Toff012 ∷ Toff012 ∷ []) (CX14 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK40 ∷ CK40⁻ ∷ []) []
                        wleaf
                      )
                      (CCZ134 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                    (CS24⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S4 ∷ Toff402 ∷ []) (Toff402 ∷ S4 ∷ CS02 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CX34 ∷ Toff014 ∷ []) (Toff014 ∷ CX34 ∷ Toff013 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX24 ∷ Toff304 ∷ []) (Toff304 ∷ CX24 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Toff024 ∷ CCZ234 ∷ []) (Toff024 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (Sw14 ∷ Toff304 ∷ []) (Toff301 ∷ Sw14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ014 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ CCZ014 ∷ []) []
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (Toff304 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS02 ∷ Toff412 ∷ []) (Toff412 ∷ CS02 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CK40 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                )
                (Toff013 ∷ Toff034 ∷ []) (Toff034 ∷ Toff013 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ []) (CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ034 ∷ CZ04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff403 ∷ Toff413 ∷ []) (Toff413 ∷ Toff403 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ CS34 ∷ []) (CS34 ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) (CX10 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ234 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) (Toff324 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ CS14 ∷ CCZ014 ∷ CS14 ∷ CZ14 ∷ CCZ014 ∷ []) (CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff413 ∷ CCZ013 ∷ []) (Toff413 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ234 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CS04⁻ ∷ S2 ∷ []) (S2 ∷ CS04⁻ ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS04 ∷ Toff302 ∷ []) (Toff302 ∷ CS04 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (Sw24 ∷ Toff023 ∷ []) (Toff034 ∷ Sw24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S4 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04 ∷ [])
                        wleaf
                      )
                      (CS14 ∷ Toff013 ∷ []) (Toff013 ∷ CS14 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (Toff204 ∷ [])
                        wleaf
                      )
                      (CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ [])
                      wleaf
                    )
                    (CS03 ∷ Sw34 ∷ []) (Sw34 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff401 ∷ Toff413 ∷ []) (Toff413 ∷ Toff401 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ []) (CX34 ∷ CCZ013 ∷ CX34 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK40 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff413 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff413 ∷ [])
                        wleaf
                      )
                      (S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S4 ∷ [])
                      wleaf
                    )
                  )
                  (Sw13 ∷ Toff401 ∷ []) (Toff403 ∷ Sw13 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ012 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ [])
                      wleaf
                    )
                    (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS02⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS02⁻ ∷ CS04⁻ ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CX24 ∷ Toff012 ∷ []) (Toff012 ∷ CX24 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (Toff014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX41 ∷ Toff304 ∷ Toff304 ∷ []) (CX41 ∷ [])
                        wleaf
                      )
                      (CX14 ∷ Toff204 ∷ []) (Toff204 ∷ CX14 ∷ Toff201 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff401 ∷ Toff402 ∷ []) (Toff402 ∷ Toff401 ∷ [])
                        wleaf
                      )
                      (CS24 ∷ Toff014 ∷ []) (Toff014 ∷ CS24 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ023 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS14⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS14⁻ ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ023 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ CS24⁻ ∷ CZ24 ∷ CCZ024 ∷ []) (CS04⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff401 ∷ []) (Toff401 ∷ CZ01 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CX43 ∷ Toff204 ∷ []) (Toff204 ∷ CX43 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ CZ34 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ []) (CCZ234 ∷ CCZ024 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (S2 ∷ CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ S2 ∷ CS24⁻ ∷ [])
                      wleaf
                    )
                    (CX20 ∷ Toff412 ∷ Toff412 ∷ []) (CX20 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ []) (Toff403 ∷ K3 ∷ CK03 ∷ S0 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ []) (CK43 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                  (CS23⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS23⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS12 ∷ CCZ124 ∷ []) (CS12 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ [])
                        wleaf
                      )
                      (Toff214 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff214 ∷ [])
                      wleaf
                    )
                    (CX01 ∷ Toff204 ∷ []) (Toff204 ∷ CX01 ∷ [])
                    (wnode
                      wleaf
                      (CX03 ∷ Toff324 ∷ []) (Toff324 ∷ CX03 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CZ01 ∷ Toff034 ∷ []) (Toff034 ∷ CZ01 ∷ CCZ134 ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff304 ∷ CZ04 ∷ []) (Toff304 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ013 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CX13 ∷ CCZ014 ∷ Toff301 ∷ []) (CX13 ∷ Toff301 ∷ [])
                        wleaf
                      )
                      (CS14 ∷ Toff201 ∷ []) (Toff201 ∷ CS14 ∷ [])
                      wleaf
                    )
                  )
                  (CX41 ∷ Toff034 ∷ []) (Toff034 ∷ CX41 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX20 ∷ Toff324 ∷ Toff324 ∷ []) (CX20 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ Toff324 ∷ []) (Toff324 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ CZ02 ∷ []) (Toff402 ∷ CCZ024 ∷ Toff402 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                  )
                )
                (Toff024 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX04 ∷ Toff324 ∷ []) (Toff324 ∷ CX04 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (Sw24 ∷ Toff102 ∷ []) (Toff104 ∷ Sw24 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (X0 ∷ CZ14 ∷ CZ14 ∷ []) (X0 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ []) (CX23 ∷ Toff324 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ Toff014 ∷ CCZ124 ∷ []) (Toff014 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS01⁻ ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ [])
                      wleaf
                    )
                    (CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS13⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff014 ∷ CCZ134 ∷ []) (Toff014 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS02 ∷ Toff304 ∷ []) (Toff304 ∷ CS02 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K4 ∷ CCZ024 ∷ K4⁻ ∷ []) (Toff402 ∷ [])
                        wleaf
                      )
                      (CX43 ∷ Toff023 ∷ []) (Toff023 ∷ CX43 ∷ Toff024 ∷ [])
                      wleaf
                    )
                  )
                  (CX24 ∷ Toff034 ∷ []) (Toff034 ∷ CX24 ∷ Toff023 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ []) (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ [])
                        wleaf
                      )
                      (K3 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ K3⁻ ∷ []) (Toff304 ∷ [])
                      wleaf
                    )
                    (S0 ∷ Toff014 ∷ []) (Toff014 ∷ S0 ∷ CS14 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K2⁻ ∷ Toff403 ∷ []) (Toff403 ∷ K2⁻ ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CK42 ∷ []) (CZ02 ∷ CK42 ∷ CZ02 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ024 ∷ CCZ124 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff301 ∷ CCZ014 ∷ []) (Toff301 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ S4 ∷ []) (S4 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CCZ234 ∷ CX02 ∷ CCZ034 ∷ []) (CX02 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ124 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ Toff134 ∷ []) (Toff134 ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                  (CS34 ∷ Toff034 ∷ []) (Toff034 ∷ CS34 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff034 ∷ CCZ134 ∷ []) (Toff034 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ014 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ K0 ∷ []) (K0 ∷ Toff024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ014 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ Toff024 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ024 ∷ CZ04 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX24 ∷ Toff302 ∷ []) (Toff302 ∷ CX24 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff204 ∷ [])
                      wleaf
                    )
                    (CX14 ∷ Toff013 ∷ []) (Toff013 ∷ CX14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ S1 ∷ CS01⁻ ∷ []) (S1 ∷ CS01⁻ ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (CCZ014 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ Toff204 ∷ CCZ014 ∷ []) (Toff204 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (Toff304 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (Toff013 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CZ24 ∷ Toff201 ∷ []) (Toff201 ∷ CZ24 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ024 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX42 ∷ Toff012 ∷ []) (Toff012 ∷ CX42 ∷ Toff014 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CZ04 ∷ []) (Toff304 ∷ CCZ034 ∷ Toff304 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CZ24 ∷ CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CZ24 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS04 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff034 ∷ Toff314 ∷ []) (Toff314 ∷ Toff014 ∷ Toff034 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S4 ∷ Toff401 ∷ []) (Toff401 ∷ S4 ∷ CS01 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CX23 ∷ Toff024 ∷ Toff024 ∷ []) (CX23 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ CZ14 ∷ Toff014 ∷ CCZ014 ∷ []) (Toff014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CX40 ∷ []) (CX40 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (Sw14 ∷ Toff204 ∷ []) (Toff201 ∷ Sw14 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX03 ∷ Toff402 ∷ Toff402 ∷ []) (CX03 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ034 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ CS34 ∷ []) (CS34 ∷ CCZ013 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CZ02 ∷ Toff214 ∷ []) (Toff214 ∷ CZ02 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff201 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff201 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CS14 ∷ CS14 ∷ []) (CS14 ∷ CS14 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) (CX13 ∷ CCZ034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX02 ∷ Toff304 ∷ Toff304 ∷ []) (CX02 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ S4 ∷ []) (S4 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ034 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX01 ∷ Toff403 ∷ []) (Toff403 ∷ CX01 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ CK34 ∷ []) (CZ04 ∷ CK34 ∷ CZ04 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                  (CZ04 ∷ CZ34 ∷ CZ34 ∷ []) (CZ04 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK42 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ []) (CX03 ∷ CCZ014 ∷ CX03 ∷ [])
                      wleaf
                    )
                    (CCZ134 ∷ []) (CX10 ∷ CCZ134 ∷ CX10 ∷ [])
                    (wnode
                      wleaf
                      (CCZ034 ∷ CX24 ∷ CCZ023 ∷ []) (CX24 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ [])
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ234 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                    (CCZ134 ∷ CS01 ∷ []) (CS01 ∷ CCZ134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ CZ24 ∷ []) (CZ24 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ CX03 ∷ CCZ024 ∷ []) (CX03 ∷ CCZ234 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ024 ∷ CZ24 ∷ []) (Toff024 ∷ CCZ024 ∷ Toff024 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (K0 ∷ CK40 ∷ S4 ∷ Toff134 ∷ []) (Toff134 ∷ K0 ∷ CK40 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ024 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ [])
                      wleaf
                    )
                  )
                )
                (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw04 ∷ Sw04 ∷ []) []
                        wleaf
                      )
                      (CX24 ∷ Toff012 ∷ Toff012 ∷ []) (CX24 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ CS03 ∷ CCZ034 ∷ CX34 ∷ []) (CX34 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CX31 ∷ Toff103 ∷ []) (CX31 ∷ Toff103 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (Sw14 ∷ Toff201 ∷ []) (Toff204 ∷ Sw14 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS01⁻ ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Toff204 ∷ CCZ034 ∷ []) (Toff204 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (S2 ∷ Toff204 ∷ []) (Toff204 ∷ S2 ∷ CS04 ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS12 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS12 ∷ [])
                        wleaf
                      )
                      (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK41 ∷ [])
                        wleaf
                      )
                      (CX21 ∷ Toff024 ∷ Toff024 ∷ []) (CX21 ∷ [])
                      wleaf
                    )
                    (CCZ134 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX23 ∷ Toff402 ∷ []) (Toff402 ∷ CX23 ∷ [])
                        wleaf
                      )
                      (Toff023 ∷ Toff324 ∷ []) (Toff024 ∷ Toff324 ∷ Toff023 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                    (S0 ∷ CS04⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S0 ∷ CS04⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ Toff403 ∷ []) (Toff403 ∷ K2 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ K1 ∷ []) (K1 ∷ Toff104 ∷ CCZ014 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ CX32 ∷ []) (CX32 ∷ CCZ034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ X4 ∷ []) (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ CK43 ∷ []) (CK43 ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                  (CX20 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX20 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ []) (Toff034 ∷ [])
                        wleaf
                      )
                      (CS12⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS12⁻ ∷ [])
                      wleaf
                    )
                    (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS23 ∷ Toff402 ∷ []) (Toff402 ∷ CS23 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ013 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ CCZ234 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ [])
                      wleaf
                    )
                    (CS03 ∷ Toff134 ∷ []) (Toff134 ∷ CS03 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CX32 ∷ []) (CX32 ∷ CCZ034 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ []) (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS02 ∷ Toff204 ∷ []) (Toff204 ∷ CS02 ∷ CS04 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CX34 ∷ []) (CX34 ∷ CCZ013 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ Toff024 ∷ CZ24 ∷ []) (Toff024 ∷ CCZ024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CK40 ∷ CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ []) (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ034 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CK41 ∷ CS04 ∷ []) (CS04 ∷ CK41 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ024 ∷ []) (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw13 ∷ Toff014 ∷ []) (Toff034 ∷ Sw13 ∷ [])
                        wleaf
                      )
                      (CS34 ∷ Toff023 ∷ []) (Toff023 ∷ CS34 ∷ [])
                      wleaf
                    )
                    (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ S0 ∷ []) (S0 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ S4 ∷ []) (S4 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CX04 ∷ CCZ013 ∷ []) (CX04 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ []) (CX14 ∷ CCZ013 ∷ CX14 ∷ [])
                      wleaf
                    )
                    (CCZ023 ∷ CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX30 ∷ Toff423 ∷ []) (Toff423 ∷ CX30 ∷ [])
                        wleaf
                      )
                      (Toff324 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff324 ∷ [])
                      wleaf
                    )
                  )
                  (CX41 ∷ Toff024 ∷ []) (Toff024 ∷ CX41 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ034 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CX10 ∷ Toff314 ∷ Toff314 ∷ []) (CX10 ∷ [])
                      wleaf
                    )
                    (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ013 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CX03 ∷ Toff204 ∷ []) (Toff204 ∷ CX03 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ012 ∷ CS04 ∷ []) (CS04 ∷ CCZ012 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX02 ∷ Toff324 ∷ []) (Toff324 ∷ CX02 ∷ Toff304 ∷ [])
                        wleaf
                      )
                      (CS13⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS13⁻ ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CZ03 ∷ []) (CX34 ∷ CCZ034 ∷ CX34 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff412 ∷ CCZ012 ∷ []) (Toff412 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ []) (CCZ034 ∷ [])
                      wleaf
                    )
                  )
                  (CS04⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) (CX30 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CS34 ∷ Toff204 ∷ []) (Toff204 ∷ CS34 ∷ [])
                    (wnode
                      wleaf
                      (CX30 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ CX30 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS14 ∷ Toff304 ∷ []) (Toff304 ∷ CS14 ∷ [])
                        wleaf
                      )
                      (CX23 ∷ Toff024 ∷ []) (Toff024 ∷ CX23 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ CX42 ∷ []) (CX42 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CZ04 ∷ []) (Toff204 ∷ CCZ024 ∷ Toff204 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CS24 ∷ []) (CS24 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX41 ∷ Toff201 ∷ []) (Toff201 ∷ CX41 ∷ Toff204 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CS04⁻ ∷ CX43 ∷ []) (CX43 ∷ CS04⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CS24 ∷ []) (CS24 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ013 ∷ CS04 ∷ []) (CS04 ∷ CCZ013 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX40 ∷ CX04 ∷ CX40 ∷ []) (Sw04 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff034 ∷ CCZ134 ∷ []) (Toff034 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CX02 ∷ []) (CX02 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (Toff423 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CX31 ∷ []) (CX31 ∷ CCZ034 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (CX32 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff401 ∷ CCZ012 ∷ []) (Toff401 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CS01 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX14 ∷ Toff301 ∷ []) (Toff301 ∷ CX14 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ134 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ [])
                      wleaf
                    )
                  )
                  (Toff023 ∷ Toff034 ∷ []) (Toff034 ∷ Toff023 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ024 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ []) (CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CS13 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS13 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CZ14 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) (CZ14 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ Toff204 ∷ CCZ014 ∷ []) (Toff204 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ034 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CX20 ∷ Toff401 ∷ []) (Toff401 ∷ CX20 ∷ Toff412 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff402 ∷ Toff403 ∷ []) (Toff403 ∷ Toff402 ∷ [])
                        wleaf
                      )
                      (CZ01 ∷ CK41 ∷ CZ01 ∷ CZ01 ∷ []) (CZ01 ∷ CK41 ∷ [])
                      wleaf
                    )
                  )
                  (CS03⁻ ∷ CS34⁻ ∷ CCZ034 ∷ CS34⁻ ∷ CZ34 ∷ CCZ034 ∷ []) (CS03⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ CCZ014 ∷ []) (CS01 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CX21 ∷ []) (CX21 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS12⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS24 ∷ CX23 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ CS24 ∷ [])
                        wleaf
                      )
                      (CS24⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS24⁻ ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CS01 ∷ Toff314 ∷ []) (Toff314 ∷ CS01 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff302 ∷ Toff304 ∷ []) (Toff304 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ Toff014 ∷ []) (Toff014 ∷ CX12 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ024 ∷ CZ02 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ CZ03 ∷ []) (CZ03 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ CS03 ∷ []) (CS03 ∷ CCZ014 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw03 ∷ Toff402 ∷ []) (Toff423 ∷ Sw03 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) (CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CK40 ∷ CCZ013 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                )
                (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (Toff134 ∷ Toff013 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw24 ∷ Toff104 ∷ []) (Toff102 ∷ Sw24 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CS04⁻ ∷ S3 ∷ []) (S3 ∷ CS04⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff103 ∷ Toff413 ∷ []) (Toff413 ∷ Toff403 ∷ Toff103 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ CS14 ∷ []) (CS14 ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ []) (CCZ234 ∷ CCZ023 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ []) (CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ [])
                      wleaf
                    )
                    (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS13 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS13 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ023 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CX40 ∷ []) (CX40 ∷ CCZ124 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ034 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                    (Toff403 ∷ Toff403 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ024 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CCZ134 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ K2 ∷ []) (K2 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff203 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff203 ∷ [])
                        wleaf
                      )
                      (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ [])
                      wleaf
                    )
                  )
                )
                (CX13 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX13 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw02 ∷ Toff403 ∷ []) (Toff423 ∷ Sw02 ∷ [])
                        wleaf
                      )
                      (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ CX20 ∷ []) (CX20 ∷ CCZ124 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX31 ∷ Toff403 ∷ []) (Toff403 ∷ CX31 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ X3 ∷ []) (X3 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ ι1 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                  )
                  (CX40 ∷ Toff034 ∷ []) (Toff034 ∷ CX40 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ234 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ024 ∷ [])
                    (wnode
                      wleaf
                      (CCZ014 ∷ []) (CX42 ∷ CCZ014 ∷ CX42 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    [] []
    (wnode
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ []) (CCZ012 ∷ [])
                        wleaf
                      )
                      (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ [])
                      wleaf
                    )
                    (CK40⁻ ∷ []) (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (Toff234 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                  (CS24 ∷ Toff012 ∷ []) (Toff012 ∷ CS24 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS14 ∷ Toff204 ∷ []) (Toff204 ∷ CS14 ∷ [])
                        wleaf
                      )
                      (S0 ∷ CS04⁻ ∷ Toff134 ∷ []) (Toff134 ∷ S0 ∷ CS04⁻ ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ CS04 ∷ []) (CS04 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX01 ∷ Toff413 ∷ []) (Toff413 ∷ CX01 ∷ Toff403 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (Toff302 ∷ CCZ234 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ []) (CCZ012 ∷ [])
                        wleaf
                      )
                      (CX42 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX42 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ []) (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS03⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS03⁻ ∷ [])
                        wleaf
                      )
                      (Toff013 ∷ Toff314 ∷ []) (Toff014 ∷ Toff314 ∷ Toff013 ∷ [])
                      wleaf
                    )
                  )
                  (Toff012 ∷ Toff024 ∷ []) (Toff024 ∷ Toff012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK40 ∷ CCZ034 ∷ []) (Toff034 ∷ CK40 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ134 ∷ [])
                      wleaf
                    )
                    (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS04⁻ ∷ CS02⁻ ∷ CCZ024 ∷ CS02⁻ ∷ CZ02 ∷ CCZ024 ∷ []) (CS04⁻ ∷ [])
                        wleaf
                      )
                      (CX43 ∷ Toff014 ∷ []) (Toff014 ∷ CX43 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ134 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CX21 ∷ Toff014 ∷ []) (Toff014 ∷ CX21 ∷ Toff024 ∷ [])
                      wleaf
                    )
                    (Sw14 ∷ Toff013 ∷ []) (Toff034 ∷ Sw14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CX03 ∷ CCZ014 ∷ []) (CX03 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CZ01 ∷ CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CZ01 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ []) (CZ14 ∷ CCZ014 ∷ CZ14 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff204 ∷ Toff304 ∷ []) (Toff304 ∷ Toff204 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                    (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff423 ∷ CCZ023 ∷ []) (Toff423 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ Toff024 ∷ CCZ024 ∷ CZ02 ∷ CK40 ∷ CZ02 ∷ S4 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (Toff034 ∷ CCZ024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ []) (CCZ024 ∷ [])
                        wleaf
                      )
                      (S3 ∷ CS34⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S3 ∷ CS34⁻ ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS03 ∷ Toff413 ∷ []) (Toff413 ∷ CS03 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ CS24 ∷ []) (CS24 ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff314 ∷ [])
                        wleaf
                      )
                      (CX14 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX14 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ Toff014 ∷ []) (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ024 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ []) (CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CS04⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS04⁻ ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ []) (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) (Toff014 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                  (CX14 ∷ Toff034 ∷ []) (Toff034 ∷ CX14 ∷ Toff013 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX41 ∷ Toff204 ∷ Toff204 ∷ []) (CX41 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CX13 ∷ CCZ014 ∷ Toff314 ∷ []) (CX13 ∷ Toff314 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ012 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CX34 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX34 ∷ [])
                      wleaf
                    )
                  )
                )
                (Toff024 ∷ Toff024 ∷ []) []
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw04 ∷ Toff203 ∷ []) (Toff234 ∷ Sw04 ∷ [])
                        wleaf
                      )
                      (CX32 ∷ Toff034 ∷ Toff034 ∷ []) (CX32 ∷ [])
                      wleaf
                    )
                    (CX02 ∷ Toff401 ∷ Toff401 ∷ []) (CX02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ S4 ∷ []) (S4 ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ014 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ []) (CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) (CX21 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK02 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CK02 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ Toff024 ∷ CCZ234 ∷ []) (Toff024 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ023 ∷ CS04 ∷ []) (CS04 ∷ CCZ023 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX04 ∷ Toff301 ∷ []) (Toff301 ∷ CX04 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ []) (CX41 ∷ CCZ034 ∷ CX41 ∷ [])
                      wleaf
                    )
                    (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) (Toff401 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS03 ∷ Toff401 ∷ []) (Toff401 ∷ CS03 ∷ [])
                        wleaf
                      )
                      (K3⁻ ∷ Toff014 ∷ []) (Toff014 ∷ K3⁻ ∷ [])
                      wleaf
                    )
                  )
                  (Sw24 ∷ Toff034 ∷ []) (Toff023 ∷ Sw24 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff204 ∷ Toff304 ∷ Toff324 ∷ []) (Toff324 ∷ Toff204 ∷ [])
                        wleaf
                      )
                      (CX01 ∷ Toff304 ∷ []) (Toff304 ∷ CX01 ∷ [])
                      wleaf
                    )
                    (CS24⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS24⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff401 ∷ CZ01 ∷ []) (Toff401 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CX43 ∷ Toff204 ∷ Toff204 ∷ []) (CX43 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ CCZ234 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CS13 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS13 ∷ [])
                      wleaf
                    )
                    (CX12 ∷ Toff401 ∷ []) (Toff401 ∷ CX12 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ CZ03 ∷ Toff403 ∷ CCZ034 ∷ []) (Toff403 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CK43 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK43 ∷ [])
                      wleaf
                    )
                  )
                  (CZ03 ∷ CZ34 ∷ CZ34 ∷ []) (CZ03 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CK40 ∷ CS04 ∷ []) (CS04 ∷ CK40 ∷ CK40 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS01 ∷ K0 ∷ CS01 ∷ K0 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS01 ∷ CS01 ∷ CS04 ∷ CS04 ∷ CS04 ∷ [])
                        wleaf
                      )
                      (K2 ∷ Toff034 ∷ []) (Toff034 ∷ K2 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ []) (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ [])
                    (wnode
                      wleaf
                      (Toff024 ∷ Toff324 ∷ Toff324 ∷ []) (Toff024 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ014 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ CX24 ∷ CCZ012 ∷ []) (CX24 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ CX30 ∷ []) (CX30 ∷ CCZ234 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX20 ∷ Toff304 ∷ []) (Toff304 ∷ CX20 ∷ Toff324 ∷ [])
                        wleaf
                      )
                      (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) (Toff014 ∷ K1 ∷ CK41 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (CX43 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ CZ02 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
                      wleaf
                    )
                  )
                )
                (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX40 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX40 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ012 ∷ [])
                      wleaf
                    )
                    (CS03 ∷ CS04⁻ ∷ CS03⁻ ∷ []) (CS04⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CZ14 ∷ []) (CZ14 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CZ02 ∷ CCZ024 ∷ []) (CZ02 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                  )
                  (CX13 ∷ Toff034 ∷ []) (Toff034 ∷ CX13 ∷ Toff014 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS14⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS14⁻ ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                    (CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ134 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CX12 ∷ Toff024 ∷ []) (Toff024 ∷ CX12 ∷ Toff014 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX14 ∷ Toff304 ∷ []) (Toff304 ∷ CX14 ∷ Toff301 ∷ [])
                        wleaf
                      )
                      (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ CK01 ∷ S0 ∷ Toff401 ∷ []) (Toff401 ∷ K1 ∷ CK01 ∷ S0 ∷ [])
                        wleaf
                      )
                      (CX34 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX34 ∷ [])
                      wleaf
                    )
                  )
                  (CX42 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX42 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff203 ∷ CCZ034 ∷ []) (Toff203 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CX34 ∷ []) (CX34 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ CS14⁻ ∷ CZ14 ∷ CCZ014 ∷ []) (CS04⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ Toff403 ∷ []) (Toff403 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ K2 ∷ []) (K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (CX23 ∷ CCZ034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ234 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CS03 ∷ K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ CK42 ∷ S4 ∷ CS03 ∷ [])
                      wleaf
                    )
                    (CX02 ∷ Toff401 ∷ []) (Toff401 ∷ CX02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff403 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff403 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ Toff034 ∷ []) (Toff034 ∷ CZ34 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ []) (Toff012 ∷ CCZ124 ∷ Toff012 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) (CX12 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ CS24 ∷ CCZ024 ∷ CS24 ∷ CZ24 ∷ CCZ024 ∷ []) (CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CCZ013 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ K2 ∷ []) (K2 ∷ Toff204 ∷ [])
                      wleaf
                    )
                    (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S1 ∷ CS01⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ S1 ∷ CS01⁻ ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) (CX31 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                  (Sw14 ∷ Toff301 ∷ []) (Toff304 ∷ Sw14 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX03 ∷ Toff234 ∷ []) (Toff234 ∷ CX03 ∷ Toff204 ∷ [])
                        wleaf
                      )
                      (CX01 ∷ Toff314 ∷ []) (Toff314 ∷ CX01 ∷ Toff304 ∷ [])
                      wleaf
                    )
                    (Toff023 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff023 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS34⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CS34⁻ ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CX43 ∷ CCZ024 ∷ []) (CX43 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff014 ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ CCZ012 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ [])
                        wleaf
                      )
                      (Toff213 ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff213 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CZ04 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CX23 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ CS13 ∷ []) (CS13 ∷ CS04 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ023 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff014 ∷ CCZ134 ∷ CCZ134 ∷ []) (Toff014 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ []) (CX14 ∷ CCZ012 ∷ CX14 ∷ [])
                      wleaf
                    )
                    (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ CS01⁻ ∷ CZ01 ∷ CCZ014 ∷ []) (CS04⁻ ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ Toff024 ∷ CCZ124 ∷ []) (Toff024 ∷ CCZ012 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ014 ∷ CZ14 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX40 ∷ Toff302 ∷ []) (Toff302 ∷ CX40 ∷ Toff324 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CS13 ∷ []) (CS13 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX20 ∷ Toff423 ∷ []) (Toff423 ∷ CX20 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ013 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff023 ∷ Toff234 ∷ []) (Toff034 ∷ Toff234 ∷ Toff023 ∷ [])
                        wleaf
                      )
                      (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CK41 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff304 ∷ Toff324 ∷ []) (Toff324 ∷ Toff304 ∷ [])
                        wleaf
                      )
                      (S4 ∷ Toff023 ∷ []) (Toff023 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) (Toff412 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ CZ03 ∷ []) (Toff403 ∷ CCZ034 ∷ Toff403 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ K4 ∷ []) (K4 ∷ Toff403 ∷ CCZ034 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                  (CZ04 ∷ Toff034 ∷ []) (Toff034 ∷ CZ04 ∷ CZ34 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (Toff201 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CX10 ∷ Toff214 ∷ Toff214 ∷ []) (CX10 ∷ [])
                    (wnode
                      wleaf
                      (Sw03 ∷ Toff324 ∷ []) (Toff024 ∷ Sw03 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ [])
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ []) (Toff024 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ124 ∷ [])
                      wleaf
                    )
                    (K0⁻ ∷ CK40 ∷ []) (X4 ∷ CK40⁻ ∷ X4 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (X0 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CS13⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS13⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ024 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw03 ∷ Toff204 ∷ []) (Toff234 ∷ Sw03 ∷ [])
                        wleaf
                      )
                      (CS12⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS12⁻ ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) (Toff301 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) (CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
                (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (Toff324 ∷ Toff023 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw04 ∷ Toff234 ∷ []) (Toff203 ∷ Sw04 ∷ [])
                        wleaf
                      )
                      (Toff012 ∷ Toff014 ∷ []) (Toff014 ∷ Toff012 ∷ [])
                      wleaf
                    )
                    (CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ CS03⁻ ∷ CZ03 ∷ CCZ034 ∷ []) (CS04⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS03⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS03⁻ ∷ [])
                        wleaf
                      )
                      (Toff134 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff134 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ024 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K3⁻ ∷ Toff204 ∷ []) (Toff204 ∷ K3⁻ ∷ [])
                        wleaf
                      )
                      (CX01 ∷ Toff214 ∷ []) (Toff214 ∷ CX01 ∷ Toff204 ∷ [])
                      wleaf
                    )
                    (CS24⁻ ∷ CS04⁻ ∷ CCZ024 ∷ CS04⁻ ∷ CZ04 ∷ CCZ024 ∷ []) (CS24⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff103 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ Toff103 ∷ [])
                        wleaf
                      )
                      (CX34 ∷ Toff013 ∷ Toff013 ∷ []) (CX34 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX24 ∷ Toff302 ∷ Toff302 ∷ []) (CX24 ∷ [])
                        wleaf
                      )
                      (Toff014 ∷ Toff024 ∷ []) (Toff024 ∷ Toff014 ∷ [])
                      wleaf
                    )
                    (CS03 ∷ Toff234 ∷ []) (Toff234 ∷ CS03 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS12 ∷ Toff402 ∷ []) (Toff402 ∷ CS12 ∷ [])
                        wleaf
                      )
                      (CS02⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS02⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CX42 ∷ CCZ014 ∷ []) (CX42 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff304 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff304 ∷ [])
                        wleaf
                      )
                      (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ X0 ∷ []) (X0 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CX40 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ CCZ013 ∷ S4 ∷ CS14 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ Toff013 ∷ CCZ134 ∷ []) (Toff013 ∷ CCZ034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ []) (S4 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ CZ01 ∷ Toff401 ∷ CCZ014 ∷ []) (Toff401 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ CX34 ∷ []) (CX34 ∷ CCZ023 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ CK42 ∷ []) (CK42 ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (CX20 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ [])
                        wleaf
                      )
                      (K3⁻ ∷ Toff024 ∷ []) (Toff024 ∷ K3⁻ ∷ [])
                      wleaf
                    )
                    (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K3⁻ ∷ Toff402 ∷ []) (Toff402 ∷ K3⁻ ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) (CCZ124 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (X4 ∷ CCZ024 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ034 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ CCZ034 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ [])
                        wleaf
                      )
                      (CX31 ∷ Toff134 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX31 ∷ Toff134 ∷ [])
                      wleaf
                    )
                  )
                  (CX14 ∷ Toff013 ∷ Toff013 ∷ []) (CX14 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff204 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff204 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                    (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS34⁻ ∷ Toff103 ∷ []) (Toff103 ∷ CS34⁻ ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CX43 ∷ []) (CX43 ∷ CCZ014 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ CZ24 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ Toff034 ∷ CCZ034 ∷ CZ03 ∷ CK40 ∷ CZ03 ∷ S4 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                    (Sw02 ∷ Toff104 ∷ []) (Toff124 ∷ Sw02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff103 ∷ CCZ034 ∷ []) (Toff103 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ CS34 ∷ []) (CS34 ∷ CS04 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ024 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX31 ∷ Toff034 ∷ Toff034 ∷ []) (CX31 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ Toff013 ∷ CCZ134 ∷ []) (Toff013 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (Toff013 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ Toff013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS34 ∷ K2 ∷ CK02 ∷ S0 ∷ []) (K2 ∷ CK02 ∷ S0 ∷ CS34 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ CK43 ∷ []) (CZ03 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (X4 ∷ CCZ014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
                        wleaf
                      )
                      (CX14 ∷ Toff201 ∷ Toff201 ∷ []) (CX14 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K2 ∷ CK02 ∷ S0 ∷ Toff402 ∷ []) (Toff402 ∷ K2 ∷ CK02 ∷ S0 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CX01 ∷ CCZ034 ∷ []) (CX01 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CX41 ∷ Toff304 ∷ []) (Toff304 ∷ CX41 ∷ [])
                      wleaf
                    )
                    (S0 ∷ CS24 ∷ CCZ024 ∷ CS24 ∷ CZ24 ∷ CCZ024 ∷ []) (S0 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff403 ∷ Toff203 ∷ Toff423 ∷ []) (Toff423 ∷ Toff203 ∷ [])
                        wleaf
                      )
                      (CS01 ∷ Toff204 ∷ []) (Toff204 ∷ CS01 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ012 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ012 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) []
                        wleaf
                      )
                      (CCZ014 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CZ03 ∷ CX34 ∷ []) (CX34 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ034 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ CCZ014 ∷ []) (Toff301 ∷ CCZ034 ∷ Toff301 ∷ [])
                      wleaf
                    )
                  )
                  (CS04 ∷ CS34 ∷ CCZ034 ∷ CS34 ∷ CZ34 ∷ CCZ034 ∷ []) (CS04 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CX03 ∷ []) (CX03 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CX10 ∷ Toff204 ∷ []) (Toff204 ∷ CX10 ∷ Toff214 ∷ [])
                    (wnode
                      wleaf
                      (CX30 ∷ Toff324 ∷ []) (Toff324 ∷ CX30 ∷ Toff024 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (CCZ134 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ134 ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS24⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS24⁻ ∷ [])
                        wleaf
                      )
                      (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ Toff034 ∷ CCZ134 ∷ []) (Toff034 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX14 ∷ Toff201 ∷ []) (Toff201 ∷ CX14 ∷ [])
                        wleaf
                      )
                      (CX13 ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX13 ∷ Toff314 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ CX43 ∷ []) (CX43 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CCZ034 ∷ Toff103 ∷ CCZ034 ∷ []) (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CS14 ∷ []) (CS14 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ013 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ013 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX04 ∷ Toff302 ∷ Toff302 ∷ []) (CX04 ∷ [])
                        wleaf
                      )
                      (CX32 ∷ Toff024 ∷ []) (Toff024 ∷ CX32 ∷ Toff034 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) (Toff401 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ []) (Toff402 ∷ CCZ012 ∷ Toff402 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CX30 ∷ []) (CX30 ∷ CCZ234 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                  (CX13 ∷ Toff014 ∷ Toff014 ∷ []) (CX13 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ []) (CX31 ∷ CCZ034 ∷ CX31 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff301 ∷ Toff413 ∷ []) (Toff413 ∷ Toff401 ∷ Toff301 ∷ [])
                        wleaf
                      )
                      (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ []) (Toff214 ∷ CCZ014 ∷ Toff214 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ []) (CCZ234 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (Sw34 ∷ Toff023 ∷ []) (Toff024 ∷ Sw34 ∷ [])
                      wleaf
                    )
                  )
                  (CX32 ∷ Toff034 ∷ []) (Toff034 ∷ CX32 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CX01 ∷ CCZ024 ∷ []) (CX01 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CX04 ∷ []) (CX04 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CCZ013 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CX43 ∷ Toff203 ∷ []) (Toff203 ∷ CX43 ∷ Toff204 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1⁻ ∷ []) (Toff104 ∷ [])
                        wleaf
                      )
                      (Toff023 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff023 ∷ [])
                      wleaf
                    )
                    (CX02 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ Toff402 ∷ []) (Toff402 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) (CK41 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                  (CS34⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS34⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ []) (Toff314 ∷ CS03 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff023 ∷ CCZ234 ∷ []) (Toff023 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS12 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS24⁻ ∷ CX23 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ CS24⁻ ∷ [])
                        wleaf
                      )
                      (Toff024 ∷ Toff302 ∷ []) (Toff302 ∷ Toff024 ∷ Toff324 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CZ04 ∷ CCZ024 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX04 ∷ Toff302 ∷ []) (Toff302 ∷ CX04 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ []) (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ [])
                      wleaf
                    )
                    (CX41 ∷ Toff013 ∷ []) (Toff013 ∷ CX41 ∷ Toff034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CS14 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (X0 ∷ CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ X0 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (X4 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ014 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw03 ∷ Toff234 ∷ []) (Toff204 ∷ Sw03 ∷ [])
                        wleaf
                      )
                      (CX01 ∷ Toff304 ∷ Toff304 ∷ []) (CX01 ∷ [])
                      wleaf
                    )
                    (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ []) (CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ []) (CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw24 ∷ Toff012 ∷ []) (Toff014 ∷ Sw24 ∷ [])
                        wleaf
                      )
                      (S1 ∷ CS14⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S1 ∷ CS14⁻ ∷ [])
                      wleaf
                    )
                    (CS04⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS04⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ []) (CX23 ∷ Toff302 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04 ∷ [])
                      wleaf
                    )
                  )
                  (K0⁻ ∷ CCZ034 ∷ []) (Toff034 ∷ K0⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS24⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS24⁻ ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ []) (CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ [])
                      wleaf
                    )
                    (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff302 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ []) (CCZ134 ∷ Toff413 ∷ CZ04 ∷ Toff413 ∷ CCZ134 ∷ CZ04 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX04 ∷ CX40 ∷ CX04 ∷ []) (Sw04 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) (CX42 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (Toff403 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ []) (CZ01 ∷ CCZ014 ∷ CZ01 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff134 ∷ CCZ034 ∷ []) (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                  (CX14 ∷ Toff024 ∷ []) (Toff024 ∷ CX14 ∷ Toff012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ []) (Toff034 ∷ CCZ134 ∷ Toff034 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ034 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CX43 ∷ Toff014 ∷ Toff014 ∷ []) (CX43 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ014 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (Toff034 ∷ K3 ∷ CK43 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ []) (CX20 ∷ CCZ124 ∷ CX20 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS23 ∷ Toff403 ∷ []) (Toff403 ∷ CS23 ∷ [])
                        wleaf
                      )
                      (K4 ∷ CK34 ∷ ι ∷ []) (K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ ι ∷ [])
                      wleaf
                    )
                  )
                  (CS24⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS24⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff301 ∷ CS34 ∷ []) (Toff301 ∷ CS34 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (CCZ034 ∷ [])
                    (wnode
                      wleaf
                      (CCZ034 ∷ CX42 ∷ []) (CX42 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
      (CCZ034 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ034 ∷ [])
      (wnode
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (Toff024 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                    (S0⁻ ∷ CS04 ∷ []) (X4 ∷ CS04⁻ ∷ X4 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ S4 ∷ CS04⁻ ∷ []) (S4 ∷ CS04⁻ ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CCZ234 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX30 ∷ Toff234 ∷ Toff234 ∷ []) (CX30 ∷ [])
                        wleaf
                      )
                      (S1 ∷ CS14⁻ ∷ Toff013 ∷ []) (Toff013 ∷ S1 ∷ CS14⁻ ∷ [])
                      wleaf
                    )
                    (CS03 ∷ Toff403 ∷ []) (Toff403 ∷ CS03 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX01 ∷ Toff403 ∷ Toff403 ∷ []) (CX01 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ []) (CX21 ∷ CCZ024 ∷ CX21 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw04 ∷ Toff302 ∷ []) (Toff324 ∷ Sw04 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CX24 ∷ []) (CX24 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ Toff403 ∷ []) (Toff403 ∷ CZ03 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff302 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff302 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ Toff134 ∷ []) (Toff134 ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ Sw14 ∷ []) (Sw14 ∷ CCZ024 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK40 ∷ S4 ∷ []) (CK40⁻ ∷ [])
                        wleaf
                      )
                      (CCZ134 ∷ CS03 ∷ []) (CS03 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ []) (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS02 ∷ Toff402 ∷ []) (Toff402 ∷ CS02 ∷ [])
                        wleaf
                      )
                      (CS12 ∷ Toff014 ∷ []) (Toff014 ∷ CS12 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ Toff304 ∷ []) (Toff304 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (CS34 ∷ Toff014 ∷ []) (Toff014 ∷ CS34 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ024 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX03 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX03 ∷ [])
                        wleaf
                      )
                      (CZ01 ∷ CCZ014 ∷ []) (CZ01 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS04⁻ ∷ Toff201 ∷ []) (Toff201 ∷ CS04⁻ ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ [])
                      wleaf
                    )
                    (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ X0 ∷ CZ34 ∷ []) (X0 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CS04 ∷ CS04 ∷ []) (CS04 ∷ CS04 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                )
                (CS23 ∷ CCZ234 ∷ []) (CS23 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ []) (S4 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CZ04 ∷ Toff304 ∷ CCZ034 ∷ []) (Toff304 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ []) (Toff403 ∷ CCZ023 ∷ Toff403 ∷ [])
                        wleaf
                      )
                      (CS34 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS34 ∷ [])
                      wleaf
                    )
                  )
                  (CX10 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX10 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (Toff201 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ K0 ∷ []) (K0 ∷ Toff014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ034 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ CCZ023 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CS04⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS04⁻ ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CS01 ∷ Toff024 ∷ []) (CS01 ∷ Toff024 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ [])
                      wleaf
                    )
                    (Sw24 ∷ Toff304 ∷ []) (Toff302 ∷ Sw24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS04 ∷ X0 ∷ []) (X0 ∷ S4 ∷ CS04⁻ ∷ [])
                        wleaf
                      )
                      (Toff013 ∷ Toff014 ∷ []) (Toff014 ∷ Toff013 ∷ [])
                      wleaf
                    )
                  )
                  (CS23 ∷ Toff034 ∷ []) (Toff034 ∷ CS23 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS04⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS04⁻ ∷ [])
                        wleaf
                      )
                      (CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ [])
                      wleaf
                    )
                    (CS03⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS04⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ []) (Toff401 ∷ CCZ012 ∷ Toff401 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CX43 ∷ []) (CX43 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ CX23 ∷ []) (CX23 ∷ CCZ024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ K0 ∷ []) (K0 ∷ Toff034 ∷ CCZ034 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (Sw02 ∷ Toff412 ∷ []) (Toff401 ∷ Sw02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff413 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff413 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ CS14 ∷ []) (CS14 ∷ CS04 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX31 ∷ Toff014 ∷ []) (Toff014 ∷ CX31 ∷ Toff034 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS02⁻ ∷ CS04⁻ ∷ CCZ024 ∷ CS04⁻ ∷ CZ04 ∷ CCZ024 ∷ []) (CS02⁻ ∷ [])
                        wleaf
                      )
                      (CX41 ∷ Toff024 ∷ Toff024 ∷ []) (CX41 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK42 ∷ [])
                        wleaf
                      )
                      (CS03 ∷ Toff204 ∷ []) (Toff204 ∷ CS03 ∷ [])
                      wleaf
                    )
                    (Toff401 ∷ Toff401 ∷ []) []
                    (wnode
                      (wnode
                        wleaf
                        (CX21 ∷ Toff402 ∷ Toff402 ∷ []) (CX21 ∷ [])
                        wleaf
                      )
                      (CS34⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS34⁻ ∷ [])
                      wleaf
                    )
                  )
                  (Sw24 ∷ Toff302 ∷ []) (Toff304 ∷ Sw24 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff302 ∷ CCZ024 ∷ []) (Toff302 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CX10 ∷ Toff304 ∷ []) (Toff304 ∷ CX10 ∷ Toff314 ∷ [])
                      wleaf
                    )
                    (S0 ∷ Toff024 ∷ []) (Toff024 ∷ S0 ∷ CS24 ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff402 ∷ CZ02 ∷ []) (Toff402 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ124 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ []) (CZ34 ∷ CCZ034 ∷ CZ34 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (Sw02 ∷ Toff401 ∷ []) (Toff412 ∷ Sw02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff401 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff401 ∷ [])
                        wleaf
                      )
                      (CZ03 ∷ CK43 ∷ CZ03 ∷ CZ03 ∷ []) (CZ03 ∷ CK43 ∷ [])
                      wleaf
                    )
                  )
                  (CX30 ∷ Toff034 ∷ []) (Toff034 ∷ CX30 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
                        wleaf
                      )
                      (CS02⁻ ∷ CX23 ∷ Toff324 ∷ []) (CX23 ∷ Toff324 ∷ CS02⁻ ∷ [])
                      wleaf
                    )
                    (CCZ023 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ023 ∷ CCZ034 ∷ [])
                    (wnode
                      wleaf
                      (CCZ014 ∷ CX30 ∷ CCZ134 ∷ []) (CX30 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (Toff034 ∷ X2 ∷ []) (X2 ∷ Toff034 ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff304 ∷ []) (Toff304 ∷ CZ04 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CX34 ∷ Toff024 ∷ []) (Toff024 ∷ CX34 ∷ Toff023 ∷ [])
                      wleaf
                    )
                    (CX24 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX24 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS34 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS34 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) (CX41 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw02 ∷ Toff304 ∷ []) (Toff324 ∷ Sw02 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                    (CCZ013 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ []) (CZ02 ∷ CCZ024 ∷ CZ02 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CS04 ∷ []) (CS04 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ124 ∷ []) (Toff024 ∷ CCZ124 ∷ Toff024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ CX04 ∷ []) (CX04 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ [])
                      wleaf
                    )
                    (CX20 ∷ Toff412 ∷ []) (Toff412 ∷ CX20 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff302 ∷ Toff423 ∷ []) (Toff423 ∷ Toff402 ∷ Toff302 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ []) (Toff034 ∷ CCZ234 ∷ Toff034 ∷ [])
                      wleaf
                    )
                  )
                  (CS24 ∷ Toff034 ∷ []) (Toff034 ∷ CS24 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ []) (CX13 ∷ CCZ014 ∷ CX13 ∷ [])
                        wleaf
                      )
                      (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS13 ∷ Toff403 ∷ []) (Toff403 ∷ CS13 ∷ [])
                        wleaf
                      )
                      (CS34 ∷ Toff024 ∷ []) (Toff024 ∷ CS34 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (Toff214 ∷ CCZ024 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff301 ∷ Toff304 ∷ []) (Toff304 ∷ Toff301 ∷ [])
                        wleaf
                      )
                      (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ [])
                      wleaf
                    )
                    (CS02 ∷ Toff324 ∷ []) (Toff324 ∷ CS02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS02⁻ ∷ S4 ∷ Toff402 ∷ S4⁻ ∷ []) (Toff402 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CX43 ∷ []) (CX43 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CX24 ∷ []) (CX24 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ012 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CS04⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS04⁻ ∷ [])
                      wleaf
                    )
                    (CS14 ∷ Toff014 ∷ []) (Toff014 ∷ CS14 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CX12 ∷ Toff201 ∷ []) (CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (K2 ∷ CK42 ∷ S4 ∷ []) (K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ CS14 ∷ []) (CS14 ∷ CCZ034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ K1 ∷ []) (K1 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (K3 ∷ CK43 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K3 ∷ CK43 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ034 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX32 ∷ Toff402 ∷ []) (Toff402 ∷ CX32 ∷ Toff403 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ CS12 ∷ []) (CS12 ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                  (CS03 ∷ CS34 ∷ CCZ034 ∷ CS34 ∷ CZ34 ∷ CCZ034 ∷ []) (CS03 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK40⁻ ∷ CK40 ∷ []) []
                        wleaf
                      )
                      (CCZ024 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ K0⁻ ∷ []) (K0⁻ ∷ Toff024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff423 ∷ CCZ023 ∷ []) (Toff423 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (K0 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ K0⁻ ∷ []) (Toff024 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CCZ024 ∷ CZ04 ∷ Toff204 ∷ CCZ024 ∷ []) (Toff204 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX42 ∷ Toff302 ∷ []) (Toff302 ∷ CX42 ∷ Toff304 ∷ [])
                        wleaf
                      )
                      (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS03 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (CX14 ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (S4 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ [])
                        wleaf
                      )
                      (CX31 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX31 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ014 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX40 ∷ Toff234 ∷ []) (Toff234 ∷ CX40 ∷ [])
                        wleaf
                      )
                      (CX40 ∷ Toff314 ∷ []) (Toff314 ∷ CX40 ∷ [])
                      wleaf
                    )
                    (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CZ24 ∷ []) (CZ24 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CX43 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX43 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (Toff014 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (S0 ∷ CS04⁻ ∷ X4 ∷ []) (X4 ∷ CS04 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ []) (CZ04 ∷ CCZ034 ∷ CZ04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ Toff134 ∷ []) (Toff134 ∷ CS04 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ []) (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ CCZ234 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ CCZ012 ∷ [])
                      wleaf
                    )
                    (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ Toff401 ∷ []) (Toff401 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (Sw23 ∷ Toff034 ∷ []) (Toff024 ∷ Sw23 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ Toff014 ∷ CZ14 ∷ []) (Toff014 ∷ CCZ014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX40 ∷ Toff324 ∷ Toff324 ∷ []) (CX40 ∷ [])
                        wleaf
                      )
                      (Sw14 ∷ Toff012 ∷ []) (Toff024 ∷ Sw14 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CS23 ∷ []) (CS23 ∷ CCZ034 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CZ01 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff012 ∷ CCZ124 ∷ []) (Toff012 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ013 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ K2 ∷ []) (K2 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CX41 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ013 ∷ S4 ∷ CS04 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ014 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ014 ∷ CCZ124 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Sw02 ∷ []) (Sw02 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ []) (CX02 ∷ CCZ014 ∷ CX02 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ024 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ S3 ∷ []) (S3 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CX40 ∷ CCZ124 ∷ []) (CX40 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) []
                        wleaf
                      )
                      (CCZ134 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                    (CCZ034 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ CCZ034 ∷ [])
                    (wnode
                      wleaf
                      (CX24 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX24 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
        (Toff034 ∷ Toff034 ∷ []) []
        (wnode
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ CS02 ∷ Toff214 ∷ []) (CS02 ∷ Toff214 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (CCZ134 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ024 ∷ []) (CZ24 ∷ CCZ024 ∷ CZ24 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw03 ∷ Toff423 ∷ []) (Toff402 ∷ Sw03 ∷ [])
                        wleaf
                      )
                      (CS12 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CS12 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff413 ∷ CCZ013 ∷ []) (Toff413 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) []
                      wleaf
                    )
                  )
                )
                (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX40 ∷ Toff324 ∷ []) (Toff324 ∷ CX40 ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ Sw24 ∷ []) (Sw24 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ CX34 ∷ []) (CX34 ∷ CS04⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ K1 ∷ CK01 ∷ S0 ∷ []) (K1 ∷ CK01 ∷ S0 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CZ02 ∷ CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CZ02 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ []) (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K3 ∷ Toff204 ∷ []) (Toff204 ∷ K3 ∷ [])
                        wleaf
                      )
                      (CX40 ∷ Toff214 ∷ []) (Toff214 ∷ CX40 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ Toff204 ∷ []) (Toff204 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS12⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                      (Sw34 ∷ Toff103 ∷ []) (Toff104 ∷ Sw34 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CK41 ∷ CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (CCZ234 ∷ CS03 ∷ []) (CS03 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff402 ∷ Toff423 ∷ []) (Toff423 ∷ Toff402 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ CX10 ∷ CCZ124 ∷ []) (CX10 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ [])
                      wleaf
                    )
                    (CS04⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS02 ∷ Toff403 ∷ []) (Toff403 ∷ CS02 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ CK41 ∷ []) (CZ01 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
                (CS14 ∷ Toff012 ∷ []) (Toff012 ∷ CS14 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK34 ∷ CCZ034 ∷ []) (Toff403 ∷ CK34 ∷ [])
                        wleaf
                      )
                      (K1 ∷ CK41 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ [])
                      wleaf
                    )
                    (K4 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ K4⁻ ∷ []) (Toff401 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ []) (CX34 ∷ CCZ023 ∷ CX34 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ Toff324 ∷ []) (Toff324 ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                  (CS03 ∷ Toff034 ∷ []) (Toff034 ∷ CS03 ∷ CS34 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ234 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (K3 ∷ Toff024 ∷ []) (Toff024 ∷ K3 ∷ [])
                      wleaf
                    )
                    (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS13⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS12⁻ ∷ Toff402 ∷ []) (Toff402 ∷ CS12⁻ ∷ [])
                        wleaf
                      )
                      (CS04 ∷ Toff314 ∷ []) (Toff314 ∷ CS04 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CCZ024 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ023 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ [])
                        wleaf
                      )
                      (CS24 ∷ Toff204 ∷ []) (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CCZ234 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                  (Sw14 ∷ Toff034 ∷ []) (Toff013 ∷ Sw14 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CX10 ∷ Toff314 ∷ []) (Toff314 ∷ CX10 ∷ [])
                      wleaf
                    )
                    (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS02 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) (CS02 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) (CCZ013 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CZ24 ∷ CCZ024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ034 ∷ [])
                      wleaf
                    )
                    (CCZ234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff103 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff103 ∷ [])
                        wleaf
                      )
                      (CK42 ∷ CS04 ∷ []) (CS04 ∷ CK42 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ []) (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Sw13 ∷ Toff403 ∷ []) (Toff401 ∷ Sw13 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ034 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS04⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (K3 ∷ CK43 ∷ S4 ∷ []) (K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX04 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX04 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (Toff012 ∷ CCZ014 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX03 ∷ Toff423 ∷ []) (Toff423 ∷ CX03 ∷ Toff402 ∷ [])
                        wleaf
                      )
                      (CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) (CX41 ∷ CCZ013 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ134 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ134 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ []) (CCZ024 ∷ [])
                      wleaf
                    )
                    (CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (Toff403 ∷ Toff423 ∷ []) (Toff423 ∷ Toff403 ∷ [])
                        wleaf
                      )
                      (CX34 ∷ Toff203 ∷ Toff203 ∷ []) (CX34 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ034 ∷ CZ34 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ013 ∷ Toff304 ∷ CCZ014 ∷ []) (Toff304 ∷ CCZ013 ∷ [])
                        wleaf
                      )
                      (K0 ∷ CK40 ∷ S4 ∷ Toff324 ∷ []) (Toff324 ∷ K0 ∷ CK40 ∷ S4 ∷ [])
                      wleaf
                    )
                    (CCZ012 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ012 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ Toff413 ∷ []) (Toff413 ∷ CS01 ∷ [])
                        wleaf
                      )
                      (CZ01 ∷ Toff024 ∷ []) (Toff024 ∷ CZ01 ∷ CCZ124 ∷ [])
                      wleaf
                    )
                  )
                  (CS04⁻ ∷ CS34⁻ ∷ CCZ034 ∷ CS34⁻ ∷ CZ34 ∷ CCZ034 ∷ []) (CS04⁻ ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
                        wleaf
                      )
                      (CX30 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX30 ∷ [])
                      wleaf
                    )
                    (CX41 ∷ Toff204 ∷ []) (Toff204 ∷ CX41 ∷ [])
                    (wnode
                      wleaf
                      (CCZ134 ∷ Sw03 ∷ []) (Sw03 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
          (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (Toff204 ∷ [])
          (wnode
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (K2⁻ ∷ Toff304 ∷ []) (Toff304 ∷ K2⁻ ∷ [])
                        wleaf
                      )
                      (CX34 ∷ Toff023 ∷ Toff023 ∷ []) (CX34 ∷ [])
                      wleaf
                    )
                    (CX34 ∷ Toff023 ∷ []) (Toff023 ∷ CX34 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K1 ∷ CK01 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ K1 ∷ CK01 ∷ S0 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ []) (CZ04 ∷ CCZ024 ∷ CZ04 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ012 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (Toff204 ∷ CCZ234 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                    (CCZ014 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff103 ∷ []) (Toff103 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CS14 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS14 ∷ [])
                      wleaf
                    )
                  )
                )
                (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ []) (CCZ124 ∷ [])
                        wleaf
                      )
                      (CS14 ∷ Toff024 ∷ []) (Toff024 ∷ CS14 ∷ [])
                      wleaf
                    )
                    (CX10 ∷ Toff412 ∷ []) (Toff412 ∷ CX10 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ014 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ012 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (CCZ234 ∷ []) (CX30 ∷ CCZ234 ∷ CX30 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ Sw13 ∷ []) (Sw13 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ CX13 ∷ []) (CX13 ∷ CCZ014 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CX32 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX32 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX31 ∷ Toff103 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX31 ∷ Toff103 ∷ [])
                        wleaf
                      )
                      (CX14 ∷ Toff012 ∷ []) (Toff012 ∷ CX14 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ []) (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX41 ∷ Toff301 ∷ []) (Toff301 ∷ CX41 ∷ Toff304 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ [])
                      wleaf
                    )
                    (CCZ234 ∷ CS04 ∷ []) (CS04 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX21 ∷ Toff401 ∷ []) (Toff401 ∷ CX21 ∷ Toff402 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (Toff324 ∷ CCZ023 ∷ [])
                      wleaf
                    )
                  )
                  (CX24 ∷ Toff023 ∷ Toff023 ∷ []) (CX24 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX01 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX01 ∷ [])
                        wleaf
                      )
                      (CCZ014 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                    (CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS13⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ124 ∷ CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ []) (CX12 ∷ Toff201 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CX04 ∷ Toff203 ∷ []) (Toff203 ∷ CX04 ∷ [])
                      wleaf
                    )
                  )
                )
                (CX23 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX23 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ CCZ034 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CS13⁻ ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CS13⁻ ∷ [])
                      wleaf
                    )
                    (CCZ234 ∷ CX20 ∷ []) (CX20 ∷ CCZ234 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX32 ∷ Toff403 ∷ Toff403 ∷ []) (CX32 ∷ [])
                        wleaf
                      )
                      (CK42 ∷ CS03 ∷ []) (CS03 ∷ CK42 ∷ [])
                      wleaf
                    )
                  )
                  (CZ03 ∷ Toff034 ∷ []) (Toff034 ∷ CZ03 ∷ CZ34 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CS01 ∷ []) (Toff314 ∷ CS03 ∷ CS01 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
                        wleaf
                      )
                      (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) (Toff214 ∷ CCZ012 ∷ [])
                      wleaf
                    )
                    (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CK03 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CK03 ∷ [])
                        wleaf
                      )
                      (CS24 ∷ Toff302 ∷ []) (Toff302 ∷ CS24 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
            (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ013 ∷ [])
            (wnode
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CX42 ∷ Toff304 ∷ Toff304 ∷ []) (CX42 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ013 ∷ CCZ134 ∷ [])
                      wleaf
                    )
                    (CX34 ∷ Toff013 ∷ []) (Toff013 ∷ CX34 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ CZ02 ∷ Toff402 ∷ CCZ024 ∷ []) (Toff402 ∷ [])
                        wleaf
                      )
                      (X4 ∷ CZ03 ∷ CZ03 ∷ []) (X4 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ014 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff234 ∷ Toff304 ∷ []) (Toff304 ∷ Toff204 ∷ Toff234 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ []) (CX01 ∷ CCZ024 ∷ CX01 ∷ [])
                      wleaf
                    )
                    (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ K0 ∷ []) (K0 ∷ Toff024 ∷ CCZ024 ∷ CCZ024 ∷ [])
                      wleaf
                    )
                  )
                )
                (CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS34⁻ ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ []) (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ124 ∷ [])
                        wleaf
                      )
                      (CS03⁻ ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CS03⁻ ∷ [])
                      wleaf
                    )
                    (CS04⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04⁻ ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) (Toff403 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CK40 ∷ CS24 ∷ []) (CS24 ∷ CK40 ∷ [])
                      wleaf
                    )
                  )
                  (CCZ034 ∷ S0 ∷ []) (S0 ∷ CCZ034 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (Toff014 ∷ Toff314 ∷ []) (Toff314 ∷ Toff014 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ034 ∷ [])
                      wleaf
                    )
                    (CCZ024 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CCZ024 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS13⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS13⁻ ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (Toff314 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                )
              )
              (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ [])
              (wnode
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ CX04 ∷ []) (CX04 ∷ CCZ012 ∷ [])
                        wleaf
                      )
                      (CCZ023 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ023 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (K3⁻ ∷ Toff401 ∷ []) (Toff401 ∷ K3⁻ ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ [])
                      wleaf
                    )
                  )
                  (CS23 ∷ Toff024 ∷ []) (Toff024 ∷ CS23 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ034 ∷ CCZ134 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ034 ∷ [])
                        wleaf
                      )
                      (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (Toff314 ∷ CCZ034 ∷ [])
                      wleaf
                    )
                    (Toff013 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ Toff013 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CS04⁻ ∷ Toff402 ∷ []) (Toff402 ∷ CS04⁻ ∷ CS02⁻ ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ013 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ014 ∷ [])
                      wleaf
                    )
                  )
                )
                (CCZ034 ∷ Toff023 ∷ CCZ234 ∷ []) (Toff023 ∷ CCZ034 ∷ [])
                (wnode
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ012 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ012 ∷ CCZ014 ∷ [])
                        wleaf
                      )
                      (Toff013 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff013 ∷ [])
                      wleaf
                    )
                    (CCZ124 ∷ CX02 ∷ []) (CX02 ∷ CCZ014 ∷ CCZ124 ∷ [])
                    (wnode
                      (wnode
                        wleaf
                        (CX10 ∷ Toff413 ∷ Toff413 ∷ []) (CX10 ∷ [])
                        wleaf
                      )
                      (Toff402 ∷ CS14 ∷ Toff402 ∷ CS14⁻ ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ [])
                      wleaf
                    )
                  )
                  (CX40 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX40 ∷ [])
                  (wnode
                    (wnode
                      (wnode
                        wleaf
                        (CCZ024 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CCZ024 ∷ [])
                        wleaf
                      )
                      (CCZ024 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ [])
                      wleaf
                    )
                    (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ [])
                    (wnode
                      wleaf
                      (CCZ012 ∷ CX42 ∷ []) (CX42 ∷ CCZ014 ∷ CCZ012 ∷ [])
                      wleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )

WsL : Set
WsL = WProofs windowsL

record Ws : Set where
  no-eta-equality
  field
    lit : WsL
    pl  : WProofs windowsP

open Ws public using (lit)

-- The n-th literal and placed windows.
wl : (n : ℕ) → WsL → WinT windowsL n
wl n W = wget windowsL W n

wp : (n : ℕ) → Ws → WinT windowsP n
wp n W = wget windowsP (Ws.pl W) n
