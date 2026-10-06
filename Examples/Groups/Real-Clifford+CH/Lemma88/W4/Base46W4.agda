------------------------------------------------------------------------
-- Presentations of groups
--
-- The four-wire steps of rule (46) on four qubits (Clément, Appendix E.5
-- at n = 4, from Lemma D.5)
--
-- Base46's equations are evaluations on four wires; on four qubits they
-- are derived.  Seventeen are facts about networks: two networks with
-- the same permutation are equal (PermCalc.perm-≈), and a rigid gate —
-- X, P ⊗ P, the box — placed by two networks that agree on its wires is
-- the same (Placed.frame).  The other two say that ζ η splits over the
-- colour of wire 0: ζ and η are merges of the box on wire 3 over that
-- colour (canon4's merge relabelled), and what is left is the crux, the
-- box on wire 3 black on wire 0 against P ⊗ P on the wires 1 2 around
-- its copy white on wire 0.  Under P ⊗ P on the wires 1 3 that is two H
-- gates with the box wire 3: the merge (171) under (0 3) splits one into
-- the CH from wire 0 onto wire 1 and an H gate black on wire 2, which
-- passes the other by (203) under (0 2), while the CH passes it by (164)
-- under the cycle 0 → 3 → 2 → 0 and X on wire 0.  Every step was checked
-- numerically first (scratchpad small-widths/r4546/t46crux.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W4.Base46W4
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (_<_ ; s≤s ; z≤n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; X² ; Ex²)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; perm ; perm-≈)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₀₁ ; module S₁₂ ; module S₂₃ ; L ; U ; P₀₃ ; P₁₃ ; P₂₃ ; L₀ ; U₀ ; O₀ ;
         L-sem ; L₃-sem ; U₃-sem ; P₀₃-sem ; P₂₃-S₀₁ ; P₂₃-L ; L-S₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃ using (box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃ using (°box₃ ; eq164 ; eq171′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃ using (box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃ using (ΛH₂′ ; °ΛH₂′ ; eq181)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃ using (N₂-box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃ using (S₂₃-box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (PP₀₃ ; PP₁₃ ; PP₁₃² ; box₃‴ ; °ΛH₂′-PP ; S₀₁-ΛH₂′-PP ; S₀₁-box₃‴)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (eq203 ; T₀₃-via ; T₀₃-L ; T₀₃-box₃ ; T₀₃-box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (module T₁₃ ; module T₀₃ ; t₀₃² ; T₁₃-via ; T₁₃-L ; T₁₃-P₁₃ ; T₁₃-P₀₃ ; T₀₃-nest′ ;
         S₁₂-X₁ ; S₁₂-X₂ ; S₁₂-X₃ ; S₂₃-X₂ ; S₂₃-X₃ ; S₁₂-P₀₃ ; braid-conj↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (revS ; net-inv ; net-inv′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl ; pl-cong ; pl-• ; pl-•₃ ; Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (Rigid ; frame ; frame₁ ; pl-pl)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceFrames using (conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Networks using (scyc ; scyc⁻¹)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (Hg₃) renaming (P₁₃ to Pc)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon4 complete₂ complete₃ using (canon4)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base46At using (Base46At)
import Examples.Groups.Real-Clifford+CH.GeneralN.Base46 as B46

open Tools (4 VRel,_===_)
open SS.Below 3 (s≤s (s≤s (s≤s z≤n))) complete₃ using () renaming (by-sem to by-sem₃)

------------------------------------------------------------------------
-- Networks

private
  σ0 σ1 σ2 : Word (S.Gen 4)
  σ0 = S.σ
  σ1 = S.σ S.↑
  σ2 = (S.σ S.↑) S.↑

  ua ub ubb uP : Word (S.Gen 4)
  ua  = σ1 • σ0 • σ2 • σ1 • σ2
  ub  = σ1 • σ0 • σ1 • σ2
  ubb = σ2 • σ1 • σ0
  uP  = σ0 • scyc⁻¹ {0} 3

  πa′≈ : B46.πa′ ≈ net (revS ua)
  πa′≈ = by-passoc (□ • □ • □ • □ • □) ((((□ • □) • □) • □) • □) Eq.refl

  πb′≈ : B46.πb′ ≈ net (revS ub)
  πb′≈ = by-passoc (□ • □ • □ • □) (((□ • □) • □) • □) Eq.refl

  bb≈ : B46.bb ≈ pl ubb (Λ□ 3)
  bb≈ = back _ (back _ (by-passoc (□ • □ • □) ((□ • □) • □) Eq.refl))

  -- Conjugation by a network.
  conjπ : ∀ (u : Word (S.Gen 4)) {w w′ : Circuit 4} → net (revS u) ≈ w′ → net u • w • w′ ≈ pl u w
  conjπ u e = back _ (back _ (sym e))

  -- The rigid gates.
  rigX : Rigid 1 (X {3})
  rigX v = sym (X-↑ (net v))

  rigΛ : Rigid 1 (Λ□ 3)
  rigΛ = Canon.swaps canon4

  rigPP : Rigid 2 (PP {2})
  rigPP v = sym (low-comm PP (net v))

  -- X on the wires 1, 2 and 3 as placements of X on wire 0.
  X1pl : pl σ0 X ≈ X ↑
  X1pl = L-sem (Ex • X • Ex) (X ↑) Eq.refl

  X2pl : pl (σ1 • σ0) X ≈ X ↑ ↑
  X2pl = L₃-sem ((Ex ↑ • Ex) • X • (Ex • Ex ↑)) (X ↑ ↑) Eq.refl

  X3pl : pl (σ2 • σ1 • σ0) X ≈ X ↑ ↑ ↑
  X3pl = begin
    (Ex ↑ ↑ • Ex ↑ • Ex) • X • ((Ex • Ex ↑) • Ex ↑ ↑)
      ≈⟨ by-passoc ((□ • □ • □) • □ • ((□ • □) • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl ⟩
    Ex ↑ ↑ • (Ex ↑ • (Ex • X • Ex) • Ex ↑) • Ex ↑ ↑
      ≈⟨ mid _ _ (mid _ _ X1pl) ⟩
    Ex ↑ ↑ • (Ex ↑ • X ↑ • Ex ↑) • Ex ↑ ↑
      ≈⟨ mid _ _ S₁₂-X₁ ⟩
    Ex ↑ ↑ • X ↑ ↑ • Ex ↑ ↑
      ≈⟨ S₂₃-X₂ ⟩
    X ↑ ↑ ↑ ∎

  -- P ⊗ P on the wires 1 2, and Col's on the wires 1 3.
  PP1pl : pl (σ0 • σ1) PP ≈ PP ↑
  PP1pl = L₃-sem ((Ex • Ex ↑) • PP • (Ex ↑ • Ex)) (PP ↑) Eq.refl

  cyc3≈ : net (revS (scyc⁻¹ {0} 3)) ≈ net (scyc {0} 3)
  cyc3≈ = perm-≈ {u = revS (scyc⁻¹ {0} 3)} {v = scyc {0} 3}
            (λ { 0F → Eq.refl ; (sF 0F) → Eq.refl ; (sF (sF 0F)) → Eq.refl ; (sF (sF (sF 0F))) → Eq.refl })

  Pc≈ : Pc ≈ pl uP PP
  Pc≈ = trans (by-passoc (□ • ((□ • □ • □) • □)) ((□ • □) • □ • (□ • □)) Eq.refl)
              (back _ (back _ (front _ (sym cyc3≈))))

  pl-comm : ∀ (u : Word (S.Gen 4)) {a b : Circuit 4} → a • b ≈ b • a → pl u a • pl u b ≈ pl u b • pl u a
  pl-comm u {a} {b} e = trans (sym (pl-• u a b)) (trans (pl-cong u e) (pl-• u b a))

------------------------------------------------------------------------
-- The network facts

ea₁ : B46.πa • B46.πa′ ≈ ε
ea₁ = trans (back _ πa′≈) (net-inv ua)

ea₂ : B46.πa′ • B46.πa ≈ ε
ea₂ = trans (front _ πa′≈) (net-inv′ ua)

eb₁ : B46.πb • B46.πb′ ≈ ε
eb₁ = trans (back _ πb′≈) (net-inv ub)

eb₂ : B46.πb′ • B46.πb ≈ ε
eb₂ = trans (front _ πb′≈) (net-inv′ ub)

ea-L : B46.πa • (Ex ↑ • Ex) ≈ Ex • (Ex ↑ • Ex ↑ ↑)
ea-L = perm-≈ {u = ua • (σ1 • σ0)} {v = σ0 • (σ1 • σ2)}
         (λ { 0F → Eq.refl ; (sF 0F) → Eq.refl ; (sF (sF 0F)) → Eq.refl ; (sF (sF (sF 0F))) → Eq.refl })

ea-R : (Ex • Ex ↑) • B46.πa′ ≈ (Ex ↑ ↑ • Ex ↑) • Ex
ea-R = trans (back _ πa′≈) (perm-≈ {u = (σ0 • σ1) • revS ua} {v = (σ2 • σ1) • σ0}
         (λ { 0F → Eq.refl ; (sF 0F) → Eq.refl ; (sF (sF 0F)) → Eq.refl ; (sF (sF (sF 0F))) → Eq.refl }))

eb-L : B46.πb • Ex ≈ Ex • (Ex ↑ • Ex ↑ ↑)
eb-L = perm-≈ {u = ub • σ0} {v = σ0 • (σ1 • σ2)}
         (λ { 0F → Eq.refl ; (sF 0F) → Eq.refl ; (sF (sF 0F)) → Eq.refl ; (sF (sF (sF 0F))) → Eq.refl })

eb-R : Ex • B46.πb′ ≈ (Ex ↑ ↑ • Ex ↑) • Ex
eb-R = trans (back _ πb′≈) (perm-≈ {u = σ0 • revS ub} {v = (σ2 • σ1) • σ0}
         (λ { 0F → Eq.refl ; (sF 0F) → Eq.refl ; (sF (sF 0F)) → Eq.refl ; (sF (sF (sF 0F))) → Eq.refl }))

ea-bb : B46.πa • B46.bb • B46.πa′ ≈ Λ□ 3
ea-bb = begin
  B46.πa • B46.bb • B46.πa′          ≈⟨ back _ (cong bb≈ πa′≈) ⟩
  pl ua (pl ubb (Λ□ 3))              ≈⟨ pl-pl ua ubb (Λ□ 3) ⟩
  pl (ua • ubb) (Λ□ 3)               ≈⟨ frame₁ rigΛ (ua • ubb) ε Eq.refl ⟩
  ε • Λ□ 3 • ε                       ≈⟨ trans left-unit right-unit ⟩
  Λ□ 3 ∎

eb-bb : B46.πb • B46.bb • B46.πb′ ≈ Λ□ 3
eb-bb = begin
  B46.πb • B46.bb • B46.πb′          ≈⟨ back _ (cong bb≈ πb′≈) ⟩
  pl ub (pl ubb (Λ□ 3))              ≈⟨ pl-pl ub ubb (Λ□ 3) ⟩
  pl (ub • ubb) (Λ□ 3)               ≈⟨ frame₁ rigΛ (ub • ubb) ε Eq.refl ⟩
  ε • Λ□ 3 • ε                       ≈⟨ trans left-unit right-unit ⟩
  Λ□ 3 ∎

ea-X : B46.πa • X • B46.πa′ ≈ X ↑ ↑
ea-X = trans (back _ (back _ πa′≈)) (trans (frame₁ rigX ua (σ1 • σ0) Eq.refl) X2pl)

ea-X₁ : B46.πa • X ↑ • B46.πa′ ≈ X ↑ ↑ ↑
ea-X₁ = trans (back _ (cong (sym X1pl) πa′≈))
          (trans (pl-pl ua σ0 X) (trans (frame₁ rigX (ua • σ0) (σ2 • σ1 • σ0) Eq.refl) X3pl))

eb-X : B46.πb • X • B46.πb′ ≈ X ↑ ↑
eb-X = trans (back _ (back _ πb′≈)) (trans (frame₁ rigX ub (σ1 • σ0) Eq.refl) X2pl)

eb-X₂ : B46.πb • X ↑ ↑ • B46.πb′ ≈ X ↑ ↑ ↑
eb-X₂ = trans (back _ (cong (sym X2pl) πb′≈))
          (trans (pl-pl ub (σ1 • σ0) X) (trans (frame₁ rigX (ub • (σ1 • σ0)) (σ2 • σ1 • σ0) Eq.refl) X3pl))

ea-P : B46.πa • PP ↑ • B46.πa′ ≈ Pc
ea-P = trans (back _ (cong (sym PP1pl) πa′≈))
         (trans (pl-pl ua (σ0 • σ1) PP) (trans (frame rigPP (ua • (σ0 • σ1)) uP agree) (sym Pc≈)))
  where
  agree : ∀ (j : Fin 4) → toℕ j < 2 → perm uP ⟨$⟩ʳ (perm (revS (ua • (σ0 • σ1))) ⟨$⟩ʳ j) ≡ j
  agree 0F       _ = Eq.refl
  agree (sF 0F)  _ = Eq.refl
  agree (sF (sF _)) (s≤s (s≤s ()))

eb-P : B46.πb • PP ↑ • B46.πb′ ≈ Pc
eb-P = trans (back _ (cong (sym PP1pl) πb′≈))
         (trans (pl-pl ub (σ0 • σ1) PP) (trans (frame rigPP (ub • (σ0 • σ1)) (uP • σ0) agree)
           (trans (sym (pl-pl uP σ0 PP)) (trans (pl-cong uP PPsym) (sym Pc≈)))))
  where
  PPsym : pl σ0 PP ≈ PP
  PPsym = L-sem (Ex • PP • Ex) PP Eq.refl
  agree : ∀ (j : Fin 4) → toℕ j < 2 → perm (uP • σ0) ⟨$⟩ʳ (perm (revS (ub • (σ0 • σ1))) ⟨$⟩ʳ j) ≡ j
  agree 0F       _ = Eq.refl
  agree (sF 0F)  _ = Eq.refl
  agree (sF (sF _)) (s≤s (s≤s ()))

e-X₂P : X ↑ ↑ • Pc ≈ Pc • X ↑ ↑
e-X₂P = trans (cong xe Pc≈) (trans (pl-comm uP c) (sym (cong Pc≈ xe)))
  where
  xe : X ↑ ↑ ≈ pl uP (X ↑ ↑ ↑)
  xe = trans (sym X2pl) (trans (frame₁ rigX (σ1 • σ0) (uP • (σ2 • σ1 • σ0)) Eq.refl)
             (trans (sym (pl-pl uP (σ2 • σ1 • σ0) X)) (pl-cong uP X3pl)))
  c : X ↑ ↑ ↑ • PP ↓ ≈ PP ↓ • X ↑ ↑ ↑
  c = sym (low-comm PP (X ↑))

------------------------------------------------------------------------
-- The splitting of ζ η over the colour of wire 0

private
  Pu² : PP ↑ • PP ↑ ≈ ε
  Pu² = lemma-cong↑ (PP • PP) ε eq111

  τ² : τ₀₂ • τ₀₂ ≈ ε
  τ² = conj-invol Ex² (lemma-cong↑ (Ex • Ex) ε Ex²)

  module TX = Conj {4} X X²
  module Pu = Conj {4} (PP ↑) Pu²
  module Tτ = Conj {4} τ₀₂ τ²
  module Q  = Conj {4} PP₁₃ PP₁₃²

  bb b₁₀ b₀₁ b₀₀ H2 Hp Hp′ : Circuit 4
  bb  = B46.bb
  b₁₀ = B46.b₁₀
  b₀₁ = B46.b₀₁
  b₀₀ = B46.b₀₀
  H2  = P₂₃ PP • b₀₁ • P₂₃ PP
  Hp  = Q.⟪ b₁₀ ⟫
  Hp′ = Q.⟪ bb ⟫

  passL : ∀ {a b y : Circuit 4} → a • y ≈ y • a → b • y ≈ y • b → (a • b) • y ≈ y • (a • b)
  passL ea eb = trans assoc (trans (back _ eb) (trans (sym assoc) (trans (front _ ea) assoc)))

  pass₂ : ∀ {a u v : Circuit 4} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
  pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  sX′ : S₀₁.⟪ X ↑ ⟫ ≈ X
  sX′ = L-sem (Ex • X ↑ • Ex) X Eq.refl

  -- The box on wire 3 is FourQubit's box₃‴.
  b‴≈ : box₃‴ ≈ bb
  b‴≈ = by-passoc (□ • (□ • (□ • □ • □) • □) • □) ((□ • □ • □) • □ • (□ • □ • □)) Eq.refl

  bb² : bb • bb ≈ ε
  bb² = trans (cong bb≈ bb≈) (trans (sym (pl-• ubb (Λ□ 3) (Λ□ 3)))
          (trans (pl-cong ubb (Canon.invol canon4)) (trans (back _ left-unit) (net-inv ubb))))

  -- The merge of the box on wire 3 over the colour of wire 0: canon4's
  -- merge on wire 1, placed.
  pX : pl ubb (X ↑) ≈ X
  pX = trans (pl-cong ubb (sym X1pl)) (trans (pl-pl ubb σ0 X)
         (trans (frame₁ rigX (ubb • σ0) ε Eq.refl) (trans left-unit right-unit)))

  pZ : pl ubb (CZ ↑ ↑) ≈ CZ ↑
  pZ = begin
    (Ex ↑ ↑ • (Ex ↑ • Ex)) • CZ ↑ ↑ • ((Ex • Ex ↑) • Ex ↑ ↑)
      ≈⟨ by-passoc ((□ • (□ • □)) • □ • ((□ • □) • □)) (□ • □ • (□ • □ • □) • □ • □) Eq.refl ⟩
    Ex ↑ ↑ • Ex ↑ • (Ex • CZ ↑ ↑ • Ex) • Ex ↑ • Ex ↑ ↑
      ≈⟨ back _ (back _ (front _ (S₀₁.⟪⟫-fix (low-comm Ex CZ)))) ⟩
    Ex ↑ ↑ • Ex ↑ • CZ ↑ ↑ • Ex ↑ • Ex ↑ ↑
      ≈⟨ U₃-sem (Ex ↑ • Ex • CZ ↑ • Ex • Ex ↑) CZ Eq.refl ⟩
    CZ ↑ ∎

  mb′ : bb • b₀₁ ≈ CZ ↑
  mb′ = begin
    bb • (X • bb • X)
      ≈⟨ cong bb≈ (cong (sym pX) (cong bb≈ (sym pX))) ⟩
    pl ubb (Λ□ 3) • (pl ubb (X ↑) • pl ubb (Λ□ 3) • pl ubb (X ↑))
      ≈⟨ sym (trans (pl-• ubb (Λ□ 3) _) (back _ (pl-•₃ ubb refl refl refl))) ⟩
    pl ubb (Λ□ 3 • (X ↑ • Λ□ 3 • X ↑))
      ≈⟨ pl-cong ubb (Canon.merge canon4) ⟩
    pl ubb (CZ ↑ ↑)
      ≈⟨ pZ ⟩
    CZ ↑ ∎

  mb : b₀₁ • bb ≈ CZ ↑
  mb = TX.⟪⟫-≈ mb′ (TX.⟪⟫-•₂ refl (TX.⟪⟫-⟪⟫ bb)) (TX.⟪⟫-fix (X-↑ CZ))

  nb01 : N₂.⟪ b₀₁ ⟫ ≈ b₀₀
  nb01 = conj-swap (sym (X-↑ (X ↑))) bb

  ζ≈ : B46.ζ ≈ b₀₀ • b₁₀
  ζ≈ = sym (N₂.⟪⟫-≈ mb (N₂.⟪⟫-•₂ nb01 refl) refl)

  ζ≈′ : B46.ζ ≈ b₁₀ • b₀₀
  ζ≈′ = sym (N₂.⟪⟫-≈ mb′ (N₂.⟪⟫-•₂ refl nb01) refl)

  η≈ : B46.η ≈ Pu.⟪ b₀₁ ⟫ • Pu.⟪ bb ⟫
  η≈ = sym (Pu.⟪⟫-≈ mb (Pu.⟪⟫-•₂ refl refl) refl)

  η≈′ : B46.η ≈ Pu.⟪ bb ⟫ • Pu.⟪ b₀₁ ⟫
  η≈′ = sym (Pu.⟪⟫-≈ mb′ (Pu.⟪⟫-•₂ refl refl) refl)

  ----------------------------------------------------------------------
  -- The crux: b₁₀ against P ⊗ P on the wires 1 2 around b₀₁

  -- Under P ⊗ P on the wires 1 3 (the Klein four-group on 1 2 3).
  klein : PP ↑ ≈ PP₁₃ • P₂₃ PP
  klein = U₃-sem PP (O₀ PP • U₀ PP) Eq.refl

  klein′ : PP ↑ ≈ P₂₃ PP • PP₁₃
  klein′ = U₃-sem PP (U₀ PP • O₀ PP) Eq.refl

  qH2 : Q.⟪ H2 ⟫ ≈ Pu.⟪ b₀₁ ⟫
  qH2 = trans (by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl)
              (cong (sym klein) (back _ (sym klein′)))

  x2P : X ↑ ↑ • PP₁₃ ≈ PP₁₃ • X ↑ ↑
  x2P = U₃-sem (X ↑ • O₀ PP) (O₀ PP • X ↑) Eq.refl

  Hp′² : Hp′ • Hp′ ≈ ε
  Hp′² = Q.⟪⟫-invol bb²

  -- (171) under (0 3): Hp is the CH from wire 0 onto wire 1 times Hp′.
  tX₂ : T₀₃.⟪ X ↑ ↑ ⟫ ≈ X ↑ ↑
  tX₂ = T₀₃-via (P₂₃-S₀₁ X) (T₁₃-via S₂₃-X₂ S₁₂-X₃ S₂₃-X₃) (P₂₃-S₀₁ X)

  tPP : T₀₃.⟪ PP ↓ ⟫ ≈ PP₁₃
  tPP = trans (T₀₃-L PP) (U₃-sem (O₀ (Ex • PP • Ex)) (O₀ PP) Eq.refl)

  tH : T₀₃.⟪ ΛH 2 ⟫ ≈ Hp′
  tH = T₀₃.⟪⟫-•₃ tPP (trans T₀₃-box₃ b‴≈) tPP

  tNH : T₀₃.⟪ N₂.⟪ ΛH 2 ⟫ ⟫ ≈ Hp
  tNH = trans (T₀₃.⟪⟫-•₃ tX₂ tH tX₂) (conj-swap x2P bb)

  tCH : T₀₃.⟪ P₁₃ CH ⟫ ≈ HC ↓
  tCH = trans (T₀₃-nest′ (P₁₃ CH)) (trans (T₁₃.⟪⟫-cong (S₀₁.⟪⟫-cong (T₁₃-P₁₃ CH))) (T₁₃-P₀₃ HC))

  mm : Hp • Hp′ ≈ HC ↓
  mm = T₀₃.⟪⟫-≈ eq171′ (T₀₃.⟪⟫-•₂ tNH tH) tCH

  hpf : Hp ≈ HC ↓ • Hp′
  hpf = trans (sym right-unit) (trans (back _ (sym Hp′²)) (trans (sym assoc) (front _ mm)))

  -- (203) under (0 2): Hp′ passes H2.
  τ-via : ∀ {w w₁ w₂ w₃ : Circuit 4} → S₀₁.⟪ w ⟫ ≈ w₁ → S₁₂.⟪ w₁ ⟫ ≈ w₂ → S₀₁.⟪ w₂ ⟫ ≈ w₃ → Tτ.⟪ w ⟫ ≈ w₃
  τ-via {w} p q r = trans (by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl)
                          (trans (S₀₁.⟪⟫-cong (trans (S₁₂.⟪⟫-cong p) q)) r)

  S₁₂-box₃‴ : S₁₂.⟪ box₃‴ ⟫ ≈ box₃‴
  S₁₂-box₃‴ = trans (braid-conj↑ box₃′) (S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong S₂₃-box₃′))

  τP13 : Tτ.⟪ PP₁₃ ⟫ ≈ PP₁₃
  τP13 = τ-via refl (S₁₂-P₀₃ PP) (S₀₁.⟪⟫-⟪⟫ PP₁₃)

  τP03 : Tτ.⟪ PP₀₃ ⟫ ≈ P₂₃ PP
  τP03 = τ-via (S₀₁.⟪⟫-⟪⟫ PP₁₃) (S₁₂.⟪⟫-⟪⟫ (P₂₃ PP)) (P₂₃-S₀₁ PP)

  τB‴ : Tτ.⟪ box₃‴ ⟫ ≈ box₃‴
  τB‴ = τ-via S₀₁-box₃‴ S₁₂-box₃‴ S₀₁-box₃‴

  τX₂ : Tτ.⟪ X ↑ ↑ ⟫ ≈ X
  τX₂ = τ-via (P₂₃-S₀₁ X) S₁₂-X₂ sX′

  τH : Tτ.⟪ S₀₁.⟪ ΛH₂′ ⟫ ⟫ ≈ Hp′
  τH = trans (Tτ.⟪⟫-cong S₀₁-ΛH₂′-PP) (trans (Tτ.⟪⟫-•₃ τP13 τB‴ τP13) (mid _ _ b‴≈))

  τ°H : Tτ.⟪ °ΛH₂′ ⟫ ≈ H2
  τ°H = trans (Tτ.⟪⟫-cong °ΛH₂′-PP) (Tτ.⟪⟫-•₃ τP03 (trans (Tτ.⟪⟫-•₃ τX₂ τB‴ τX₂) (mid _ _ b‴≈)) τP03)

  h2a : Hp′ • H2 ≈ H2 • Hp′
  h2a = Tτ.⟪⟫-≈ eq203 (Tτ.⟪⟫-•₂ τH τ°H) (Tτ.⟪⟫-•₂ τ°H τH)

  -- (164) under the cycle 0 → 3 → 2 → 0 and X on wire 0: the CH from wire
  -- 0 onto wire 1 passes H2.
  τU : Tτ.⟪ U °CH ⟫ ≈ L HC°
  τU = L₃-sem (τ₀₂ • U₀ °CH • τ₀₂) (L₀ HC°) Eq.refl

  uπ : Word (S.Gen 4)
  uπ = σ2 • σ0 • σ1 • σ0

  πB : S₂₃.⟪ Tτ.⟪ box₃ ⟫ ⟫ ≈ bb
  πB = trans (by-passoc (□ • ((□ • □ • □) • □ • (□ • □ • □)) • □) ((□ • (□ • (□ • □))) • □ • (((□ • □) • □) • □)) Eq.refl)
             (trans (frame₁ rigΛ uπ ubb Eq.refl) (sym bb≈))

  hb′ : L HC° • bb ≈ bb • L HC°
  hb′ = S₂₃.⟪⟫-≈ (Tτ.⟪⟫-≈ eq164 (Tτ.⟪⟫-•₂ refl refl) (Tτ.⟪⟫-•₂ refl refl))
          (S₂₃.⟪⟫-•₂ πU πB) (S₂₃.⟪⟫-•₂ πB πU)
    where
    πU : S₂₃.⟪ Tτ.⟪ U °CH ⟫ ⟫ ≈ L HC°
    πU = trans (S₂₃.⟪⟫-cong τU) (L-S₂₃ HC°)

  hb : HC ↓ • b₀₁ ≈ b₀₁ • HC ↓
  hb = TX.⟪⟫-≈ hb′ (TX.⟪⟫-•₂ nHC refl) (TX.⟪⟫-•₂ refl nHC)
    where
    nHC : TX.⟪ L HC° ⟫ ≈ HC ↓
    nHC = L-sem (X • HC° • X) HC Eq.refl

  h2b : HC ↓ • H2 ≈ H2 • HC ↓
  h2b = pass₂ hP (pass₂ hb hP)
    where
    hP : HC ↓ • P₂₃ PP ≈ P₂₃ PP • HC ↓
    hP = sym (P₂₃-L PP HC)

  hp-h2 : Hp • H2 ≈ H2 • Hp
  hp-h2 = trans (front _ hpf) (trans (passL h2b h2a) (back _ (sym hpf)))

  crux : b₁₀ • Pu.⟪ b₀₁ ⟫ ≈ Pu.⟪ b₀₁ ⟫ • b₁₀
  crux = Q.⟪⟫-≈ hp-h2 (Q.⟪⟫-•₂ (Q.⟪⟫-⟪⟫ b₁₀) qH2) (Q.⟪⟫-•₂ qH2 (Q.⟪⟫-⟪⟫ b₁₀))

------------------------------------------------------------------------
-- The two splittings

e-ζη : B46.ζ • B46.η ≈ B46.Vo • B46.Vc
e-ζη = begin
  B46.ζ • B46.η
    ≈⟨ cong ζ≈ η≈ ⟩
  (b₀₀ • b₁₀) • (Pu.⟪ b₀₁ ⟫ • Pu.⟪ bb ⟫)
    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  b₀₀ • (b₁₀ • Pu.⟪ b₀₁ ⟫) • Pu.⟪ bb ⟫
    ≈⟨ back _ (front _ crux) ⟩
  b₀₀ • (Pu.⟪ b₀₁ ⟫ • b₁₀) • Pu.⟪ bb ⟫
    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
  B46.Vo • B46.Vc ∎

e-Vc : B46.Vc • B46.η • B46.ζ ≈ B46.Vo′
e-Vc = begin
  (b₁₀ • Pu.⟪ bb ⟫) • B46.η • B46.ζ
    ≈⟨ back _ (cong η≈′ ζ≈′) ⟩
  (b₁₀ • Pu.⟪ bb ⟫) • (Pu.⟪ bb ⟫ • Pu.⟪ b₀₁ ⟫) • (b₁₀ • b₀₀)
    ≈⟨ by-passoc ((□ • □) • (□ • □) • (□ • □)) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
  b₁₀ • (Pu.⟪ bb ⟫ • Pu.⟪ bb ⟫) • Pu.⟪ b₀₁ ⟫ • b₁₀ • b₀₀
    ≈⟨ back _ (trans (front _ (Pu.⟪⟫-invol bb²)) left-unit) ⟩
  b₁₀ • Pu.⟪ b₀₁ ⟫ • b₁₀ • b₀₀
    ≈⟨ trans (sym assoc) (front _ crux) ⟩
  (Pu.⟪ b₀₁ ⟫ • b₁₀) • b₁₀ • b₀₀
    ≈⟨ trans assoc (back _ (trans (sym assoc) (trans (front _ (N₂.⟪⟫-invol bb²)) left-unit))) ⟩
  B46.Vo′ ∎

------------------------------------------------------------------------
-- (339) for the box: (181) under (0 3) and the lower swap

private
  -- Col's P ⊗ P on the wires 1 3 is FourQubit's.
  PP1pl₃ : 3 ⊢ (Ex • Ex ↑) • PP • (Ex ↑ • Ex) ≈ PP ↑
  PP1pl₃ = by-sem₃ ((Ex • Ex ↑) • PP • (Ex ↑ • Ex)) (PP ↑) Eq.refl {0}

  PP2pl : PP ↑ ↑ ≈ pl ((σ1 • σ2) • (σ0 • σ1)) PP
  PP2pl = trans (sym (lemma-cong↑ _ _ PP1pl₃)) (trans (pl-cong (σ1 • σ2) (sym PP1pl)) (pl-pl (σ1 • σ2) (σ0 • σ1) PP))

  Pc≈PP₁₃ : Pc ≈ PP₁₃
  Pc≈PP₁₃ = sym (begin
    Ex ↑ • PP ↑ ↑ • Ex ↑
      ≈⟨ mid _ _ PP2pl ⟩
    pl σ1 (pl ((σ1 • σ2) • (σ0 • σ1)) PP)
      ≈⟨ pl-pl σ1 ((σ1 • σ2) • (σ0 • σ1)) PP ⟩
    pl (σ1 • ((σ1 • σ2) • (σ0 • σ1))) PP
      ≈⟨ frame rigPP (σ1 • ((σ1 • σ2) • (σ0 • σ1))) (uP • σ0) agree ⟩
    pl (uP • σ0) PP
      ≈⟨ trans (sym (pl-pl uP σ0 PP)) (pl-cong uP (L-sem (Ex • PP • Ex) PP Eq.refl)) ⟩
    pl uP PP
      ≈⟨ sym Pc≈ ⟩
    Pc ∎)
    where
    agree : ∀ (j : Fin 4) → toℕ j < 2 → perm (uP • σ0) ⟨$⟩ʳ (perm (revS (σ1 • ((σ1 • σ2) • (σ0 • σ1)))) ⟨$⟩ʳ j) ≡ j
    agree 0F       _ = Eq.refl
    agree (sF 0F)  _ = Eq.refl
    agree (sF (sF _)) (s≤s (s≤s ()))

  tP03 : T₀₃.⟪ PP₀₃ ⟫ ≈ PP₀₃
  tP03 = trans (T₀₃-nest′ PP₀₃) (trans (T₁₃.⟪⟫-cong (S₀₁.⟪⟫-cong (T₁₃-P₀₃ PP)))
           (trans (T₁₃-L (Ex • PP • Ex)) (P₀₃-sem (Ex • PP • Ex) PP Eq.refl)))

  tB‴ : T₀₃.⟪ box₃‴ ⟫ ≈ box₃
  tB‴ = conj-sym t₀₃² T₀₃-box₃

  t°H : T₀₃.⟪ °ΛH₂′ ⟫ ≈ PP₀₃ • °box₃ • PP₀₃
  t°H = trans (T₀₃.⟪⟫-cong °ΛH₂′-PP) (T₀₃.⟪⟫-•₃ tP03 (T₀₃.⟪⟫-•₃ tX₂ tB‴ tX₂) tP03)

  sH : S₀₁.⟪ PP₀₃ • °box₃ • PP₀₃ ⟫ ≈ X ↑ ↑ • Hg₃ 0 • X ↑ ↑
  sH = trans (S₀₁.⟪⟫-•₃ (S₀₁.⟪⟫-⟪⟫ PP₁₃) (sym N₂-box₃′) (S₀₁.⟪⟫-⟪⟫ PP₁₃))
             (trans (cong (sym Pc≈PP₁₃) (back _ (sym Pc≈PP₁₃))) (sym (conj-swap e-X₂P box₃′)))

c339₄ : (Λ□ 3 ↓ᵏ 0) • (X ↑ ↑ • Hg₃ 0 • X ↑ ↑) ≈ (X ↑ ↑ • Hg₃ 0 • X ↑ ↑) • (Λ□ 3 ↓ᵏ 0)
c339₄ = S₀₁.⟪⟫-≈ (T₀₃.⟪⟫-≈ eq181 (T₀₃.⟪⟫-•₂ T₀₃-box₃′ t°H) (T₀₃.⟪⟫-•₂ t°H T₀₃-box₃′))
          (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ box₃) sH) (S₀₁.⟪⟫-•₂ sH (S₀₁.⟪⟫-⟪⟫ box₃))

------------------------------------------------------------------------
-- The record

base46₄ : Base46At 0
base46₄ = record
  { ea₁ = ea₁ ; ea₂ = ea₂ ; eb₁ = eb₁ ; eb₂ = eb₂ ; ea-bb = ea-bb ; eb-bb = eb-bb
  ; ea-X = ea-X ; ea-X₁ = ea-X₁ ; ea-P = ea-P ; ea-L = ea-L ; ea-R = ea-R
  ; eb-X = eb-X ; eb-X₂ = eb-X₂ ; eb-P = eb-P ; eb-L = eb-L ; eb-R = eb-R
  ; e-X₂P = e-X₂P ; e-ζη = e-ζη ; e-Vc = e-Vc }
