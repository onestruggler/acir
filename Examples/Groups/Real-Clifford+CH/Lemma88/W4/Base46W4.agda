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
open import Data.Nat using (_<_ ; s≤s ; z≤n)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; perm ; perm-≈)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₀₁ ; module S₁₂ ; module S₂₃ ; L-sem ; L₃-sem ; U₃-sem)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃ using (S₁₂-X₁ ; S₂₃-X₂)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (revS ; net-inv ; net-inv′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl ; pl-cong ; pl-• ; Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (Rigid ; frame ; frame₁ ; pl-pl)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Networks using (scyc ; scyc⁻¹)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using () renaming (P₁₃ to Pc)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon4 complete₂ complete₃ using (canon4)
import Examples.Groups.Real-Clifford+CH.GeneralN.Base46 as B46

open Tools (4 VRel,_===_)

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
