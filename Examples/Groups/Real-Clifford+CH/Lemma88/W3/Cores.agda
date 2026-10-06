------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical cores of rules (39), (40), (45) and (46) on three
-- qubits (Clément, Appendix E.5 at n = 3, from Lemma D.2)
--
-- On three wires the multi-controlled H gate ΛH 1 is CH ↑ and the box
-- Λ□ 2 is CZ ↑, so each core is a three-wire equation between CH's,
-- CZ's and X's:
--
-- * (39): CH₂₀ against the CZ of the wires 1 2 white on wire 1, which X
--   on wire 1 and CZ ↑ both pass.
-- * (40): with h = CH₂₀ and c the lower CZ, CCZX is h c h c
--   (symm-controls), the box white on wire 0 is c° = X c X, and c c° is
--   Z ↑, which h passes: h c h c c° h ≈ h c°.
-- * (45): Lemma D.2's (146) conjugated by X on wire 2.
-- * (46): Lemma D.2's (147), its CH ↓ and °CH ↓ spelled through the
--   swaps.
--
-- Only completeness on two qubits is used.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W3.Cores
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; ax ; CZ² ; CH² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂
  using (L ; U ; L-sem ; U-sem ; L-comm ; X↑-O ; Z↑-O ; O-L ; O-invol)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (CZ↑-CH₂₀ ; eq146 ; eq147 ; module N₂)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Letters46 {0} using (Core46)

open Tools (3 VRel,_===_)
open WordAlgebra (3 VRel,_===_) using (comm-•)

private
  Ex↑² : Ex ↑ • Ex ↑ ≈ ε
  Ex↑² = lemma-cong↑ (Ex • Ex) ε Ex²

  x12 : X ↑ ↑ • X ↑ ≈ X ↑ • X ↑ ↑
  x12 = sym (lemma-cong↑ (X • X ↑) (X ↑ • X) (X-↑ X))

  -- X on wire 2 passes a gate on the lower pair.
  N₂-fix : ∀ (u : Circuit 2) → N₂.⟪ L u ⟫ ≈ L u
  N₂-fix u = N₂.⟪⟫-fix (sym (L-comm u X))

  -- The CH ↓ spelled through the swaps: the CH from wire 2 onto wire 0
  -- under the swap of the wires 1 2.
  ch↓ : (Ex ↑ • Ex ↓) • CH ↑ • (Ex ↓ • Ex ↑) ≈ CH ↓
  ch↓ = trans (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl) (conj-sym Ex↑² (O-L CH))

------------------------------------------------------------------------
-- (39)

core39₀ : (Ex ↓ • ΛH 1 • Ex ↓) • (X ↑ • Λ□ 2 • X ↑) ≈ (X ↑ • Λ□ 2 • X ↑) • (Ex ↓ • ΛH 1 • Ex ↓)
core39₀ = comm-• (sym xh) (comm-• (sym CZ↑-CH₂₀) (sym xh))
  where
  xh : X ↑ • CH₂₀ ≈ CH₂₀ • X ↑
  xh = X↑-O CH

------------------------------------------------------------------------
-- (40)

core40₀ : (Ex ↓ • ΛH 1 • Ex ↓) • ((X • X ↑ ↑) • (Ex ↑ • (Ex ↓ • Λ□ 2 • Ex ↓) • Ex ↑) • (X • X ↑ ↑))
          ≈ ΛZX 2 • ((X • X ↑ ↑) • (Ex ↑ • (Ex ↓ • Λ□ 2 • Ex ↓) • Ex ↑) • (X • X ↑ ↑)) • (Ex ↓ • ΛH 1 • Ex ↓)
core40₀ = sym (begin
  CCZX • Btd • h                            ≈⟨ cong (ax symm-controls) (front _ btd) ⟩
  (h • c • h • c) • (c° • h)                 ≈⟨ by-passoc ((□ • □ • □ • □) • (□ • □)) (□ • □ • □ • (□ • □) • □) Eq.refl ⟩
  h • c • h • (c • c°) • h                   ≈⟨ back _ (back _ (back _ (front _ ccz))) ⟩
  h • c • h • Z ↑ • h                        ≈⟨ back _ (back _ (trans (back _ (Z↑-O CH))
                                                 (trans (sym assoc) (trans (front _ h²) left-unit)))) ⟩
  h • c • Z ↑                                ≈⟨ back _ (back _ (sym ccz)) ⟩
  h • c • (c • c°)                           ≈⟨ back _ (trans (sym assoc) (trans (front _ CZ²) left-unit)) ⟩
  h • c°                                     ≈⟨ back _ (sym btd) ⟩
  h • Btd ∎)
  where
  h c c° Btd : Circuit 3
  h   = CH₂₀
  c   = CZ ↓
  c°  = X • CZ • X
  Btd = (X • X ↑ ↑) • (Ex ↑ • CZ₂₀ • Ex ↑) • (X • X ↑ ↑)
  h² : h • h ≈ ε
  h² = O-invol CH CH²
  -- The CZ of the wires 0 1 times its version white on wire 0: Z ↑.
  ccz : c • c° ≈ Z ↑
  ccz = L-sem (CZ • (X • CZ • X)) (Z ↑) Eq.refl
  -- The box white on wire 0, wire 2 idle.
  btd : Btd ≈ c°
  btd = begin
    (X • X ↑ ↑) • (Ex ↑ • CZ₂₀ • Ex ↑) • (X • X ↑ ↑)   ≈⟨ back _ (cong (conj-sym Ex↑² (O-L CZ)) (X-↑ (X ↑))) ⟩
    (X • X ↑ ↑) • CZ • (X ↑ ↑ • X)                     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    X • (X ↑ ↑ • CZ • X ↑ ↑) • X                       ≈⟨ mid _ _ (N₂-fix CZ) ⟩
    X • CZ • X ∎

------------------------------------------------------------------------
-- (45)

private
  -- °CH ↓ spelled through the swaps and X on the wires 1 2.
  Cw : Circuit 3
  Cw = (X ↑ • X ↑ ↑) • (Ex ↑ • Ex ↓) • ΛH 1 • (Ex ↓ • Ex ↑) • (X ↑ • X ↑ ↑)

core45₀ : ΛH 1 • (X ↑ • Λ□ 2 • X ↑) • Cw • ΛH 1 • Cw ≈ Cw • ΛH 1 • Cw • (X ↑ • Λ□ 2 • X ↑) • ΛH 1
core45₀ = N₂.⟪⟫-≈ eq146 (N₂.⟪⟫-•₅ eA eZ eC eA eC) (N₂.⟪⟫-•₅ eC eA eC eZ eA)
  where
  eA : N₂.⟪ U °CH ⟫ ≈ CH ↑
  eA = U-sem (X ↑ • °CH • X ↑) CH Eq.refl
  eZ : N₂.⟪ U °CZ° ⟫ ≈ X ↑ • CZ ↑ • X ↑
  eZ = U-sem (X ↑ • °CZ° • X ↑) CZ° Eq.refl
  cw : Cw ≈ °CH ↓
  cw = begin
    (X ↑ • X ↑ ↑) • (Ex ↑ • Ex ↓) • CH ↑ • (Ex ↓ • Ex ↑) • (X ↑ • X ↑ ↑)
      ≈⟨ by-passoc ((□ • □) • (□ • □) • □ • (□ • □) • (□ • □)) ((□ • □) • ((□ • □) • □ • (□ • □)) • (□ • □)) Eq.refl ⟩
    (X ↑ • X ↑ ↑) • ((Ex ↑ • Ex ↓) • CH ↑ • (Ex ↓ • Ex ↑)) • (X ↑ • X ↑ ↑)
      ≈⟨ back _ (cong ch↓ (sym x12)) ⟩
    (X ↑ • X ↑ ↑) • CH • (X ↑ ↑ • X ↑)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    X ↑ • (X ↑ ↑ • CH • X ↑ ↑) • X ↑
      ≈⟨ mid _ _ (N₂-fix CH) ⟩
    X ↑ • CH • X ↑ ∎
  eC : N₂.⟪ °CH ↓ ⟫ ≈ Cw
  eC = trans (N₂-fix °CH) (sym cw)

------------------------------------------------------------------------
-- (46)

core46₀ : Core46
core46₀ = trans lhs (trans eq147 (sym rhs))
  where
  f≈ : X ↑ • ((Ex ↑ • Ex ↓) • CH ↑ • (Ex ↓ • Ex ↑)) • X ↑ ≈ °CH ↓
  f≈ = mid _ _ ch↓
  lhs = back _ (back _ (back _ (back _ (cong ch↓ (back _ (back _ f≈))))))
  rhs = cong f≈ (back _ (back _ (front _ ch↓)))
