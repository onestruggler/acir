------------------------------------------------------------------------
-- Presentations of groups
--
-- Permuting the wires of a four-qubit circuit
--
-- A gate placed somewhere else is the conjugate of the gate by swaps,
-- and an equation is carried to another placement by conjugating it
-- (Conj.⟪⟫-≈).  Here are the swap words in play beyond the three adjacent
-- swaps — the transpositions (1 3) and (0 3), each an involution and so
-- a conjugation module — the two relations of the symmetric group that
-- relate them (the braid relation is the swap rule (f) for the swap
-- itself, `U-shift Ex`; swaps on disjoint pairs commute), and the action
-- of (1 3) on what the four-qubit equations are made of: a two-wire
-- circuit on a pair of wires, X on a wire, the box and the doubly
-- controlled H.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Permutations
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; Ex² ; S-X↓ ; S-X↑ ; comm-↓↑)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq157 ; eq161 ; eq162)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃ ; L₃-top)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The adjacent swaps

Ex₁² : (₄₊ n) ⊢ Ex ↑ • Ex ↑ ≈ ε
Ex₁² = lemma-cong↑ (Ex • Ex) ε Ex²

Ex₂² : (₄₊ n) ⊢ Ex ↑ ↑ • Ex ↑ ↑ ≈ ε
Ex₂² = lemma-cong↑ (Ex ↑ • Ex ↑) ε (lemma-cong↑ (Ex • Ex) ε Ex²)

-- Swaps on disjoint pairs commute.
far : (₄₊ n) ⊢ Ex ↓ • Ex ↑ ↑ ≈ Ex ↑ ↑ • Ex ↓
far = L-comm Ex Ex

-- The braid relation: the swap rule for the swap itself.
braid : (₃₊ n) ⊢ Ex ↓ • Ex ↑ • Ex ↓ ≈ Ex ↑ • Ex ↓ • Ex ↑
braid {n} = sym (trans (U-shift Ex) assoc)
  where open Tools ((₃₊ n) VRel,_===_)

-- Conjugating by three swaps, braided.
braid-conj : (w : Circuit (₃₊ n)) →
  (₃₊ n) ⊢ Ex ↑ • (Ex ↓ • (Ex ↑ • w • Ex ↑) • Ex ↓) • Ex ↑
         ≈ Ex ↓ • (Ex ↑ • (Ex ↓ • w • Ex ↓) • Ex ↑) • Ex ↓
braid-conj {n} w = begin
  Ex ↑ • (Ex ↓ • (Ex ↑ • w • Ex ↑) • Ex ↓) • Ex ↑
    ≈⟨ by-passoc (□ • (□ • (□ • □ • □) • □) • □) ((□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
  (Ex ↑ • Ex ↓ • Ex ↑) • w • (Ex ↑ • Ex ↓ • Ex ↑)
    ≈⟨ cong (sym braid) (back _ (sym braid)) ⟩
  (Ex ↓ • Ex ↑ • Ex ↓) • w • (Ex ↓ • Ex ↑ • Ex ↓)
    ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl ⟩
  Ex ↓ • (Ex ↑ • (Ex ↓ • w • Ex ↓) • Ex ↑) • Ex ↓ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- The same one wire up, for any circuit on four wires.
braid↑ : (₄₊ n) ⊢ Ex ↑ • Ex ↑ ↑ • Ex ↑ ≈ Ex ↑ ↑ • Ex ↑ • Ex ↑ ↑
braid↑ = lemma-cong↑ (Ex ↓ • Ex ↑ • Ex ↓) (Ex ↑ • Ex ↓ • Ex ↑) braid

braid-conj↑ : (w : Circuit (₄₊ n)) →
  (₄₊ n) ⊢ Ex ↑ • (Ex ↑ ↑ • (Ex ↑ • w • Ex ↑) • Ex ↑ ↑) • Ex ↑
         ≈ Ex ↑ ↑ • (Ex ↑ • (Ex ↑ ↑ • w • Ex ↑ ↑) • Ex ↑) • Ex ↑ ↑
braid-conj↑ {n} w = begin
  Ex ↑ • (Ex ↑ ↑ • (Ex ↑ • w • Ex ↑) • Ex ↑ ↑) • Ex ↑
    ≈⟨ by-passoc (□ • (□ • (□ • □ • □) • □) • □) ((□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
  (Ex ↑ • Ex ↑ ↑ • Ex ↑) • w • (Ex ↑ • Ex ↑ ↑ • Ex ↑)
    ≈⟨ cong braid↑ (back _ braid↑) ⟩
  (Ex ↑ ↑ • Ex ↑ • Ex ↑ ↑) • w • (Ex ↑ ↑ • Ex ↑ • Ex ↑ ↑)
    ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl ⟩
  Ex ↑ ↑ • (Ex ↑ • (Ex ↑ ↑ • w • Ex ↑ ↑) • Ex ↑) • Ex ↑ ↑ ∎
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- The transposition (1 3)

t₁₃ : Circuit (₄₊ n)
t₁₃ = Ex ↑ ↑ • Ex ↑ • Ex ↑ ↑

t₁₃² : (₄₊ n) ⊢ t₁₃ • t₁₃ ≈ ε
t₁₃² {n} = conj-invol Ex₂² Ex₁²
  where open Tools ((₄₊ n) VRel,_===_)

module T₁₃ {n : ℕ} = Conj {₄₊ n} t₁₃ t₁₃²

-- As three conjugations.
T₁₃-nest : (w : Circuit (₄₊ n)) → (₄₊ n) ⊢ T₁₃.⟪ w ⟫ ≈ S₂₃.⟪ S₁₂.⟪ S₂₃.⟪ w ⟫ ⟫ ⟫
T₁₃-nest {n} w =
  by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl
  where open Tools ((₄₊ n) VRel,_===_)

-- The action of (1 3) from the action of the three swaps.
T₁₃-via : {w w₁ w₂ w₃ : Circuit (₄₊ n)} →
          (₄₊ n) ⊢ S₂₃.⟪ w ⟫ ≈ w₁ → (₄₊ n) ⊢ S₁₂.⟪ w₁ ⟫ ≈ w₂ → (₄₊ n) ⊢ S₂₃.⟪ w₂ ⟫ ≈ w₃ →
          (₄₊ n) ⊢ T₁₃.⟪ w ⟫ ≈ w₃
T₁₃-via {n} {w} p q r =
  trans (T₁₃-nest w) (trans (S₂₃.⟪⟫-cong (trans (S₁₂.⟪⟫-cong p) q)) r)
  where open Tools ((₄₊ n) VRel,_===_)

-- An action read backwards.
T₁₃-back : {w w′ : Circuit (₄₊ n)} → (₄₊ n) ⊢ T₁₃.⟪ w ⟫ ≈ w′ → (₄₊ n) ⊢ T₁₃.⟪ w′ ⟫ ≈ w
T₁₃-back {n} {w} e = trans (T₁₃.⟪⟫-cong (sym e)) (T₁₃.⟪⟫-⟪⟫ w)
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (1 3) on a two-wire circuit placed on a pair of wires

S₂₃-P₁₃ : (u : Circuit 2) → (₄₊ n) ⊢ S₂₃.⟪ P₁₃ u ⟫ ≈ U u
S₂₃-P₁₃ {n} u = trans (S₂₃.⟪⟫-cong (sym (U-S₂₃ u))) (S₂₃.⟪⟫-⟪⟫ (U u))
  where open Tools ((₄₊ n) VRel,_===_)

S₂₃-P₀₃ : (u : Circuit 2) → (₄₊ n) ⊢ S₂₃.⟪ P₀₃ u ⟫ ≈ O u
S₂₃-P₀₃ {n} u = trans (S₂₃.⟪⟫-cong (sym (O-S₂₃ u))) (S₂₃.⟪⟫-⟪⟫ (O u))
  where open Tools ((₄₊ n) VRel,_===_)

-- The middle swap leaves the pair 0 3 alone.
S₁₂-P₀₃ : (u : Circuit 2) → (₄₊ n) ⊢ S₁₂.⟪ P₀₃ u ⟫ ≈ P₀₃ u
S₁₂-P₀₃ {n} u = trans (braid-conj (P₂₃ u)) (S₀₁.⟪⟫-cong (S₁₂.⟪⟫-cong (P₂₃-S₀₁ (u ↓ᵏ n))))
  where open Tools ((₄₊ n) VRel,_===_)

T₁₃-L : (u : Circuit 2) → (₄₊ n) ⊢ T₁₃.⟪ L u ⟫ ≈ P₀₃ u
T₁₃-L u = T₁₃-via (L-S₂₃ u) (O-L u) (O-S₂₃ u)

T₁₃-P₀₃ : (u : Circuit 2) → (₄₊ n) ⊢ T₁₃.⟪ P₀₃ u ⟫ ≈ L u
T₁₃-P₀₃ u = T₁₃-back (T₁₃-L u)

T₁₃-O : (u : Circuit 2) → (₄₊ n) ⊢ T₁₃.⟪ O u ⟫ ≈ O u
T₁₃-O u = T₁₃-via (O-S₂₃ u) (S₁₂-P₀₃ u) (S₂₃-P₀₃ u)

-- On the pairs that contain wire 1 or wire 3 the two-wire circuit comes
-- out with its own wires exchanged.
T₁₃-U : (u : Circuit 2) → (₄₊ n) ⊢ T₁₃.⟪ U u ⟫ ≈ P₂₃ (Ex • u • Ex)
T₁₃-U {n} u = T₁₃-via (U-S₂₃ u) (S₁₂.⟪⟫-⟪⟫ (P₂₃ u)) refl
  where open Tools ((₄₊ n) VRel,_===_)

T₁₃-P₂₃ : (u : Circuit 2) → (₄₊ n) ⊢ T₁₃.⟪ P₂₃ u ⟫ ≈ U (Ex • u • Ex)
T₁₃-P₂₃ {n} u = T₁₃-via {w₁ = P₂₃ (Ex • u • Ex)} refl refl (S₂₃-P₁₃ (Ex • u • Ex))
  where open Tools ((₄₊ n) VRel,_===_)

T₁₃-P₁₃ : (u : Circuit 2) → (₄₊ n) ⊢ T₁₃.⟪ P₁₃ u ⟫ ≈ P₁₃ (Ex • u • Ex)
T₁₃-P₁₃ {n} u = T₁₃-via {w₂ = U (Ex • u • Ex)} (S₂₃-P₁₃ u) refl (U-S₂₃ (Ex • u • Ex))
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (1 3) on X

S₂₃-X₂ : (₄₊ n) ⊢ S₂₃.⟪ X ↑ ↑ ⟫ ≈ X ↑ ↑ ↑
S₂₃-X₂ = lemma-cong↑ (Ex ↑ • X ↑ • Ex ↑) (X ↑ ↑)
           (lemma-cong↑ (Ex • X ↓ • Ex) (X ↑) S-X↓)

S₂₃-X₃ : (₄₊ n) ⊢ S₂₃.⟪ X ↑ ↑ ↑ ⟫ ≈ X ↑ ↑
S₂₃-X₃ = lemma-cong↑ (Ex ↑ • X ↑ ↑ • Ex ↑) (X ↑)
           (lemma-cong↑ (Ex • X ↑ • Ex) (X ↓) S-X↑)

S₁₂-X₁ : (₄₊ n) ⊢ S₁₂.⟪ X ↑ ⟫ ≈ X ↑ ↑
S₁₂-X₁ = lemma-cong↑ (Ex • X ↓ • Ex) (X ↑) S-X↓

S₁₂-X₂ : (₄₊ n) ⊢ S₁₂.⟪ X ↑ ↑ ⟫ ≈ X ↑
S₁₂-X₂ = lemma-cong↑ (Ex • X ↑ • Ex) (X ↓) S-X↑

S₁₂-X₃ : (₄₊ n) ⊢ S₁₂.⟪ X ↑ ↑ ↑ ⟫ ≈ X ↑ ↑ ↑
S₁₂-X₃ {n} = lemma-cong↑ (Ex • X ↑ ↑ • Ex) (X ↑ ↑) (S′.⟪⟫-fix (L-comm Ex X))
  where module S′ = Conj {₃₊ n} Ex Ex²

S₂₃-X₁ : (₄₊ n) ⊢ S₂₃.⟪ X ↑ ⟫ ≈ X ↑
S₂₃-X₁ {n} = lemma-cong↑ (Ex ↑ • X ↓ • Ex ↑) (X ↓) (S′.⟪⟫-fix (sym (comm-↓↑ X Ex)))
  where
  open Tools ((₃₊ n) VRel,_===_)
  module S′ = Conj {₃₊ n} (Ex ↑) (lemma-cong↑ (Ex • Ex) ε Ex²)

T₁₃-X₁ : (₄₊ n) ⊢ T₁₃.⟪ X ↑ ⟫ ≈ X ↑ ↑ ↑
T₁₃-X₁ = T₁₃-via S₂₃-X₁ S₁₂-X₁ S₂₃-X₂

T₁₃-X₂ : (₄₊ n) ⊢ T₁₃.⟪ X ↑ ↑ ⟫ ≈ X ↑ ↑
T₁₃-X₂ = T₁₃-via S₂₃-X₂ S₁₂-X₃ S₂₃-X₃

T₁₃-X₃ : (₄₊ n) ⊢ T₁₃.⟪ X ↑ ↑ ↑ ⟫ ≈ X ↑
T₁₃-X₃ = T₁₃-back T₁₃-X₁

-- Hence on a negated control.
T₁₃-N₂ : {w w′ : Circuit (₄₊ n)} → (₄₊ n) ⊢ T₁₃.⟪ w ⟫ ≈ w′ → (₄₊ n) ⊢ T₁₃.⟪ N₂.⟪ w ⟫ ⟫ ≈ N₂.⟪ w′ ⟫
T₁₃-N₂ e = T₁₃.⟪⟫-•₃ T₁₃-X₂ e T₁₃-X₂

T₁₃-N₁ : {w w′ : Circuit (₄₊ n)} → (₄₊ n) ⊢ T₁₃.⟪ w ⟫ ≈ w′ → (₄₊ n) ⊢ T₁₃.⟪ N₁.⟪ w ⟫ ⟫ ≈ N₃.⟪ w′ ⟫
T₁₃-N₁ e = T₁₃.⟪⟫-•₃ T₁₃-X₁ e T₁₃-X₁

T₁₃-N₃ : {w w′ : Circuit (₄₊ n)} → (₄₊ n) ⊢ T₁₃.⟪ w ⟫ ≈ w′ → (₄₊ n) ⊢ T₁₃.⟪ N₃.⟪ w ⟫ ⟫ ≈ N₁.⟪ w′ ⟫
T₁₃-N₃ e = T₁₃.⟪⟫-•₃ T₁₃-X₃ e T₁₃-X₃

------------------------------------------------------------------------
-- Negations on different wires commute

X₂-X₃ : (₄₊ n) ⊢ X ↑ ↑ • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • X ↑ ↑
X₂-X₃ = lemma-cong↑ (X ↑ • X ↑ ↑) (X ↑ ↑ • X ↑)
          (lemma-cong↑ (X ↓ • X ↑) (X ↑ • X ↓) (comm-↓↑ X X))

N₂-N₃ : (w : Circuit (₄₊ n)) → (₄₊ n) ⊢ N₂.⟪ N₃.⟪ w ⟫ ⟫ ≈ N₃.⟪ N₂.⟪ w ⟫ ⟫
N₂-N₃ {n} w = begin
  X ↑ ↑ • (X ↑ ↑ ↑ • w • X ↑ ↑ ↑) • X ↑ ↑
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
  (X ↑ ↑ • X ↑ ↑ ↑) • w • (X ↑ ↑ ↑ • X ↑ ↑)
    ≈⟨ cong X₂-X₃ (back _ (sym X₂-X₃)) ⟩
  (X ↑ ↑ ↑ • X ↑ ↑) • w • (X ↑ ↑ • X ↑ ↑ ↑)
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
  X ↑ ↑ ↑ • (X ↑ ↑ • w • X ↑ ↑) • X ↑ ↑ ↑ ∎
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (1 3) on the gates

-- The box with its box wire on wire 0 is symmetric in its controls,
-- (157) and (161).
T₁₃-box₃ : (₄₊ n) ⊢ T₁₃.⟪ box₃ ⟫ ≈ box₃
T₁₃-box₃ = T₁₃-via eq161 eq157 eq161

T₁₃-°box₃ : (₄₊ n) ⊢ T₁₃.⟪ °box₃ ⟫ ≈ °box₃
T₁₃-°box₃ = T₁₃-N₂ T₁₃-box₃

-- The doubly controlled H with its H on wire 0 and its box wire on
-- wire 1.
ΛH₀₁ : Circuit (₄₊ n)
ΛH₀₁ {n} = S₀₁.⟪ ΛH 2 ↓ᵏ n ⟫

-- It is symmetric in its controls, (162).
S₂₃-ΛH₀₁ : (₄₊ n) ⊢ S₂₃.⟪ ΛH₀₁ ⟫ ≈ ΛH₀₁
S₂₃-ΛH₀₁ = S₂₃.⟪⟫-•₃ (L-S₂₃ Ex) eq162 (L-S₂₃ Ex)

-- So is the H gate with its box wire on wire 3, in its controls on the
-- wires 1 and 2.
S₁₂-ΛH₂′ : (₄₊ n) ⊢ S₁₂.⟪ ΛH₂′ ⟫ ≈ ΛH₂′
S₁₂-ΛH₂′ {n} = trans (braid-conj↑ ΛH₀₁) (S₂₃.⟪⟫-cong (S₁₂.⟪⟫-cong S₂₃-ΛH₀₁))
  where open Tools ((₄₊ n) VRel,_===_)

-- (1 3) takes the H gate with its box wire on wire 3 to it.
T₁₃-ΛH₂′ : (₄₊ n) ⊢ T₁₃.⟪ ΛH₂′ ⟫ ≈ ΛH₀₁
T₁₃-ΛH₂′ {n} = T₁₃-via (S₂₃.⟪⟫-⟪⟫ (S₁₂.⟪ ΛH₀₁ ⟫)) (S₁₂.⟪⟫-⟪⟫ ΛH₀₁) S₂₃-ΛH₀₁

------------------------------------------------------------------------
-- The transposition (0 3)

t₀₃ : Circuit (₄₊ n)
t₀₃ = Ex ↓ • t₁₃ • Ex ↓

t₀₃² : (₄₊ n) ⊢ t₀₃ • t₀₃ ≈ ε
t₀₃² {n} = conj-invol Ex² t₁₃²
  where open Tools ((₄₊ n) VRel,_===_)

module T₀₃ {n : ℕ} = Conj {₄₊ n} t₀₃ t₀₃²

-- (0 3) = (0 1) (1 3) (0 1) = (1 3) (0 1) (1 3).
t₀₃-alt : (₄₊ n) ⊢ t₀₃ ≈ t₁₃ • Ex ↓ • t₁₃
t₀₃-alt {n} = begin
  Ex ↓ • (Ex ↑ ↑ • Ex ↑ • Ex ↑ ↑) • Ex ↓
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
  (Ex ↓ • Ex ↑ ↑) • Ex ↑ • (Ex ↑ ↑ • Ex ↓)
    ≈⟨ cong far (back _ (sym far)) ⟩
  (Ex ↑ ↑ • Ex ↓) • Ex ↑ • (Ex ↓ • Ex ↑ ↑)
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
  Ex ↑ ↑ • (Ex ↓ • Ex ↑ • Ex ↓) • Ex ↑ ↑
    ≈⟨ mid _ _ braid ⟩
  Ex ↑ ↑ • (Ex ↑ • Ex ↓ • Ex ↑) • Ex ↑ ↑
    ≈⟨ back _ (front _ (back _ (front _ (sym (L-S₂₃ Ex))))) ⟩
  Ex ↑ ↑ • (Ex ↑ • (Ex ↑ ↑ • Ex ↓ • Ex ↑ ↑) • Ex ↑) • Ex ↑ ↑
    ≈⟨ by-passoc (□ • (□ • (□ • □ • □) • □) • □) ((□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
  (Ex ↑ ↑ • Ex ↑ • Ex ↑ ↑) • Ex ↓ • (Ex ↑ ↑ • Ex ↑ • Ex ↑ ↑) ∎
  where open Tools ((₄₊ n) VRel,_===_)

T₀₃-nest : (w : Circuit (₄₊ n)) → (₄₊ n) ⊢ T₀₃.⟪ w ⟫ ≈ S₀₁.⟪ T₁₃.⟪ S₀₁.⟪ w ⟫ ⟫ ⟫
T₀₃-nest {n} w =
  by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl
  where open Tools ((₄₊ n) VRel,_===_)

T₀₃-nest′ : (w : Circuit (₄₊ n)) → (₄₊ n) ⊢ T₀₃.⟪ w ⟫ ≈ T₁₃.⟪ S₀₁.⟪ T₁₃.⟪ w ⟫ ⟫ ⟫
T₀₃-nest′ {n} w = begin
  t₀₃ • w • t₀₃
    ≈⟨ cong t₀₃-alt (back _ t₀₃-alt) ⟩
  (t₁₃ • Ex ↓ • t₁₃) • w • (t₁₃ • Ex ↓ • t₁₃)
    ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl ⟩
  t₁₃ • (Ex ↓ • (t₁₃ • w • t₁₃) • Ex ↓) • t₁₃ ∎
  where open Tools ((₄₊ n) VRel,_===_)
