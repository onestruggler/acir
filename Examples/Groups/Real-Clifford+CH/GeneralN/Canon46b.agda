------------------------------------------------------------------------
-- Presentations of groups
--
-- Rule (46) of Figure 8 at the canonical position (Clément, Lemma 8.8)
--
-- Canon46a reduces Core46 to the commutation of UA F UA and UB K UB,
-- with K = K₁ K₂; that is F against V K V⁻¹ with V = UA UB.  Between
-- P ⊗ P on the wires 0 1 (`PF`, `PM`):
--
--   F ↦ Vh Fo, the H gate on wire 1 with its box wire 2, black on
--   wire 0, and the box on wire 2 with wire 1 idle, black on wire 0;
--   K₁ ↦ C0, K₂ ↦ G′, the box on wire 1 and the H gate on wire 1 with
--   its box wire 2, both white on wire 0;
--   UA UB ↦ ζ η, a circuit on the wires 1 2, which splits over the
--   colour of wire 0 into Vo (white) and Vc (black), words in the box on
--   wire 3 of the bottom four wires (Base46).
--
-- So what is to show is that Vh Fo passes Vo (C0 G′) Vo⁻¹, where Vc,
-- black on wire 0, has passed C0 G′: every gate there is separated from
-- the other side by the colour of wire 0.  The pairs are (339) — the
-- four-wire box against the H gate, under the relabellings πa, πb of
-- the bottom four wires (`C339₄`: the four-wire box is the product of
-- the box over every colouring of the wires 4 …, merge-top₃) — (338)
-- with x ≠ y, and boxes against boxes ((335), (336)).  Each was checked
-- numerically first (scratchpad t46b.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon46b
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true ; false)
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Data.Nat using (ℕ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Vec using (_∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; X² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₁₂ ; L₃-sem)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (col-pair′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; SymAt ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All complete₂ complete₃ using (mergesₙ)
import Examples.Groups.Real-Clifford+CH.GeneralN.MergeAll as MergeAll
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (col ; conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (Hg₃ ; P₁₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (pass-∏ ; allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (module Carry ; sep)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box339 complete₂ complete₃ using (eq339)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box337 complete₂ complete₃ using (col-2)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (eq336ᶜ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon46a complete₂ complete₃ using (module At)
import Examples.Groups.Real-Clifford+CH.GeneralN.Base46 as B46
open import Examples.Groups.Real-Clifford+CH.Lemma88.Letters46 using (Core46)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N m′ : ℕ
    N  = ₁₊ (₄₊ k)
    m′ = ₁₊ k

    c₄ : Comp 4
    c₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    symAt : SymAt (₁₊ k)
    symAt = eqSymAt (₁₊ k) completes

    canon : Canon (₂₊ k)
    canon = canonN k completes

  open Tools (N VRel,_===_)
  open At k below
  open SS.Below 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) c₄ using (by-sem)
  open MergeAll (₃₊ k) (mergesₙ k completes) using (merge-top₃)

  private
    via : ∀ {y u w : Circuit N} → u ≈ w → y • w ≈ w • y → y • u ≈ u • y
    via e p = trans (back _ e) (trans p (front _ (sym e)))

    via′ : ∀ {y u w : Circuit N} → u ≈ w → w • y ≈ y • w → u • y ≈ y • u
    via′ e p = trans (front _ e) (trans p (back _ (sym e)))

    both : ∀ {p p′ q q′ : Circuit N} → p ≈ p′ → q ≈ q′ → p′ • q′ ≈ q′ • p′ → p • q ≈ q • p
    both ep eq e = trans (cong ep eq) (trans e (sym (cong eq ep)))

    pass₂ : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
    pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

    pass₂′ : ∀ {a u v : Circuit N} → u • a ≈ a • u → v • a ≈ a • v → (u • v) • a ≈ a • (u • v)
    pass₂′ eu ev = sym (pass₂ (sym eu) (sym ev))

    pass₃ : ∀ {a u v w : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • w ≈ w • a →
            a • (u • v • w) ≈ (u • v • w) • a
    pass₃ eu ev ew = pass₂ eu (pass₂ ev ew)

    Pu² : PP ↑ • PP ↑ ≈ ε
    Pu² = lemma-cong↑ _ _ eq111

    module CX  = Carry {N} X X²
    module CN  = Carry {N} (X ↑ ↑) X₂²
    module CPu = Carry {N} (PP ↑) Pu²
    module CUA = Carry {N} UA UA²

    X-back : ∀ {a b a′ b′} → X • a • X ≈ a′ → X • b • X ≈ b′ → a′ • b′ ≈ b′ • a′ → a • b ≈ b • a
    X-back ea eb e = CX.carry (conj-sym X² ea) (conj-sym X² eb) e

    Pu-back : ∀ {a b a′ b′} → Pu.⟪ a ⟫ ≈ a′ → Pu.⟪ b ⟫ ≈ b′ → a′ • b′ ≈ b′ • a′ → a • b ≈ b • a
    Pu-back ea eb e = CPu.carry (conj-sym Pu² ea) (conj-sym Pu² eb) e

  ----------------------------------------------------------------------
  -- Conjugation by a word and its inverse

  module Rel (π π′ : Circuit N) (e₁ : π • π′ ≈ ε) (e₂ : π′ • π ≈ ε) where

    ⟪_⟫ : Circuit N → Circuit N
    ⟪ w ⟫ = π • w • π′

    ⟪⟫-• : ∀ a b → ⟪ a • b ⟫ ≈ ⟪ a ⟫ • ⟪ b ⟫
    ⟪⟫-• a b = begin
      π • (a • b) • π′
        ≈⟨ by-passoc (□ • (□ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
      π • a • b • π′
        ≈⟨ back _ (back _ (trans (sym left-unit) (front _ (sym e₂)))) ⟩
      π • a • (π′ • π) • b • π′
        ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
      ⟪ a ⟫ • ⟪ b ⟫ ∎

    ⟪⟫-•₃ : ∀ {a b d a′ b′ d′} → ⟪ a ⟫ ≈ a′ → ⟪ b ⟫ ≈ b′ → ⟪ d ⟫ ≈ d′ → ⟪ a • b • d ⟫ ≈ a′ • b′ • d′
    ⟪⟫-•₃ {a} {b} {d} ea eb ed = trans (⟪⟫-• a (b • d)) (cong ea (trans (⟪⟫-• b d) (cong eb ed)))

    private
      unwrap : ∀ x → π′ • ⟪ x ⟫ • π ≈ x
      unwrap x = begin
        π′ • (π • x • π′) • π      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
        (π′ • π) • x • (π′ • π)    ≈⟨ cong e₂ (back _ e₂) ⟩
        ε • x • ε                  ≈⟨ trans left-unit right-unit ⟩
        x ∎

    back′ : ∀ {a b a′ b′} → ⟪ a ⟫ ≈ a′ → ⟪ b ⟫ ≈ b′ → a′ • b′ ≈ b′ • a′ → a • b ≈ b • a
    back′ {a} {b} ea eb e = begin
      a • b                  ≈⟨ sym (unwrap (a • b)) ⟩
      π′ • ⟪ a • b ⟫ • π     ≈⟨ mid _ _ (trans (⟪⟫-• a b) (trans (cong ea eb) (trans e (sym (trans (⟪⟫-• b a) (cong eb ea)))))) ⟩
      π′ • ⟪ b • a ⟫ • π     ≈⟨ unwrap (b • a) ⟩
      b • a ∎

  ----------------------------------------------------------------------
  -- The four-wire boxes and the relabellings

  b₁₁ b₁₀ b₀₁ b₀₀ B3 πa πa′ πb πb′ : Circuit N
  b₁₁ = B46.bb ↓ᵏ m′
  b₁₀ = X ↑ ↑ • b₁₁ • X ↑ ↑
  b₀₁ = X • b₁₁ • X
  b₀₀ = X • b₁₀ • X
  B3  = Λ□ 3 ↓ᵏ m′
  πa  = B46.πa ↓ᵏ m′
  πa′ = B46.πa′ ↓ᵏ m′
  πb  = B46.πb ↓ᵏ m′
  πb′ = B46.πb′ ↓ᵏ m′

  G′ G ζ η Vo Vc Vo′ Q : Circuit N
  G′  = PP ↑ • D0 • PP ↑
  G   = PP ↑ • C0 • PP ↑
  ζ   = X ↑ ↑ • CZ ↑ • X ↑ ↑
  η   = PP ↑ • CZ ↑ • PP ↑
  Vo  = b₀₀ • (PP ↑ • b₀₁ • PP ↑)
  Vc  = b₁₀ • (PP ↑ • b₁₁ • PP ↑)
  Vo′ = (PP ↑ • b₀₁ • PP ↑) • b₀₀
  Q   = C0 • G′

  private
    ev : ∀ {u v : Circuit 4} → Evaluated u v → (u ↓ᵏ m′) ≈ (v ↓ᵏ m′)
    ev {u} {v} e = by-sem u v (Evaluated.same e) {m′}

  module Ra = Rel πa πa′ (ev B46.ea₁) (ev B46.ea₂)
  module Rb = Rel πb πb′ (ev B46.eb₁) (ev B46.eb₂)

  private
    Ex↑↑² : Ex ↑ ↑ • Ex ↑ ↑ ≈ ε
    Ex↑↑² = lemma-cong↑ _ _ (lemma-cong↑ _ _ Ex²)

    -- The swaps of the wires 2 3 and 1 2 pass the box.
    E-Λ₀ : Ex ↑ • Ex ↑ ↑ • Λ₀ • Ex ↑ ↑ • Ex ↑ ≈ Λ₀
    E-Λ₀ = begin
      Ex ↑ • Ex ↑ ↑ • Λ₀ • Ex ↑ ↑ • Ex ↑
        ≈⟨ back _ (trans (sym assoc) (trans (front _ (symAt 1)) (trans assoc (back _ (trans (sym assoc) (trans (front _ Ex↑↑²) left-unit)))))) ⟩
      Ex ↑ • Λ₀ • Ex ↑
        ≈⟨ S₁₂-Λ₀ ⟩
      Λ₀ ∎

  -- The box on wire 2 under πa is the box on wire 1, and so is the box on
  -- wire 1 under πb.
  Ra-Λ₂ : Ra.⟪ Λ₂ ⟫ ≈ Λ₁
  Ra-Λ₂ = begin
    πa • (Ex ↑ • (Ex • Λ₀ • Ex) • Ex ↑) • πa′
      ≈⟨ by-passoc (□ • (□ • (□ • □ • □) • □) • □) ((□ • (□ • □)) • □ • ((□ • □) • □)) Eq.refl ⟩
    (πa • (Ex ↑ • Ex)) • Λ₀ • ((Ex • Ex ↑) • πa′)
      ≈⟨ cong (ev B46.ea-L) (back _ (ev B46.ea-R)) ⟩
    (Ex • (Ex ↑ • Ex ↑ ↑)) • Λ₀ • ((Ex ↑ ↑ • Ex ↑) • Ex)
      ≈⟨ by-passoc ((□ • (□ • □)) • □ • ((□ • □) • □)) (□ • (□ • □ • □ • □ • □) • □) Eq.refl ⟩
    Ex • (Ex ↑ • Ex ↑ ↑ • Λ₀ • Ex ↑ ↑ • Ex ↑) • Ex
      ≈⟨ mid _ _ E-Λ₀ ⟩
    Λ₁ ∎

  Rb-Λ₁ : Rb.⟪ Λ₁ ⟫ ≈ Λ₁
  Rb-Λ₁ = begin
    πb • (Ex • Λ₀ • Ex) • πb′
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (πb • Ex) • Λ₀ • (Ex • πb′)
      ≈⟨ cong (ev B46.eb-L) (back _ (ev B46.eb-R)) ⟩
    (Ex • (Ex ↑ • Ex ↑ ↑)) • Λ₀ • ((Ex ↑ ↑ • Ex ↑) • Ex)
      ≈⟨ by-passoc ((□ • (□ • □)) • □ • ((□ • □) • □)) (□ • (□ • □ • □ • □ • □) • □) Eq.refl ⟩
    Ex • (Ex ↑ • Ex ↑ ↑ • Λ₀ • Ex ↑ ↑ • Ex ↑) • Ex
      ≈⟨ mid _ _ E-Λ₀ ⟩
    Λ₁ ∎

  ----------------------------------------------------------------------
  -- The canonical pairs with the four-wire box

  private
    ones′ : Bits m′
    ones′ = replicate m′ true

    -- The four-wire box is the box over every colouring of the wires 4 ….
    B3-∏ : B3 ≈ ∏ (allBits m′) (λ x → col (true ∷ true ∷ true ∷ true ∷ x) Λ₀)
    B3-∏ = sym (merge-top₃ m′ ≤-refl)

    X23 : X ↑ ↑ • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • X ↑ ↑
    X23 = lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ X))

    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    -- White on the wires 2 3.
    col-23 : ∀ (w : Circuit N) →
             col (true ∷ true ∷ false ∷ false ∷ ones′) w ≈ X ↑ ↑ • (X ↑ ↑ ↑ • w • X ↑ ↑ ↑) • X ↑ ↑
    col-23 w = begin
      col (true ∷ true ∷ false ∷ false ∷ ones′) w
        ≈⟨ ≡→≈ (Eq.cong (λ z → (X ↑ ↑ • X ↑ ↑ ↑ • z ↑ ↑ ↑ ↑) • w • (X ↑ ↑ • X ↑ ↑ ↑ • z ↑ ↑ ↑ ↑)) (allT m′)) ⟩
      (X ↑ ↑ • X ↑ ↑ ↑ • ε) • w • (X ↑ ↑ • X ↑ ↑ ↑ • ε)
        ≈⟨ cong (back _ right-unit) (back _ (trans (back _ right-unit) X23)) ⟩
      (X ↑ ↑ • X ↑ ↑ ↑) • w • (X ↑ ↑ ↑ • X ↑ ↑)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      X ↑ ↑ • (X ↑ ↑ ↑ • w • X ↑ ↑ ↑) • X ↑ ↑ ∎

  -- (339): the four-wire box against the H gate on wire 3 with its box
  -- wire 1, white on wire 2.
  C339₄ : B3 • (X ↑ ↑ • Hg₃ m′ • X ↑ ↑) ≈ (X ↑ ↑ • Hg₃ m′ • X ↑ ↑) • B3
  C339₄ = via (sym (col-2 (Hg₃ m′)))
            (via′ B3-∏ (sym (pass-∏ (allBits m′) (λ x → col (true ∷ true ∷ true ∷ true ∷ x) Λ₀)
                                  (λ x → sym (eq339 k below true x ones′)))))

  -- (336): the four-wire box against the box on wire 1, in any colours.
  B3-Λ₁ : ∀ t → B3 • col t Λ₁ ≈ col t Λ₁ • B3
  B3-Λ₁ t = via′ B3-∏ (sym (pass-∏ (allBits m′) (λ x → col (true ∷ true ∷ true ∷ true ∷ x) Λ₀)
              (λ x → sym (col-pair′ (true ∷ true ∷ true ∷ true ∷ x) t Λ₀ Λ₁ (eq336ᶜ k below)))))

  ----------------------------------------------------------------------
  -- The four-wire box, black on the wires 0 2, against the gates

  private
    X2P : X ↑ ↑ • P₁₃ ≈ P₁₃ • X ↑ ↑
    X2P = ev B46.e-X₂P

    Hg₃-form : ∀ {x} → x ≈ P₁₃ • (X ↑ ↑ • Λ₁ • X ↑ ↑) • P₁₃ → x ≈ X ↑ ↑ • Hg₃ m′ • X ↑ ↑
    Hg₃-form e = trans e (conj-swap (sym X2P) Λ₁)

    s1100 : Bits N
    s1100 = true ∷ true ∷ false ∷ false ∷ ones′

  b11-G′ : b₁₁ • G′ ≈ G′ • b₁₁
  b11-G′ = Ra.back′ (ev B46.ea-bb)
             (Hg₃-form (Ra.⟪⟫-•₃ (ev B46.ea-P) (Ra.⟪⟫-•₃ (ev B46.ea-X) Ra-Λ₂ (ev B46.ea-X)) (ev B46.ea-P)))
             C339₄

  b11-G : b₁₁ • G ≈ G • b₁₁
  b11-G = Rb.back′ (ev B46.eb-bb)
            (Hg₃-form (Rb.⟪⟫-•₃ (ev B46.eb-P) (Rb.⟪⟫-•₃ (ev B46.eb-X) Rb-Λ₁ (ev B46.eb-X)) (ev B46.eb-P)))
            C339₄

  b11-D0 : b₁₁ • D0 ≈ D0 • b₁₁
  b11-D0 = Ra.back′ (ev B46.ea-bb) (Ra.⟪⟫-•₃ (ev B46.ea-X) Ra-Λ₂ (ev B46.ea-X))
             (via (sym (col-2 Λ₁)) (B3-Λ₁ s110))

  XfX : Circuit N
  XfX = X • f • X

  b11-XfX : b₁₁ • XfX ≈ XfX • b₁₁
  b11-XfX = Ra.back′ (ev B46.ea-bb)
              (Ra.⟪⟫-•₃ (ev B46.ea-X) (Ra.⟪⟫-•₃ (ev B46.ea-X₁) Ra-Λ₂ (ev B46.ea-X₁)) (ev B46.ea-X))
              (via (sym (col-23 Λ₁)) (B3-Λ₁ s1100))

  b11-X2C0 : b₁₁ • (X ↑ ↑ • C0 • X ↑ ↑) ≈ (X ↑ ↑ • C0 • X ↑ ↑) • b₁₁
  b11-X2C0 = Rb.back′ (ev B46.eb-bb)
               (trans (Rb.⟪⟫-•₃ (ev B46.eb-X₂) (Rb.⟪⟫-•₃ (ev B46.eb-X) Rb-Λ₁ (ev B46.eb-X)) (ev B46.eb-X₂))
                      (conj-swap (sym X23) Λ₁))
               (via (sym (col-23 Λ₁)) (B3-Λ₁ s1100))

  ----------------------------------------------------------------------
  -- X on wire 2 passes the gates with their box wire there

  X2-Λ₂ : X ↑ ↑ • Λ₂ ≈ Λ₂ • X ↑ ↑
  X2-Λ₂ = τ-back (conj-sym τ² τX0) τΛ₂ (Canon.x-box canon)

  private
    X2-X : X ↑ ↑ • X ≈ X • X ↑ ↑
    X2-X = sym (X-↑ (X ↑))

    X2-X1 : X ↑ ↑ • X ↑ ≈ X ↑ • X ↑ ↑
    X2-X1 = sym (lemma-cong↑ _ _ (X-↑ X))

    X-Pu : X • PP ↑ ≈ PP ↑ • X
    X-Pu = X-↑ PP

  G′-form : G′ ≈ X • Vh • X
  G′-form = conj-swap (sym X-Pu) Λ₂

  X2-G′ : X ↑ ↑ • G′ ≈ G′ • X ↑ ↑
  X2-G′ = via G′-form (pass₃ X2-X X2-Vh X2-X)

  X2-D0 : X ↑ ↑ • D0 ≈ D0 • X ↑ ↑
  X2-D0 = pass₃ X2-X X2-Λ₂ X2-X

  X2-XfX : X ↑ ↑ • XfX ≈ XfX • X ↑ ↑
  X2-XfX = pass₃ X2-X (pass₃ X2-X1 X2-Λ₂ X2-X1) X2-X

  ----------------------------------------------------------------------
  -- The pairs of the endgame

  b10-C0 : b₁₀ • C0 ≈ C0 • b₁₀
  b10-C0 = CN.carry refl (N₂.⟪⟫-⟪⟫ C0) b11-X2C0

  b10-G′ : b₁₀ • G′ ≈ G′ • b₁₀
  b10-G′ = CN.carry refl (N₂.⟪⟫-fix X2-G′) b11-G′

  Pb11-C0 : (PP ↑ • b₁₁ • PP ↑) • C0 ≈ C0 • (PP ↑ • b₁₁ • PP ↑)
  Pb11-C0 = Pu-back (Pu.⟪⟫-⟪⟫ b₁₁) refl b11-G

  Pb11-G′ : (PP ↑ • b₁₁ • PP ↑) • G′ ≈ G′ • (PP ↑ • b₁₁ • PP ↑)
  Pb11-G′ = Pu-back (Pu.⟪⟫-⟪⟫ b₁₁) (Pu.⟪⟫-⟪⟫ D0) b11-D0

  Vc-Q : Vc • Q ≈ Q • Vc
  Vc-Q = pass₂′ (pass₂ b10-C0 b10-G′) (pass₂ Pb11-C0 Pb11-G′)

  -- The H gate Vh.
  Vh-b00 : Vh • b₀₀ ≈ b₀₀ • Vh
  Vh-b00 = X-back (sym G′-form) (unconj X²) (sym b10-G′)

  Λ₂-b01 : Λ₂ • b₀₁ ≈ b₀₁ • Λ₂
  Λ₂-b01 = X-back refl (unconj X²) (sym b11-D0)

  Vh-Pb01 : Vh • (PP ↑ • b₀₁ • PP ↑) ≈ (PP ↑ • b₀₁ • PP ↑) • Vh
  Vh-Pb01 = Pu-back (Pu.⟪⟫-⟪⟫ Λ₂) (Pu.⟪⟫-⟪⟫ b₀₁) Λ₂-b01

  -- (338) with x ≠ y: the H gate against the box on its H wire,
  -- separated on wire 0, under the cycle of the wires 0 1 2.
  G′-Λ₁ : G′ • Λ₁ ≈ Λ₁ • G′
  G′-Λ₁ = π-back πG′ πΛ₁
            (sym (via (sym (col-2 HG)) (sep k below (replicate (₂₊ k) true))))
    where
    πG′ : πc G′ ≈ X ↑ ↑ • HG • X ↑ ↑
    πG′ = trans (πc-•₃ πPPu (πc-•₃ πX0 πΛ₂ πX0) πPPu) (conj-swap PX2 Λ₁)

  Vh-C0 : Vh • C0 ≈ C0 • Vh
  Vh-C0 = X-back (sym G′-form) (unconj X²) G′-Λ₁

  Λ₂-D0 : Λ₂ • D0 ≈ D0 • Λ₂
  Λ₂-D0 = τ-back τΛ₂ (T.⟪⟫-•₃ τX0 τΛ₂ τX0) W-Zg

  Vh-G′ : Vh • G′ ≈ G′ • Vh
  Vh-G′ = Pu-back (Pu.⟪⟫-⟪⟫ Λ₂) (Pu.⟪⟫-⟪⟫ D0) Λ₂-D0

  -- The box Fo, as Λ₂ f.
  private
    τf : T.⟪ f ⟫ ≈ Y
    τf = T.⟪⟫-•₃ τX1 τΛ₂ τX1

    τC0 : T.⟪ C0 ⟫ ≈ X ↑ ↑ • Λ₁ • X ↑ ↑
    τC0 = T.⟪⟫-•₃ τX0 τΛ₁ τX0

  Λ₂-C0 : Λ₂ • C0 ≈ C0 • Λ₂
  Λ₂-C0 = τ-back τΛ₂ τC0 (via (sym (col-2 Λ₁)) (eq336ᶜ k below s110))

  f-C0 : f • C0 ≈ C0 • f
  f-C0 = τ-back τf τC0
           (both (sym (col-1 Λ₀)) (sym (col-2 Λ₁)) (col-pair′ s101 s110 Λ₀ Λ₁ (eq336ᶜ k below)))

  f-D0 : f • D0 ≈ D0 • f
  f-D0 = τ-back τf (T.⟪⟫-•₃ τX0 τΛ₂ τX0) Y-Zg

  Λ₂-b00 : Λ₂ • b₀₀ ≈ b₀₀ • Λ₂
  Λ₂-b00 = X-back refl (unconj X²) (CN.carry (N₂.⟪⟫-fix X2-D0) refl (sym b11-D0))

  f-b00 : f • b₀₀ ≈ b₀₀ • f
  f-b00 = X-back refl (unconj X²) (CN.carry (N₂.⟪⟫-fix X2-XfX) refl (sym b11-XfX))

  f-b01 : f • b₀₁ ≈ b₀₁ • f
  f-b01 = X-back refl (unconj X²) (sym b11-XfX)

  Fo≈ : Fo ≈ Λ₂ • f
  Fo≈ = sym Fo-form

  Fo-b00 : Fo • b₀₀ ≈ b₀₀ • Fo
  Fo-b00 = via′ Fo≈ (pass₂′ Λ₂-b00 f-b00)

  Fo-Pb01 : Fo • (PP ↑ • b₀₁ • PP ↑) ≈ (PP ↑ • b₀₁ • PP ↑) • Fo
  Fo-Pb01 = Pu-back PuFo (Pu.⟪⟫-⟪⟫ b₀₁) (via′ Fo≈ (pass₂′ Λ₂-b01 f-b01))

  Fo-C0 : Fo • C0 ≈ C0 • Fo
  Fo-C0 = via′ Fo≈ (pass₂′ Λ₂-C0 f-C0)

  Fo-G′ : Fo • G′ ≈ G′ • Fo
  Fo-G′ = Pu-back PuFo (Pu.⟪⟫-⟪⟫ D0) (via′ Fo≈ (pass₂′ Λ₂-D0 f-D0))

  -- Vh Fo passes Vo, C0 G′ and Vo′.
  private
    VF : ∀ {x} → Vh • x ≈ x • Vh → Fo • x ≈ x • Fo → (Vh • Fo) • x ≈ x • (Vh • Fo)
    VF ev ef = pass₂′ ev ef

  VF-Vo : (Vh • Fo) • Vo ≈ Vo • (Vh • Fo)
  VF-Vo = VF (pass₂ Vh-b00 Vh-Pb01) (pass₂ Fo-b00 Fo-Pb01)

  VF-Q : (Vh • Fo) • Q ≈ Q • (Vh • Fo)
  VF-Q = VF (pass₂ Vh-C0 Vh-G′) (pass₂ Fo-C0 Fo-G′)

  VF-Vo′ : (Vh • Fo) • Vo′ ≈ Vo′ • (Vh • Fo)
  VF-Vo′ = VF (pass₂ Vh-Pb01 Vh-b00) (pass₂ Fo-Pb01 Fo-b00)

  ----------------------------------------------------------------------
  -- Between P ⊗ P on the wires 0 1

  private
    PUA : P.⟪ UA ⟫ ≈ ζ
    PUA = L₃-sem (PP • (X ↑ ↑ • CH ↑ • X ↑ ↑) • PP) (X ↑ ↑ • CZ ↑ • X ↑ ↑) Eq.refl

    PUB : P.⟪ UB ⟫ ≈ η
    PUB = L₃-sem (PP • (Ex ↑ • CH ↑ • Ex ↑) • PP) (PP ↑ • CZ ↑ • PP ↑) Eq.refl

    PK₁ : P.⟪ K₁ ⟫ ≈ C0
    PK₁ = trans (P.⟪⟫-•₂ PYo (trans (P.⟪⟫-cong D≈HG) (P.⟪⟫-⟪⟫ Λ₁)))
                (trans (front _ Yo-form) (trans assoc (trans (back _ Λ₁²) right-unit)))

    Zo-form : Zo ≈ D0 • Λ₂
    Zo-form = trans (S₁₂.⟪⟫-cong Yo-form) (S₁₂.⟪⟫-•₂ (S₁₂.⟪⟫-•₃ S12X0 refl S12X0) refl)

    ZoΛ₂ : Zo • Λ₂ ≈ D0
    ZoΛ₂ = trans (front _ Zo-form) (trans assoc (trans (back _ Λ₂²) right-unit))

    PK₂ : P.⟪ K₂ ⟫ ≈ G′
    PK₂ = begin
      P.⟪ Zo • C ⟫
        ≈⟨ P.⟪⟫-cong (cong (sym QZo) (sym (conj-sym Q² QC))) ⟩
      P.⟪ Q.⟪ Zo ⟫ • Q.⟪ Λ₂ ⟫ ⟫
        ≈⟨ P.⟪⟫-cong (trans (sym (Q.⟪⟫-• Zo Λ₂)) (Q.⟪⟫-cong ZoΛ₂)) ⟩
      PP • (PP₀₂ • D0 • PP₀₂) • PP
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (PP • PP₀₂) • D0 • (PP₀₂ • PP)
        ≈⟨ cong klein₂ (back _ klein₁) ⟩
      G′ ∎

    e1 : ζ • η ≈ Vo • Vc
    e1 = ev B46.e-ζη

    e2 : Vc • η • ζ ≈ Vo′
    e2 = ev B46.e-Vc

  M : Circuit N
  M = UA • (UB • (K₁ • K₂) • UB) • UA

  PM : P.⟪ M ⟫ ≈ Vo • Q • Vo′
  PM = begin
    P.⟪ M ⟫
      ≈⟨ P.⟪⟫-•₃ PUA (P.⟪⟫-•₃ PUB (P.⟪⟫-•₂ PK₁ PK₂) PUB) PUA ⟩
    ζ • (η • Q • η) • ζ
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (ζ • η) • Q • (η • ζ)
      ≈⟨ front _ e1 ⟩
    (Vo • Vc) • Q • (η • ζ)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □) • □ • □) Eq.refl ⟩
    Vo • (Vc • Q) • η • ζ
      ≈⟨ back _ (front _ Vc-Q) ⟩
    Vo • (Q • Vc) • η • ζ
      ≈⟨ by-passoc (□ • (□ • □) • □ • □) (□ • □ • (□ • □ • □)) Eq.refl ⟩
    Vo • Q • (Vc • η • ζ)
      ≈⟨ back _ (back _ e2) ⟩
    Vo • Q • Vo′ ∎

  F-M : F • M ≈ M • F
  F-M = P-back PF PM (pass₃ VF-Vo VF-Q VF-Vo′)

  endgame : Endgame
  endgame = CUA.carry refl (unconj UA²) F-M

  core46 : Core46 {₂₊ k}
  core46 = reduce endgame
