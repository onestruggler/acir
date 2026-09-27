------------------------------------------------------------------------
-- Presentations of groups
--
-- The box is the square of the multi-controlled ZX (Clément, Lemma D.15,
-- Equation (355))
--
-- At width 5 + k, with Λ the box on wire 0 controlled by all the other
-- wires, E = Ex-conj Λ the box on wire 1 and Z₀ = Z on wire 0:
--
--   Λ ≈ ΛXZ • ΛXZ   (`eq355`)        Λ ≈ ΛZX • ΛZX   (`eq355′`)
--
-- The paper splits the singly controlled rotations of (305) over every
-- colouring of the wires 2 … by (354) and passes the pieces by (347).
-- Here the D-trick of GeneralN.Canon40 runs on the box instead:
--
--   * Λ ≈ Z₀ W Z₀ W with W = CH E CH, from (305) (BoxForms), Z on a
--     control (270) and on the box wire (19), and CH passing Λ (298);
--   * Z₀ is E merged over every colouring of the wires 2 …
--     (MergeAll.merge-top₁), and every factor but the black one passes
--     ΛZX: ΛZX ≈ h E h E by (353) (h the four-wire H gate H●), and E
--     white on wire 2 is X on wire 2 around E, which h passes (ZX353's
--     `Bo-h`), up to a colouring above wire 2 that h does not see (X on
--     its box wire 3 passes it, Base355); other white controls are moved
--     to wire 2 by adjacent swaps (`move′`);
--   * so D′ = Z₀ E passes ΛZX (Canon40's `pass-last`) and E, and
--     Λ ≈ D′ E W D′ E W ≈ E W E W = ΛXZ ΛXZ.
--
-- The plan was checked step by step numerically at four to seven wires
-- first, by a workflow with an adversarial reviewer (scratchpad r4x).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.ZX355
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero)
open import Data.Nat using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n ; ≤-refl)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (swapAt)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; Ex² ; CH² ; Z² ; X² ; S-Z↑)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; swB ; swapAt-negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.LocalPlace using (local-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (swapAt² ; swap-far)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃ using (eq270 ; box-Z₀)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFull complete₂ complete₃ using (eq298)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxForms complete₂ complete₃ using (eq305)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; SymAt ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All complete₂ complete₃ using (mergesₙ)
import Examples.Groups.Real-Clifford+CH.GeneralN.MergeAll as MergeAll
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (col ; col-Ex ; conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base353 using (H○ ; H● ; e-CH ; e-comm ; e-○²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base355 using (e-X₃●)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃
  using (B-o ; Bo-h ; ∏-conj ; ∏-cong ; allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon40 complete₂ complete₃ using (pass-last ; swB-invol ; swB-1)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (module Carry)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (move′ ; eq335)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N m′ : ℕ
    N  = ₁₊ (₄₊ k)
    m′ = ₁₊ k

    c₄ : Comp 4
    c₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

    c : Comp (₄₊ k)
    c = below (n<1+n (₄₊ k))

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    symAt : SymAt (₁₊ k)
    symAt = eqSymAt (₁₊ k) completes

    canon : Canon (₂₊ k)
    canon = canonN k completes

  open Tools (N VRel,_===_)
  open SS.Below 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) c₄ using (by-sem)
  open MergeAll (₃₊ k) (mergesₙ k completes) using (merge-top₁)

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    via : ∀ {y u w : Circuit N} → u ≈ w → y • w ≈ w • y → y • u ≈ u • y
    via e p = trans (back _ e) (trans p (front _ (sym e)))

    pass₂ : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
    pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

    Λ E Z₀ W h o : Circuit N
    Λ  = Λ□ (₄₊ k)
    E  = Ex ↓ • Λ • Ex ↓
    Z₀ = Ex ↓ • Z ↑ • Ex ↓
    W  = CH • E • CH
    h  = H● ↓ᵏ m′
    o  = H○ ↓ᵏ m′

    module C₁ = Carry {N} (Ex ↓) Ex²

    --------------------------------------------------------------------
    -- Involutions and the three commutations with Λ and E

    Λ² : Λ • Λ ≈ ε
    Λ² = Canon.invol canon

    E² : E • E ≈ ε
    E² = S₀₁.⟪⟫-invol Λ²

    Z₀² : Z₀ • Z₀ ≈ ε
    Z₀² = S₀₁.⟪⟫-invol (lemma-cong↑ _ _ Z²)

    Z₀E : Z₀ • E ≈ E • Z₀
    Z₀E = C₁.carry refl refl (eq270 (₄₊ k) fzero)

    Z₀Λ : Z₀ • Λ ≈ Λ • Z₀
    Z₀Λ = trans (front _ S-Z↑) (trans (box-Z₀ (₂₊ k)) (back _ (sym S-Z↑)))

    CHΛ : CH • Λ ≈ Λ • CH
    CHΛ = eq298 (₁₊ k) c

    --------------------------------------------------------------------
    -- (305) as Λ ≈ Z₀ W Z₀ W

    -- Conjugating Λ by CH Z₀ changes nothing.
    fix : Λ ≈ (CH • Z₀) • Λ • (Z₀ • CH)
    fix = sym (begin
      (CH • Z₀) • Λ • (Z₀ • CH)          ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □) • □ • □) Eq.refl ⟩
      CH • (Z₀ • Λ) • Z₀ • CH            ≈⟨ back _ (front _ Z₀Λ) ⟩
      CH • (Λ • Z₀) • Z₀ • CH            ≈⟨ back _ (trans assoc (back _ (trans (sym assoc) (trans (front _ Z₀²) left-unit)))) ⟩
      CH • Λ • CH                        ≈⟨ trans (sym assoc) (front _ CHΛ) ⟩
      (Λ • CH) • CH                      ≈⟨ cancelʳ _ CH² ⟩
      Λ ∎)

    Λ-W : Λ ≈ Z₀ • W • Z₀ • W
    Λ-W = begin
      Λ
        ≈⟨ fix ⟩
      (CH • Z₀) • Λ • (Z₀ • CH)
        ≈⟨ back _ (front _ (sym (eq305 k c))) ⟩
      (CH • Z₀) • ((Z₀ • CH • Z₀ • CH) • E • (CH • Z₀ • CH • Z₀) • E) • (Z₀ • CH)
        ≈⟨ by-passoc ((□ • □) • ((□ • □ • □ • □) • □ • (□ • □ • □ • □) • □) • (□ • □))
                     (□ • (□ • □) • □ • □ • □ • □ • □ • □ • □ • (□ • □ • □) • □) Eq.refl ⟩
      CH • (Z₀ • Z₀) • CH • Z₀ • CH • E • CH • Z₀ • CH • (Z₀ • E • Z₀) • CH
        ≈⟨ trans (back _ (trans (front _ Z₀²) left-unit)) (trans (sym assoc) (trans (front _ CH²) left-unit)) ⟩
      Z₀ • CH • E • CH • Z₀ • CH • (Z₀ • E • Z₀) • CH
        ≈⟨ back _ (back _ (back _ (back _ (back _ (back _ (front _ ZEZ)))))) ⟩
      Z₀ • CH • E • CH • Z₀ • CH • E • CH
        ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □ • □) (□ • (□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
      Z₀ • W • Z₀ • W ∎
      where
      ZEZ : Z₀ • E • Z₀ ≈ E
      ZEZ = trans (sym assoc) (trans (front _ Z₀E) (trans assoc (trans (back _ Z₀²) right-unit)))

    W-ZX : W ≈ ΛZX (₄₊ k) • E
    W-ZX = sym (trans (by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl)
                      (back _ (back _ (trans (back _ E²) right-unit))))

    --------------------------------------------------------------------
    -- ΛZX in its form h E h E ((353))

    e₁ : CH ≈ h • o
    e₁ = by-sem (CH ↓) (H● • H○) (Evaluated.same e-CH) {m′}

    e₂ : o • h ≈ h • o
    e₂ = by-sem (H○ • H●) (H● • H○) (Evaluated.same e-comm) {m′}

    e₃ : o • o ≈ ε
    e₃ = by-sem (H○ • H○) ε (Evaluated.same e-○²) {m′}

    ZX-hE : ΛZX (₄₊ k) ≈ h • E • h • E
    ZX-hE = begin
      CH • E • CH • E
        ≈⟨ cong e₁ (back _ (front _ (trans e₁ (sym e₂)))) ⟩
      (h • o) • E • (o • h) • E
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
      h • (o • E) • o • h • E
        ≈⟨ back _ (front _ (sym (B-o k below))) ⟩
      h • (E • o) • o • h • E
        ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      h • E • (o • o) • h • E
        ≈⟨ back _ (back _ (trans (front _ e₃) left-unit)) ⟩
      h • E • h • E ∎

    --------------------------------------------------------------------
    -- Z₀ as E merged over every colouring of the wires 2 …

    Ec : Bits (₃₊ k) → Circuit N
    Ec y = col (true ∷ true ∷ y) E

    Ec-form : ∀ y → Ec y ≈ Ex ↓ • col (true ∷ true ∷ y) Λ • Ex ↓
    Ec-form y = conj-swap (sym (low-comm Ex (negsB y))) Λ

    Z₀-∏ : Z₀ ≈ ∏ (allBits (₃₊ k)) Ec
    Z₀-∏ = begin
      Ex ↓ • (Λ□ 1 ↓ᵏ (₃₊ k)) • Ex ↓
        ≈⟨ mid _ _ (sym (merge-top₁ (₃₊ k) ≤-refl)) ⟩
      Ex ↓ • ∏ (allBits (₃₊ k)) (λ y → col (true ∷ true ∷ y) Λ) • Ex ↓
        ≈⟨ ∏-conj (Ex ↓) Ex² (allBits (₃₊ k)) (λ y → col (true ∷ true ∷ y) Λ) ⟩
      ∏ (allBits (₃₊ k)) (λ y → Ex ↓ • col (true ∷ true ∷ y) Λ • Ex ↓)
        ≈⟨ ∏-cong (allBits (₃₊ k)) (λ y → sym (Ec-form y)) ⟩
      ∏ (allBits (₃₊ k)) Ec ∎

    Ec1 : Ec (replicate (₃₊ k) true) ≈ E
    Ec1 = trans (≡→≈ (Eq.cong (λ z → z ↑ ↑ • E • z ↑ ↑) (allT (₃₊ k)))) (trans left-unit right-unit)

    --------------------------------------------------------------------
    -- Every factor but the black one passes ΛZX

    -- h does not see a colouring of the wires 3 …: X on its box wire 3
    -- passes it, and it is local.
    h-U : ∀ (y : Bits (₂₊ k)) → h • negsB y ↑ ↑ ↑ ≈ negsB y ↑ ↑ ↑ • h
    h-U (true  ∷ y) = local-comm H● (negsB y)
    h-U (false ∷ y) = pass₂ hX (local-comm H● (negsB y))
      where
      hX : h • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • h
      hX = conj-comm (lemma-cong↑ _ _ (lemma-cong↑ _ _ (lemma-cong↑ _ _ X²)))
                     (by-sem (X ↑ ↑ ↑ • H● • X ↑ ↑ ↑) H● (Evaluated.same e-X₃●) {m′})

    -- E passes every colouring of itself ((335) under the swap of the
    -- wires 0 1).
    E-Ec : ∀ y → E • Ec y ≈ Ec y • E
    E-Ec y = C₁.carry refl (col-Ex (true ∷ true ∷ y) Λ) (eq335 k below (true ∷ true ∷ y))

    -- White on wire 2: X on wire 2 around E, which h passes (Bo-h), up to
    -- the colouring above.
    base : ∀ (y : Bits (₂₊ k)) → ΛZX (₄₊ k) • Ec (false ∷ y) ≈ Ec (false ∷ y) • ΛZX (₄₊ k)
    base y = sym (via ZX-hE (pass₂ Ec-h (pass₂ (sym (E-Ec (false ∷ y))) (pass₂ Ec-h (sym (E-Ec (false ∷ y)))))))
      where
      U : Circuit N
      U = negsB y ↑ ↑ ↑
      X₂U : X ↑ ↑ • U ≈ U • X ↑ ↑
      X₂U = lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ (negsB y)))
      Ec-UBoU : Ec (false ∷ y) ≈ U • N₂.⟪ E ⟫ • U
      Ec-UBoU = begin
        (X ↑ ↑ • U) • E • (X ↑ ↑ • U)       ≈⟨ front _ X₂U ⟩
        (U • X ↑ ↑) • E • (X ↑ ↑ • U)       ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
        U • (X ↑ ↑ • E • X ↑ ↑) • U ∎
      Ec-h : Ec (false ∷ y) • h ≈ h • Ec (false ∷ y)
      Ec-h = sym (via Ec-UBoU (pass₂ (h-U y) (pass₂ (sym (Bo-h k below)) (h-U y))))

    -- The swap of two adjacent wires above wire 1.
    module Sw (i : ℕ) where
      S : Circuit N
      S = swapAt (suc (suc i))

      S² : S • S ≈ ε
      S² = swapAt² (suc (suc i))

      S-Ex : S • Ex ≈ Ex • S
      S-Ex = sym (swap-far 0 (suc (suc i)) (s≤s (s≤s z≤n)))

      S-E : S • E ≈ E • S
      S-E = pass₂ S-Ex (pass₂ (symAt (suc i)) S-Ex)

      S-CH : S • CH ≈ CH • S
      S-CH = sym (low-comm CH (swapAt i))

      S-ZX : S • ΛZX (₄₊ k) ≈ ΛZX (₄₊ k) • S
      S-ZX = pass₂ S-CH (pass₂ S-E (pass₂ S-CH S-E))

      module CS = Carry {N} S S²
      module TS = Conj {N} S S²

      S-Ec : ∀ t → TS.⟪ Ec (swB i t) ⟫ ≈ Ec t
      S-Ec t = trans (TS.⟪⟫-•₃ (swapAt-negsB (suc (suc i)) (true ∷ true ∷ swB i t))
                               (TS.⟪⟫-fix S-E)
                               (swapAt-negsB (suc (suc i)) (true ∷ true ∷ swB i t)))
                     (≡→≈ (Eq.cong (λ z → col (true ∷ true ∷ z) E) (swB-invol i t)))

    Q : Bits (₃₊ k) → Set
    Q t = t ≢ replicate (₃₊ k) true → ΛZX (₄₊ k) • Ec t ≈ Ec t • ΛZX (₄₊ k)

    all : ∀ t → Q t
    all = move′ Q (λ r _ → base r)
                (λ i t q t≢ → Sw.CS.carry i (Sw.TS.⟪⟫-fix i (Sw.S-ZX i)) (Sw.S-Ec i t)
                                (q (λ e → t≢ (swB-1 i t e))))
                (λ ne → ⊥-elim (ne Eq.refl))

    --------------------------------------------------------------------
    -- D′ = Z₀ E passes ΛZX and E, and squares away

    D′ : Circuit N
    D′ = Z₀ • E

    ZX-D′ : ΛZX (₄₊ k) • D′ ≈ D′ • ΛZX (₄₊ k)
    ZX-D′ = via (cong Z₀-∏ (sym Ec1))
                (pass-last (₃₊ k) Ec all (trans (cong Ec1 Ec1) E²))

    E-D′ : E • D′ ≈ D′ • E
    E-D′ = trans (sym assoc) (front _ (sym Z₀E))

    D′² : D′ • D′ ≈ ε
    D′² = begin
      (Z₀ • E) • (Z₀ • E)      ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
      Z₀ • (E • Z₀) • E        ≈⟨ back _ (front _ (sym Z₀E)) ⟩
      Z₀ • (Z₀ • E) • E        ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
      (Z₀ • Z₀) • (E • E)      ≈⟨ trans (front _ Z₀²) (trans left-unit E²) ⟩
      ε ∎

    D′-W : D′ • W ≈ W • D′
    D′-W = via W-ZX (pass₂ (sym ZX-D′) (sym E-D′))

    Z₀-D′ : Z₀ ≈ D′ • E
    Z₀-D′ = sym (trans assoc (trans (back _ E²) right-unit))

  ----------------------------------------------------------------------
  -- (355)

  eq355 : Λ□ (₄₊ k) ≈ ΛXZ (₄₊ k) • ΛXZ (₄₊ k)
  eq355 = begin
    Λ
      ≈⟨ Λ-W ⟩
    Z₀ • W • Z₀ • W
      ≈⟨ cong Z₀-D′ (back _ (front _ Z₀-D′)) ⟩
    (D′ • E) • W • (D′ • E) • W
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □) (□ • □ • □ • □ • □ • □) Eq.refl ⟩
    D′ • E • W • D′ • E • W
      ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (sym D′-W)) assoc))) ⟩
    D′ • E • D′ • W • E • W
      ≈⟨ back _ (trans (sym assoc) (trans (front _ E-D′) assoc)) ⟩
    D′ • D′ • E • W • E • W
      ≈⟨ trans (sym assoc) (trans (front _ D′²) left-unit) ⟩
    E • W • E • W
      ≈⟨ by-passoc (□ • (□ • □ • □) • □ • (□ • □ • □)) ((□ • □ • □ • □) • (□ • □ • □ • □)) Eq.refl ⟩
    ΛXZ (₄₊ k) • ΛXZ (₄₊ k) ∎

  eq355′ : Λ□ (₄₊ k) ≈ ΛZX (₄₊ k) • ΛZX (₄₊ k)
  eq355′ = sym (begin
    ΛZX (₄₊ k) • ΛZX (₄₊ k)
      ≈⟨ insertʳ _ CH² ⟩
    ((ΛZX (₄₊ k) • ΛZX (₄₊ k)) • CH) • CH
      ≈⟨ front _ (by-passoc (((□ • □ • □ • □) • (□ • □ • □ • □)) • □) (□ • ((□ • □ • □ • □) • (□ • □ • □ • □))) Eq.refl) ⟩
    (CH • (ΛXZ (₄₊ k) • ΛXZ (₄₊ k))) • CH
      ≈⟨ front _ (back _ (sym eq355)) ⟩
    (CH • Λ) • CH
      ≈⟨ front _ CHΛ ⟩
    (Λ • CH) • CH
      ≈⟨ cancelʳ _ CH² ⟩
    Λ ∎)
