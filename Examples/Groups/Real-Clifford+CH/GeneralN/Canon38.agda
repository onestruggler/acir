------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical forms of rule (38) of Figure 8 (Clément, Lemma 8.8)
--
-- At width 5 + k, with HG the H gate (H on wire 0, box wire 1, Col.Hg)
-- and R β the rotation on wire 0 (RotCol), a rotation commutes with HG
-- when some wire above 1 other than its target separates their colours
-- — the paper's (348)–(350) with x ≠ y, here by the rotation's target:
--
--   * on wire 0 (`C38₀`), the colouring on HG black on wire 0 and white
--     on wire 2: the letters of R β (Canon32's HG and K, (333)/(334))
--     pass HG by Canon32.letter-comm, the white wire moved to 3;
--   * on wire 1 (`C38₁`), the colouring on the rotation, black on
--     wire 1 and white on wire 2: its letters under the swap of the
--     wires 0 1 are the crossed pairs of Canon32 (`HG-letter₁`);
--   * on wire 3 (`C38₂`), the rotation placed by the transposition of
--     the wires 0 3 and HG white on the wires 2 3.  Here the rotation is
--     c K c K with c the CH from wire 2 onto wire 3 ((353), K the box
--     on wire 2 which the transposition fixes); K passes HG by (339)
--     (Canon32.Kneg-HG), and c passes HG by `N2`, which is new: HG is
--     the box on wire 0 between P ⊗ P and the swap on the wires 0 1,
--     which c does not see, and by (320) the box is a word in four
--     rotations on the wires 0–3, which pass c by evaluation, and the
--     box `Box₃` with wire 3 idle; c with its control negated passes
--     Box₃ because, after moving the box wire onto the idle wire (274),
--     it is the CH from a control onto the box wire, (297).
--
-- Every step was checked numerically at five to seven wires first
-- (scratchpad r5x/r38, canon38.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon38
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl ; n≤1+n ; m≤n⇒m≤1+n)
open import Data.Vec using (_∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; perm ; φ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex² ; X²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₁₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃ using (ZX₃ ; XZ₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (revS ; negsB ; negs² ; swB ; swapAt-negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon ; pl ; pl-• ; pl-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (frame₁ ; pl-pl)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑ ; X-place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (swap-far)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; Hg)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; SymAt ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete ; box274)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFull complete₂ complete₃ using (eq297)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Gadget318 complete₂ complete₃ using (Box₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box320 complete₂ complete₃ using (eq320 ; Kᵇ ; Kᵇ′ ; D₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (module Carry)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (module XY)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (col-flip)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (S-ZX ; S-XZ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon40 complete₂ complete₃ using (Kcol)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon32 complete₂ complete₃
  using (letter ; letters ; letter-comm ; rot-rigid ; HG-letter₁ ; Kneg-HG)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base38
  using (c₄ ; Q₄ ; e-ZX ; e-XZ ; e-Kb ; e-Kb′ ; e-°c ; e-pc)

-- The transposition of the wires 0 3, and the network putting the box
-- on wire 2 (K below); where they send wires, at a variable width (at
-- a width 3 + m the conversion checker unfolds much further).
t03 : ∀ {n} → Word (S.Gen (₄₊ n))
t03 = S.σ • (S.σ S.↑ • ((S.σ S.↑) S.↑ • (S.σ S.↑ • S.σ)))

k₀ : ∀ {n} → Word (S.Gen (₄₊ n))
k₀ = S.σ S.↑ • S.σ

perm-t03 : ∀ {n} → perm {₄₊ n} t03 ⟨$⟩ʳ sF (sF (sF 0F)) ≡ 0F
perm-t03 = Eq.refl

cond-K : ∀ {n} → perm {₄₊ n} k₀ ⟨$⟩ʳ (perm (revS (t03 • k₀)) ⟨$⟩ʳ 0F) ≡ 0F
cond-K = Eq.refl

-- Word algebra at any width.
module _ {n : ℕ} where
  open Tools (n VRel,_===_)

  private
    passLg : ∀ {a b y : Circuit n} → a • y ≈ y • a → b • y ≈ y • b → (a • b) • y ≈ y • (a • b)
    passLg ea eb = trans assoc (trans (back _ eb) (trans (sym assoc) (trans (front _ ea) assoc)))

  -- Conjugation by a word with a left inverse carries a commutation.
  tcomm : ∀ {P Pi x y : Circuit n} → Pi • P ≈ ε → x • y ≈ y • x →
          (P • x • Pi) • (P • y • Pi) ≈ (P • y • Pi) • (P • x • Pi)
  tcomm {P} {Pi} {x} {y} e xy = trans (merge x y) (trans (back _ (front _ xy)) (sym (merge y x)))
    where
    merge : ∀ u v → (P • u • Pi) • (P • v • Pi) ≈ P • (u • v) • Pi
    merge u v = begin
      (P • u • Pi) • (P • v • Pi)   ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      P • u • (Pi • P) • v • Pi     ≈⟨ back _ (back _ (trans (front _ e) left-unit)) ⟩
      P • u • v • Pi                ≈⟨ back _ (sym assoc) ⟩
      P • (u • v) • Pi ∎

  -- s u s passes what s and u pass.
  conj-pass : ∀ {s u y : Circuit n} → s • y ≈ y • s → u • y ≈ y • u → (s • u • s) • y ≈ y • (s • u • s)
  conj-pass es eu = passLg es (passLg eu es)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    canon : Canon (₂₊ k)
    canon = canonN k completes

    completeₖ : Complete k
    completeₖ = completes (n≤1+n k)

    complete₁ₖ : Complete (₁₊ k)
    complete₁ₖ = completes ≤-refl

    symₖ : SymAt k
    symₖ = eqSymAt k (λ j≤ → completes (m≤n⇒m≤1+n j≤))

    comp₄ : Comp 4
    comp₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

  open Tools (N VRel,_===_)
  open SS.Below 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) comp₄ using (by-sem)
  open XY k below using (X-Hg)

  -- The H gate, the box on wire 2, the CH from wire 2 onto wire 3, and
  -- the transposition of the wires 0 3.
  HG K c₂₃ : Circuit N
  HG  = Hg (₂₊ k)
  K   = S₁₂.⟪ Ex ↓ • Λ□ (₄₊ k) • Ex ↓ ⟫
  c₂₃ = (Ex • CH • Ex) ↑ ↑

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    Λ : Circuit N
    Λ = Λ□ (₄₊ k)

    both : ∀ {p p′ q q′ : Circuit N} → p ≈ p′ → q ≈ q′ → p • q ≈ q • p → p′ • q′ ≈ q′ • p′
    both ep eq e = trans (sym (cong ep eq)) (trans e (cong eq ep))

    pass₂ : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
    pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

    passL : ∀ {a b y : Circuit N} → a • y ≈ y • a → b • y ≈ y • b → (a • b) • y ≈ y • (a • b)
    passL ea eb = trans assoc (trans (back _ eb) (trans (sym assoc) (trans (front _ ea) assoc)))

    fixc : ∀ {s u : Circuit N} → s • u ≈ u • s → s • s ≈ ε → s • u • s ≈ u
    fixc e s² = trans (sym assoc) (trans (front _ e) (trans assoc (trans (back _ s²) right-unit)))

    w4 : Circuit N → Circuit N → Circuit N
    w4 x y = x • y • x • y

    passW : ∀ {y a b : Circuit N} → a • y ≈ y • a → b • y ≈ y • b → w4 a b • y ≈ y • w4 a b
    passW ea eb = passL ea (passL eb (passL ea eb))

    passW′ : ∀ {y a b : Circuit N} → y • a ≈ a • y → y • b ≈ b • y → y • w4 a b ≈ w4 a b • y
    passW′ ea eb = pass₂ ea (pass₂ eb (pass₂ ea eb))

    Ex↑↑² : Ex ↑ ↑ • Ex ↑ ↑ ≈ ε
    Ex↑↑² = lemma-cong↑ _ _ (lemma-cong↑ _ _ Ex²)

    X↑↑² : X ↑ ↑ • X ↑ ↑ ≈ ε
    X↑↑² = lemma-cong↑ _ _ (lemma-cong↑ _ _ X²)

    X↑↑↑² : X ↑ ↑ ↑ • X ↑ ↑ ↑ ≈ ε
    X↑↑↑² = lemma-cong↑ _ _ (lemma-cong↑ _ _ (lemma-cong↑ _ _ X²))

    module C₂₃ = Carry {N} (Ex ↑ ↑) Ex↑↑²
    module CX  = Carry {N} X X²
    module CX₂ = Carry {N} (X ↑ ↑) X↑↑²
    module TX  = Conj {N} X X²
    module TX₂ = Conj {N} (X ↑ ↑) X↑↑²
    module S₂₃′ = Conj {N} (Ex ↑ ↑) Ex↑↑²
    module E₀ = Conj {N} Ex Ex²

    --------------------------------------------------------------------
    -- Colourings

    col-cong : ∀ (s : Bits N) {a b : Circuit N} → a ≈ b → col s a ≈ col s b
    col-cong s e = mid _ _ e

    col-• : ∀ (s : Bits N) a b → col s (a • b) ≈ col s a • col s b
    col-• s a b = sym (begin
      (negsB s • a • negsB s) • (negsB s • b • negsB s)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
      negsB s • a • ((negsB s • negsB s) • b • negsB s)
        ≈⟨ back _ (back _ (trans (front _ (negs² s)) left-unit)) ⟩
      negsB s • a • (b • negsB s)
        ≈⟨ back _ (sym assoc) ⟩
      negsB s • (a • b) • negsB s ∎)

    col-w4 : ∀ (s : Bits N) a b → col s (w4 a b) ≈ w4 (col s a) (col s b)
    col-w4 s a b = trans (col-• s a _) (back _ (trans (col-• s b _) (back _ (col-• s a b))))

    -- The swap of the wires 2 3 through a colouring.
    colS₂ : ∀ (s : Bits N) w → Ex ↑ ↑ • col s w • Ex ↑ ↑ ≈ col (swB 2 s) (Ex ↑ ↑ • w • Ex ↑ ↑)
    colS₂ s w = S₂₃′.⟪⟫-•₃ (swapAt-negsB 2 s) refl (swapAt-negsB 2 s)

    -- X on wire 0 around a colouring black there.
    colX0 : ∀ (s : Bits (₄₊ k)) w → X • col (true ∷ s) w • X ≈ col (false ∷ s) w
    colX0 s w = trans (by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl)
                      (back _ (back _ (sym (X-↑ (negsB s)))))

  ----------------------------------------------------------------------
  -- Networks above wire 1 pass HG

  HG-rigid : ∀ (v : Word (S.Gen (₃₊ k))) → net v ↑ ↑ • HG ≈ HG • net v ↑ ↑
  HG-rigid [ g ]ʷ  = pass₂ sPP (pass₂ sB sPP)
    where
    sPP : φ g ↑ ↑ • PP ↓ ≈ PP ↓ • φ g ↑ ↑
    sPP = sym (low-comm PP (φ g))
    sB : φ g ↑ ↑ • (Ex ↓ • Λ • Ex ↓) ≈ (Ex ↓ • Λ • Ex ↓) • φ g ↑ ↑
    sB = pass₂ (sym (low-comm Ex (φ g))) (pass₂ (Canon.swaps canon [ g S.↥ ]ʷ) (sym (low-comm Ex (φ g))))
  HG-rigid ε       = trans left-unit (sym right-unit)
  HG-rigid (u • v) = passL (HG-rigid u) (HG-rigid v)

  private
    HG-S₂₃ : Ex ↑ ↑ • HG • Ex ↑ ↑ ≈ HG
    HG-S₂₃ = fixc (HG-rigid [ S.gate₂ S.σ-gate ]ʷ) Ex↑↑²

    rot-S₂₃ : ∀ β → Ex ↑ ↑ • rot β • Ex ↑ ↑ ≈ rot β
    rot-S₂₃ β = fixc (rot-rigid k below β [ S.gate₂ S.σ-gate S.↥ ]ʷ) Ex↑↑²

  ----------------------------------------------------------------------
  -- The rotation on wire 0

  C38₀ : ∀ β (z : Bits N) → lookupℕ 0 z ≡ true → lookupℕ 2 z ≡ false →
         rot β • col z HG ≈ col z HG • rot β
  C38₀ β (true ∷ b ∷ false ∷ c ∷ r) Eq.refl Eq.refl =
    C₂₃.carry (rot-S₂₃ β) (trans (colS₂ e HG) (col-cong (swB 2 e) HG-S₂₃)) base
    where
    e : Bits N
    e = true ∷ b ∷ c ∷ false ∷ r
    base : rot β • col e HG ≈ col e HG • rot β
    base = both (sym (letters k below β)) refl
                (passW (letter-comm k below β true b c r) (letter-comm k below (not β) true b c r))
  C38₀ β (false ∷ _)             () _
  C38₀ β (true ∷ _ ∷ true ∷ _)   _  ()

  ----------------------------------------------------------------------
  -- The rotation on wire 1

  C38₁ : ∀ β (z : Bits N) → lookupℕ 1 z ≡ true → lookupℕ 2 z ≡ false →
         HG • col z (Ex • rot β • Ex) ≈ col z (Ex • rot β • Ex) • HG
  C38₁ β (a ∷ true ∷ false ∷ c ∷ r) Eq.refl Eq.refl =
    C₂₃.carry HG-S₂₃ (trans (colS₂ e (Ex • rot β • Ex)) (col-cong (swB 2 e) ExRE)) base
    where
    e : Bits N
    e = a ∷ true ∷ c ∷ false ∷ r
    ExRE : Ex ↑ ↑ • (Ex • rot β • Ex) • Ex ↑ ↑ ≈ Ex • rot β • Ex
    ExRE = trans (conj-swap (sym (swap-far 0 2 (s≤s (s≤s z≤n)))) (rot β)) (mid _ _ (rot-S₂₃ β))
    form : col e (Ex • rot β • Ex) ≈ w4 (col e (Ex • letter k below β • Ex)) (col e (Ex • letter k below (not β) • Ex))
    form = trans (col-cong e (trans (E₀.⟪⟫-cong (letters k below β)) (E₀.⟪⟫-•₄ refl refl refl refl)))
                 (col-w4 e _ _)
    base : HG • col e (Ex • rot β • Ex) ≈ col e (Ex • rot β • Ex) • HG
    base = both refl (sym form) (passW′ (HG-letter₁ k below β a c r) (HG-letter₁ k below (not β) a c r))
  C38₁ β (_ ∷ false ∷ _)         () _
  C38₁ β (_ ∷ true ∷ true ∷ _)   _  ()

  ----------------------------------------------------------------------
  -- K against HG white on the wires 2 3 ((339))

  KHG : ∀ (z : Bits N) → lookupℕ 2 z ≡ false → lookupℕ 3 z ≡ false → K • col z HG ≈ col z HG • K
  KHG (true  ∷ b ∷ false ∷ false ∷ r) Eq.refl Eq.refl = Kneg-HG k below true b false r
  KHG (false ∷ b ∷ false ∷ false ∷ r) Eq.refl Eq.refl =
    CX.carry (TX.⟪⟫-⟪⟫ K) (colX0 (b ∷ false ∷ false ∷ r) HG) (Kneg-HG k below false b false r)
  KHG (_ ∷ _ ∷ true ∷ _)         () _
  KHG (_ ∷ _ ∷ false ∷ true ∷ _) _  ()

  ----------------------------------------------------------------------
  -- N2: the CH from wire 2 onto wire 3 against HG white on the wires 2 3

  private
    Q : Circuit N
    Q = X ↑ ↑ • X ↑ ↑ ↑

    Q² : Q • Q ≈ ε
    Q² = begin
      (X ↑ ↑ • X ↑ ↑ ↑) • (X ↑ ↑ • X ↑ ↑ ↑)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
      X ↑ ↑ • (X ↑ ↑ ↑ • X ↑ ↑) • X ↑ ↑ ↑     ≈⟨ back _ (front _ (sym (lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ X))))) ⟩
      X ↑ ↑ • (X ↑ ↑ • X ↑ ↑ ↑) • X ↑ ↑ ↑     ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
      (X ↑ ↑ • X ↑ ↑) • (X ↑ ↑ ↑ • X ↑ ↑ ↑)   ≈⟨ trans (cong X↑↑² X↑↑↑²) left-unit ⟩
      ε ∎

    module TQ = Conj {N} Q Q²

    -- The four rotations of (320), by evaluation.
    eZX : c₂₃ • (Q • ZX₃ • Q) ≈ (Q • ZX₃ • Q) • c₂₃
    eZX = by-sem (c₄ • (Q₄ • ΛZX 3 • Q₄)) ((Q₄ • ΛZX 3 • Q₄) • c₄) (Evaluated.same e-ZX) {₁₊ k}

    eXZ : c₂₃ • (Q • XZ₃ • Q) ≈ (Q • XZ₃ • Q) • c₂₃
    eXZ = by-sem (c₄ • (Q₄ • ΛXZ 3 • Q₄)) ((Q₄ • ΛXZ 3 • Q₄) • c₄) (Evaluated.same e-XZ) {₁₊ k}

    eKb : c₂₃ • (Q • Kᵇ k below • Q) ≈ (Q • Kᵇ k below • Q) • c₂₃
    eKb = by-sem (c₄ • (Q₄ • (Ex • ΛZX 3 • Ex) • Q₄)) ((Q₄ • (Ex • ΛZX 3 • Ex) • Q₄) • c₄)
                 (Evaluated.same e-Kb) {₁₊ k}

    eKb′ : c₂₃ • (Q • Kᵇ′ k below • Q) ≈ (Q • Kᵇ′ k below • Q) • c₂₃
    eKb′ = by-sem (c₄ • (Q₄ • (Ex • ΛXZ 3 • Ex) • Q₄)) ((Q₄ • (Ex • ΛXZ 3 • Ex) • Q₄) • c₄)
                  (Evaluated.same e-Kb′) {₁₊ k}

    -- The box with wire 3 idle: its box wire moved onto wire 3 ((274)),
    -- the CH with its control negated is the CH from a control onto the
    -- box wire ((297)).
    Λ₃ : Circuit (₄₊ k)
    Λ₃ = Λ□ (₃₊ k)

    P Pi : Circuit N
    P  = Ex ↑ ↑ • Ex ↑
    Pi = Ex ↑ • Ex ↑ ↑

    Pi-P : Pi • P ≈ ε
    Pi-P = begin
      (Ex ↑ • Ex ↑ ↑) • (Ex ↑ ↑ • Ex ↑)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
      Ex ↑ • (Ex ↑ ↑ • Ex ↑ ↑) • Ex ↑     ≈⟨ back _ (trans (front _ Ex↑↑²) left-unit) ⟩
      Ex ↑ • Ex ↑                         ≈⟨ lemma-cong↑ _ _ Ex² ⟩
      ε ∎

    box-P : Box₃ k ≈ P • Λ₃ ↑ • Pi
    box-P = begin
      Box₃ k
        ≈⟨ cong (front _ (front _ left-unit)) (back _ (back _ (back _ right-unit))) ⟩
      ((Ex ↑ ↑ • Ex ↑) • Ex) • Λ₃ ↑ • (Ex • (Ex ↑ • Ex ↑ ↑))
        ≈⟨ by-passoc (((□ • □) • □) • □ • (□ • (□ • □))) ((□ • □) • (□ • □ • □) • (□ • □)) Eq.refl ⟩
      P • (Ex • Λ₃ ↑ • Ex) • Pi
        ≈⟨ back _ (front _ (box274 (₁₊ k) complete₁ₖ)) ⟩
      P • Λ₃ ↑ • Pi ∎

    oc oc31 : Circuit N
    oc   = X ↑ ↑ • c₂₃ • X ↑ ↑
    oc31 = (Ex ↑ • °CH • Ex ↑) ↑

    e297′ : (₄₊ k) ⊢ (Ex ↑ • °CH • Ex ↑) • Λ₃ ≈ Λ₃ • (Ex ↑ • °CH • Ex ↑)
    e297′ = conj-pass (symₖ 0) (eq297 k completeₖ)

    oc-P : oc ≈ P • oc31 • Pi
    oc-P = by-sem (X ↑ ↑ • c₄ • X ↑ ↑) ((Ex ↑ ↑ • Ex ↑) • (Ex ↑ • °CH • Ex ↑) ↑ • (Ex ↑ • Ex ↑ ↑))
                  (Evaluated.same e-°c) {₁₊ k}

    oc-box : oc • Box₃ k ≈ Box₃ k • oc
    oc-box = both (sym oc-P) (sym box-P) (tcomm Pi-P (lemma-cong↑ _ _ e297′))

    -- X on the idle wire 3 passes Box₃.
    QBQ : Q • Box₃ k • Q ≈ X ↑ ↑ • Box₃ k • X ↑ ↑
    QBQ = begin
      (X ↑ ↑ • X ↑ ↑ ↑) • Box₃ k • (X ↑ ↑ • X ↑ ↑ ↑)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □) • (□ • □)) Eq.refl ⟩
      X ↑ ↑ • (X ↑ ↑ ↑ • Box₃ k) • (X ↑ ↑ • X ↑ ↑ ↑)
        ≈⟨ back _ (front _ (X-place 3 Λ₃)) ⟩
      X ↑ ↑ • (Box₃ k • X ↑ ↑ ↑) • (X ↑ ↑ • X ↑ ↑ ↑)
        ≈⟨ by-passoc (□ • (□ • □) • (□ • □)) (□ • □ • (□ • □) • □) Eq.refl ⟩
      X ↑ ↑ • Box₃ k • (X ↑ ↑ ↑ • X ↑ ↑) • X ↑ ↑ ↑
        ≈⟨ back _ (back _ (front _ (sym (lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ X)))))) ⟩
      X ↑ ↑ • Box₃ k • (X ↑ ↑ • X ↑ ↑ ↑) • X ↑ ↑ ↑
        ≈⟨ back _ (back _ (trans assoc (trans (back _ X↑↑↑²) right-unit))) ⟩
      X ↑ ↑ • Box₃ k • X ↑ ↑ ∎

    eBox : c₂₃ • (Q • Box₃ k • Q) ≈ (Q • Box₃ k • Q) • c₂₃
    eBox = both refl (sym QBQ) (CX₂.carry (TX₂.⟪⟫-⟪⟫ c₂₃) refl oc-box)

    -- The box between Q, by (320).
    cQΛQ : c₂₃ • (Q • Λ • Q) ≈ (Q • Λ • Q) • c₂₃
    cQΛQ = both refl (sym form) (pass₂ eZX (pass₂ eD (pass₂ eXZ eD)))
      where
      DQ : Circuit N
      DQ = (Q • Kᵇ k below • Q) • (Q • Box₃ k • Q) • (Q • Kᵇ′ k below • Q)
      form : Q • Λ • Q ≈ (Q • ZX₃ • Q) • DQ • (Q • XZ₃ • Q) • DQ
      form = trans (TQ.⟪⟫-cong (eq320 k below))
                   (TQ.⟪⟫-•₄ refl (TQ.⟪⟫-•₃ refl refl refl) refl (TQ.⟪⟫-•₃ refl refl refl))
      eD : c₂₃ • DQ ≈ DQ • c₂₃
      eD = pass₂ eKb (pass₂ eBox eKb′)

    -- HG between Q: the box between P ⊗ P and the swap, which c does not
    -- see.
    cQHQ : c₂₃ • (Q • HG • Q) ≈ (Q • HG • Q) • c₂₃
    cQHQ = both refl (sym form) (pass₂ cPP (pass₂ (pass₂ cEx (pass₂ cQΛQ cEx)) cPP))
      where
      form : Q • HG • Q ≈ PP ↓ • (Ex ↓ • (Q • Λ • Q) • Ex ↓) • PP ↓
      form = trans (conj-swap (sym (low-comm PP (X • X ↑))) (Ex ↓ • Λ • Ex ↓))
                   (mid _ _ (conj-swap (sym (low-comm Ex (X • X ↑))) Λ))
      cPP : c₂₃ • PP ↓ ≈ PP ↓ • c₂₃
      cPP = sym (low-comm PP (Ex • CH • Ex))
      cEx : c₂₃ • Ex ↓ ≈ Ex ↓ • c₂₃
      cEx = sym (low-comm Ex (Ex • CH • Ex))

    -- The colours: on the wires above 3 c does not see them, on wire 1
    -- (HG's box wire) HG does not, on wire 0 X passes c.
    N2₂ : ∀ (r : Bits (₁₊ k)) → c₂₃ • col (true ∷ true ∷ false ∷ false ∷ r) HG ≈ col (true ∷ true ∷ false ∷ false ∷ r) HG • c₂₃
    N2₂ r = both refl (sym form) (pass₂ cR (pass₂ cQHQ cR))
      where
      R : Circuit N
      R = negsB r ↑ ↑ ↑ ↑
      RQ : R • Q ≈ Q • R
      RQ = sym (lemma-cong↑ _ _ (lemma-cong↑ _ _ (low-comm (X • X ↑) (negsB r))))
      cR : c₂₃ • R ≈ R • c₂₃
      cR = lemma-cong↑ _ _ (lemma-cong↑ _ _ (low-comm (Ex • CH • Ex) (negsB r)))
      form : col (true ∷ true ∷ false ∷ false ∷ r) HG ≈ R • (Q • HG • Q) • R
      form = begin
        (X ↑ ↑ • (X ↑ ↑ ↑ • R)) • HG • (X ↑ ↑ • (X ↑ ↑ ↑ • R))
          ≈⟨ cong (sym assoc) (back _ (sym assoc)) ⟩
        (Q • R) • HG • (Q • R)
          ≈⟨ front _ (sym RQ) ⟩
        (R • Q) • HG • (Q • R)
          ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
        R • (Q • HG • Q) • R ∎

    N2₁ : ∀ a (r : Bits (₁₊ k)) → c₂₃ • col (a ∷ true ∷ false ∷ false ∷ r) HG ≈ col (a ∷ true ∷ false ∷ false ∷ r) HG • c₂₃
    N2₁ true  r = N2₂ r
    N2₁ false r = CX.carry (TX.⟪⟫-fix (X-↑ ((Ex • CH • Ex) ↑))) (colX0 (true ∷ false ∷ false ∷ r) HG) (N2₂ r)

  N2 : ∀ (z : Bits N) → lookupℕ 2 z ≡ false → lookupℕ 3 z ≡ false → c₂₃ • col z HG ≈ col z HG • c₂₃
  N2 (a ∷ true  ∷ false ∷ false ∷ r) Eq.refl Eq.refl = N2₁ a r
  N2 (a ∷ false ∷ false ∷ false ∷ r) Eq.refl Eq.refl =
    both refl (sym (col-flip (sF 0F) (a ∷ true ∷ false ∷ false ∷ r) X-Hg)) (N2₁ a r)
  N2 (_ ∷ _ ∷ true ∷ _)         () _
  N2 (_ ∷ _ ∷ false ∷ true ∷ _) _  ()

  ----------------------------------------------------------------------
  -- The rotation on wire 3

  private
    CH₂ : Circuit N
    CH₂ = S₁₂.⟪ CH ⟫

    ZX-K : ΛZX (₄₊ k) ≈ CH₂ • K • CH₂ • K
    ZX-K = trans (sym (S-ZX k below)) (S₁₂.⟪⟫-•₄ refl refl refl refl)

    XZ-K : ΛXZ (₄₊ k) ≈ K • CH₂ • K • CH₂
    XZ-K = trans (sym (S-XZ k below)) (S₁₂.⟪⟫-•₄ refl refl refl refl)

    -- The transposition fixes K: it exchanges two of its controls.
    K-pl : K ≈ pl k₀ Λ
    K-pl = by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl

    pK : pl t03 K ≈ K
    pK = begin
      pl t03 K               ≈⟨ pl-cong t03 K-pl ⟩
      pl t03 (pl k₀ Λ)       ≈⟨ pl-pl t03 k₀ Λ ⟩
      pl (t03 • k₀) Λ        ≈⟨ frame₁ (Canon.swaps canon) (t03 • k₀) k₀ cond-K ⟩
      pl k₀ Λ                ≈⟨ sym K-pl ⟩
      K ∎

    -- It carries the CH from wire 2 onto wire 0 to c.
    pc : pl t03 CH₂ ≈ c₂₃
    pc = by-sem ((Ex • (Ex ↑ • (Ex ↑ ↑ • (Ex ↑ • Ex)))) • (Ex ↑ • CH • Ex ↑) • ((((Ex • Ex ↑) • Ex ↑ ↑) • Ex ↑) • Ex))
                c₄ (Evaluated.same e-pc) {₁₊ k}

    pl4 : ∀ x y → pl t03 (w4 x y) ≈ w4 (pl t03 x) (pl t03 y)
    pl4 x y = trans (pl-• t03 x _) (back _ (trans (pl-• t03 y _) (back _ (pl-• t03 x y))))

    rot-t : pl t03 (rot true) ≈ w4 c₂₃ K
    rot-t = trans (pl-cong t03 ZX-K) (trans (pl4 CH₂ K) (cong pc (cong pK (cong pc pK))))

    rot-f : pl t03 (rot false) ≈ w4 K c₂₃
    rot-f = trans (pl-cong t03 XZ-K) (trans (pl4 K CH₂) (cong pK (cong pc (cong pK pc))))

  C38₂ : ∀ β (z : Bits N) → lookupℕ 2 z ≡ false → lookupℕ 3 z ≡ false →
         pl t03 (rot β) • col z HG ≈ col z HG • pl t03 (rot β)
  C38₂ true  z z2 z3 = both (sym rot-t) refl (passW (N2 z z2 z3) (KHG z z2 z3))
  C38₂ false z z2 z3 = both (sym rot-f) refl (passW (KHG z z2 z3) (N2 z z2 z3))
