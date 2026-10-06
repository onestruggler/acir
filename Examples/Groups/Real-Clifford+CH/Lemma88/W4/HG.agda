------------------------------------------------------------------------
-- Presentations of groups
--
-- A placed rotation against the gadget on four qubits (Clément,
-- Appendix E.5 at n = 4, rule (38), from Lemma D.5)
--
-- On four wires the gadget is the H gate HG = ΛH₀₁ (H on wire 0, box
-- wire 1, controls 2 3) white on the wires 2 3, and HGFrom reduces
-- HGRot 1 to its three canonical cases, the rotation's target on wire 0,
-- 1 or 3.  Each is proved in the frame of the transposition of the wires
-- 1 3, where HG is Lemma D.5's ΛH₂′ (box wire 3, controls 1 2) and the
-- rotations are fixed:
--
-- * C0, target on wire 0: X on wire 1 passes HG ((207)); white on wire
--   2 the H gate passes both rotations ((210), (211): they are words in
--   ΛH₂′ and the box on wire 1, which pass it by (181)), and white on
--   the wires 2 3 too, being the H gate white on wire 2 times °CH₂₀
--   ((171ᶜ) under the swap of the wires 1 2), which the rotations pass
--   ((232), (233)).
-- * C1, target on wire 1: in the frame the rotation is (0 3)'s, a′ B a′ B
--   with a′ the CH from wire 1 onto wire 3 and B the box on wire 1.  ΛH₂′
--   is the box on wire 3 between P ⊗ P on the wires 0 3, which turns a′
--   into the CZ of the wires 1 3 ((160) under (0 3)); white on wire 1, a′
--   gains H on wire 3, which ΛH₂′ passes as ΛH₀₁ passes H on its box
--   wire ((154)).  B white on wire 2 is the box of (181ᵇ); white on wire
--   0 too it is that box times the CZ of the wires 2 3 negated on wire 2
--   (the merge (170)), which ΛH₂′ passes.
-- * C2, target on wire 3: in the frame the rotation is the one on wire
--   1, c K c K with c the CH from wire 2 onto wire 1 and K the box on
--   wire 2, and the H gate white on the wires 1 2 is °G °CH₂₀.  c passes
--   °CH₂₀ ((134)) and °G ((164) negated and under (0 3)), K passes it
--   ((181) under the middle swap); white on wire 0, K becomes K times the
--   CZ of the wires 1 3 (the merge (170) under (0 2)), which passes °G
--   ((163) under (0 3), between P ⊗ P).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W4.HG
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using () renaming (zero to 0F ; suc to sF)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; X² ; comm-↓↑)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; φ)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (°CH₂₀ ; eq134 ; module N₁ ; module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₀₁ ; module S₁₂ ; module S₂₃ ; L ; U ; O ; P₀₃ ; P₁₃ ; P₂₃ ; O₀ ; U₀ ; M₃ ;
         L-sem ; U-sem ; U₃-sem ; M₃-sem ; M₃-O ; M₃-U ; O-L ; P₂₃-S₀₁ ; P₁₃-O ; P₀₃-U)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃ using (box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq154 ; eq156 ; eq157 ; eq160 ; eq163 ; eq166)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃ using (°box₃ ; eq164 ; eq170)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃ using (box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃ using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃ using (ΛH₂′ ; °ΛH₂′ ; eq181)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃ using (eq181ᵇ ; CZ°₂₃-ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (eq171ᶜ ; ΛH₂′-°ΛH₂′ ; PP₀₁ ; PP₀₃ ; PP₀₁² ; PP₀₃² ; box₃‴ ; °box₃‴ ; ΛH₀₁-PP ; ΛH₂′-PP ; °ΛH₂′-PP)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (eq207 ; T₀₃-via ; T₀₃-L ; T₀₃-box₃ ; T₀₃-box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (eq210 ; eq211 ; eq214 ; eq214′ ; °ΛH₂′² ; box₃′²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations4 complete₂ complete₃ using (eq232 ; eq233)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (module T₁₃ ; module T₀₃ ; t₀₃ ; T₁₃-via ; T₁₃-back ; T₁₃-N₂ ; T₁₃-N₃ ; T₁₃-ΛH₂′ ; T₁₃-O ; T₀₃-nest′ ;
         S₂₃-ΛH₀₁ ; S₁₂-ΛH₂′ ; S₁₂-X₁ ; S₁₂-X₂ ; S₁₂-X₃ ; S₂₃-X₂ ; S₂₃-X₃ ; S₁₂-P₀₃ ; X₂-X₃ ;
         braid↑ ; braid-conj)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (swW)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (pl-col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; col-flip)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HGRotCol using (HGRot ; t03)
import Examples.Groups.Real-Clifford+CH.GeneralN.HGFrom as HGF
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Kit complete₂ complete₃ using (s12₄ ; rig₄)

open Tools (4 VRel,_===_)
open WordAlgebra (4 VRel,_===_) using (comm-abab)

private
  HG G °G : Circuit 4
  HG = Ex ↓ • ΛH 2 • Ex ↓
  G  = ΛH₂′
  °G = °ΛH₂′

  R : Bool → Circuit 4
  R = rot {1}

  pass₂ : ∀ {a u v : Circuit 4} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
  pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  passL : ∀ {a b y : Circuit 4} → a • y ≈ y • a → b • y ≈ y • b → (a • b) • y ≈ y • (a • b)
  passL ea eb = trans assoc (trans (back _ eb) (trans (sym assoc) (trans (front _ ea) assoc)))

------------------------------------------------------------------------
-- The H gate passes the networks on the wires 2 3

private
  HG-gen : ∀ (g : S.Gen 2) → φ g ↑ ↑ • HG ≈ HG • φ g ↑ ↑
  HG-gen (S.gate₀ ())
  HG-gen (S.gate₁ ())
  HG-gen (S.gate₂ S.σ-gate)    = S₂₃.⟪⟫-comm S₂₃-ΛH₀₁
  HG-gen (S.gate₀ () S.↥)
  HG-gen (S.gate₁ () S.↥)
  HG-gen (S.gate₀ () S.↥ S.↥)

HG-rigid₄ : ∀ (v : Word (S.Gen 2)) → net v ↑ ↑ • HG ≈ HG • net v ↑ ↑
HG-rigid₄ [ g ]ʷ  = HG-gen g
HG-rigid₄ ε       = trans left-unit (sym right-unit)
HG-rigid₄ (u • v) = passL (HG-rigid₄ u) (HG-rigid₄ v)

------------------------------------------------------------------------
-- The frame of the transposition of the wires 1 3

private
  T₁₃R : ∀ β → T₁₃.⟪ R β ⟫ ≈ R β
  T₁₃R β = T₁₃-via (s23 β) (S₁₂.⟪⟫-fix (s12₄ β)) (s23 β)
    where
    s23 : ∀ β → S₂₃.⟪ R β ⟫ ≈ R β
    s23 true  = S₂₃.⟪⟫-fix (sym eq214)
    s23 false = S₂₃.⟪⟫-fix (sym eq214′)

  T₁₃HG : T₁₃.⟪ HG ⟫ ≈ G
  T₁₃HG = T₁₃-back T₁₃-ΛH₂′

  -- An equation with a rotation, carried back from the frame.
  unframe : ∀ β {W W′ : Circuit 4} → T₁₃.⟪ W ⟫ ≈ W′ → R β • W′ ≈ W′ • R β → R β • W ≈ W • R β
  unframe β {W} {W′} t e = T₁₃.⟪⟫-≈ e (T₁₃.⟪⟫-•₂ (T₁₃R β) (T₁₃-back t)) (T₁₃.⟪⟫-•₂ (T₁₃-back t) (T₁₃R β))

------------------------------------------------------------------------
-- C0: the target on the H gate's H wire

private
  -- White on wire 2, the H gate passes the rotations.
  °G-R : ∀ β → °G • R β ≈ R β • °G
  °G-R true  = trans (back _ eq210) (trans (comm-abab (sym ΛH₂′-°ΛH₂′) (sym eq181)) (front _ (sym eq210)))
  °G-R false = trans (back _ eq211) (trans (comm-abab (sym eq181) (sym ΛH₂′-°ΛH₂′)) (front _ (sym eq211)))

  -- White on the wires 1 2 (in the frame), it is the H gate white on
  -- wire 2 times °CH₂₀: the merge on wire 1.
  m₁ : G • N₁.⟪ G ⟫ ≈ CH₂₀
  m₁ = S₁₂.⟪⟫-≈ eq171ᶜ (S₁₂.⟪⟫-•₂ S₁₂-ΛH₂′ (S₁₂.⟪⟫-•₃ S₁₂-X₂ S₁₂-ΛH₂′ S₁₂-X₂)) (O-L CH)

  m₂ : °G • N₂.⟪ N₁.⟪ G ⟫ ⟫ ≈ °CH₂₀
  m₂ = trans (sym (N₂.⟪⟫-• G (N₁.⟪ G ⟫))) (N₂.⟪⟫-cong m₁)

  form₁₂ : N₂.⟪ N₁.⟪ G ⟫ ⟫ ≈ °G • °CH₂₀
  form₁₂ = trans (sym left-unit) (trans (front _ (sym °ΛH₂′²)) (trans assoc (back _ m₂)))

  R-°CH₂₀ : ∀ β → R β • °CH₂₀ ≈ °CH₂₀ • R β
  R-°CH₂₀ true  = sym eq232
  R-°CH₂₀ false = sym eq233

  W₁ : ∀ β → R β • N₂.⟪ N₁.⟪ G ⟫ ⟫ ≈ N₂.⟪ N₁.⟪ G ⟫ ⟫ • R β
  W₁ β = trans (back _ form₁₂) (trans (pass₂ (sym (°G-R β)) (R-°CH₂₀ β)) (front _ (sym form₁₂)))

  -- The gadget's colourings, as conjugations.
  cTT : col (true ∷ true ∷ false ∷ true ∷ []) HG ≈ N₂.⟪ HG ⟫
  cTT = cong right-unit (back _ right-unit)

  cTF : col (true ∷ true ∷ false ∷ false ∷ []) HG ≈ N₂.⟪ N₃.⟪ HG ⟫ ⟫
  cTF = begin
    (X ↑ ↑ • (X ↑ ↑ ↑ • ε)) • HG • (X ↑ ↑ • (X ↑ ↑ ↑ • ε))
      ≈⟨ cong (back _ right-unit) (back _ (back _ right-unit)) ⟩
    (X ↑ ↑ • X ↑ ↑ ↑) • HG • (X ↑ ↑ • X ↑ ↑ ↑)
      ≈⟨ back _ (back _ X₂-X₃) ⟩
    (X ↑ ↑ • X ↑ ↑ ↑) • HG • (X ↑ ↑ ↑ • X ↑ ↑)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    N₂.⟪ N₃.⟪ HG ⟫ ⟫ ∎

  sX : S₀₁.⟪ X ⟫ ≈ X ↑
  sX = L-sem (Ex • X • Ex) (X ↑) Eq.refl

  -- X on the box wire passes HG.
  xh : X ↑ • HG ≈ HG • X ↑
  xh = S₀₁.⟪⟫-≈ eq207 (S₀₁.⟪⟫-•₂ sX refl) (S₀₁.⟪⟫-•₂ refl sX)

  C0t : ∀ β c → R β • col (true ∷ true ∷ false ∷ c ∷ []) HG ≈ col (true ∷ true ∷ false ∷ c ∷ []) HG • R β
  C0t β true  = trans (back _ cTT) (trans (unframe β (T₁₃-N₂ T₁₃HG) (sym (°G-R β))) (front _ (sym cTT)))
  C0t β false = trans (back _ cTF) (trans (unframe β (T₁₃-N₂ (T₁₃-N₃ T₁₃HG)) (W₁ β)) (front _ (sym cTF)))

C0₄ : ∀ β (z : Bits 4) → lookupℕ 0 z ≡ true → lookupℕ 2 z ≡ false → R β • col z HG ≈ col z HG • R β
C0₄ β (true ∷ true  ∷ false ∷ c ∷ []) _ _ = C0t β c
C0₄ β (true ∷ false ∷ false ∷ c ∷ []) _ _ = trans (back _ e) (trans (C0t β c) (front _ (sym e)))
  where
  e : col (true ∷ false ∷ false ∷ c ∷ []) HG ≈ col (true ∷ true ∷ false ∷ c ∷ []) HG
  e = col-flip (sF 0F) (true ∷ true ∷ false ∷ c ∷ []) xh
C0₄ β (false ∷ _)              () _
C0₄ β (true ∷ b ∷ true ∷ _)    _  ()

------------------------------------------------------------------------
-- Colourings, and the frames of (1 3) and (0 3)

private
  col-• : ∀ (s : Bits 4) u v → col s (u • v) ≈ col s u • col s v
  col-• s u v = sym (begin
    (negsB s • u • negsB s) • (negsB s • v • negsB s)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
    negsB s • u • ((negsB s • negsB s) • v • negsB s)
      ≈⟨ back _ (back _ (trans (front _ (negs² s)) left-unit)) ⟩
    negsB s • u • (v • negsB s)
      ≈⟨ back _ (sym assoc) ⟩
    negsB s • (u • v) • negsB s ∎)

  col-abab : ∀ (s : Bits 4) u v → col s (u • v • u • v) ≈ col s u • col s v • col s u • col s v
  col-abab s u v = trans (col-• s u _) (back _ (trans (col-• s v _) (back _ (col-• s u v))))

  module N₀ = Conj {4} X X²

  -- White on wire 0 is X on wire 0 around black there.
  col0 : ∀ (t : Bits 3) (w : Circuit 4) → col (false ∷ t) w ≈ N₀.⟪ col (true ∷ t) w ⟫
  col0 t w = begin
    (X • M) • w • (X • M)     ≈⟨ back _ (back _ (comm-↓↑ {n = 2} X (negsB t))) ⟩
    (X • M) • w • (M • X)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    X • (M • w • M) • X ∎
    where
    M : Circuit 4
    M = negsB t ↑

  -- (1 3) as a network, carrying a colouring.
  t13w : Word (S.Gen 4)
  t13w = [ S.gate₂ S.σ-gate S.↥ S.↥ ]ʷ • [ S.gate₂ S.σ-gate S.↥ ]ʷ • [ S.gate₂ S.σ-gate S.↥ S.↥ ]ʷ

  pl-T : ∀ (w : Circuit 4) → pl t13w w ≈ T₁₃.⟪ w ⟫
  pl-T w = back _ (back _ assoc)

  T₁₃-col : ∀ (s : Bits 4) w {w′} → T₁₃.⟪ w ⟫ ≈ w′ → T₁₃.⟪ col s w ⟫ ≈ col (swW t13w s) w′
  T₁₃-col s w e = trans (sym (pl-T _)) (trans (pl-col t13w s w) (mid _ _ (trans (pl-T w) e)))

  -- (0 3) as Canon38's network.
  pl-T03 : ∀ (w : Circuit 4) → pl t03 w ≈ T₀₃.⟪ w ⟫
  pl-T03 w = cong n03 (back _ (trans (by-passoc ((((□ • □) • □) • □) • □) (□ • (□ • (□ • (□ • □)))) Eq.refl) n03))
    where
    n03 : Ex • (Ex ↑ • (Ex ↑ ↑ • (Ex ↑ • Ex))) ≈ t₀₃
    n03 = back _ (trans (by-passoc (□ • (□ • (□ • □))) ((□ • □ • □) • □) Eq.refl) (front _ braid↑))

  -- (1 3) after (0 3) is (0 1) on the rotations.
  T₁₃T₀₃ : ∀ β → T₁₃.⟪ T₀₃.⟪ R β ⟫ ⟫ ≈ Ex • R β • Ex
  T₁₃T₀₃ β = trans (T₁₃.⟪⟫-cong (T₀₃-nest′ (R β))) (trans (T₁₃.⟪⟫-⟪⟫ _) (S₀₁.⟪⟫-cong (T₁₃R β)))

------------------------------------------------------------------------
-- C1: the target on the H gate's box wire

private
  a′ cz′ : Circuit 4
  a′  = P₁₃ HC
  cz′ = P₁₃ (Ex • CZ • Ex)

  -- (0 3)'s rotation: the CH from wire 1 onto wire 3 and the box on wire 1.
  Rf : Bool → Circuit 4
  Rf true  = a′ • box₃′ • a′ • box₃′
  Rf false = box₃′ • a′ • box₃′ • a′

  T₀₃-R : ∀ β → T₀₃.⟪ R β ⟫ ≈ Rf β
  T₀₃-R true  = T₀₃.⟪⟫-•₄ (T₀₃-L CH) T₀₃-box₃′ (T₀₃-L CH) T₀₃-box₃′
  T₀₃-R false = T₀₃.⟪⟫-•₄ T₀₃-box₃′ (T₀₃-L CH) T₀₃-box₃′ (T₀₃-L CH)

  -- Between P ⊗ P on the wires 0 3 the CH onto wire 3 is the CZ.
  e1 : PP₀₃ • a′ • PP₀₃ ≈ cz′
  e1 = begin
    PP₀₃ • P₁₃ HC • PP₀₃
      ≈⟨ cong (sym (M₃-O PP)) (cong (sym (M₃-U HC)) (sym (M₃-O PP))) ⟩
    M₃ (O₀ PP) • M₃ (U₀ HC) • M₃ (O₀ PP)
      ≈⟨ sym (S₂₃.⟪⟫-•₃ refl refl refl) ⟩
    M₃ (O₀ PP • U₀ HC • O₀ PP)
      ≈⟨ M₃-sem (O₀ PP • U₀ HC • O₀ PP) (U₀ (Ex • CZ • Ex)) Eq.refl ⟩
    M₃ (U₀ (Ex • CZ • Ex))
      ≈⟨ M₃-U (Ex • CZ • Ex) ⟩
    cz′ ∎

  module PPc = Conj {4} PP₀₃ PP₀₃²
  module PPl = Conj {4} PP₀₁ PP₀₁²

  PP-cz′ : PPc.⟪ cz′ ⟫ ≈ a′
  PP-cz′ = trans (PPc.⟪⟫-cong (sym e1)) (PPc.⟪⟫-⟪⟫ a′)

  -- (160) and (163) under (0 3): the box on wire 3 passes the CZ and
  -- the CH from wire 1.
  cz-β₃ : cz′ • box₃‴ ≈ box₃‴ • cz′
  cz-β₃ = T₀₃.⟪⟫-≈ eq160 (T₀₃.⟪⟫-•₂ (T₀₃-L CZ) T₀₃-box₃) (T₀₃.⟪⟫-•₂ T₀₃-box₃ (T₀₃-L CZ))

  ch-β₃ : a′ • box₃‴ ≈ box₃‴ • a′
  ch-β₃ = T₀₃.⟪⟫-≈ eq163 (T₀₃.⟪⟫-•₂ (T₀₃-L CH) T₀₃-box₃) (T₀₃.⟪⟫-•₂ T₀₃-box₃ (T₀₃-L CH))

  G-a′ : G • a′ ≈ a′ • G
  G-a′ = PPc.⟪⟫-≈ (sym cz-β₃) (PPc.⟪⟫-•₂ (sym ΛH₂′-PP) PP-cz′) (PPc.⟪⟫-•₂ PP-cz′ (sym ΛH₂′-PP))

  -- H on wire 3: ΛH₀₁ passes H on its box wire, which is Z between P ⊗ P.
  HG-H₁ : HG • H ↑ ≈ H ↑ • HG
  HG-H₁ = sym (PPl.⟪⟫-≈ z1 (PPl.⟪⟫-•₂ pZ (sym ΛH₀₁-PP)) (PPl.⟪⟫-•₂ (sym ΛH₀₁-PP) pZ))
    where
    sZ : S₀₁.⟪ Z ⟫ ≈ Z ↑
    sZ = L-sem (Ex • Z • Ex) (Z ↑) Eq.refl
    z1 : Z ↑ • box₃′ ≈ box₃′ • Z ↑
    z1 = S₀₁.⟪⟫-≈ eq154 (S₀₁.⟪⟫-•₂ sZ refl) (S₀₁.⟪⟫-•₂ refl sZ)
    pZ : PPl.⟪ Z ↑ ⟫ ≈ H ↑
    pZ = L-sem (PP • Z ↑ • PP) (H ↑) Eq.refl

  tH : T₁₃.⟪ H ↑ ⟫ ≈ H ↑ ↑ ↑
  tH = U₃-sem ((Ex ↑ • Ex • Ex ↑) • H • (Ex ↑ • Ex • Ex ↑)) (H ↑ ↑) Eq.refl

  G-H₃ : G • H ↑ ↑ ↑ ≈ H ↑ ↑ ↑ • G
  G-H₃ = T₁₃.⟪⟫-≈ HG-H₁ (T₁₃.⟪⟫-•₂ T₁₃HG tH) (T₁₃.⟪⟫-•₂ tH T₁₃HG)

  -- The colours of the CH: only its control's counts.
  X₀-a′ : X • a′ ≈ a′ • X
  X₀-a′ = comm-↓↑ {n = 2} X (Ex • HC ↑ • Ex)

  X₂-a′ : X ↑ ↑ • a′ ≈ a′ • X ↑ ↑
  X₂-a′ = U₃-sem (X ↑ • O₀ HC) (O₀ HC • X ↑) Eq.refl

  a′° : col (true ∷ false ∷ true ∷ true ∷ []) a′ ≈ a′ • H ↑ ↑ ↑
  a′° = U₃-sem ((X • ε) • O₀ HC • (X • ε)) (O₀ HC • H ↑ ↑) Eq.refl

  colA : ∀ a c → col (a ∷ c ∷ false ∷ true ∷ []) a′ ≈ col (true ∷ c ∷ true ∷ true ∷ []) a′
  colA true  c = col-flip (sF (sF 0F)) (true ∷ c ∷ true ∷ true ∷ []) X₂-a′
  colA false c = trans (col-flip (sF (sF 0F)) (false ∷ c ∷ true ∷ true ∷ []) X₂-a′)
                       (col-flip 0F (true ∷ c ∷ true ∷ true ∷ []) X₀-a′)

  G-A : ∀ c → G • col (true ∷ c ∷ true ∷ true ∷ []) a′ ≈ col (true ∷ c ∷ true ∷ true ∷ []) a′ • G
  G-A true  = trans (back _ (trans left-unit right-unit))
                    (trans G-a′ (front _ (sym (trans left-unit right-unit))))
  G-A false = trans (back _ a′°) (trans (pass₂ G-a′ G-H₃) (front _ (sym a′°)))

  -- The colours of the box on wire 1: wire 1 is its box wire.
  X₁-B′ : X ↑ • box₃′ ≈ box₃′ • X ↑
  X₁-B′ = S₀₁.⟪⟫-≈ eq156 (S₀₁.⟪⟫-•₂ sX refl) (S₀₁.⟪⟫-•₂ refl sX)

  colB : ∀ a c → col (a ∷ c ∷ false ∷ true ∷ []) box₃′ ≈ col (a ∷ true ∷ false ∷ true ∷ []) box₃′
  colB a true  = refl
  colB a false = col-flip (sF 0F) (a ∷ true ∷ false ∷ true ∷ []) X₁-B′

  °B : Circuit 4
  °B = S₀₁.⟪ °box₃ ⟫

  nB : °B ≈ N₂.⟪ box₃′ ⟫
  nB = S₀₁.⟪⟫-•₃ (P₂₃-S₀₁ X) refl (P₂₃-S₀₁ X)

  °B² : °B • °B ≈ ε
  °B² = S₀₁.⟪⟫-invol (N₂.⟪⟫-invol eq166)

  sX′ : S₀₁.⟪ X ↑ ⟫ ≈ X
  sX′ = L-sem (Ex • X ↑ • Ex) X Eq.refl

  -- The merge (170) on wire 1, negated on wire 2, under the lower swap.
  m0 : box₃ • N₁.⟪ box₃ ⟫ ≈ P₂₃ CZ
  m0 = S₁₂.⟪⟫-≈ eq170 (S₁₂.⟪⟫-•₂ eq157 (S₁₂.⟪⟫-•₃ S₁₂-X₂ eq157 S₁₂-X₂)) (S₁₂.⟪⟫-⟪⟫ (P₂₃ CZ))

  m1 : °B • S₀₁.⟪ N₂.⟪ N₁.⟪ box₃ ⟫ ⟫ ⟫ ≈ P₂₃ CZ°
  m1 = S₀₁.⟪⟫-≈ (N₂.⟪⟫-≈ m0 (N₂.⟪⟫-•₂ refl refl) refl) (S₀₁.⟪⟫-•₂ refl refl) (P₂₃-S₀₁ CZ°)

  cF : col (false ∷ true ∷ false ∷ true ∷ []) box₃′ ≈ S₀₁.⟪ N₂.⟪ N₁.⟪ box₃ ⟫ ⟫ ⟫
  cF = begin
    (X • (X ↑ ↑ • ε)) • box₃′ • (X • (X ↑ ↑ • ε))
      ≈⟨ cong (back _ right-unit) (back _ (back _ right-unit)) ⟩
    (X • X ↑ ↑) • box₃′ • (X • X ↑ ↑)
      ≈⟨ front _ (comm-↓↑ {n = 2} X (X ↑)) ⟩
    (X ↑ ↑ • X) • box₃′ • (X • X ↑ ↑)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    X ↑ ↑ • (X • box₃′ • X) • X ↑ ↑
      ≈⟨ sym (S₀₁.⟪⟫-•₃ (P₂₃-S₀₁ X) (S₀₁.⟪⟫-•₃ sX′ refl sX′) (P₂₃-S₀₁ X)) ⟩
    S₀₁.⟪ N₂.⟪ N₁.⟪ box₃ ⟫ ⟫ ⟫ ∎

  G-B : ∀ a → G • col (a ∷ true ∷ false ∷ true ∷ []) box₃′ ≈ col (a ∷ true ∷ false ∷ true ∷ []) box₃′ • G
  G-B true  = trans (back _ cT) (trans (sym eq181ᵇ) (front _ (sym cT)))
    where
    cT : col (true ∷ true ∷ false ∷ true ∷ []) box₃′ ≈ °B
    cT = trans (cong right-unit (back _ right-unit)) (sym nB)
  G-B false = trans (back _ cT) (trans (pass₂ (sym eq181ᵇ) (sym CZ°₂₃-ΛH₂′)) (front _ (sym cT)))
    where
    cT : col (false ∷ true ∷ false ∷ true ∷ []) box₃′ ≈ °B • P₂₃ CZ°
    cT = trans cF (trans (sym left-unit) (trans (front _ (sym °B²)) (trans assoc (back _ m1))))

  gA : ∀ a c → G • col (a ∷ c ∷ false ∷ true ∷ []) a′ ≈ col (a ∷ c ∷ false ∷ true ∷ []) a′ • G
  gA a c = trans (back _ (colA a c)) (trans (G-A c) (front _ (sym (colA a c))))

  gB : ∀ a c → G • col (a ∷ c ∷ false ∷ true ∷ []) box₃′ ≈ col (a ∷ c ∷ false ∷ true ∷ []) box₃′ • G
  gB a c = trans (back _ (colB a c)) (trans (G-B a) (front _ (sym (colB a c))))

  inFrame₁ : ∀ β a c → G • col (a ∷ c ∷ false ∷ true ∷ []) (Rf β) ≈ col (a ∷ c ∷ false ∷ true ∷ []) (Rf β) • G
  inFrame₁ true  a c =
    trans (back _ (col-abab (a ∷ c ∷ false ∷ true ∷ []) a′ box₃′))
          (trans (comm-abab (gA a c) (gB a c)) (front _ (sym (col-abab (a ∷ c ∷ false ∷ true ∷ []) a′ box₃′))))
  inFrame₁ false a c =
    trans (back _ (col-abab (a ∷ c ∷ false ∷ true ∷ []) box₃′ a′))
          (trans (comm-abab (gB a c) (gA a c)) (front _ (sym (col-abab (a ∷ c ∷ false ∷ true ∷ []) box₃′ a′))))

C1₄ : ∀ β (z : Bits 4) → lookupℕ 1 z ≡ true → lookupℕ 2 z ≡ false →
      HG • col z (Ex • R β • Ex) ≈ col z (Ex • R β • Ex) • HG
C1₄ β (a ∷ true ∷ false ∷ c ∷ []) _ _ =
  T₁₃.⟪⟫-≈ (inFrame₁ β a c) (T₁₃.⟪⟫-•₂ T₁₃-ΛH₂′ tW) (T₁₃.⟪⟫-•₂ tW T₁₃-ΛH₂′)
  where
  tW : T₁₃.⟪ col (a ∷ c ∷ false ∷ true ∷ []) (Rf β) ⟫ ≈ col (a ∷ true ∷ false ∷ c ∷ []) (Ex • R β • Ex)
  tW = T₁₃-col (a ∷ c ∷ false ∷ true ∷ []) (Rf β) (trans (T₁₃.⟪⟫-cong (sym (T₀₃-R β))) (T₁₃T₀₃ β))
C1₄ β (_ ∷ false ∷ _)       () _
C1₄ β (_ ∷ true ∷ true ∷ _) _  ()

------------------------------------------------------------------------
-- C2: the target on a control of the H gate

private
  K : Circuit 4
  K = S₁₂.⟪ box₃′ ⟫

  -- In the frame the rotation is the one on wire 1: the CH from wire 2
  -- onto wire 1 and the box on wire 2.
  Rg : Bool → Circuit 4
  Rg true  = U CH • K • U CH • K
  Rg false = K • U CH • K • U CH

  uc : S₀₁.⟪ S₁₂.⟪ CH ⟫ ⟫ ≈ U CH
  uc = trans (S₀₁.⟪⟫-cong (O-L CH)) (S₀₁.⟪⟫-⟪⟫ (U CH))

  sK : S₀₁.⟪ K ⟫ ≈ K
  sK = trans (sym (braid-conj box₃)) (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-cong eq157))

  rc : ∀ β → Ex • R β • Ex ≈ Rg β
  rc true  = trans (S₀₁.⟪⟫-cong (sym (S₁₂.⟪⟫-fix (s12₄ true))))
                   (trans (S₀₁.⟪⟫-cong (S₁₂.⟪⟫-•₄ refl refl refl refl)) (S₀₁.⟪⟫-•₄ uc sK uc sK))
  rc false = trans (S₀₁.⟪⟫-cong (sym (S₁₂.⟪⟫-fix (s12₄ false))))
                   (trans (S₀₁.⟪⟫-cong (S₁₂.⟪⟫-•₄ refl refl refl refl)) (S₀₁.⟪⟫-•₄ sK uc sK uc))

  tR : ∀ β → T₁₃.⟪ Ex • R β • Ex ⟫ ≈ pl t03 (R β)
  tR β = trans (T₁₃.⟪⟫-cong (S₀₁.⟪⟫-cong (sym (T₁₃R β))))
               (trans (sym (T₀₃-nest′ (R β))) (sym (pl-T03 (R β))))

  -- The H gate in the frame, white on the wires 1 2.
  Y : Circuit 4
  Y = N₂.⟪ N₁.⟪ G ⟫ ⟫

  tX : T₁₃.⟪ X ↑ ⟫ ≈ X ↑ ↑ ↑
  tX = U₃-sem ((Ex ↑ • Ex • Ex ↑) • X • (Ex ↑ • Ex • Ex ↑)) (X ↑ ↑) Eq.refl

  X₃-G : X ↑ ↑ ↑ • G ≈ G • X ↑ ↑ ↑
  X₃-G = T₁₃.⟪⟫-≈ xh (T₁₃.⟪⟫-•₂ tX T₁₃HG) (T₁₃.⟪⟫-•₂ T₁₃HG tX)

  cY : col (true ∷ false ∷ false ∷ true ∷ []) G ≈ Y
  cY = begin
    (X ↑ • (X ↑ ↑ • ε)) • G • (X ↑ • (X ↑ ↑ • ε))
      ≈⟨ cong (back _ right-unit) (back _ (back _ right-unit)) ⟩
    (X ↑ • X ↑ ↑) • G • (X ↑ • X ↑ ↑)
      ≈⟨ front _ (lemma-cong↑ (X • X ↑) (X ↑ • X) (comm-↓↑ {n = 1} X X)) ⟩
    (X ↑ ↑ • X ↑) • G • (X ↑ • X ↑ ↑)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    Y ∎

  Ya : Bool → Circuit 4
  Ya true  = Y
  Ya false = N₀.⟪ Y ⟫

  cY1 : ∀ a → col (a ∷ false ∷ false ∷ true ∷ []) G ≈ Ya a
  cY1 true  = cY
  cY1 false = trans (col0 (false ∷ false ∷ true ∷ []) G) (N₀.⟪⟫-cong cY)

  cYa : ∀ a b → col (a ∷ false ∷ false ∷ b ∷ []) G ≈ Ya a
  cYa a true  = cY1 a
  cYa a false = trans (col-flip (sF (sF (sF 0F))) (a ∷ false ∷ false ∷ true ∷ []) X₃-G) (cY1 a)

  -- The CH passes Y: (134), and (164) negated, under (0 3), between P ⊗ P.
  t13X₂ : T₁₃.⟪ X ↑ ↑ ⟫ ≈ X ↑ ↑
  t13X₂ = T₁₃-via S₂₃-X₂ S₁₂-X₃ S₂₃-X₃

  t°b : T₀₃.⟪ °box₃ ⟫ ≈ °box₃‴
  t°b = T₀₃.⟪⟫-•₃ tX₂ T₀₃-box₃ tX₂
    where
    tX₂ : T₀₃.⟪ X ↑ ↑ ⟫ ≈ X ↑ ↑
    tX₂ = T₀₃-via (P₂₃-S₀₁ X) t13X₂ (P₂₃-S₀₁ X)

  tU : T₀₃.⟪ U CH ⟫ ≈ U CH
  tU = T₀₃-via {w₁ = O CH} refl (T₁₃-O CH) (S₀₁.⟪⟫-⟪⟫ (U CH))

  u-°β₃ : U CH • °box₃‴ ≈ °box₃‴ • U CH
  u-°β₃ = T₀₃.⟪⟫-≈ e164′ (T₀₃.⟪⟫-•₂ tU t°b) (T₀₃.⟪⟫-•₂ t°b tU)
    where
    nU : N₂.⟪ U °CH ⟫ ≈ U CH
    nU = U-sem (X ↑ • °CH • X ↑) CH Eq.refl
    e164′ : U CH • °box₃ ≈ °box₃ • U CH
    e164′ = N₂.⟪⟫-≈ eq164 (N₂.⟪⟫-•₂ nU refl) (N₂.⟪⟫-•₂ refl nU)

  u-°G : U CH • °G ≈ °G • U CH
  u-°G = trans (back _ °ΛH₂′-PP) (trans (pass₂ uPP (pass₂ u-°β₃ uPP)) (front _ (sym °ΛH₂′-PP)))
    where
    uPP : U CH • PP₀₃ ≈ PP₀₃ • U CH
    uPP = sym (P₀₃-U PP CH)

  UCH-Y : U CH • Y ≈ Y • U CH
  UCH-Y = trans (back _ form₁₂) (trans (pass₂ u-°G eq134) (front _ (sym form₁₂)))

  -- The box on wire 2 passes Y: (181) under the middle swap, and X on its
  -- box wire.
  K-Y : K • Y ≈ Y • K
  K-Y = N₂.⟪⟫-≈ kN1 (N₂.⟪⟫-•₂ nK refl) (N₂.⟪⟫-•₂ refl nK)
    where
    sG : S₁₂.⟪ °G ⟫ ≈ N₁.⟪ G ⟫
    sG = S₁₂.⟪⟫-•₃ S₁₂-X₂ S₁₂-ΛH₂′ S₁₂-X₂
    kN1 : K • N₁.⟪ G ⟫ ≈ N₁.⟪ G ⟫ • K
    kN1 = S₁₂.⟪⟫-≈ eq181 (S₁₂.⟪⟫-•₂ refl sG) (S₁₂.⟪⟫-•₂ sG refl)
    nK : N₂.⟪ K ⟫ ≈ K
    nK = N₂.⟪⟫-fix (S₁₂.⟪⟫-≈ X₁-B′ (S₁₂.⟪⟫-•₂ S₁₂-X₁ refl) (S₁₂.⟪⟫-•₂ refl S₁₂-X₁))

  -- White on wire 0: the box on wire 2 becomes itself times the CZ of the
  -- wires 1 3 (the merge (170) under (0 2)), which passes Y.
  pcz : P₁₃ CZ ≈ cz′
  pcz = U₃-sem (O₀ CZ) (O₀ (Ex • CZ • Ex)) Eq.refl

  mK : K • N₀.⟪ K ⟫ ≈ cz′
  mK = trans (S₀₁.⟪⟫-≈ stepb (S₀₁.⟪⟫-•₂ sK (S₀₁.⟪⟫-•₃ sX′ sK sX′)) (S₀₁.⟪⟫-⟪⟫ (P₁₃ CZ))) pcz
    where
    stepa : box₃′ • N₂.⟪ box₃′ ⟫ ≈ P₀₃ CZ
    stepa = S₀₁.⟪⟫-≈ eq170 (S₀₁.⟪⟫-•₂ refl nB) refl
    stepb : K • N₁.⟪ K ⟫ ≈ P₀₃ CZ
    stepb = S₁₂.⟪⟫-≈ stepa (S₁₂.⟪⟫-•₂ refl (S₁₂.⟪⟫-•₃ S₁₂-X₂ refl S₁₂-X₂)) (S₁₂-P₀₃ CZ)

  K² : K • K ≈ ε
  K² = S₁₂.⟪⟫-invol box₃′²

  N₀K : N₀.⟪ K ⟫ ≈ K • cz′
  N₀K = trans (sym left-unit) (trans (front _ (sym K²)) (trans assoc (back _ mK)))

  cz-Y : cz′ • Y ≈ Y • cz′
  cz-Y = trans (back _ form₁₂) (trans (pass₂ cz-°G cz-°CH) (front _ (sym form₁₂)))
    where
    nA : N₂.⟪ a′ ⟫ ≈ a′
    nA = N₂.⟪⟫-fix X₂-a′
    a°β₃ : a′ • °box₃‴ ≈ °box₃‴ • a′
    a°β₃ = N₂.⟪⟫-≈ ch-β₃ (N₂.⟪⟫-•₂ nA refl) (N₂.⟪⟫-•₂ refl nA)
    cz-°G : cz′ • °G ≈ °G • cz′
    cz-°G = PPc.⟪⟫-≈ a°β₃ (PPc.⟪⟫-•₂ e1 (sym °ΛH₂′-PP)) (PPc.⟪⟫-•₂ (sym °ΛH₂′-PP) e1)
    pX : cz′ • X ↑ ↑ ≈ X ↑ ↑ • cz′
    pX = U₃-sem (O₀ (Ex • CZ • Ex) • X ↑) (X ↑ • O₀ (Ex • CZ • Ex)) Eq.refl
    cz-°CH : cz′ • °CH₂₀ ≈ °CH₂₀ • cz′
    cz-°CH = pass₂ pX (pass₂ (P₁₃-O (Ex • CZ • Ex) CH) pX)

  K-N₀Y : K • N₀.⟪ Y ⟫ ≈ N₀.⟪ Y ⟫ • K
  K-N₀Y = N₀.⟪⟫-≈ e (N₀.⟪⟫-•₂ (N₀.⟪⟫-⟪⟫ K) refl) (N₀.⟪⟫-•₂ refl (N₀.⟪⟫-⟪⟫ K))
    where
    e : N₀.⟪ K ⟫ • Y ≈ Y • N₀.⟪ K ⟫
    e = trans (front _ N₀K) (trans (passL K-Y cz-Y) (back _ (sym N₀K)))

  UCH-N₀Y : U CH • N₀.⟪ Y ⟫ ≈ N₀.⟪ Y ⟫ • U CH
  UCH-N₀Y = N₀.⟪⟫-≈ UCH-Y (N₀.⟪⟫-•₂ nU0 refl) (N₀.⟪⟫-•₂ refl nU0)
    where
    nU0 : N₀.⟪ U CH ⟫ ≈ U CH
    nU0 = N₀.⟪⟫-fix (comm-↓↑ {n = 2} X (CH {0} ↓ᵏ 1))

  uY : ∀ a → U CH • Ya a ≈ Ya a • U CH
  uY true  = UCH-Y
  uY false = UCH-N₀Y

  kY : ∀ a → K • Ya a ≈ Ya a • K
  kY true  = K-Y
  kY false = K-N₀Y

  rg : ∀ β a → Rg β • Ya a ≈ Ya a • Rg β
  rg true  a = sym (comm-abab (sym (uY a)) (sym (kY a)))
  rg false a = sym (comm-abab (sym (kY a)) (sym (uY a)))

  inFrame₂ : ∀ β a b → (Ex • R β • Ex) • col (a ∷ false ∷ false ∷ b ∷ []) G
                     ≈ col (a ∷ false ∷ false ∷ b ∷ []) G • (Ex • R β • Ex)
  inFrame₂ β a b = trans (cong (rc β) (cYa a b)) (trans (rg β a) (sym (cong (cYa a b) (rc β))))

C2₄ : ∀ β (z : Bits 4) → lookupℕ 2 z ≡ false → lookupℕ 3 z ≡ false →
      pl t03 (R β) • col z HG ≈ col z HG • pl t03 (R β)
C2₄ β (a ∷ b ∷ false ∷ false ∷ []) _ _ =
  T₁₃.⟪⟫-≈ (inFrame₂ β a b) (T₁₃.⟪⟫-•₂ (tR β) tC) (T₁₃.⟪⟫-•₂ tC (tR β))
  where
  tC : T₁₃.⟪ col (a ∷ false ∷ false ∷ b ∷ []) G ⟫ ≈ col (a ∷ b ∷ false ∷ false ∷ []) HG
  tC = T₁₃-col (a ∷ false ∷ false ∷ b ∷ []) G T₁₃-ΛH₂′
C2₄ β (_ ∷ _ ∷ true ∷ _)         () _
C2₄ β (_ ∷ _ ∷ false ∷ true ∷ _) _  ()

------------------------------------------------------------------------
-- The rotation placed anywhere against the gadget

hgrot₁ : HGRot 1
hgrot₁ = HGF.hgrot {0} rig₄ HG HG-rigid₄ refl C0₄ C1₄ C2₄
