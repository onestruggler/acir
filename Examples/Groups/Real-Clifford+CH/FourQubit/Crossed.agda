------------------------------------------------------------------------
-- Presentations of groups
--
-- A triply controlled rotation against a doubly controlled one, crossed
-- (Clément, Lemma D.5, Equations (216)–(218))
--
-- K is the triply controlled ZX on wire 1 from the wires 0, 3 and,
-- negatively, 2; M = CCZX is the doubly controlled ZX on wire 0 from the
-- wires 1 and 2.  They commute because of the colours on wire 2, but the
-- target of each is a control of the other, and no decomposition of one
-- passes the other factor by factor.  As for (139) on three wires, M is
-- taken in its other form p q p q, (14), with p the CH from wire 2 and q
-- the lower CZ: then p passes K, and q exchanges K and its inverse
-- (`pass-pqpq`).  Three forms of K are used.
--
--   °G′ c′ °G′ c′, from (212): p passes the CZ c′ of wires 1 3, and the
--     white H gate °G′ = H(1, 3; 0, °2) — between its P ⊗ P this is
--     (164), an H on a control of a box of the other colour.
--   a′ °B a′ °B, the definition: q turns a′ into its conjugate by Z on
--     wire 1, and both pass the box; so q K q is K between Z on wire 1.
--   G₃ °c₃ G₃ °c₃, (212) for the other control, with the box wire of the
--     H gate on wire 2 where X passes it, (207): this form passes the Z
--     on wire 1 controlled negatively by wire 3 — the H gate as in (190)
--     — which is c′ times Z on wire 1.  So K between Z on wire 1 is K
--     between c′, its inverse.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Crossed
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax ; Z² ; CZ² ; S-X↓ ; S-Z↑)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃ ; CZ₃₀ ; CZ₃₀-P)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq160)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃ ; eq164)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃
  using (N₂-box₃′ ; °CZ₂₀-ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (PP₁₃ ; box₃‴ ; °box₃‴ ; S₀₁-°box₃‴ ; S₀₁-°ΛH₂′-PP)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (T₀₃-box₃ ; eq207)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₂ ; eq117 ; eq118 ; eq119 ; eq120 ; °CZ₂₀-O)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The gates

-- The triply controlled ZX and XZ on wire 1, from the wires 0, 3 and,
-- negatively, 2.
K K′ : Circuit (₄₊ n)
K  = S₀₁.⟪ N₂.⟪ ZX₃ ⟫ ⟫
K′ = S₀₁.⟪ N₂.⟪ XZ₃ ⟫ ⟫

module _ {n : ℕ} where
  private
    Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    p q z₁ a′ °B °G′ c′ ζ G₂ G₃ °c₃ : Circuit (₄₊ n)
    p   = CH₂₀
    q   = CZ ↓
    z₁  = Z ↑
    a′  = HC ↓
    °B  = °box₃
    °G′ = S₀₁.⟪ °ΛH₂′ ⟫
    c′  = P₁₃ CZ
    ζ   = P₁₃ °CZ
    G₂  = S₁₂.⟪ ΛH₀₁ ⟫
    G₃  = S₀₁.⟪ G₂ ⟫
    °c₃ = U °CZ

    N₂-L : (u : Circuit 2) → N₂.⟪ L u ⟫ ≈ L u
    N₂-L u = N₂.⟪⟫-fix (sym (L-comm u X))

    N₂-c : N₂.⟪ CZ₃₀ ⟫ ≈ CZ₃₀
    N₂-c = trans (N₂.⟪⟫-cong CZ₃₀-P)
          (trans (N₂.⟪⟫-fix (sym (P₀₃-U CZ (X ↑)))) (sym CZ₃₀-P))

    S₀₁-c : S₀₁.⟪ CZ₃₀ ⟫ ≈ c′
    S₀₁-c = trans (S₀₁.⟪⟫-cong CZ₃₀-P) (S₀₁.⟪⟫-⟪⟫ c′)

    c′² : c′ • c′ ≈ ε
    c′² = conj-invol Ex₁² (lemma-cong↑ (U (CZ • CZ)) ε (U-sem (CZ • CZ) ε Eq.refl))

    z₁² : z₁ • z₁ ≈ ε
    z₁² = lemma-cong↑ (Z • Z) ε Z²

    q² : q • q ≈ ε
    q² = CZ²

    ------------------------------------------------------------------
    -- The three forms of K

    -- The definition.
    K-form₁ : K ≈ a′ • °B • a′ • °B
    K-form₁ = trans (S₀₁.⟪⟫-cong (N₂.⟪⟫-•₄ (N₂-L CH) N₂-box₃′ (N₂-L CH) N₂-box₃′))
                    (S₀₁.⟪⟫-•₄ refl (S₀₁.⟪⟫-⟪⟫ °box₃) refl (S₀₁.⟪⟫-⟪⟫ °box₃))

    -- (212) and (213).
    K-form₂ : K ≈ °G′ • c′ • °G′ • c′
    K-form₂ = trans (S₀₁.⟪⟫-cong (trans (N₂.⟪⟫-cong eq212) (N₂.⟪⟫-•₄ refl N₂-c refl N₂-c)))
                    (S₀₁.⟪⟫-•₄ refl S₀₁-c refl S₀₁-c)

    K′-form₂ : K′ ≈ c′ • °G′ • c′ • °G′
    K′-form₂ = trans (S₀₁.⟪⟫-cong (trans (N₂.⟪⟫-cong eq213) (N₂.⟪⟫-•₄ N₂-c refl N₂-c refl)))
                     (S₀₁.⟪⟫-•₄ S₀₁-c refl S₀₁-c refl)

    -- (212) for the control on wire 2: the box wire of the H gate on
    -- wire 2, where X passes it.
    X₂-G₂ : X ↑ ↑ • G₂ ≈ G₂ • X ↑ ↑
    X₂-G₂ = S₁₂.⟪⟫-≈
      (S₀₁.⟪⟫-≈ eq207 (S₀₁.⟪⟫-•₂ S-X↓ refl) (S₀₁.⟪⟫-•₂ refl S-X↓))
      (S₁₂.⟪⟫-•₂ S₁₂-X₁ refl) (S₁₂.⟪⟫-•₂ refl S₁₂-X₁)

    S₂₃-c : S₂₃.⟪ CZ₃₀ ⟫ ≈ CZ₂₀
    S₂₃-c = trans (S₂₃.⟪⟫-cong CZ₃₀-P) (S₂₃-P₀₃ CZ)

    ZX₃-form₃ : ZX₃ ≈ G₂ • CZ₂₀ • G₂ • CZ₂₀
    ZX₃-form₃ = trans (sym S₂₃-ZX₃) (trans (S₂₃.⟪⟫-cong eq212)
      (S₂₃.⟪⟫-•₄ S-G S₂₃-c S-G S₂₃-c))
      where
      S-G : S₂₃.⟪ ΛH₂′ ⟫ ≈ G₂
      S-G = S₂₃.⟪⟫-⟪⟫ G₂

    S₀₁-°b : S₀₁.⟪ °CZ₂₀ ⟫ ≈ °c₃
    S₀₁-°b = trans (S₀₁.⟪⟫-cong °CZ₂₀-O) (S₀₁.⟪⟫-⟪⟫ °c₃)

    K-form₃ : K ≈ G₃ • °c₃ • G₃ • °c₃
    K-form₃ = trans (S₀₁.⟪⟫-cong (trans (N₂.⟪⟫-cong ZX₃-form₃)
                                   (N₂.⟪⟫-•₄ N-G refl N-G refl)))
                    (S₀₁.⟪⟫-•₄ refl S₀₁-°b refl S₀₁-°b)
      where
      N-G : N₂.⟪ G₂ ⟫ ≈ G₂
      N-G = N₂.⟪⟫-fix X₂-G₂

    ------------------------------------------------------------------
    -- p passes K and its inverse

    -- (164) with the colours exchanged …
    e164° : U CH • °box₃ ≈ °box₃ • U CH
    e164° = N₂.⟪⟫-≈ eq164 (N₂.⟪⟫-•₂ N-t refl) (N₂.⟪⟫-•₂ refl N-t)
      where
      N-t : N₂.⟪ U °CH ⟫ ≈ U CH
      N-t = N₂.⟪⟫-⟪⟫ (U CH)

    -- … and under the cycle 1 → 0 → 3 → 1: the CH from wire 2 onto
    -- wire 0 passes the white box on wire 3.
    T₀₃-U : (u : Circuit 2) → T₀₃.⟪ U u ⟫ ≈ U u
    T₀₃-U u = trans (T₀₃-nest (U u)) (trans (S₀₁.⟪⟫-cong (T₁₃-O u)) (S₀₁.⟪⟫-⟪⟫ (U u)))

    T₀₃-X₂ : T₀₃.⟪ X ↑ ↑ ⟫ ≈ X ↑ ↑
    T₀₃-X₂ = trans (T₀₃-nest (X ↑ ↑))
            (trans (S₀₁.⟪⟫-cong (trans (T₁₃.⟪⟫-cong (P₂₃-S₀₁ X)) T₁₃-X₂)) (P₂₃-S₀₁ X))

    T₀₃-°box₃ : T₀₃.⟪ °box₃ ⟫ ≈ °box₃‴
    T₀₃-°box₃ = T₀₃.⟪⟫-•₃ T₀₃-X₂ T₀₃-box₃ T₀₃-X₂

    p-°β : p • °box₃‴ ≈ °box₃‴ • p
    p-°β = S₀₁.⟪⟫-≈ (T₀₃.⟪⟫-≈ e164° (T₀₃.⟪⟫-•₂ (T₀₃-U CH) T₀₃-°box₃)
                                     (T₀₃.⟪⟫-•₂ T₀₃-°box₃ (T₀₃-U CH)))
      (S₀₁.⟪⟫-•₂ refl S₀₁-°box₃‴) (S₀₁.⟪⟫-•₂ S₀₁-°box₃‴ refl)

    p-PP : p • PP₁₃ ≈ PP₁₃ • p
    p-PP = sym (P₁₃-O PP CH)

    p-°G′ : p • °G′ ≈ °G′ • p
    p-°G′ = begin
      p • °G′                        ≈⟨ back _ S₀₁-°ΛH₂′-PP ⟩
      p • (PP₁₃ • °box₃‴ • PP₁₃)     ≈⟨ comm-• p-PP (comm-• p-°β p-PP) ⟩
      (PP₁₃ • °box₃‴ • PP₁₃) • p     ≈⟨ front _ (sym S₀₁-°ΛH₂′-PP) ⟩
      °G′ • p ∎

    p-c′ : p • c′ ≈ c′ • p
    p-c′ = sym (P₁₃-O CZ CH)

    p-K : p • K ≈ K • p
    p-K = begin
      p • K                         ≈⟨ back _ K-form₂ ⟩
      p • (°G′ • c′ • °G′ • c′)     ≈⟨ comm-abab p-°G′ p-c′ ⟩
      (°G′ • c′ • °G′ • c′) • p     ≈⟨ front _ (sym K-form₂) ⟩
      K • p ∎

    p-K′ : p • K′ ≈ K′ • p
    p-K′ = begin
      p • K′                        ≈⟨ back _ K′-form₂ ⟩
      p • (c′ • °G′ • c′ • °G′)     ≈⟨ comm-abab p-c′ p-°G′ ⟩
      (c′ • °G′ • c′ • °G′) • p     ≈⟨ front _ (sym K′-form₂) ⟩
      K′ • p ∎

    ------------------------------------------------------------------
    -- K passes the Z on wire 1 controlled negatively by wire 3

    ζ-°c₃ : ζ • °c₃ ≈ °c₃ • ζ
    ζ-°c₃ = sym (comm-12-13 °CZ °CZ (evaluated Eq.refl))

    ζ-G₃ : ζ • G₃ ≈ G₃ • ζ
    ζ-G₃ = S₀₁.⟪⟫-≈
      (S₂₃.⟪⟫-≈ °CZ₂₀-ΛH₂′ (S₂₃.⟪⟫-•₂ m₁ m₂) (S₂₃.⟪⟫-•₂ m₂ m₁))
      (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ ζ) refl) (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-⟪⟫ ζ))
      where
      m₁ : S₂₃.⟪ °CZ₂₀ ⟫ ≈ P₀₃ °CZ
      m₁ = trans (S₂₃.⟪⟫-cong °CZ₂₀-O) (O-S₂₃ °CZ)
      m₂ : S₂₃.⟪ ΛH₂′ ⟫ ≈ G₂
      m₂ = S₂₃.⟪⟫-⟪⟫ G₂

    ζ-K : ζ • K ≈ K • ζ
    ζ-K = begin
      ζ • K                         ≈⟨ back _ K-form₃ ⟩
      ζ • (G₃ • °c₃ • G₃ • °c₃)     ≈⟨ comm-abab ζ-G₃ ζ-°c₃ ⟩
      (G₃ • °c₃ • G₃ • °c₃) • ζ     ≈⟨ front _ (sym K-form₃) ⟩
      K • ζ ∎

    -- It is the CZ of wires 1 3 and Z on wire 1.
    ζ-form : ζ ≈ c′ • z₁
    ζ-form = begin
      P₁₃ °CZ
        ≈⟨ S₁₂.⟪⟫-cong (lemma-cong↑ (U °CZ) (U (CZ • Z ↓)) (U-sem °CZ (CZ • Z ↓) Eq.refl)) ⟩
      P₁₃ (CZ • Z ↓)
        ≈⟨ P₁₃-• CZ (Z ↓) ⟩
      c′ • P₁₃ (Z ↓)
        ≈⟨ back _ (lemma-cong↑ (Ex • Z ↑ • Ex) (Z ↓) S-Z↑) ⟩
      c′ • z₁ ∎

    -- So K between Z on wire 1 is K between that CZ: its inverse.
    z₁Kz₁ : z₁ • K • z₁ ≈ K′
    z₁Kz₁ = begin
      z₁ • K • z₁
        ≈⟨ sym (trans assoc (cancelˡ _ c′²)) ⟩
      (c′ • c′) • z₁ • K • z₁
        ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • ((□ • □) • □) • □) Eq.refl ⟩
      c′ • ((c′ • z₁) • K) • z₁
        ≈⟨ back _ (front _ (trans (front _ (sym ζ-form)) (trans ζ-K (back _ ζ-form)))) ⟩
      c′ • (K • c′ • z₁) • z₁
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
      c′ • K • c′ • (z₁ • z₁)
        ≈⟨ back _ (back _ (trans (back _ z₁²) right-unit)) ⟩
      c′ • K • c′
        ≈⟨ back _ (front _ K-form₂) ⟩
      c′ • (°G′ • c′ • °G′ • c′) • c′
        ≈⟨ by-passoc (□ • (□ • □ • □ • □) • □) ((□ • □ • □ • □) • (□ • □)) Eq.refl ⟩
      (c′ • °G′ • c′ • °G′) • (c′ • c′)
        ≈⟨ trans (back _ c′²) right-unit ⟩
      c′ • °G′ • c′ • °G′
        ≈⟨ sym K′-form₂ ⟩
      K′ ∎

    ------------------------------------------------------------------
    -- q exchanges K and its inverse

    module Z₁ = Conj {₄₊ n} z₁ z₁²

    q-a′ : q • a′ ≈ Z₁.⟪ a′ ⟫ • q
    q-a′ = L-sem (CZ • HC) ((Z ↑ • HC • Z ↑) • CZ) Eq.refl

    q-°B : q • °B ≈ °B • q
    q-°B = N₂.⟪⟫-≈ eq160 (N₂.⟪⟫-•₂ (N₂-L CZ) refl) (N₂.⟪⟫-•₂ refl (N₂-L CZ))

    z₁-box : z₁ • box₃ ≈ box₃ • z₁
    z₁-box = comm-• eq119 (comm-• z₁-c (comm-• eq120 z₁-c))
      where
      z₁-c : z₁ • CZ₃₀ ≈ CZ₃₀ • z₁
      z₁-c = begin
        Z ↑ • CZ₃₀         ≈⟨ back _ CZ₃₀-P ⟩
        U (Z ↓) • P₀₃ CZ   ≈⟨ sym (P₀₃-U CZ (Z ↓)) ⟩
        P₀₃ CZ • U (Z ↓)   ≈⟨ front _ (sym CZ₃₀-P) ⟩
        CZ₃₀ • Z ↑ ∎

    Z₁-°B : Z₁.⟪ °B ⟫ ≈ °B
    Z₁-°B = Z₁.⟪⟫-fix (N₂.⟪⟫-≈ z₁-box (N₂.⟪⟫-•₂ (N₂-L (Z ↑)) refl) (N₂.⟪⟫-•₂ refl (N₂-L (Z ↑))))

    -- q through a word x y x y.
    pass₄ : ∀ {x y x′ y′ : Circuit (₄₊ n)} → q • x ≈ x′ • q → q • y ≈ y′ • q →
            q • (x • y • x • y) ≈ (x′ • y′ • x′ • y′) • q
    pass₄ {x} {y} {x′} {y′} qx qy = begin
      q • (x • y • x • y)
        ≈⟨ by-passoc (□ • (□ • □ • □ • □)) ((□ • □) • □ • □ • □) Eq.refl ⟩
      (q • x) • y • x • y
        ≈⟨ front _ qx ⟩
      (x′ • q) • y • x • y
        ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □) • □ • □) Eq.refl ⟩
      x′ • (q • y) • x • y
        ≈⟨ back _ (front _ qy) ⟩
      x′ • (y′ • q) • x • y
        ≈⟨ by-passoc (□ • (□ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
      x′ • y′ • (q • x) • y
        ≈⟨ back _ (back _ (front _ qx)) ⟩
      x′ • y′ • (x′ • q) • y
        ≈⟨ by-passoc (□ • □ • (□ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
      x′ • y′ • x′ • (q • y)
        ≈⟨ back _ (back _ (back _ qy)) ⟩
      x′ • y′ • x′ • (y′ • q)
        ≈⟨ by-passoc (□ • □ • □ • (□ • □)) ((□ • □ • □ • □) • □) Eq.refl ⟩
      (x′ • y′ • x′ • y′) • q ∎

    q-K : q • K ≈ K′ • q
    q-K = begin
      q • K
        ≈⟨ back _ K-form₁ ⟩
      q • (a′ • °B • a′ • °B)
        ≈⟨ pass₄ q-a′ q-°B ⟩
      (Z₁.⟪ a′ ⟫ • °B • Z₁.⟪ a′ ⟫ • °B) • q
        ≈⟨ front _ (sym (Z₁.⟪⟫-•₄ refl Z₁-°B refl Z₁-°B)) ⟩
      Z₁.⟪ a′ • °B • a′ • °B ⟫ • q
        ≈⟨ front _ (Z₁.⟪⟫-cong (sym K-form₁)) ⟩
      (z₁ • K • z₁) • q
        ≈⟨ front _ z₁Kz₁ ⟩
      K′ • q ∎

    qKq : q • K • q ≈ K′
    qKq = trans (sym assoc) (trans (front _ q-K) (cancelʳ _ q²))

    q-K′ : q • K′ ≈ K • q
    q-K′ = sym (conj-comm q² qKq)

    ------------------------------------------------------------------
    -- Inverses

    KK′ : K • K′ ≈ ε
    KK′ = trans (sym (S₀₁.⟪⟫-• (N₂.⟪ ZX₃ ⟫) (N₂.⟪ XZ₃ ⟫)))
         (trans (S₀₁.⟪⟫-cong (trans (sym (N₂.⟪⟫-• ZX₃ XZ₃)) (trans (N₂.⟪⟫-cong eq208′) N₂.⟪⟫-ε)))
                S₀₁.⟪⟫-ε)

    K′K : K′ • K ≈ ε
    K′K = eq209

  -- (216)
  eq216 : K • CCZX ≈ CCZX • K
  eq216 = sym (begin
    CCZX • K
      ≈⟨ front _ (ax symm-controls) ⟩
    (p • q • p • q) • K
      ≈⟨ pass-pqpq p-K p-K′ q-K q-K′ ⟩
    K • (p • q • p • q)
      ≈⟨ back _ (sym (ax symm-controls)) ⟩
    K • CCZX ∎)

  -- (217)
  eq217 : K • CCXZ ≈ CCXZ • K
  eq217 = comm-inv eq117 eq118 eq216

  -- (218)
  eq218 : K′ • CCZX ≈ CCZX • K′
  eq218 = sym (comm-inv KK′ K′K (sym eq216))
