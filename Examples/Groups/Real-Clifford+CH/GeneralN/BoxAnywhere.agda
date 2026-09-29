------------------------------------------------------------------------
-- Presentations of groups
--
-- Two boxes anywhere, in any colours, commute (Clément, Lemma D.13,
-- Equations (335) and (336), placed)
--
-- `boxF u s` is the canonical box placed by a network u — its box wire
-- the wire u brings to wire 0 — and coloured by s (BoxFrames).  A
-- colouring passes a network with its bits permuted along the network
-- (`net-negs`, `swW`), and two colourings compose to one (`negs-xor`,
-- `combine`).  So two placed boxes with the same box wire are,
-- conjugated back by the network of one of them, the canonical box and
-- a colouring of it — (335) (`BoxComm.C335`) — and two with different
-- box wires, by a network bringing their box wires to the wires 0 and 1
-- (BoxFrames' σ-for), the canonical box and a colouring of the box on
-- wire 1 — (336).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BoxAnywhere
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; X²)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; perm ; φ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (negsB ; negs² ; revS ; net-inv ; net-inv′ ; swapAt-negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames
  using (Canon ; module Frames ; pl ; pl-• ; pl-cong ; perm-• ; perm-σ₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (B₁ ; C335 ; C336)

private
  variable
    n : ℕ

open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours public

------------------------------------------------------------------------
-- Placed boxes

module Anywhere {m : ℕ} (C : Canon m) (c335 : C335 m) (c336 : C336 m) where

  open Frames C

  private
    N : ℕ
    N = ₃₊ m

    Λ : Circuit N
    Λ = Λ□ (₂₊ m)

  open Tools (N VRel,_===_)

  private
    -- A placement undone.
    unpl : ∀ (w : Word (S.Gen N)) (a : Circuit N) → pl (revS w) (pl w a) ≈ a
    unpl w a = begin
      net (revS w) • (net w • a • net (revS w)) • net (revS (revS w))
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (net (revS w) • net w) • a • (net (revS w) • net (revS (revS w)))
        ≈⟨ cong (net-inv′ w) (back _ (net-inv (revS w))) ⟩
      ε • a • ε
        ≈⟨ trans left-unit right-unit ⟩
      a ∎

    repl : ∀ (w : Word (S.Gen N)) (a : Circuit N) → pl w (pl (revS w) a) ≈ a
    repl w a = begin
      net w • (net (revS w) • a • net (revS (revS w))) • net (revS w)
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (net w • net (revS w)) • a • (net (revS (revS w)) • net (revS w))
        ≈⟨ cong (net-inv w) (back _ (net-inv′ (revS w))) ⟩
      ε • a • ε
        ≈⟨ trans left-unit right-unit ⟩
      a ∎

    -- Commuting after a placement is commuting.
    by-pl : ∀ (w : Word (S.Gen N)) {a b : Circuit N} →
            pl (revS w) a • pl (revS w) b ≈ pl (revS w) b • pl (revS w) a → a • b ≈ b • a
    by-pl w {a} {b} e = begin
      a • b                                          ≈⟨ sym (repl w (a • b)) ⟩
      pl w (pl (revS w) (a • b))                     ≈⟨ pl-cong w (pl-• (revS w) a b) ⟩
      pl w (pl (revS w) a • pl (revS w) b)           ≈⟨ pl-cong w e ⟩
      pl w (pl (revS w) b • pl (revS w) a)           ≈⟨ pl-cong w (sym (pl-• (revS w) b a)) ⟩
      pl w (pl (revS w) (b • a))                     ≈⟨ repl w (b • a) ⟩
      b • a ∎

    -- A coloured placed box, placed back.
    back-box : ∀ (w : Word (S.Gen N)) (s : Bits N) (a : Circuit N) →
               pl (revS w) (negsB s • pl w a • negsB s) ≈ col (swW (revS w) s) a
    back-box w s a = begin
      pl (revS w) (negsB s • pl w a • negsB s)
        ≈⟨ trans (pl-• (revS w) (negsB s) _) (back _ (pl-• (revS w) (pl w a) (negsB s))) ⟩
      pl (revS w) (negsB s) • pl (revS w) (pl w a) • pl (revS w) (negsB s)
        ≈⟨ cong (net-negs (revS w) s) (cong (unpl w a) (net-negs (revS w) s)) ⟩
      col (swW (revS w) s) a ∎

    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

  -- Two boxes with the same box wire.
  same : ∀ (u u′ : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t ≡ 0F →
         (s s′ : Bits N) → boxF u s • boxF u′ s′ ≈ boxF u′ s′ • boxF u s
  same u u′ t pu pu′ s s′ = begin
    boxF u s • boxF u′ s′     ≈⟨ back _ e ⟩
    boxF u s • boxF u s′      ≈⟨ by-pl u (trans (cong (back-box u s Λ) (back-box u s′ Λ))
                                          (trans (col-pair (swW (revS u) s) (swW (revS u) s′) Λ c335)
                                                 (sym (cong (back-box u s′ Λ) (back-box u s Λ))))) ⟩
    boxF u s′ • boxF u s      ≈⟨ front _ (sym e) ⟩
    boxF u′ s′ • boxF u s ∎
    where
    e : boxF u′ s′ ≈ boxF u s′
    e = back _ (front _ (frame-eq u′ u t pu′ pu))

  -- Two boxes with different box wires.
  apart : ∀ (u u′ : Word (S.Gen N)) (t t′ : Fin N) → t′ ≢ t → perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t′ ≡ 0F →
          (s s′ : Bits N) → boxF u s • boxF u′ s′ ≈ boxF u′ s′ • boxF u s
  apart u u′ t t′ t′≢t pu pu′ s s′ with σ-for u t′ t t′≢t pu
  ... | σ , σt , σt′ = begin
    boxF u s • boxF u′ s′
      ≈⟨ cong e₁ e₂ ⟩
    (negsB s • pl σ Λ • negsB s) • (negsB s′ • pl σ (B₁ m) • negsB s′)
      ≈⟨ by-pl σ (trans (cong (back-box σ s Λ) (back-box σ s′ (B₁ m)))
                  (trans (col-pair′ (swW (revS σ) s) (swW (revS σ) s′) Λ (B₁ m) c336)
                         (sym (cong (back-box σ s′ (B₁ m)) (back-box σ s Λ))))) ⟩
    (negsB s′ • pl σ (B₁ m) • negsB s′) • (negsB s • pl σ Λ • negsB s)
      ≈⟨ sym (cong e₂ e₁) ⟩
    boxF u′ s′ • boxF u s ∎
    where
    σ′ : Word (S.Gen N)
    σ′ = σ • S.σ
    pσ′ : perm σ′ ⟨$⟩ʳ t′ ≡ 0F
    pσ′ = Eq.trans (perm-• σ S.σ t′) (Eq.trans (Eq.cong (perm S.σ ⟨$⟩ʳ_) σt′) perm-σ₁)
    B-pl : pl σ′ Λ ≈ pl σ (B₁ m)
    B-pl = by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl
    e₁ : boxF u s ≈ negsB s • pl σ Λ • negsB s
    e₁ = back _ (front _ (frame-eq u σ t pu σt))
    e₂ : boxF u′ s′ ≈ negsB s′ • pl σ (B₁ m) • negsB s′
    e₂ = back _ (front _ (trans (frame-eq u′ σ′ t′ pu′ pσ′) B-pl))

  -- Any two placed boxes, in any colours.
  boxes-comm : ∀ (u u′ : Word (S.Gen N)) (t t′ : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t′ ≡ 0F →
               (s s′ : Bits N) → boxF u s • boxF u′ s′ ≈ boxF u′ s′ • boxF u s
  boxes-comm u u′ t t′ pu pu′ s s′ with t′ ≟ t
  ... | yes Eq.refl = same u u′ t pu pu′ s s′
  ... | no  t′≢t    = apart u u′ t t′ t′≢t pu pu′ s s′
