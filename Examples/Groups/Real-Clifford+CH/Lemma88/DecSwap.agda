------------------------------------------------------------------------
-- Presentations of groups
--
-- The encoded swap decoded on every pair of wires (Clément, the case of
-- SWAP in the proof of Lemma 8.6, Appendix E.4)
--
-- At width 5 + k.  E-swap p is E-CZ p followed by three products over
-- the contexts c of the other wires, the bits of the wires p + 1, p
-- written as a pair: the letters (−1)_[11] X_[11,10], an X on wire p
-- where wire p + 1 is set, then (−1)_[01] X_[01,11], an X on wire p + 1
-- where wire p is set, then the first again.  By Lemma 8.5 (Letter85)
-- each letter decodes to one rotation coloured by the context, XZ on
-- p in the first product and ZX on p + 1 in the second.  In the frame
-- σ of the network bringing p to wire 0 and p + 1 to wire 1
-- (Lemma87Z.Frame₁), resp. σ₂ bringing p + 1 to wire 0 and p to wire 1,
-- every colouring is black on wire 1 and the context above, because
-- the rotation passes the network on its controls (Canon32.rot-rigid);
-- so each product merges into the two-wire rotation (DecX.merge₁R).
-- The two frames differ by the swap of the wires p, p + 1, and back in
-- place (TwoWire.pair-down) the four factors are CZ, CZX, CXZ, CZX on
-- the wires p, p + 1: the swap, by one two-qubit identity, decided
-- (`dSwap`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.DecSwap
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; _≤_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl ; ≤-pred ; <-trans ; n<1+n)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; _•_ ; _ʷ)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using () renaming (module Below to SBelow)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; net-↑)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; lookupℕ ; insertℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas using (lookup-insert ; lookup-insert-below)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (index)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏ ; zx ; E-X ; E-swap ; E-CZ ; str₂′)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat ; swapAt ; shiftDown ; shiftUp)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (negsB ; sdS ; revS ; revS-↑ ; revS-sdS ; net-sdS ; net-suS ; net-inv ; sd-negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place ; pl-pl)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl ; pl-cong ; pl-• ; pl-•₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Layouts using (setT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoWire using (on2 ; pair-down)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All complete₂ complete₃ using (mergesₙ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (∏-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon32 complete₂ complete₃ using (rot-rigid)
open import Examples.Groups.Real-Clifford+CH.Lemma88.DecX complete₂ complete₃ using (merge₁R)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Letter85 complete₂ complete₃ using (lemma85 ; dEX ; setT-insert)
import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87Z as Lemma87Z
import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87CZ as Lemma87CZ
import Examples.Groups.Real-Clifford+CH.Lemma88.Easy as Easy

private
  variable
    n : ℕ

-- The swap is the two-wire circuit Ex.
swapAt-on2 : ∀ p → swapAt {n} p ≡ on2 Ex p
swapAt-on2 {zero}        p       = Eq.refl
swapAt-on2 {suc zero}    zero    = Eq.refl
swapAt-on2 {suc zero}    (suc p) = Eq.refl
swapAt-on2 {suc (suc n)} zero    = Eq.refl
swapAt-on2 {suc (suc n)} (suc p) = Eq.cong _↑ (swapAt-on2 {suc n} p)

private
  setT-true : ∀ i (y : Bits n) → lookupℕ i y ≡ true → setT i y ≡ y
  setT-true i       []          _ = Eq.refl
  setT-true zero    (true ∷ y)  _ = Eq.refl
  setT-true zero    (false ∷ y) ()
  setT-true (suc i) (b ∷ y)     h = Eq.cong (b ∷_) (setT-true i y h)

------------------------------------------------------------------------
-- At width 5 + k

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    m N : ℕ
    m = ₂₊ k
    N = ₃₊ m

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

  open Tools (N VRel,_===_)
  open Easy m using (e33)
  open Lemma87Z (canonN k completes) (mergesₙ k completes) using (dʷ-∏ ; pl-∏ ; flip-insert ; flip-below ; module Frame₁)
  open Lemma87CZ (canonN k completes) (mergesₙ k completes) using (lemmaCZ)
  open SBelow 2 (s≤s (s≤s z≤n)) complete₂ using () renaming (by-sem to by-sem₂)

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

  module Swap (p : ℕ) (p< : ₂₊ p ≤ N) where

    private
      p≤ : p ≤ ₁₊ m
      p≤ = ≤-pred (≤-pred p<)

      p<N : p < N
      p<N = <-trans (n<1+n p) p<

      module F = Frame₁ p p≤

      σ σ₂ : Word (S.Gen N)
      σ  = F.σ
      σ₂ = sdS (suc p) • (sdS p S.↑)

      -- The encoded X is decoded below every wire.
      dxs : ∀ t → t < N → ∀ w → w < t → (d ʷ) (E-X {m} w) ≈ Xat w
      dxs t t<N w w<t = dEX k below w (<-trans w<t t<N)

      -- The rotation passes the network on its controls.
      inner : ∀ β → pl (sdS {₄₊ k} p S.↑) (rot β) ≈ rot β
      inner β = begin
        net (sdS p S.↑) • rot β • net (revS (sdS p S.↑))
          ≈⟨ ≡→≈ (Eq.cong₂ (λ a b → a • rot β • b) (net-↑ (sdS p)) (Eq.trans (Eq.cong net (revS-↑ (sdS p))) (net-↑ (revS (sdS p))))) ⟩
        net (sdS p) ↑ • rot β • net (revS (sdS p)) ↑
          ≈⟨ trans (sym assoc) (front _ (rot-rigid k below β (sdS p))) ⟩
        (rot β • net (sdS p) ↑) • net (revS (sdS p)) ↑
          ≈⟨ trans assoc (trans (back _ (lemma-cong↑ _ _ (net-inv (sdS p)))) right-unit) ⟩
        rot β ∎

      rigid : ∀ β → pl σ (rot β) ≈ pl (sdS p) (rot β)
      rigid β = trans (sym (pl-pl (sdS p) (sdS p S.↑) (rot β))) (pl-cong (sdS p) (inner β))

      rigid₂ : ∀ β → pl σ₂ (rot β) ≈ pl (sdS (suc p)) (rot β)
      rigid₂ β = trans (sym (pl-pl (sdS (suc p)) (sdS p S.↑) (rot β))) (pl-cong (sdS (suc p)) (inner β))

      -- The colours in the second frame.
      colours₂ : ∀ c → pl σ₂ (negsB (true ∷ true ∷ c)) ≈ negsB (str₂′ p c true true)
      colours₂ c = begin
        pl σ₂ (negsB (true ∷ true ∷ c))
          ≈⟨ sym (pl-pl (sdS (suc p)) (sdS p S.↑) _) ⟩
        pl (sdS (suc p)) (net (sdS p S.↑) • negsB (true ∷ c) ↑ • net (revS (sdS p S.↑)))
          ≈⟨ pl-cong (sdS (suc p)) (trans (≡→≈ nets) (lemma-cong↑ _ _ (sd-negsB p true c p≤))) ⟩
        pl (sdS (suc p)) (negsB (true ∷ insertℕ p true c))
          ≈⟨ sd-negsB (suc p) true (insertℕ p true c) (s≤s p≤) ⟩
        negsB (str₂′ p c true true) ∎
        where
        nets : net (sdS p S.↑) • negsB (true ∷ c) ↑ • net (revS (sdS p S.↑))
               ≡ (net (sdS p) • negsB (true ∷ c) • net (revS (sdS p))) ↑
        nets = Eq.cong₂ (λ a b → a • negsB (true ∷ c) ↑ • b) (net-↑ (sdS p))
                        (Eq.trans (Eq.cong net (revS-↑ (sdS p))) (net-↑ (revS (sdS p))))

      -- A two-wire circuit in the first frame is that circuit on the
      -- wires p, p + 1.
      plσ≡ : ∀ (g : Circuit N) → pl σ g ≡ (shiftDown p • shiftDown p ↑) • g • (shiftUp p ↑ • shiftUp p)
      plσ≡ g = Eq.cong₂ (λ a b → a • g • b)
                 (Eq.cong₂ _•_ (net-sdS p) (Eq.trans (net-↑ (sdS p)) (Eq.cong _↑ (net-sdS p))))
                 (Eq.cong₂ _•_ (Eq.trans (Eq.cong net (revS-↑ (sdS p)))
                                         (Eq.trans (net-↑ (revS (sdS p))) (Eq.cong _↑ (Eq.trans (Eq.cong net (revS-sdS p)) (net-suS p)))))
                               (Eq.trans (Eq.cong net (revS-sdS p)) (net-suS p)))

      at : ∀ (g : Circuit 2) → pl σ (g ↓ᵏ (₃₊ k)) ≈ on2 g p
      at g = trans (≡→≈ (plσ≡ (g ↓ᵏ (₃₊ k)))) (pair-down g p p≤)

      -- The second frame is the first after the swap.
      σ₂-σ : ∀ (g : Circuit N) → pl σ₂ g ≈ swapAt p • pl σ g • swapAt p
      σ₂-σ g = trans (≡→≈ nets)
                 (trans (by-passoc (((□ • □) • □) • □ • (□ • (□ • □))) (□ • (((□ • □) • □ • (□ • □)) • □)) Eq.refl)
                        (≡→≈ (Eq.cong (λ z → swapAt p • z • swapAt p) (Eq.sym (plσ≡ g)))))
        where
        nets : pl σ₂ g ≡ ((swapAt p • shiftDown p) • shiftDown p ↑) • g • (shiftUp p ↑ • (shiftUp p • swapAt p))
        nets = Eq.cong₂ (λ a b → a • g • b)
                 (Eq.cong₂ _•_ (net-sdS (suc p)) (Eq.trans (net-↑ (sdS p)) (Eq.cong _↑ (net-sdS p))))
                 (Eq.cong₂ _•_ (Eq.trans (Eq.cong net (revS-↑ (sdS p)))
                                         (Eq.trans (net-↑ (revS (sdS p))) (Eq.cong _↑ (Eq.trans (Eq.cong net (revS-sdS p)) (net-suS p)))))
                               (Eq.trans (Eq.cong net (revS-sdS (suc p))) (net-suS (suc p))))

    ----------------------------------------------------------------------
    -- The letters

    ℓ₁ ℓ₂ : Bits (₁₊ m) → Word (GenP N)
    ℓ₁ c = zx {N} (index N (str₂′ p c true true)) (index N (str₂′ p c true false)) (index N (str₂′ p c true true))
    ℓ₂ c = zx {N} (index N (str₂′ p c false true)) (index N (str₂′ p c false true)) (index N (str₂′ p c true true))

    dec₁ : ∀ c → (d ʷ) (ℓ₁ c) ≈ pl σ (col (true ∷ true ∷ c) (rot false))
    dec₁ c = begin
      (d ʷ) (zx (index N G) (index N (str₂′ p c true false)) (index N G))
        ≈⟨ e33 (index N G) (index N (str₂′ p c true false)) ⟩
      (d ʷ) (zx (index N G) (index N G) (index N (str₂′ p c true false)))
        ≈⟨ ≡→≈ (Eq.cong (λ v → (d ʷ) (zx {N} (index N G) (index N G) (index N v))) (Eq.sym flipG)) ⟩
      (d ʷ) (zx (index N G) (index N G) (index N (flipAt p G)))
        ≈⟨ lemma85 k below p p<N (dxs p p<N) G ⟩
      place (sdS p) (setT p G) (rot (not (lookupℕ p G)))
        ≈⟨ ≡→≈ (Eq.cong₂ (λ s b → place (sdS p) s (rot (not b))) (setT-true p G Gp) Gp) ⟩
      negsB G • pl (sdS p) (rot false) • negsB G
        ≈⟨ sym (pl-•₃ σ (F.colours′ true true c) (rigid false) (F.colours′ true true c)) ⟩
      pl σ (col (true ∷ true ∷ c) (rot false)) ∎
      where
      G : Bits N
      G = str₂′ p c true true
      flipG : flipAt p G ≡ str₂′ p c true false
      flipG = Eq.trans (flip-below p (suc p) true (insertℕ p true c) (n<1+n p) (s≤s p≤))
                       (Eq.cong (insertℕ (suc p) true) (flip-insert p true c p≤))
      Gp : lookupℕ p G ≡ true
      Gp = Eq.trans (lookup-insert-below (suc p) p true (insertℕ p true c) (n<1+n p) (s≤s p≤)) (lookup-insert p true c p≤)

    dec₂ : ∀ c → (d ʷ) (ℓ₂ c) ≈ pl σ₂ (col (true ∷ true ∷ c) (rot true))
    dec₂ c = begin
      (d ʷ) (zx (index N G) (index N G) (index N (str₂′ p c true true)))
        ≈⟨ ≡→≈ (Eq.cong (λ v → (d ʷ) (zx {N} (index N G) (index N G) (index N v))) (Eq.sym flipG)) ⟩
      (d ʷ) (zx (index N G) (index N G) (index N (flipAt (suc p) G)))
        ≈⟨ lemma85 k below (suc p) p< (dxs (suc p) p<) G ⟩
      place (sdS (suc p)) (setT (suc p) G) (rot (not (lookupℕ (suc p) G)))
        ≈⟨ ≡→≈ (Eq.cong₂ (λ s b → place (sdS (suc p)) s (rot (not b)))
                         (setT-insert (suc p) false (insertℕ p true c) (s≤s p≤))
                         (lookup-insert (suc p) false (insertℕ p true c) (s≤s p≤))) ⟩
      negsB Hc • pl (sdS (suc p)) (rot true) • negsB Hc
        ≈⟨ sym (pl-•₃ σ₂ (colours₂ c) (rigid₂ true) (colours₂ c)) ⟩
      pl σ₂ (col (true ∷ true ∷ c) (rot true)) ∎
      where
      G Hc : Bits N
      G = str₂′ p c false true
      Hc = str₂′ p c true true
      flipG : flipAt (suc p) G ≡ Hc
      flipG = flip-insert (suc p) false (insertℕ p true c) (s≤s p≤)

    ----------------------------------------------------------------------
    -- The products

    dP₁ : (d ʷ) (∏ (allBits (₁₊ m)) ℓ₁) ≈ pl σ (ΛXZ 1 ↓ᵏ (₃₊ k))
    dP₁ = begin
      (d ʷ) (∏ (allBits (₁₊ m)) ℓ₁)
        ≈⟨ ≡→≈ (dʷ-∏ (allBits (₁₊ m)) ℓ₁) ⟩
      ∏ (allBits (₁₊ m)) (λ c → (d ʷ) (ℓ₁ c))
        ≈⟨ ∏-cong (allBits (₁₊ m)) dec₁ ⟩
      ∏ (allBits (₁₊ m)) (λ c → pl σ (col (true ∷ true ∷ c) (rot false)))
        ≈⟨ sym (pl-∏ σ (allBits (₁₊ m)) (λ c → col (true ∷ true ∷ c) (rot false))) ⟩
      pl σ (∏ (allBits (₁₊ m)) (λ c → col (true ∷ true ∷ c) (rot false)))
        ≈⟨ pl-cong σ (merge₁R k below false (₃₊ k) ≤-refl) ⟩
      pl σ (ΛXZ 1 ↓ᵏ (₃₊ k)) ∎

    dP₂ : (d ʷ) (∏ (allBits (₁₊ m)) ℓ₂) ≈ pl σ₂ (ΛZX 1 ↓ᵏ (₃₊ k))
    dP₂ = begin
      (d ʷ) (∏ (allBits (₁₊ m)) ℓ₂)
        ≈⟨ ≡→≈ (dʷ-∏ (allBits (₁₊ m)) ℓ₂) ⟩
      ∏ (allBits (₁₊ m)) (λ c → (d ʷ) (ℓ₂ c))
        ≈⟨ ∏-cong (allBits (₁₊ m)) dec₂ ⟩
      ∏ (allBits (₁₊ m)) (λ c → pl σ₂ (col (true ∷ true ∷ c) (rot true)))
        ≈⟨ sym (pl-∏ σ₂ (allBits (₁₊ m)) (λ c → col (true ∷ true ∷ c) (rot true))) ⟩
      pl σ₂ (∏ (allBits (₁₊ m)) (λ c → col (true ∷ true ∷ c) (rot true)))
        ≈⟨ pl-cong σ₂ (merge₁R k below true (₃₊ k) ≤-refl) ⟩
      pl σ₂ (ΛZX 1 ↓ᵏ (₃₊ k)) ∎

    ----------------------------------------------------------------------
    -- The swap

    dSwap : (d ʷ) (E-swap {m} p) ≈ swapAt p
    dSwap = begin
      (d ʷ) (E-CZ p) • (d ʷ) (∏ (allBits (₁₊ m)) ℓ₁) • (d ʷ) (∏ (allBits (₁₊ m)) ℓ₂) • (d ʷ) (∏ (allBits (₁₊ m)) ℓ₁)
        ≈⟨ cong (sym (lemmaCZ p p<)) (cong dP₁ (cong dP₂ dP₁)) ⟩
      on2 CZ p • pl σ XZ′ • pl σ₂ ZX′ • pl σ XZ′
        ≈⟨ cong (sym (at CZ)) (back _ (front _ (trans (σ₂-σ ZX′) (cong Sw (back _ Sw))))) ⟩
      pl σ CZ • pl σ XZ′ • (pl σ Ex • pl σ ZX′ • pl σ Ex) • pl σ XZ′
        ≈⟨ sym split ⟩
      pl σ (CZ • XZ′ • (Ex • ZX′ • Ex) • XZ′)
        ≈⟨ pl-cong σ (by-sem₂ (CZ • ΛXZ 1 • (Ex • ΛZX 1 • Ex) • ΛXZ 1) Ex Eq.refl {₃₊ k}) ⟩
      pl σ Ex
        ≈⟨ at Ex ⟩
      on2 Ex p
        ≈⟨ ≡→≈ (Eq.sym (swapAt-on2 p)) ⟩
      swapAt p ∎
      where
      XZ′ ZX′ : Circuit N
      XZ′ = ΛXZ 1 ↓ᵏ (₃₊ k)
      ZX′ = ΛZX 1 ↓ᵏ (₃₊ k)
      Sw : swapAt p ≈ pl σ Ex
      Sw = sym (trans (at Ex) (≡→≈ (Eq.sym (swapAt-on2 p))))
      split : pl σ (CZ • XZ′ • (Ex • ZX′ • Ex) • XZ′) ≈ pl σ CZ • pl σ XZ′ • (pl σ Ex • pl σ ZX′ • pl σ Ex) • pl σ XZ′
      split = trans (pl-• σ CZ _) (back _ (trans (pl-• σ XZ′ _) (back _ (trans (pl-• σ (Ex • ZX′ • Ex) XZ′)
                (front _ (pl-•₃ σ refl refl refl))))))

  -- Lemma 8.6 for the swap, on every pair of wires.
  dS : ∀ p → ₂₊ p ≤ N → (d ʷ) (E-swap {m} p) ≈ swapAt p
  dS p p< = Swap.dSwap p p<
