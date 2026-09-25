------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.7 for H and CH: decoding the encoding gives the gate back
-- (Clément, Appendix E.4, the cases of H and CH)
--
-- Every letter of E(H) on wire p is an H-pattern (HLetters) and so
-- decodes to the multi-controlled H with its H on p and its box on the
-- pairing wire q.  That gate is the box between two P ⊗ P on the wires
-- q, p (`ΛH-PP`: for two or more controls by Definition 2.4, for one by
-- the rule (18)), and the negations of its controls pass P ⊗ P, which
-- acts on the two wires that carry none (`Letter.comm`).  So the letter
-- decodes to R • B • R, where B is the box that Lemma 8.4 decodes the
-- letter of E(Z) for the same context to and R is P ⊗ P placed on q, p,
-- the same for every context (`Letter.letter`).  The product over the
-- contexts is then R • D(E(Z)) • R, which Lemma 8.7 for Z makes
-- R • Z • R, and P ⊗ P turns Z into H ((113)).  For CH the same reading
-- reduces E(CH) to E(CZ), and (18) turns CZ into CH; there R is P ⊗ P on
-- the wires p − 1, p, which the pair of shifts of Definition 2.4 carries
-- there (TwoWire's `pair-down`).  No merge of H gates is needed (the
-- paper's (310), after the reordering (340)): the merge was done once,
-- for Z and CZ.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; _≤_ ; suc)
open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
open import Word.Base using (_•_)

module Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87H
  {m : ℕ} (C : Canon m)
  (mergeAt′ : ∀ K → 1 ≤ K → K ≤ ₁₊ m → ∀ c → 1 ≤ c → c ≤ suc K →
              (₂₊ K) ⊢ (Xat c • Λ□ (suc K) • Xat c) • Λ□ (suc K) ≈ placeAt c (Λ□ K))
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Fin using (Fin ; toℕ ; fromℕ<) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (zero ; _<_ ; _<ᵇ_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n ; n<1+n ; n≢1+n)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _ʷ)

import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; net-↑ ; perm)
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (Layout ; mcH ; ΛH ; shiftDown ; shiftUp ; shiftDown₁ ; shiftUp₁ ; negs ; tgtWire ; hWire)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (index)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; insertℕ ; lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
  using (insert-swap ; lookup-insert ; lookup-insert-below)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt ; flipAt-comm)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏ ; hh ; zz ; E-H ; E-CH ; E-Z ; E-CZ ; str₁ ; str₂)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d ; layoutH)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module PP↓ ; PP-CZ↑ ; PP-Z↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (sdS ; suS ; revS ; revS-↑ ; net-sdS ; net-suS ; revS-sdS ; negsB ; sd-negsB ; sd-target)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl ; pl-cong ; pl-• ; pl-•₃ ; module Frames)
open import Examples.Groups.Real-Clifford+CH.GeneralN.OneWire using (on1)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoWire using (on2 ; pair-down ; pl-sd-↑ ; placeAt-on2-top)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HLetters
  using (dH-pat ; negs-layoutH ; tgtWire-layoutH ; hWire₀-layoutH ; setT-flips)
open import Examples.Groups.Real-Clifford+CH.GeneralN.MergeAll (₁₊ m) mergeAt′ using (∏-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87Z C mergeAt′
  using (flip-insert ; flip-below ; dʷ-∏ ; pl-ε ; box² ; rev-invol ; factor ; lemmaZ ; module Frame₁ ; back₀)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87CZ C mergeAt′ using (factor₂ ; lemmaCZ)

open Frames C using (boxF ; frame-eq ; boxF-flip)

private
  N : ℕ
  N = ₃₊ m

------------------------------------------------------------------------
-- P ⊗ P and the multi-controlled H

private
  ΛH-PP′ : ∀ k → (₃₊ k) ⊢ ΛH (₁₊ k) ≈ PP ↓ • Λ□ (₂₊ k) • PP ↓
  ΛH-PP′ zero    = sym PP-CZ↑
    where open Tools (3 VRel,_===_)
  ΛH-PP′ (suc k) = refl
    where open Tools ((₄₊ k) VRel,_===_)

  -- (18) one wire up at a time: P ⊗ P on the wires j, j + 1 turns the CZ
  -- on the wires j + 1, j + 2 into the CH.
  lift-18 : ∀ {n} j → j ≤ n → (₃₊ n) ⊢ on2 PP j • on2 CZ (suc j) • on2 PP j ≈ on2 CH (suc j)
  lift-18 zero    _       = PP-CZ↑
  lift-18 {suc n} (suc j) (s≤s p) =
    lemma-cong↑ (on2 PP j • on2 CZ (suc j) • on2 PP j) (on2 CH (suc j)) (lift-18 j p)

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  PP² : PP ↓ • PP ↓ ≈ ε
  PP² = trans (back _ (sym left-unit)) PP↓.⟪⟫-ε

  ΛH-PP : ΛH (₁₊ m) ≈ PP ↓ • Λ□ (₂₊ m) • PP ↓
  ΛH-PP = ΛH-PP′ m

  -- A product conjugated factor by factor by an involution.
  conj-∏ : ∀ {A : Set} (R : Circuit N) → R • R ≈ ε → (xs : List A) (f : A → Circuit N) →
           ∏ xs (λ x → R • f x • R) ≈ R • ∏ xs f • R
  conj-∏ R R² []       f = sym (trans (back _ left-unit) R²)
  conj-∏ R R² (x ∷ xs) f = begin
    (R • f x • R) • ∏ xs (λ y → R • f y • R)
      ≈⟨ back _ (conj-∏ R R² xs f) ⟩
    (R • f x • R) • (R • ∏ xs f • R)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    R • f x • (R • R) • ∏ xs f • R
      ≈⟨ back _ (back _ (trans (front _ R²) left-unit)) ⟩
    R • f x • ∏ xs f • R
      ≈⟨ back _ (sym assoc) ⟩
    R • (f x • ∏ xs f) • R ∎

  sn<ᵇn : ∀ n → (suc n <ᵇ n) ≡ false
  sn<ᵇn zero    = Eq.refl
  sn<ᵇn (suc n) = sn<ᵇn n

------------------------------------------------------------------------
-- A frame

-- R is P ⊗ P read in the frame σ; it is the same for every context.
module Frame (σ : Word (S.Gen N)) where

  R : Circuit N
  R = pl σ (PP ↓)

  R² : R • R ≈ ε
  R² = trans (sym (pl-• σ (PP ↓) (PP ↓))) (trans (pl-cong σ PP²) (pl-ε σ))

  -- The product of letters each of which decodes to R • D(g x) • R.
  product : ∀ {A : Set} (xs : List A) (f g : A → Word (GenP N)) →
            (∀ x → (d ʷ) (f x) ≈ R • (d ʷ) (g x) • R) →
            (d ʷ) (∏ xs f) ≈ R • (d ʷ) (∏ xs g) • R
  product xs f g e = begin
    (d ʷ) (∏ xs f)                           ≈⟨ ≡→≈ (dʷ-∏ xs f) ⟩
    ∏ xs (λ x → (d ʷ) (f x))                 ≈⟨ ∏-cong xs e ⟩
    ∏ xs (λ x → R • (d ʷ) (g x) • R)         ≈⟨ conj-∏ R R² xs (λ x → (d ʷ) (g x)) ⟩
    R • ∏ xs (λ x → (d ʷ) (g x)) • R         ≈⟨ back _ (front _ (≡→≈ (Eq.sym (dʷ-∏ xs g)))) ⟩
    R • (d ʷ) (∏ xs g) • R ∎

  -- P ⊗ P conjugating a gate read in the frame.
  final : ∀ {u v u′ v′ : Circuit N} → PP ↓ • u • PP ↓ ≈ v → pl σ u ≈ u′ → pl σ v ≈ v′ → R • u′ • R ≈ v′
  final {u} {v} {u′} {v′} e eu ev = begin
    R • u′ • R                     ≈⟨ back _ (front _ (sym eu)) ⟩
    R • pl σ u • R                 ≈⟨ sym (pl-•₃ σ refl refl refl) ⟩
    pl σ (PP ↓ • u • PP ↓)         ≈⟨ pl-cong σ e ⟩
    pl σ v                         ≈⟨ ev ⟩
    v′ ∎

  ----------------------------------------------------------------------
  -- One letter

  -- The letter on the codes of G with the bits h (the H) and q (the
  -- box) flipped or not, σ being the network of Definition 2.4 for its
  -- layout and s the colours σ brings above the wires 0, 1.
  module Letter (G : Bits N) (h q hw : ℕ) (s : Bits (₁₊ m))
                (h< : h < N) (q< : q < N) (h≢q : h ≢ q) (gh : lookupℕ h G ≡ false) (gq : lookupℕ q G ≡ false)
                (qF : Fin N) (tq : toℕ qF ≡ q) (σq : perm σ ⟨$⟩ʳ qF ≡ 0F)
                (hw≡ : (if h <ᵇ q then suc h else h) ≡ hw)
                (n₁ : shiftDown q • shiftDown₁ hw ≈ net σ)
                (n₂ : shiftUp₁ hw • shiftUp q ≈ net (revS σ))
                (col : pl σ (negsB (true ∷ true ∷ s)) ≈ negsB (flipAt h (flipAt q G))) where

    private
      T : Bits N
      T = flipAt h (flipAt q G)

      Nt : Circuit N
      Nt = negsB (true ∷ true ∷ s)

      pq : perm (sdS {N} q) ⟨$⟩ʳ qF ≡ 0F
      pq = Eq.subst (λ j → perm (sdS {N} j) ⟨$⟩ʳ qF ≡ 0F) tq (sd-target qF)

      L : Layout N
      L = layoutH {m} G h q

      e-neg : negs L ≡ negsB T
      e-neg = Eq.trans (negs-layoutH h q G) (Eq.cong negsB (setT-flips G h q gh gq h≢q))

      e-t : tgtWire L ≡ q
      e-t = tgtWire-layoutH h q G h≢q q<

      e-h : hWire L ≡ hw
      e-h = Eq.trans (Eq.cong₂ (λ a b → if a <ᵇ b then suc a else a) (hWire₀-layoutH h q G h<) e-t) hw≡

      e-mcH : mcH L ≡ negsB T • shiftDown q • shiftDown₁ hw • ΛH (₁₊ m) • shiftUp₁ hw • shiftUp q • negsB T
      e-mcH =
        Eq.trans (Eq.cong (λ a → a • shiftDown (tgtWire L) • shiftDown₁ (hWire L) • ΛH (₁₊ m) •
                                     shiftUp₁ (hWire L) • shiftUp (tgtWire L) • a) e-neg)
        (Eq.trans (Eq.cong (λ t → negsB T • shiftDown t • shiftDown₁ (hWire L) • ΛH (₁₊ m) •
                                    shiftUp₁ (hWire L) • shiftUp t • negsB T) e-t)
                  (Eq.cong (λ w → negsB T • shiftDown q • shiftDown₁ w • ΛH (₁₊ m) •
                                    shiftUp₁ w • shiftUp q • negsB T) e-h))

      -- The negations pass P ⊗ P: in the frame they sit above it.
      comm : negsB T • R ≈ R • negsB T
      comm = begin
        negsB T • pl σ (PP ↓)          ≈⟨ front _ (sym col) ⟩
        pl σ Nt • pl σ (PP ↓)          ≈⟨ sym (pl-• σ Nt (PP ↓)) ⟩
        pl σ (Nt • PP ↓)               ≈⟨ pl-cong σ (sym (low-comm PP (negsB s))) ⟩
        pl σ (PP ↓ • Nt)               ≈⟨ pl-• σ (PP ↓) Nt ⟩
        pl σ (PP ↓) • pl σ Nt          ≈⟨ back _ col ⟩
        pl σ (PP ↓) • negsB T ∎

      box-flip : boxF (sdS q) T ≈ boxF (sdS q) (flipAt h G)
      box-flip = Eq.subst (λ w → boxF (sdS q) w ≈ boxF (sdS q) (flipAt h G)) (Eq.sym e)
                          (boxF-flip (sdS q) qF pq (flipAt h G))
        where
        e : T ≡ flipAt (toℕ qF) (flipAt h G)
        e = Eq.trans (flipAt-comm h q G) (Eq.cong (λ j → flipAt j (flipAt h G)) (Eq.sym tq))

    mcH-form : mcH L ≈ R • boxF (sdS q) (flipAt h G) • R
    mcH-form = begin
      mcH L
        ≈⟨ ≡→≈ e-mcH ⟩
      negsB T • shiftDown q • shiftDown₁ hw • ΛH (₁₊ m) • shiftUp₁ hw • shiftUp q • negsB T
        ≈⟨ back _ (by-passoc (□ • □ • □ • □ • □ • □) ((□ • □) • □ • (□ • □) • □) Eq.refl) ⟩
      negsB T • (shiftDown q • shiftDown₁ hw) • ΛH (₁₊ m) • (shiftUp₁ hw • shiftUp q) • negsB T
        ≈⟨ back _ (cong n₁ (back _ (front _ n₂))) ⟩
      negsB T • net σ • ΛH (₁₊ m) • net (revS σ) • negsB T
        ≈⟨ back _ (back _ (front _ ΛH-PP)) ⟩
      negsB T • net σ • (PP ↓ • Λ□ (₂₊ m) • PP ↓) • net (revS σ) • negsB T
        ≈⟨ back _ (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) ⟩
      negsB T • pl σ (PP ↓ • Λ□ (₂₊ m) • PP ↓) • negsB T
        ≈⟨ back _ (front _ (pl-•₃ σ refl refl refl)) ⟩
      negsB T • (R • pl σ (Λ□ (₂₊ m)) • R) • negsB T
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (negsB T • R) • pl σ (Λ□ (₂₊ m)) • (R • negsB T)
        ≈⟨ cong comm (back _ (sym comm)) ⟩
      (R • negsB T) • pl σ (Λ□ (₂₊ m)) • (negsB T • R)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      R • boxF σ T • R
        ≈⟨ back _ (front _ (back _ (front _ (frame-eq σ (sdS q) qF σq pq)))) ⟩
      R • boxF (sdS q) T • R
        ≈⟨ back _ (front _ box-flip) ⟩
      R • boxF (sdS q) (flipAt h G) • R ∎

    letter : (d ʷ) (hh (index N G) (index N (flipAt h G)) (index N (flipAt q G)) (index N (flipAt h (flipAt q G))))
               ≈ R • boxF (sdS q) (flipAt h G) • R
    letter = begin
      (d ʷ) (hh (index N G) (index N (flipAt h G)) (index N (flipAt q G)) (index N (flipAt h (flipAt q G))))
        ≈⟨ ≡→≈ (dH-pat G h q h< q< h≢q gh gq) ⟩
      rev (mcH L)
        ≈⟨ rev-cong mcH-form ⟩
      rev (R • F • R)
        ≈⟨ rev-invol (R • F • R) inv ⟩
      R • F • R ∎
      where
      F : Circuit N
      F = boxF (sdS q) (flipAt h G)
      inv : (R • F • R) • (R • F • R) ≈ ε
      inv = begin
        (R • F • R) • (R • F • R)
          ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
        R • F • (R • R) • F • R
          ≈⟨ back _ (back _ (trans (front _ R²) left-unit)) ⟩
        R • F • F • R
          ≈⟨ back _ (trans (sym assoc) (trans (front _ (box² (sdS q) (flipAt h G))) left-unit)) ⟩
        R • R
          ≈⟨ R² ⟩
        ε ∎

------------------------------------------------------------------------
-- The networks of the two frames

private
  n₁₀ : shiftDown {N} (₂₊ m) • shiftDown₁ 1 ≈ net (sdS {N} (₂₊ m))
  n₁₀ = trans right-unit (≡→≈ (Eq.sym (net-sdS (₂₊ m))))

  n₂₀ : shiftUp₁ {N} 1 • shiftUp (₂₊ m) ≈ net (revS (sdS {N} (₂₊ m)))
  n₂₀ = trans left-unit (≡→≈ (Eq.sym (Eq.trans (Eq.cong net (revS-sdS (₂₊ m))) (net-suS (₂₊ m)))))

  q₀F : Fin N
  q₀F = fromℕ< (≤-refl {N})

  tq₀ : toℕ q₀F ≡ ₂₊ m
  tq₀ = toℕ-fromℕ< (≤-refl {N})

  σq₀ : perm (sdS {N} (₂₊ m)) ⟨$⟩ʳ q₀F ≡ 0F
  σq₀ = Eq.subst (λ j → perm (sdS {N} j) ⟨$⟩ʳ q₀F ≡ 0F) tq₀ (sd-target q₀F)

  -- A gate on wire 0, or the lower wire of a two-wire gate there: the
  -- network sdS (2 + m), the box wire on top.
  module F₀ = Frame (sdS (₂₊ m))

  -- A gate on wire 1 + p, or the lower wire of a two-wire gate there.
  module Nets (p : ℕ) (p≤ : p ≤ ₁₊ m) where
    open Frame₁ p p≤ public using (σ ; pF ; tp ; σq ; colours′ ; back)

    n₁ : shiftDown {N} p • shiftDown₁ (suc p) ≈ net σ
    n₁ = ≡→≈ (Eq.sym (Eq.cong₂ _•_ (net-sdS p) (Eq.trans (net-↑ (sdS p)) (Eq.cong _↑ (net-sdS p)))))

    n₂ : shiftUp₁ {N} (suc p) • shiftUp p ≈ net (revS σ)
    n₂ = ≡→≈ (Eq.sym (Eq.cong₂ _•_
           (Eq.trans (Eq.cong net (revS-↑ (sdS p)))
             (Eq.trans (net-↑ (revS (sdS p))) (Eq.cong _↑ (Eq.trans (Eq.cong net (revS-sdS p)) (net-suS p)))))
           (Eq.trans (Eq.cong net (revS-sdS p)) (net-suS p))))

    hw≡ : (if suc p <ᵇ p then suc (suc p) else suc p) ≡ suc p
    hw≡ = Eq.cong (λ b → if b then suc (suc p) else suc p) (sn<ᵇn p)

    module F = Frame σ

    h≢q : suc p ≢ p
    h≢q e = n≢1+n p (Eq.sym e)

------------------------------------------------------------------------
-- Lemma 8.7 for H

private
  -- The codes of a letter of E(H), as flips of the first.
  fl₀ : ∀ c → flipAt (₂₊ m) (str₁ {m} 0 c false false) ≡ str₁ 0 c true false
  fl₀ c = Eq.cong (false ∷_) (flip-insert (₁₊ m) false c ≤-refl)

  fl₁ : ∀ p → p ≤ ₁₊ m → ∀ c → flipAt p (str₁ {m} (suc p) c false false) ≡ str₁ (suc p) c true false
  fl₁ p p≤ c = Eq.trans (flip-below p (suc p) false (insertℕ p false c) (n<1+n p) (s≤s p≤))
                        (Eq.cong (insertℕ (suc p) false) (flip-insert p false c p≤))

  fl₁′ : ∀ p → p ≤ ₁₊ m → ∀ b c → flipAt (suc p) (str₁ {m} (suc p) c b false) ≡ str₁ (suc p) c b true
  fl₁′ p p≤ b c = flip-insert (suc p) false (insertℕ p b c) (s≤s p≤)

lemmaH : ∀ p → p < N → on1 H p ≈ (d ʷ) (E-H {m} p)
lemmaH zero p<N = sym (begin
  (d ʷ) (E-H 0)
    ≈⟨ F₀.product (allBits (₁₊ m)) _ _ letter₀ ⟩
  F₀.R • (d ʷ) (E-Z 0) • F₀.R
    ≈⟨ back _ (front _ (sym (lemmaZ 0 p<N))) ⟩
  F₀.R • on1 Z 0 • F₀.R
    ≈⟨ F₀.final {Z ↑} {H ↑} PP-Z↑ (back₀ Z) (back₀ H) ⟩
  on1 H 0 ∎)
  where
  letter₀ : ∀ c → (d ʷ) (hh (index N (str₁ 0 c false false)) (index N (str₁ 0 c false true))
                            (index N (str₁ 0 c true false)) (index N (str₁ 0 c true true)))
                  ≈ F₀.R • (d ʷ) (zz (index N (str₁ 0 c false true)) (index N (str₁ 0 c true true))) • F₀.R
  letter₀ c = trans (Eq.subst (λ w → (d ʷ) (hh (index N G) (index N (flipAt 0 G)) (index N w) (index N (flipAt 0 w)))
                                       ≈ F₀.R • boxF (sdS (₂₊ m)) (flipAt 0 G) • F₀.R)
                              (fl₀ c) L.letter)
                    (back _ (front _ (sym (factor 0 p<N c))))
    where
    G : Bits N
    G = str₁ 0 c false false
    col : pl (sdS (₂₊ m)) (negsB (true ∷ true ∷ c)) ≈ negsB (flipAt 0 (flipAt (₂₊ m) G))
    col = Eq.subst (λ w → pl (sdS (₂₊ m)) (negsB (true ∷ true ∷ c)) ≈ negsB (flipAt 0 w)) (Eq.sym (fl₀ c))
                   (sd-negsB (₂₊ m) true (true ∷ c) ≤-refl)
    module L = F₀.Letter G 0 (₂₊ m) 1 c (s≤s z≤n) ≤-refl (λ ()) Eq.refl (lookup-insert (₁₊ m) false c ≤-refl)
                         q₀F tq₀ σq₀ Eq.refl n₁₀ n₂₀ col
lemmaH (suc p) p<N@(s≤s (s≤s p≤)) = sym (begin
  (d ʷ) (E-H (suc p))
    ≈⟨ Nt.F.product (allBits (₁₊ m)) _ _ letter₁ ⟩
  Nt.F.R • (d ʷ) (E-Z (suc p)) • Nt.F.R
    ≈⟨ back _ (front _ (sym (lemmaZ (suc p) p<N))) ⟩
  Nt.F.R • on1 Z (suc p) • Nt.F.R
    ≈⟨ Nt.F.final {Z ↑} {H ↑} PP-Z↑ (Nt.back Z) (Nt.back H) ⟩
  on1 H (suc p) ∎)
  where
  module Nt = Nets p p≤
  letter₁ : ∀ c → (d ʷ) (hh (index N (str₁ (suc p) c false false)) (index N (str₁ (suc p) c false true))
                            (index N (str₁ (suc p) c true false)) (index N (str₁ (suc p) c true true)))
                  ≈ Nt.F.R • (d ʷ) (zz (index N (str₁ (suc p) c false true)) (index N (str₁ (suc p) c true true))) • Nt.F.R
  letter₁ c = trans (Eq.subst (λ y → (d ʷ) (hh (index N G) (index N (str₁ (suc p) c false true))
                                                 (index N (str₁ (suc p) c true false)) (index N y))
                                       ≈ Nt.F.R • boxF (sdS p) (str₁ (suc p) c false true) • Nt.F.R)
                              T≡
                              (Eq.subst₂ (λ w x → (d ʷ) (hh (index N G) (index N x) (index N w)
                                                             (index N (flipAt (suc p) (flipAt p G))))
                                                    ≈ Nt.F.R • boxF (sdS p) x • Nt.F.R)
                                         (fl₁ p p≤ c) (fl₁′ p p≤ false c) L.letter))
                    (back _ (front _ (sym (factor (suc p) p<N c))))
    where
    G : Bits N
    G = str₁ (suc p) c false false
    T≡ : flipAt (suc p) (flipAt p G) ≡ str₁ (suc p) c true true
    T≡ = Eq.trans (Eq.cong (flipAt (suc p)) (fl₁ p p≤ c)) (fl₁′ p p≤ true c)
    col : pl Nt.σ (negsB (true ∷ true ∷ c)) ≈ negsB (flipAt (suc p) (flipAt p G))
    col = Eq.subst (λ w → pl Nt.σ (negsB (true ∷ true ∷ c)) ≈ negsB w) (Eq.sym T≡) (Nt.colours′ true true c)
    gh : lookupℕ (suc p) G ≡ false
    gh = lookup-insert (suc p) false (insertℕ p false c) (s≤s p≤)
    gq : lookupℕ p G ≡ false
    gq = Eq.trans (lookup-insert-below (suc p) p false (insertℕ p false c) (n<1+n p) (s≤s p≤))
                  (lookup-insert p false c p≤)
    module L = Nt.F.Letter G (suc p) p (suc p) c p<N (≤-trans (n≤1+n _) p<N) Nt.h≢q gh gq
                           Nt.pF Nt.tp Nt.σq Nt.hw≡ Nt.n₁ Nt.n₂ col

------------------------------------------------------------------------
-- Lemma 8.7 for CH

private
  fl₂₀ : ∀ c → flipAt (₂₊ m) (str₂ {m} 0 c false true false) ≡ str₂ 0 c true true false
  fl₂₀ c = Eq.cong (λ v → false ∷ true ∷ v) (flip-insert m false c ≤-refl)

  fl₂ : ∀ p → p ≤ m → ∀ c → flipAt p (str₂ {m} (suc p) c false true false) ≡ str₂ (suc p) c true true false
  fl₂ p p≤ c =
    Eq.trans (flip-below p (₂₊ p) true (insertℕ (suc p) false (insertℕ p false c))
                         (≤-trans (n<1+n p) (n≤1+n _)) (s≤s (s≤s p≤)))
      (Eq.cong (insertℕ (₂₊ p) true)
        (Eq.trans (flip-below p (suc p) false (insertℕ p false c) (n<1+n p) (s≤s p≤))
                  (Eq.cong (insertℕ (suc p) false) (flip-insert p false c p≤))))

  fl₂′ : ∀ p → p ≤ m → ∀ b c → flipAt (suc p) (str₂ {m} (suc p) c b true false) ≡ str₂ (suc p) c b true true
  fl₂′ p p≤ b c =
    Eq.trans (flip-below (suc p) (₂₊ p) true (insertℕ (suc p) false (insertℕ p b c)) (n<1+n (suc p)) (s≤s (s≤s p≤)))
             (Eq.cong (insertℕ (₂₊ p) true) (flip-insert (suc p) false (insertℕ p b c) (s≤s p≤)))

  -- The gates on the wires 0, 1, read in the frame of the top wire.
  top₂ : ∀ (g : Circuit 2) → pl (sdS {N} (₂₊ m)) (on2 g 0 ↑) ≈ on2 g 0
  top₂ g = trans (pl-sd-↑ (₂₊ m) (on2 g 0)) (placeAt-on2-top g 0 (s≤s (s≤s z≤n)))

lemmaCH : ∀ p → ₂₊ p ≤ N → on2 CH p ≈ (d ʷ) (E-CH {m} p)
lemmaCH zero p< = sym (begin
  (d ʷ) (E-CH 0)
    ≈⟨ F₀.product (allBits m) _ _ letter₀ ⟩
  F₀.R • (d ʷ) (E-CZ 0) • F₀.R
    ≈⟨ back _ (front _ (sym (lemmaCZ 0 p<))) ⟩
  F₀.R • on2 CZ 0 • F₀.R
    ≈⟨ F₀.final {CZ ↑} {CH ↑} PP-CZ↑ (top₂ CZ) (top₂ CH) ⟩
  on2 CH 0 ∎)
  where
  letter₀ : ∀ c → (d ʷ) (hh (index N (str₂ 0 c false true false)) (index N (str₂ 0 c false true true))
                            (index N (str₂ 0 c true true false)) (index N (str₂ 0 c true true true)))
                  ≈ F₀.R • (d ʷ) (zz (index N (str₂ 0 c false true true)) (index N (str₂ 0 c true true true))) • F₀.R
  letter₀ c = trans (Eq.subst (λ w → (d ʷ) (hh (index N G) (index N (flipAt 0 G)) (index N w) (index N (flipAt 0 w)))
                                       ≈ F₀.R • boxF (sdS (₂₊ m)) (flipAt 0 G) • F₀.R)
                              (fl₂₀ c) L.letter)
                    (back _ (front _ (sym (factor₂ 0 p< c))))
    where
    G : Bits N
    G = str₂ 0 c false true false
    col : pl (sdS (₂₊ m)) (negsB (true ∷ true ∷ true ∷ c)) ≈ negsB (flipAt 0 (flipAt (₂₊ m) G))
    col = Eq.subst (λ w → pl (sdS (₂₊ m)) (negsB (true ∷ true ∷ true ∷ c)) ≈ negsB (flipAt 0 w)) (Eq.sym (fl₂₀ c))
                   (sd-negsB (₂₊ m) true (true ∷ true ∷ c) ≤-refl)
    module L = F₀.Letter G 0 (₂₊ m) 1 (true ∷ c) (s≤s z≤n) ≤-refl (λ ()) Eq.refl (lookup-insert m false c ≤-refl)
                         q₀F tq₀ σq₀ Eq.refl n₁₀ n₂₀ col
lemmaCH (suc p) p<@(s≤s (s≤s (s≤s p≤))) = sym (begin
  (d ʷ) (E-CH (suc p))
    ≈⟨ Nt.F.product (allBits m) _ _ letter₁ ⟩
  Nt.F.R • (d ʷ) (E-CZ (suc p)) • Nt.F.R
    ≈⟨ back _ (front _ (sym (lemmaCZ (suc p) p<))) ⟩
  Nt.F.R • on2 CZ (suc p) • Nt.F.R
    ≈⟨ cong Rp (back _ (front _ Rp)) ⟩
  on2 PP p • on2 CZ (suc p) • on2 PP p
    ≈⟨ lift-18 p p≤ ⟩
  on2 CH (suc p) ∎)
  where
  p≤′ : p ≤ ₁₊ m
  p≤′ = ≤-trans p≤ (n≤1+n m)
  module Nt = Nets p p≤′
  -- P ⊗ P in the frame is P ⊗ P on the wires p, p + 1.
  Rp : Nt.F.R ≈ on2 PP p
  Rp = trans (cong (sym Nt.n₁) (back _ (sym Nt.n₂))) (pair-down PP p p≤′)
  letter₁ : ∀ c → (d ʷ) (hh (index N (str₂ (suc p) c false true false)) (index N (str₂ (suc p) c false true true))
                            (index N (str₂ (suc p) c true true false)) (index N (str₂ (suc p) c true true true)))
                  ≈ Nt.F.R • (d ʷ) (zz (index N (str₂ (suc p) c false true true))
                                        (index N (str₂ (suc p) c true true true))) • Nt.F.R
  letter₁ c = trans (Eq.subst (λ y → (d ʷ) (hh (index N G) (index N (str₂ (suc p) c false true true))
                                                 (index N (str₂ (suc p) c true true false)) (index N y))
                                       ≈ Nt.F.R • boxF (sdS p) (str₂ (suc p) c false true true) • Nt.F.R)
                              T≡
                              (Eq.subst₂ (λ w x → (d ʷ) (hh (index N G) (index N x) (index N w)
                                                             (index N (flipAt (suc p) (flipAt p G))))
                                                    ≈ Nt.F.R • boxF (sdS p) x • Nt.F.R)
                                         (fl₂ p p≤ c) (fl₂′ p p≤ false c) L.letter))
                    (back _ (front _ (sym (factor₂ (suc p) p< c))))
    where
    G : Bits N
    G = str₂ (suc p) c false true false
    s : Bits (₁₊ m)
    s = insertℕ p true c
    T≡ : flipAt (suc p) (flipAt p G) ≡ str₂ (suc p) c true true true
    T≡ = Eq.trans (Eq.cong (flipAt (suc p)) (fl₂ p p≤ c)) (fl₂′ p p≤ true c)
    -- The frame's colours: the wires below the gate, then its upper wire.
    S≡ : str₁ {m} (suc p) s true true ≡ str₂ (suc p) c true true true
    S≡ = Eq.trans (Eq.cong (insertℕ (suc p) true) (insert-swap p p true true c ≤-refl p≤))
                  (insert-swap (suc p) (suc p) true true (insertℕ p true c) ≤-refl (s≤s p≤))
    col : pl Nt.σ (negsB (true ∷ true ∷ s)) ≈ negsB (flipAt (suc p) (flipAt p G))
    col = Eq.subst (λ w → pl Nt.σ (negsB (true ∷ true ∷ s)) ≈ negsB w) (Eq.trans S≡ (Eq.sym T≡))
                   (Nt.colours′ true true s)
    gh : lookupℕ (suc p) G ≡ false
    gh = Eq.trans (lookup-insert-below (₂₊ p) (suc p) true (insertℕ (suc p) false (insertℕ p false c))
                                       (n<1+n (suc p)) (s≤s (s≤s p≤)))
                  (lookup-insert (suc p) false (insertℕ p false c) (s≤s p≤))
    gq : lookupℕ p G ≡ false
    gq = Eq.trans (lookup-insert-below (₂₊ p) p true (insertℕ (suc p) false (insertℕ p false c))
                                       (≤-trans (n<1+n p) (n≤1+n _)) (s≤s (s≤s p≤)))
           (Eq.trans (lookup-insert-below (suc p) p false (insertℕ p false c) (n<1+n p) (s≤s p≤))
                     (lookup-insert p false c p≤))
    module L = Nt.F.Letter G (suc p) p (suc p) s (≤-trans (n≤1+n _) p<) (≤-trans (n≤1+n _) (≤-trans (n≤1+n _) p<))
                           Nt.h≢q gh gq Nt.pF Nt.tp Nt.σq Nt.hw≡ Nt.n₁ Nt.n₂ col
