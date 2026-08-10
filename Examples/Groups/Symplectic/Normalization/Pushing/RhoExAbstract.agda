------------------------------------------------------------------------
-- Presentations of groups
--
-- Strategy B for the residual half of srel-wd — and the proof that it
-- is CIRCULAR.
--
-- The plan under test was: discharge the residual (≈) half of
--
--     act c (dual u)  ≋  act c (Ex • u • Ex)
--
-- without ever computing ρ-Ex, by using `ract-sound` (which relates the
-- coset action back to ≈) plus group reasoning — Ex • Ex ≈ ε, right
-- cancellation, etc.
--
-- This module carries that plan out, and it works: `Strategy-B` below
-- derives the residual half of *every* srel-wd obligation from
--
--   (a) the word-level equation u ≈ t  (free for an axiom: `axiom`), and
--   (b) the coset (≡) half, step n c u ≡ step n c t,
--
-- with no case analysis on the coset and no closed form for any
-- residual.  But it needs one further ingredient:
--
--   ↑-inj :  w ↑ ≈ v ↑  (at width ₁₊ n)  →  w ≈ v  (at width n)
--
-- i.e. that the wire-embedding Spₙ ↪ Spₙ₊₁ is faithful.
--
-- `Converse` below shows that ↑-inj is *exactly* what the
-- Reidemeister–Schreier construction produces at that same level, from
-- the very obligation we were trying to prove: feeding
-- `Normalization.CosetNF.SingleLevel.Transfer` its five hypotheses — of
-- which `h-wd-ax` IS srel-wd — yields `fʷ-injective`, which is ↑-inj.
--
-- So, modulo the four *already discharged* Extension hypotheses
-- (Iᶜ / [I]≈ε' / ⁻¹[⇑]-gen' / f-wd-ax, Normalization.agda:106-198 and
-- :312-313), we have at every level n:
--
--     srel-wd residual half   ⟸  ↑-inj   (Strategy-B.resid-half)
--     ↑-inj                   ⟸  srel-wd (Converse.↑-inj)
--
-- The two are inter-derivable at the SAME level, so Strategy B cannot
-- discharge srel-wd.  Both directions are machine-checked below.
--
-- What this does establish, and is worth recording: given the coset
-- half, the residual half of srel-wd is EQUIVALENT to faithfulness of
-- `_↑`.  Any independent proof of ↑-inj (a faithful semantic model, or
-- a syntactic retraction Circuit (₁₊ n) → Circuit n) would discharge
-- the residual half of every axiom at once — not just Ex — and would be
-- a strictly better investment than computing ρ-Ex.  Conversely, the
-- difficulty of ρ-Ex is not an accident: it is a shadow of the
-- completeness theorem itself.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.RhoExAbstract
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike using (module Group-Lemmas)
import Normalization.CosetNF as CosetNF

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open Symplectic-GroupLike using (grouplike)

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime

import Examples.Groups.Symplectic.Normalization.Pushing.PushML p-2 p-prime as PushML
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
  using (C ; ract ; _≋_)
open import Examples.Groups.Symplectic.Normalization.Pushing.SyllableAction p-2 p-prime
  using (act ; resid ; step)

------------------------------------------------------------------------
-- The section, and word-level soundness of the coset action.
--
-- `ract-sound` is a statement about single generators.  Threading it
-- over a word is the standard fold (`CosetNF.lemma-ᵗ-act` /
-- `Reidemeister-Schreier.RightAction.lemma-⊛` do the same thing); it is
-- reproved here so that this module depends on NOTHING that consumes
-- srel-wd.  In particular it does not go through `SingleLevel.Transfer`.

[_]ᶜ : ∀ {n : ℕ} → C (₁₊ n) → Circuit (₁₊ n)
[_]ᶜ {n} = [_]ᵐˡ

act-sound : ∀ (n : ℕ) (c : C (₁₊ n)) (w : Circuit (₁₊ n)) →
  let open PB ((₁₊ n) QRel,_===_) in
  [ c ]ᶜ • w ≈ ((resid n c w) ↑) • [ step n c w ]ᶜ
act-sound n c [ g ]ʷ = PushML.ract-sound c g
act-sound n c ε      = PB.trans PB.right-unit (PB.sym PB.left-unit)
act-sound n c (w • v) = begin
  [ c ]ᶜ • (w • v)
    ≈⟨ sym assoc ⟩
  ([ c ]ᶜ • w) • v
    ≈⟨ cleft (act-sound n c w) ⟩
  (((resid n c w) ↑) • [ step n c w ]ᶜ) • v
    ≈⟨ assoc ⟩
  ((resid n c w) ↑) • ([ step n c w ]ᶜ • v)
    ≈⟨ cright (act-sound n (step n c w) v) ⟩
  ((resid n c w) ↑) • (((resid n (step n c w) v) ↑) • [ step n (step n c w) v ]ᶜ)
    ≈⟨ sym assoc ⟩
  (((resid n c w) ↑) • ((resid n (step n c w) v) ↑)) • [ step n (step n c w) v ]ᶜ ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

------------------------------------------------------------------------
-- Strategy B, in full.
--
-- Given faithfulness of `_↑`, the residual half of the coset action is
-- determined by the word-level equation and the coset half — abstractly,
-- with no computation of any residual.

module Strategy-B
  (n : ℕ)
  (↑-inj : ∀ (w v : Circuit n) →
     PB._≈_ ((₁₊ n) QRel,_===_) (w ↑) (v ↑) → PB._≈_ (n QRel,_===_) w v)
  where

  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open Group-Lemmas ((₁₊ n) QRel,_===_) (grouplike {₁₊ n}) using (•-cancelʳ)
  open SR word-setoid

  -- The headline: the residual half, from the word equation + coset half.
  resid-half : ∀ (c : C (₁₊ n)) {u t : Circuit (₁₊ n)} →
    u ≈ t → step n c u ≡ step n c t →
    PB._≈_ (n QRel,_===_) (resid n c u) (resid n c t)
  resid-half c {u} {t} eq ceq = ↑-inj (resid n c u) (resid n c t) (•-cancelʳ lifted)
    where
    lifted : (((resid n c u) ↑) • [ step n c t ]ᶜ)
           ≈ (((resid n c t) ↑) • [ step n c t ]ᶜ)
    lifted = begin
      ((resid n c u) ↑) • [ step n c t ]ᶜ
        ≡⟨ Eq.cong (λ z → ((resid n c u) ↑) • [ z ]ᶜ) (Eq.sym ceq) ⟩
      ((resid n c u) ↑) • [ step n c u ]ᶜ
        ≈⟨ sym (act-sound n c u) ⟩
      [ c ]ᶜ • u
        ≈⟨ cright eq ⟩
      [ c ]ᶜ • t
        ≈⟨ act-sound n c t ⟩
      ((resid n c t) ↑) • [ step n c t ]ᶜ ∎

  -- Packaged as ≋.
  ≋-from-≈ : ∀ (c : C (₁₊ n)) {u t : Circuit (₁₊ n)} →
    u ≈ t → step n c u ≡ step n c t → act n c u ≋ act n c t
  ≋-from-≈ c eq ceq = resid-half c eq ceq , ceq

  -- Consequence: the WHOLE of ⁻¹[⇑]-wd'' (every axiom, every coset,
  -- including srel c10/c11 and the structural cong↑/comm₁/comm₂ cases)
  -- follows from its coset half alone.  ρ-Ex is never needed.
  wd-from-coset : ∀ (c : C (₁₊ n)) {u t : Circuit (₁₊ n)} →
    ((₁₊ n) QRel,_===_) u t → step n c u ≡ step n c t →
    act n c u ≋ act n c t
  wd-from-coset c ax ceq = ≋-from-≈ c (axiom ax) ceq

------------------------------------------------------------------------
-- The Ex/duality instance: what DualTransport asked for.
--
-- `srel-wd-dual` (DualTransport.agda:102-109) needs the intertwiner
--   act c (dual u) ≋ act c (Ex • u • Ex)
-- at the two words of the axiom.  Under Strategy B this is discharged by
-- the ≈-fact `lemma-Ex-dual` (dual w ≈ Ex • w • Ex, Lemmas.Duality) plus
-- the coset half that ExAction/ExIntertwine already establish — with no
-- closed form for ρ-Ex.

module Ex-Dual
  (n : ℕ)
  (↑-inj : ∀ (w v : Circuit (₁₊ n)) →
     PB._≈_ ((₂₊ n) QRel,_===_) (w ↑) (v ↑) → PB._≈_ ((₁₊ n) QRel,_===_) w v)
  (dual : Circuit (₂₊ n) → Circuit (₂₊ n))
  where

  open Strategy-B (₁₊ n) ↑-inj using (≋-from-≈)

  dual-≋-Ex : ∀ (c : C (₂₊ n)) (u : Circuit (₂₊ n)) →
    PB._≈_ ((₂₊ n) QRel,_===_) (dual u) (Ex • u • Ex) →
    step (₁₊ n) c (dual u) ≡ step (₁₊ n) c (Ex • u • Ex) →
    act (₁₊ n) c (dual u) ≋ act (₁₊ n) c (Ex • u • Ex)
  dual-≋-Ex c u eq ceq = ≋-from-≈ c eq ceq

------------------------------------------------------------------------
-- The converse — where the circularity is.
--
-- ↑-inj at level n is `fʷ-injective` of
-- `CosetNF.SingleLevel.Transfer` at level n, and that module's second
-- hypothesis `h-wd-ax` is verbatim srel-wd at level n (the type of
-- `Normalization.⁻¹[⇑]-wd'' {n}`).
--
-- The other four hypotheses are NOT assumptions of the development —
-- they are already discharged, hole-free, in Normalization.agda:
--   I           = Iᶜ            (Normalization.agda:109-111)
--   [I]≈ε       = [I]≈ε'        (Normalization.agda:158-162)
--   h=⁻¹f-gen   = ⁻¹[⇑]-gen'    (Normalization.agda:191-198)
--   f-wd-ax, h=ract             (Normalization.agda:312-318, reproved here)
-- They are taken as parameters here only so that this module does not
-- have to import Normalization.agda, which still contains holes.

module Converse
  (n : ℕ)
  (I : C (₁₊ n))
  ([I]≈ε : PB._≈_ ((₁₊ n) QRel,_===_) [ I ]ᶜ ε)
  (h=⁻¹f-gen : ∀ (x : Gen n) → ([ x ]ʷ , I) ≋ act n I [ x ↥ ]ʷ)
  -- ↓ THIS is srel-wd: the type of Normalization.⁻¹[⇑]-wd'' {n}.
  (h-wd-ax : ∀ (c : C (₁₊ n)) {u t : Circuit (₁₊ n)} →
     ((₁₊ n) QRel,_===_) u t → act n c u ≋ act n c t)
  where

  private
    fᵍ : Gen n → Circuit (₁₊ n)
    fᵍ = [_]ʷ ∘ _↥

    f-wd-ax : ∀ {w v : Circuit n} → (n QRel,_===_) w v →
      PB._≈_ ((₁₊ n) QRel,_===_) ((fᵍ ʷ) w) ((fᵍ ʷ) v)
    f-wd-ax {w} {v} x = Eq.subst₂ (PB._≈_ ((₁₊ n) QRel,_===_))
      (Eq.sym (wconcatmap-[f]ʷ w)) (Eq.sym (wconcatmap-[f]ʷ v))
      (PB.axiom (cong↑ x))

    h=ract : ∀ (c : C (₁₊ n)) (b : Gen (₁₊ n)) →
      PB._≈_ ((₁₊ n) QRel,_===_)
        ([ c ]ᶜ • [ b ]ʷ)
        ((fᵍ ʷ) (ract c b .proj₁) • [ ract c b .proj₂ ]ᶜ)
    h=ract c b = Eq.subst
      (λ x → PB._≈_ ((₁₊ n) QRel,_===_) ([ c ]ᶜ • [ b ]ʷ)
                    (x • [ ract c b .proj₂ ]ᶜ))
      (Eq.sym (wconcatmap-[f]ʷ (ract c b .proj₁)))
      (PushML.ract-sound c b)

  module SL = CosetNF.SingleLevel
    (n QRel,_===_) ((₁₊ n) QRel,_===_) (C (₁₊ n)) I fᵍ (ract {n}) (λ c → [ c ]ᶜ)

  module TR = SL.Transfer h=⁻¹f-gen h-wd-ax f-wd-ax [I]≈ε h=ract

  -- Reidemeister–Schreier hands back exactly the ingredient Strategy B
  -- was missing.
  ↑-inj : ∀ (w v : Circuit n) →
    PB._≈_ ((₁₊ n) QRel,_===_) (w ↑) (v ↑) → PB._≈_ (n QRel,_===_) w v
  ↑-inj w v hyp = TR.fʷ-injective w v
    (Eq.subst₂ (PB._≈_ ((₁₊ n) QRel,_===_))
      (Eq.sym (wconcatmap-[f]ʷ w)) (Eq.sym (wconcatmap-[f]ʷ v)) hyp)

  -- ... and therefore srel-wd re-derives itself.  The loop, closed.
  circular : ∀ (c : C (₁₊ n)) {u t : Circuit (₁₊ n)} →
    ((₁₊ n) QRel,_===_) u t → step n c u ≡ step n c t →
    act n c u ≋ act n c t
  circular = Strategy-B.wd-from-coset n ↑-inj
