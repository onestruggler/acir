------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ and their normal form via coset enumeration
-- Adapted to the Circuit / Lift-Relation framework
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.Push (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
  using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Unit using (tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; inspect ; module ≡-Reasoning) renaming ([_] to [_]ₑ)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.NormalForm.Propositional as NFBase
open NFBase using (NormalFormInjective ; NormalForm)


--open import Examples.Groups.Symplectic.NewCosets p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime


private variable
  n : ℕ

open import Examples.Groups.Symplectic.BR.One.A p-2 p-prime as OA
import Examples.Groups.Symplectic.BR.Two.ML'-Top p-2 p-prime as ML'T
open import Examples.Groups.Symplectic.Normalization.Pushing.PushLM1 p-2 p-prime
  using (push-LM1 ; A-dir-S-power)
  using (push-E-S^)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMbS p-2 p-prime
  using (mbSⁿ)
open import Data.Fin using (toℕ)

open import Data.Vec

------------------------------------------------------------------------
-- Bottom-wire ML' push (SCAFFOLD)
--
-- The width-≥2 coset action pushes a bottom-wire unary gate g = gate₁ x
-- through an ML' (₂₊ n) box.  It is the "bottom" dual of the top-gate push
-- BR.Two.ML'-Top.lemma-ML'-Top (which handles g ↥):
--
--   1. the gate hits the trailing A box first, emitting a bottom S-power
--      S^ j and a residual A box a' (BR.One.A.lemma-single-qupit-br-A and
--      PushLM1.A-dir-S-power give dir_A ≡ S^ j);
--   2. S^ j is pushed left through the M column and the B-vector, escaping
--      upward as (dir ↑)   [mbv-bot-push / push-MBvec-bot];
--   3. the residual A box a' is reattached.
--
-- Unlike the top-gate case, pushing a bottom S through one B box
-- (BR.Two.B.lemma-B-br … S-gen) emits a *fresh* bottom S-power together
-- with S↑ and CZ escapes, so step 2 is a cascade — the core work still to
-- be done.  The signatures below fix the interface; the bodies are holes.

-- The bottom single gates are always bottom-wire-single.
bws1 : ∀ {k} (x : SympGate 1) → OA.Bottom-Wire-Single k (gate₁ x)
bws1 H-gate = tt
bws1 S-gate = tt

-- Push a bottom S-power S^ j through the M column · B-vector.  Returns the
-- upward escape (dir : Gen k, to be ↑-lifted) and the updated M and B-vec.
-- NOTE: this residual shape is provisional — the B-box cascade (each box
-- emitting fresh S/S↑/CZ) may force a richer return type.
-- Push S^ j (= S ^ toℕ j) through the M column · B-vector, via the
-- iterated single-S push PushMbS.mbSⁿ.  The B-vector is left unchanged.
mbv-bot-push : ∀ {k} (m : M (₁₊ k)) (bv : Vec B k) (j : ℤ ₚ) →
  Word (Gen k) × (M (₁₊ k) × Vec B k)
mbv-bot-push m bv j =
  proj₁ (mbSⁿ (toℕ j) m bv) , (proj₁ (proj₂ (mbSⁿ (toℕ j) m bv)) , bv)

-- Soundness of mbv-bot-push:  ([ m ]ᵐ • [ bv ]ᵛᵇ) • S^ j escapes as dir ↑.
push-MBvec-bot : ∀ {k} (m : M (₁₊ k)) (bv : Vec B k) (j : ℤ ₚ) →
  let open PB ((₁₊ k) QRel,_===_) in
  ([ m ]ᵐ • [ bv ]ᵛᵇ) • S^ j ≈
    (proj₁ (mbv-bot-push m bv j) ↑) •
      ([ proj₁ (proj₂ (mbv-bot-push m bv j)) ]ᵐ •
       [ proj₂ (proj₂ (mbv-bot-push m bv j)) ]ᵛᵇ)
push-MBvec-bot m bv j = proj₂ (proj₂ (mbSⁿ (toℕ j) m bv))

-- Assemble the ML' (₂₊ n) update: A-box push (dir_A ≡ S^ j, residual a')
-- then mbv-bot-push of S^ j through the M column and B-vector.
ml'-bot-push : ∀ {n} → ML' (₂₊ n) → SympGate 1 →
  Word (Gen (₁₊ n)) × ML' (₂₊ n)
ml'-bot-push {n} ((dv , e) , (bv , a)) x =
  let
    g  = gate₁ x
    a' = OA.dir-and-A'-of (₁₊ n) a g (bws1 x) .proj₂
    j  = A-dir-S-power a g (bws1 x) .proj₁
    r  = mbv-bot-push (dv , e) bv j
  in proj₁ r , (proj₁ (proj₂ r) , (proj₂ (proj₂ r) , a'))

-- The bottom-wire ML' push.  Proof sketch (bottom dual of lemma-ML'-Top);
-- Mw = [ (dv,e) ]ᵐ, Bv = [ bv ]ᵛᵇ, Ae = [ a ]ᵃ, G = [ gate₁ x ]ʷ:
--
--   (Mw • (Bv • Ae)) • G
--     ≈⟨ assoc ; assoc ⟩          Mw • (Bv • (Ae • G))
--     ≈⟨ A-box bottom push ⟩       Mw • (Bv • (S^ j • Ae'))   [dir_A ≡ S^ j]
--     ≈⟨ re-bracket (assoc) ⟩      (Mw • (Bv • S^ j)) • Ae'
--     ≈⟨ push-MBvec-bot ⟩          ((dir ↑) • (Mw' • Bv')) • Ae'
--     ≈⟨ assoc ; assoc ⟩          (dir ↑) • (Mw' • (Bv' • Ae'))
lemma-ML'-Bot : ∀ {n} (ml : ML' (₂₊ n)) (x : SympGate 1) →
  let open PB ((₂₊ n) QRel,_===_)
      r = ml'-bot-push ml x
  in [ ml ]ᵐˡ' • [ gate₁ x ]ʷ ≈ (proj₁ r ↑) • [ proj₂ r ]ᵐˡ'
lemma-ML'-Bot {n} ((dv , e) , (bv , a)) x = proof
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  g   = gate₁ x
  a'  = OA.dir-and-A'-of (₁₊ n) a g (bws1 x) .proj₂
  jj  = A-dir-S-power a g (bws1 x) .proj₁
  dir = proj₁ (mbv-bot-push (dv , e) bv jj)
  m'  = proj₁ (proj₂ (mbv-bot-push (dv , e) bv jj))

  -- A-box bottom push (dir_A ≡ S^ jj), bridged Section ↔ LM-Sym.
  A-push : [ a ]ᵃ • [ g ]ʷ ≈ S^ jj • [ a' ]ᵃ
  A-push = trans (cleft (refl' (ML'T.abox-eq a)))
           (trans (OA.lemma-single-qupit-br-A (₁₊ n) a g (bws1 x))
           (trans (cleft (refl' (A-dir-S-power a g (bws1 x) .proj₂)))
                  (cright (refl' (Eq.sym (ML'T.abox-eq a'))))))

  proof : ([ (dv , e) ]ᵐ • ([ bv ]ᵛᵇ • [ a ]ᵃ)) • [ g ]ʷ
        ≈ dir ↑ • ([ m' ]ᵐ • ([ bv ]ᵛᵇ • [ a' ]ᵃ))
  proof = begin
    ([ (dv , e) ]ᵐ • ([ bv ]ᵛᵇ • [ a ]ᵃ)) • [ g ]ʷ
      ≈⟨ assoc ⟩
    [ (dv , e) ]ᵐ • (([ bv ]ᵛᵇ • [ a ]ᵃ) • [ g ]ʷ)     ≈⟨ cright assoc ⟩
    [ (dv , e) ]ᵐ • ([ bv ]ᵛᵇ • ([ a ]ᵃ • [ g ]ʷ))     ≈⟨ cright (cright A-push) ⟩
    [ (dv , e) ]ᵐ • ([ bv ]ᵛᵇ • (S^ jj • [ a' ]ᵃ))     ≈⟨ cright (sym assoc) ⟩
    [ (dv , e) ]ᵐ • (([ bv ]ᵛᵇ • S^ jj) • [ a' ]ᵃ)     ≈⟨ sym assoc ⟩
    ([ (dv , e) ]ᵐ • ([ bv ]ᵛᵇ • S^ jj)) • [ a' ]ᵃ     ≈⟨ cleft (sym assoc) ⟩
    (([ (dv , e) ]ᵐ • [ bv ]ᵛᵇ) • S^ jj) • [ a' ]ᵃ     ≈⟨ cleft (push-MBvec-bot (dv , e) bv jj) ⟩
    (dir ↑ • ([ m' ]ᵐ • [ bv ]ᵛᵇ)) • [ a' ]ᵃ           ≈⟨ assoc ⟩
    dir ↑ • (([ m' ]ᵐ • [ bv ]ᵛᵇ) • [ a' ]ᵃ)           ≈⟨ cright assoc ⟩
    dir ↑ • ([ m' ]ᵐ • ([ bv ]ᵛᵇ • [ a' ]ᵃ)) ∎

------------------------------------------------------------------------
-- Right coset action

-- The right action of a generator on a coset: ract c b returns the
-- residual circuit b' and the coset c' reached from c by b, so that
-- [ c ]ᶜ • [ b ]ʷ ≈ b' ↑ • [ c' ]ᶜ (see ract-sound below).
ract : ∀ {n} -> ML' (₁₊ n) → SympGate 1 → Circuit n × ML' (₁₊ n)
-- Width 1 (no B boxes): the bottom gate enters the single A box, emitting
-- a power of S that the E box of M absorbs (PushLM1.push-LM1).  Nothing
-- escapes upward, so the residual circuit is ε and the coset update is
-- e ↦ e − k (A-box S-power) and a ↦ a' (A-box residual).
ract {₀} (([] , e) , ([] , a)) H-gate =
  ε , (([] , e + - k) , ([] , a'))
  where
  g : Gen 1
  g  = gate₁ H-gate
  a' = OA.dir-and-A'-of 0 a g tt .proj₂
  k  = A-dir-S-power a g tt .proj₁
ract {₀} (([] , e) , ([] , a)) S-gate =
  ε , (([] , e + - k) , ([] , a'))
  where
  g : Gen 1
  g  = gate₁ S-gate
  a' = OA.dir-and-A'-of 0 a g tt .proj₂
  k  = A-dir-S-power a g tt .proj₁
-- Width ≥ 2: read off the coset update from the (scaffolded) bottom-wire
-- ML' push.
ract {₁₊ n} ml x = ml'-bot-push ml x

------------------------------------------------------------------------
-- Soundness of the coset action

[_]ᶜ = [_]ᵐˡ'

-- ract-sound certifies the coset-table transition: for
-- (b' , c') = ract c b we have [ c ]ᶜ • [ b ]ʷ ≈ b' ↑ • [ c' ]ᶜ.
ract-sound : ∀ {n} c b →
  let
    open PB ((₁₊ n) QRel,_===_)
    (b' , c') = ract {n} c b
  in

    [ c ]ᶜ • [ gate₁ b ]ʷ ≈ b' ↑ • [ c' ]ᶜ

-- Width 1: the bottom gate is absorbed by the A/E boxes with no upward
-- escape.  push-LM1 is stated over LM-Sym's boxes, whose A box differs
-- (as a function) from Section's; ML'T.abox-eq bridges them (E boxes are
-- definitionally S^(- ·) in both, so need no bridge).
ract-sound {₀} (([] , e) , ([] , a)) H-gate =
  trans (cleft (cright left-unit))
  (trans (cleft (cright (refl' (ML'T.abox-eq a))))
  (trans (push-LM1 e a g tt)
  (trans (cright (refl' (Eq.sym (ML'T.abox-eq a'))))
  (trans (cright (sym left-unit))
         (sym left-unit)))))
  where
  open PB (1 QRel,_===_)
  open PP (1 QRel,_===_)
  g : Gen 1
  g  = gate₁ H-gate
  a' = OA.dir-and-A'-of 0 a g tt .proj₂
ract-sound {₀} (([] , e) , ([] , a)) S-gate =
  trans (cleft (cright left-unit))
  (trans (cleft (cright (refl' (ML'T.abox-eq a))))
  (trans (push-LM1 e a g tt)
  (trans (cright (refl' (Eq.sym (ML'T.abox-eq a'))))
  (trans (cright (sym left-unit))
         (sym left-unit)))))
  where
  open PB (1 QRel,_===_)
  open PP (1 QRel,_===_)
  g : Gen 1
  g  = gate₁ S-gate
  a' = OA.dir-and-A'-of 0 a g tt .proj₂
-- Width ≥ 2: soundness is exactly the (scaffolded) bottom-wire ML' push.
ract-sound {₁₊ n} ml x = lemma-ML'-Bot ml x
