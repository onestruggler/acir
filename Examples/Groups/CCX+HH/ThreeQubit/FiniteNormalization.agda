------------------------------------------------------------------------
-- Presentations of groups
--
-- A finite normal-form table as an auxiliary presentation for Clement
-- translation.  The only axioms are its initial state and letter steps.
-- No matrix equality is used as a target axiom.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Presentation.Base as PB

module Examples.Groups.CCX+HH.ThreeQubit.FiniteNormalization
  {B Y N : Set} (Δ : WRel Y) (e : B → Word Y)
  (I : N) (section : N → Word B) (step : B → N → N)
  (initial : PB._≈_ Δ ((e ʷ) (section I)) ε)
  (factor : ∀ g n → PB._≈_ Δ
    (e g • (e ʷ) (section n)) ((e ʷ) (section (step g n))))
  (separate : ∀ {n m} → PB._≈_ Δ
    ((e ʷ) (section n)) ((e ʷ) (section m)) → n ≡ m)
  where

import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

private module A = PB Δ

encode : Word B → Word Y
encode = e ʷ

infix 4 _===_
data _===_ : WRel B where
  start : section I === ε
  table : ∀ g n → [ g ]ʷ • section n === section (step g n)

open PB _===_ public using (_≈_)
private
  module P = PB _===_
  module Q = PP _===_

run : N → Word B → N
run n [ g ]ʷ = step g n
run n ε = n
run n (u • v) = run (run n v) u

nf : Word B → N
nf = run I

encode-axiom : ∀ {u v} → u === v → encode u A.≈ encode v
encode-axiom start = initial
encode-axiom (table g n) = factor g n

encode-cong : ∀ {u v} → u ≈ v → encode u A.≈ encode v
encode-cong = PP.StarCongruence.fʷ-cong _===_ Δ e encode-axiom

module _ where
  open SR Q.word-setoid hiding (start)

  normalize-from : ∀ w n → w • section n ≈ section (run n w)
  normalize-from [ g ]ʷ n = P.axiom (table g n)
  normalize-from ε n = P.left-unit
  normalize-from (u • v) n = begin
    (u • v) • section n              ≈⟨ P.assoc ⟩
    u • (v • section n)              ≈⟨ P.cong P.refl (normalize-from v n) ⟩
    u • section (run n v)            ≈⟨ normalize-from u (run n v) ⟩
    section (run (run n v) u)        ∎

  normalize : ∀ w → w ≈ section (nf w)
  normalize w = begin
    w                               ≈⟨ P.sym P.right-unit ⟩
    w • ε                           ≈⟨ P.cong P.refl (P.sym (P.axiom start)) ⟩
    w • section I                   ≈⟨ normalize-from w I ⟩
    section (nf w)                  ∎

encode-injective : ∀ {u v} → encode u A.≈ encode v → u ≈ v
encode-injective {u} {v} uv =
  P.trans (normalize u) (P.trans (P.refl' (Eq.cong section same)) (P.sym (normalize v)))
  where
  same : nf u ≡ nf v
  same = separate (A.trans (A.sym (encode-cong (normalize u)))
    (A.trans uv (encode-cong (normalize v))))
