------------------------------------------------------------------------
-- Presentations of groups
--
-- The spare wire of a control, as vector operators: ctrl C one wire
-- up, brought down by the swap of wires 0 1, acts as ctrl₁ C.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.SpareSem where

open import Data.Nat.Base using (ℕ ; suc ; _^_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (_•_)
open import Notations using (₄₊)

import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ ; τ-↑ ; interpret)
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (ctrl)
open import Examples.Groups.CCX+HH.NaturalP.CtrlPad using (ctrl₁)
open import Examples.Groups.CCX+HH.NaturalP.CtrlSem using (ctrl-sem ; conj₀)
open import Examples.Groups.CCX+HH.NaturalP.CtrlSame using (ctrl₁-sem)
open import Examples.Groups.CCX+HH.NaturalP.Blocks2 using (Op ; ctrlA)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum)
open import Examples.Groups.CCX+HH.GeneralN.ActionSemantics using (action⇒matrix)

private
  variable
    n : ℕ

  -- The word, respelled.
  respell : (C : P.Circuit (₄₊ n)) →
    τ (P.σ • (ctrl C P.↑ • P.σ)) ≡ H.Ex {₄₊ n} • (τ (ctrl C) H.↑ • H.Ex {₄₊ n})
  respell {n} C = cong (λ c → H.Ex {₄₊ n} • (c • H.Ex {₄₊ n})) (τ-↑ (ctrl C))

  step₁ : (C : P.Circuit (₄₊ n)) → ∀ v →
    quantum (H.Ex {₄₊ n} • (τ (ctrl C) H.↑ • H.Ex {₄₊ n})) v ≡
    ctrlA (2 ^ suc (₄₊ n)) (Q.bottom {₄₊ n} (quantum (τ C))) v
  step₁ {n} C v = conj₀ (₄₊ n) (τ (ctrl C)) (quantum (τ C)) (ctrl-sem C) v

  step₂ : (C : P.Circuit (₄₊ n)) → ∀ v →
    ctrlA (2 ^ suc (₄₊ n)) (Q.bottom {₄₊ n} (quantum (τ C))) v ≡ quantum (τ (ctrl₁ C)) v
  step₂ C v = sym (ctrl₁-sem C v)


  -- An equation of actions, wrapped in a record: the words of a generic
  -- lemma are then solved from a signature rather than written in a
  -- clause body, where Agda elaborates them differently enough that
  -- comparing their actions means evaluating them.
  record QEq {k} (u v : H.Circuit k) : Set where
    field eq : ∀ x → quantum u x ≡ quantum v x

  am : ∀ {k} {u v : H.Circuit k} → QEq u v → Q.interpret u ≡ Q.interpret v
  am {u = u} {v} h = action⇒matrix {u = u} {v = v} (QEq.eq h)

  act : (C : P.Circuit (₄₊ n)) →
    QEq (H.Ex {₄₊ n} • (τ (ctrl C) H.↑ • H.Ex {₄₊ n})) (τ (ctrl₁ C))
  act C = record { eq = λ v → trans (step₁ C v) (step₂ C v) }

  mat : (C : P.Circuit (₄₊ n)) →
    Q.interpret (H.Ex {₄₊ n} • (τ (ctrl C) H.↑ • H.Ex {₄₊ n})) ≡ Q.interpret (τ (ctrl₁ C))
  mat C = am (act C)

  respell-mat : (C : P.Circuit (₄₊ n)) →
    Q.interpret (τ (P.σ • (ctrl C P.↑ • P.σ))) ≡
    Q.interpret (H.Ex {₄₊ n} • (τ (ctrl C) H.↑ • H.Ex {₄₊ n}))
  respell-mat C = cong Q.interpret (respell C)

spare-sem : (C : P.Circuit (₄₊ n)) →
  interpret (P.σ • (ctrl C P.↑ • P.σ)) ≡ interpret (ctrl₁ C)
spare-sem C = trans (respell-mat C) (mat C)
