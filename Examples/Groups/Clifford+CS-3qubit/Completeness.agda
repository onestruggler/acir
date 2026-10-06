------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
--
-- The original was checked with --call-by-name, which saved memory
-- while the rewrite loops of Presentation.Tactics.Words returned their
-- unevaluated argument.  With those loops fixed, call-by-name only
-- loses sharing, and the default call-by-need is much faster.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- This module contains the proof of completeness.

open import Presentation.Tactics.Equality as Eq using (_≡_; auto)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Word.Base
open import Presentation.Tactics.Judgement

open import Presentation.Tactics.Lists
open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open import Presentation.Tactics.Words
open import Presentation.Tactics.Reidemeister-Schreier

module Examples.Groups.Clifford+CS-3qubit.Completeness where


open import Examples.Groups.Clifford+CS-3qubit.TwoLevel-Lemmas as TwoLevel-Lemmas
open TwoLevel-Rewrite-Twolevel
module TRT2 = TwoLevel-Rewrite-Twolevel2
module TRT3 = TwoLevel-Rewrite-Twolevel3
open Inverse-TwoLevel

open import Examples.Groups.Clifford+CS-3qubit.Gate as Gate


import Examples.Groups.Clifford+CS-3qubit.Step1.Theorem as Step1
import Examples.Groups.Clifford+CS-3qubit.Step2.Theorem as Step2
import Examples.Groups.Clifford+CS-3qubit.Step3.Main as Step3
import Examples.Groups.Clifford+CS-3qubit.Step4.Main as Step4
import Examples.Groups.Clifford+CS-3qubit.Step5.Main as Step5
import Examples.Groups.Clifford+CS-3qubit.Step6.Main as Step6
import Examples.Groups.Clifford+CS-3qubit.Step7.Main as Step7
import Examples.Groups.Clifford+CS-3qubit.Step8.Main as Step8


open import Examples.Groups.Clifford+CS-3qubit.Theorem as Theorem using (module TwoLevel ; module CliffordCS ; completeness-property)
open Step1 using (module TwoLevel-Less)
open Step2 using (module TwoLevel-Simplified)
open Step3 using (Cosets ; I ; I₁)

open import Examples.Groups.Clifford+CS-3qubit.Step1.Completeness renaming (hypA to Step1-hypA ; hypB to Step1-hypB ; g to Step1-g) hiding (completeness)
open import Examples.Groups.Clifford+CS-3qubit.Step2.Completeness renaming (hypA to Step2-hypA ; hypB to Step2-hypB) hiding (completeness)

Gen0 = TwoLevel.Gen
Rel0 = TwoLevel.Rel

Gen1 = TwoLevel-Less.Gen
Rel1 = TwoLevel-Less.Rel

Gen2 = TwoLevel-Simplified.Gen
Rel2 = TwoLevel-Simplified.Rel

import Examples.Groups.Clifford+CS-3qubit.Step3.Rel as R3
import Examples.Groups.Clifford+CS-3qubit.Step4.Rel as R4
import Examples.Groups.Clifford+CS-3qubit.Step5.Rel as R5
import Examples.Groups.Clifford+CS-3qubit.Step6.Rel as R6
import Examples.Groups.Clifford+CS-3qubit.Step7.Rel as R7

Gen3 = Gate.Gate
Rel3 = R3.Rel

Gen4 = Gen3
Rel4 = R4.Rel

Gen5 = Gen3
Rel5 = R5.Rel

Gen6 = Gen3
Rel6 = R6.Rel

Gen7 = Gen3
Rel7 = R7.Rel

Gen8 = CliffordCS.Gen
Rel8 = CliffordCS.Rel

f01 = Step1.f
f10 = Step1-g

f12 = Step2.f
f21 = Step2.g

f23 = Step3.h
f32 = Step3.simple-of-gate-gen

f34 = Step4.simple-of-gen
f43 = Step4.gen-of-simple

f45 = Step5.simple-of-gen
f54 = Step5.gen-of-simple

f56 = Step6.simple-of-gen
f65 = Step6.gen-of-simple

f67 = Step7.simple-of-gen
f76 = Step7.gen-of-simple

f78 = Step8.simple-of-gen
f87 = Step8.gen-of-simple


module S012 = Reidemeister-Schreier-SS {Gen0} {Rel0} {Gen1} {Rel1} {Gen2} {Rel2} f10 f01 f21 f12 Step1-hypA (\ x y -> Step1-hypB {x} {y}) Step2-hypA Step2-hypB

module S013 = Reidemeister-Schreier-FS {Gen0} {Rel0} {Gen2} {Rel2} {Gen3} {Rel3} Cosets I S012.hf S012.gk f23 f32 S012.hypA3 S012.hypB3 Step3.hypA Step3.hypB
module S345 = Reidemeister-Schreier-SS {Gen3} {Rel3} {Gen4} {Rel4} {Gen5} {Rel5} f34 f43 f45 f54 Step4.hypA ( \x y -> Step4.hypB {x} {y}) Step5.hypA ( \ x y -> Step5.hypB {x} {y})
module S567 = Reidemeister-Schreier-SS {Gen5} {Rel5} {Gen6} {Rel6} {Gen7} {Rel7} f56 f65 f67 f76 Step6.hypA ( \ x y -> Step6.hypB {x} {y}) Step7.hypA ( \x y -> Step7.hypB {x} {y})
--module S678 = Reidemeister-Schreier-SS {Gen6} {Rel6} {Gen7} {Rel7} {Gen8} {Rel8} f67 f76 f78 f87 Step7.hypA ( \ x y -> Step7.hypB {x} {y}) Step8.hypA ( \x y -> Step8.hypB {x} {y})
module S357 = Reidemeister-Schreier-SS {Gen3} {Rel3} {Gen5} {Rel5} {Gen7} {R7.Rel} S345.hf S345.gk S567.hf S567.gk S345.hypA3 S345.hypB3 S567.hypA3 S567.hypB3
module S378 = Reidemeister-Schreier-SS {Gen3} {Rel3} {Gen7} {Rel7} {CliffordCS.Gen} {CliffordCS.Rel} S357.hf S357.gk f78 f87 S357.hypA3 S357.hypB3 Step8.hypA (\ x y -> Step8.hypB {x} {y})
module S038 = Reidemeister-Schreier-SF {TwoLevel.Gen} {TwoLevel.Rel} {Gen3} {Rel3} {CliffordCS.Gen} {CliffordCS.Rel} Cosets I S013.hf S013.gk S378.hf S378.gk S013.hypA3 S013.hypB3 S378.hypA3 S378.hypB3

open S038


open import Examples.Groups.Clifford+CS-3qubit.Step2.TwoLevel-Simplified-Lemmas
open Associative
open Monoid-Equational
open import Examples.Groups.Clifford+CS-3qubit.Step1.Soundness
import Examples.Groups.Clifford+CS-3qubit.Step2.Soundness as T2S

module S234 = Reidemeister-Schreier-SF {Gen2} {Rel2} {Gen3} {Rel3} {Gen4} {Rel4} Cosets I f23 f32 f34 f43  Step3.hypA (Step3.hypB) Step4.hypA (\ x y -> Step4.hypB {x} {y})

module S12' = Reidemeister-Schreier-Simplified {Gen2} {Rel2} {Gen1} {Rel1} f12 f21 Step2-hypA Step2-hypB
module S012' = Reidemeister-Schreier-SS {TwoLevel.Gen} {TwoLevel.Rel} {Gen1} {Rel1} {Gen2} {Rel2} f01 f01 f21 f12 Step1-hypA (\ x y -> Step1-hypB {x} {y}) Step2-hypA Step2-hypB

normalize-tlxs : Word TwoLevel.Gen -> Word TwoLevel.Gen
normalize-tlxs w = (S012'.gk ʷ) (word-of-list (TRn.multistep 200 (list-of-word ((S012'.hf ʷ) w))))

lemma-id* : ∀ {x} -> (f01 ʷ) x ≡ x
lemma-id* {[ TwoLevel.i-gen x ]ʷ} = _≡_.refl
lemma-id* {[ TwoLevel.X-gen jk ]ʷ} = _≡_.refl
lemma-id* {[ TwoLevel.K-gen jk ]ʷ} = _≡_.refl
lemma-id* {ε} = _≡_.refl
lemma-id* {x • x₁} with lemma-id* {x} | lemma-id* {x₁}
... | h1 | h2 = Eq.cong₂ _•_ h1 h2

open import Examples.Groups.Clifford+CS-3qubit.Index as Index

lemma-aux00 : ∀ {w} -> TwoLevel.Rel ⊢ w === (f12 ʷ) ((f21 ʷ) w)
lemma-aux00 {[ TwoLevel.i-gen Index.Index.₀ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.i-gen Index.Index.₁ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.i-gen Index.Index.₂ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.i-gen Index.Index.₃ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.i-gen Index.Index.₄ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.i-gen Index.Index.₅ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.i-gen Index.Index.₆ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.i-gen Index.Index.₇ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₀₁ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₀₂ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₀₃ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₀₄ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₀₅ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₀₆ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₀₇ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₁₂ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₁₃ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₁₄ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₁₅ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₁₆ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₁₇ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₂₃ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₂₄ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₂₅ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₂₆ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₂₇ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₃₄ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₃₅ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₃₆ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₃₇ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₄₅ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₄₆ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₄₇ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₅₆ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₅₇ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.X-gen ₆₇ ]ʷ} = TRT2.rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₀₁ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₀₂ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₀₃ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₀₄ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₀₅ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₀₆ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₀₇ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₁₂ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₁₃ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₁₄ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₁₅ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₁₆ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₁₇ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₂₃ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₂₄ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₂₅ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₂₆ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₂₇ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₃₄ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₃₅ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₃₆ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₃₇ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₄₅ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₄₆ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₄₇ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₅₆ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₅₇ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {[ TwoLevel.K-gen ₆₇ ]ʷ} = rewrite-twolevel 100 auto
lemma-aux00 {ε} = rewrite-twolevel 100 auto
lemma-aux00 {w • w'} with lemma-aux00 {w} | lemma-aux00 {w'}
... | h1 | h2 = cong h1 h2



lemma-normalize-tlxs : ∀ (w : Word TwoLevel.Gen) -> TwoLevel.Rel ⊢ w === normalize-tlxs w
lemma-normalize-tlxs w = symm (
  equational normalize-tlxs w
    by refl
  equals (S012'.gk ʷ) (word-of-list (TRn.multistep 200 (list-of-word ((S012'.hf ʷ) w))))
    by refl' (lemma-*-* f12 f01 ((word-of-list (TRn.multistep 200 (list-of-word ((S012'.hf ʷ) w)))))) reversed
  equals (f01 ʷ) ((f12 ʷ) (word-of-list (TRn.multistep 200 (list-of-word ((S012'.hf ʷ) w)))))
    by soundness (T2S.soundness (TRn.lemma-multistep 200 (list-of-word ((S012'.hf ʷ) w)))) reversed
  equals (f01 ʷ) ((f12 ʷ) ( ( word-of-list (list-of-word ((S012'.hf ʷ) w)))))
    by soundness (T2S.soundness (lemma-list-of-word ((S012'.hf ʷ) w))) reversed
  equals (f01 ʷ) ((f12 ʷ) ( (  ( ((S012'.hf ʷ) w)))))
    by soundness (T2S.soundness (refl' (lemma-*-* f10 f21 w))) reversed
  equals (f01 ʷ) ((f12 ʷ) (  (f21 ʷ) ((f10 ʷ) w)))
    by soundness (T2S.soundness (S12'.lemma-b (refl' (Eq.sym (lemma-id* {w}))))) reversed
  equals (f01 ʷ) ((f12 ʷ) (  (f21 ʷ) ( w)))
    by refl' (lemma-id* {((f12 ʷ) (  (f21 ʷ) ( w)))})
  equals (f12 ʷ) ((f21 ʷ) w)
    by lemma-aux00 {w} reversed
  equals w
  )

open Rewriting
open import Examples.Groups.Clifford+CS-3qubit.CosetNF

module BC2 = Basis-Change-With-Standardization TwoLevel-Lemmas.group-like (TwoLevel-Step-Order.step then TwoLevel-Step-Twolevel.step then TwoLevel-Step-Twolevel.X-step) Commuting-TwoLevel.comm-canonical Commuting-TwoLevel.lemma-comm-canonical

module BC4 = Basis-Change-With-Standardization TwoLevel-Lemmas.group-like (TwoLevel-Step-Twolevel.step) (Legacy.listf-of-f normalize-tlxs) (Legacy.lemma-listf-of-f lemma-normalize-tlxs)
module TRT4 = Step-With-Standardization (step-cong (TwoLevel-Step-Order.step then TwoLevel-Step-Twolevel.step)) (Legacy.listf-of-f normalize-tlxs) (Legacy.lemma-listf-of-f lemma-normalize-tlxs) renaming (general-rewrite to rewrite-twolevel)

open Commuting-TwoLevel

lemma-f : ∀ (x : CliffordCS.Gen) -> TwoLevel.Rel ⊢ Theorem.f x === S038.gk x
lemma-f CliffordCS.S0-gen = rewrite-twolevel 100 auto
lemma-f CliffordCS.S1-gen = rewrite-twolevel 100 auto
lemma-f CliffordCS.S2-gen = rewrite-twolevel 100 auto
lemma-f CliffordCS.CS01-gen = rewrite-twolevel 100 auto
lemma-f CliffordCS.CS12-gen = rewrite-twolevel 100 auto
lemma-f CliffordCS.iI-gen = rewrite-twolevel 100 auto
lemma-f CliffordCS.K0-gen = rewrite-twolevel 100 auto
lemma-f CliffordCS.K2-gen = aux
  where
    open TwoLevel
    
    aux :  Rel ⊢ K ₀₁ • K ₂₃ • K ₄₅ • K ₆₇ === gk CliffordCS.K2-gen
    aux =
      equational K ₀₁ • K ₂₃ • K ₄₅ • K ₆₇
        by rewrite-twolevel 50 auto
      equals (X ₃₆ • X ₁₄) • (K ₀₄ • K ₁₅ • K ₂₆ • K ₃₇) • X ₃₆ • X ₁₄
        by right left lemma-f CliffordCS.K0-gen
      equals (X ₃₆ • X ₁₄) • (gk CliffordCS.K0-gen) • X ₃₆ • X ₁₄
        by right-unit reversed
      equals ((X ₃₆ • X ₁₄) • (gk CliffordCS.K0-gen) • X ₃₆ • X ₁₄) • ε
        by right lemma-normalize-tlxs (X ₁₂ • X ₃₄ • X ₂₃ • X ₃₄ • X ₅₆ • X ₄₅ • X ₃₄ • X ₄₅ • X ₃₄ • X ₂₃ • X ₁₂ • X ₃₄ • X ₄₅ • X ₃₄ • X ₄₅ • X ₅₆) reversed
      equals ((X ₃₆ • X ₁₄) • (gk CliffordCS.K0-gen) • X ₃₆ • X ₁₄) • X ₁₂ • X ₃₄ • X ₂₃ • X ₃₄ • X ₅₆ • X ₄₅ • X ₃₄ • X ₄₅ • X ₃₄ • X ₂₃ • X ₁₂ • X ₃₄ • X ₄₅ • X ₃₄ • X ₄₅ • X ₅₆
        by rewrite-twolevel 100 auto
      equals gk CliffordCS.K2-gen
lemma-f CliffordCS.K1-gen = aux2
  where
    open TwoLevel

    aux2 :  Rel ⊢ K ₀₂ • K ₁₃ • K ₄₆ • K ₅₇ === gk CliffordCS.K1-gen
    aux2 =
      equational K ₀₂ • K ₁₃ • K ₄₆ • K ₅₇
        by right-unit reversed
      equals (K ₀₂ • K ₁₃ • K ₄₆ • K ₅₇) • ε
        by right lemma-normalize-tlxs (X ₃₄ • X ₂₃ • X ₃₄ • X ₄₅ • X ₃₄ • X ₄₅ • X ₃₄ • X ₂₃ • X ₃₄ • X ₄₅ • X ₃₄ • X ₄₅) reversed
      equals (K ₀₂ • K ₁₃ • K ₄₆ • K ₅₇) • (X ₃₄ • X ₂₃ • X ₃₄ • X ₄₅ • X ₃₄ • X ₄₅ • X ₃₄ • X ₂₃ • X ₃₄ • X ₄₅ • X ₃₄ • X ₄₅)
        by rewrite-twolevel 100 auto
      equals gk CliffordCS.K1-gen


lemma-f* : ∀ (x : Word CliffordCS.Gen) -> TwoLevel.Rel ⊢ (Theorem.f ʷ) x === (S038.gk ʷ) x
lemma-f* ([ x ]ʷ) = lemma-f x
lemma-f* ε = refl
lemma-f* (w • w') with lemma-f* w | lemma-f* w'
... | h1 | h2 = cong h1 h2

completeness : completeness-property
completeness {w} {v} hyp = S038.reidemeister-schreier w v hyp'
  where
    hyp' : TwoLevel.Rel ⊢ (S038.gk ʷ) w === (S038.gk ʷ) v
    hyp' =
      equational (S038.gk ʷ) w
        by lemma-f* w reversed
      equals (Theorem.f ʷ) w
        by hyp
      equals (Theorem.f ʷ) v
        by lemma-f* v
      equals (S038.gk ʷ) v

