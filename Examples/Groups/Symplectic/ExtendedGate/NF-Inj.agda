-- Part of the Examples.Groups.Symplectic.ExtendedGate.NF-Inj split (memory-reduced typechecking).
-- --safe omitted while the 4 head-injectivity lemmas remain postulated.
-- (call-by-need: --call-by-name omitted; these proof-heavy modules typecheck
--  far faster and with less memory under the default sharing strategy.)
{-# OPTIONS --cubical-compatible --termination-depth=4 #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.PropositionalEquality as Eq


open import Function using (_∘_ ; id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
open import Data.Bool hiding (_<_ ; _≤_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)

open import Data.Maybe hiding (zipWith ; map)
open import Data.Sum using ([_,_] ; [_,_]′)
open import Data.Unit using (⊤ ; tt)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)


open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting using ()
open import Data.Nat.Primality



module Examples.Groups.Symplectic.ExtendedGate.NF-Inj (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime
open Symplectic-Derived-Gen renaming (M to ZM)
open import Examples.Groups.Symplectic.ExtendedGate.NF1 p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Action.ActionLemmas p-2 p-prime
open Normal-Form1

private
  variable
    n : ℕ
    
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Action.Properties p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Soundness p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import Examples.Groups.Symplectic.ExtendedGate.NF2 p-2 p-prime
open LM2
open ≡-Reasoning
open Eq hiding ([_])

open import Examples.Groups.Symplectic.ExtendedGate.NF p-2 p-prime using (act-nf)
open import Examples.Groups.Symplectic.ExtendedGate.NF-Inj-Base p-2 p-prime using (lemma-aux-vec)
open import Examples.Groups.Symplectic.ExtendedGate.NF-Inj-LM p-2 p-prime using (lemma-lm-head-inj ; lemma-lm-tail-surj)

-- The NF circuit word gives the same Pauli action as act-nf.
-- Proof: structural induction on NF n, using lemma-act-↑ for the lifting step.
lemma-act-nf : ∀ {n} (nf : NF n) → act [ nf ] ≗ act-nf nf
lemma-act-nf {₀} tt [] = auto
lemma-act-nf {₁₊ n} (ih , lm) ps =
  let s = act [ lm ]ˡᵐ ps in
  begin
    act [ (ih , lm) ] ps                          ≡⟨ auto ⟩
    act ([ ih ] ↑) (act [ lm ]ˡᵐ ps)             ≡⟨ Eq.cong (act ([ ih ] ↑)) (Eq.sym (lemma-aux-vec n s)) ⟩
    act ([ ih ] ↑) (head s ∷ tail s)              ≡⟨ lemma-act-↑ [ ih ] (head s) (tail s) ⟩
    head s ∷ act [ ih ] (tail s)                   ≡⟨ Eq.cong (head s ∷_) (lemma-act-nf ih (tail s)) ⟩
    head s ∷ act-nf ih (tail s)                    ≡⟨ auto ⟩
    act-nf (ih , lm) ps                            ∎



-- Distinct NFs have distinct Pauli actions.
--
-- Proof (structural induction on n):
--   Base (n=0): NF 0 = ⊤, trivial.
--   Step (n = 1+n'): Given (ih₁,lm₁) and (ih₂,lm₂) with act-nf (ih₁,lm₁) = act-nf (ih₂,lm₂).
--   Write G_i = act [lm_i]ˡᵐ and M_i = act-nf ih_i.  The hypothesis expands to
--     head(G_i ps) ∷ M_i(tail(G_i ps)) equal for i=1,2 at every ps.
--
--   Step 1 – lm₁ = lm₂: head(act-nf (ih,lm) ps) = head(act [lm]ˡᵐ ps) by computation,
--   so Eq.cong head (hyp ps) gives head(G₁ ps) = head(G₂ ps) for all ps.
--   lemma-lm-head-inj then yields lm₁ = lm₂.
--
--   Step 2 – ih₁ = ih₂ via IH: substitute lm₁ = lm₂ into hyp to get
--   M₁(tail(G ps)) = M₂(tail(G ps)) for all ps (where G = act [lm₁]ˡᵐ).
--   By surjectivity of tail ∘ G (lemma-lm-tail-surj), this holds on all of Pauli n',
--   so the IH gives ih₁ = ih₂.
lemma-nf-inj : ∀ {n} (nf₁ nf₂ : NF n) → act-nf nf₁ ≗ act-nf nf₂ → nf₁ ≡ nf₂
lemma-nf-inj {₀} tt tt _ = auto
lemma-nf-inj {₁₊ n} (ih₁ , lm₁) (ih₂ , lm₂) hyp = ≡×≡⇒≡ (ih-eq , lm-eq)
  where
  open ≡-Reasoning

  head-eq : ∀ ps → head (act [ lm₁ ]ˡᵐ ps) ≡ head (act [ lm₂ ]ˡᵐ ps)
  head-eq ps = Eq.cong head (hyp ps)

  lm-eq : lm₁ ≡ lm₂
  lm-eq = lemma-lm-head-inj lm₁ lm₂ head-eq

  -- Substitute lm₁ = lm₂ into hyp: RHS uses lm₂, Eq.sym lm-eq rewrites it to lm₁,
  -- giving M₁(tail(G ps)) ≡ M₂(tail(G ps)) on the tail component.
  tail-agree : ∀ ps → act-nf ih₁ (tail (act [ lm₁ ]ˡᵐ ps))
                     ≡ act-nf ih₂ (tail (act [ lm₁ ]ˡᵐ ps))
  tail-agree ps = Eq.cong tail
    (subst (λ lm' → head (act [ lm₁ ]ˡᵐ ps) ∷ act-nf ih₁ (tail (act [ lm₁ ]ˡᵐ ps))
                   ≡ head (act [ lm' ]ˡᵐ ps) ∷ act-nf ih₂ (tail (act [ lm' ]ˡᵐ ps)))
      (Eq.sym lm-eq) (hyp ps))

  ih-act-eq : act-nf ih₁ ≗ act-nf ih₂
  ih-act-eq qs =
    let (ps , eq) = lemma-lm-tail-surj lm₁ qs in begin
      act-nf ih₁ qs                           ≡⟨ Eq.cong (act-nf ih₁) (Eq.sym eq) ⟩
      act-nf ih₁ (tail (act [ lm₁ ]ˡᵐ ps))   ≡⟨ tail-agree ps ⟩
      act-nf ih₂ (tail (act [ lm₁ ]ˡᵐ ps))   ≡⟨ Eq.cong (act-nf ih₂) eq ⟩
      act-nf ih₂ qs                           ∎

  ih-eq : ih₁ ≡ ih₂
  ih-eq = lemma-nf-inj ih₁ ih₂ ih-act-eq

