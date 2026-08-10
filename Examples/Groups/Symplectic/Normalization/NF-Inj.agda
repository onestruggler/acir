------------------------------------------------------------------------
-- Presentations of groups
--
-- Semantic injectivity of the symplectic normal form.
--
-- The normal-form embedding [_] : NF n → Circuit n is injective on the
-- symplectic action: distinct normal forms denote distinct symplectic
-- transformations.  This is the completeness crux for the qupit-Clifford
-- presentation.
--
-- The proof is the structural engine (act / act-nf / lemma-act-nf /
-- lemma-nf-inj).  Tail-surjectivity of the ML coset action is proved here
-- from the invertibility of the symplectic action; head-injectivity of
-- the ML coset action is imported from Normalization.LMHeadInj, where it
-- is proved outright.  The module is postulate-free and --safe.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.NF-Inj
  (p-2 : ℕ) (p-prime : Prime (2+ p-2))
  where

open import Data.Product using (_×_ ; _,_ ; ∃)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Vec using (Vec ; _∷_ ; [] ; head ; tail)
open import Function using (id)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≗_)

open import Notations
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (Pauli ; pI)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (Circuit ; Gen ; _↑)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime as Sem using (_≈ˢ_)
open Sem.Symplectic using (ap ; ap⁻¹ ; invʳ)
open Sem.Interpretation using (⟦_⟧ ; actg)
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime hiding (⟦_⟧)
import Examples.Groups.Symplectic.Normalization.LMHeadInj p-2 p-prime as LMHI

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The Pauli action of a circuit

-- act w = ap ⟦ w ⟧ : the linear symplectic action of the circuit w.  It
-- composes on the nose (act (w • v) = act w ∘ act v) and reads a single
-- generator as actg.
act : ∀ {n} → Circuit n → Pauli n → Pauli n
act w = ap ⟦ w ⟧

-- Shifting a circuit up one wire leaves the top wire untouched and acts
-- on the tail.  Structural induction on w; every case is definitional.
lemma-act-↑ : ∀ {n} (w : Circuit n) p ps → act (w ↑) (p ∷ ps) ≡ p ∷ act w ps
lemma-act-↑ [ g ]ʷ  p ps = Eq.refl
lemma-act-↑ ε       p ps = Eq.refl
lemma-act-↑ (w • v) p ps =
  Eq.trans (Eq.cong (act (w ↑)) (lemma-act-↑ v p ps))
           (lemma-act-↑ w p (act v ps))

------------------------------------------------------------------------
-- The Pauli action read directly off a normal form

-- act-nf peels the normal form one wire at a time: the ML coset factor
-- acts, the resulting head is fixed, and the inner NF acts on the tail.
act-nf : ∀ {n} → NF n → Pauli n → Pauli n
act-nf {0}    _        = id
act-nf {₁₊ n} (ih , lm) ps = head s ∷ act-nf ih (tail s)
  where s = act [ lm ]ᵐˡ ps

-- head/tail reconstruction of a non-empty vector.
lemma-aux-vec : ∀ {A : Set} n (v : Vec A (₁₊ n)) → head v ∷ tail v ≡ v
lemma-aux-vec ₀      (x ∷ v) = Eq.refl
lemma-aux-vec (₁₊ n) (x ∷ v) = Eq.refl

-- The circuit [ nf ] acts exactly as act-nf.  Structural induction on nf,
-- using lemma-act-↑ for the lifted prefix.
lemma-act-nf : ∀ {n} (nf : NF n) → act [ nf ] ≗ act-nf nf
lemma-act-nf {0}    _        [] = Eq.refl
lemma-act-nf {₁₊ n} (ih , lm) ps =
  let s = act [ lm ]ᵐˡ ps in
  begin
    act [ (ih , lm) ] ps               ≡⟨ Eq.refl ⟩
    act ([ ih ] ↑) s                   ≡⟨ Eq.cong (act ([ ih ] ↑)) (Eq.sym (lemma-aux-vec n s)) ⟩
    act ([ ih ] ↑) (head s ∷ tail s)   ≡⟨ lemma-act-↑ [ ih ] (head s) (tail s) ⟩
    head s ∷ act [ ih ] (tail s)       ≡⟨ Eq.cong (head s ∷_) (lemma-act-nf ih (tail s)) ⟩
    head s ∷ act-nf ih (tail s)        ≡⟨ Eq.refl ⟩
    act-nf (ih , lm) ps                ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The gate-arithmetic crux (proved)
--
-- Head-injectivity of the ML coset action: two coset representatives that
-- agree on every head output are equal.  This is the combinatorial heart
-- of completeness, proved outright in Normalization.LMHeadInj (width-1
-- base in Normalization.NF1HeadInj; the width induction, the
-- inj₁ ≁ inj₂ separation, and the box-parameter recovery all
-- machine-checked, --safe).

lemma-lm-head-inj : ∀ {n} (lm₁ lm₂ : ML (₁₊ n)) →
  (∀ (ps : Pauli (₁₊ n)) → head (act [ lm₁ ]ᵐˡ ps) ≡ head (act [ lm₂ ]ᵐˡ ps)) → lm₁ ≡ lm₂
lemma-lm-head-inj = LMHI.lemma-lm-head-inj-proved

-- tail ∘ act [ lm ]ᵐˡ is surjective onto Pauli n.  No coset structure is
-- needed: act [ lm ]ᵐˡ = ap ⟦ [ lm ]ᵐˡ ⟧ is a bijection (the Symplectic
-- record carries its inverse ap⁻¹), so pI ∷ qs has the preimage
-- ap⁻¹ ⟦ [ lm ]ᵐˡ ⟧ (pI ∷ qs), whose action's tail is qs.
lemma-lm-tail-surj : ∀ {n} (lm : ML (₁₊ n)) (qs : Pauli n) →
  ∃ λ (ps : Pauli (₁₊ n)) → tail (act [ lm ]ᵐˡ ps) ≡ qs
lemma-lm-tail-surj {n} lm qs =
  ap⁻¹ ⟦ [ lm ]ᵐˡ ⟧ (pI ∷ qs) , Eq.cong tail (invʳ ⟦ [ lm ]ᵐˡ ⟧ (pI ∷ qs))

------------------------------------------------------------------------
-- Injectivity of act-nf, hence of [_] on the symplectic action

-- Distinct normal forms have distinct actions.  Structural induction on n:
--   * the coset factor lm is recovered from head outputs (lemma-lm-head-inj);
--   * with lm fixed, the inner NFs agree on the whole of Pauli n by
--     surjectivity of tail ∘ act [ lm ]ᵐˡ (lemma-lm-tail-surj), so the
--     induction hypothesis applies.
lemma-nf-inj : ∀ {n} (nf₁ nf₂ : NF n) → act-nf nf₁ ≗ act-nf nf₂ → nf₁ ≡ nf₂
lemma-nf-inj {0}    _ _ _ = Eq.refl
lemma-nf-inj {₁₊ n} (ih₁ , lm₁) (ih₂ , lm₂) hyp = ≡×≡⇒≡ (ih-eq , lm-eq)
  where
  open Eq.≡-Reasoning

  head-eq : ∀ (ps : Pauli (₁₊ n)) → head (act [ lm₁ ]ᵐˡ ps) ≡ head (act [ lm₂ ]ᵐˡ ps)
  head-eq ps = Eq.cong head (hyp ps)

  lm-eq : lm₁ ≡ lm₂
  lm-eq = lemma-lm-head-inj {n} lm₁ lm₂ head-eq

  -- Substitute lm₁ = lm₂ into hyp, then project the tail component.
  tail-agree : ∀ (ps : Pauli (₁₊ n)) → act-nf ih₁ (tail (act [ lm₁ ]ᵐˡ ps))
                     ≡ act-nf ih₂ (tail (act [ lm₁ ]ᵐˡ ps))
  tail-agree ps = Eq.cong tail
    (Eq.subst (λ lm' → head (act [ lm₁ ]ᵐˡ ps) ∷ act-nf ih₁ (tail (act [ lm₁ ]ᵐˡ ps))
                     ≡ head (act [ lm' ]ᵐˡ ps) ∷ act-nf ih₂ (tail (act [ lm' ]ᵐˡ ps)))
      (Eq.sym lm-eq) (hyp ps))

  ih-act-eq : act-nf ih₁ ≗ act-nf ih₂
  ih-act-eq qs =
    let (ps , eq) = lemma-lm-tail-surj {n} lm₁ qs in
    begin
      act-nf ih₁ qs                          ≡⟨ Eq.cong (act-nf ih₁) (Eq.sym eq) ⟩
      act-nf ih₁ (tail (act [ lm₁ ]ᵐˡ ps))   ≡⟨ tail-agree ps ⟩
      act-nf ih₂ (tail (act [ lm₁ ]ᵐˡ ps))   ≡⟨ Eq.cong (act-nf ih₂) eq ⟩
      act-nf ih₂ qs                          ∎

  ih-eq : ih₁ ≡ ih₂
  ih-eq = lemma-nf-inj ih₁ ih₂ ih-act-eq

-- The completeness crux: the normal-form embedding is injective for the
-- symplectic semantics.
⟦[]⟧-injective : ∀ {n} (u v : NF n) → ⟦ [ u ] ⟧ ≈ˢ ⟦ [ v ] ⟧ → u ≡ v
⟦[]⟧-injective u v eq = lemma-nf-inj u v aeq
  where
  aeq : act-nf u ≗ act-nf v
  aeq ps = Eq.trans (Eq.sym (lemma-act-nf u ps))
                    (Eq.trans (eq ps) (lemma-act-nf v ps))
