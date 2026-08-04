------------------------------------------------------------------------
-- Presentations of groups
--
-- Surjectivity of the plain qupit-Clifford action onto the symplectic
-- group Sp(2n, ℤ/pℤ): every symplectic transformation S is the action of
-- some plain circuit w.
--
-- This is a DIRECT proof (no transport through the extended gate set).
-- The engine is `lemma-invnf`: every linear, sform-preserving map f has a
-- box normal form whose action `act-nf` inverts f.  The construction is
-- the standard "clear the top wire, recurse on the tail":
--
--   * plain `act w = ap ⟦ w ⟧` is linear and sform-preserving for free,
--     from the Symplectic record fields (linear-+, linear-*, preserves);
--   * `lemma-fundamental'` clears the top wire — given a symplectic f it
--     produces an ML coset box lm with act [ lm ]ᵐˡ (f pZ₀) = pZ₀ and
--     act [ lm ]ᵐˡ (f pX₀) = pX₀ — via the single-level `Theorem-LM`;
--   * the residual `act [ lm ]ᵐˡ ∘ f` then fixes Z₀/X₀, so it acts as the
--     identity on the top wire and a smaller linear symplectic map on the
--     tail (Linear-Symp-FixZX⇒FixP / Linear-Symp-⇒FixP⇒), and the
--     induction hypothesis applies.
--
-- The whole reduction is proved here.  The one remaining gate-specific
-- input is `Theorem-LM` (the single-level box existence), postulated: the
-- base cases already exist as Examples.Groups.Symplectic.NF1-Sym.Theorem-NF1
-- (n = 1) and NF2-Sym.Theorem-LM2 (n = 2); only the top-level recursion,
-- together with matching those files' `act = dact ∘ der` to `ap ⟦_⟧`,
-- remains to be assembled.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --termination-depth=2 #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Surjectivity (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (Vec ; [] ; _∷_ ; head ; tail)
open import Function using (_∘_ ; id)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≗_ ; module ≡-Reasoning)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

open import Examples.Groups.Pauli.Semantics p-2 p-prime

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (Circuit ; Gen ; _↑)

open import Examples.Groups.Symplectic.Semantics p-2 p-prime as Sem
  using (_≈ˢ_ ; _∘ˢ_ ; _⁻¹ˢ)
open Sem.Symplectic using (ap ; ap⁻¹ ; invˡ ; linear-+ ; linear-* ; preserves)
open Sem.Interpretation using (⟦_⟧)

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  using (NF ; [_] ; [_]ᵐˡ ; ML)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Linear and symplectic predicates on a Pauli map

IsLinear : ∀ {n} (f : Pauli n → Pauli n) → Set
IsLinear f =
  (∀ ps qs → f (ps +ₚ qs) ≡ f ps +ₚ f qs) ×
  (∀ k ps → f (k *ₚ ps) ≡ k *ₚ f ps)

IsSymp : ∀ {n} (f : Pauli n → Pauli n) → Set
IsSymp {n} f = ∀ ps qs → sform (f ps) (f qs) ≡ sform ps qs

Fix-Z₀-X₀ : ∀ {n} (f : Pauli (₁₊ n) → Pauli (₁₊ n)) → Set
Fix-Z₀-X₀ f = f pZ₀ ≡ pZ₀ × f pX₀ ≡ pX₀

Fix-P₀ : ∀ {n} (f : Pauli (₁₊ n) → Pauli (₁₊ n)) → Set
Fix-P₀ f = ∀ p ps → f (p ∷ ps) ≡ p ∷ tail (f (pI ∷ ps))

------------------------------------------------------------------------
-- The Pauli action of a circuit is linear and symplectic — for free,
-- from the Symplectic record carried by ⟦ w ⟧.

act : ∀ {n} → Circuit n → Pauli n → Pauli n
act w = ap ⟦ w ⟧

actw-linear : ∀ {n} (w : Circuit n) → IsLinear (act w)
actw-linear w = linear-+ ⟦ w ⟧ , linear-* ⟦ w ⟧

actw-symp : ∀ {n} (w : Circuit n) → IsSymp (act w)
actw-symp w = preserves ⟦ w ⟧

------------------------------------------------------------------------
-- The Pauli action read off a normal form (as in Normalization.NF-Inj)

act-nf : ∀ {n} → NF n → Pauli n → Pauli n
act-nf {0}    tt        = id
act-nf {₁₊ n} (ih , lm) ps = head s ∷ act-nf ih (tail s)
  where s = act [ lm ]ᵐˡ ps

lemma-act-↑ : ∀ {n} (w : Circuit n) p ps → act (w ↑) (p ∷ ps) ≡ p ∷ act w ps
lemma-act-↑ [ g ]ʷ  p ps = Eq.refl
lemma-act-↑ ε       p ps = Eq.refl
lemma-act-↑ (w • v) p ps =
  Eq.trans (Eq.cong (act (w ↑)) (lemma-act-↑ v p ps)) (lemma-act-↑ w p (act v ps))

lemma-aux-vec : ∀ {A : Set} n (v : Vec A (₁₊ n)) → head v ∷ tail v ≡ v
lemma-aux-vec ₀      (x ∷ v) = Eq.refl
lemma-aux-vec (₁₊ n) (x ∷ v) = Eq.refl

lemma-act-nf : ∀ {n} (nf : NF n) → act [ nf ] ≗ act-nf nf
lemma-act-nf {0}    tt        [] = Eq.refl
lemma-act-nf {₁₊ n} (ih , lm) ps =
  let s = act [ lm ]ᵐˡ ps in
  begin
    act [ (ih , lm) ] ps               ≡⟨ Eq.refl ⟩
    act ([ ih ] ↑) s                   ≡⟨ Eq.cong (act ([ ih ] ↑)) (Eq.sym (lemma-aux-vec n s)) ⟩
    act ([ ih ] ↑) (head s ∷ tail s)   ≡⟨ lemma-act-↑ [ ih ] (head s) (tail s) ⟩
    head s ∷ act [ ih ] (tail s)       ≡⟨ Eq.cong (head s ∷_) (lemma-act-nf ih (tail s)) ⟩
    head s ∷ act-nf ih (tail s)        ≡⟨ Eq.refl ⟩
    act-nf (ih , lm) ps                ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Pauli-arithmetic helpers (gate-independent)

+₁-idˡ : ∀ p → p +₁ pI ≡ p
+₁-idˡ (a , b) = Eq.cong₂ _,_ (+-identityʳ a) (+-identityʳ b)

+ₚ-idˡ : ∀ {n} ps → pIₙ {n} +ₚ ps ≡ ps
+ₚ-idˡ {₀}    []       = Eq.refl
+ₚ-idˡ {₁₊ n} (x ∷ ps) =
  Eq.cong₂ _∷_ (Eq.cong₂ _,_ (+-identityˡ (x .proj₁)) (+-identityˡ (x .proj₂))) (+ₚ-idˡ ps)

+ₚ-idʳ : ∀ {n} ps → ps +ₚ pIₙ {n} ≡ ps
+ₚ-idʳ {₀}    []       = Eq.refl
+ₚ-idʳ {₁₊ n} (x ∷ ps) = Eq.cong₂ _∷_ (+₁-idˡ x) (+ₚ-idʳ ps)

*₁-zeroʳ : ∀ k → k *₁ pI ≡ pI
*₁-zeroʳ k = Eq.cong₂ _,_ (*-zeroʳ k) (*-zeroʳ k)

lemma-pauli-zero : ∀ {n} b → b *ₚ pIₙ {n} ≡ pIₙ {n}
lemma-pauli-zero {₀}    b = Eq.refl
lemma-pauli-zero {₁₊ n} b = Eq.cong₂ _∷_ (*₁-zeroʳ b) (lemma-pauli-zero b)

lemma-aux-px : ∀ {n} → pX ∷ pIₙ {n} ≡ pX₀
lemma-aux-px {₀}    = Eq.refl
lemma-aux-px {₁₊ n} = Eq.refl

lemma-aux-pz : ∀ {n} → pZ ∷ pIₙ {n} ≡ pZ₀
lemma-aux-pz {₀}    = Eq.refl
lemma-aux-pz {₁₊ n} = Eq.refl

lemma-aux-kx : ∀ {n} k → k *₁ pX ∷ pIₙ {n} ≡ k *ₚ pX₀
lemma-aux-kx {₀}    k = Eq.refl
lemma-aux-kx {₁₊ n} k = Eq.cong₂ _∷_ Eq.refl (Eq.sym (lemma-pauli-zero k))

lemma-aux-kz : ∀ {n} k → k *₁ pZ ∷ pIₙ {n} ≡ k *ₚ pZ₀
lemma-aux-kz {₀}    k = Eq.refl
lemma-aux-kz {₁₊ n} k = Eq.cong₂ _∷_ Eq.refl (Eq.sym (lemma-pauli-zero k))

pasXZ : ∀ (p : Pauli1) → ∃ λ a → ∃ λ b → p ≡ (a *₁ pX +₁ b *₁ pZ)
pasXZ (x , y) = x , y , claim
  where
  open ≡-Reasoning
  claim : (x , y) ≡ x *₁ pX +₁ y *₁ pZ
  claim = begin
    (x , y)                         ≡⟨ Eq.sym (Eq.cong₂ _,_ (*-identityʳ x) (*-identityʳ y)) ⟩
    (x * ₁ , y * ₁)                 ≡⟨ Eq.sym (Eq.cong₂ _,_ (+-identityʳ (x * ₁)) (+-identityˡ (y * ₁))) ⟩
    (x * ₁ + ₀ , ₀ + y * ₁)         ≡⟨ Eq.sym (Eq.cong₂ (λ u v → (x * ₁ + u , v + y * ₁)) (*-zeroʳ y) (*-zeroʳ x)) ⟩
    (x * ₁ + y * ₀ , x * ₀ + y * ₁) ≡⟨ Eq.refl ⟩
    x *₁ pX +₁ y *₁ pZ ∎

------------------------------------------------------------------------
-- sform helpers (gate-independent)

sform-pI-q=0 : ∀ (q : Pauli1) → sform1 pI q ≡ ₀
sform-pI-q=0 (c , d) = begin
  - ₀ * d + c * ₀ ≡⟨ Eq.cong₂ _+_ (Eq.trans (Eq.cong (_* d) -0#≈0#) (*-zeroˡ d)) (*-zeroʳ c) ⟩
  ₀ + ₀           ≡⟨ +-identityˡ ₀ ⟩
  ₀ ∎
  where open ≡-Reasoning

lemma-sform-pIₙ-q=0 : ∀ (p : Pauli n) → sform pIₙ p ≡ ₀
lemma-sform-pIₙ-q=0 []       = Eq.refl
lemma-sform-pIₙ-q=0 (q ∷ ps) =
  Eq.trans (Eq.cong₂ _+_ (sform-pI-q=0 q) (lemma-sform-pIₙ-q=0 ps)) (+-identityˡ ₀)

lemma-sform1-pIʳ : ∀ x → sform1 x pI ≡ ₀
lemma-sform1-pIʳ (a , b) =
  Eq.trans (Eq.cong₂ _+_ (*-zeroʳ (- a)) (*-zeroˡ b)) (+-identityˡ ₀)

lemma-alt : ∀ p → sform1 p p ≡ ₀
lemma-alt (a , b) = begin
  - a * b + a * b   ≡⟨ Eq.cong (_+ a * b) (Eq.sym (-‿distribˡ-* a b)) ⟩
  - (a * b) + a * b ≡⟨ +-inverseˡ (a * b) ⟩
  ₀ ∎
  where open ≡-Reasoning

lemma-sform-ZX1 : sform1 pZ pX ≡ ₁
lemma-sform-ZX1 = begin
  sform1 pZ pX     ≡⟨ Eq.refl ⟩
  - ₀ * ₀ + ₁ * ₁  ≡⟨ Eq.cong₂ _+_ (*-zeroʳ (- ₀)) (*-identityˡ ₁) ⟩
  ₀ + ₁            ≡⟨ +-identityˡ ₁ ⟩
  ₁ ∎
  where open ≡-Reasoning

lemma-aux-sformXZ : ∀ {n} → sform {₁₊ n} pZ₀ pX₀ ≡ ₁
lemma-aux-sformXZ {n} = begin
  sform1 pZ pX + sform {n} pIₙ pIₙ ≡⟨ Eq.cong (sform1 pZ pX +_) (lemma-sform-pIₙ-q=0 {n} pIₙ) ⟩
  sform1 pZ pX + ₀                 ≡⟨ +-identityʳ (sform1 pZ pX) ⟩
  sform1 pZ pX                     ≡⟨ lemma-sform-ZX1 ⟩
  ₁ ∎
  where open ≡-Reasoning

lemma-sform1-XZ : ∀ p → sform1 pZ p ≡ ₀ × sform1 pX p ≡ ₀ → p ≡ pI
lemma-sform1-XZ (c , d) (eq1 , eq2) = ≡×≡⇒≡ (aux , aux3a)
  where
  open ≡-Reasoning
  aux : c ≡ ₀
  aux = begin
    c              ≡⟨ Eq.sym (*-identityʳ c) ⟩
    c * ₁          ≡⟨ Eq.sym (+-identityˡ (c * ₁)) ⟩
    ₀ + c * ₁      ≡⟨ Eq.cong (_+ c * ₁) (Eq.sym (*-zeroˡ d)) ⟩
    ₀ * d + c * ₁  ≡⟨ Eq.cong (λ z → z * d + c * ₁) (Eq.sym -0#≈0#) ⟩
    - ₀ * d + c * ₁ ≡⟨ eq1 ⟩
    ₀ ∎
  aux2 : - d ≡ ₀
  aux2 = begin
    - d            ≡⟨ Eq.sym (-1*x≈-x d) ⟩
    - ₁ * d        ≡⟨ Eq.sym (+-identityʳ (- ₁ * d)) ⟩
    - ₁ * d + ₀    ≡⟨ Eq.cong (- ₁ * d +_) (Eq.sym (*-zeroʳ c)) ⟩
    - ₁ * d + c * ₀ ≡⟨ eq2 ⟩
    ₀ ∎
  aux3a : d ≡ ₀
  aux3a = Eq.trans (Eq.sym (-‿involutive d)) (Eq.trans (Eq.cong -_ aux2) -0#≈0#)

------------------------------------------------------------------------
-- The single-level box existence (the one gate-specific input)
--
-- Given a symplectic pair (p, q) — sform p q = 1 — there is an ML coset
-- box sending p to pZ₀ and q to pX₀.  Base cases exist as NF1-Sym.Theorem-NF1
-- and NF2-Sym.Theorem-LM2; the top-level recursion (and matching their
-- `act = dact ∘ der` to `ap ⟦_⟧`) is the remaining work.

open import Examples.Groups.Symplectic.TheoremLM p-2 p-prime using (Theorem-LM)

------------------------------------------------------------------------
-- Clearing the top wire, and the tail sub-map

lemma-fundamental' : ∀ {n} (f : Pauli (₁₊ n) → Pauli (₁₊ n)) → IsSymp f →
  ∃ λ (lm : ML (₁₊ n)) → act [ lm ]ᵐˡ (f pZ₀) ≡ pZ₀ × act [ lm ]ᵐˡ (f pX₀) ≡ pX₀
lemma-fundamental' {n} f hyp = Theorem-LM (f pZ₀) (f pX₀) aux
  where
  open ≡-Reasoning
  aux : sform (f pZ₀) (f pX₀) ≡ ₁
  aux = Eq.trans (hyp pZ₀ pX₀) (lemma-aux-sformXZ {n})

-- If f is linear + symplectic and fixes Z₀/X₀ then f(p ∷ pIₙ) = p ∷ pIₙ.
lemma-linear0' : ∀ {n} (f : Pauli (₁₊ n) → Pauli (₁₊ n)) →
  IsLinear f → Fix-Z₀-X₀ f → ∀ p → f (p ∷ pIₙ) ≡ p ∷ pIₙ
lemma-linear0' {n} f (fp , fm) (eqz , eqx) p = begin
  f (p ∷ pIₙ)                                   ≡⟨ Eq.cong (λ □ → f (□ ∷ pIₙ)) eq ⟩
  f (a *₁ pX +₁ b *₁ pZ ∷ pIₙ)                  ≡⟨ Eq.cong f (Eq.cong₂ _∷_ Eq.refl (Eq.sym (+ₚ-idˡ pIₙ))) ⟩
  f ((a *₁ pX ∷ pIₙ) +ₚ (b *₁ pZ ∷ pIₙ))        ≡⟨ fp (a *₁ pX ∷ pIₙ) (b *₁ pZ ∷ pIₙ) ⟩
  f (a *₁ pX ∷ pIₙ) +ₚ f (b *₁ pZ ∷ pIₙ)        ≡⟨ Eq.cong₂ (λ s t → f s +ₚ f t) (lemma-aux-kx a) (lemma-aux-kz b) ⟩
  f (a *ₚ pX₀) +ₚ f (b *ₚ pZ₀)                  ≡⟨ Eq.cong₂ _+ₚ_ (fm a pX₀) (fm b pZ₀) ⟩
  a *ₚ f pX₀ +ₚ b *ₚ f pZ₀                      ≡⟨ Eq.cong₂ _+ₚ_ (Eq.cong (a *ₚ_) eqx) (Eq.cong (b *ₚ_) eqz) ⟩
  a *ₚ pX₀ +ₚ b *ₚ pZ₀                          ≡⟨ Eq.cong₂ (λ s t → a *ₚ s +ₚ b *ₚ t) (Eq.sym lemma-aux-px) (Eq.sym lemma-aux-pz) ⟩
  a *ₚ (pX ∷ pIₙ) +ₚ b *ₚ (pZ ∷ pIₙ)            ≡⟨ Eq.refl ⟩
  (a *₁ pX +₁ b *₁ pZ) ∷ (a *ₚ pIₙ +ₚ b *ₚ pIₙ) ≡⟨ Eq.cong (λ □ → □ ∷ (a *ₚ pIₙ +ₚ b *ₚ pIₙ)) (Eq.sym eq) ⟩
  p ∷ (a *ₚ pIₙ +ₚ b *ₚ pIₙ)                    ≡⟨ Eq.cong₂ (λ s t → p ∷ s +ₚ t) (lemma-pauli-zero a) (lemma-pauli-zero b) ⟩
  p ∷ (pIₙ +ₚ pIₙ)                              ≡⟨ Eq.cong (p ∷_) (+ₚ-idˡ pIₙ) ⟩
  p ∷ pIₙ ∎
  where
  open ≡-Reasoning
  pab = pasXZ p
  a = pab .proj₁
  b = pab .proj₂ .proj₁
  eq = pab .proj₂ .proj₂

Linear-Symp-FixZX⇒FixP : ∀ {n} (f : Pauli (₁₊ n) → Pauli (₁₊ n)) →
  IsLinear f → IsSymp f → Fix-Z₀-X₀ f → Fix-P₀ f
Linear-Symp-FixZX⇒FixP {n} f (fp , fm) symp (eqz , eqx) p ps = begin
  f (p ∷ ps)                                                        ≡⟨ Eq.cong f (Eq.sym (+ₚ-idˡ (p ∷ ps))) ⟩
  f (pIₙ +ₚ (p ∷ ps))                                              ≡⟨ Eq.cong f (Eq.cong₂ _∷_ (Eq.sym (Eq.cong₂ _,_ (+-comm (p .proj₁) ₀) (+-comm (p .proj₂) ₀))) Eq.refl) ⟩
  f ((p ∷ pIₙ) +ₚ (pI ∷ ps))                                       ≡⟨ fp (p ∷ pIₙ) (pI ∷ ps) ⟩
  f (p ∷ pIₙ) +ₚ f (pI ∷ ps)                                       ≡⟨ Eq.cong (_+ₚ f (pI ∷ ps)) (lemma-linear0' f (fp , fm) (eqz , eqx) p) ⟩
  (p ∷ pIₙ) +ₚ f (pI ∷ ps)                                         ≡⟨ Eq.cong ((p ∷ pIₙ) +ₚ_) (Eq.sym (lemma-aux-vec n (f (pI ∷ ps)))) ⟩
  (p ∷ pIₙ) +ₚ (head (f (pI ∷ ps)) ∷ tail (f (pI ∷ ps)))           ≡⟨ Eq.cong (λ □ → (p ∷ pIₙ) +ₚ (□ ∷ tail (f (pI ∷ ps)))) aux9 ⟩
  (p ∷ pIₙ) +ₚ (pI ∷ tail (f (pI ∷ ps)))                           ≡⟨ Eq.refl ⟩
  (p +₁ pI) ∷ (pIₙ +ₚ tail (f (pI ∷ ps)))                          ≡⟨ Eq.cong₂ _∷_ (+₁-idˡ p) (+ₚ-idˡ (tail (f (pI ∷ ps)))) ⟩
  p ∷ tail (f (pI ∷ ps)) ∎
  where
  open ≡-Reasoning
  aux2a : ∀ p → sform (p ∷ pIₙ) (f (pI ∷ ps)) ≡ ₀
  aux2a p = begin
    sform (p ∷ pIₙ) (f (pI ∷ ps))       ≡⟨ Eq.cong (λ □ → sform □ (f (pI ∷ ps))) (Eq.sym (lemma-linear0' f (fp , fm) (eqz , eqx) p)) ⟩
    sform (f (p ∷ pIₙ)) (f (pI ∷ ps))   ≡⟨ symp (p ∷ pIₙ) (pI ∷ ps) ⟩
    sform (p ∷ pIₙ) (pI ∷ ps)           ≡⟨ Eq.cong₂ _+_ (lemma-sform1-pIʳ p) (lemma-sform-pIₙ-q=0 ps) ⟩
    ₀ + ₀                               ≡⟨ +-identityˡ ₀ ⟩
    ₀ ∎
  aux7 : sform1 pX (head (f (pI ∷ ps))) ≡ ₀
  aux7 = let ps' = f (pI ∷ ps) in begin
    sform1 pX (head ps')                             ≡⟨ Eq.sym (+-identityʳ (sform1 pX (head ps'))) ⟩
    sform1 pX (head ps') + ₀                         ≡⟨ Eq.cong (sform1 pX (head ps') +_) (Eq.sym (lemma-sform-pIₙ-q=0 (tail ps'))) ⟩
    sform (pX ∷ pIₙ) (head ps' ∷ tail ps')           ≡⟨ Eq.cong (sform (pX ∷ pIₙ)) (lemma-aux-vec n ps') ⟩
    sform (pX ∷ pIₙ) ps'                             ≡⟨ aux2a pX ⟩
    ₀ ∎
  aux8 : sform1 pZ (head (f (pI ∷ ps))) ≡ ₀
  aux8 = let ps' = f (pI ∷ ps) in begin
    sform1 pZ (head ps')                             ≡⟨ Eq.sym (+-identityʳ (sform1 pZ (head ps'))) ⟩
    sform1 pZ (head ps') + ₀                         ≡⟨ Eq.cong (sform1 pZ (head ps') +_) (Eq.sym (lemma-sform-pIₙ-q=0 (tail ps'))) ⟩
    sform (pZ ∷ pIₙ) (head ps' ∷ tail ps')           ≡⟨ Eq.cong (sform (pZ ∷ pIₙ)) (lemma-aux-vec n ps') ⟩
    sform (pZ ∷ pIₙ) ps'                             ≡⟨ aux2a pZ ⟩
    ₀ ∎
  aux9 : head (f (pI ∷ ps)) ≡ pI
  aux9 = lemma-sform1-XZ (head (f (pI ∷ ps))) (aux8 , aux7)

------------------------------------------------------------------------
-- Composition and the tail sub-map are linear and symplectic

lemma-symp-compose : ∀ {n} (f h : Pauli n → Pauli n) → IsSymp f → IsSymp h → IsSymp (h ∘ f)
lemma-symp-compose f h fs hs ps qs = Eq.trans (hs (f ps) (f qs)) (fs ps qs)

lemma-linear-compose : ∀ {n} (f h : Pauli n → Pauli n) → IsLinear f → IsLinear h → IsLinear (h ∘ f)
lemma-linear-compose f h (fa , fm) (ha , hm) = c1 , c2
  where
  c1 : ∀ ps qs → (h ∘ f) (ps +ₚ qs) ≡ (h ∘ f) ps +ₚ (h ∘ f) qs
  c1 ps qs = Eq.trans (Eq.cong h (fa ps qs)) (ha (f ps) (f qs))
  c2 : ∀ k ps → (h ∘ f) (k *ₚ ps) ≡ k *ₚ (h ∘ f) ps
  c2 k ps = Eq.trans (Eq.cong h (fm k ps)) (hm k (f ps))

lemma-tail-linear-+ : ∀ {n} (ps qs : Pauli (₁₊ n)) → tail (ps +ₚ qs) ≡ tail ps +ₚ tail qs
lemma-tail-linear-+ (x ∷ ps) (x₁ ∷ qs) = Eq.refl

lemma-tail-linear-* : ∀ {n} k (ps : Pauli (₁₊ n)) → tail (k *ₚ ps) ≡ k *ₚ tail ps
lemma-tail-linear-* k (x ∷ ps) = Eq.refl

lemma-sub : ∀ {n} (f : Pauli (₁₊ n) → Pauli (₁₊ n)) → IsLinear f →
  IsLinear (λ ps → tail (f (pI ∷ ps)))
lemma-sub {n} f (p , m) = c1 , c2
  where
  open ≡-Reasoning
  g = λ ps → tail (f (pI ∷ ps))
  c1 : ∀ ps qs → g (ps +ₚ qs) ≡ g ps +ₚ g qs
  c1 ps qs = begin
    tail (f (pI ∷ (ps +ₚ qs)))            ≡⟨ Eq.cong tail (p (pI ∷ ps) (pI ∷ qs)) ⟩
    tail (f (pI ∷ ps) +ₚ f (pI ∷ qs))     ≡⟨ lemma-tail-linear-+ (f (pI ∷ ps)) (f (pI ∷ qs)) ⟩
    tail (f (pI ∷ ps)) +ₚ tail (f (pI ∷ qs)) ∎
  lemma-aux : ∀ {n} k (ps : Pauli n) → pI ∷ (k *ₚ ps) ≡ k *ₚ (pI ∷ ps)
  lemma-aux k ps = Eq.cong₂ _∷_ (Eq.sym (*₁-zeroʳ k)) Eq.refl
  c2 : ∀ k ps → g (k *ₚ ps) ≡ k *ₚ g ps
  c2 k ps = begin
    tail (f (pI ∷ (k *ₚ ps)))    ≡⟨ Eq.cong (λ □ → tail (f □)) (lemma-aux k ps) ⟩
    tail (f (k *ₚ (pI ∷ ps)))    ≡⟨ Eq.cong tail (m k (pI ∷ ps)) ⟩
    tail (k *ₚ f (pI ∷ ps))      ≡⟨ lemma-tail-linear-* k (f (pI ∷ ps)) ⟩
    k *ₚ tail (f (pI ∷ ps)) ∎

Linear-Symp-⇒FixP⇒ : ∀ {n} (f : Pauli (₁₊ n) → Pauli (₁₊ n)) →
  IsLinear f → IsSymp f → Fix-P₀ f →
  IsLinear (λ ps → tail (f (pI ∷ ps))) × IsSymp (λ ps → tail (f (pI ∷ ps)))
Linear-Symp-⇒FixP⇒ {n} f fl symp fp0 = lemma-sub f fl , claim
  where
  open ≡-Reasoning
  claim : IsSymp (λ ps → tail (f (pI ∷ ps)))
  claim ps qs = begin
    sform (tail (f (pI ∷ ps))) (tail (f (pI ∷ qs)))         ≡⟨ Eq.sym (+-identityˡ _) ⟩
    ₀ + sform (tail (f (pI ∷ ps))) (tail (f (pI ∷ qs)))     ≡⟨ Eq.cong (_+ sform (tail (f (pI ∷ ps))) (tail (f (pI ∷ qs)))) (Eq.sym (sform-pI-q=0 pI)) ⟩
    sform (pI ∷ tail (f (pI ∷ ps))) (pI ∷ tail (f (pI ∷ qs))) ≡⟨ Eq.cong₂ sform (Eq.sym (fp0 pI ps)) (Eq.sym (fp0 pI qs)) ⟩
    sform (f (pI ∷ ps)) (f (pI ∷ qs))                       ≡⟨ symp (pI ∷ ps) (pI ∷ qs) ⟩
    sform (pI ∷ ps) (pI ∷ qs)                               ≡⟨ Eq.cong (_+ sform ps qs) (sform-pI-q=0 pI) ⟩
    ₀ + sform ps qs                                         ≡⟨ +-identityˡ _ ⟩
    sform ps qs ∎

------------------------------------------------------------------------
-- The inverting normal form: every linear symplectic f has an NF whose
-- action inverts it.

lemma-invnf : ∀ {n} (f : Pauli n → Pauli n) → IsLinear f → IsSymp f →
  ∃ λ (nf : NF n) → (act-nf nf) ∘ f ≗ id
lemma-invnf {0}    f fl symp = tt , claim
  where
  claim : (p : Pauli 0) → act-nf tt (f p) ≡ p
  claim [] with f []
  ... | [] = Eq.refl
lemma-invnf {₁₊ n} f fl symp = (ih , lm) , claim
  where
  open ≡-Reasoning
  lmp = lemma-fundamental' f symp
  lm  = lmp .proj₁
  lmf = act [ lm ]ᵐˡ ∘ f
  lmfl : IsLinear lmf
  lmfl = lemma-linear-compose f (act [ lm ]ᵐˡ) fl (actw-linear [ lm ]ᵐˡ)
  lmf-symp : IsSymp lmf
  lmf-symp = lemma-symp-compose f (act [ lm ]ᵐˡ) symp (actw-symp [ lm ]ᵐˡ)
  lmf-fp0 : Fix-P₀ lmf
  lmf-fp0 = Linear-Symp-FixZX⇒FixP lmf lmfl lmf-symp (lmp .proj₂)
  gls = Linear-Symp-⇒FixP⇒ lmf lmfl lmf-symp lmf-fp0
  ihp = lemma-invnf (λ ps → tail (lmf (pI ∷ ps))) (gls .proj₁) (gls .proj₂)
  ih  = ihp .proj₁

  claim : ∀ p → act-nf (ih , lm) (f p) ≡ p
  claim (p ∷ ps) = let s1 = act [ lm ]ᵐˡ (f (p ∷ ps)) in begin
    head s1 ∷ act-nf ih (tail s1)                                   ≡⟨ Eq.cong₂ _∷_ Eq.refl (Eq.cong (act-nf ih) (Eq.cong tail (lmf-fp0 p ps))) ⟩
    head s1 ∷ act-nf ih (tail (lmf (pI ∷ ps)))                      ≡⟨ Eq.cong₂ _∷_ Eq.refl (ihp .proj₂ ps) ⟩
    head s1 ∷ ps                                                    ≡⟨ Eq.cong (_∷ ps) (Eq.cong head (lmf-fp0 p ps)) ⟩
    head (p ∷ tail (lmf (pI ∷ ps))) ∷ ps                           ≡⟨ Eq.refl ⟩
    p ∷ ps ∎

------------------------------------------------------------------------
-- Surjectivity onto the symplectic group

surj-nf : ∀ {n} (S : Sem.Symplectic n) → ∃ λ (w : Circuit n) → ⟦ w ⟧ ≈ˢ S
surj-nf {n} S = [ nf ] , claim
  where
  open ≡-Reasoning
  invnf = lemma-invnf (ap⁻¹ S)
            (linear-+ (S ⁻¹ˢ) , linear-* (S ⁻¹ˢ)) (preserves (S ⁻¹ˢ))
  nf = invnf .proj₁
  claim : ⟦ [ nf ] ⟧ ≈ˢ S
  claim p = begin
    act [ nf ] p                    ≡⟨ lemma-act-nf nf p ⟩
    act-nf nf p                     ≡⟨ Eq.cong (act-nf nf) (Eq.sym (invˡ S p)) ⟩
    act-nf nf (ap⁻¹ S (ap S p))     ≡⟨ invnf .proj₂ (ap S p) ⟩
    ap S p ∎
