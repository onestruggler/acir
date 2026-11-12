------------------------------------------------------------------------
-- Presentations of groups
--
-- A two-qutrit replacement, discovered externally and checked here.
-- Twelve gates (three CZ) become six gates (one CZ), with scalar omega.
-- The semantic premise and phase are computed, not assumed or proved
-- from circuit axioms. Completeness reconstructs the exact certificate.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Qupit-Clifford.CertificateExample where

open import Algebra.Bundles using (Group)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; zero ; suc ; toℕ)
import Data.Fin.Properties as FP
open import Data.Nat using (ℕ ; _+_)
open import Data.Nat.Primality using (prime?)
open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂ ; ∃)
import Data.Product.Properties as PP
open import Data.Vec using ([] ; _∷_)
import Data.Vec.Properties as VP
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
import Relation.Binary.PropositionalEquality as Eq
open import Word.Base using (Word ; ε ; [_]ʷ ; _•_)
open import Presentation.Construct.Base using ([_]ₗ ; [_]ᵣ)
import Presentation.Base as PB

open import ForStdlib.Data.Fin.Mod using (ℤ ; ℤ* ; _^′_ ; ₀ ; ₁)
  renaming (_+_ to _+₃_ ; _*_ to _*₃_ ; -_ to -₃_)
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
  using (module PrimeModulus')
open PrimeModulus' 1 (from-yes (prime? 3)) using (ₚ ; ₚ-₁)

g* : ℤ* ₚ
g* = suc (suc zero) , λ ()

g-gen : ∀ ((x , _) : ℤ* ₚ) →
  ∃ λ (k : ℤ ₚ-₁) → x ≡ proj₁ g* ^′ toℕ k
g-gen (zero , nz) = ⊥-elim (nz refl)
g-gen (suc zero , _) = zero , refl
g-gen (suc (suc zero) , _) = suc zero , refl

import Examples.Groups.Qupit-Clifford.Syntactics
  0 (from-yes (prime? 3)) g* g-gen as Syn
import Examples.Groups.Qupit-Clifford.Certificate
  0 (from-yes (prime? 3)) g* g-gen as Client
import Examples.Groups.Qupit-Clifford.SemFE
  0 (from-yes (prime? 3)) g* g-gen as FE
import Examples.Groups.Qupit-Clifford.Semantics
  0 (from-yes (prime? 3)) as Sem
import Examples.Groups.ProjectivePauli.Semantics
  1 (from-yes (prime? 3)) as Pauli
import Examples.Groups.Symplectic.Semantics
  1 (from-yes (prime? 3)) as Sp
import Examples.Groups.Cyclic.Scalars 1 as Sc
import Examples.Groups.Symplectic.Syntactics.Gates
  1 (from-yes (prime? 3)) as Gates
open Gates.Symplectic using (S ; H ; CZ ; _↑)

module W = FE.Weyl 2
module C = Client.At 2
module E = PB (2 Syn.Exact,_===_)

import Examples.Groups.Qupit-Clifford.SemShift
  0 (from-yes (prime? 3)) g* g-gen as Shift
import Examples.Groups.Qupit-Clifford.SemRealises
  0 (from-yes (prime? 3)) g* g-gen as Phase
module Ph = Phase.Width 2
open Pauli using (Pauli ; pIₙ ; _+ₚ_ ; sform)
open Sp.Symplectic using (ap)

-- A compact executable reading, related to the presentation evaluator
-- by its public equations. This avoids reducing transported actions.
record Value : Set where
  constructor value
  field
    pauli : Pauli 2
    act : Pauli 2 → Pauli 2
    phase : Fin 3
open Value

_⊗_ : Value → Value → Value
value P f e ⊗ value Q g d =
  value (P +ₚ f Q) (λ q → f (g q))
    ((e +₃ d) +₃ (Sem.1/2 *₃ sform P (f Q)))

record Reads (w : Syn.Circuit 2) (v : Value) : Set where
  constructor reads
  field
    pauli-ok : proj₁ W.⟦ w ⟧ ≡ pauli v
    act-ok : ∀ q → ap (proj₂ W.⟦ w ⟧) q ≡ act v q
    phase-ok : Ph.Φ w ≡ phase v
open Reads

abstract

  reads-• : ∀ {u v x y} → Reads u x → Reads v y → Reads (u • v) (x ⊗ y)
  reads-• {u} {v} {value P f e} {value Q g d}
    (reads pu au eu) (reads pv av ev) = reads pe ae ee
    where
    pq : ap (proj₂ W.⟦ u ⟧) (proj₁ W.⟦ v ⟧) ≡ f Q
    pq = Eq.trans (Eq.cong (ap (proj₂ W.⟦ u ⟧)) pv) (au Q)
    pe : proj₁ W.⟦ u • v ⟧ ≡ P +ₚ f Q
    pe = Eq.trans (proj₁ (W.⟦⟧-∙ u v)) (Eq.cong₂ _+ₚ_ pu pq)
    ae : ∀ q → ap (proj₂ W.⟦ u • v ⟧) q ≡ f (g q)
    ae = λ q → Eq.trans (proj₂ (W.⟦⟧-∙ u v) q)
      (Eq.trans (Eq.cong (ap (proj₂ W.⟦ u ⟧)) (av q)) (au (g q)))
    ee : Ph.Φ (u • v) ≡ (e +₃ d) +₃ (Sem.1/2 *₃ sform P (f Q))
    ee = Eq.trans (Ph.Φ-• u v)
      (Eq.cong₂ _+₃_ (Eq.cong₂ _+₃_ eu ev)
        (Eq.cong (Sem.1/2 *₃_) (Eq.cong₂ sform pu pq)))

data Gate : Set where
  H₀ S₀ H₁ S₁ CZ₀ : Gate

spell : Gate → Syn.Circuit 2
spell H₀ = H
spell S₀ = S
spell H₁ = H ↑
spell S₁ = S ↑
spell CZ₀ = CZ

atom : Gate → Value
atom H₀ = value pIₙ (λ { ((a , b) ∷ R) → (-₃ b , a) ∷ R }) ₀
atom S₀ = value ((₀ , ₁) ∷ (₀ , ₀) ∷ [])
  (λ { ((a , b) ∷ R) → (a , b +₃ a) ∷ R }) ₀
atom H₁ = value pIₙ
  (λ { (q ∷ (a , b) ∷ []) → q ∷ (-₃ b , a) ∷ [] }) ₀
atom S₁ = value ((₀ , ₀) ∷ (₀ , ₁) ∷ [])
  (λ { (q ∷ (a , b) ∷ []) → q ∷ (a , b +₃ a) ∷ [] }) ₀
atom CZ₀ = value pIₙ
  (λ { ((a , b) ∷ (c , d) ∷ []) → (a , b +₃ c) ∷ (c , d +₃ a) ∷ [] }) ₀

abstract

  atom-ok : ∀ g → Reads (spell g) (atom g)
  atom-ok H₀ = reads refl (λ { ((a , b) ∷ R) → Shift.gate₁H-act a b R })
    (Ph.Φ-gate _)
  atom-ok S₀ = reads Shift.gate₁S-Pauli
    (λ { ((a , b) ∷ R) → Shift.gate₁S-act a b R }) (Ph.Φ-gate _)
  atom-ok H₁ = reads refl (λ { (q ∷ (a , b) ∷ []) → refl }) (Ph.Φ-gate _)
  atom-ok S₁ = reads
    (Eq.trans (proj₁ (Shift.⟦⟧-↑ S)) (Eq.cong ((₀ , ₀) ∷_) Shift.gate₁S-Pauli))
    (λ { (q ∷ (a , b) ∷ []) →
      Eq.trans (proj₂ (Shift.⟦⟧-↑ S) (q ∷ (a , b) ∷ []))
        (Eq.cong (q ∷_) (Shift.gate₁S-act a b [])) }) (Ph.Φ-gate _)
  atom-ok CZ₀ = reads refl
    (λ { ((a , b) ∷ (c , d) ∷ []) → refl }) (Ph.Φ-gate _)

expand : Word Gate → Syn.Circuit 2
expand [ g ]ʷ = spell g
expand ε = ε
expand (u • v) = expand u • expand v

eval : Word Gate → Value
eval [ g ]ʷ = atom g
eval ε = value pIₙ (λ q → q) ₀
eval (u • v) = eval u ⊗ eval v

abstract

  eval-ok : ∀ w → Reads (expand w) (eval w)
  eval-ok [ g ]ʷ = atom-ok g
  eval-ok ε = reads refl (λ _ → refl) Ph.Φ-ε
  eval-ok (u • v) = reads-• (eval-ok u) (eval-ok v)

-- Wire 0 is the bottom wire. Juxtaposition follows Word._•_.
input output : Word Gate
input = [ S₁ ]ʷ • [ CZ₀ ]ʷ • [ H₁ ]ʷ • [ H₀ ]ʷ • [ H₁ ]ʷ • [ CZ₀ ]ʷ •
  [ S₁ ]ʷ • [ S₀ ]ʷ • [ H₀ ]ʷ • [ CZ₀ ]ʷ • [ S₀ ]ʷ • [ H₀ ]ʷ
output = [ S₀ ]ʷ • [ S₀ ]ʷ • [ S₁ ]ʷ • [ H₁ ]ʷ • [ H₁ ]ʷ • [ CZ₀ ]ʷ

before after : Syn.Circuit 2
before = expand input
after = expand output

computed-pauli : pauli (eval input) ≡ pauli (eval output)
computed-pauli = refl

computed-action : ∀ q → act (eval input) q ≡ act (eval output) q
computed-action ((a , b) ∷ (c , d) ∷ []) =
  from-yes (FP.all? λ a → FP.all? λ b → FP.all? λ c → FP.all? λ d →
    VP.≡-dec (PP.≡-dec FP._≟_ FP._≟_)
      (act (eval input) ((a , b) ∷ (c , d) ∷ []))
      (act (eval output) ((a , b) ∷ (c , d) ∷ []))) a b c d

abstract

  semantic-agreement : ∀ {u v x y} → Reads u x → Reads v y →
    pauli x ≡ pauli y → (∀ q → act x q ≡ act y q) →
    Group._≈_ (Sem.Pauli⋊Sp-group 2) W.⟦ u ⟧ W.⟦ v ⟧
  semantic-agreement ru rv pe ae =
    Eq.trans (pauli-ok ru) (Eq.trans pe (Eq.sym (pauli-ok rv))) ,
    λ q → Eq.trans (act-ok ru q)
      (Eq.trans (ae q) (Eq.sym (act-ok rv q)))

  phase-difference : ∀ {u v x y} → Reads u x → Reads v y →
    C.correction u v ≡ phase x +₃ (-₃ phase y)
  phase-difference ru rv = Eq.cong₂ (λ x y → x +₃ (-₃ y))
    (phase-ok ru) (phase-ok rv)

projective-agrees : Group._≈_ (Sem.Pauli⋊Sp-group 2)
  W.⟦ before ⟧ W.⟦ after ⟧
projective-agrees = semantic-agreement
  {u = before} {v = after} {x = eval input} {y = eval output}
  (eval-ok input) (eval-ok output) computed-pauli computed-action

input-phase : Ph.Φ before ≡ suc zero
input-phase = phase-ok (eval-ok input)

output-phase : Ph.Φ after ≡ zero
output-phase = phase-ok (eval-ok output)

phase-is-one : C.correction before after ≡ suc zero
phase-is-one = phase-difference
  {u = before} {v = after} {x = eval input} {y = eval output}
  (eval-ok input) (eval-ok output)

abstract

  repair-known : ∀ {u v t} →
    Group._≈_ (Sem.Pauli⋊Sp-group 2) W.⟦ u ⟧ W.⟦ v ⟧ →
    C.correction u v ≡ t → E._≈_ [ u ]ᵣ ([ Sc.emb t ]ₗ • [ v ]ᵣ)
  repair-known {u} {v} {t} eq phase-eq = E.trans
    {w = [ u ]ᵣ}
    {v = [ Sc.emb (C.correction u v) ]ₗ • [ v ]ᵣ}
    {u = [ Sc.emb t ]ₗ • [ v ]ᵣ}
    (C.repair u v eq)
    (E.refl' (Eq.cong (λ s → [ Sc.emb s ]ₗ • [ v ]ᵣ) phase-eq))

certificate : E._≈_ [ before ]ᵣ ([ Sc.emb (suc zero) ]ₗ • [ after ]ᵣ)
certificate = repair-known {u = before} {v = after} {t = suc zero}
  projective-agrees phase-is-one

replace : ∀ l r →
  E._≈_ (l • ([ before ]ᵣ • r))
    (l • (([ Sc.emb (suc zero) ]ₗ • [ after ]ᵣ) • r))
replace l r = E.cong {w = l} {w' = l}
  {v = [ before ]ᵣ • r} {v' = ([ Sc.emb (suc zero) ]ₗ • [ after ]ᵣ) • r}
  E.refl (E.cong {w = [ before ]ᵣ} {w' = [ Sc.emb (suc zero) ]ₗ • [ after ]ᵣ}
    {v = r} {v' = r} certificate E.refl)

size : Word Gate → ℕ
size [ _ ]ʷ = 1
size ε = 0
size (u • v) = size u + size v

cz-count : Word Gate → ℕ
cz-count [ CZ₀ ]ʷ = 1
cz-count [ _ ]ʷ = 0
cz-count ε = 0
cz-count (u • v) = cz-count u + cz-count v

gate-counts : _≡_ {A = ℕ × ℕ} (size input , size output) (12 , 6)
gate-counts = refl

entangling-counts : _≡_ {A = ℕ × ℕ} (cz-count input , cz-count output) (3 , 1)
entangling-counts = refl
