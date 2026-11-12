------------------------------------------------------------------------
-- Presentations of groups
--
-- A phase-repair client: a projectively valid replacement u -> v becomes
-- an exact derivation u ≈ ω^(Φ u - Φ v) v. The client supplies only the
-- equality of the Pauli and symplectic components. The phase is computed
-- by the existing Weyl evaluator, and completeness supplies the proof.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Qupit-Clifford.Certificate
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (Group)
import Relation.Binary.PropositionalEquality as Eq
open import Word.Base using (ε ; _•_)
open import Presentation.Construct.Base using ([_]ₗ ; [_]ᵣ)
import Presentation.Base as PB

import Examples.Groups.Qupit-Clifford.Syntactics
  p-3 p-prime g* g-gen as Syn
import Examples.Groups.Qupit-Clifford.Semantics p-3 p-prime as Sem
import Examples.Groups.Qupit-Clifford.Structural
  p-3 p-prime g* g-gen as Bridge
import Examples.Groups.Qupit-Clifford.SemFE
  p-3 p-prime g* g-gen as FE
import Examples.Groups.Qupit-Clifford.SemRealises
  p-3 p-prime g* g-gen as Phase
import Examples.Groups.Clifford+MinusOne.Qupit.Semantics
  p-3 p-prime g* g-gen as Reading
import Examples.Groups.Cyclic.Scalars as CySc

module Sc = CySc p-2
module KB = PB Syn.Scalar-relation

module At (n : ℕ) where

  module B = Bridge.Bridge n
  module W = FE.Weyl n
  module R = Reading.Exact-Reading n
  module Ph = Phase.Width n
  module C = Group (Sem.Pauli⋊Sp-group n)
  module S = Group (Sem.Clifford-group n)
  module QB = PB (Syn.CR._QRel,_===_ n)

  correction : Syn.Circuit n → Syn.Circuit n → ℤ ₚ
  correction u v = Ph.Φ u + (- Ph.Φ v)

  private
    read-phase : ∀ w → Bridge.read-scalar (R.Ev.scal w) ≡ Ph.Φ w
    read-phase w = Eq.trans (Bridge.KI.⟦⟧-cong (Ph.scal≈ w))
      (Bridge.read-emb (Ph.Φ w))

    read-circuit : ∀ w →
      S._≈_ (B.interpret [ w ]ᵣ) (Sem.ω^ Ph.Φ w , W.⟦ w ⟧)
    read-circuit w = S.trans
      {i = B.interpret [ w ]ᵣ}
      {j = B.to-structural (R.Ev.scal w , w)}
      {k = Sem.ω^ Ph.Φ w , W.⟦ w ⟧}
      (B.to-cong (R.emb-r-pair w))
      (Eq.cong Sem.ω^_ (read-phase w) , (Eq.refl , λ _ → Eq.refl))

    read-corrected : ∀ t w →
      S._≈_ (B.interpret ([ Sc.emb t ]ₗ • [ w ]ᵣ))
        (Sem.ω^ (t + Ph.Φ w) , W.⟦ w ⟧)
    read-corrected t w = S.trans
      {i = B.interpret ([ Sc.emb t ]ₗ • [ w ]ᵣ)}
      {j = B.to-structural ((Sc.emb t • R.Ev.scal w) • ε , ε • w)}
      {k = Sem.ω^ (t + Ph.Φ w) , W.⟦ w ⟧}
      (B.to-cong (R.val (Sc.emb t) w))
      (Eq.cong Sem.ω^_ scalar , W.⟦⟧-cong {ε • w} {w} QB.left-unit)
      where
      scalar : Bridge.read-scalar ((Sc.emb t • R.Ev.scal w) • ε)
        ≡ t + Ph.Φ w
      scalar = Eq.trans
        (Bridge.KI.⟦⟧-cong
          {(Sc.emb t • R.Ev.scal w) • ε} {Sc.emb t • R.Ev.scal w}
          KB.right-unit)
        (Eq.trans (Bridge.KI.∙-homo (Sc.emb t) (R.Ev.scal w))
          (Eq.cong₂ _+_ (Bridge.read-emb t) (read-phase w)))

  repair : (u v : Syn.Circuit n) → C._≈_ W.⟦ u ⟧ W.⟦ v ⟧ →
    PB._≈_ (n Syn.Exact,_===_) [ u ]ᵣ
      ([ Sc.emb (correction u v) ]ₗ • [ v ]ᵣ)
  repair u v eq = B.certify {u = [ u ]ᵣ}
    {v = [ Sc.emb (correction u v) ]ₗ • [ v ]ᵣ}
    (S.trans
      {i = B.interpret [ u ]ᵣ}
      {j = Sem.ω^ Ph.Φ u , W.⟦ u ⟧}
      {k = B.interpret ([ Sc.emb (correction u v) ]ₗ • [ v ]ᵣ)}
      (read-circuit u)
      (S.trans
        {i = Sem.ω^ Ph.Φ u , W.⟦ u ⟧}
        {j = Sem.ω^ (correction u v + Ph.Φ v) , W.⟦ v ⟧}
        {k = B.interpret ([ Sc.emb (correction u v) ]ₗ • [ v ]ᵣ)}
        (Eq.cong Sem.ω^_ scalar , eq)
        (S.sym
          {x = B.interpret ([ Sc.emb (correction u v) ]ₗ • [ v ]ᵣ)}
          {y = Sem.ω^ (correction u v + Ph.Φ v) , W.⟦ v ⟧}
          (read-corrected (correction u v) v))))
    where
    scalar : Ph.Φ u ≡ correction u v + Ph.Φ v
    scalar = Eq.sym (Eq.trans (+-assoc (Ph.Φ u) (- Ph.Φ v) (Ph.Φ v))
      (Eq.trans (Eq.cong (Ph.Φ u +_) (+-inverseˡ (Ph.Φ v)))
        (+-identityʳ (Ph.Φ u))))
