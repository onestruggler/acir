------------------------------------------------------------------------
-- Presentations of groups
--
-- The rule set with -1 is isomorphic to Figure 1 of arXiv:2609.40106.
--
-- Two rule sets, one group:
--
--   1) _Exact±,_===_ (Syntactics) over ω, -1 and the gates H, S, CZ —
--      the exact qupit Clifford rule set of Clifford.Qupit with -1
--      adjoined as a central generator of order 2;
--   2) _F,_===_ (Figure1.Syntactics) over -ω, H, S, CZ — Figure 1's
--      rules C0–C15 with the structural rules of circuits.
--
-- The isomorphism is Translation's exchange of scalar generators,
--
--     fig :  ω ↦ (-ω)^(p+1),  -1 ↦ (-ω)^p,     new :  -ω ↦ -1 • ω,
--
-- the identity on gates.  Presentation.Morphism's StarGroupIsomorphism
-- asks for four things:
--
--   new well defined   every Figure-1 rule holds in the rule set with
--                      -1: Figure1.Derived;
--   fig well defined   every rule of the rule set with -1 holds in
--                      Figure 1: this module;
--   the round trips    on generators: Translation.
--
-- fig well defined.  ωᵖ = 1, (-1)² = 1 and the centrality rules are
-- (-ω)^(2p) = 1 (C0) and the structural comm₀.  The content is in the
-- sixteen Paper-V0 relations, each twisted by the power of ω it carries
-- in the exact group: (S • H)³ = ω^((p²-1)/8) and fifteen with no
-- scalar.  Figure 1 has no such rules — order-SH is not among them at
-- all — so they have to be derived there, scalars included.  This is
-- done without computing a single scalar inside Figure 1:
--
--   1. mod scalars the relation is a theorem of Figure 1 (Figure1.Lift,
--      through Figure1.ModScalar.Iso), so it holds in Figure 1 up to
--      SOME power (-ω)^a of the scalar;
--   2. that equation, read back by `new` (Figure1.Derived), holds in
--      the rule set with -1; so does the twisted relation itself, so
--      (-ω)^a equals the relation's own scalar there;
--   3. scalars of the rule set with -1 are faithful — its presentation
--      theorem reads them off as a pair (ωᵃ, (-1)ᵃ) (Presentation.
--      scalar-injective) — so a is the right exponent, modulo p and
--      modulo 2; and since -ω = ω^(p+1) • (-1)^p, that is enough to
--      identify (-ω)^a with the relation's scalar in Figure 1 itself.
--
-- So the scalars Figure 1 carries — the Legendre symbols and phases of
-- its multipliers and the λ_p² of its swap — are checked exactly once,
-- in Figure1.Derived, and the exact group's own correction ω^((p²-1)/8)
-- falls out of them.
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

module Examples.Groups.Clifford+MinusOne.Qupit.Iso
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Nat.DivMod using (_%_ ; m≡m%n+[m/n]*n ; [m+kn]%n≡m%n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (proj₁ ; proj₂ ; _×_)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; wmap ; _ʷ)
import Word.Base as WB
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Construct.Base
  using (_⋄_⋄_ ; _∪_ ; [_]ₗ ; [_]ᵣ ; ConjRelʷ ; CommRel ; comm)
open import Presentation.Construct.Properties.Extension using (tw)
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
open import Presentation.Morphism using (module GroupMorphism)

import Examples.Groups.Cyclic.Syntactics as Cy

import Examples.Groups.Clifford+MinusOne.Qupit.Syntactics
  p-3 p-prime g* g-gen as N
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Syntactics
  p-3 p-prime g* g-gen as F
import Examples.Groups.Clifford+MinusOne.Qupit.Translation
  p-3 p-prime g* g-gen as T
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Derived
  p-3 p-prime g* g-gen as D
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Lift
  p-3 p-prime g* g-gen as Lift
import Examples.Groups.Clifford+MinusOne.Qupit.Presentation
  p-3 p-prime g* g-gen as P
import Examples.Groups.Clifford.Qupit.SemSHExp p-3 p-prime as SHE

open T using (Alph ; _≈±_ ; _≈ᶠ_ ; fig ; new ; Fʷ ; Gʷ)

private
  variable
    n : ℕ

  module KB = PB N.Scalar-relation
  module MB = PB N.MinusOne-relation

------------------------------------------------------------------------
-- Arithmetic of the scalar in Figure 1

module Scalar (n : ℕ) where

  open PB (F._F,_===_ n) public
  open PP (F._F,_===_ n) public using (word-setoid ; ^-+ ; ^^ ; ^-cong ; ε^k=ε)
  open SR word-setoid

  -- (-ω)^(2p) = 1.
  ν^2p : F.ν ^ (p Nat.+ p) ≈ ε
  ν^2p = axiom (F.srel F.c0)

  -- Exponents of ν matter modulo 2p.
  ν^-mod : ∀ j → F.ν ^ j ≈ F.ν ^ (j % (p Nat.+ p))
  ν^-mod j = begin
    F.ν ^ j
      ≡⟨ Eq.cong (F.ν ^_) (m≡m%n+[m/n]*n j (p Nat.+ p)) ⟩
    F.ν ^ (j % (p Nat.+ p) Nat.+ (j Nat./ (p Nat.+ p)) Nat.* (p Nat.+ p))
      ≈⟨ ^-+ F.ν (j % (p Nat.+ p)) _ ⟩
    F.ν ^ (j % (p Nat.+ p)) • F.ν ^ ((j Nat./ (p Nat.+ p)) Nat.* (p Nat.+ p))
      ≈⟨ cright (trans (refl' (Eq.cong (F.ν ^_)
                         (NP.*-comm (j Nat./ (p Nat.+ p)) (p Nat.+ p))))
                  (trans (sym (^^ F.ν (p Nat.+ p) (j Nat./ (p Nat.+ p))))
                    (trans (^-cong _ _ (j Nat./ (p Nat.+ p)) ν^2p)
                           (ε^k=ε (j Nat./ (p Nat.+ p)))))) ⟩
    F.ν ^ (j % (p Nat.+ p)) • ε
      ≈⟨ right-unit ⟩
    F.ν ^ (j % (p Nat.+ p))
      ∎

  -- A multiple of 2p vanishes.
  ν^-2p* : ∀ k → F.ν ^ (k Nat.* (p Nat.+ p)) ≈ ε
  ν^-2p* k =
    trans (ν^-mod (k Nat.* (p Nat.+ p)))
          (refl' (Eq.cong (F.ν ^_) (Data.Nat.DivMod.m*n%n≡0 k (p Nat.+ p))))
    where import Data.Nat.DivMod

  -- ω^p = 1: (p + 1)·p is a multiple of 2p, p being odd.
  ωˢ^p : F.ωˢ ^ p ≈ ε
  ωˢ^p with SHE.p-odd
  ... | q , e = begin
    (F.ν ^ ₁₊ p) ^ p          ≈⟨ ^^ F.ν (₁₊ p) p ⟩
    F.ν ^ (₁₊ p Nat.* p)      ≡⟨ Eq.cong (F.ν ^_) (shape q e) ⟩
    F.ν ^ ((₁₊ q) Nat.* (p Nat.+ p))
                              ≈⟨ ν^-2p* (₁₊ q) ⟩
    ε                         ∎
    where
    shape : ∀ q → p ≡ 1 Nat.+ 2 Nat.* q →
            ₁₊ p Nat.* p ≡ (₁₊ q) Nat.* (p Nat.+ p)
    shape q e = Eq.trans (Eq.cong (λ z → ₁₊ z Nat.* p) e) (solve-shape q p)
      where
      open +-*-Solver using (_:+_ ; _:*_ ; con ; _:=_)
        renaming (solve to nsolve)
      solve-shape : ∀ q r →
        ₁₊ (1 Nat.+ 2 Nat.* q) Nat.* r ≡ ₁₊ q Nat.* (r Nat.+ r)
      solve-shape = nsolve 2 (λ q r →
        (con 2 :+ con 2 :* q) :* r := (con 1 :+ q) :* (r :+ r)) Eq.refl

  -- (-1)² = 1.
  -1ˢ² : F.-1ˢ • F.-1ˢ ≈ ε
  -1ˢ² = trans (sym (^-+ F.ν p p)) ν^2p

  -- -ω splits as ω^(p+1) • (-1)^p, raised to any power.
  ν^-split : ∀ k → F.ν ^ k ≈ F.ωˢ ^ k • F.-1ˢ ^ k
  ν^-split k = begin
    F.ν ^ k                                     ≈⟨ sym right-unit ⟩
    F.ν ^ k • ε                                 ≈⟨ cright sym (ν^-2p* k) ⟩
    F.ν ^ k • F.ν ^ (k Nat.* (p Nat.+ p))       ≈⟨ sym (^-+ F.ν k _) ⟩
    F.ν ^ (k Nat.+ k Nat.* (p Nat.+ p))
                                  ≡⟨ Eq.cong (F.ν ^_) (arith k p) ⟩
    F.ν ^ (₁₊ p Nat.* k Nat.+ p Nat.* k)        ≈⟨ ^-+ F.ν _ _ ⟩
    F.ν ^ (₁₊ p Nat.* k) • F.ν ^ (p Nat.* k)
                                  ≈⟨ sym (cong (^^ F.ν (₁₊ p) k) (^^ F.ν p k)) ⟩
    F.ωˢ ^ k • F.-1ˢ ^ k                        ∎
    where
    open +-*-Solver using (_:+_ ; _:*_ ; con ; _:=_)
      renaming (solve to nsolve)
    arith : ∀ k r →
      k Nat.+ k Nat.* (r Nat.+ r) ≡ ₁₊ r Nat.* k Nat.+ r Nat.* k
    arith = nsolve 2 (λ k r →
      k :+ k :* (r :+ r) := (con 1 :+ r) :* k :+ r :* k) Eq.refl

------------------------------------------------------------------------
-- The two scalar factors, read in Figure 1

-- (f ʷ) commutes with the left-associated power too.
ʷ-^' : ∀ {A B : Set} (h : A → Word B) (w : Word A) (k : ℕ) →
       (h ʷ) (w WB.^' k) ≡ ((h ʷ) w) WB.^' k
ʷ-^' h w ₀      = Eq.refl
ʷ-^' h w (₁₊ ₀) = Eq.refl
ʷ-^' h w (₂₊ k) = Eq.cong (_• (h ʷ) w) (ʷ-^' h w (₁₊ k))

-- ω ↦ ω^(p+1) respects ωᵖ = 1, and -1 ↦ (-ω)^p respects (-1)² = 1.
fω : Word N.ScalarGen → Word (F.Gen n)
fω = (λ _ → F.ωˢ) ʷ

fm : Word N.MinusOneGen → Word (F.Gen n)
fm = (λ _ → F.-1ˢ) ʷ

fω-cong : ∀ {c c'} → KB._≈_ c c' → fω {n} c ≈ᶠ fω c'
fω-cong {n} = SC.fʷ-cong
  where
  open Scalar n using (ωˢ^p ; trans ; refl')
  wd : ∀ {w v} → N.Scalar-relation w v → fω {n} w ≈ᶠ fω v
  wd Cy.order =
    trans (refl' (ʷ-^' (λ _ → F.ωˢ) Cy.T p))
          (trans (PP.^'=^ (F._F,_===_ n) {p} {F.ωˢ}) ωˢ^p)
  module SC = PP.StarCongruence N.Scalar-relation (F._F,_===_ n) (λ _ → F.ωˢ) wd

fm-cong : ∀ {c c'} → MB._≈_ c c' → fm {n} c ≈ᶠ fm c'
fm-cong {n} = SC.fʷ-cong
  where
  open Scalar n using (-1ˢ² ; trans)
  wd : ∀ {w v} → N.MinusOne-relation w v → fm {n} w ≈ᶠ fm v
  wd Cy.order = -1ˢ²
  module SC = PP.StarCongruence N.MinusOne-relation (F._F,_===_ n)
                (λ _ → F.-1ˢ) wd

-- A word over the scalar alphabet is a power of its one letter.
len : Word ⊤ → ℕ
len [ _ ]ʷ  = 1
len ε       = 0
len (u • v) = len u Nat.+ len v

pow-len : ∀ (Γ : Word.Base.WRel ⊤) (c : Word ⊤) →
          PB._≈_ Γ c (Cy.T ^ len c)
pow-len Γ [ tt ]ʷ = PB.refl
pow-len Γ ε       = PB.refl
pow-len Γ (u • v) =
  PB.trans (PB.cong (pow-len Γ u) (pow-len Γ v))
           (PB.sym (PP.^-+ Γ Cy.T (len u) (len v)))
  where import Word.Base

-- f of a twice-left-embedded scalar word.
F-ₗₗ : (c : Word N.ScalarGen) → Fʷ {n} [ [ c ]ₗ ]ₗ ≡ fω c
F-ₗₗ [ _ ]ʷ  = Eq.refl
F-ₗₗ ε       = Eq.refl
F-ₗₗ (u • v) = Eq.cong₂ _•_ (F-ₗₗ u) (F-ₗₗ v)

F-ᵣ : (c : Word N.MinusOneGen) → Fʷ {n} [ c ]ᵣ ≡ fm c
F-ᵣ [ _ ]ʷ  = Eq.refl
F-ᵣ ε       = Eq.refl
F-ᵣ (u • v) = Eq.cong₂ _•_ (F-ᵣ u) (F-ᵣ v)

------------------------------------------------------------------------
-- new on whole derivations

new-cong : ∀ {u v} → u ≈ᶠ v → Gʷ {n} u ≈± Gʷ v
new-cong {n} = SC.fʷ-cong
  where
  module SC = PP.StarCongruence (F._F,_===_ n) (n N.Exact±,_===_) new
                D.new-well-defined

------------------------------------------------------------------------
-- The twisted relators hold in Figure 1

module Twisted (n : ℕ) where

  private
    module NA = T.Algebra n
    module GL = Group-Lemmas (n N.Exact±,_===_)
                  (_IsPresentationOf_.gl (P.presentation± n))

  -- ω^m, as a power of -ω: (-ω)^(p+1) is ω.
  ω-pow : ∀ m → [ [ Cy.T ^ m ]ₗ ]ₗ ≈± N.-ω± ^ (₁₊ p Nat.* m)
  ω-pow m =
    PB.trans (PB.refl' _ (Eq.trans (Eq.cong (wmap inj₁) (T.wmap-^ inj₁ Cy.T m))
                                   (T.wmap-^ inj₁ [ inj₁ tt ]ʷ m)))
      (PB.trans (PP.^-cong (n N.Exact±,_===_) _ _ m ω≈)
                (PP.^^ (n N.Exact±,_===_) N.-ω± (₁₊ p) m))
    where
    ω≈ : N.ω± ≈± N.-ω± ^ ₁₊ p
    ω≈ = PB.trans (T.new-left-inv-gen (inj₁ (inj₁ tt)))
                  (PB.refl' _ (T.ʷ-^ new F.ν (₁₊ p)))

  -- Step 2.  Read back by new, the lifted equation and the twisted
  -- relator are two expressions for ⌜ u ⌝, so (-ω)^a is the relator's
  -- scalar in the rule set with -1.
  back : ∀ {u v} (r : n N.CR.QRel, u === v) (a : ℕ) →
         T.E u ≈ᶠ F.ν ^ a • T.E v →
         N.-ω± ^ a ≈± N.-ω± ^ (₁₊ p Nat.* len (N.corr r))
  back {u} {v} r a lifted = GL.•-cancelʳ {h = N.⌜ v ⌝} chain
    where
    open SR (PP.word-setoid (n N.Exact±,_===_))
    m = len (N.corr r)

    chain : N.-ω± ^ a • N.⌜ v ⌝ ≈± N.-ω± ^ (₁₊ p Nat.* m) • N.⌜ v ⌝
    chain = begin
      N.-ω± ^ a • N.⌜ v ⌝
        ≡⟨ Eq.sym (Eq.cong₂ _•_ (T.ʷ-^ new F.ν a) (T.G-E v)) ⟩
      Gʷ (F.ν ^ a • T.E v)
        ≈⟨ new-cong (PB.sym lifted) ⟩
      Gʷ (T.E u)
        ≡⟨ T.G-E u ⟩
      N.⌜ u ⌝
        ≈⟨ PB.axiom (_⋄_⋄_.left (_⋄_⋄_.mid (_∪_.right (tw r)))) ⟩
      [ [ N.corr r ]ₗ ]ₗ • N.⌜ v ⌝
        ≈⟨ PB.cong (NA.scalars (pow-len N.Scalar-relation (N.corr r))) PB.refl ⟩
      [ [ Cy.T ^ m ]ₗ ]ₗ • N.⌜ v ⌝
        ≈⟨ PB.cong (ω-pow m) PB.refl ⟩
      N.-ω± ^ (₁₊ p Nat.* m) • N.⌜ v ⌝
        ∎

  -- Step 3.  The rule set with -1 reads a power of -ω as the pair of its
  -- exponents mod p and mod 2; Figure 1 rebuilds it from them.
  --
  -- (The pair is taken apart in a helper, not by `with`: abstracting
  -- scalar-injective's application out of the goal unfolds it.)
  pinned : ∀ (a m : ℕ) → N.-ω± ^ a ≈± N.-ω± ^ (₁₊ p Nat.* m) →
           F.ν ^ a ≈ᶠ fω (Cy.T ^ m)
  pinned a m e = rebuild a m (P.scalar-injective n a (₁₊ p Nat.* m) e)
    where
    rebuild : ∀ (a m : ℕ) →
              KB._≈_ (N.ω ^ a) (N.ω ^ (₁₊ p Nat.* m)) ×
              MB._≈_ (Cy.T ^ a) (Cy.T ^ (₁₊ p Nat.* m)) →
              F.ν ^ a ≈ᶠ fω (Cy.T ^ m)
    rebuild a m (eω , em) = begin
      F.ν ^ a                               ≈⟨ ν^-split a ⟩
      F.ωˢ ^ a • F.-1ˢ ^ a
        ≡⟨ Eq.sym (Eq.cong₂ _•_ (T.ʷ-^ _ Cy.T a) (T.ʷ-^ _ Cy.T a)) ⟩
      fω (Cy.T ^ a) • fm (Cy.T ^ a)         ≈⟨ cong (fω-cong eω) (fm-cong em) ⟩
      fω (Cy.T ^ b) • fm (Cy.T ^ b)         ≡⟨ Eq.cong₂ _•_ (T.ʷ-^ _ Cy.T b)
                                                           (T.ʷ-^ _ Cy.T b) ⟩
      F.ωˢ ^ b • F.-1ˢ ^ b                  ≈⟨ sym (ν^-split b) ⟩
      F.ν ^ b                               ≈⟨ sym (^^ F.ν (₁₊ p) m) ⟩
      F.ωˢ ^ m                              ≡⟨ Eq.sym (T.ʷ-^ _ Cy.T m) ⟩
      fω (Cy.T ^ m)                         ∎
      where
      open Scalar n
      open SR word-setoid
      b = ₁₊ p Nat.* m

  -- Step 1, and the conclusion.
  twisted : ∀ {u v} (r : n N.CR.QRel, u === v) →
            T.E u ≈ᶠ fω (N.corr r) • T.E v
  twisted r = from-lift r (Lift.lift-v0 n (PB.axiom r))
    where
    from-lift : ∀ {u v} (r : n N.CR.QRel, u === v) →
                ∃ (λ (a : ℕ) → T.E u ≈ᶠ F.ν ^ a • T.E v) →
                T.E u ≈ᶠ fω (N.corr r) • T.E v
    from-lift r (a , lifted) =
      PB.trans lifted
        (PB.cong (PB.trans (pinned a m (back r a lifted))
                           (fω-cong (PB.sym (pow-len N.Scalar-relation
                                                     (N.corr r)))))
                 PB.refl)
      where
      m = len (N.corr r)

------------------------------------------------------------------------
-- fig is well defined

fig-well-defined : ∀ {u v} → (n N.Exact±,_===_) u v → Fʷ u ≈ᶠ Fʷ v
-- ωᵖ = 1.
fig-well-defined {n} (_⋄_⋄_.left (_⋄_⋄_.left {u} {v} x)) =
  Eq.subst₂ _≈ᶠ_ (Eq.sym (F-ₗₗ u)) (Eq.sym (F-ₗₗ v)) (fω-cong (PB.axiom x))
fig-well-defined (_⋄_⋄_.left (_⋄_⋄_.right ()))
-- ω is central: comm₀, walked across ω^(p+1).
fig-well-defined {n} (_⋄_⋄_.left (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm tt x)))) =
  PB.sym (F.ν^-central (₁₊ p) [ T.sym→fig x ]ʷ)
-- The twisted relators.
fig-well-defined {n} (_⋄_⋄_.left (_⋄_⋄_.mid (_∪_.right (tw {u} {v} r)))) =
  Eq.subst₂ _≈ᶠ_ (Eq.sym (T.F-⌜⌝ u))
            (Eq.sym (Eq.cong₂ _•_ (F-ₗₗ (N.corr r)) (T.F-⌜⌝ v)))
            (Twisted.twisted n r)
-- (-1)² = 1.
fig-well-defined {n} (_⋄_⋄_.right {u} {v} x) =
  Eq.subst₂ _≈ᶠ_ (Eq.sym (F-ᵣ u)) (Eq.sym (F-ᵣ v)) (fm-cong (PB.axiom x))
-- -1 is central.
fig-well-defined {n} (_⋄_⋄_.mid (comm (inj₁ s) tt)) =
  PB.sym (F.ν^-central p F.ωˢ)
fig-well-defined {n} (_⋄_⋄_.mid (comm (inj₂ x) tt)) =
  PB.sym (F.ν^-central p [ T.sym→fig x ]ʷ)

------------------------------------------------------------------------
-- Group-likeness of Figure 1, transported

fig-cong : ∀ {u v} → u ≈± v → Fʷ {n} u ≈ᶠ Fʷ v
fig-cong {n} = SC.fʷ-cong
  where
  module SC = PP.StarCongruence (n N.Exact±,_===_) (F._F,_===_ n) fig
                fig-well-defined

grouplike± : Grouplike (n N.Exact±,_===_)
grouplike± {n} = _IsPresentationOf_.gl (P.presentation± n)

-- A Figure-1 generator inverts like its image: if w • new y ≈ ε on the
-- other side, then fig w • y ≈ ε here.
grouplike-F : Grouplike (F._F,_===_ n)
grouplike-F {n} y =
  Fʷ (new y GL.⁻¹) ,
  PB.trans (PB.cong PB.refl (T.fig-left-inv-gen y))
           (fig-cong (GL.inverseˡ {g = new y}))
  where
  module GL = Group-Lemmas (n N.Exact±,_===_) grouplike±

------------------------------------------------------------------------
-- The isomorphism

module Iso (n : ℕ) where

  private
    module GM = GroupMorphism (n N.Exact±,_===_) (F._F,_===_ n)
                  grouplike± grouplike-F

  open GM.StarGroupIsomorphism fig new
         fig-well-defined T.fig-left-inv-gen
         D.new-well-defined T.new-left-inv-gen
    public using (isGroupIsomorphism)

open GroupMorphisms

-- The theorem: the word group of the rule set with -1 is isomorphic to
-- the word group of Figure 1, by the exchange of scalar generators.
Theorem-Exact±-iso-Figure1 : ∀ {n} →
  let module G1 = Group-Lemmas (n N.Exact±,_===_) grouplike±
      module G2 = Group-Lemmas (F._F,_===_ n) grouplike-F
  in IsGroupIsomorphism (Group.rawGroup G1.•-ε-group)
                        (Group.rawGroup G2.•-ε-group) (fig {n} ʷ)
Theorem-Exact±-iso-Figure1 {n} = Iso.isGroupIsomorphism n
