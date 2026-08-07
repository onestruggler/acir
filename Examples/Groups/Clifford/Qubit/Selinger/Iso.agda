------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's Figure 8 modulo the global scalar, against the extension
-- presentation of the phaseless Clifford group.
--
-- Two rule sets describe the same group, C(n)/⟨ω⟩:
--
--   1) _CRel,_===_ of Qubit.Selinger.Figure8-Mod-Scalar — Selinger's
--      Figure 8 with the scalar quotiented out (C4 reads SHSHSH = 1),
--      over the gate generators Gen n;
--   2) _Clifford,_===_ (Qubit.Presentation) — the extension presentation
--      of Pauli n by Sp(2n,2), over PauliGen n ⊎ Gen n.
--
-- The comparison is set up as in Examples.Groups.Symplectic.Simplified.
-- Iso, but there the two rule sets share a generating set and the
-- isomorphism is the identity on words.  Here the generating sets differ,
-- so the builder is Presentation.Morphism.GroupMorphism.
-- StarGroupIsomorphism, which takes a translation in each direction.
--
-- The supporting material is split off:
--
--   Selinger.Translation — the maps f and g and their word extensions;
--   Selinger.PauliWords  — the calculus of X and Z in Figure 8 mod
--                          scalars (squares, XZ = ZX, disjoint wires);
--   Selinger.GroupLike   — group-likeness of both rule sets.
--
-- This module assembles them: the round trips, fwd-pauli, the split of
-- f-well-defined, and the isomorphism itself.  See the note at the
-- bottom for what the remaining parameters amount to.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger.Iso where

open import Data.Nat using (ℕ ; zero)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; _ʷ ; wmap)

import Presentation.Base as PB
open import Presentation.Morphism using (module GroupMorphism)
open import Presentation.Construct.Base
  using (_⋄_⋄_ ; _∪_ ; [_]ₗ ; [_]ᵣ ; ConjRelʷ ; CommRel ; _⊕^_)
open import Presentation.Construct.Properties.Extension using (tw)
import Examples.Groups.Cyclic.Syntactics as CyS

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot
  using (p-2 ; p-prime ; g* ; g-gen)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; gate₁ ; H-gate)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime as MS
open MS using (X ; Z ; _CRel,_===_ ; lemma-cong↑)

open import Examples.Groups.Clifford.Qubit.Presentation
  using (PauliGen ; _Clifford,_===_ ; conj ; corr ; vecToWord)
open import Examples.Groups.Pauli.Semantics p-2 p-prime using (pIₙ)
open import Examples.Groups.Pauli.Presentation p-2 p-prime using (Γ-H)
open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  using (module Simplified-Relations)
open Simplified-Relations using (M₋₁ ; _QRel,_===_)
  renaming (srel to ssrel ; order-S to sorder-S ; order-H to sorder-H)

-- The three supporting modules.
open import Examples.Groups.Clifford.Qubit.Selinger.Translation
open import Examples.Groups.Clifford.Qubit.Selinger.PauliWords
open import Examples.Groups.Clifford.Qubit.Selinger.GroupLike

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The round trip on the Figure-8 side
--
-- f ∘ g is the identity on gate generators, on the nose.

f-left-inv-gen : (x : Gen n) →
                 PB._≈_ (n CRel,_===_) [ x ]ʷ ((f ʷ) (g x))
f-left-inv-gen x = PB.refl

------------------------------------------------------------------------
-- Pauli generators as gate words
--
-- The Z generator on wire 0 is S², and this is immediate: it is exactly
-- the twisted relator for order-S, whose correction Z₀ is the single
-- nontrivial entry of corr in Qubit.Presentation.
--
-- Split on n: Presentation.Z₀ is defined by cases on the wire count, so
-- it does not reduce against Z-gen while n is a variable.

Z-gen-eq : (n : ℕ) →
           PB._≈_ ((₁₊ n) Clifford,_===_)
                  [ inj₁ (Z-gen {n}) ]ʷ ((g ʷ) (Z {n}))
Z-gen-eq zero =
  PB.sym (PB.trans (PB.axiom (_⋄_⋄_.mid (_∪_.right (tw (ssrel sorder-S)))))
                   PB.right-unit)
Z-gen-eq (₁₊ m) =
  PB.sym (PB.trans (PB.axiom (_⋄_⋄_.mid (_∪_.right (tw (ssrel sorder-S)))))
                   PB.right-unit)

------------------------------------------------------------------------
-- The reduction: everything left on the g side rests on M₋₁ ≈ ε
--
-- M₋₁ = M 1 = SHSHSH = (SH)³ is the scalar word.  It is trivial in the
-- phaseless Clifford group, but syntactically that is the statement that
-- the accumulated Pauli correction of Simplified.Lemmas.lemma-order-SH
-- vanishes — see the closing note.  Granting it, H² = ε follows at once
-- from the twisted relator for the simplified order-H, whose correction
-- is ε and whose right-hand side is M₋₁.

module Reduction
  (M₋₁≈ε : ∀ {n} → PB._≈_ ((₁₊ n) Clifford,_===_) [ M₋₁ {n} ]ᵣ ε)
  where

  H²≈ε : ∀ {n} → PB._≈_ ((₁₊ n) Clifford,_===_) [ Symplectic.H ^ 2 ]ᵣ ε
  H²≈ε = PB.trans (PB.axiom (_⋄_⋄_.mid (_∪_.right (tw (ssrel sorder-H)))))
                  (PB.trans PB.left-unit M₋₁≈ε)

  -- Z-gen-eq with the right embedding spelled out.
  Z-gen-eqᵣ : (n : ℕ) →
              PB._≈_ ((₁₊ n) Clifford,_===_) [ inj₁ (Z-gen {n}) ]ʷ [ Z {n} ]ᵣ
  Z-gen-eqᵣ n =
    Eq.subst (λ □ → PB._≈_ ((₁₊ n) Clifford,_===_) [ inj₁ (Z-gen {n}) ]ʷ □)
             (gʷ≡ᵣ (Z {n})) (Z-gen-eq n)

  -- conj carries the wire-0 Z generator to the wire-0 X generator, since
  -- actg H pZ = pX.  The trailing ε's are vecToWord's empty exponents.
  conj-eq : (n : ℕ) →
            PB._≈_ ((₁₊ n) Clifford,_===_)
                   [ conj (gate₁ H-gate) (Z-gen {n}) ]ₗ [ inj₁ (X-gen {n}) ]ʷ
  conj-eq zero   = PB.right-unit
  conj-eq (₁₊ m) = PB.trans (PB.cong PB.right-unit tail-ε) PB.right-unit
    where
    -- The tail is wmap inj₁ (wmap inj₂ (vecToWord pIₙ)); fuse the two
    -- relabellings, then collapse by pIw-ε at wire count ₁₊ m.
    tail-ε : PB._≈_ ((₂₊ m) Clifford,_===_)
                    (wmap inj₁ (wmap inj₂ (vecToWord (pIₙ {₁₊ m})))) ε
    tail-ε =
      Eq.subst (λ □ → PB._≈_ ((₂₊ m) Clifford,_===_) □ ε)
               (Eq.sym (wmap-∘ inj₁ inj₂ (vecToWord (pIₙ {₁₊ m}))))
               (pIw-ε ((₂₊ m) Clifford,_===_) (₁₊ m) (λ x → inj₁ (inj₂ x)))

  -- X = H Z H, and the two H's collapse by H² ≈ ε.
  X-gen-eq : (n : ℕ) →
             PB._≈_ ((₁₊ n) Clifford,_===_)
                    [ inj₁ (X-gen {n}) ]ʷ ((g ʷ) (X {n}))
  X-gen-eq n =
    Eq.subst (λ □ → PB._≈_ ((₁₊ n) Clifford,_===_) [ inj₁ (X-gen {n}) ]ʷ □)
             (gʷ≡ᵣ (X {n})) (PB.sym chain)
    where
    chain : PB._≈_ ((₁₊ n) Clifford,_===_) [ X {n} ]ᵣ [ inj₁ (X-gen {n}) ]ʷ
    chain =
      PB.trans (PB.cong PB.refl (PB.cong (PB.sym (Z-gen-eqᵣ n)) PB.refl))
        (PB.trans (PB.sym PB.assoc)
          (PB.trans (PB.cong (PB.axiom (_⋄_⋄_.mid (_∪_.left
                       (ConjRelʷ.comm (Z-gen {n}) (gate₁ H-gate))))) PB.refl)
            (PB.trans PB.assoc
              (PB.trans (PB.cong PB.refl H²≈ε)
                (PB.trans PB.right-unit (conj-eq n))))))

------------------------------------------------------------------------
-- fwd-pauli
--
-- The Pauli relations hold among the derived words.  At wire 0 they are
-- X² = Z² = ε and XZ = ZX; the `right` branch shifts and recurses; the
-- `mid` branch is disjoint-wire commutation.

pauli-rel : ∀ {n u v} → (Γ-H ⊕^ n) u v →
            PB._≈_ (n CRel,_===_) (Pw u) (Pw v)
pauli-rel {₁₊ zero} (_⋄_⋄_.left  CyS.order) = X²≈ε
pauli-rel {₁₊ zero} (_⋄_⋄_.right CyS.order) = Z²≈ε
pauli-rel {₁₊ zero} (_⋄_⋄_.mid (CommRel.comm tt tt)) = XZ.XZ≈ZX zero
pauli-rel {₂₊ m} (_⋄_⋄_.left (_⋄_⋄_.left  CyS.order)) = X²≈ε
pauli-rel {₂₊ m} (_⋄_⋄_.left (_⋄_⋄_.right CyS.order)) = Z²≈ε
pauli-rel {₂₊ m} (_⋄_⋄_.left (_⋄_⋄_.mid (CommRel.comm tt tt))) = XZ.XZ≈ZX (₁₊ m)
-- subst rather than rewrite: rewriting here hides the structural
-- recursion from the termination checker.
pauli-rel {₂₊ m} (_⋄_⋄_.right {u} {v} x) =
  Eq.subst₂ (PB._≈_ ((₂₊ m) CRel,_===_))
            (Eq.sym (Pw-↑ m u)) (Eq.sym (Pw-↑ m v))
            (lemma-cong↑ (Pw {₁₊ m} u) (Pw {₁₊ m} v) (pauli-rel x))
pauli-rel {₂₊ m} (_⋄_⋄_.mid (CommRel.comm (inj₁ tt) b)) =
  PB.sym (↑Comm.↑-comm-X (₁₊ m) (pauliGen→word b))
pauli-rel {₂₊ m} (_⋄_⋄_.mid (CommRel.comm (inj₂ tt) b)) =
  PB.sym (↑Comm.↑-comm-Z (₁₊ m) (pauliGen→word b))

fwd-pauli : ∀ {n u v} → (Γ-H ⊕^ n) u v →
            PB._≈_ (n CRel,_===_) ((f ʷ) [ u ]ₗ) ((f ʷ) [ v ]ₗ)
fwd-pauli {n} {u} {v} x
  rewrite fₗ≡Pw {n} u | fₗ≡Pw {n} v = pauli-rel x

------------------------------------------------------------------------
-- f-well-defined, split by axiom family
--
-- The extension relation is (Γ-H ⊕^ n) ⋄ EmptyRel ⋄ (ConjRelʷ ∪
-- RelTwist), so there are exactly three real cases; the EmptyRel factor
-- contributes none.  fwd-pauli is proved above; what remains is
--
--   fwd-conj — each gate conjugates each Pauli generator as conj says;
--   fwd-tw   — each simplified symplectic relator holds up to its
--              Pauli correction corr.

module F-WD
  (n : ℕ)
  (fwd-conj : (y : PauliGen n) (x : Gen n) →
              PB._≈_ (n CRel,_===_)
                     ((f ʷ) ([ [ x ]ʷ ]ᵣ • [ [ y ]ʷ ]ₗ))
                     ((f ʷ) ([ conj x y ]ₗ • [ [ x ]ʷ ]ᵣ)))
  (fwd-tw : ∀ {u v} (r̄ : (n QRel,_===_) u v) →
            PB._≈_ (n CRel,_===_)
                   ((f ʷ) [ u ]ᵣ) ((f ʷ) ([ corr r̄ ]ₗ • [ v ]ᵣ)))
  where

  f-well-defined : ∀ {w v} → (n Clifford,_===_) w v →
                   PB._≈_ (n CRel,_===_) ((f ʷ) w) ((f ʷ) v)
  f-well-defined (_⋄_⋄_.left x)  = fwd-pauli x
  f-well-defined (_⋄_⋄_.right ())
  f-well-defined (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm y x))) = fwd-conj y x
  f-well-defined (_⋄_⋄_.mid (_∪_.right (tw r̄)))             = fwd-tw r̄

------------------------------------------------------------------------
-- The isomorphism
--
-- Given the two well-definedness conditions and the round trip g ∘ f,
-- the two rule sets present the same group, and the isomorphism is (f ʷ).
-- Both group-likeness witnesses come from Selinger.GroupLike.

module Iso
  (n : ℕ)
  -- Every extension axiom holds among the derived Figure-8 words.
  (f-well-defined : ∀ {w v} → (n Clifford,_===_) w v →
                    PB._≈_ (n CRel,_===_) ((f ʷ) w) ((f ʷ) v))
  -- Every Figure-8 axiom (mod scalar) holds in the extension presentation.
  (g-well-defined : ∀ {u t} → (n CRel,_===_) u t →
                    PB._≈_ (n Clifford,_===_) ((g ʷ) u) ((g ʷ) t))
  -- Each Pauli generator equals its gate word, back in the extension.
  (g-left-inv-gen : (x : PauliGen n ⊎ Gen n) →
                    PB._≈_ (n Clifford,_===_) [ x ]ʷ ((g ʷ) (f x)))
  where

  private
    module GM = GroupMorphism (n Clifford,_===_) (n CRel,_===_)
                  (GL.grouplike-Cl n) grouplike-MS

  open GM.StarGroupIsomorphism f g
         f-well-defined f-left-inv-gen g-well-defined g-left-inv-gen
    public using (isGroupIsomorphism)

------------------------------------------------------------------------
-- What the remaining parameters amount to
--
-- g-left-inv-gen is the smallest.  On a gate generator it is refl; on a
-- Pauli generator it asks for Z = S² and X = HS²H inside
-- _Clifford,_===_.  Both wire-0 cases are proved:
--
--   * Z-gen-eq (unconditional) is exactly the twisted relator for
--     order-S, whose correction Z₀ is the one nontrivial entry of corr;
--   * Reduction.X-gen-eq follows from M₋₁ ≈ ε, via the conjugation axiom
--     for H (conj H Z-gen is the X generator, since actg H pZ = pX),
--     which turns [ X ]ᵣ into [ X-gen ]ₗ • [ H ² ]ᵣ, and then
--     Reduction.H²≈ε.
--
-- So the wire-0 half of g-left-inv-gen rests on the single lemma
--
--     M₋₁≈ε :  [ M₋₁ ]ᵣ  ≈  ε      in _Clifford,_===_,
--
-- where M₋₁ = M 1 = SHSHSH = (SH)³ is the scalar word.  The same lemma
-- is what C2 (H² = ε) and C4 ((SH)³ = ε) of g-well-defined need, so it
-- is the shared next target.  It says the accumulated Pauli correction
-- of Simplified.Lemmas.lemma-order-SH is trivial; corr-witness in
-- Presentation.Construct.Properties.Extension computes that correction
-- from the derivation, and discharging it means evaluating that word in
-- the Pauli presentation, where Pauli-presentation's injectivity reduces
-- it to a check in Pauli-group n.
--
-- What is still missing for g-left-inv-gen beyond M₋₁≈ε is the higher
-- wires: a Pauli generator inj₂ y sits at wire ≥ 1, and relating
-- _Clifford,_===_ at wire counts n and ₁₊ n needs a structural shift
-- lemma that has not been built.
--
-- f-well-defined is split by module F-WD above; fwd-pauli is proved, so
-- only fwd-conj and fwd-tw remain.  fwd-conj is one case per gate/Pauli
-- pair, matching conj against C6–C9.  fwd-tw is one case per simplified
-- symplectic relator, each holding up to its Pauli correction corr r̄; it
-- is the largest piece left.
--
-- g-well-defined is the converse: derive C2–C15 (with ω = ε) inside the
-- extension presentation.
--
-- These are the two substantive halves and are a large development —
-- essentially Selinger's completeness argument in both directions.
