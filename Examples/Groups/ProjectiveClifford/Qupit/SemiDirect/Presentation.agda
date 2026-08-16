------------------------------------------------------------------------
-- Presentations of groups
--
-- The Pauli-by-symplectic semidirect product, presented.
--
-- SDProduct builds the relation
--
--   XZ n ⋄ Simplified n ⋄ ConjRelʷ conj
--
-- over the generators XZ.Gen n ⊎ Sym.Gen n: the Pauli rules on the
-- left, the simplified symplectic rules on the right, and the
-- conjugation rule h·n = (conj h n)·h in the middle.  The generic
-- machinery of Presentation.Construct.Properties.SemiDirectProduct
-- turns presentations of the two factors into a presentation of their
-- semidirect product, so all that is needed here is to feed it the
-- pieces.
--
-- Every input is a theorem, so the presentation below is
-- unconditional — no postulate, no hole, no hypothesis:
--
--   * the symplectic factor: Simplified.Presentation.presentation,
--     which presents Sp(2n, ℤ/pℤ);
--   * the Pauli factor: Pauli.Presentation-Alt's presentation, which
--     presents (ℤ/pℤ × ℤ/pℤ)ⁿ;
--   * the two well-definedness hypotheses on the conjugation action:
--     ConjAction.respects-Δ and ConjAction.respects-Γ (the `hyph` and
--     `hypn` that Iso.agda's commented-out attempt left open).
--
-- See the note at the foot of the file on how `Pauli⋊Sp` relates to
-- Semantics.agda's `Pauli⋊Sp-group`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --termination-depth=4 #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Presentation
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import Algebra.Bundles using (Group)
open import Data.Product using (_×_)
open import Level using (0ℓ)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
import Presentation.Construct.Properties.SemiDirectProduct as SDP'

open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Sp-group ; Symplectic ; _≈ˢ_ ; _∘ˢ_ ; module Interpretation)
open Symplectic using (ap)
open Interpretation using () renaming (⟦_⟧ to ⟦_⟧ˢ)
open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; _+ₚ_ ; +ₚ-group)
open import Examples.Construct.SemiDirectProduct.Clifford p-2 p-prime
  using (Pauli⋊Sp-group ; act-cong-ap)
import Examples.Groups.ProjectivePauli.Presentation-Alt p-2 p-prime as XZ
import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen as NSim
import Examples.Groups.Symplectic.Simplified.Presentation p-2 p-prime g* g-gen as SimPres
open import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Syntactics p-3 p-prime g* g-gen
  using (module SemiDirect)
import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.ConjAction p-3 p-prime g* g-gen as CA

------------------------------------------------------------------------
-- The instantiation, one width at a time

module Semidirect (n : ℕ) where

  -- The two factor relations and the conjugation action, as
  -- SemiDirectProduct expects them.
  Γ = XZ._QRel,_===_ n
  Δ = NSim.Simplified-Relations._QRel,_===_ n
  cj = SemiDirect.conj {n}

  private
    module SDP = SDP' Γ Δ cj

  open PB Γ using () renaming (_≈_ to _≈₁_)

  --------------------------------------------------------------------
  -- The presentation
  --
  -- Every input is a theorem: the two factor presentations, and the two
  -- well-definedness obligations proved in ConjAction.

  private
    module P = SDP.Presentation (CA.respects-Δ {n}) (CA.respects-Γ {n})
                 (+ₚ-group n) (Sp-group n)
                 (XZ.presentation {n}) (SimPres.presentation {n})

  -- The semidirect product of the Pauli group by Sp(2n, ℤ/pℤ), with the
  -- action transported through the two presentations.
  Pauli⋊Sp : Group 0ℓ 0ℓ
  Pauli⋊Sp = P.G1⋊G2

  -- The headline theorem: the relation SDProduct assembles presents
  -- that group.
  presentation : (SemiDirect._QRel,_===_ n) IsPresentationOf Pauli⋊Sp
  presentation = P.dpres

  --------------------------------------------------------------------
  -- The transported action is the linear action
  --
  -- This is the identification the note at the foot of the file records
  -- as outstanding, and it has to be stated here: `act` is a definition
  -- of the private module P, so no other file can name it.
  --
  -- `act S Q` conjugates REPRESENTATIVE words — inv₂ S and inv₁ Q,
  -- chosen by the two presentations' surjectivity — and reads the result
  -- back into the Pauli group.  ConjAction.conjw-sem says that reading
  -- is `ap` of the acting representative's denotation, and the two
  -- correction lemmas inv₁-corr / inv₂-corr then replace those
  -- denotations by the elements themselves.  Nothing has to be computed:
  -- the representatives stay abstract throughout.

  private
    -- The Pauli presentation's interpretation is Presentation-Alt's
    -- `sem`, and the simplified symplectic one is Interpretation.⟦_⟧;
    -- both are the extension of the same generator map, written out.
    pauli-sem : ∀ (w : Word (XZ.Gen n)) → P.⟦ w ⟧₁ ≡ XZ.sem w
    pauli-sem [ x ]ʷ  = Eq.refl
    pauli-sem ε       = Eq.refl
    pauli-sem (u • v) = Eq.cong₂ _+ₚ_ (pauli-sem u) (pauli-sem v)

    symp-sem : ∀ (c : Word (NSim.Symplectic.Gen n)) → P.⟦ c ⟧₂ ≡ ⟦ c ⟧ˢ
    symp-sem [ x ]ʷ  = Eq.refl
    symp-sem ε       = Eq.refl
    symp-sem (u • v) = Eq.cong₂ _∘ˢ_ (symp-sem u) (symp-sem v)

  -- ABSTRACT, and this matters to clients.  Both proofs go through
  -- P.inv₁ and P.inv₂, which are the SURJECTIVITY WITNESSES of the two
  -- factor presentations — existence proofs.  Left transparent, any
  -- conversion check a client makes that so much as considers unfolding
  -- `∙-agrees` drags those in and detonates (measured: a two-line lemma
  -- about Z ^ j went from 27 s to OOM at 12 GB).  Sealed, only the two
  -- TYPES escape, which is all anyone wants.
  abstract

    act≡ap : ∀ (S : Symplectic n) (Q : Pauli n) → P.act S Q ≡ ap S Q
    act≡ap S Q =
      Eq.trans (pauli-sem (SDP.conjss (P.inv₂ S) (P.inv₁ Q)))
        (Eq.trans (CA.conjw-sem (P.inv₂ S) (P.inv₁ Q))
                  (act-cong-ap {S = ⟦ P.inv₂ S ⟧ˢ} {T = S} symp-eq pauli-eq))
      where
      -- {S} and {T} are given by hand: _≈ˢ_ compares transformations
      -- through their ACTIONS, so unification eta-expands a Symplectic
      -- meta and leaves every field but `ap` unsolved.
      symp-eq : ⟦ P.inv₂ S ⟧ˢ ≈ˢ S
      symp-eq = Eq.subst (_≈ˢ S) (symp-sem (P.inv₂ S)) (P.inv₂-corr S)
      pauli-eq : XZ.sem (P.inv₁ Q) ≡ Q
      pauli-eq = Eq.trans (Eq.sym (pauli-sem (P.inv₁ Q))) (P.inv₁-corr Q)

    -- ... so the two semidirect products carry the very same
    -- multiplication.  Both are SDP.group (+ₚ-group n) (Sp-group n) at
    -- their respective actions, so carrier, equality, unit and inverse
    -- already agree definitionally, and this is all that was missing.
    ∙-agrees : ∀ (x y : Pauli n × Symplectic n) →
               Group._∙_ Pauli⋊Sp x y ≡ Group._∙_ (Pauli⋊Sp-group n) x y
    ∙-agrees (a , S) (b , T) = Eq.cong (λ z → (a +ₚ z) , (S ∘ˢ T)) (act≡ap S b)

------------------------------------------------------------------------
-- The theorem, at every width

-- The Pauli-by-symplectic relation presents the semidirect product of
-- the Pauli group by Sp(2n, ℤ/pℤ).
presentation : ∀ {n} →
               (SemiDirect._QRel,_===_ n) IsPresentationOf (Semidirect.Pauli⋊Sp n)
presentation {n} = Semidirect.presentation n

------------------------------------------------------------------------
-- A note on the group
--
-- The generic construction builds the semidirect product from the
-- *transported* action — a symplectic element acts on a Pauli by
-- conjugating representative words and re-interpreting — so Pauli⋊Sp is
-- that group rather than definitionally the `Pauli⋊Sp-group` of
-- Semantics.agda, whose action is `ap`.  ConjAction.conjw-sem is
-- exactly the statement that the two actions agree on representatives,
-- and `act≡ap` above turns that into the identification: the two
-- actions are equal outright, so by `∙-agrees` the two groups carry the
-- same multiplication and no transport is left to do.
--
-- For the record, the route the two obligations took (ConjAction) was
--
--   conj-sem : sem ((conj ⁿ') c w) ≡ actg c (sem w)
--
-- for a generator c, extended to words as
--
--   conjw-sem : sem ((conj ʰ') c w) ≡ ap ⟦ c ⟧ (sem w)
--
-- both by induction, from the fourteen generator cases of conj (each a
-- concrete ℤ/pℤ identity, e.g. conj H X = Z against actg H (₁,₀) =
-- (-₀,₁)).  Given the bridge:
--
--   * Respects-Γ: a Pauli rule gives sem u ≡ sem v (soundness), hence
--     actg c (sem u) ≡ actg c (sem v), hence the two conjugates have
--     equal readings, hence they are ≈ by completeness of the Pauli
--     presentation.
--
--   * Respects-Δ: a symplectic rule gives ⟦c⟧ ≈ˢ ⟦d⟧ (soundness of the
--     simplified presentation), i.e. ap ⟦c⟧ ≗ ap ⟦d⟧; the bridge turns
--     that into equal readings, and completeness again concludes.
--
-- So the long rules — M-power, semi-M*CZ, selinger-c10 … c15 — never
-- have to be conjugated by hand: they are handled by soundness of the
-- presentation they already have.
------------------------------------------------------------------------
