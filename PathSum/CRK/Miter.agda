------------------------------------------------------------------------
-- Presentations of groups
--
-- The miter of a circuit over {H, CNOT, R_k, R_k†} (Amy, QPL 2018,
-- section 3)
--
-- Section 3 reduces checking a circuit C against a specification ξ to
-- checking that the miter ⟦ C† ⟧ ∘ ξ is the identity.  PathSum.Miter
-- does this for circuits over {H , S , CZ}; this module does it for
-- the paper's own gate set, with the inverse C† of PathSum.CRK.Adjoint.
-- The argument is PathSum.Miter's, over the gate matrices of
-- PathSum.CRK.Semantics.
--
-- C† inverts C on both sides, up to the scalar 2^k, k = norm C the
-- number of Hadamards (†-cancelʳ, †-cancelˡ).  This is proved on
-- columns, gate by gate, and with no appeal to unitarity: as
-- unnormalised matrices H H = 2, CNOT CNOT = 1 and R_k† R_k = 1 =
-- R_k R_k† (inv-cancel, from PathSum.Adjoint.Gates).  Gate by gate
-- means by induction on C, peeling its first gate g, which C† inverts
-- last; the factor 2^j accumulated so far passes through the gates
-- still to come, since a circuit commutes with every linear map on
-- amplitudes (applyᴬ-linear).  The other side needs no second
-- induction: C † † is C on the nose here, so C C† is (C†)† C†.  The
-- cancellations ask the column to see assignments only through their
-- values (Respects): H H and CNOT CNOT read the column at an
-- assignment only pointwise equal to z.
--
-- With these, the miter at one pair of columns is miterᶜ: a column ψ
-- with normalisation k is C applied to the column φ exactly when C†
-- sends ψ back to φ, the normalisations of ψ and of C both carried
-- over to φ's side.  Read at the basis columns through proposition
-- 2.10 (PathSum.CRK.Semantics), miterᶜ gives the headline results.
-- spec-miter: ⟦ C ⟧ ≋ ξ exactly when C† sends every column of ξ to the
-- matching basis column, scaled by the normalisations of ξ and C, for
-- any path-sum ξ, well formed or not.  miter: two circuits are
-- equivalent exactly when ⟦ C₁ ++ C₂ † ⟧ ≋ idPS.  The paper's miter
-- ⟦ C₂† ⟧ ∘ ⟦ C₁ ⟧ runs C₁ first, so for two circuits it is the circuit
-- C₁ ++ C₂ †, interpreted directly.  Consequences: C† is a two-sided
-- inverse up to ≋ (†-inverseʳ, †-inverseˡ), and appending a circuit on
-- the right both preserves and reflects ≋ (++-congʳ, ++-cancelʳ).
--
-- Two departures, both inherited from PathSum.CRK.Circuit: CNOT
-- carries a proof that its control and target differ -- which is what
-- makes it self-inverse, CNOT c c zeroing the target -- and R k is the
-- gate R_k only for k ≤ M; for larger k both R k and R† k denote R_M
-- and its inverse, so the cancellation holds for every k all the same.
--
-- Not here: the miter against a general ξ as a composition of
-- path-sums ⟦ C† ⟧ ∘ ξ (definition 2.6), which spec-miter states on
-- the columns of ξ; the composite itself, and prepending a circuit,
-- are PathSum.CRK.Miter.Compose.  Equivalence of Clifford circuits
-- decided through the miter is PathSum.CRK.Equivalence, and
-- translation validation at any level PathSum.CRK.Validation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _∸_)

module PathSum.CRK.Miter (M₀ : ℕ) where

open import Data.Integer.Base using (-_; _*_)
open import Data.Integer.Properties using (*-identityˡ)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using () renaming (_+_ to _ℕ+_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adjoint.Gates M₀ using
  (had-had; cnot-cnot; phase-cancel; phase-cancel⁻; had-linear;
   phase-linear; cnot-linear)
open import PathSum.AmpLinear M₀ using
  (Linear; ·ᴬ-linear; scale-linear; scale-+; scale-exp; scale-comm;
   scale-twice; pow-·ᴬ)
open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; idPS)
open import PathSum.CircuitSemantics M₀ using (Column; δ; δ-resp)
open import PathSum.CRK.Adjoint M using
  (inv; _†; †-involutive; norm-++; norm-†)
open import PathSum.CRK.Circuit M using
  (Gate; H; CNOT; R; R†; Circuit; norm; ⟦_⟧)
open import PathSum.CRK.Semantics M₀ using
  (gateᴬ; applyᴬ; applyᴬ-++; applyᴬ-cong; applyᴬ-resp; gateᴬ-resp;
   prop-2-10)
open import PathSum.CRK.Theorems M₀ using (circuit-≋-id)
open import PathSum.Cyclotomic M₀ using
  (_≐_; _·ᴬ_; scale; scale-map; scale-injective; Respects)
open import PathSum.Denotation M₀ using
  (amp; _≋_; ≋-refl; ≋-sym; ≋-trans; amp-≗)
open import PathSum.Order M using (pow)

import Data.Nat.Properties as ℕ

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Circuits commute with linear maps

-- A gate builds each new entry from old ones by sums, rotations and
-- moves, so a linear map applied to every entry before the gate may as
-- well be applied after it.

gateᴬ-linear : ∀ {f} → Linear f → (g : Gate n) (ψ : Column n) →
               ∀ z → gateᴬ g (λ u → f (ψ u)) z ≐ f (gateᴬ g ψ z)
gateᴬ-linear lin (H w)        ψ z = had-linear lin w ψ z
gateᴬ-linear lin (CNOT c t p) ψ z = cnot-linear lin c t ψ z
gateᴬ-linear lin (R k w)      ψ z =
  phase-linear lin (λ u → pow (M ∸ k) * [ u w ]ᶻ) ψ z
gateᴬ-linear lin (R† k w)     ψ z =
  phase-linear lin (λ u → - (pow (M ∸ k) * [ u w ]ᶻ)) ψ z

applyᴬ-linear : ∀ {f} → Linear f → (C : Circuit n) (ψ : Column n) →
                ∀ z → applyᴬ C (λ u → f (ψ u)) z ≐ f (applyᴬ C ψ z)
applyᴬ-linear         lin []      ψ z _ = refl
applyᴬ-linear {f = f} lin (g ∷ C) ψ z i =
  trans (applyᴬ-cong C {gateᴬ g (λ u → f (ψ u))} {λ u → f (gateᴬ g ψ u)}
                     (gateᴬ-linear lin g ψ) z i)
        (applyᴬ-linear lin C (gateᴬ g ψ) z i)

-- The gates of C ++ D act first to last: those of C, then those of D
-- (PathSum.CRK.Semantics's applyᴬ-++), here at one entry.

private
  ++-at : (C D : Circuit n) (ψ : Column n) →
          ∀ z → applyᴬ (C ++ D) ψ z ≐ applyᴬ D (applyᴬ C ψ) z
  ++-at C D ψ z i = cong (λ F → F z i) (applyᴬ-++ C D ψ)


------------------------------------------------------------------------
-- Each gate is inverted by inv

-- Up to the gate's own normalisation: 2 for a Hadamard, 1 for the
-- others.

inv-cancel : (g : Gate n) (ψ : Column n) → Respects ψ →
             ∀ z → gateᴬ (inv g) (gateᴬ g ψ) z ≐
                   pow (norm (g ∷ [])) ·ᴬ ψ z
inv-cancel (H w)        ψ resp z   = had-had w ψ resp z
inv-cancel (CNOT c t p) ψ resp z i =
  trans (cnot-cnot c t p ψ resp z i) (sym (*-identityˡ (ψ z i)))
inv-cancel (R k w)      ψ resp z i =
  trans (phase-cancel (λ u → pow (M ∸ k) * [ u w ]ᶻ) ψ z i)
        (sym (*-identityˡ (ψ z i)))
inv-cancel (R† k w)     ψ resp z i =
  trans (phase-cancel⁻ (λ u → pow (M ∸ k) * [ u w ]ᶻ) ψ z i)
        (sym (*-identityˡ (ψ z i)))


------------------------------------------------------------------------
-- C† inverts C

-- By induction on C, peeling its first gate g: C† ends with inv g, so
-- inv g is the first thing to meet g.  The normalisation 2^(norm C)
-- accumulated so far is an integer multiple, and passes through the
-- remaining gate by linearity.

†-cancelʳ : (C : Circuit n) (ψ : Column n) → Respects ψ →
            ∀ z → applyᴬ (C †) (applyᴬ C ψ) z ≐ pow (norm C) ·ᴬ ψ z
†-cancelʳ []      ψ resp z i = sym (*-identityˡ (ψ z i))
†-cancelʳ (g ∷ C) ψ resp z i =
  trans (cong (λ F → F z i)
              (applyᴬ-++ (C †) (inv g ∷ []) (applyᴬ C (gateᴬ g ψ))))
  (trans (applyᴬ-cong (inv g ∷ []) {applyᴬ (C †) (applyᴬ C (gateᴬ g ψ))}
                      {λ u → pow (norm C) ·ᴬ gateᴬ g ψ u}
                      (†-cancelʳ C (gateᴬ g ψ) (gateᴬ-resp g resp)) z i)
  (trans (applyᴬ-linear (·ᴬ-linear (pow (norm C))) (inv g ∷ [])
                        (gateᴬ g ψ) z i)
  (trans (cong (λ u → pow (norm C) * u) (inv-cancel g ψ resp z i))
  (trans (pow-·ᴬ (norm C) (norm (g ∷ [])) (ψ z) i)
         (cong (λ j → pow j * ψ z i)
               (trans (ℕ.+-comm (norm C) (norm (g ∷ [])))
                      (sym (norm-++ (g ∷ []) C))))))))

-- On the other side it is the same fact for C†, whose inverse is C.

†-cancelˡ : (C : Circuit n) (ψ : Column n) → Respects ψ →
            ∀ z → applyᴬ C (applyᴬ (C †) ψ) z ≐ pow (norm C) ·ᴬ ψ z
†-cancelˡ C ψ resp z i =
  trans (cong (λ D → applyᴬ D (applyᴬ (C †) ψ) z i) (sym (†-involutive C)))
    (trans (†-cancelʳ (C †) ψ resp z i)
           (cong (λ j → pow j * ψ z i) (norm-† C)))


------------------------------------------------------------------------
-- The miter at one pair of columns

-- ψ is a column read with normalisation 1/√2^k, φ one fed to C, which
-- normalises by 1/√2^j, j = norm C.  That ψ is C applied to φ says
-- √2^j ψ = √2^k C φ, cross-multiplied as PathSum.Denotation's ≋ is.
-- Applying C† and cancelling C† C = 2^j = √2^j √2^j turns this into
-- C† ψ = √2^(k+j) φ, and applying C and cancelling C C† turns it back:
-- both directions end with an equation between multiples by √2^j,
-- which cancel (Cyclotomic's scale-injective).

miterᶜ : (C : Circuit n) (k : ℕ) (ψ φ : Column n) → Respects ψ →
         Respects φ →
         ((∀ z → scale (norm C) (ψ z) ≐ scale k (applyᴬ C φ z)) ⇔
          (∀ z → applyᴬ (C †) ψ z ≐ scale (k ℕ+ norm C) (φ z)))
miterᶜ C k ψ φ rψ rφ = mk⇔ to from
  where
  to : (∀ z → scale (norm C) (ψ z) ≐ scale k (applyᴬ C φ z)) →
       ∀ z → applyᴬ (C †) ψ z ≐ scale (k ℕ+ norm C) (φ z)
  to E z = scale-injective (norm C) (applyᴬ (C †) ψ z)
                           (scale (k ℕ+ norm C) (φ z)) chain
    where
    chain : scale (norm C) (applyᴬ (C †) ψ z) ≐
            scale (norm C) (scale (k ℕ+ norm C) (φ z))
    chain i =
      trans (sym (applyᴬ-linear (scale-linear (norm C)) (C †) ψ z i))
      (trans (applyᴬ-cong (C †) {λ u → scale (norm C) (ψ u)}
                          {λ u → scale k (applyᴬ C φ u)} E z i)
      (trans (applyᴬ-linear (scale-linear k) (C †) (applyᴬ C φ) z i)
      (trans (scale-map k (†-cancelʳ C φ rφ z) i)
      (trans (sym (scale-map k (scale-twice (norm C) (φ z)) i))
      (trans (scale-+ k (norm C) (scale (norm C) (φ z)) i)
             (scale-comm (k ℕ+ norm C) (norm C) (φ z) i))))))

  from : (∀ z → applyᴬ (C †) ψ z ≐ scale (k ℕ+ norm C) (φ z)) →
         ∀ z → scale (norm C) (ψ z) ≐ scale k (applyᴬ C φ z)
  from F z = scale-injective (norm C) (scale (norm C) (ψ z))
                             (scale k (applyᴬ C φ z)) chain
    where
    chain : scale (norm C) (scale (norm C) (ψ z)) ≐
            scale (norm C) (scale k (applyᴬ C φ z))
    chain i =
      trans (scale-twice (norm C) (ψ z) i)
      (trans (sym (†-cancelˡ C ψ rψ z i))
      (trans (applyᴬ-cong C {applyᴬ (C †) ψ}
                          {λ u → scale (k ℕ+ norm C) (φ u)} F z i)
      (trans (applyᴬ-linear (scale-linear (k ℕ+ norm C)) C φ z i)
      (trans (sym (scale-+ k (norm C) (applyᴬ C φ z) i))
             (scale-comm k (norm C) (applyᴬ C φ z) i)))))


------------------------------------------------------------------------
-- Circuits against circuits, on matrices

-- ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ multiplies each side by the other's normalisation;
-- by proposition 2.10 it says the same of the circuits' matrices,
-- column by column.

circuit-≋ : (C₁ C₂ : Circuit n) →
            (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔
             (∀ x z → scale (norm C₂) (applyᴬ C₁ (δ x) z) ≐
                      scale (norm C₁) (applyᴬ C₂ (δ x) z)))
circuit-≋ C₁ C₂ = mk⇔
  (λ eq x z i → trans (sym (scale-map (norm C₂) (prop-2-10 C₁ x z) i))
    (trans (eq x z i) (scale-map (norm C₁) (prop-2-10 C₂ x z) i)))
  (λ eq x z i → trans (scale-map (norm C₂) (prop-2-10 C₁ x z) i)
    (trans (eq x z i) (sym (scale-map (norm C₁) (prop-2-10 C₂ x z) i))))


------------------------------------------------------------------------
-- The miter against a specification

-- Section 3: ⟦ C ⟧ ≡ ξ exactly when C† undoes ξ, with ξ's normalisation
-- and C's both carried to the other side.  Stated on columns -- C†
-- applied to each column of ξ gives the basis column.  Nothing is
-- assumed of ξ: the columns of any path-sum see assignments only
-- through their values (Denotation's amp-≗), which is all miterᶜ
-- needs.

spec-miter : (C : Circuit n) (ξ : PathSum n k m) →
             (⟦ C ⟧ ≋ ξ ⇔
              (∀ x z → applyᴬ (C †) (amp ξ x) z ≐
                       scale (k ℕ+ norm C) (δ x z)))
spec-miter {k = k} C ξ = mk⇔
  (λ eq x → Equivalence.to (at x) (λ z i →
     trans (sym (eq x z i)) (scale-map k (prop-2-10 C x z) i)))
  (λ eq x z i → trans (scale-map k (prop-2-10 C x z) i)
     (sym (Equivalence.from (at x) (eq x) z i)))
  where
  at : ∀ x →
       (∀ z → scale (norm C) (amp ξ x z) ≐ scale k (applyᴬ C (δ x) z)) ⇔
       (∀ z → applyᴬ (C †) (amp ξ x) z ≐ scale (k ℕ+ norm C) (δ x z))
  at x = miterᶜ C k (amp ξ x) (δ x)
                (λ z z′ zz → amp-≗ ξ x {z} {z′} zz) (δ-resp x)


------------------------------------------------------------------------
-- The miter of two circuits

-- The paper's miter ⟦ C₂† ⟧ ∘ ⟦ C₁ ⟧ runs C₁ first, so it is the
-- circuit C₁ ++ C₂ †, interpreted directly.  Its normalisation is the
-- two circuits' together, which the identity must match.

private
  norm-miter : (C₁ C₂ : Circuit n) →
               norm C₁ ℕ+ norm C₂ ≡ norm (C₁ ++ C₂ †)
  norm-miter C₁ C₂ =
    sym (trans (norm-++ C₁ (C₂ †))
               (cong (λ u → norm C₁ ℕ+ u) (norm-† C₂)))

miter : (C₁ C₂ : Circuit n) → (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔ ⟦ C₁ ++ C₂ † ⟧ ≋ idPS)
miter C₁ C₂ = mk⇔ to from
  where
  -- miterᶜ at the column C₁ makes of each basis state.

  at : ∀ x →
       (∀ z → scale (norm C₂) (applyᴬ C₁ (δ x) z) ≐
              scale (norm C₁) (applyᴬ C₂ (δ x) z)) ⇔
       (∀ z → applyᴬ (C₂ †) (applyᴬ C₁ (δ x)) z ≐
              scale (norm C₁ ℕ+ norm C₂) (δ x z))
  at x = miterᶜ C₂ (norm C₁) (applyᴬ C₁ (δ x)) (δ x)
                (applyᴬ-resp C₁ (δ-resp x)) (δ-resp x)

  to : ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ → ⟦ C₁ ++ C₂ † ⟧ ≋ idPS
  to eq = Equivalence.from (circuit-≋-id (C₁ ++ C₂ †)) (λ x z i →
    trans (++-at C₁ (C₂ †) (δ x) z i)
      (trans (Equivalence.to (at x)
                (Equivalence.to (circuit-≋ C₁ C₂) eq x) z i)
             (scale-exp (δ x z) (norm-miter C₁ C₂) i)))

  from : ⟦ C₁ ++ C₂ † ⟧ ≋ idPS → ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧
  from eq = Equivalence.from (circuit-≋ C₁ C₂) (λ x →
    Equivalence.from (at x) (λ z i →
      trans (sym (++-at C₁ (C₂ †) (δ x) z i))
        (trans (Equivalence.to (circuit-≋-id (C₁ ++ C₂ †)) eq x z i)
               (sym (scale-exp (δ x z) (norm-miter C₁ C₂) i)))))


------------------------------------------------------------------------
-- C† is a two-sided inverse, up to ≋

-- On the right it is the miter of C against itself; on the left it is
-- the right-hand fact for C†, whose inverse is C gate for gate.

†-inverseʳ : (C : Circuit n) → ⟦ C ++ C † ⟧ ≋ idPS
†-inverseʳ C = Equivalence.to (miter C C) (≋-refl {ξ = ⟦ C ⟧})

†-inverseˡ : (C : Circuit n) → ⟦ C † ++ C ⟧ ≋ idPS
†-inverseˡ C =
  subst (λ D → ⟦ C † ++ D ⟧ ≋ idPS) (†-involutive C) (†-inverseʳ (C †))


------------------------------------------------------------------------
-- Appending a circuit respects ≋

-- The circuit D appended after C and C′ commutes with the
-- normalisations, so it carries their equation along.

++-congʳ : (C C′ D : Circuit n) → ⟦ C ⟧ ≋ ⟦ C′ ⟧ →
           ⟦ C ++ D ⟧ ≋ ⟦ C′ ++ D ⟧
++-congʳ C C′ D eq =
  Equivalence.from (circuit-≋ (C ++ D) (C′ ++ D)) cols
  where
  E : ∀ x z → scale (norm C′) (applyᴬ C (δ x) z) ≐
              scale (norm C) (applyᴬ C′ (δ x) z)
  E = Equivalence.to (circuit-≋ C C′) eq

  -- Through D, at the columns of C and C′ on the basis state x.

  through : ∀ x z →
            scale (norm C′) (applyᴬ D (applyᴬ C (δ x)) z) ≐
            scale (norm C) (applyᴬ D (applyᴬ C′ (δ x)) z)
  through x z i =
    trans (sym (applyᴬ-linear (scale-linear (norm C′)) D
                              (applyᴬ C (δ x)) z i))
      (trans (applyᴬ-cong D {λ u → scale (norm C′) (applyᴬ C (δ x) u)}
                            {λ u → scale (norm C) (applyᴬ C′ (δ x) u)}
                            (E x) z i)
             (applyᴬ-linear (scale-linear (norm C)) D
                            (applyᴬ C′ (δ x)) z i))

  cols : ∀ x z → scale (norm (C′ ++ D)) (applyᴬ (C ++ D) (δ x) z) ≐
                 scale (norm (C ++ D)) (applyᴬ (C′ ++ D) (δ x) z)
  cols x z i =
    trans (scale-map (norm (C′ ++ D)) split i)
    (trans (scale-exp A (norm-++ C′ D) i)
    (trans (sym (scale-+ (norm C′) (norm D) A i))
    (trans (scale-comm (norm C′) (norm D) A i)
    (trans (scale-map (norm D) (through x z) i)
    (trans (scale-comm (norm D) (norm C) A′ i)
    (trans (scale-+ (norm C) (norm D) A′ i)
    (trans (scale-exp A′ (sym (norm-++ C D)) i)
           (sym (scale-map (norm (C ++ D)) split′ i)))))))))
    where
    A  = applyᴬ D (applyᴬ C (δ x)) z
    A′ = applyᴬ D (applyᴬ C′ (δ x)) z
    split  = ++-at C D (δ x) z
    split′ = ++-at C′ D (δ x) z

-- And D can be cancelled again, by appending D†: after any prefix C,
-- D followed by D† acts as nothing.

++-†-cancel : (C D : Circuit n) → ⟦ (C ++ D) ++ D † ⟧ ≋ ⟦ C ⟧
++-†-cancel C D =
  Equivalence.from (circuit-≋ ((C ++ D) ++ D †) C) (λ x z i →
    let X = applyᴬ C (δ x) z in
    trans (scale-map (norm C) (back x z) i)
    (trans (scale-map (norm C)
              (†-cancelʳ D (applyᴬ C (δ x)) (applyᴬ-resp C (δ-resp x))
                         z) i)
    (trans (sym (scale-map (norm C) (scale-twice (norm D) X) i))
    (trans (scale-+ (norm C) (norm D) (scale (norm D) X) i)
    (trans (scale-+ (norm C ℕ+ norm D) (norm D) X i)
           (scale-exp X norm-thrice i))))))
  where
  back : ∀ x z → applyᴬ ((C ++ D) ++ D †) (δ x) z ≐
                 applyᴬ (D †) (applyᴬ D (applyᴬ C (δ x))) z
  back x z i =
    trans (++-at (C ++ D) (D †) (δ x) z i)
          (cong (λ F → applyᴬ (D †) F z i) (applyᴬ-++ C D (δ x)))

  norm-thrice : (norm C ℕ+ norm D) ℕ+ norm D ≡ norm ((C ++ D) ++ D †)
  norm-thrice =
    sym (trans (norm-++ (C ++ D) (D †))
               (trans (cong (λ u → u ℕ+ norm (D †)) (norm-++ C D))
                      (cong (λ u → (norm C ℕ+ norm D) ℕ+ u)
                            (norm-† D))))

++-cancelʳ : (C C′ D : Circuit n) → ⟦ C ++ D ⟧ ≋ ⟦ C′ ++ D ⟧ →
             ⟦ C ⟧ ≋ ⟦ C′ ⟧
++-cancelʳ C C′ D eq =
  ≋-trans {ξ = ⟦ C ⟧} {ζ = ⟦ (C ++ D) ++ D † ⟧} {χ = ⟦ C′ ⟧}
    (≋-sym {ξ = ⟦ (C ++ D) ++ D † ⟧} {ζ = ⟦ C ⟧} (++-†-cancel C D))
    (≋-trans {ξ = ⟦ (C ++ D) ++ D † ⟧} {ζ = ⟦ (C′ ++ D) ++ D † ⟧}
             {χ = ⟦ C′ ⟧}
             (++-congʳ (C ++ D) (C′ ++ D) (D †) eq) (++-†-cancel C′ D))
