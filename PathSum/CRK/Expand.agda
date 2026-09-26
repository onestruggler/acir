------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits over {H, CNOT, R_k, R_k†}: translation validation beyond
-- Clifford, incomplete by reduction and complete by expansion
--
-- PathSum.CRK.Validation formalises the translation validation of
-- section 5.1 (Amy, QPL 2018): eliminate the miter C₁ ++ C₂ † to its
-- isometry restriction (section 4.1, PathSum.Gauss.Corollary.⟦_⟧ᴿ),
-- reduce with figure 2, and read the verdict off what is left.  For
-- Clifford circuits (level at most 2) every normal form settles it
-- (validation-clifford).  This module is what section 4 says about the
-- general case, at every level.
--
--  * Settled C₁ C₂: the miter's restriction reduces, by some chain of
--    figure 2, to a path-sum without path variables -- the case in which
--    the syntactic test decides the question (Validation.validation-any).
--    Validation is complete at a level d if every equivalent pair of
--    level at most d is settled (Complete d); and the refutation of
--    corollary 4.4 is sound at level d if an irreducible reduct with a
--    path variable left always refutes (StuckRefutes d).  Both hold at
--    level 2 (complete-2, stuck-refutes-2: lemma 4.3 through
--    PathSum.Full.Clifford).  Both fail at level 3 --
--    PathSum.Examples.ValidationIncomplete exhibits two equivalent
--    Clifford+T circuits whose miter's restriction is already
--    irreducible with seven path variables.  irreducible-unsettled is
--    the step from such a restriction to "not settled", and the
--    witness-… lemmas draw the rest from one such pair: the
--    restriction is the identity, neither property holds at the pair's
--    level, answering no instead of expanding is unsound, and normal
--    forms are not unique.
--  * The remedy of section 4, at the level of circuits: eliminate, then
--    run PathSum.Expand's procedure on the restriction -- normalise,
--    test syntactically or expand what is left.  circuit-decidableᵉ
--    decides ⟦ C ⟧ ≋ |x⟩ ↦ |x⟩ and validation-decidableᵉ decides
--    ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧, at every level; at level 2 the expansion never
--    accepts (validation-clifford-rejects), which is why
--    Validation.validation-decidable-clifford can do without it.
--  * The matrix of a circuit, gate by gate (MatrixId, matrix-id?,
--    circuit-id!, equivalent!, inequivalent!): the counterpart for this
--    gate set of PathSum.CRK.WithX's, through proposition 2.10
--    (PathSum.CRK.Semantics.prop-2-10).  It is not the paper's method;
--    it is how a closed identity that no rule proves is checked.
--  * A restriction reified in one elimination step, named and read
--    cheaply (restricted, restricted-ᴿ, restricted-irreducible,
--    restricted-congruent): the circuit-level form of
--    PathSum.Gauss.Single.  Where elimination ends is proved here for
--    every state (after-pivot and settled, private), so that at a
--    closed circuit only forms are computed -- which pivot elimination
--    picks, and what the wires hold after it -- never a phase.
--  * The names closed statements are made with (Miter, Restriction,
--    Restricts, Equivalent, IsIdentity; see that section for why).
--
-- Everything here is exponential: the matrix has 4^n entries computed
-- through every gate, and PathSum.Expand's procedure is exponential
-- (see its header).  The polynomial-time claims of the paper are not
-- formalised.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.CRK.Expand (M₀ : ℕ) where

open import Data.Bool.Base using (true; false; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (all?)
open import Data.Integer.Base using (0ℤ; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)
open import Data.List.Base using (_++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (zero; _≤_)
open import Data.Product.Base using (_×_; _,_; ∃; Σ; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂; [_,_]′)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using
  (Dec; yes; no; True; False; map′; toWitness; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Bool.Properties as Bool
import Data.Product.Properties as Product

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using (same-≗)
open import PathSum.Base using (PathSum; phase; idPS)
open import PathSum.Congruence M₀ using (Congruent; congruent?)
open import PathSum.Order M using (pow)
open import PathSum.CircuitSemantics M₀ using (Column; δ)
open import PathSum.Compose.Laws M₀ using (amp-idPS-δ)
open import PathSum.CRK.Adjoint M using (_†; level-miter)
open import PathSum.CRK.Circuit M using
  (Circuit; norm; level; paths; ⟦_⟧; State; sig)
open import PathSum.CRK.Miter M₀ using (miter)
open import PathSum.CRK.Semantics M₀ using
  (applyᴬ; applyᴬ-resp; applyᴬ-cong; prop-2-10)
open import PathSum.CRK.Validation M₀ using
  (validation-reduct; validation-refuted-gauss;
   validation-clifford-refutes)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; zpow; _≐_; scale; scale-map; Respects)
open import PathSum.Decide M₀ using (search)
open import PathSum.Denotation M₀ using (Assign; _≋_)
open import PathSum.Expand M₀ using
  (Verdict; Accepts; Expanded; decide-id; clifford-rejects;
   UniqueNormalForms; unique⇒no-expansion)
open import PathSum.Full M using (_⟶ᶠ*_; εᶠ; ⟶*⇒⟶ᶠ*)
open import PathSum.Full.Match M using (Irreducibleᶠ)
open import PathSum.Full.Obstruction M using
  (Obstructed; obstructed?; obstructed⇒irreducible; irreducible-stuck)
open import PathSum.Gauss M₀ using
  (Gauss; refuted; reduced; Reified; gauss; gauss-by; step; sol; restrict)
open import PathSum.Gauss.Corollary M₀ using
  (⟦_⟧ᴿ; stateᶜ; restriction; not-id-gauss; lemma-4-1-gauss;
   identity-reifies; identity-reduces; ⟦⟧ᴿ-Internal; ⟦⟧ᴿ-Ord≤2)
open import PathSum.Gauss.Forms using
  (pivot; none; pivot?; coefʸ; coefʸ-x; some-or-all; verdict; not-≢)
open import PathSum.Gauss.Single M₀ using
  (pivot-first; fast-step; step-phase; step-obstructed)
open import PathSum.Linear using (Lin; varᴸ; valᴸ; valᴸ-var)
open import PathSum.Polynomial using (x[_]; _≟ᵐ_)

private
  variable
    n m m′ : ℕ


------------------------------------------------------------------------
-- Statements about closed circuits

-- The facts below are stated through these names, whose arguments are
-- the circuits (the convention of PathSum.Examples.Base), and a closed
-- client states its facts through them too -- referring to them in
-- this module itself, at its parameter (E.Restricts 0 ...), not in a
-- module application of it.  Otherwise a closed statement is matched
-- against the lemma proving it by computing both sides: the two
-- computations read back terms that are equal but not syntactically
-- so, and Agda compares them by unfolding the substitution in the
-- phases (a restriction equation at eight path variables took 50 s
-- and 6 GB that way, where it now takes no time).  For the same reason
-- a client spells each index one way throughout (the lemmas below
-- produce suc m′, not a numeral).

-- The miter of section 5.1.

Miter : Circuit n → Circuit n → Circuit n
Miter C₁ C₂ = C₁ ++ C₂ †

-- A restriction of C, with m path variables: its normalisation is
-- C's, spelt as this module spells it.

Restriction : Circuit n → ℕ → Set
Restriction {n} C m = PathSum n (norm C) m

-- Elimination reifies the restriction of C as ξ.

Restricts : (C : Circuit n) → PathSum n (norm C) m → Set
Restricts {m = m} C ξ = ⟦ C ⟧ᴿ ≡ just (m , ξ)

-- Two circuits are equivalent.

Equivalent : Circuit n → Circuit n → Set
Equivalent C₁ C₂ = ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧

-- A path-sum is the identity.  Opaque, so that two statements of it are
-- compared by their arguments: unfolded, _≋_ is compared through the
-- amplitudes, which at a closed restriction sum all its paths as soon
-- as anything differs between the two sides (minutes, where the
-- opaque statement takes no time).  IsIdentity⇔ opens it.

opaque
  IsIdentity : ∀ {k} → PathSum n k m → Set
  IsIdentity ξ = ξ ≋ idPS

  IsIdentity⇔ : ∀ {k} (ξ : PathSum n k m) → (IsIdentity ξ ⇔ ξ ≋ idPS)
  IsIdentity⇔ ξ = mk⇔ (λ h → h) (λ h → h)


------------------------------------------------------------------------
-- The matrix of a circuit

-- A circuit is the identity exactly when its matrix, computed gate by
-- gate and left unnormalised, is √2^(norm C) times the identity.

MatrixId : Circuit n → Set
MatrixId C = ∀ x z → applyᴬ C (δ x) z ≐ scale (norm C) (δ x z)

circuit-≋-id : (C : Circuit n) → (⟦ C ⟧ ≋ idPS ⇔ MatrixId C)
circuit-≋-id C = mk⇔
  (λ eq x z i → trans (sym (prop-2-10 C x z i))
    (trans (eq x z i) (scale-map (norm C) (amp-idPS-δ x z) i)))
  (λ eq x z i → trans (prop-2-10 C x z i)
    (trans (eq x z i) (sym (scale-map (norm C) (amp-idPS-δ x z) i))))

private
  -- A decidable property that reads assignments only through their
  -- values holds everywhere or fails somewhere (PathSum.Decide.search).

  every? : {P : Assign n → Set} → (∀ x → Dec (P x)) →
           (∀ {x x′} → (∀ i → x i ≡ x′ i) → P x → P x′) →
           Dec (∀ x → P x)
  every? {P = P} P? resp =
    [ yes , (λ (x , ¬p) → no (λ h → ¬p (h x))) ]′ (search P P? resp)

  coords? : (a b : Amp) → Dec (a ≐ b)
  coords? a b = all? (λ i → a i ≟ℤ b i)

  δ-resp : (x : Assign n) → Respects (δ x)
  δ-resp x z z′ zz i = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i)
    (same-≗ {x = x} {x′ = x} {z = z} {z′ = z′} (λ _ → refl) zz)

  δ-≗ : {x x′ : Assign n} → (∀ i → x i ≡ x′ i) → ∀ z → δ x z ≐ δ x′ z
  δ-≗ {x = x} {x′} xx z i = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i)
    (same-≗ {x = x} {x′ = x′} {z = z} {z′ = z} xx (λ _ → refl))

-- Every entry, every coordinate.

matrix-id? : (C : Circuit n) → Dec (MatrixId C)
matrix-id? {n} C = every? (λ x → every? (entry? x) (resp-z x)) resp-x
  where
  Entry : Assign n → Assign n → Set
  Entry x z = applyᴬ C (δ x) z ≐ scale (norm C) (δ x z)

  entry? : ∀ x z → Dec (Entry x z)
  entry? x z = coords? (applyᴬ C (δ x) z) (scale (norm C) (δ x z))

  resp-z : ∀ x {z z′} → (∀ w → z w ≡ z′ w) → Entry x z → Entry x z′
  resp-z x {z} {z′} zz e i =
    trans (sym (applyᴬ-resp C (δ-resp x) z z′ zz i))
      (trans (e i) (scale-map (norm C) (δ-resp x z z′ zz) i))

  resp-x : ∀ {x x′} → (∀ i → x i ≡ x′ i) →
           (∀ z → Entry x z) → ∀ z → Entry x′ z
  resp-x {x} {x′} xx h z i =
    trans (sym (applyᴬ-cong C {δ x} {δ x′} (δ-≗ xx) z i))
      (trans (h z i) (scale-map (norm C) (δ-≗ xx z) i))

-- A closed circuit whose matrix computes to the identity is the
-- identity, and one whose matrix computes to something else is not;
-- two circuits whose miter's matrix computes to the identity are
-- equivalent (PathSum.CRK.Miter.miter).

circuit-id! : (C : Circuit n) → {True (matrix-id? C)} → ⟦ C ⟧ ≋ idPS
circuit-id! C {t} =
  Equivalence.from (circuit-≋-id C) (toWitness {a? = matrix-id? C} t)

circuit-not-id! : (C : Circuit n) → {False (matrix-id? C)} →
                  ¬ (⟦ C ⟧ ≋ idPS)
circuit-not-id! C {f} eq =
  toWitnessFalse {a? = matrix-id? C} f (Equivalence.to (circuit-≋-id C) eq)

equivalent! : (C₁ C₂ : Circuit n) → {True (matrix-id? (Miter C₁ C₂))} →
              Equivalent C₁ C₂
equivalent! C₁ C₂ {t} =
  Equivalence.from (miter C₁ C₂) (circuit-id! (C₁ ++ C₂ †) {t})

inequivalent! : (C₁ C₂ : Circuit n) → {False (matrix-id? (Miter C₁ C₂))} →
                ¬ Equivalent C₁ C₂
inequivalent! C₁ C₂ {f} e =
  circuit-not-id! (C₁ ++ C₂ †) {f} (Equivalence.to (miter C₁ C₂) e)


------------------------------------------------------------------------
-- A restriction reified in one elimination step

-- The circuit's state, read at a number of path variables given by an
-- equation (at a closed circuit, refl).

stateᵉ : (C : Circuit n) → paths C ≡ m → State n m
stateᵉ {n = n} C e = subst (State n) e (stateᶜ C)

-- The state a run of elimination ends in, when it reifies.

restrictionˢ : {st : State n m} → Gauss st → Maybe (Σ ℕ (State n))
restrictionˢ (refuted _ _) = nothing
restrictionˢ (reduced r)   = just (Reified.m′ r , Reified.final r)

-- Where it ends is established here for any state, not by computing
-- at a closed one.  At a closed state Agda's reduction shares work
-- between the two sides of an equation and reads back terms that are
-- equal but no longer syntactically so, and then compares the phases
-- of the two ends by unfolding the substitution into its double sum
-- over all monomials (about 70 s at six path variables, sixteen times
-- as much for every two more).

private
  -- Past a pivot, elimination only relays the rest.

  after-pivot : (st : State n (suc m)) (w : Fin n) (j : Fin (suc m))
                (piv : coefʸ (sig st w) j ≡ true) →
                restrictionˢ (gauss-by st (pivot w j piv)) ≡
                restrictionˢ (gauss (step st w j))
  after-pivot st w j piv with gauss (step st w j)
  ... | refuted _ _ = refl
  ... | reduced _   = refl

  -- A state whose every wire holds its input already is the end.

  -- (Elimination inspects the number of path variables first, so the
  -- proof does too.)

  no-pivot : (st : State n m) → (∀ v → sig st v ≡ varᴸ x[ v ]) →
             ∀ v j → coefʸ (sig st v) j ≡ true → ⊥
  no-pivot st outs v j piv = contradiction
    (trans (sym piv) (subst (λ l → coefʸ l j ≡ false) (sym (outs v))
                            (coefʸ-x v j)))
    (λ ())

  no-miss : (st : State n m) → (∀ v → sig st v ≡ varᴸ x[ v ]) →
            ∀ v x → (∀ y → valᴸ (sig st v) x y ≡ not (x v)) → ⊥
  no-miss {m = m} st outs v x miss = contradiction
    (trans (sym (miss (λ _ → false)))
           (subst (λ l → valᴸ l x (λ _ → false) ≡ x v) (sym (outs v))
                  (valᴸ-var {m = m} x[ v ] x (λ _ → false))))
    (not-≢ (x v))

  settled : (st : State n m) → (∀ v → sig st v ≡ varᴸ x[ v ]) →
            restrictionˢ (gauss st) ≡ just (m , st)
  settled {m = zero} st outs with pivot? (sig st)
  ... | pivot v () piv
  ... | none free with some-or-all (λ v → verdict (sig st v) v (free v))
  ...   | inj₂ _             = refl
  ...   | inj₁ (v , x , miss) = ⊥-elim (no-miss st outs v x miss)
  settled {m = suc m} st outs with pivot? (sig st)
  ... | pivot v j piv = ⊥-elim (no-pivot st outs v j piv)
  ... | none free with some-or-all (λ v → verdict (sig st v) v (free v))
  ...   | inj₂ _             = refl
  ...   | inj₁ (v , x , miss) = ⊥-elim (no-miss st outs v x miss)

  restriction-subst : ∀ {k q} (st : State n q) (e : q ≡ m) →
                      restriction {k = k} (gauss st) ≡
                      restriction {k = k} (gauss (subst (State n) e st))
  restriction-subst st refl = refl

  restriction-ˢ : ∀ {k} {st : State n m} (g : Gauss st) {s : State n m′} →
                  restrictionˢ g ≡ just (m′ , s) →
                  restriction {k = k} g ≡ just (m′ , restrict s)
  restriction-ˢ (refuted _ _) ()
  restriction-ˢ (reduced r)   refl = refl

-- The restriction of one step of elimination, at the pivot (w , j).

restricted : (C : Circuit n) → paths C ≡ suc m → Fin n → Fin (suc m) →
             PathSum n (norm C) m
restricted C e w j = restrict (step (stateᵉ C e) w j)

-- Elimination pivots at (w , j) and then every wire holds its input:
-- ⟦ C ⟧ᴿ is that restriction.  At a closed circuit the hypotheses are
-- checked by computation on forms alone -- which pivot elimination
-- picks, and what the wires hold after the step -- never on phases.

restricted-ᴿ : (C : Circuit n) (e : paths C ≡ suc m) (w : Fin n)
  (j : Fin (suc m)) (piv : coefʸ (sig (stateᵉ C e) w) j ≡ true) →
  pivot? (sig (stateᵉ C e)) ≡ pivot w j piv →
  (∀ v → sig (step (stateᵉ C e) w j) v ≡ varᴸ x[ v ]) →
  Restricts C (restricted C e w j)
restricted-ᴿ C e w j piv e₁ outs =
  trans (restriction-subst (stateᶜ C) e)
    (trans (pivot-first (stateᵉ C e) w j piv e₁)
      (restriction-ˢ (gauss-by (stateᵉ C e) (pivot w j piv))
        (trans (after-pivot (stateᵉ C e) w j piv)
               (settled (step (stateᵉ C e) w j) outs))))

-- With the wires' forms decided.

_≟ᴸ_ : (l l′ : Lin n m) → Dec (l ≡ l′)
_≟ᴸ_ = Product.≡-dec Bool._≟_ _≟ᵐ_

outputs? : (st : State n m) → Dec (∀ v → sig st v ≡ varᴸ x[ v ])
outputs? st = all? (λ v → sig st v ≟ᴸ varᴸ x[ v ])

restricted-ᴿ! : (C : Circuit n) (e : paths C ≡ suc m) (w : Fin n)
  (j : Fin (suc m)) (piv : coefʸ (sig (stateᵉ C e) w) j ≡ true) →
  pivot? (sig (stateᵉ C e)) ≡ pivot w j piv →
  {True (outputs? (step (stateᵉ C e) w j))} →
  Restricts C (restricted C e w j)
restricted-ᴿ! C e w j piv e₁ {t} =
  restricted-ᴿ C e w j piv e₁
    (toWitness {a? = outputs? (step (stateᵉ C e) w j)} t)

-- The certificate of PathSum.Full.Obstruction at any number of path
-- variables: it is stated for at least two, and fails below.  (The
-- number is left general so that a closed client can name it by one
-- numeral throughout: 7 and suc (suc 5) are different terms, and Agda
-- compares two restrictions indexed by them by unfolding their phases.)

Obstructedᵐ : ∀ {k} → Fin n → PathSum n k m → Set
Obstructedᵐ {m = suc (suc _)} i ξ = Obstructed i ξ
Obstructedᵐ {m = zero}        i ξ = ⊥
Obstructedᵐ {m = suc zero}    i ξ = ⊥

obstructedᵐ? : ∀ {k} (i : Fin n) (ξ : PathSum n k m) → Dec (Obstructedᵐ i ξ)
obstructedᵐ? {m = suc (suc _)} i ξ = obstructed? i ξ
obstructedᵐ? {m = zero}        i ξ = no λ ()
obstructedᵐ? {m = suc zero}    i ξ = no λ ()

-- When the step solves y_j = x_w, the certificate, computed on the
-- cheap phase of PathSum.Gauss.Single.fast-step, shows the restriction
-- irreducible.

restricted-irreducible :
  (C : Circuit n) (e : paths C ≡ suc m) (w : Fin n) (j : Fin (suc m))
  (i : Fin n) → sol (stateᵉ C e) w j ≡ varᴸ x[ w ] →
  Obstructedᵐ i (fast-step {k = 0} (stateᵉ C e) w j) →
  Irreducibleᶠ (restricted C e w j)
restricted-irreducible {m = suc (suc _)} C e w j i s obs =
  obstructed⇒irreducible i (restricted C e w j)
    (step-obstructed {k′ = 0} {k = norm C} i (stateᵉ C e) w j s obs)
restricted-irreducible {m = zero}        C e w j i s ()
restricted-irreducible {m = suc zero}    C e w j i s ()

restricted-irreducible! :
  (C : Circuit n) (e : paths C ≡ suc m) (w : Fin n) (j : Fin (suc m))
  (i : Fin n) → {True (sol (stateᵉ C e) w j ≟ᴸ varᴸ x[ w ])} →
  {True (obstructedᵐ? i (fast-step {k = 0} (stateᵉ C e) w j))} →
  Irreducibleᶠ (restricted C e w j)
restricted-irreducible! C e w j i {s} {t} =
  restricted-irreducible C e w j i
    (toWitness {a? = sol (stateᵉ C e) w j ≟ᴸ varᴸ x[ w ]} s)
    (toWitness {a? = obstructedᵐ? i (fast-step {k = 0} (stateᵉ C e) w j)} t)

-- Its phase, read off coefficient by coefficient: congruent to any
-- path-sum the cheap phase is congruent to (PathSum.Congruence).

restricted-congruent :
  (C : Circuit n) (e : paths C ≡ suc m) (w : Fin n) (j : Fin (suc m)) →
  sol (stateᵉ C e) w j ≡ varᴸ x[ w ] →
  ∀ {k′} {ζ : PathSum n k′ m} →
  Congruent (fast-step {k = 0} (stateᵉ C e) w j) ζ →
  Congruent (restricted C e w j) ζ
restricted-congruent C e w j s {ζ = ζ} (outs , ph) = outs , λ γ →
  subst (λ a → pow M ∣ (a - phase ζ γ))
        (sym (step-phase {k = norm C} {k′ = 0} (stateᵉ C e) w j s γ))
        (ph γ)

restricted-congruent! :
  (C : Circuit n) (e : paths C ≡ suc m) (w : Fin n) (j : Fin (suc m)) →
  {True (sol (stateᵉ C e) w j ≟ᴸ varᴸ x[ w ])} →
  ∀ {k′} (ζ : PathSum n k′ m) →
  {True (congruent? (fast-step {k = 0} (stateᵉ C e) w j) ζ)} →
  Congruent (restricted C e w j) ζ
restricted-congruent! C e w j {s} {k′} ζ {t} =
  restricted-congruent C e w j
    (toWitness {a? = sol (stateᵉ C e) w j ≟ᴸ varᴸ x[ w ]} s) {k′} {ζ}
    (toWitness {a? = congruent? (fast-step {k = 0} (stateᵉ C e) w j) ζ} t)


------------------------------------------------------------------------
-- When reduction settles translation validation

-- The miter's restriction reduces to a path-sum without path variables,
-- which the syntactic test then decides (Validation.validation-any).

Settled : Circuit n → Circuit n → Set
Settled {n} C₁ C₂ =
  ∃ λ m′ → ∃ λ (ξ : PathSum n (norm (Miter C₁ C₂)) m′) →
    Restricts (Miter C₁ C₂) ξ ×
    ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) → ξ ⟶ᶠ* ξ′

-- Translation validation by reduction is complete at level d: every
-- equivalent pair of circuits of level at most d is settled.

Complete : ℕ → Set
Complete d = ∀ {n} (C₁ C₂ : Circuit n) → level C₁ ≤ d → level C₂ ≤ d →
             Equivalent C₁ C₂ → Settled C₁ C₂

-- The refutation of corollary 4.4 is sound at level d: a reduct of the
-- restriction to which no rule applies, with a path variable left,
-- refutes.

StuckRefutes : ℕ → Set
StuckRefutes d =
  ∀ {n} (C₁ C₂ : Circuit n) → level C₁ ≤ d → level C₂ ≤ d →
  ∀ {m′} {ξ : PathSum n (norm (Miter C₁ C₂)) m′} →
  Restricts (Miter C₁ C₂) ξ →
  ∀ {k′ m″} {ξ′ : PathSum n k′ (suc m″)} → ξ ⟶ᶠ* ξ′ → Irreducibleᶠ ξ′ →
  ¬ Equivalent C₁ C₂

-- Both hold for Clifford circuits: the restriction of an identity
-- miter reduces to a syntactic identity by lemma 4.3 ...

complete-2 : Complete 2
complete-2 C₁ C₂ lv₁ lv₂ e =
  by (identity-reifies (C₁ ++ C₂ †) C≋id)
  where
  C≋id = Equivalence.to (miter C₁ C₂) e
  lv   = level-miter C₁ C₂ lv₁ lv₂

  by : (∃ λ m′ → ∃ λ ξ → ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ)) → Settled C₁ C₂
  by (m′ , ξ , eq) =
    m′ , ξ , eq , 0 , proj₁ r , ⟶*⇒⟶ᶠ* (proj₁ (proj₂ r))
    where
    r = identity-reduces (C₁ ++ C₂ †) lv {ξ = ξ} eq C≋id

-- ... and every step of figure 2 keeps it Clifford
-- (Validation.validation-clifford-refutes).

stuck-refutes-2 : StuckRefutes 2
stuck-refutes-2 C₁ C₂ lv₁ lv₂ eq steps irr =
  validation-clifford-refutes C₁ C₂ lv₁ lv₂ eq steps irr

-- A restriction that is itself irreducible, with a path variable left,
-- is never settled: the only chain out of it is the empty one.

irreducible-unsettled :
  (C₁ C₂ : Circuit n) {ξ : PathSum n (norm (Miter C₁ C₂)) (suc m′)} →
  Restricts (Miter C₁ C₂) ξ → Irreducibleᶠ ξ →
  ¬ Settled C₁ C₂
irreducible-unsettled {n = n} {m′ = m′} C₁ C₂ {ξ} eq irr
                      (_ , _ , eq′ , _ , ξ′ , steps) =
  go (trans (sym eq) eq′) steps
  where
  go : ∀ {m″} {ξ″ : PathSum n (norm (C₁ ++ C₂ †)) m″} →
       just (suc m′ , ξ) ≡ just (m″ , ξ″) → ξ″ ⟶ᶠ* ξ′ → ⊥
  go refl s = irreducible-stuck ξ irr s


------------------------------------------------------------------------
-- What one equivalent pair with an irreducible restriction refutes

-- Two equivalent circuits whose miter's restriction ξ is irreducible
-- with a path variable left.  Then ξ is the identity (lemma 4.1 at the
-- miter), though no rule of figure 2 applies to it; and so neither
-- completeness nor the refutation of corollary 4.4 holds at any level
-- the pair has, the refutation that answers no without expanding is
-- unsound, and normal forms are not unique.

module _ {n : ℕ} (C₁ C₂ : Circuit n) {m′ : ℕ}
         {ξ : PathSum n (norm (Miter C₁ C₂)) (suc m′)}
         (eq : Restricts (Miter C₁ C₂) ξ) (irr : Irreducibleᶠ ξ)
         (e : Equivalent C₁ C₂) where

  witness-id : IsIdentity ξ
  witness-id = Equivalence.from (IsIdentity⇔ ξ) id≋
    where
    id≋ : ξ ≋ idPS
    id≋ = Equivalence.to (validation-reduct C₁ C₂ eq {ξ″ = ξ} εᶠ) e

  witness-not-complete : ∀ {d} → level C₁ ≤ d → level C₂ ≤ d →
                         ¬ Complete d
  witness-not-complete lv₁ lv₂ c =
    irreducible-unsettled C₁ C₂ eq irr (c C₁ C₂ lv₁ lv₂ e)

  witness-not-stuck-refutes : ∀ {d} → level C₁ ≤ d → level C₂ ≤ d →
                              ¬ StuckRefutes d
  witness-not-stuck-refutes lv₁ lv₂ s =
    s C₁ C₂ lv₁ lv₂ eq {ξ′ = ξ} εᶠ irr e

  witness-shortcut-unsound :
    ¬ (∀ {n k m} (ζ : PathSum n k (suc m)) → Irreducibleᶠ ζ →
       ¬ (ζ ≋ idPS))
  witness-shortcut-unsound claim =
    claim ξ irr (Equivalence.to (IsIdentity⇔ ξ) witness-id)

  witness-not-unique : ¬ UniqueNormalForms
  witness-not-unique u = unique⇒no-expansion u ξ irr
    (Equivalence.to (IsIdentity⇔ ξ) witness-id)


------------------------------------------------------------------------
-- The remedy: expand what reduction leaves

-- A circuit is the identity exactly when its restriction is (lemma 4.1
-- at the circuit), which PathSum.Expand decides: elimination, then
-- normalisation, then the syntactic test or the expansion.

circuit-decidableᵉ : (C : Circuit n) → Dec (⟦ C ⟧ ≋ idPS)
circuit-decidableᵉ {n} C = by ⟦ C ⟧ᴿ refl
  where
  by : (r : Maybe (Σ ℕ (PathSum n (norm C)))) → ⟦ C ⟧ᴿ ≡ r →
       Dec (⟦ C ⟧ ≋ idPS)
  by nothing         eq = no (not-id-gauss C eq)
  by (just (m′ , ξ)) eq =
    map′ (Equivalence.from (lemma-4-1-gauss C eq))
         (Equivalence.to (lemma-4-1-gauss C eq)) (decide-id ξ)

-- Translation validation, complete at every level.

validation-decidableᵉ : (C₁ C₂ : Circuit n) → Dec (Equivalent C₁ C₂)
validation-decidableᵉ {n} C₁ C₂ = by ⟦ C₁ ++ C₂ † ⟧ᴿ refl
  where
  by : (r : Maybe (Σ ℕ (PathSum n (norm (C₁ ++ C₂ †))))) →
       ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ r → Dec (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
  by nothing         eq = no (validation-refuted-gauss C₁ C₂ eq)
  by (just (m′ , ξ)) eq =
    map′ (Equivalence.from iff) (Equivalence.to iff) (decide-id ξ)
    where
    iff = validation-reduct C₁ C₂ eq {ξ″ = ξ} εᶠ

-- For Clifford circuits the expanded branch never accepts: the
-- restriction is Clifford, and PathSum.Expand.clifford-rejects applies.

validation-clifford-rejects :
  (C₁ C₂ : Circuit n) → level C₁ ≤ 2 → level C₂ ≤ 2 →
  {ξ : PathSum n (norm (Miter C₁ C₂)) m′} →
  Restricts (Miter C₁ C₂) ξ →
  (v : Verdict ξ) → Expanded v → ¬ Accepts v
validation-clifford-rejects C₁ C₂ lv₁ lv₂ eq =
  clifford-rejects
    (⟦⟧ᴿ-Internal (C₁ ++ C₂ †) eq ,
     ⟦⟧ᴿ-Ord≤2 (C₁ ++ C₂ †) eq (level-miter C₁ C₂ lv₁ lv₂))
