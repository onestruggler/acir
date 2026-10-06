------------------------------------------------------------------------
-- Presentations of groups
--
-- Long-distance cancellation of phase gates (Amy, QPL 2018, section
-- 2.1)
--
-- Section 2.1 of the paper says that path-sums "unify many semantic
-- equivalences of quantum circuits -- particularly allowing the
-- long-distance cancellation of phase gates applied to the same
-- logical state [2]", in contrast with matrices, which unify every
-- equivalence at exponential cost.  This module proves the claim for
-- the paper's gate set {H, CNOT, R_k, R_k†} (PathSum.CRK.Circuit).
--
-- The logical state a gate acts on is the Z₂-linear form its wire
-- holds in the interpretation state of definition 2.9 (a parity of
-- input and path variables), and R_k adds 2^(M-k) times the lifting of
-- that form to the phase.  So if R_k acts on wire w, then a circuit D
-- of CNOT and phase gates (no Hadamard: PGate, circ) carries that
-- parity to wire w′, and R_k† acts on w′, the two terms are the same
-- polynomial with opposite signs, and they cancel -- coefficient by
-- coefficient, as integers, before any rule of figure 2 is applied and
-- whatever D does in between (cancel-sig, cancel-poly; the gates in
-- between only add their own terms, an offset that D carries through,
-- poly-runᵖ).  The cancellation survives any circuit before (C₁, with
-- Hadamards and all) and after (C₃): the interpretation states of
--
--    C₁ ; R_k w ; D ; R_k† w′ ; C₃     and     C₁ ; D ; C₃
--
-- agree (long-distance): the same number of path variables, the same
-- form on every wire, and phases equal coefficient by coefficient.
-- Agree is that relation on states, and run-cong says that running any
-- circuit preserves it.  So the two path-sums are the same path-sum up
-- to equality of coefficients, and hence equivalent
-- (long-distance-≋).  The order of the two gates does not matter
-- (long-distance†: R_k† first, then R_k).
--
-- The condition is on the forms alone -- the form D leaves on w′ is
-- the form on w before it -- so at a closed circuit it is a
-- computation on forms, never on phases.  PathSum.Examples.LongDistance
-- runs a two-qubit instance, whose path-sum is then literally the
-- identity's, and checks it against the matrix route as well.
--
-- Only this kind of cancellation is claimed: the parity must reach w′
-- through gates that keep the path variables (no Hadamard between the
-- two phase gates), which is the setting of [2].
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.CRK.Cancellation (M₀ : ℕ) where

open import Data.Fin.Base using (Fin; zero)
open import Data.Fin.Subset using (inside; outside)
open import Data.Integer.Base using (ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (+-inverseʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Nat.Base using (_∸_)
open import Data.Product.Base using (∃; _,_; proj₁; proj₂)
open import Data.Vec.Base using (_∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum)
open import PathSum.Circuit M using (wkPoly)
open import PathSum.Compose.Gates M₀ using (≋-amp)
open import PathSum.Congruence M₀ using (amp-≈)
open import PathSum.CRK.Amp M₀ using (toPS)
open import PathSum.CRK.Circuit M using
  (Gate; H; CNOT; R; R†; Circuit; State; state; poly; sig; init; stepH;
   stepCNOT; stepR; stepR†; run; run-++; ⟦_⟧; norm; paths; paths≡norm;
   _[_↦_])
open import PathSum.Cyclotomic M₀ using (_≐_)
open import PathSum.Denotation M₀ using (amp; _≋_)
open import PathSum.Linear using (Lin; liftᴸ; varᴸ; wkLin; mul-y₀; _⊕ᴸ_)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (Poly; Mon; y[_]; _≈[_]_; _·ᴾ_)
open import PathSum.Polynomial.Properties using (i∣0)
open import PathSum.Reduction M using (½)

open +-*-Solver using (solve; _:+_; _:-_; :-_; _:=_)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- Gates that move parities and add phases

-- CNOT, R_k and R_k†: everything but the Hadamard.

data PGate (n : ℕ) : Set where
  cnot : (c t : Fin n) → c ≢ t → PGate n
  rz   : ℕ → Fin n → PGate n
  rz†  : ℕ → Fin n → PGate n

gate : PGate n → Gate n
gate (cnot c t p) = CNOT c t p
gate (rz k w)     = R k w
gate (rz† k w)    = R† k w

circ : List (PGate n) → Circuit n
circ = map gate

-- They keep the number of path variables, so a run of them is a map on
-- states of one type.

stepᵖ : PGate n → State n m → State n m
stepᵖ (cnot c t _) = stepCNOT c t
stepᵖ (rz k w)     = stepR k w
stepᵖ (rz† k w)    = stepR† k w

runᵖ : List (PGate n) → State n m → State n m
runᵖ []      st = st
runᵖ (g ∷ D) st = runᵖ D (stepᵖ g st)

run-circ : (D : List (PGate n)) (st : State n m) →
           run (circ D) st ≡ (m , runᵖ D st)
run-circ []               st = refl
run-circ (cnot c t p ∷ D) st = run-circ D (stepCNOT c t st)
run-circ (rz k w ∷ D)     st = run-circ D (stepR k w st)
run-circ (rz† k w ∷ D)    st = run-circ D (stepR† k w st)

-- Their forms do not read the phase.

sig-runᵖ : (D : List (PGate n)) (st st′ : State n m) → sig st ≡ sig st′ →
           sig (runᵖ D st) ≡ sig (runᵖ D st′)
sig-runᵖ []               st st′ e = e
sig-runᵖ (cnot c t p ∷ D) st st′ e = sig-runᵖ D _ _
  (cong (λ σ → σ [ t ↦ σ t ⊕ᴸ σ c ]) e)
sig-runᵖ (rz k w ∷ D)     st st′ e = sig-runᵖ D _ _ e
sig-runᵖ (rz† k w ∷ D)    st st′ e = sig-runᵖ D _ _ e

-- An offset Q of the phase is carried through: each gate adds the same
-- term on both sides.

private
  shift-+ : ∀ p p′ q a → p ≡ p′ + q → p + a ≡ (p′ + a) + q
  shift-+ p p′ q a refl = solve 3 (λ p′ q a → (p′ :+ q) :+ a := (p′ :+ a) :+ q)
                                refl p′ q a

  shift-- : ∀ p p′ q a → p ≡ p′ + q → p - a ≡ (p′ - a) + q
  shift-- p p′ q a refl =
    solve 3 (λ p′ q a → (p′ :+ q) :+ (:- a) := (p′ :+ (:- a)) :+ q)
          refl p′ q a

poly-runᵖ : (D : List (PGate n)) (st st′ : State n m) (Q : Poly n m) →
            sig st ≡ sig st′ → (∀ γ → poly st γ ≡ poly st′ γ + Q γ) →
            ∀ γ → poly (runᵖ D st) γ ≡ poly (runᵖ D st′) γ + Q γ
poly-runᵖ []               st st′ Q e h = h
poly-runᵖ (cnot c t p ∷ D) st st′ Q e h = poly-runᵖ D _ _ Q
  (cong (λ σ → σ [ t ↦ σ t ⊕ᴸ σ c ]) e) h
poly-runᵖ (rz k w ∷ D)     st st′ Q e h = poly-runᵖ D _ _ Q e (λ γ →
  trans (cong (λ σ → poly st γ + (pow (M ∸ k) ·ᴾ liftᴸ (σ w)) γ) e)
        (shift-+ (poly st γ) (poly st′ γ) (Q γ)
                 ((pow (M ∸ k) ·ᴾ liftᴸ (sig st′ w)) γ) (h γ)))
poly-runᵖ (rz† k w ∷ D)    st st′ Q e h = poly-runᵖ D _ _ Q e (λ γ →
  trans (cong (λ σ → poly st γ - (pow (M ∸ k) ·ᴾ liftᴸ (σ w)) γ) e)
        (shift-- (poly st γ) (poly st′ γ) (Q γ)
                 ((pow (M ∸ k) ·ᴾ liftᴸ (sig st′ w)) γ) (h γ)))


------------------------------------------------------------------------
-- The cancellation, on interpretation states

-- R_k on w, then D, then R_k† on w′, against D alone: the same forms,
-- and, when D carries the form on w to w′, the same phase.

module _ {n m : ℕ} (st : State n m) (D : List (PGate n)) (k : ℕ)
         (w w′ : Fin n) where

  private
    -- The term R_k adds.

    T : Poly n m
    T = pow (M ∸ k) ·ᴾ liftᴸ (sig st w)

  cancel-sig : sig (stepR† k w′ (runᵖ D (stepR k w st))) ≡ sig (runᵖ D st)
  cancel-sig = sig-runᵖ D (stepR k w st) st refl

  cancel-poly : sig (runᵖ D st) w′ ≡ sig st w →
                ∀ γ → poly (stepR† k w′ (runᵖ D (stepR k w st))) γ ≡
                      poly (runᵖ D st) γ
  cancel-poly carried γ = trans
    (cong₂ _-_ (poly-runᵖ D (stepR k w st) st T refl (λ _ → refl) γ)
               (cong (λ l → (pow (M ∸ k) ·ᴾ liftᴸ l) γ)
                     (trans (cong (λ σ → σ w′) cancel-sig) carried)))
    (back (poly (runᵖ D st) γ) (T γ))
    where
    back : ∀ p t → (p + t) - t ≡ p
    back = solve 2 (λ p t → (p :+ t) :+ (:- t) := p) refl

  -- The other order: R_k† on w first, R_k on w′ last.

  cancel-sig† : sig (stepR k w′ (runᵖ D (stepR† k w st))) ≡ sig (runᵖ D st)
  cancel-sig† = sig-runᵖ D (stepR† k w st) st refl

  cancel-poly† : sig (runᵖ D st) w′ ≡ sig st w →
                 ∀ γ → poly (stepR k w′ (runᵖ D (stepR† k w st))) γ ≡
                       poly (runᵖ D st) γ
  cancel-poly† carried γ = trans
    (cong₂ _+_ (poly-runᵖ D (stepR† k w st) st (λ δ → - T δ) refl
                          (λ _ → refl) γ)
               (cong (λ l → (pow (M ∸ k) ·ᴾ liftᴸ l) γ)
                     (trans (cong (λ σ → σ w′) cancel-sig†) carried)))
    (back (poly (runᵖ D st) γ) (T γ))
    where
    back : ∀ p t → (p + (- t)) + t ≡ p
    back = solve 2 (λ p t → (p :+ (:- t)) :+ t := p) refl


------------------------------------------------------------------------
-- States that agree

-- The same number of path variables, the same forms, and phases equal
-- coefficient by coefficient.

data Agree {n : ℕ} : ∃ (State n) → ∃ (State n) → Set where
  agree : ∀ {m} {st st′ : State n m} → sig st ≡ sig st′ →
          (∀ γ → poly st γ ≡ poly st′ γ) → Agree (m , st) (m , st′)

-- Running a circuit keeps states agreeing: every gate reads only the
-- forms and adds the same term to both phases.

private
  wkPoly-≗ : {P P′ : Poly n m} → (∀ γ → P γ ≡ P′ γ) →
             ∀ γ → wkPoly P γ ≡ wkPoly P′ γ
  wkPoly-≗ h (α , inside  ∷ β) = refl
  wkPoly-≗ h (α , outside ∷ β) = h (α , β)

run-cong : (C : Circuit n) {st st′ : State n m} → sig st ≡ sig st′ →
           (∀ γ → poly st γ ≡ poly st′ γ) → Agree (run C st) (run C st′)
run-cong []                {st} {st′} e h = agree e h
run-cong (H w ∷ C)         {st} {st′} e h = run-cong C
  (cong (λ σ → (λ v → wkLin (σ v)) [ w ↦ varᴸ y[ zero ] ]) e)
  (λ γ → cong₂ _+_ (wkPoly-≗ h γ)
                   (cong (λ σ → mul-y₀ (½ ·ᴾ liftᴸ (σ w)) γ) e))
run-cong (CNOT c t p ∷ C)  {st} {st′} e h = run-cong C
  (cong (λ σ → σ [ t ↦ σ t ⊕ᴸ σ c ]) e) h
run-cong (R k w ∷ C)       {st} {st′} e h = run-cong C e (λ γ →
  cong₂ _+_ (h γ) (cong (λ σ → (pow (M ∸ k) ·ᴾ liftᴸ (σ w)) γ) e))
run-cong (R† k w ∷ C)      {st} {st′} e h = run-cong C e (λ γ →
  cong₂ _-_ (h γ) (cong (λ σ → (pow (M ∸ k) ·ᴾ liftᴸ (σ w)) γ) e))

-- Agreeing states have as many path variables, and their path-sums the
-- same amplitudes (PathSum.Congruence.amp-≈).

agree-paths : {p q : ∃ (State n)} → Agree p q → proj₁ p ≡ proj₁ q
agree-paths (agree _ _) = refl

private
  ≡⇒≈ : ∀ {c} {P Q : Poly n m} → (∀ γ → P γ ≡ Q γ) → P ≈[ c ] Q
  ≡⇒≈ {c = c} {P} {Q} h γ = subst (λ q → c ∣ (P γ - q)) (h γ)
    (subst (c ∣_) (sym (+-inverseʳ (P γ))) i∣0)

agree-amp : ∀ {k k′} {p q : ∃ (State n)} → Agree p q →
            ∀ x z → amp (toPS {k = k} (proj₂ p)) x z ≐
                    amp (toPS {k = k′} (proj₂ q)) x z
agree-amp {k = k} {k′} (agree {st = st} {st′} e h) x z =
  amp-≈ (toPS {k = k} st) (toPS {k = k′} st′)
    (λ w → ≡⇒≈ (λ γ → cong (λ σ → liftᴸ (σ w) γ) e)) (≡⇒≈ h) x z

-- Circuits whose runs agree are equivalent.

agree-≋ : (X Y : Circuit n) → Agree (run X (init {n})) (run Y (init {n})) →
          ⟦ X ⟧ ≋ ⟦ Y ⟧
agree-≋ X Y a = ≋-amp ⟦ X ⟧ ⟦ Y ⟧
  (trans (sym (paths≡norm X)) (trans (agree-paths a) (paths≡norm Y)))
  (agree-amp {k = norm X} {k′ = norm Y} a)


------------------------------------------------------------------------
-- Long-distance cancellation

-- In any circuit: R_k on w, then any CNOT and phase gates D that carry
-- the form on w to w′, then R_k† on w′, is D alone -- before any rule
-- is applied, the two circuits have agreeing interpretation states.

module _ {n : ℕ} (C₁ C₃ : Circuit n) (D : List (PGate n)) (k : ℕ)
         (w w′ : Fin n) where

  private
    st : State n (proj₁ (run C₁ (init {n})))
    st = proj₂ (run C₁ (init {n}))

    -- Running the pieces in turn (run-++), D as a map on states.

    split : (G : Gate n) (T : Circuit n) →
            run (C₁ ++ G ∷ circ D ++ T) (init {n}) ≡
            run (G ∷ circ D ++ T) st
    split G T = run-++ C₁ (G ∷ circ D ++ T) init

    through : (C : Circuit n) (s : State n (proj₁ (run C₁ (init {n})))) →
              run (circ D ++ C) s ≡ run C (runᵖ D s)
    through C s = trans (run-++ (circ D) C s)
                        (cong (λ p → run C (proj₂ p)) (run-circ D s))

    eqX : run (C₁ ++ R k w ∷ circ D ++ R† k w′ ∷ C₃) (init {n}) ≡
          run C₃ (stepR† k w′ (runᵖ D (stepR k w st)))
    eqX = trans (split (R k w) (R† k w′ ∷ C₃)) (through (R† k w′ ∷ C₃) (stepR k w st))

    eqX† : run (C₁ ++ R† k w ∷ circ D ++ R k w′ ∷ C₃) (init {n}) ≡
           run C₃ (stepR k w′ (runᵖ D (stepR† k w st)))
    eqX† = trans (split (R† k w) (R k w′ ∷ C₃)) (through (R k w′ ∷ C₃) (stepR† k w st))

    eqY : run (C₁ ++ circ D ++ C₃) (init {n}) ≡ run C₃ (runᵖ D st)
    eqY = trans (run-++ C₁ (circ D ++ C₃) init) (through C₃ st)

  -- The condition: D leaves on w′ the form that was on w.

  Carries : Set
  Carries = sig (runᵖ D st) w′ ≡ sig st w

  long-distance : Carries →
                  Agree (run (C₁ ++ R k w ∷ circ D ++ R† k w′ ∷ C₃) (init {n}))
                        (run (C₁ ++ circ D ++ C₃) (init {n}))
  long-distance carried = subst₂ Agree (sym eqX) (sym eqY)
    (run-cong C₃ (cancel-sig st D k w w′) (cancel-poly st D k w w′ carried))

  long-distance† : Carries →
                   Agree (run (C₁ ++ R† k w ∷ circ D ++ R k w′ ∷ C₃) (init {n}))
                         (run (C₁ ++ circ D ++ C₃) (init {n}))
  long-distance† carried = subst₂ Agree (sym eqX†) (sym eqY)
    (run-cong C₃ (cancel-sig† st D k w w′)
                 (cancel-poly† st D k w w′ carried))

  -- Hence the two circuits are equivalent.

  long-distance-≋ : Carries →
                    ⟦ C₁ ++ R k w ∷ circ D ++ R† k w′ ∷ C₃ ⟧ ≋
                    ⟦ C₁ ++ circ D ++ C₃ ⟧
  long-distance-≋ carried =
    agree-≋ (C₁ ++ R k w ∷ circ D ++ R† k w′ ∷ C₃) (C₁ ++ circ D ++ C₃)
            (long-distance carried)

  long-distance†-≋ : Carries →
                     ⟦ C₁ ++ R† k w ∷ circ D ++ R k w′ ∷ C₃ ⟧ ≋
                     ⟦ C₁ ++ circ D ++ C₃ ⟧
  long-distance†-≋ carried =
    agree-≋ (C₁ ++ R† k w ∷ circ D ++ R k w′ ∷ C₃) (C₁ ++ circ D ++ C₃)
            (long-distance† carried)
