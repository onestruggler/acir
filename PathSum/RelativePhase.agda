------------------------------------------------------------------------
-- Presentations of groups
--
-- Path-sums that permute basis states up to a relative phase (Amy,
-- QPL 2018, section 5.2)
--
-- Section 5.2 verifies "the Maslov decomposition [23] using relative
-- phase Toffolis" of the n-bit Toffoli gate.  A relative-phase Toffoli
-- gate is not a Toffoli gate: it sends |x⟩ to e^{2πi φ(x)} |x[t ≔ x_t ⊕
-- x_c₁ x_c₂]⟩ for a phase φ that depends on x, so its matrix is the
-- Toffoli permutation times a diagonal matrix of phases.  It needs
-- fewer T gates than the Toffoli gate, and a decomposition may use it
-- wherever it is later undone by its inverse before the wires it reads
-- change: then the phases cancel.  This module is the general theory
-- of such operators; the plan of the work package is as follows.
--
-- * Here.  Phases are the integers of PathSum.Denotation, numerators
--   over N = 2^M, read modulo N since ζ^N = 1: a ≡ᴺ b, a congruence
--   (≡ᴺ-refl, -sym, -trans, -+, --) under which ζ^a and rotation by a
--   are invariant (zpow-≡ᴺ, rot-≡ᴺ).  A path-sum ξ computes F up to
--   the phase φ when its unnormalised amplitude from x to z is
--   √2^k ζ^φ(x) δ(F(x), z), k its normalisation: its operator is the
--   permutation matrix of F times the diagonal matrix of the phases
--   ζ^φ(x) (a record, _computes_up-to_, for the reason
--   PathSum.Classical's _computes_ is one; that notion is the case
--   φ = 0, computes⇒up-to and up-to⇒computes).  The notion only reads
--   F pointwise and φ modulo N (up-to-≗, up-to-phase), is invariant
--   under ≋ (≋-up-to), and determines ξ up to ≋ (up-to-≋).  The
--   specifications are the path-sums phased P f = ⟨ P , f ⟩, without
--   path variables: |x⟩ ↦ ζ^P(x) |f(x)⟩ (phased-up-to, up-to⇒≋phased).
--   By proposition 2.7 phases add along the permutation: ξ′ ∘ ξ
--   computes G ∘ F up to φ(x) + ψ(F x) (∘ᴾ-up-to), and so does a
--   circuit C ; D (⟦++⟧-up-to).  Hence the lemma a relative-phase
--   decomposition rests on (sandwich): in C ; D ; E, if the phase C
--   produces at x and the phase E produces at the state D leaves are
--   opposite modulo N, the composite computes the composite
--   permutation up to D's phase alone.  A path-sum that computes F
--   both exactly and up to φ has ζ^φ(x) = 1 at every x (up-to-exact),
--   which is how a gate is shown not to be the Toffoli gate.  And by
--   PathSum.CRK.Conjugate, if C computes a bijection F up to φ, its
--   inverse C† computes the inverse bijection G up to -φ(G x)
--   (†-up-to), for F, G and φ that read an assignment only through its
--   values (Respects-F, Respects-φ).
--
-- * PathSum.Maslov.Arith: the integer, Boolean and amplitude identities
--   of the proofs, apart from any circuit (phases modulo N; sums over
--   two path variables with a rotation).
--
-- * PathSum.Maslov.Gate: the relative-phase Toffoli gate rtof c₁ c₂ t
--   = H T CNOT(c₂,t) T† CNOT(c₁,t) T CNOT(c₂,t) T† H on the target t,
--   four T gates, two Hadamards and three CNOTs, on any wires with
--   c₁, c₂ ≠ t, for every n and M₀.  Read along each of its four paths
--   (PathSum.CRK.Path) and summed, it computes the Toffoli function up
--   to the phase ½ x_c₁ x_t + ¼ x_c₁ x_c₂, i.e.
--
--      |x⟩ ↦ i^(x_c₁ x_c₂) (-1)^(x_c₁ x_t) |x[t ≔ x_t ⊕ x_c₁ x_c₂]⟩,
--
--   so its path-sum is ≋ the explicit diagonal-times-permutation
--   path-sum with that phase polynomial (rtof-spec), and it is not
--   the Toffoli gate (rtof-not-toffoli).  The circuit is its own
--   mirror image, its inverse (PathSum.CRK.Adjoint's _†, rtof-†), and
--   the gate followed by its inverse computes the identity exactly
--   (rtof-rtof): the phase at x and the phase at the Toffoli image of
--   x cancel.  More generally the phases cancel around any circuit
--   that leaves the three wires' values alone (rtof-sandwich), which
--   is what a decomposition into relative-phase Toffoli gates needs.
--
-- * PathSum.Maslov.Eighths: sums of eighth roots of unity by
--   computation.  Such a sum is written as an integer combination of
--   ζ^0, ζ^⅛, ζ^¼ and ζ^⅜ (Lin: the other four eighth roots are their
--   negatives), so that Agda compares two such sums by refl (Σᴮ-ˡ).
--
-- * PathSum.Maslov.Gate4: the relative-phase Toffoli-4 gate
--   rc3x a b c d, with three controls a, b, c and target d -- eight T
--   gates, four Hadamards and six CNOTs -- on any wires with
--   a, b, c ≠ d, for every n and M₀.  It computes the three-control
--   Toffoli function up to the phase ¼ x_a x_b + ¼ x_a x_b x_c +
--   ½ x_a x_b x_d (rc3x-up-to, rc3x-spec), and does not compute it
--   exactly (rc3x-not-toffoli).  It is not its own inverse; its
--   inverse computes the same function up to minus the phase read
--   after the gate, so that the gate followed by its inverse computes
--   the identity exactly (rc3x-rc3x†) and around any circuit that
--   leaves the four wires alone the two cancel their phases
--   (rc3x-sandwich).
--
-- * PathSum.Maslov.Chain and PathSum.Maslov: the decomposition itself
--   (phase B).  Section 5.2 uses ⌈(n-3)/2⌉ ancillas, and table 2's
--   counts for Maslov50 and Maslov100 -- 74 and 149 qubits, 192 and
--   392 path variables, 481 and 981 Clifford gates, 384 and 784 T
--   gates -- are, at these two even n, those of n - 2 relative-phase
--   Toffoli-4 gates (each 8 T, 4 H and 6 CNOT) plus one CNOT, on
--   n + ⌈(n-3)/2⌉ = n + (n-2)/2 wires: a chain of (n-2)/2 such gates
--   computing the conjunction of the n - 1 controls into as many
--   ancillas, three controls for the first gate and two more for each
--   next one, a CNOT from the last ancilla onto the target, and the
--   chain undone by the gates' inverses.  (At odd n such a chain
--   covers one control fewer, and the middle gate is an exact Toffoli
--   gate on the last ancilla and that control.)  A Toffoli-4 gate has
--   the counts of two three-qubit gates (4 T, 2 H and 3 CNOT each), so
--   the same T, Clifford and path-variable counts are also those of
--   2n - 4 three-qubit gates plus one CNOT; but a chain of those adds
--   one control at a time and needs n - 2 ancillas, 2n - 2 qubits (98
--   and 198), not 74 and 149.  The sources confirm this reading: the
--   gates are [23]'s (Maslov, arXiv:1508.03273: rtof is its figure 3's
--   dashed box, rc3x its figure 4), and the chain is the one the
--   paper's tool generates (maslovToffoli in Feynman's
--   src/Feynman/Verification/SOP.hs, whose rToffoli4 is rc3x).
--   Maslov's own construction with ⌈(n − 3)/2⌉ clean ancillas ([23],
--   Proposition 4) has an exact Toffoli gate in the middle and
--   8n − 17 T gates, 383 at n = 50; table 2's 384 is this chain's,
--   8n − 16 at even n.  PathSum.Maslov
--   proves it for every n ≥ 3: by sandwich, level by level, the
--   circuit computes an exact permutation on every input, which on the
--   inputs whose ancillas are 0 is the n-bit Toffoli gate, leaving
--   them 0; and its counts are table 2's at n = 50 and n = 100.
--
-- Everything is stated through amplitudes, as for PathSum.Classical:
-- the output polynomials matter only through their values.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.RelativePhase (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; divides; ∣m∣n⇒∣m+n; ∣m⇒∣-m)
open import Data.Integer.Properties using (+-identityʳ; +-inverseʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (_++_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import PathSum.Adjoint.Gates M₀ using (conj-δ)
open import PathSum.AmpLinear M₀ using
  (rot-linear; scale-+; scale-exp; scale-comm)
open import PathSum.Assign using
  (same; same-≗; same-refl; same-true; same-intro)
open import PathSum.Base using (PathSum; ⟨_,_⟩)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Classical M₀ using
  (_computes_; computing; amp-computes; none; fun; outBit-none; δ-≗)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.CRK M₀ using (amp-⟦++⟧; norm-++)
open import PathSum.Compose.Properties M₀ using
  (hits-same; prop-2-7ᶜ; applyᴾ-cong; applyᴾ-scale; applyᴾ-linear;
   amp-applyᴾ)
open import PathSum.Compose.Sum M₀ using
  (if-cong; zpow-≡; rot-if; scale-rot)
open import PathSum.CRK.Adjoint (suc (suc (suc M₀))) using (_†; norm-†)
open import PathSum.CRK.Conjugate M₀ using (circuit-adjoint)
open import PathSum.CRK.Path M₀ using (Circuit; ⟦_⟧; norm)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; zpow; zpow-cong; rot; rot-map; rot-comp; rot-0;
   coeff-cong; scale; scale-map; scale-injective; N)
open import PathSum.Denotation M₀ using (Assign; amp; hits; _≋_)
open import PathSum.Polynomial using (Poly; eval)
open import PathSum.Polynomial.Properties using (eval-cong)
open import PathSum.Ring M₀ using (conj-cong; conj-rot)
open import PathSum.Ring.Laws M₀ using (conj-scale)

open +-*-Solver using (solve; _:+_; _:-_; :-_; _:=_)

private
  variable
    n k k′ m m′ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Phases modulo 1

-- A phase is a numerator over N = 2^M, and ζ^N = 1: two phases are the
-- same when they differ by a multiple of N.  A record, so that the two
-- phases can be read off its type.

infix 4 _≡ᴺ_

record _≡ᴺ_ (a b : ℤ) : Set where
  constructor mod-N
  field
    divides-N : (+ N) ∣ (a - b)

open _≡ᴺ_ public

private
  neg-diff : ∀ a b → - (a - b) ≡ b - a
  neg-diff = solve 2 (λ a b → :- (a :- b) := b :- a) refl

  chain : ∀ a b c → (a - b) + (b - c) ≡ a - c
  chain = solve 3 (λ a b c → (a :- b) :+ (b :- c) := a :- c) refl

  sums : ∀ a a′ b b′ → (a - a′) + (b - b′) ≡ (a + b) - (a′ + b′)
  sums = solve 4 (λ a a′ b b′ →
    (a :- a′) :+ (b :- b′) := (a :+ b) :- (a′ :+ b′)) refl

  negs : ∀ a b → - (a - b) ≡ (- a) - (- b)
  negs = solve 2 (λ a b → :- (a :- b) := (:- a) :- (:- b)) refl

  shift : ∀ u a b → b - a ≡ (u - a) - (u - b)
  shift = solve 3 (λ u a b → b :- a := (u :- a) :- (u :- b)) refl

-- It is a congruence for addition and subtraction.

≡ᴺ-refl : ∀ {a} → a ≡ᴺ a
≡ᴺ-refl {a} = mod-N (divides 0ℤ (+-inverseʳ a))

≡ᴺ-≡ : ∀ {a b} → a ≡ b → a ≡ᴺ b
≡ᴺ-≡ refl = ≡ᴺ-refl

≡ᴺ-sym : ∀ {a b} → a ≡ᴺ b → b ≡ᴺ a
≡ᴺ-sym {a} {b} (mod-N h) =
  mod-N (subst ((+ N) ∣_) (neg-diff a b) (∣m⇒∣-m h))

≡ᴺ-trans : ∀ {a b c} → a ≡ᴺ b → b ≡ᴺ c → a ≡ᴺ c
≡ᴺ-trans {a} {b} {c} (mod-N h) (mod-N g) =
  mod-N (subst ((+ N) ∣_) (chain a b c) (∣m∣n⇒∣m+n h g))

≡ᴺ-+ : ∀ {a a′ b b′} → a ≡ᴺ a′ → b ≡ᴺ b′ → a + b ≡ᴺ a′ + b′
≡ᴺ-+ {a} {a′} {b} {b′} (mod-N h) (mod-N g) =
  mod-N (subst ((+ N) ∣_) (sums a a′ b b′) (∣m∣n⇒∣m+n h g))

≡ᴺ-neg : ∀ {a b} → a ≡ᴺ b → - a ≡ᴺ - b
≡ᴺ-neg {a} {b} (mod-N h) = mod-N (subst ((+ N) ∣_) (negs a b) (∣m⇒∣-m h))

≡ᴺ-- : ∀ {a a′ b b′} → a ≡ᴺ a′ → b ≡ᴺ b′ → a - b ≡ᴺ a′ - b′
≡ᴺ-- h g = ≡ᴺ-+ h (≡ᴺ-neg g)

-- A multiple of N is 0.

≡ᴺ-N : ∀ z → z * (+ N) ≡ᴺ 0ℤ
≡ᴺ-N z = mod-N (divides z (+-identityʳ (z * (+ N))))

-- Powers of ζ and rotations only read a phase modulo N.

zpow-≡ᴺ : ∀ {a b} → a ≡ᴺ b → zpow a ≐ zpow b
zpow-≡ᴺ {a} {b} (mod-N h) = zpow-cong {a} {b} h

rot-≡ᴺ : ∀ {a b} → a ≡ᴺ b → ∀ v → rot a v ≐ rot b v
rot-≡ᴺ {a} {b} h v i =
  coeff-cong v ((+ toℕ i) - a) ((+ toℕ i) - b)
    (subst ((+ N) ∣_) (shift (+ toℕ i) a b) (divides-N (≡ᴺ-sym h)))

-- Chains of congruences, each phase written out (which also spares
-- Agda solving for phases hidden under _-_).

module ≡ᴺ-Reasoning where

  infix  1 begin_
  infixr 2 _≡ᴺ⟨_⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {a b} → a ≡ᴺ b → a ≡ᴺ b
  begin p = p

  _≡ᴺ⟨_⟩_ : ∀ a {b c} → a ≡ᴺ b → b ≡ᴺ c → a ≡ᴺ c
  a ≡ᴺ⟨ p ⟩ q = ≡ᴺ-trans p q

  _≡⟨_⟩_ : ∀ a {b c} → a ≡ b → b ≡ᴺ c → a ≡ᴺ c
  a ≡⟨ p ⟩ q = ≡ᴺ-trans (≡ᴺ-≡ p) q

  _∎ : ∀ a → a ≡ᴺ a
  a ∎ = ≡ᴺ-refl


------------------------------------------------------------------------
-- Computing a permutation up to a phase

-- ξ computes F up to the phase φ when its operator is the permutation
-- matrix of F times the diagonal matrix of the phases ζ^φ(x), up to
-- its normalisation: the unnormalised amplitude from x to z is
-- √2^k ζ^φ(x) δ(F(x), z).  A record, like PathSum.Classical's
-- _computes_, so that Agda compares two such statements by their
-- arguments instead of unfolding them into amplitudes.

infix 4 _computes_up-to_

record _computes_up-to_ {n k m : ℕ} (ξ : PathSum n k m)
                        (F : Assign n → Assign n)
                        (φ : Assign n → ℤ) : Set where
  constructor computing-up-to
  field
    amp-up-to : ∀ x z → amp ξ x z ≐ scale k (rot (φ x) (δ (F x) z))

open _computes_up-to_ public

-- Computing F exactly is computing it up to the phase 0.

computes⇒up-to : (ξ : PathSum n k m) {F : Assign n → Assign n} →
                 ξ computes F → ξ computes F up-to (λ _ → 0ℤ)
computes⇒up-to {k = k} ξ {F} c = computing-up-to λ x z →
  amp-computes c x z ∙ scale-map k (≐-sym (rot-0 (δ (F x) z)))

up-to⇒computes : (ξ : PathSum n k m) {F : Assign n → Assign n}
                 {φ : Assign n → ℤ} → ξ computes F up-to φ →
                 (∀ x → φ x ≡ᴺ 0ℤ) → ξ computes F
up-to⇒computes {k = k} ξ {F} c h = computing λ x z →
  amp-up-to c x z
  ∙ scale-map k (rot-≡ᴺ (h x) (δ (F x) z) ∙ rot-0 (δ (F x) z))

-- Only the values of F, and φ modulo N, matter.

up-to-≗ : (ξ : PathSum n k m) {F G : Assign n → Assign n}
          {φ : Assign n → ℤ} → (∀ x w → F x w ≡ G x w) →
          ξ computes F up-to φ → ξ computes G up-to φ
up-to-≗ {k = k} ξ {φ = φ} h c = computing-up-to λ x z →
  amp-up-to c x z ∙ scale-map k (rot-map (φ x) (δ-≗ (h x) z))

up-to-phase : (ξ : PathSum n k m) {F : Assign n → Assign n}
              {φ ψ : Assign n → ℤ} → (∀ x → φ x ≡ᴺ ψ x) →
              ξ computes F up-to φ → ξ computes F up-to ψ
up-to-phase {k = k} ξ {F} h c = computing-up-to λ x z →
  amp-up-to c x z ∙ scale-map k (rot-≡ᴺ (h x) (δ (F x) z))

-- Equivalent path-sums compute the same permutations up to the same
-- phases, and two path-sums that do are equivalent.

≋-up-to : (ξ : PathSum n k m) (ζ : PathSum n k′ m′)
          {F : Assign n → Assign n} {φ : Assign n → ℤ} → ξ ≋ ζ →
          ζ computes F up-to φ → ξ computes F up-to φ
≋-up-to {k = k} {k′ = k′} ξ ζ {F} {φ} eq c = computing-up-to λ x z →
  scale-injective k′ (amp ξ x z) (scale k (rot (φ x) (δ (F x) z)))
    (eq x z ∙ scale-map k (amp-up-to c x z)
            ∙ scale-comm k k′ (rot (φ x) (δ (F x) z)))

up-to-≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′)
          {F : Assign n → Assign n} {φ : Assign n → ℤ} →
          ξ computes F up-to φ → ζ computes F up-to φ → ξ ≋ ζ
up-to-≋ {k = k} {k′ = k′} ξ ζ {F} {φ} cξ cζ x z =
  scale-map k′ (amp-up-to cξ x z)
  ∙ scale-comm k′ k (rot (φ x) (δ (F x) z))
  ∙ scale-map k (≐-sym (amp-up-to cζ x z))

-- A path-sum that computes F both exactly and up to φ has ζ^φ(x) = 1
-- at every x: read the amplitude from x to F(x) both ways.  (Stated
-- for any path-sum, so that a client never compares the two readings
-- of a concrete amplitude itself.)

private
  unguard : {s : Bool} {a b : Amp} → s ≡ true →
            (if s then a else 0ᴬ) ≐ (if s then b else 0ᴬ) → a ≐ b
  unguard refl h = h

up-to-exact : (ξ : PathSum n k m) {F : Assign n → Assign n}
              {φ : Assign n → ℤ} → ξ computes F → ξ computes F up-to φ →
              ∀ x → zpow 0ℤ ≐ zpow (φ x + 0ℤ)
up-to-exact {k = k} ξ {F} {φ} c u x =
  unguard (same-refl (F x)) (both ∙ rot-if (same (F x) (F x)) (φ x) 0ℤ)
  where
  both : δ (F x) (F x) ≐ rot (φ x) (δ (F x) (F x))
  both = scale-injective k (δ (F x) (F x)) (rot (φ x) (δ (F x) (F x)))
    (≐-sym (amp-computes c x (F x)) ∙ amp-up-to u x (F x))


------------------------------------------------------------------------
-- The specifications: a phase polynomial and a permutation

-- |x⟩ ↦ ζ^P(x) |f(x)⟩: no path variables, no normalisation, the phase
-- polynomial P and the output polynomials f, read modulo 2.  With
-- P = 0 this is PathSum.Classical's classical f.

phased : Poly n 0 → (Fin n → Poly n 0) → PathSum n 0 0
phased P f = ⟨ P , f ⟩

-- Its single path hits z exactly when z is f(x), with the phase P(x).

amp-phased : (P : Poly n 0) (f : Fin n → Poly n 0) (x z : Assign n) →
             amp (phased P f) x z ≐ rot (eval P x none) (δ (fun f x) z)
amp-phased P f x z = at (λ ())
  where
  at : (y : Assign 0) →
       (if hits (phased P f) x y z then zpow (eval P x y) else 0ᴬ) ≐
       rot (eval P x none) (δ (fun f x) z)
  at y =
    if-cong (trans (hits-same (phased P f) x y z)
                   (same-≗ (outBit-none (phased P f) x y) (λ _ → refl)))
            (zpow-≡ (trans (eval-cong P {x} {x} {y} {none}
                                      (λ _ → refl) (λ ()))
                           (sym (+-identityʳ (eval P x none)))))
    ∙ ≐-sym (rot-if (same (fun f x) z) (eval P x none) 0ℤ)

phased-up-to : (P : Poly n 0) (f : Fin n → Poly n 0) →
               phased P f computes fun f up-to (λ x → eval P x none)
phased-up-to P f = computing-up-to (amp-phased P f)

-- So a path-sum is equivalent to phased P f exactly when it computes
-- fun f up to the values of P (one direction; the other is ≋-up-to).

up-to⇒≋phased : (ξ : PathSum n k m) (P : Poly n 0) (f : Fin n → Poly n 0) →
                ξ computes fun f up-to (λ x → eval P x none) →
                ξ ≋ phased P f
up-to⇒≋phased ξ P f c = up-to-≋ ξ (phased P f) c (phased-up-to P f)


------------------------------------------------------------------------
-- Composition

-- By proposition 2.7 the column of ξ′ ∘ ξ at x is U_ξ′ applied to the
-- column of ξ at x, which is √2^k ζ^φ(x) times the basis column at
-- F(x); U_ξ′ commutes with both factors (PathSum.AmpLinear), and maps
-- that basis column to √2^k′ ζ^ψ(F x) times the one at G(F x).  The
-- phases add along the permutation.

∘ᴾ-up-to : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m)
           {F G : Assign n → Assign n} {φ ψ : Assign n → ℤ} →
           ξ computes F up-to φ → ξ′ computes G up-to ψ →
           (ξ′ ∘ᴾ ξ) computes (λ x → G (F x)) up-to (λ x → φ x + ψ (F x))
∘ᴾ-up-to {k′ = k′} {k = k} ξ′ ξ {F} {G} {φ} {ψ} cF cG =
  computing-up-to λ x z →
  prop-2-7ᶜ ξ′ ξ x z
  ∙ applyᴾ-cong ξ′ {amp ξ x} {λ w → scale k (rot (φ x) (δ (F x) w))}
                (amp-up-to cF x) z
  ∙ ≐-sym (applyᴾ-scale ξ′ k (λ w → rot (φ x) (δ (F x) w)) z)
  ∙ scale-map k (applyᴾ-linear (rot-linear (φ x)) ξ′ (δ (F x)) z)
  ∙ scale-map k (rot-map (φ x) (≐-sym (amp-applyᴾ ξ′ (F x) z)))
  ∙ scale-map k (rot-map (φ x) (amp-up-to cG (F x) z))
  ∙ scale-map k (≐-sym (scale-rot k′ (φ x)
                          (rot (ψ (F x)) (δ (G (F x)) z))))
  ∙ scale-map k (scale-map k′ (rot-comp (φ x) (ψ (F x)) (δ (G (F x)) z)))
  ∙ scale-+ k k′ (rot (φ x + ψ (F x)) (δ (G (F x)) z))

-- For circuits over {H, CNOT, R_k, R_k†}: ⟦C;D⟧ = ⟦D⟧ ∘ ⟦C⟧
-- (PathSum.Compose.CRK).

⟦++⟧-up-to : (C D : Circuit n) {F G : Assign n → Assign n}
             {φ ψ : Assign n → ℤ} →
             ⟦ C ⟧ computes F up-to φ → ⟦ D ⟧ computes G up-to ψ →
             ⟦ C ++ D ⟧ computes (λ x → G (F x))
               up-to (λ x → φ x + ψ (F x))
⟦++⟧-up-to C D {F} {G} {φ} {ψ} cC cD = computing-up-to λ x z →
  amp-⟦++⟧ C D x z
  ∙ amp-up-to (∘ᴾ-up-to ⟦ D ⟧ ⟦ C ⟧ cC cD) x z
  ∙ scale-exp (rot (φ x + ψ (F x)) (δ (G (F x)) z)) (sym (norm-++ C D))


------------------------------------------------------------------------
-- Phases that cancel

-- C ; D ; E computes the composite permutation up to the phase φ(x) +
-- ψ(F x) + χ(G(F x)).  When C's phase at x and E's phase at the state
-- D leaves cancel modulo N, only D's phase remains.  This is how a gate
-- that is correct only up to a relative phase can still be used: undo
-- it (E) after a circuit (D) that leaves alone whatever the phases
-- read.

sandwich : (C D E : Circuit n) {F G K : Assign n → Assign n}
           {φ ψ χ : Assign n → ℤ} →
           ⟦ C ⟧ computes F up-to φ → ⟦ D ⟧ computes G up-to ψ →
           ⟦ E ⟧ computes K up-to χ →
           (∀ x → φ x + χ (G (F x)) ≡ᴺ 0ℤ) →
           ⟦ C ++ D ++ E ⟧ computes (λ x → K (G (F x)))
             up-to (λ x → ψ (F x))
sandwich C D E {F} {G} {K} {φ} {ψ} {χ} cC cD cE h =
  up-to-phase ⟦ C ++ D ++ E ⟧ remaining
    (⟦++⟧-up-to C (D ++ E) cC (⟦++⟧-up-to D E cD cE))
  where
  regroup : ∀ a b c → a + (b + c) ≡ b + (a + c)
  regroup = solve 3 (λ a b c → a :+ (b :+ c) := b :+ (a :+ c)) refl

  remaining : ∀ x → φ x + (ψ (F x) + χ (G (F x))) ≡ᴺ ψ (F x)
  remaining x = ≡ᴺ-trans
    (≡ᴺ-≡ (regroup (φ x) (ψ (F x)) (χ (G (F x)))))
    (≡ᴺ-trans (≡ᴺ-+ (≡ᴺ-refl {ψ (F x)}) (h x))
              (≡ᴺ-≡ (+-identityʳ (ψ (F x)))))


------------------------------------------------------------------------
-- The inverse

-- A phase, or a function on assignments, that reads an assignment only
-- through its values.

Respects-φ : (Assign n → ℤ) → Set
Respects-φ {n} φ = ∀ {x y : Assign n} → (∀ w → x w ≡ y w) → φ x ≡ φ y

Respects-F : (Assign n → Assign n) → Set
Respects-F {n} F =
  ∀ {x y : Assign n} → (∀ w → x w ≡ y w) → ∀ w → F x w ≡ F y w

private
  guard-false : {q : Bool} {a b : Amp} → q ≡ false →
                (if false then a else 0ᴬ) ≐ (if q then b else 0ᴬ)
  guard-false refl _ = refl

  false-back : {p q : Bool} → p ≡ false → (q ≡ true → p ≡ true) →
               q ≡ false
  false-back {q = true}  p≡f back = trans (sym (back refl)) p≡f
  false-back {q = false} p≡f back = refl

-- By PathSum.CRK.Conjugate the operator of C† is the conjugate
-- transpose of that of C.  If C computes the bijection F up to φ, its
-- row at x is nonzero only at the z with F(z) = x, that is z = G(x),
-- G the inverse of F, where it is √2^k ζ^φ(z); conjugated, that is the
-- column of C† at x: C† computes G up to -φ(G x).  (So if C's phases
-- are undone by C†'s, it is along the permutation: C ; C† computes
-- x ↦ G(F x) = x up to φ(x) - φ(G(F x)), which is 0 when φ respects
-- the values of assignments.)

†-up-to : (C : Circuit n) {F G : Assign n → Assign n}
          {φ : Assign n → ℤ} → ⟦ C ⟧ computes F up-to φ →
          Respects-F F → Respects-F G → Respects-φ φ →
          (∀ x w → F (G x) w ≡ x w) → (∀ z w → G (F z) w ≡ z w) →
          ⟦ C † ⟧ computes G up-to (λ x → - φ (G x))
†-up-to {n} C {F} {G} {φ} c rF rG rφ FG GF = computing-up-to λ x z →
  circuit-adjoint C x z
  ∙ conj-cong (amp-up-to c z x)
  ∙ conj-scale (norm C) (rot (φ z) (δ (F z) x))
  ∙ scale-map (norm C) (conj-rot (φ z) (δ (F z) x)
                        ∙ rot-map (- φ z) (conj-δ (F z) x)
                        ∙ column x z)
  ∙ scale-exp (rot (- φ (G x)) (δ (G x) z)) (sym (norm-† C))
  where
  column : ∀ x z → rot (- φ z) (δ (F z) x) ≐ rot (- φ (G x)) (δ (G x) z)
  column x z =
    rot-if (same (F z) x) (- φ z) 0ℤ
    ∙ go (same (F z) x) refl
    ∙ ≐-sym (rot-if (same (G x) z) (- φ (G x)) 0ℤ)
    where
    back : same (G x) z ≡ true → same (F z) x ≡ true
    back h = same-intro (F z) x (λ w →
      trans (rF (λ j → sym (same-true (G x) z h j)) w) (FG x w))

    go : ∀ b → same (F z) x ≡ b →
         (if b then zpow (- φ z + 0ℤ) else 0ᴬ) ≐
         (if same (G x) z then zpow (- φ (G x) + 0ℤ) else 0ᴬ)
    go true  e = if-cong (sym (same-intro (G x) z Gx≗z))
      (zpow-≡ (cong (λ u → - u + 0ℤ) (rφ (λ w → sym (Gx≗z w)))))
      where
      Gx≗z : ∀ w → G x w ≡ z w
      Gx≗z w = trans (rG (λ j → sym (same-true (F z) x e j)) w) (GF z w)
    go false e = guard-false {a = zpow (- φ z + 0ℤ)} (false-back e back)
