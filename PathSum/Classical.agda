------------------------------------------------------------------------
-- Presentations of groups
--
-- Classical path-sums: permutations of basis states (Amy, QPL 2018,
-- section 5.2)
--
-- Section 5.2 verifies reversible circuits -- n-bit Toffoli gates,
-- adders -- against specifications that are path-sums without path
-- variables, |x⟩ ↦ |f(x)⟩.  This module is the library of such
-- path-sums, and the first of the Toffoli development; the plan of
-- the whole is as follows.
--
-- * Here: classical f = ⟨ 0 , f ⟩, with no path variables, no
--   normalisation, phase 0 and output polynomials f read modulo 2.
--   It computes the Boolean function fun f, the output bits at each
--   input -- the values of the expressions, when f are lifts of
--   Boolean expressions (fun-liftᵉ, by lemma 2.5) -- and its
--   amplitudes are the 0/1 indicator δ (fun f x) z (amp-classical).
--   More generally ξ computes F when its unnormalised amplitude from x
--   to z is √2^k δ (F x) z, k its normalisation: the operator of ξ is
--   the permutation matrix of F.  (A record, _computes_, so that Agda
--   compares such statements without unfolding them into amplitudes;
--   two path-sums computing one function are equivalent, computes-≋,
--   so nothing is lost.)  That notion is closed under ≋ (≋-computes)
--   and under composition, since by proposition 2.7 the column of
--   ξ′ ∘ ξ at x is U_ξ′ applied to √2^k times the basis column at F x
--   (∘ᴾ-computes); so two classical path-sums compose to a classical
--   one, whose outputs are the composite's own, f′ substituted into by
--   the lift of f (definition 2.6), and whose function is the
--   composite function (∘ᴾ-classical, fun-∘).  A circuit over
--   {H, CNOT, R_k, R_k†} built from pieces that
--   compute F and G computes G ∘ F (⟦++⟧-computes, through
--   PathSum.Compose.CRK's ⟦C₁;C₂⟧ = ⟦C₂⟧ ∘ ⟦C₁⟧); the empty circuit
--   computes the identity and a CNOT its classical function.  setWire
--   t Q is the family of outputs that overwrites wire t with Q and
--   leaves the others alone, idᶜ the one that overwrites nothing.
--
-- * PathSum.CRK.Path: the interpretation state of PathSum.CRK.Circuit
--   read along one path -- the value each wire's linear form takes,
--   and the value of the phase polynomial -- gate by gate, and a whole
--   circuit simulated along a path (Sim, sim-trace).  Nothing there
--   computes a polynomial; every fact is an evaluation.  It also fixes
--   the one instance of PathSum.CRK.Circuit that every module reading
--   a concrete circuit must share (this one included).
--
-- * PathSum.Toffoli.Arith and PathSum.Toffoli.Gate: the integer,
--   Boolean and amplitude identities the proof needs, apart from any
--   circuit; and the circuit with its specification, the wire values
--   along a path, and the sum over the circuit's two path variables.
--
-- * PathSum.Toffoli: the seven-T Toffoli circuit tof c₁ c₂ t on any
--   three distinct wires of an n-wire circuit, for any M = 3 + M₀, and
--   the theorem that it computes |x⟩ ↦ |x[t ≔ x_t ⊕ x_c₁ x_c₂]⟩
--   (tof-computes), i.e. that its path-sum is ≋ the classical
--   path-sum with that output on t (tof-spec); and, through the
--   composition lemmas here, that two of them in a row compute the
--   identity (tof-tof).  The proof reads the circuit's path-sum along
--   each of its four paths (PathSum.CRK.Path),
--   finds the phase ½ y₁ (y₂ + x_t + x_c₁ x_c₂) modulo 1 and the
--   outputs x[t ≔ y₂] -- the paper's path-sum of example 3.3, on any
--   wires -- and sums the paths: the sum over y₁ is 2 or 0 according
--   as y₂ = x_t ⊕ x_c₁ x_c₂, which is what the paper's [HH] step does
--   symbolically, and the remaining factor 2 is the two units of
--   normalisation its [Elim] step removes.  The paper's derivation by
--   the rules of figure 2 is formalised for the closed three-qubit
--   instance in PathSum.Examples.Toffoli; carried out symbolically for
--   arbitrary wires it would have to compare polynomials after
--   substitution, coefficient by coefficient, whereas the amplitudes
--   need only a handful of Boolean and integer identities, all proved
--   by evaluation.  The circuit is never computed as a closed instance.
--
-- Only amplitudes are read, so every statement holds whatever
-- coefficients the output polynomials have beyond their values.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Classical (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; if_then_else_; _xor_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (1ℤ; 0ℤ)
open import Data.List.Base using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary.Decidable using (⌊_⌋)

import Data.Fin.Properties as Fin

open import PathSum.AmpLinear M₀ using (scale-+; scale-exp; scale-comm)
open import PathSum.Assign using (_[_≔_]; same-≗)
open import PathSum.Base using (PathSum; ⟨_,_⟩; out)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.CRK M₀ using (amp-⟦++⟧; norm-++)
open import PathSum.Compose.Properties M₀ using
  (hits-same; outBit-∘; prop-2-7ᶜ; applyᴾ-cong; applyᴾ-scale;
   amp-applyᴾ)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡)
open import PathSum.CRK.Path M₀ using
  (CNOT; Circuit; ⟦_⟧; end; CNOT-sim; amp-sim)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; zpow; scale; scale-map; scale-injective)
open import PathSum.Denotation M₀ using
  (Assign; amp; outBit; hits; _≋_; eval-0ᴾ-val; eval-μ-val)
open import PathSum.Polynomial using (Poly; x[_]; 0ᴾ; μ; eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Boolean using (BExp; ⟦_⟧ᵉ; liftᵉ; eval-liftᵉ)
open import PathSum.Polynomial.Properties using (eval-cong)

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
-- Classical path-sums

-- The only path of a path-sum without path variables.

none : Assign 0
none ()

-- |x⟩ ↦ |f(x)⟩: phase 0, no path variables, no normalisation, and the
-- output polynomials f, read modulo 2.

classical : (Fin n → Poly n 0) → PathSum n 0 0
classical f = ⟨ 0ᴾ , f ⟩

-- The Boolean function it computes: the bit each output takes at x.

fun : (Fin n → Poly n 0) → Assign n → Assign n
fun f x w = outBit (classical f) x none w

-- Its outputs read the same bits along any empty path.

outBit-none : (ξ : PathSum n k 0) (x : Assign n) (y : Assign 0) →
              ∀ w → outBit ξ x y w ≡ outBit ξ x none w
outBit-none ξ x y w = cong odd (eval-cong (out ξ w) {x} {x} {y} {none}
                                          (λ _ → refl) (λ ()))


------------------------------------------------------------------------
-- The amplitudes of a classical path-sum

-- The basis column only reads the values of its state.

δ-≗ : {u u′ : Assign n} → (∀ w → u w ≡ u′ w) → ∀ z → δ u z ≐ δ u′ z
δ-≗ {u = u} {u′} h z = if-cong (same-≗ {x = u} {x′ = u′} {z = z} {z′ = z}
                                       h (λ _ → refl))
                               (λ _ → refl)

-- The single path hits z exactly when z is f(x), with phase 0: the
-- amplitudes are the 0/1 indicator of the graph of fun f.

amp-classical : (f : Fin n → Poly n 0) (x z : Assign n) →
                amp (classical f) x z ≐ δ (fun f x) z
amp-classical {n} f x z = at (λ ())
  where
  at : (y : Assign 0) →
       (if hits (classical f) x y z
        then zpow (eval (0ᴾ {n} {0}) x y) else 0ᴬ) ≐ δ (fun f x) z
  at y = if-cong
    (trans (hits-same (classical f) x y z)
           (same-≗ (outBit-none (classical f) x y) (λ _ → refl)))
    (zpow-≡ (eval-0ᴾ-val x y))


------------------------------------------------------------------------
-- Computing a Boolean function

-- ξ computes F when its operator is the permutation matrix of F, up to
-- its normalisation: the unnormalised amplitude from x to z is
-- √2^k δ (F x) z.
--
-- A record rather than a definition, so that Agda never unfolds it into
-- amplitudes when it compares two such statements: it compares the
-- path-sums and the functions instead.  (Unfolded, the statement that
-- two seven-T Toffoli circuits in a row compute a function, taken from
-- one module into another, exhausted 6 GB.)

infix 4 _computes_

record _computes_ {n k m : ℕ} (ξ : PathSum n k m)
                  (F : Assign n → Assign n) : Set where
  constructor computing
  field
    amp-computes : ∀ x z → amp ξ x z ≐ scale k (δ (F x) z)

open _computes_ public

classical-computes : (f : Fin n → Poly n 0) → classical f computes fun f
classical-computes f = computing (amp-classical f)

-- Only the values of F matter.

computes-≗ : (ξ : PathSum n k m) {F G : Assign n → Assign n} →
             (∀ x w → F x w ≡ G x w) → ξ computes F → ξ computes G
computes-≗ {k = k} ξ h c =
  computing (λ x z → amp-computes c x z ∙ scale-map k (δ-≗ (h x) z))

-- Equivalent path-sums compute the same functions, and two path-sums
-- computing the same function are equivalent.

≋-computes : (ξ : PathSum n k m) (ζ : PathSum n k′ m′)
             {F : Assign n → Assign n} → ξ ≋ ζ → ζ computes F →
             ξ computes F
≋-computes {k = k} {k′ = k′} ξ ζ {F} eq c = computing λ x z →
  scale-injective k′ (amp ξ x z) (scale k (δ (F x) z))
    (eq x z ∙ scale-map k (amp-computes c x z) ∙ scale-comm k k′ (δ (F x) z))

computes-≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′)
             {F : Assign n → Assign n} → ξ computes F → ζ computes F →
             ξ ≋ ζ
computes-≋ {k = k} {k′ = k′} ξ ζ {F} cξ cζ x z =
  scale-map k′ (amp-computes cξ x z) ∙ scale-comm k′ k (δ (F x) z)
  ∙ scale-map k (≐-sym (amp-computes cζ x z))

-- So a path-sum is equivalent to classical f exactly when it computes
-- fun f.

computes⇒≋classical : (ξ : PathSum n k m) (f : Fin n → Poly n 0) →
                      ξ computes fun f → ξ ≋ classical f
computes⇒≋classical ξ f c =
  computes-≋ ξ (classical f) c (classical-computes f)

≋classical⇒computes : (ξ : PathSum n k m) (f : Fin n → Poly n 0) →
                      ξ ≋ classical f → ξ computes fun f
≋classical⇒computes ξ f eq =
  ≋-computes ξ (classical f) eq (classical-computes f)

-- Classical path-sums are equivalent exactly when they compute the same
-- function (one direction; the other is ≋classical⇒computes read at a
-- classical path-sum, with scale 0 the identity).

classical-≋ : (f g : Fin n → Poly n 0) → (∀ x w → fun f x w ≡ fun g x w) →
              classical f ≋ classical g
classical-≋ f g h = computes⇒≋classical (classical f) g
  (computes-≗ (classical f) h (classical-computes f))


------------------------------------------------------------------------
-- Composition

-- By proposition 2.7 the column of ξ′ ∘ ξ at x is U_ξ′ applied to the
-- column of ξ at x, which is √2^k times the basis column at F x; U_ξ′
-- is linear, and maps that basis column to √2^k′ times the one at
-- G (F x).

∘ᴾ-computes : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m)
              {F G : Assign n → Assign n} → ξ computes F → ξ′ computes G →
              (ξ′ ∘ᴾ ξ) computes (λ x → G (F x))
∘ᴾ-computes {k′ = k′} {k = k} ξ′ ξ {F} {G} cF cG = computing λ x z →
  prop-2-7ᶜ ξ′ ξ x z
  ∙ applyᴾ-cong ξ′ {amp ξ x} {λ w → scale k (δ (F x) w)}
                (amp-computes cF x) z
  ∙ ≐-sym (applyᴾ-scale ξ′ k (δ (F x)) z)
  ∙ scale-map k (≐-sym (amp-applyᴾ ξ′ (F x) z))
  ∙ scale-map k (amp-computes cG (F x) z)
  ∙ scale-+ k k′ (δ (G (F x)) z)

-- Two classical path-sums compose to a classical one.  Its outputs are
-- the composite's own -- g with the lift of f substituted for the
-- inputs (definition 2.6) -- and its function is the composite.

fun-∘ : (g f : Fin n → Poly n 0) (x : Assign n) →
        ∀ w → fun (out (classical g ∘ᴾ classical f)) x w ≡
              fun g (fun f x) w
fun-∘ g f x w = outBit-∘ (classical g) (classical f) x none none w

∘ᴾ-classical : (g f : Fin n → Poly n 0) →
               (classical g ∘ᴾ classical f) ≋
               classical (out (classical g ∘ᴾ classical f))
∘ᴾ-classical g f =
  computes⇒≋classical (classical g ∘ᴾ classical f)
    (out (classical g ∘ᴾ classical f))
    (computes-≗ (classical g ∘ᴾ classical f)
      (λ x w → sym (fun-∘ g f x w))
      (∘ᴾ-computes (classical g) (classical f)
                   (classical-computes f) (classical-computes g)))

-- Any classical path-sum with the composite function will do.

∘ᴾ-classical-≋ : (g f h : Fin n → Poly n 0) →
                 (∀ x w → fun g (fun f x) w ≡ fun h x w) →
                 (classical g ∘ᴾ classical f) ≋ classical h
∘ᴾ-classical-≋ g f h eq =
  computes⇒≋classical (classical g ∘ᴾ classical f) h
    (computes-≗ (classical g ∘ᴾ classical f) eq
      (∘ᴾ-computes (classical g) (classical f)
                   (classical-computes f) (classical-computes g)))


------------------------------------------------------------------------
-- Circuits over {H, CNOT, R_k, R_k†}

-- ⟦C₁;C₂⟧ = ⟦C₂⟧ ∘ ⟦C₁⟧ (PathSum.Compose.CRK), so if C₁ computes F and
-- C₂ computes G then C₁;C₂ computes G ∘ F.

⟦++⟧-computes : (C D : Circuit n) {F G : Assign n → Assign n} →
                ⟦ C ⟧ computes F → ⟦ D ⟧ computes G →
                ⟦ C ++ D ⟧ computes (λ x → G (F x))
⟦++⟧-computes C D {F} {G} cC cD = computing λ x z →
  amp-⟦++⟧ C D x z
  ∙ amp-computes (∘ᴾ-computes ⟦ D ⟧ ⟦ C ⟧ cC cD) x z
  ∙ scale-exp (δ (G (F x)) z) (sym (norm-++ C D))

-- The empty circuit computes the identity, and a CNOT adds its control
-- to its target.  Neither allocates a path variable, so the single
-- path is read by a simulation (PathSum.CRK.Path) of no gate or one.

⟦[]⟧-computes : ⟦_⟧ {n} [] computes (λ x → x)
⟦[]⟧-computes = computing λ x z →
  amp-sim [] x z (λ _ → x) (λ _ → 0ℤ) (λ _ → end (λ _ → refl) refl)

⟦CNOT⟧-computes : (c t : Fin n) (p : c ≢ t) →
                  ⟦ CNOT c t p ∷ [] ⟧ computes (λ x → x [ t ≔ x t xor x c ])
⟦CNOT⟧-computes c t p = computing λ x z →
  amp-sim (CNOT c t p ∷ []) x z (λ _ → x [ t ≔ x t xor x c ]) (λ _ → 0ℤ)
          (λ _ → CNOT-sim (λ _ → refl) (end (λ _ → refl) refl))

-- The same, for circuits shown equivalent to classical path-sums.

⟦++⟧-classical : (C D : Circuit n) (f g h : Fin n → Poly n 0) →
                 ⟦ C ⟧ ≋ classical f → ⟦ D ⟧ ≋ classical g →
                 (∀ x w → fun g (fun f x) w ≡ fun h x w) →
                 ⟦ C ++ D ⟧ ≋ classical h
⟦++⟧-classical C D f g h eqC eqD eq =
  computes⇒≋classical ⟦ C ++ D ⟧ h
    (computes-≗ ⟦ C ++ D ⟧ eq
      (⟦++⟧-computes C D (≋classical⇒computes ⟦ C ⟧ f eqC)
                         (≋classical⇒computes ⟦ D ⟧ g eqD)))


------------------------------------------------------------------------
-- The identity, and overwriting one wire

private
  odd-if : ∀ b → odd (if b then 1ℤ else 0ℤ) ≡ b
  odd-if true  = refl
  odd-if false = refl

-- |x⟩ ↦ |x⟩: every output is its input.  The empty circuit is
-- equivalent to it.

idᶜ : Fin n → Poly n 0
idᶜ w = μ x[ w ]

fun-idᶜ : (x : Assign n) → ∀ w → fun idᶜ x w ≡ x w
fun-idᶜ x w = trans (cong odd (eval-μ-val x[ w ] x none)) (odd-if (x w))

⟦[]⟧-classical : ⟦_⟧ {n} [] ≋ classical idᶜ
⟦[]⟧-classical = computes⇒≋classical (⟦_⟧ []) idᶜ
  (computes-≗ (⟦_⟧ []) (λ x w → sym (fun-idᶜ x w)) ⟦[]⟧-computes)

-- |x⟩ ↦ |x[t ≔ Q(x)]⟩: every output is its input, except wire t, which
-- reads Q.

setWire : Fin n → Poly n 0 → Fin n → Poly n 0
setWire t Q w = if ⌊ w Fin.≟ t ⌋ then Q else μ x[ w ]

fun-setWire : (t : Fin n) (Q : Poly n 0) (x : Assign n) →
              ∀ w → fun (setWire t Q) x w ≡
                    (x [ t ≔ odd (eval Q x none) ]) w
fun-setWire t Q x w = go ⌊ w Fin.≟ t ⌋
  where
  go : ∀ d → odd (eval (if d then Q else μ x[ w ]) x none) ≡
             (if d then odd (eval Q x none) else x w)
  go true  = refl
  go false = trans (cong odd (eval-μ-val x[ w ] x none)) (odd-if (x w))

-- The lift of a Boolean expression reads the expression's value
-- (lemma 2.5, PathSum.Polynomial.Boolean.eval-liftᵉ).

odd-liftᵉ : (e : BExp n 0) (x : Assign n) →
            odd (eval (liftᵉ e) x none) ≡ ⟦ e ⟧ᵉ x none
odd-liftᵉ e x = trans (cong odd (eval-liftᵉ e x none)) (odd-if (⟦ e ⟧ᵉ x none))

-- So a classical path-sum whose outputs are the lifts of Boolean
-- expressions computes the expressions' values.

fun-liftᵉ : (e : Fin n → BExp n 0) (x : Assign n) →
            ∀ w → fun (λ v → liftᵉ (e v)) x w ≡ ⟦ e w ⟧ᵉ x none
fun-liftᵉ e x w = odd-liftᵉ (e w) x

fun-setWireᵉ : (t : Fin n) (e : BExp n 0) (x : Assign n) →
               ∀ w → fun (setWire t (liftᵉ e)) x w ≡
                     (x [ t ≔ ⟦ e ⟧ᵉ x none ]) w
fun-setWireᵉ t e x w = trans (fun-setWire t (liftᵉ e) x w)
  (cong (λ b → (x [ t ≔ b ]) w) (odd-liftᵉ e x))
