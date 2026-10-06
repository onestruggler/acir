------------------------------------------------------------------------
-- Presentations of groups
--
-- Every normal form of the ladder is exponentially large: proposition
-- 3.2's time bound fails for figure 2, for polynomials written as sums
-- of monomials (Amy, QPL 2018, sections 3 and 3.2)
--
-- The paper.  Section 3: "A key feature of our calculus is that the
-- reduction rules strictly decrease the number of path variables,
-- producing a (not necessarily unique) normal form in polynomial
-- time."  Section 3.2: "Moreover, each rewrite rule can be matched
-- against in polynomial time, hence every path-sum reduces to a normal
-- form in polynomial time."  Proposition 3.2: "Every sequence of
-- rewrites terminates with an irreducible path-sum.  The sequence is
-- linear in the number of path variables m and for an n-qubit
-- path-sum takes time polynomial in n and m."  (Section 4 repeats it:
-- "While our calculus computes a normal form in polynomial time ...")
--
-- Erratum, with its qualification.  For figure 2 as stated, and for
-- path-sums represented as in definition 2.1 -- the phase and the
-- output polynomials written as sums of monomials -- these time claims
-- are false, reading time as at least the size of the output.
-- PathSum.Ladder's ξ n has 2n qubits, 2n path variables, 4n terms in
-- PathSum.Size.Sparse's representation (ξ-represents, ξ-terms), order
-- at most 3 (ξ-order, below; exactly 3 for n ≥ 2 -- the term
-- ½u₁v₀x₁ -- which is not formalised; ξ 1 has order 2) and
-- single-variable outputs.  It has a normal form (normal-form-exists),
-- every chain to one has at most 2n steps (PathSum.Full.⟶ᶠ*-bounded),
-- and every normal form reachable from it -- whatever rules are
-- applied, in whatever order, at whatever variables (PathSum.Full's
-- _⟶ᶠ_) -- has no path variables and normalisation 0
-- (normal-form-shape), phase 0 modulo 1 (normal-form-phase), outputs x
-- and V (normal-form-outputs), and in its last output an odd
-- coefficient on each of the 2^n monomials over the x inputs
-- (normal-form-odd).  So
--
-- * every list of monomials (with integer coefficients) whose values,
--   read modulo 2, are that output's -- in any order, with repetitions,
--   with even coefficients thrown in -- has at least 2^n entries
--   (normal-form-terms);
-- * PathSum.Size.Sparse's representations, whose outputs are
--   Z₂-linear forms, represent none of these normal forms once n ≥ 2
--   (normal-form-no-rep): the cost model of PathSum.Cost cannot hold
--   them.
--
-- The quantifier is the strong one: *every* reachable normal form is
-- large, so no strategy -- no choice of rules, order or variables --
-- reaches a small one, and any procedure that outputs a normal form as
-- a list of monomials writes at least 2^n of them.  The inference
-- ("each rule can be matched in polynomial time, hence ...") fails
-- because a reduct can be much larger than its redex: [HH] substitutes
-- a non-linear quotient, which multiplies out.
--
-- Not refuted.  Termination, and a sequence length linear in m
-- (PathSum.Full); the time bound for the linear rules at fixed order
-- (PathSum.Cost.Normalise) and for all of figure 2 at order 2
-- (PathSum.Cost.Irreducible) -- for n ≥ 2 the linear normaliser on
-- ξ n stops, in polynomial time, at a path-sum that is not a normal
-- form of figure 2 (this follows from normal-form-no-rep and
-- PathSum.Cost.Normalise, and is not formalised; at n = 1 the quotient
-- of the only gadget is affine and the linear rules reduce ξ 1
-- completely); the claim for ⟦ C ⟧ of Clifford+T circuits, the family
-- being one of path-sums -- what the paper's composition gives for a
-- ladder of Toffoli gates written with example 3.3's Toffoli
-- path-sum -- and the normal forms reachable from ⟦ C ⟧ not being
-- characterised here; and representations with sharing (a Boolean
-- circuit, or the lifting liftᵉ of a PathSum.Polynomial.Boolean.BExp)
-- or with complemented literals (an exclusive sum of products), in
-- which these normal forms have polynomial size: V_g is
-- a_g ⊕ ¬x_g a_(g-1) ⊕ ... ⊕ ¬x_g ⋯ ¬x_0, g + 2 products, and with
-- sharing all of V costs O(n).  Nothing is claimed about running time
-- on a machine; time is read as at least output size, as in
-- PathSum.Hardness.Blowup.
--
-- The proof: PathSum.Ladder.Steps (every step keeps the invariant of
-- PathSum.Ladder.Invariant), PathSum.Ladder.Progress (a path-sum
-- satisfying it with a path variable left is reducible), and here:
-- with no path variables left every gadget is dead (all-dead), the
-- normalisation is 0, and the last output at a = 0 is the NOR of the
-- x's (Gadget.Vs-dead); Möbius inversion modulo 2 at a = 0
-- (andNot-coefficients, after eval-ext0, as in PathSum.Hardness.Blowup)
-- gives every coefficient over the x's odd, and PathSum.Polynomial.
-- Count turns that into the bound on lists of monomials.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Ladder.Size (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using
  (Fin; zero; suc; splitAt; fromℕ; inject₁; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.Fin.Subset using (Subset; inside; outside)
  renaming (⊥ to ∅)
open import Data.Integer.Base using (ℤ; 0ℤ; +_)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Properties using (+-identityˡ; *-zeroʳ)
open import Data.Integer.Divisibility.Signed using (_∣_; ∣m∣n⇒∣m+n; ∣m⇒∣m*n)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

import Data.List.Relation.Unary.All as AllU
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Nat.Base using (zero; suc; _+_; _*_; _^_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (≤-reflexive; ≤-trans; +-mono-≤; n≤1+n; ∸-monoʳ-≤; _≤?_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′; map₁)
open import Data.Vec.Base using ([]; _∷_; _++_; replicate)
open import Data.Vec.Properties using (++-injectiveˡ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Nat.Base as ℕ

private
  M : ℕ
  M = ℕ.suc (ℕ.suc (ℕ.suc M₀))

open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Full M using (_⟶ᶠ*_)
open import PathSum.Full.Match M using (Irreducibleᶠ; normal-formᶠ)
open import PathSum.Ladder M₀ using
  (ξ; ξ-rep; ξ-represents; ξ-terms; xw; aw; ½ᵗ; coeff-½; prevMon;
   gadgetTerms; concatF; phaseTerms; _≡ᴹ_; ≡ᴹ-trans; ≡⇒≡ᴹ; hb)
open import PathSum.Ladder.Gadget using
  (State; live; half; dead; U; V; present; xb; ab; Vs-dead; andNot;
   wsum; wsum-cong; Gad; gad; state; step; term; Vs; Bsum; step-dead;
   term-dead; Vs-cong)
open import PathSum.Ladder.Invariant M₀ using
  (Layout; st; loc; loc-present; gads; Inv; lay; k-eq; out-ok; phase-ok;
   Inv-ξ;
   _◂_)
open import PathSum.Ladder.Steps M₀ using (Inv-steps; outF-aw)
open import PathSum.Ladder.Progress M₀ using (progress)
open import PathSum.Linear using (liftᴸ; liftXor-linear)
open import PathSum.Mobius using (evalˢ; eval-nested)
open import PathSum.Order M using (Ord≤; pow; val; pow-∣)
open import PathSum.Polynomial using
  (Mon; Poly; Var; x[_]; y[_]; ⟪_⟫; _∪ᵐ_; Σsub; sat; eval; ∥_∥; _≟ᵐ_)
open import PathSum.Polynomial.Product using (monoᴾ)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Count using
  (count; count-true; module Terms)
open import PathSum.Polynomial.Parity using (odd-+; odd-even)
open import PathSum.Polynomial.Properties using
  (Σsub-0; Σsub-cong; sat-cong; ∥⟪v⟫∥≡1; ∥∪ᵐ∥≤; ∥1ᵐ∥≡0; i∣0)
open import PathSum.Size.Monomials using (Σˡ)
open import PathSum.Size.Sparse M using
  (Term; coeff; ⟦⟧ˢ-at; Rep; Represents; forms; terms)
open import Relation.Nullary.Decidable using (yes; no)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- With no path variables left, every gadget is dead

private
  nothing₀ : (mc : Maybe (Fin 0)) → is-just mc ≡ false
  nothing₀ (just ())
  nothing₀ nothing = refl

  true≢false : ¬ (true ≡ false)
  true≢false ()

all-dead : (L : Layout n 0) → ∀ g → st L g ≡ dead
all-dead L g = by (st L g) refl
  where
  absentᵏ : ∀ b → present (st L g) b ≡ false
  absentᵏ b = trans (sym (loc-present L g b)) (nothing₀ (loc L g b))

  by : (s : State) → st L g ≡ s → st L g ≡ dead
  by live e = ⊥-elim (true≢false
    (trans (sym (cong (λ s → present s U) e)) (absentᵏ U)))
  by half e = ⊥-elim (true≢false
    (trans (sym (cong (λ s → present s V) e)) (absentᵏ V)))
  by dead e = e

private
  wsum-dead : ∀ n → wsum {n} (λ _ → dead) ≡ 0
  wsum-dead zero    = refl
  wsum-dead (suc n) = wsum-dead n


------------------------------------------------------------------------
-- A reachable normal form has no path variables

reducible : {ζ : PathSum (n + n) k m} → Inv n ζ → Irreducibleᶠ ζ → m ≡ 0
reducible {m = zero}  I irr = refl
reducible {m = suc m} I irr =
  ⊥-elim (irr (proj₂ (proj₂ (proj₂ (progress I)))))

normal-form-shape : (n : ℕ) {k′ m′ : ℕ} {ζ : PathSum (n + n) k′ m′} →
                    ξ n ⟶ᶠ* ζ → Irreducibleᶠ ζ → (m′ ≡ 0) × (k′ ≡ 0)
normal-form-shape n {ζ = ζ} chain irr = m≡0 , by m≡0 I
  where
  I : Inv n ζ
  I = Inv-steps (Inv-ξ n) chain

  m≡0 = reducible I irr

  by : ∀ {k m} {ζ : PathSum (n + n) k m} → m ≡ 0 → Inv n ζ → k ≡ 0
  by refl I′ = trans (k-eq I′)
    (trans (wsum-cong (all-dead (lay I′))) (wsum-dead n))


------------------------------------------------------------------------
-- What a reachable normal form computes

-- The ladder's function: the x's unchanged, and a_g ↦ V_g with
-- V_g = a_g ⊕ (¬x_g ∧ V_(g-1)), V_(-1) = 1 -- the values every gadget
-- hands on once all are dead.

ladderV : (n : ℕ) → (Fin (n + n) → Bool) → Fin n → Bool
ladderV n x = Vs true (λ g → gad dead (x (xw {n} g)) (x (aw {n} g)) false false)

ladderOut : (n : ℕ) → (Fin (n + n) → Bool) → Fin (n + n) → Bool
ladderOut n x w = [ (λ g → x (xw {n} g)) , ladderV n x ]′ (splitAt n w)

private
  Bsum-dead : (G : Fin n → Gad) → (∀ h → state (G h) ≡ dead) →
              ∀ p → Bsum p G ≡ false
  Bsum-dead {zero}  G d p = refl
  Bsum-dead {suc n} G d p =
    cong₂ _xor_ (term-dead (G zero) p (d zero))
                (Bsum-dead (λ h → G (suc h)) (λ h → d (suc h))
                           (step (G zero) p))

-- Every reachable normal form has phase 0 modulo 1 ...

normal-form-phase : (n : ℕ) {k′ m′ : ℕ} {ζ : PathSum (n + n) k′ m′} →
                    ξ n ⟶ᶠ* ζ → Irreducibleᶠ ζ →
                    ∀ x y → eval (phase ζ) x y ≡ᴹ 0ℤ
normal-form-phase n {ζ = ζ} chain irr = by (reducible I irr) I
  where
  I : Inv n ζ
  I = Inv-steps (Inv-ξ n) chain

  by : ∀ {k m} {ζ : PathSum (n + n) k m} → m ≡ 0 → Inv n ζ →
       ∀ x y → eval (phase ζ) x y ≡ᴹ 0ℤ
  by refl I′ x y = ≡ᴹ-trans (phase-ok I′ x y)
    (≡⇒≡ᴹ (cong hb (Bsum-dead (gads (lay I′) x y) (all-dead (lay I′)) true)))

-- ... and outputs x and V, read modulo 2.  (That ξ n itself has the
-- operator |x, a⟩ ↦ |x, V⟩ then follows by soundness, PathSum.Full.
-- Sound; it is not stated here.)

normal-form-outputs : (n : ℕ) {k′ m′ : ℕ} {ζ : PathSum (n + n) k′ m′} →
                      ξ n ⟶ᶠ* ζ → Irreducibleᶠ ζ →
                      ∀ w x y → odd (eval (out ζ w) x y) ≡ ladderOut n x w
normal-form-outputs n {ζ = ζ} chain irr = by (reducible I irr) I
  where
  I : Inv n ζ
  I = Inv-steps (Inv-ξ n) chain

  by : ∀ {k m} {ζ : PathSum (n + n) k m} → m ≡ 0 → Inv n ζ →
       ∀ w x y → odd (eval (out ζ w) x y) ≡ ladderOut n x w
  by refl I′ w x y = trans (out-ok I′ w x y) (sides (splitAt n w))
    where
    L = lay I′

    same : ∀ g → Vs true (gads L x y) g ≡ ladderV n x g
    same = Vs-cong (gads L x y)
      (λ g → gad dead (x (xw {n} g)) (x (aw {n} g)) false false)
      (λ h q → step-dead (gads L x y h) q (all-dead L h)) true

    sides : (s : Fin n ⊎ Fin n) →
            [ (λ g → x (xw {n} g)) , Vs true (gads L x y) ]′ s ≡
            [ (λ g → x (xw {n} g)) , ladderV n x ]′ s
    sides (inj₁ g) = refl
    sides (inj₂ g) = same g


------------------------------------------------------------------------
-- The last output at a = 0 is the NOR of the x's

-- The point that is v on the x wires and 0 on the a wires.

ext0 : (Fin n → Bool) → Fin (n + n) → Bool
ext0 {n} v w = [ v , (λ _ → false) ]′ (splitAt n w)

private
  none : Fin 0 → Bool
  none ()

  ext0-x : (v : Fin n → Bool) (g : Fin n) → ext0 v (xw g) ≡ v g
  ext0-x {n} v g = cong [ v , (λ _ → false) ]′ (splitAt-↑ˡ n g n)

  ext0-a : (v : Fin n → Bool) (g : Fin n) → ext0 v (aw g) ≡ false
  ext0-a {n} v g = cong [ v , (λ _ → false) ]′ (splitAt-↑ʳ n n g)

  andNot-cong : ∀ p {x x′ : Fin n → Bool} → (∀ i → x i ≡ x′ i) →
                andNot p x ≡ andNot p x′
  andNot-cong {zero}  p h = refl
  andNot-cong {suc n} p {x} {x′} h = trans
    (cong (λ b → andNot (not b ∧ p) (λ i → x (suc i))) (h zero))
    (andNot-cong (not (x′ zero) ∧ p) {x = λ i → x (suc i)}
                 {x′ = λ i → x′ (suc i)} (λ i → h (suc i)))

nor-out : (n′ : ℕ) {k′ : ℕ} {ζ : PathSum (suc n′ + suc n′) k′ 0} →
          Inv (suc n′) ζ → ∀ v →
          (y : Fin 0 → Bool) →
          odd (eval (out ζ (aw (fromℕ n′))) (ext0 v) y) ≡ andNot true v
nor-out n′ {ζ = ζ} I v y = trans (out-ok I (aw (fromℕ n′)) (ext0 v) y)
  (trans (outF-aw L (ext0 v) y (fromℕ n′))
    (trans (Vs-dead (gads L (ext0 v) y) (all-dead L)
                    (λ h → ext0-a v h) true)
           (andNot-cong true (λ h → ext0-x v h))))
  where
  L : Layout (suc n′) 0
  L = lay I


------------------------------------------------------------------------
-- Möbius inversion modulo 2 for the NOR

-- (As PathSum.Hardness.Blowup's nor-coefficients, for p ∧ NOR.)

private
  evalˢ-false : ∀ {k} (f : Subset (suc k) → ℤ) (x : Fin k → Bool) →
                evalˢ f (false ◂ x) ≡ evalˢ (λ s → f (outside ∷ s)) x
  evalˢ-false {k} f x = trans
    (cong (_+ℤ evalˢ (λ s → f (outside ∷ s)) x) (Σsub-0 {k}))
    (+-identityˡ _)

  andNot-false : ∀ {k} (x : Fin k → Bool) → andNot false x ≡ false
  andNot-false {zero}  x = refl
  andNot-false {suc k} x = trans
    (cong (λ b → andNot b (λ i → x (suc i))) (∧-zeroʳ (not (x zero))))
    (andNot-false (λ i → x (suc i)))

  xor-false : ∀ a b → a xor b ≡ false → a ≡ b
  xor-false true  true  _ = refl
  xor-false false false _ = refl
  xor-false true  false ()
  xor-false false true  ()

andNot-coefficients : ∀ {k} (f : Subset k → ℤ) (p : Bool) →
                      (∀ x → odd (evalˢ f x) ≡ andNot p x) →
                      ∀ s → odd (f s) ≡ p
andNot-coefficients {zero}  f p h []            = h (λ ())
andNot-coefficients {suc k} f p h (outside ∷ s) =
  andNot-coefficients (λ s → f (outside ∷ s)) p h₀ s
  where
  h₀ : ∀ x → odd (evalˢ (λ s → f (outside ∷ s)) x) ≡ andNot p x
  h₀ x = trans (cong odd (sym (evalˢ-false f x))) (h (false ◂ x))
andNot-coefficients {suc k} f p h (inside ∷ s) =
  andNot-coefficients (λ s → f (inside ∷ s)) p h₁ s
  where
  h₀ : ∀ x → odd (evalˢ (λ s → f (outside ∷ s)) x) ≡ andNot p x
  h₀ x = trans (cong odd (sym (evalˢ-false f x))) (h (false ◂ x))

  h₁ : ∀ x → odd (evalˢ (λ s → f (inside ∷ s)) x) ≡ andNot p x
  -- At y₀ = 1 the value is the sum of the halves' values, and the NOR
  -- is 0 there.
  h₁ x = trans (xor-false _ _
    (trans (sym (odd-+ (evalˢ (λ s → f (inside ∷ s)) x)
                       (evalˢ (λ s → f (outside ∷ s)) x)))
           (trans (h (true ◂ x)) (andNot-false x))))
    (h₀ x)

-- At the points with a = 0 a polynomial without path variables reads
-- its coefficients on the monomials over the x wires.  (PathSum.
-- Hardness.Blowup.eval-ext0.)

private
  ext0′ : ∀ {n r} → (Fin n → Bool) → Fin (n + r) → Bool
  ext0′ {n} v w = [ v , (λ _ → false) ]′ (splitAt n w)

  ext0-suc : ∀ {n r} (v : Fin (suc n) → Bool) (w : Fin (n + r)) →
             ext0′ {suc n} {r} v (suc w) ≡
             ext0′ {n} {r} (λ i → v (suc i)) w
  ext0-suc {n} {r} v w = go (splitAt n w)
    where
    go : (s : Fin n ⊎ Fin r) →
         [ v , (λ _ → false) ]′ (map₁ suc s) ≡
         [ (λ i → v (suc i)) , (λ _ → false) ]′ s
    go (inj₁ i) = refl
    go (inj₂ j) = refl

  evalˢ-zeros : ∀ {r} (g : Subset r → ℤ) →
                evalˢ g (λ _ → false) ≡ g (replicate r outside)
  evalˢ-zeros {zero}  g = refl
  evalˢ-zeros {suc r} g =
    trans (cong (_+ℤ evalˢ (λ s → g (outside ∷ s)) (λ _ → false)) (Σsub-0 {r}))
    (trans (+-identityˡ _) (evalˢ-zeros (λ s → g (outside ∷ s))))

  evalˢ-ext0 : ∀ {n r} (g : Subset (n + r) → ℤ) (v : Fin n → Bool) →
               evalˢ g (ext0′ {n} {r} v) ≡
               evalˢ (λ s → g (s ++ replicate r outside)) v
  evalˢ-ext0 {zero}      g v = evalˢ-zeros g
  evalˢ-ext0 {suc n} {r} g v = cong₂ _+ℤ_ (head (v zero)) tail
    where
    v′ : Fin n → Bool
    v′ i = v (suc i)

    shifted : ∀ s → sat s (λ i → ext0′ {suc n} {r} v (suc i)) ≡
                    sat s (ext0′ {n} {r} v′)
    shifted s = sat-cong s (ext0-suc {n} {r} v)

    head : ∀ b →
           Σsub (λ s → if b ∧ sat s (λ i → ext0′ {suc n} {r} v (suc i))
                       then g (inside ∷ s) else 0ℤ) ≡
           Σsub (λ s → if b ∧ sat s v′
                       then g (inside ∷ (s ++ replicate r outside)) else 0ℤ)
    head true  =
      trans (Σsub-cong (λ s → cong (λ c → if c then g (inside ∷ s) else 0ℤ)
                                   (shifted s)))
            (evalˢ-ext0 (λ s → g (inside ∷ s)) v′)
    head false = trans (Σsub-0 {n + r}) (sym (Σsub-0 {n}))

    tail : Σsub (λ s → if sat s (λ i → ext0′ {suc n} {r} v (suc i))
                       then g (outside ∷ s) else 0ℤ) ≡
           Σsub (λ s → if sat s v′
                       then g (outside ∷ (s ++ replicate r outside)) else 0ℤ)
    tail =
      trans (Σsub-cong (λ s → cong (λ c → if c then g (outside ∷ s) else 0ℤ)
                                   (shifted s)))
            (evalˢ-ext0 (λ s → g (outside ∷ s)) v′)

eval-ext0 : (P : Poly (n + n) 0) (v : Fin n → Bool) →
            (y : Fin 0 → Bool) → eval P (ext0 v) y ≡
            evalˢ (λ s → P (s ++ replicate n outside , [])) v
eval-ext0 {n} P v y =
  trans (eval-nested P (ext0 v) y) (evalˢ-ext0 {n} {n} (λ α → P (α , [])) v)


------------------------------------------------------------------------
-- Every polynomial with the last output's values has 2^n odd
-- coefficients

-- The monomial of the x's in s.

onX : Subset n → Mon (n + n) 0
onX {n} s = s ++ replicate n outside , []

private
  onX-injective : (s t : Subset n) → onX s ≡ onX t → s ≡ t
  onX-injective s t e = ++-injectiveˡ s t (cong proj₁ e)

  -- Any polynomial P with the output's values modulo 2.
  odd-onX : (n′ : ℕ) {k′ : ℕ} {ζ : PathSum (suc n′ + suc n′) k′ 0} →
            Inv (suc n′) ζ → (P : Poly (suc n′ + suc n′) 0) →
            (∀ x y → odd (eval P x y) ≡ odd (eval (out ζ (aw (fromℕ n′))) x y)) →
            ∀ s → odd (P (onX s)) ≡ true
  odd-onX n′ {ζ = ζ} I P h = andNot-coefficients
    (λ s → P (s ++ replicate (suc n′) outside , [])) true
    (λ v → trans (cong odd (sym (eval-ext0 P v none)))
                 (trans (h (ext0 v) none) (nor-out n′ I v none)))

-- A reachable normal form of ξ (n′ + 1): its last output has an odd
-- coefficient on every monomial over the x wires (the y part of the
-- monomial is empty; there are no path variables) ...

normal-form-odd : (n′ : ℕ) {k′ m′ : ℕ} {ζ : PathSum (suc n′ + suc n′) k′ m′} →
                  ξ (suc n′) ⟶ᶠ* ζ → Irreducibleᶠ ζ →
                  ∀ (s : Subset (suc n′)) →
                  odd (out ζ (aw (fromℕ n′))
                         (s ++ replicate (suc n′) outside , ∅)) ≡ true
normal-form-odd n′ {ζ = ζ} chain irr = by (reducible I irr) I
  where
  I : Inv (suc n′) ζ
  I = Inv-steps (Inv-ξ (suc n′)) chain

  by : ∀ {k m} {ζ : PathSum (suc n′ + suc n′) k m} → m ≡ 0 →
       Inv (suc n′) ζ → ∀ s →
       odd (out ζ (aw (fromℕ n′)) (s ++ replicate (suc n′) outside , ∅)) ≡ true
  by {ζ = ζ′} refl I′ = odd-onX n′ I′ (out ζ′ (aw (fromℕ n′))) (λ x y → refl)

-- ... so every list of monomials (with integer coefficients) whose
-- values are that output's, modulo 2, has at least 2^(n′+1) entries ...

⟦_⟧ᵗ : List (Mon n m × ℤ) → Poly n m
⟦_⟧ᵗ = Terms.⟦_⟧ᵗ _≟ᵐ_

normal-form-terms : (n′ : ℕ) {k′ m′ : ℕ}
                    {ζ : PathSum (suc n′ + suc n′) k′ m′} →
                    ξ (suc n′) ⟶ᶠ* ζ → Irreducibleᶠ ζ →
                    (ts : List (Mon (suc n′ + suc n′) m′ × ℤ)) →
                    (∀ x y → odd (eval ⟦ ts ⟧ᵗ x y) ≡
                             odd (eval (out ζ (aw (fromℕ n′))) x y)) →
                    2 ^ suc n′ ≤ length ts
normal-form-terms n′ {ζ = ζ} chain irr = by (reducible I irr) I
  where
  I : Inv (suc n′) ζ
  I = Inv-steps (Inv-ξ (suc n′)) chain

  by : ∀ {k m} {ζ : PathSum (suc n′ + suc n′) k m} → m ≡ 0 →
       Inv (suc n′) ζ → (ts : List (Mon (suc n′ + suc n′) m × ℤ)) →
       (∀ x y → odd (eval ⟦ ts ⟧ᵗ x y) ≡
                odd (eval (out ζ (aw (fromℕ n′))) x y)) →
       2 ^ suc n′ ≤ length ts
  by {ζ = ζ′} refl I′ ts h = subst (_≤ length ts) (count-true {suc n′})
    (Terms.terms-cover _≟ᵐ_ {suc n′} (λ _ → true) (onX {suc n′})
                       onX-injective ts
      (λ s _ → odd-onX n′ I′ ⟦ ts ⟧ᵗ h s))

-- ... and once n ≥ 2 no representation of PathSum.Size.Sparse -- the
-- cost model's, whose outputs are Z₂-linear forms -- represents it:
-- the monomial x₀x₁ has an odd coefficient, which a linear form's
-- lifting never has.

normal-form-no-rep : (n″ : ℕ) {k′ m′ : ℕ}
                     {ζ : PathSum (suc (suc n″) + suc (suc n″)) k′ m′} →
                     ξ (suc (suc n″)) ⟶ᶠ* ζ → Irreducibleᶠ ζ →
                     (R : Rep (suc (suc n″) + suc (suc n″)) m′) →
                     ¬ Represents ζ R
normal-form-no-rep n″ {ζ = ζ} chain irr = by (reducible I irr) I
  where
  I : Inv (suc (suc n″)) ζ
  I = Inv-steps (Inv-ξ (suc (suc n″))) chain

  w = aw (fromℕ (suc n″))

  -- x₀x₁: the first two x wires.
  s₂ : Subset (suc (suc n″))
  s₂ = inside ∷ inside ∷ ∅

  by : ∀ {k m} {ζ : PathSum (suc (suc n″) + suc (suc n″)) k m} → m ≡ 0 →
       Inv (suc (suc n″)) ζ → (R : Rep (suc (suc n″) + suc (suc n″)) m) →
       ¬ Represents ζ R
  by {ζ = ζ′} refl I′ R (_ , outs) = true≢false (trans (sym odd-here)
    (trans (cong odd (outs w (onX s₂)))
           (odd-even (liftXor-linear (proj₁ (forms R w)) (proj₂ (forms R w))
                                     (onX s₂) (s≤s (s≤s z≤n))))))
    where
    odd-here : odd (out ζ′ w (onX s₂)) ≡ true
    odd-here = odd-onX (suc n″) I′ (out ζ′ w) (λ x y → refl) s₂


------------------------------------------------------------------------
-- A normal form exists

normal-form-exists : (n : ℕ) →
                     Σ ℕ λ k′ → Σ ℕ λ m′ → Σ (PathSum (n + n) k′ m′) λ ζ →
                     (ξ n ⟶ᶠ* ζ) × Irreducibleᶠ ζ
normal-form-exists n = normal-formᶠ (ξ n)




------------------------------------------------------------------------
-- The family has order at most 3

-- Every term of ξ n is ½ times a monomial of degree at most 3, so its
-- phase has order at most 3 (definition 2.11, PathSum.Order): a fixed
-- order, the setting of proposition 3.2's time bound in PathSum.Cost.
-- (For n ≥ 2 the order is exactly 3, by the term ½u₁v₀x₁; that is not
-- formalised.  ξ 1 has order 2.)

private
  Small : (n : ℕ) → Term (n + n) (n + n) → Set
  Small n t = (∥ proj₁ t ∥ ≤ 3) × (proj₂ t ≡ ½ᵗ)

  deg-⟪⟫ : (v : Var n m) → ∥ ⟪ v ⟫ ∥ ≤ 1
  deg-⟪⟫ v = ≤-reflexive (∥⟪v⟫∥≡1 v)

  deg-∪ : ∀ {i j} (a b : Mon n m) → ∥ a ∥ ≤ i → ∥ b ∥ ≤ j →
          ∥ a ∪ᵐ b ∥ ≤ i + j
  deg-∪ a b ha hb = ≤-trans (∥∪ᵐ∥≤ a b) (+-mono-≤ ha hb)

  deg-prev : (g : Fin n) → ∥ prevMon g ∥ ≤ 1
  deg-prev {suc n} zero    =
    ≤-trans (≤-reflexive (∥1ᵐ∥≡0 {suc n + suc n} {suc n + suc n})) z≤n
  deg-prev {suc n} (suc h) =
    deg-⟪⟫ {n = suc n + suc n} {m = suc n + suc n} y[ aw {suc n} (inject₁ h) ]

  gadget-small : (g : Fin n) → All (Small n) (gadgetTerms g)
  gadget-small {n} g =
    (≤-trans (d∪ ⟪ y[ xw g ] ⟫ ⟪ y[ aw g ] ⟫ (dv y[ xw g ]) (dv y[ aw g ]))
             (n≤1+n 2) , refl) ∷
    (≤-trans (d∪ ⟪ y[ xw g ] ⟫ ⟪ x[ aw g ] ⟫ (dv y[ xw g ]) (dv x[ aw g ]))
             (n≤1+n 2) , refl) ∷
    (≤-trans (d∪ ⟪ y[ xw g ] ⟫ (prevMon g) (dv y[ xw g ]) (deg-prev g))
             (n≤1+n 2) , refl) ∷
    (d∪ (⟪ y[ xw g ] ⟫ ∪ᵐ prevMon g) ⟪ x[ xw g ] ⟫
        (d∪ ⟪ y[ xw g ] ⟫ (prevMon g) (dv y[ xw g ]) (deg-prev g))
        (dv x[ xw g ]) , refl) ∷
    []
    where
    dv : (v : Var (n + n) (n + n)) → ∥ ⟪ v ⟫ ∥ ≤ 1
    dv v = deg-⟪⟫ v

    d∪ : ∀ {i j} (a b : Mon (n + n) (n + n)) → ∥ a ∥ ≤ i → ∥ b ∥ ≤ j →
         ∥ a ∪ᵐ b ∥ ≤ i + j
    d∪ = deg-∪

  All-concatF : {A : Set} {P : A → Set} (f : Fin n → List A) →
                (∀ g → All P (f g)) → All P (concatF f)
  All-concatF {zero}  f h = []
  All-concatF {suc n} f h =
    AllP.++⁺ (h zero) (All-concatF (λ g → f (suc g)) (λ g → h (suc g)))

  Σˡ-∣ : {A : Set} {c : ℤ} (as : List A) (f : A → ℤ) →
         All (λ a → c ∣ f a) as → c ∣ Σˡ as f
  Σˡ-∣ []       f []       = i∣0
  Σˡ-∣ (a ∷ as) f (h ∷ hs) = ∣m∣n⇒∣m+n h (Σˡ-∣ as f hs)

  one≤ : ∀ s → s ≤ 3 → 1 ≤ 4 ∸ s
  one≤ zero                      _ = s≤s z≤n
  one≤ (suc zero)                _ = s≤s z≤n
  one≤ (suc (suc zero))          _ = s≤s z≤n
  one≤ (suc (suc (suc zero)))    _ = s≤s z≤n
  one≤ (suc (suc (suc (suc s)))) (s≤s (s≤s (s≤s ())))

  mono-cases : (δ γ : Mon n m) → (γ ≡ δ) ⊎ (monoᴾ δ γ ≡ 0ℤ)
  mono-cases δ γ with γ ≟ᵐ δ
  ... | yes γ≡δ = inj₁ γ≡δ
  ... | no  _   = inj₂ refl

ξ-order : (n : ℕ) → Ord≤ 3 (phase (ξ n))
ξ-order n γ = subst (pow (val 3 ∥ γ ∥) ∣_)
  (sym (⟦⟧ˢ-at (phaseTerms n) γ))
  (Σˡ-∣ (phaseTerms n) _
    (AllU.map each (All-concatF {n} gadgetTerms gadget-small)))
  where
  -- A coefficient ½ times 0 or 1, on a monomial of degree at most 3.
  each : ∀ {t} → Small n t →
         pow (val 3 ∥ γ ∥) ∣ (coeff (proj₂ t) *ℤ monoᴾ (proj₁ t) γ)
  each {δ , c} (dδ , refl) with ∥ γ ∥ ≤? 3
  ... | yes small = ∣m⇒∣m*n (monoᴾ δ γ)
          (subst (pow (val 3 ∥ γ ∥) ∣_) (sym coeff-½)
                 (pow-∣ (∸-monoʳ-≤ M (one≤ ∥ γ ∥ small))))
  ... | no  large with mono-cases δ γ
  ...   | inj₁ γ≡δ = contradiction (subst (λ ε → ∥ ε ∥ ≤ 3) (sym γ≡δ) dδ) large
  ...   | inj₂ e   = subst (pow (val 3 ∥ γ ∥) ∣_)
                       (sym (trans (cong (coeff ½ᵗ *ℤ_) e)
                                   (*-zeroʳ (coeff ½ᵗ))))
                       i∣0
