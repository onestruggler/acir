------------------------------------------------------------------------
-- Presentations of groups
--
-- The rewrite rules simulate the hidden shift algorithm, for every size
--
-- Section 5.2 of Amy's "Towards Large-scale Functional Verification of
-- Universal Quantum Circuits" (QPL 2018): "Our calculus further finds
-- the correct output |s⟩ ... even without providing the specification,
-- effectively simulating the algorithm."  PathSum.HiddenShift.
-- Simulation proves that every reduction of the hidden shift circuit
-- on |0⟩ which eliminates all its path variables ends at |x⟩ ↦ |s⟩
-- (hidden-shift-reduces); PathSum.HiddenShift.Example exhibits one such
-- reduction at m = 1.  This module proves that one exists for every
-- m, every g (any polynomial on m bits, read modulo 2) and every shift
-- s (hidden-shift-exists).  Together: the rules of figure 2, applied
-- without the specification, reduce the circuit on |0⟩ to a path-sum
-- with no path variables, and it is |x⟩ ↦ |s⟩ coefficient by
-- coefficient (hidden-shift-finds).
--
-- The same holds of the path-sum as the paper writes it.  Nothing below
-- reads the circuit's polynomials, only their values, so the reduction
-- applies to every path-sum over the circuit's 3n path variables whose
-- outputs are the last layer's path and whose phase is ½ hs-parity
-- modulo 1 (Written: the hypotheses of Simulation.at0-HS-congruent, of
-- which Example's written-out Ξ₁ is an instance at m = 1).  Every such
-- path-sum reduces completely (written-reduces), to |x⟩ ↦ |s⟩
-- coefficient by coefficient (written-finds); the circuit on |0⟩ is
-- one of them (written₀).
--
-- The chain.  The circuit's 3n path variables, n = 2m, are six blocks
-- a, b, c, d, e, h of m (PathSum.HiddenShift.Blocks), and the chain
-- makes three passes over the coordinates i < m:
--
--   pass 1: [HH] at b_i with d_i ← a_i ⊕ s_L,i, then [Elim] of d_i;
--   pass 2: [HH] at c_i with e_i ← s_L,i,       then [Elim] of e_i;
--   pass 3: [HH] at a_i with h_i ← s_R,i,       then [Elim] of h_i.
--
-- By construction that is 6m steps, 3m of each rule, taking the 3n path
-- variables and the normalisation 3n to none (the step count is not
-- stated as a theorem; the endpoint's type records the rest).  After
-- pass 1 the two terms of g cancel (d = a ⊕ s_L), which is why pass 3
-- can remove a; passes 2 and 3 set the outputs e and h to s_L and s_R.
-- Every rule acts at a variable in the middle of the list, through
-- PathSum.Full's renumbering (a step is `at j (plain (hhᴳ …))` followed
-- by `elimAtᶠ`), and the quotients are the lifts of a_i ⊕ s_L,i and of
-- constants, which are Boolean-valued and linear.
--
-- How it is built.  The circuit is a composite of five path-sums
-- (definition 2.6), whose polynomials do not compute, so no premise
-- is checked on coefficients: each is proved from values by Möbius
-- inversion (PathSum.HiddenShift.Track).  A stage of the reduction of a
-- written path-sum ξ₀ (module Reduce) is a State: the current
-- path-sum, a chain to it from ξ₀, a label (block and coordinate) for
-- each of its path variables,
-- and a map ρ from its paths to the circuit's, read by label, such that
-- its phase is ½ Fblk (ρ y) modulo 1 and its outputs are Gblk (ρ y)
-- modulo 2 (Fblk is the circuit's parity in block form).  ρ reads a
-- present label off the path (reads) and gives a removed one the value
-- the rules fixed for it (dflts); every present label has a position
-- (find), found through the labels rather than computed, and only
-- present labels have one (only, inj).  A step locates its variables,
-- proves the [HH]'s premise from the derivative of Fblk under the flip
-- of the eliminated variable (Blocks' ∂-b, ∂-c, ∂-a), applies
-- Track.hh-elim, and re-establishes the invariants for the smaller
-- path-sum (Advance).  A pass sweeps the coordinates (Sweep); the
-- stages between passes agree (Blocks' Ret₁₂, Ret₂₃); and at the end no
-- label is present, so the path-sum has no path variables (finish).
-- That the endpoint is |x⟩ ↦ |s⟩ is not re-proved along the way: it
-- follows from soundness of the rules (PathSum.Full.Sound) and
-- Simulation.spec-only-if.
--
-- What is not proved here.  The chain is given, not found: that the
-- automatic search PathSum.Full.Match.normal-formᶠ ends without path
-- variables is not shown (by hidden-shift-reduces, wherever any
-- complete search ends, it ends at |s⟩).  The circuits of figure 3
-- (PathSum.HiddenShift.Circuit and Symbolic) are other path-sums --
-- definition 2.9's, with X = H R₁ H adding path variables in figure
-- 3(a), and in figure 3(b) a phase that reads the symbolic shift
-- register -- whose complete reductions are constructed in
-- PathSum.HiddenShift.ExistsCircuit and ExistsSymbolic, by the same
-- passes run on a machine for any labels and input-dependent values.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Exists (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _xor_)
open import Data.Bool.Properties using (xor-comm; xor-assoc; xor-same)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using
  (Fin; zero; suc; punchIn; punchOut; splitAt; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using
  (punchIn-injective; punchInᵢ≢i; punchIn-punchOut; splitAt-↑ˡ;
   splitAt-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.Integer.Base using (_-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.List.Base using (List; []; _∷_; allFin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-allFin)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using ([_,_]′; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)

import Data.Fin.Properties as Fin

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-self)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Congruence M₀ using (Congruent; ≈-≋)
open import PathSum.Denotation M₀ using
  (Assign; outBit; _≋_; ≋-sym; ≋-trans)
open import PathSum.Full.Sound M₀ using (⟶ᶠ*-sound)
open import PathSum.HiddenShift M₀ using
  (HS; hs-norm; specᴾ; boolᴾ; boolᴾ-resp)
open import PathSum.HiddenShift.Blocks
open import PathSum.HiddenShift.Simulation M₀ using
  (at0; eval-at0; hs-parity; layer₁; layer₂; layer₃; phase-HS; outBit-HS;
   hidden-shift-≋; at0-HS-congruent; spec-only-if; hidden-shift-reduces)
open import PathSum.HiddenShift.Track M₀ using (Tracks; hh-elim)
open import PathSum.HiddenShift.Walsh using
  (0ᵃ; _⊕ᵃ_; lhalf; rhalf; dot; dot-cong; dot-0ˡ; dot-⧺; ⧺-split; mm;
   dual)
open import PathSum.Polynomial using (Poly; y[_]; eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Boolean using
  (var; lit; _⊕ᵉ_; liftᵉ; eval-liftᵉ; Absent-liftᵉ)
open import PathSum.Reorder using
  (insertᵃ; insertᵃ-here; insertᵃ-punchIn; front)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Full M using (_⟶ᶠ*_; εᶠ; _◅◅ᶠ_)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½; elim-reduct)
open import PathSum.Reduction.General M using (hhᴳ-reduct)

private
  variable
    k : ℕ


------------------------------------------------------------------------
-- Small facts

private
  fin0 : Fin 0 → ⊥
  fin0 ()

  t≢f : true ≢ false
  t≢f ()

  y-inj : ∀ {n k} {i j : Fin k} → y[_] {n} {k} i ≡ y[ j ] → i ≡ j
  y-inj refl = refl

  -- Labels in different blocks, or at different coordinates, differ.

  blk≢ : ∀ {m} {b b′ : Blk} {i i′ : Fin m} → b ≢ b′ → (b , i) ≢ (b′ , i′)
  blk≢ ne e = ne (cong proj₁ e)

  crd≢ : ∀ {m} {b : Blk} {i i′ : Fin m} → i ≢ i′ → (b , i) ≢ (b , i′)
  crd≢ ne e = ne (cong proj₂ e)

  -- Setting y_j to either bit leaves the other positions alone.

  insertᵃ-off : ∀ (j p : Fin (suc k)) → j ≢ p → (c c′ : Bool)
                (y : Assign k) → insertᵃ j c y p ≡ insertᵃ j c′ y p
  insertᵃ-off j p j≢p c c′ y = trans
    (cong (insertᵃ j c y) (sym (punchIn-punchOut j≢p)))
    (trans (insertᵃ-punchIn j c y (punchOut j≢p))
      (sym (trans (cong (insertᵃ j c′ y) (sym (punchIn-punchOut j≢p)))
                  (insertᵃ-punchIn j c′ y (punchOut j≢p)))))

  -- a ⊕ (a ⊕ b) is b.

  xor-cancelˡ : ∀ a b → a xor (a xor b) ≡ b
  xor-cancelˡ a b = trans (sym (xor-assoc a a b)) (cong (_xor b) (xor-same a))


------------------------------------------------------------------------
-- The circuit's path variables, labelled

-- A path of the circuit is its three Hadamard layers' paths, of n bits
-- each (Simulation's layer₁, layer₂, layer₃); the first half of each
-- layer is the block a, c or e, the second b, d or h.

private
  pos₁ pos₂ pos₃ : ∀ n → Fin n → Fin (hs-norm n)
  pos₁ n i = (((i ↑ˡ 0) ↑ˡ n) ↑ˡ 0) ↑ˡ n
  pos₂ n i = (((n ℕ+ 0) ↑ʳ i) ↑ˡ 0) ↑ˡ n
  pos₃ n i = (((n ℕ+ 0) ℕ+ n) ℕ+ 0) ↑ʳ i

  from0 : ∀ {A : Set} → Fin 0 → A
  from0 ()

-- The position of each label.

pos₀ : ∀ m → Lbl m → Fin (hs-norm (m ℕ+ m))
pos₀ m (A₁ , i) = pos₁ (m ℕ+ m) (i ↑ˡ m)
pos₀ m (B₁ , i) = pos₁ (m ℕ+ m) (m ↑ʳ i)
pos₀ m (C₂ , i) = pos₂ (m ℕ+ m) (i ↑ˡ m)
pos₀ m (D₂ , i) = pos₂ (m ℕ+ m) (m ↑ʳ i)
pos₀ m (E₃ , i) = pos₃ (m ℕ+ m) (i ↑ˡ m)
pos₀ m (H₃ , i) = pos₃ (m ℕ+ m) (m ↑ʳ i)

-- The label of each position.

private
  halves : ∀ m → Blk → Blk → Fin (m ℕ+ m) → Lbl m
  halves m b b′ i = [ (λ k → b , k) , (λ k → b′ , k) ]′ (splitAt m i)

  lab₁ : ∀ m → Fin ((m ℕ+ m) ℕ+ 0) → Lbl m
  lab₁ m t = [ halves m A₁ B₁ , from0 ]′ (splitAt (m ℕ+ m) t)

  lab₂ : ∀ m → Fin (((m ℕ+ m) ℕ+ 0) ℕ+ (m ℕ+ m)) → Lbl m
  lab₂ m t = [ lab₁ m , halves m C₂ D₂ ]′ (splitAt ((m ℕ+ m) ℕ+ 0) t)

  lab₃ : ∀ m → Fin ((((m ℕ+ m) ℕ+ 0) ℕ+ (m ℕ+ m)) ℕ+ 0) → Lbl m
  lab₃ m t = [ lab₂ m , from0 ]′ (splitAt (((m ℕ+ m) ℕ+ 0) ℕ+ (m ℕ+ m)) t)

lab₀ : ∀ m → Fin (hs-norm (m ℕ+ m)) → Lbl m
lab₀ m t =
  [ lab₃ m , halves m E₃ H₃ ]′
  (splitAt ((((m ℕ+ m) ℕ+ 0) ℕ+ (m ℕ+ m)) ℕ+ 0) t)

-- They are inverse.

private
  sel-ˡ : ∀ a b {X : Set} (f : Fin a → X) (g : Fin b → X) (i : Fin a) →
          [ f , g ]′ (splitAt a (i ↑ˡ b)) ≡ f i
  sel-ˡ a b f g i = cong [ f , g ]′ (splitAt-↑ˡ a i b)

  sel-ʳ : ∀ a b {X : Set} (f : Fin a → X) (g : Fin b → X) (i : Fin b) →
          [ f , g ]′ (splitAt a (a ↑ʳ i)) ≡ g i
  sel-ʳ a b f g i = cong [ f , g ]′ (splitAt-↑ʳ a b i)

  split-inv : ∀ a b {c} {X : Set} (f : Fin a → X) (g : Fin b → X)
              (h : X → Fin c) (e : Fin (a ℕ+ b) → Fin c) →
              (∀ i → h (f i) ≡ e (i ↑ˡ b)) → (∀ i → h (g i) ≡ e (a ↑ʳ i)) →
              ∀ t → h ([ f , g ]′ (splitAt a t)) ≡ e t
  split-inv a b f g h e hf hg t = go (splitAt a t) refl
    where
    go : ∀ r → splitAt a t ≡ r → h ([ f , g ]′ r) ≡ e t
    go (inj₁ i) eq = trans (hf i) (cong e (splitAt⁻¹-↑ˡ eq))
    go (inj₂ i) eq = trans (hg i) (cong e (splitAt⁻¹-↑ʳ eq))

lab₀-pos₀ : ∀ m ℓ → lab₀ m (pos₀ m ℓ) ≡ ℓ
lab₀-pos₀ m (A₁ , i) = trans (layer-a (i ↑ˡ m)) (sel-ˡ m m _ _ i)
  where
  n = m ℕ+ m
  layer-a : ∀ t → lab₀ m (pos₁ n t) ≡ halves m A₁ B₁ t
  layer-a t = trans
    (sel-ˡ (((n ℕ+ 0) ℕ+ n) ℕ+ 0) n (lab₃ m) (halves m E₃ H₃)
           (((t ↑ˡ 0) ↑ˡ n) ↑ˡ 0))
    (trans (sel-ˡ ((n ℕ+ 0) ℕ+ n) 0 (lab₂ m) from0 ((t ↑ˡ 0) ↑ˡ n))
      (trans (sel-ˡ (n ℕ+ 0) n (lab₁ m) (halves m C₂ D₂) (t ↑ˡ 0))
             (sel-ˡ n 0 (halves m A₁ B₁) from0 t)))
lab₀-pos₀ m (B₁ , i) = trans (layer-a (m ↑ʳ i)) (sel-ʳ m m _ _ i)
  where
  n = m ℕ+ m
  layer-a : ∀ t → lab₀ m (pos₁ n t) ≡ halves m A₁ B₁ t
  layer-a t = trans
    (sel-ˡ (((n ℕ+ 0) ℕ+ n) ℕ+ 0) n (lab₃ m) (halves m E₃ H₃)
           (((t ↑ˡ 0) ↑ˡ n) ↑ˡ 0))
    (trans (sel-ˡ ((n ℕ+ 0) ℕ+ n) 0 (lab₂ m) from0 ((t ↑ˡ 0) ↑ˡ n))
      (trans (sel-ˡ (n ℕ+ 0) n (lab₁ m) (halves m C₂ D₂) (t ↑ˡ 0))
             (sel-ˡ n 0 (halves m A₁ B₁) from0 t)))
lab₀-pos₀ m (C₂ , i) = trans (layer-c (i ↑ˡ m)) (sel-ˡ m m _ _ i)
  where
  n = m ℕ+ m
  layer-c : ∀ t → lab₀ m (pos₂ n t) ≡ halves m C₂ D₂ t
  layer-c t = trans
    (sel-ˡ (((n ℕ+ 0) ℕ+ n) ℕ+ 0) n (lab₃ m) (halves m E₃ H₃)
           (((n ℕ+ 0) ↑ʳ t) ↑ˡ 0))
    (trans (sel-ˡ ((n ℕ+ 0) ℕ+ n) 0 (lab₂ m) from0 ((n ℕ+ 0) ↑ʳ t))
           (sel-ʳ (n ℕ+ 0) n (lab₁ m) (halves m C₂ D₂) t))
lab₀-pos₀ m (D₂ , i) = trans (layer-c (m ↑ʳ i)) (sel-ʳ m m _ _ i)
  where
  n = m ℕ+ m
  layer-c : ∀ t → lab₀ m (pos₂ n t) ≡ halves m C₂ D₂ t
  layer-c t = trans
    (sel-ˡ (((n ℕ+ 0) ℕ+ n) ℕ+ 0) n (lab₃ m) (halves m E₃ H₃)
           (((n ℕ+ 0) ↑ʳ t) ↑ˡ 0))
    (trans (sel-ˡ ((n ℕ+ 0) ℕ+ n) 0 (lab₂ m) from0 ((n ℕ+ 0) ↑ʳ t))
           (sel-ʳ (n ℕ+ 0) n (lab₁ m) (halves m C₂ D₂) t))
lab₀-pos₀ m (E₃ , i) =
  trans (sel-ʳ ((((m ℕ+ m) ℕ+ 0) ℕ+ (m ℕ+ m)) ℕ+ 0) (m ℕ+ m) (lab₃ m)
               (halves m E₃ H₃) (i ↑ˡ m))
        (sel-ˡ m m _ _ i)
lab₀-pos₀ m (H₃ , i) =
  trans (sel-ʳ ((((m ℕ+ m) ℕ+ 0) ℕ+ (m ℕ+ m)) ℕ+ 0) (m ℕ+ m) (lab₃ m)
               (halves m E₃ H₃) (m ↑ʳ i))
        (sel-ʳ m m _ _ i)

pos₀-lab₀ : ∀ m t → pos₀ m (lab₀ m t) ≡ t
pos₀-lab₀ m = split-inv (((n ℕ+ 0) ℕ+ n) ℕ+ 0) n (lab₃ m) (halves m E₃ H₃)
                        (pos₀ m) (λ t → t) inner₃ half₃
  where
  n = m ℕ+ m

  half₁ : ∀ i → pos₀ m (halves m A₁ B₁ i) ≡ pos₁ n i
  half₁ = split-inv m m (λ k → A₁ , k) (λ k → B₁ , k) (pos₀ m) (pos₁ n)
                    (λ _ → refl) (λ _ → refl)

  half₂ : ∀ i → pos₀ m (halves m C₂ D₂ i) ≡ pos₂ n i
  half₂ = split-inv m m (λ k → C₂ , k) (λ k → D₂ , k) (pos₀ m) (pos₂ n)
                    (λ _ → refl) (λ _ → refl)

  half₃ : ∀ i → pos₀ m (halves m E₃ H₃ i) ≡ pos₃ n i
  half₃ = split-inv m m (λ k → E₃ , k) (λ k → H₃ , k) (pos₀ m) (pos₃ n)
                    (λ _ → refl) (λ _ → refl)

  inner₁ : ∀ i → pos₀ m (lab₁ m i) ≡ ((i ↑ˡ n) ↑ˡ 0) ↑ˡ n
  inner₁ = split-inv n 0 (halves m A₁ B₁) from0 (pos₀ m)
                     (λ t → ((t ↑ˡ n) ↑ˡ 0) ↑ˡ n) half₁ (λ ())

  inner₂ : ∀ i → pos₀ m (lab₂ m i) ≡ (i ↑ˡ 0) ↑ˡ n
  inner₂ = split-inv (n ℕ+ 0) n (lab₁ m) (halves m C₂ D₂) (pos₀ m)
                     (λ t → (t ↑ˡ 0) ↑ˡ n) inner₁ half₂

  inner₃ : ∀ i → pos₀ m (lab₃ m i) ≡ i ↑ˡ n
  inner₃ = split-inv ((n ℕ+ 0) ℕ+ n) 0 (lab₂ m) from0 (pos₀ m)
                     (λ t → t ↑ˡ n) inner₂ (λ ())


------------------------------------------------------------------------
-- Sweeping the coordinates

-- A property of the sets of coordinates done that respects pointwise
-- equality and survives doing one more coordinate holds once all are
-- done if it held when none were.  The coordinates are visited in the
-- order of allFin; one already done is skipped.

module Sweep {m : ℕ} (S : (Fin m → Bool) → Set)
             (resp : ∀ {d d′} → (∀ i → d i ≡ d′ i) → S d → S d′)
             (step : ∀ d i → d i ≡ false → S d → S (d [ i ≔ true ]))
             where

  private
    mark : List (Fin m) → (Fin m → Bool) → Fin m → Bool
    mark []       d = d
    mark (x ∷ xs) d = mark xs (d [ x ≔ true ])

    step′ : ∀ d x → S d → S (d [ x ≔ true ])
    step′ d x s = go (d x) refl
      where
      go : ∀ b → d x ≡ b → S (d [ x ≔ true ])
      go false e = step d x e s
      go true  e = resp {d = d} {d′ = d [ x ≔ true ]} (λ i → sym (trans
        (cong (λ b → (d [ x ≔ b ]) i) (sym e)) (≔-self d x i))) s

    run : ∀ xs d → S d → S (mark xs d)
    run []       d s = s
    run (x ∷ xs) d s = run xs (d [ x ≔ true ]) (step′ d x s)

    set : ∀ (d : Fin m → Bool) x i → i ≡ x → (d [ x ≔ true ]) i ≡ true
    set d x i i≡x = trans (cong (d [ x ≔ true ]) i≡x) (≔-here d x true)

    mark-true : ∀ xs d i → d i ≡ true → mark xs d i ≡ true
    mark-true []       d i e = e
    mark-true (x ∷ xs) d i e =
      mark-true xs (d [ x ≔ true ]) i (go (i Fin.≟ x))
      where
      go : Dec (i ≡ x) → (d [ x ≔ true ]) i ≡ true
      go (yes i≡x) = set d x i i≡x
      go (no  i≢x) = trans (≔-there d true i≢x) e

    mark-∈ : ∀ xs d i → i ∈ xs → mark xs d i ≡ true
    mark-∈ (x ∷ xs) d i (here i≡x) =
      mark-true xs (d [ x ≔ true ]) i (set d x i i≡x)
    mark-∈ (x ∷ xs) d i (there p) = mark-∈ xs (d [ x ≔ true ]) i p

  all : S (λ _ → false) → S (λ _ → true)
  all s = resp {d = mark (allFin m) (λ _ → false)} {d′ = λ _ → true}
               (λ i → mark-∈ (allFin m) (λ _ → false) i (∈-allFin i))
               (run (allFin m) (λ _ → false) s)


------------------------------------------------------------------------
-- The reduction, for one g and s

module _ {m : ℕ} (g : Poly m 0) (s : Assign (m ℕ+ m)) where

  private
    sL sR : Assign m
    sL = lhalf {m} s
    sR = rhalf {m} s

  open Phase (boolᴾ g) (boolᴾ-resp g) sL sR

  -- The circuit's path, read by label.

  ρ₀ : Assign (hs-norm (m ℕ+ m)) → LAssign m
  ρ₀ Y ℓ = Y (pos₀ m ℓ)

  private
    dot-halves : (u v : Assign (m ℕ+ m)) →
                 dot u v ≡ dot (lhalf {m} u) (lhalf {m} v) xor
                           dot (rhalf {m} u) (rhalf {m} v)
    dot-halves u v = trans
      (dot-cong (λ j → sym (⧺-split m m u j)) (λ j → sym (⧺-split m m v j)))
      (dot-⧺ (lhalf {m} u) (lhalf {m} v) (rhalf {m} u) (rhalf {m} v))

  -- The parity of the circuit's phase on |0⟩ is Fblk of its path, and
  -- its outputs are Gblk.

  parity-blocks : ∀ Y → hs-parity g s 0ᵃ Y ≡ Fblk (ρ₀ Y)
  parity-blocks Y = trans
    (cong₂ (λ p q → ((p xor q) xor dual (boolᴾ g) y₂) xor dot y₂ y₃)
           (cong (_xor mm (boolᴾ g) (y₁ ⊕ᵃ s)) (dot-0ˡ y₁))
           (dot-halves y₁ y₂))
    (cong (λ q → ((mm (boolᴾ g) (y₁ ⊕ᵃ s) xor
                   (dot (lhalf {m} y₁) (lhalf {m} y₂) xor
                    dot (rhalf {m} y₁) (rhalf {m} y₂))) xor
                  dual (boolᴾ g) y₂) xor q)
          (dot-halves y₂ y₃))
    where
    y₁ y₂ y₃ : Assign (m ℕ+ m)
    y₁ = layer₁ (m ℕ+ m) Y
    y₂ = layer₂ (m ℕ+ m) Y
    y₃ = layer₃ (m ℕ+ m) Y

  out-blocks : ∀ Y w → layer₃ (m ℕ+ m) Y w ≡ Gblk w (ρ₀ Y)
  out-blocks Y w = go (splitAt m w) refl
    where
    go : ∀ r → splitAt m w ≡ r →
         layer₃ (m ℕ+ m) Y w ≡ [ ρ₀ Y ‹ E₃ › , ρ₀ Y ‹ H₃ › ]′ r
    go (inj₁ i) eq = cong (λ t → Y (pos₃ (m ℕ+ m) t)) (sym (splitAt⁻¹-↑ˡ eq))
    go (inj₂ i) eq = cong (λ t → Y (pos₃ (m ℕ+ m) t)) (sym (splitAt⁻¹-↑ʳ eq))

  -- A path-sum written as the paper writes the circuit's: its outputs
  -- are the last layer's path and its phase is ½ hs-parity modulo 1,
  -- the hypotheses of Simulation.at0-HS-congruent, over the circuit's
  -- 3n path variables and normalisation.  The circuit on |0⟩ is one
  -- (written₀); so is every written-out polynomial form of it, as
  -- PathSum.HiddenShift.Example's Ξ₁ at m = 1.

  Written : PathSum (m ℕ+ m) (hs-norm (m ℕ+ m)) (hs-norm (m ℕ+ m)) → Set
  Written ξ₀ =
    (∀ x Y w → outBit ξ₀ x Y w ≡ layer₃ (m ℕ+ m) Y w) ×
    (∀ x Y → pow M ∣ (eval (phase ξ₀) x Y - ½ * [ hs-parity g s 0ᵃ Y ]ᶻ))

  written₀ : Written (at0 (HS g s))
  written₀ =
    (λ x Y w → trans (cong odd (eval-at0 (out (HS g s) w) x Y))
                     (outBit-HS g s 0ᵃ Y w)) ,
    (λ x Y → subst (λ t → pow M ∣ (t - ½ * [ hs-parity g s 0ᵃ Y ]ᶻ))
                   (sym (eval-at0 (phase (HS g s)) x Y))
                   (phase-HS g s 0ᵃ Y))

  -- Such a path-sum is known by these values.

  written-tracks : ∀ ξ₀ → Written ξ₀ →
                   Tracks ξ₀ (λ Y → Fblk (ρ₀ Y)) (λ w Y → Gblk w (ρ₀ Y))
  written-tracks ξ₀ (outs , phs) = record
    { phase-at = λ x Y →
        subst (λ b → pow M ∣ (eval (phase ξ₀) x Y - ½ * [ b ]ᶻ))
              (parity-blocks Y) (phs x Y)
    ; out-at = λ w x Y → trans (outs x Y w) (out-blocks Y w)
    }

  tracks₀ : Tracks (at0 (HS g s)) (λ Y → Fblk (ρ₀ Y)) (λ w Y → Gblk w (ρ₀ Y))
  tracks₀ = written-tracks (at0 (HS g s)) written₀

  ----------------------------------------------------------------------
  -- Locating variables

  private
    -- A present label other than v is at a position other than v's.

    locate : ∀ {Ret : Lbl m → Bool} {k} (lab : Fin (suc k) → Lbl m) →
             (∀ ℓ → Ret ℓ ≡ true → Σ (Fin (suc k)) (λ p → lab p ≡ ℓ)) →
             ∀ {v} (j : Fin (suc k)) → lab j ≡ v →
             ∀ u → Ret u ≡ true → u ≢ v →
             Σ (Fin k) (λ i → lab (punchIn j i) ≡ u)
    locate lab fd j lj u Ru u≢v =
      punchOut j≢p , trans (cong lab (punchIn-punchOut j≢p)) (proj₂ (fd u Ru))
      where
      j≢p : j ≢ proj₁ (fd u Ru)
      j≢p e = u≢v (trans (sym (proj₂ (fd u Ru)))
                         (trans (cong lab (sym e)) lj))

    -- Two present labels do not fit in one path variable.

    one-slot : ∀ {Ret : Lbl m → Bool} (lab : Fin 1 → Lbl m) →
               (∀ ℓ → Ret ℓ ≡ true → Σ (Fin 1) (λ p → lab p ≡ ℓ)) →
               ∀ v u → Ret v ≡ true → Ret u ≡ true → v ≢ u → ⊥
    one-slot lab fd v u Rv Ru v≢u with fd v Rv | fd u Ru
    ... | zero , lv | zero , lu = v≢u (trans (sym lv) lu)

  ----------------------------------------------------------------------
  -- The path-sum with y_j set, read by label

  -- A present label other than v keeps its value when y_j, which is v,
  -- flips; v takes the value of y_j; a removed label keeps its fixed
  -- value.

  private
    module Flip {Ret : Lbl m → Bool} {k : ℕ}
                (lab : Fin (suc k) → Lbl m) (ρ : Assign (suc k) → LAssign m)
                (rd : ∀ y p → ρ y (lab p) ≡ y p)
                (df : ∀ y ℓ → Ret ℓ ≡ false → ρ y ℓ ≡ dflt ℓ (ρ y))
                (fd : ∀ ℓ → Ret ℓ ≡ true → Σ (Fin (suc k)) (λ p → lab p ≡ ℓ))
                (j : Fin (suc k)) {v : Lbl m} (lj : lab j ≡ v) where

      Zᶜ : Bool → Assign k → LAssign m
      Zᶜ c y = ρ (insertᵃ j c y)

      self : ∀ c y → Zᶜ c y v ≡ c
      self c y = trans (cong (Zᶜ c y) (sym lj))
                       (trans (rd (insertᵃ j c y) j) (insertᵃ-here j c y))

      flipped : ∀ y → Zᶜ true y v xor Zᶜ false y v ≡ true
      flipped y = cong₂ _xor_ (self true y) (self false y)

      read : ∀ y (p : Fin k) {ℓ} → lab (punchIn j p) ≡ ℓ → Zᶜ false y ℓ ≡ y p
      read y p lp = trans (cong (Zᶜ false y) (sym lp))
        (trans (rd (insertᵃ j false y) (punchIn j p))
               (insertᵃ-punchIn j false y p))

      kept : ∀ y ℓ → Ret ℓ ≡ true → ℓ ≢ v → Zᶜ true y ℓ ≡ Zᶜ false y ℓ
      kept y ℓ R ℓ≢v = trans (cong (Zᶜ true y) (sym (proj₂ (fd ℓ R))))
        (trans (rd (insertᵃ j true y) (proj₁ (fd ℓ R)))
          (trans (insertᵃ-off j (proj₁ (fd ℓ R)) j≢p true false y)
            (trans (sym (rd (insertᵃ j false y) (proj₁ (fd ℓ R))))
                   (cong (Zᶜ false y) (proj₂ (fd ℓ R))))))
        where
        j≢p : j ≢ proj₁ (fd ℓ R)
        j≢p e = ℓ≢v (trans (sym (proj₂ (fd ℓ R)))
                           (trans (cong lab (sym e)) lj))

      dfl : ∀ c y ℓ → Ret ℓ ≡ false → Zᶜ c y ℓ ≡ dflt ℓ (Zᶜ c y)
      dfl c y ℓ R = df (insertᵃ j c y) ℓ R

      -- A removed label whose fixed value is the same at both paths.

      fixed : ∀ y ℓ → Ret ℓ ≡ false →
              dflt ℓ (Zᶜ true y) ≡ dflt ℓ (Zᶜ false y) →
              Zᶜ true y ℓ ≡ Zᶜ false y ℓ
      fixed y ℓ R e = trans (dfl true y ℓ R) (trans e (sym (dfl false y ℓ R)))

  ----------------------------------------------------------------------
  -- One [HH] and one [Elim]: the new invariants

  -- After [HH] at y_j (label v) with y_i ← q and [Elim] of y_i (label
  -- u), the path-sum's paths are read at y_j = 0, y_i = q; v and u are
  -- removed, with the values the rules fixed.

  private
    module Advance {Ret Ret′ : Lbl m → Bool} {k : ℕ}
      (lab : Fin (suc (suc k)) → Lbl m) (ρ : Assign (suc (suc k)) → LAssign m)
      (rd : ∀ y p → ρ y (lab p) ≡ y p)
      (df : ∀ y ℓ → Ret ℓ ≡ false → ρ y ℓ ≡ dflt ℓ (ρ y))
      (fd : ∀ ℓ → Ret ℓ ≡ true → Σ (Fin (suc (suc k))) (λ p → lab p ≡ ℓ))
      (on : ∀ p → Ret (lab p) ≡ true)
      (ij : ∀ p q → lab p ≡ lab q → p ≡ q)
      (j : Fin (suc (suc k))) (i : Fin (suc k)) (q : Assign (suc k) → Bool)
      {v u : Lbl m} (lj : lab j ≡ v) (li : lab (punchIn j i) ≡ u)
      (dv : ∀ Z → dflt v Z ≡ false)
      (du : ∀ y → dflt u (ρ (insertᵃ j false
                    (insertᵃ i false y [ i ≔ q (insertᵃ i false y) ]))) ≡
                  q (insertᵃ i false y))
      (Rv : Ret′ v ≡ false) (Ru : Ret′ u ≡ false)
      (R′ : ∀ ℓ → ℓ ≢ v → ℓ ≢ u → Ret′ ℓ ≡ Ret ℓ)
      where

      σ : Assign k → Assign (suc (suc k))
      σ y = insertᵃ j false (insertᵃ i false y [ i ≔ q (insertᵃ i false y) ])

      lab″ : Fin k → Lbl m
      lab″ p = lab (punchIn j (punchIn i p))

      ρ″ : Assign k → LAssign m
      ρ″ y = ρ (σ y)

      reads″ : ∀ y p → ρ″ y (lab″ p) ≡ y p
      reads″ y p = trans (rd (σ y) (punchIn j (punchIn i p)))
        (trans (insertᵃ-punchIn j false
                  (insertᵃ i false y [ i ≔ q (insertᵃ i false y) ])
                  (punchIn i p))
          (trans (≔-there (insertᵃ i false y) (q (insertᵃ i false y))
                          (punchInᵢ≢i i p))
                 (insertᵃ-punchIn i false y p)))

      dflts″ : ∀ y ℓ → Ret′ ℓ ≡ false → ρ″ y ℓ ≡ dflt ℓ (ρ″ y)
      dflts″ y ℓ R = go (ℓ ≟ˡ v) (ℓ ≟ˡ u)
        where
        go : Dec (ℓ ≡ v) → Dec (ℓ ≡ u) → ρ″ y ℓ ≡ dflt ℓ (ρ″ y)
        go (yes e) _ = trans (cong (ρ″ y) (trans e (sym lj)))
          (trans (rd (σ y) j)
            (trans (insertᵃ-here j false
                     (insertᵃ i false y [ i ≔ q (insertᵃ i false y) ]))
                   (sym (trans (cong (λ t → dflt t (ρ″ y)) e) (dv (ρ″ y))))))
        go (no _) (yes e) = trans (cong (ρ″ y) (trans e (sym li)))
          (trans (rd (σ y) (punchIn j i))
            (trans (insertᵃ-punchIn j false
                     (insertᵃ i false y [ i ≔ q (insertᵃ i false y) ]) i)
              (trans (≔-here (insertᵃ i false y) i (q (insertᵃ i false y)))
                     (sym (trans (cong (λ t → dflt t (ρ″ y)) e) (du y))))))
        go (no ℓ≢v) (no ℓ≢u) = df (σ y) ℓ (trans (sym (R′ ℓ ℓ≢v ℓ≢u)) R)

      find″ : ∀ ℓ → Ret′ ℓ ≡ true → Σ (Fin k) (λ p → lab″ p ≡ ℓ)
      find″ ℓ R =
        punchOut i≢p₁ ,
        trans (cong (λ t → lab (punchIn j t)) (punchIn-punchOut i≢p₁))
              (trans (cong lab (punchIn-punchOut j≢p)) (proj₂ found))
        where
        ℓ≢v : ℓ ≢ v
        ℓ≢v e = t≢f (trans (sym R) (trans (cong Ret′ e) Rv))

        ℓ≢u : ℓ ≢ u
        ℓ≢u e = t≢f (trans (sym R) (trans (cong Ret′ e) Ru))

        found : Σ (Fin (suc (suc k))) (λ p → lab p ≡ ℓ)
        found = fd ℓ (trans (sym (R′ ℓ ℓ≢v ℓ≢u)) R)

        j≢p : j ≢ proj₁ found
        j≢p e = ℓ≢v (trans (sym (proj₂ found)) (trans (cong lab (sym e)) lj))

        i≢p₁ : i ≢ punchOut j≢p
        i≢p₁ e = ℓ≢u (trans (sym (proj₂ found))
          (trans (cong lab (sym (punchIn-punchOut j≢p)))
                 (trans (cong (λ t → lab (punchIn j t)) (sym e)) li)))

      only″ : ∀ p → Ret′ (lab″ p) ≡ true
      only″ p = trans (R′ (lab″ p) ≢v ≢u) (on (punchIn j (punchIn i p)))
        where
        ≢v : lab″ p ≢ v
        ≢v e = punchInᵢ≢i j (punchIn i p) (ij _ _ (trans e (sym lj)))

        ≢u : lab″ p ≢ u
        ≢u e = punchInᵢ≢i i p
          (punchIn-injective j (punchIn i p) i (ij _ _ (trans e (sym li))))

      inj″ : ∀ p p′ → lab″ p ≡ lab″ p′ → p ≡ p′
      inj″ p p′ e = punchIn-injective i p p′
        (punchIn-injective j (punchIn i p) (punchIn i p′) (ij _ _ e))

  ----------------------------------------------------------------------
  -- The reduction of a written path-sum

  -- Everything below is about one path-sum ξ₀ with the circuit's
  -- values, known through tr₀.

  module Reduce
    (ξ₀ : PathSum (m ℕ+ m) (hs-norm (m ℕ+ m)) (hs-norm (m ℕ+ m)))
    (tr₀ : Tracks ξ₀ (λ Y → Fblk (ρ₀ Y)) (λ w Y → Gblk w (ρ₀ Y)))
    where

    --------------------------------------------------------------------
    -- A stage of the reduction

    -- Ret says which labels are still path variables.

    record State (Ret : Lbl m → Bool) : Set where
      constructor stage
      field
        size   : ℕ
        ξ      : PathSum (m ℕ+ m) size size
        lab    : Fin size → Lbl m
        ρ      : Assign size → LAssign m
        chain  : ξ₀ ⟶ᶠ* ξ
        tracks : Tracks ξ (λ y → Fblk (ρ y)) (λ w y → Gblk w (ρ y))
        reads  : ∀ y p → ρ y (lab p) ≡ y p
        dflts  : ∀ y ℓ → Ret ℓ ≡ false → ρ y ℓ ≡ dflt ℓ (ρ y)
        find   : ∀ ℓ → Ret ℓ ≡ true → Σ (Fin size) (λ p → lab p ≡ ℓ)
        only   : ∀ p → Ret (lab p) ≡ true
        inj    : ∀ p q → lab p ≡ lab q → p ≡ q

    State-resp : ∀ {Ret Ret′} → (∀ ℓ → Ret ℓ ≡ Ret′ ℓ) →
                 State Ret → State Ret′
    State-resp h (stage sz ξ lab ρ ch tr rd df fd on ij) =
      stage sz ξ lab ρ ch tr rd (λ y ℓ R → df y ℓ (trans (h ℓ) R))
            (λ ℓ R → fd ℓ (trans (h ℓ) R))
            (λ p → trans (sym (h (lab p))) (on p)) ij

    -- ξ₀, every label present.

    initial : State (Ret₁ (λ _ → false))
    initial = stage (hs-norm (m ℕ+ m)) ξ₀ (lab₀ m) ρ₀ εᶠ tr₀
      (λ Y p → cong Y (pos₀-lab₀ m p))
      (λ Y ℓ R → ⊥-elim (t≢f (trans (sym (Ret₁-all ℓ)) R)))
      (λ ℓ _ → pos₀ m ℓ , lab₀-pos₀ m ℓ)
      (λ p → Ret₁-all (lab₀ m p))
      (λ p q e → trans (sym (pos₀-lab₀ m p))
                       (trans (cong (pos₀ m) e) (pos₀-lab₀ m q)))

    -- No label present: no path variable left.

    finish : State (Ret₃ (λ _ → true)) →
             Σ (PathSum (m ℕ+ m) 0 0) (λ ζ → ξ₀ ⟶ᶠ* ζ)
    finish (stage zero    ξ lab ρ ch tr rd df fd on ij) = ξ , ch
    finish (stage (suc _) ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (t≢f (trans (sym (on zero)) (Ret₃-none (lab zero))))

    --------------------------------------------------------------------
    -- Pass 1: [HH] at b_i with d_i ← a_i ⊕ s_L,i, then [Elim] of d_i

    pass₁ : ∀ d i → d i ≡ false →
            State (Ret₁ d) → State (Ret₁ (d [ i ≔ true ]))
    pass₁ d i di (stage zero ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (fin0 (proj₁ (fd (B₁ , i) (cong not di))))
    pass₁ d i di (stage (suc zero) ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (one-slot lab fd (B₁ , i) (D₂ , i) (cong not di) (cong not di)
                       (blk≢ (λ ())))
    pass₁ d i di (stage (suc (suc k)) ξ lab ρ ch tr rd df fd on ij) =
      stage k ζ lab″ ρ″ (ch ◅◅ᶠ proj₁ res) (proj₂ res)
            reads″ dflts″ find″ only″ inj″
      where
      j : Fin (suc (suc k))
      j = proj₁ (fd (B₁ , i) (cong not di))

      lj : lab j ≡ (B₁ , i)
      lj = proj₂ (fd (B₁ , i) (cong not di))

      iu : Fin (suc k)
      iu = proj₁ (locate lab fd j lj (D₂ , i) (cong not di) (blk≢ (λ ())))

      li : lab (punchIn j iu) ≡ (D₂ , i)
      li = proj₂ (locate lab fd j lj (D₂ , i) (cong not di) (blk≢ (λ ())))

      a : Fin (suc k)
      a = proj₁ (locate lab fd j lj (A₁ , i) refl (blk≢ (λ ())))

      la : lab (punchIn j a) ≡ (A₁ , i)
      la = proj₂ (locate lab fd j lj (A₁ , i) refl (blk≢ (λ ())))

      a≢iu : a ≢ iu
      a≢iu e = blk≢ {b = A₁} {b′ = D₂} (λ ()) (trans (sym la)
                             (trans (cong (λ t → lab (punchIn j t)) e) li))

      q : Assign (suc k) → Bool
      q y = y a xor sL i

      Q : Poly (m ℕ+ m) (suc k)
      Q = liftᵉ (var y[ a ] ⊕ᵉ lit (sL i))

      open Flip lab ρ rd df fd j lj

      -- The labels other than b_i keep their values.

      A-kept : ∀ y t → Zᶜ true y (A₁ , t) ≡ Zᶜ false y (A₁ , t)
      A-kept y t = kept y (A₁ , t) refl (blk≢ (λ ()))

      B-kept : ∀ y t → t ≢ i → Zᶜ true y (B₁ , t) ≡ Zᶜ false y (B₁ , t)
      B-kept y t t≢i = go (d t) refl
        where
        go : ∀ b → d t ≡ b → Zᶜ true y (B₁ , t) ≡ Zᶜ false y (B₁ , t)
        go false e = kept y (B₁ , t) (cong not e) (crd≢ t≢i)
        go true  e = fixed y (B₁ , t) (cong not e) refl

      C-kept : ∀ y t → Zᶜ true y (C₂ , t) ≡ Zᶜ false y (C₂ , t)
      C-kept y t = kept y (C₂ , t) refl (blk≢ (λ ()))

      D-kept : ∀ y t → Zᶜ true y (D₂ , t) ≡ Zᶜ false y (D₂ , t)
      D-kept y t = go (d t) refl
        where
        go : ∀ b → d t ≡ b → Zᶜ true y (D₂ , t) ≡ Zᶜ false y (D₂ , t)
        go false e = kept y (D₂ , t) (cong not e) (blk≢ (λ ()))
        go true  e = fixed y (D₂ , t) (cong not e)
                           (cong (_xor sL t) (A-kept y t))

      E-kept : ∀ y t → Zᶜ true y (E₃ , t) ≡ Zᶜ false y (E₃ , t)
      E-kept y t = kept y (E₃ , t) refl (blk≢ (λ ()))

      H-kept : ∀ y t → Zᶜ true y (H₃ , t) ≡ Zᶜ false y (H₃ , t)
      H-kept y t = kept y (H₃ , t) refl (blk≢ (λ ()))

      -- The derivative in b_i is d_i ⊕ (a_i ⊕ s_L,i).

      dF : ∀ y → Fblk (Zᶜ true y) xor Fblk (Zᶜ false y) ≡ y iu xor q y
      dF y = trans
        (∂-b (Zᶜ true y) (Zᶜ false y) i (A-kept y) (B-kept y) (flipped y)
             (C-kept y) (D-kept y) (E-kept y) (H-kept y))
        (trans (cong₂ (λ p r → (p xor sL i) xor r)
                      (read y a la) (read y iu li))
               (xor-comm (y a xor sL i) (y iu)))

      dG : ∀ w y → Gblk w (Zᶜ true y) ≡ Gblk w (Zᶜ false y)
      dG w y = Gblk-cong {Z = Zᶜ true y} {Z′ = Zᶜ false y}
                         (E-kept y) (H-kept y) w

      ζ : PathSum (m ℕ+ m) k k
      ζ = elim-reduct (front iu (hhᴳ-reduct (front j ξ) iu Q))

      res = hh-elim ξ tr j iu Q q
        (λ x y → eval-liftᵉ (var y[ a ] ⊕ᵉ lit (sL i)) x y)
        (Absent-liftᵉ y[ iu ] (var y[ a ] ⊕ᵉ lit (sL i))
                      ((λ e → a≢iu (sym (y-inj e))) , tt))
        dF dG

      -- d_i is fixed to a_i ⊕ s_L,i, a_i being still a path variable.

      σ₁ : Assign k → Assign (suc (suc k))
      σ₁ y =
        insertᵃ j false (insertᵃ iu false y [ iu ≔ q (insertᵃ iu false y) ])

      du : ∀ y → dflt (D₂ , i) (ρ (σ₁ y)) ≡ q (insertᵃ iu false y)
      du y = cong (_xor sL i) (trans (cong (ρ (σ₁ y)) (sym la))
        (trans (rd (σ₁ y) (punchIn j a))
          (trans (insertᵃ-punchIn j false
                    (insertᵃ iu false y [ iu ≔ q (insertᵃ iu false y) ]) a)
                 (≔-there (insertᵃ iu false y) (q (insertᵃ iu false y))
                          a≢iu))))

      R′ : ∀ ℓ → ℓ ≢ (B₁ , i) → ℓ ≢ (D₂ , i) →
           Ret₁ (d [ i ≔ true ]) ℓ ≡ Ret₁ d ℓ
      R′ (A₁ , t) _  _  = refl
      R′ (B₁ , t) ne _  =
        cong not (≔-there d true (λ e → ne (cong (B₁ ,_) e)))
      R′ (C₂ , t) _  _  = refl
      R′ (D₂ , t) _  ne =
        cong not (≔-there d true (λ e → ne (cong (D₂ ,_) e)))
      R′ (E₃ , t) _  _  = refl
      R′ (H₃ , t) _  _  = refl

      open Advance {Ret′ = Ret₁ (d [ i ≔ true ])} lab ρ rd df fd on ij j iu q
                   lj li (λ _ → refl) du
                   (cong not (≔-here d i true))
                   (cong not (≔-here d i true)) R′

    --------------------------------------------------------------------
    -- Pass 2: [HH] at c_i with e_i ← s_L,i, then [Elim] of e_i

    pass₂ : ∀ d i → d i ≡ false →
            State (Ret₂ d) → State (Ret₂ (d [ i ≔ true ]))
    pass₂ d i di (stage zero ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (fin0 (proj₁ (fd (C₂ , i) (cong not di))))
    pass₂ d i di (stage (suc zero) ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (one-slot lab fd (C₂ , i) (E₃ , i) (cong not di) (cong not di)
                       (blk≢ (λ ())))
    pass₂ d i di (stage (suc (suc k)) ξ lab ρ ch tr rd df fd on ij) =
      stage k ζ lab″ ρ″ (ch ◅◅ᶠ proj₁ res) (proj₂ res)
            reads″ dflts″ find″ only″ inj″
      where
      j : Fin (suc (suc k))
      j = proj₁ (fd (C₂ , i) (cong not di))

      lj : lab j ≡ (C₂ , i)
      lj = proj₂ (fd (C₂ , i) (cong not di))

      iu : Fin (suc k)
      iu = proj₁ (locate lab fd j lj (E₃ , i) (cong not di) (blk≢ (λ ())))

      li : lab (punchIn j iu) ≡ (E₃ , i)
      li = proj₂ (locate lab fd j lj (E₃ , i) (cong not di) (blk≢ (λ ())))

      q : Assign (suc k) → Bool
      q _ = sL i

      Q : Poly (m ℕ+ m) (suc k)
      Q = liftᵉ (lit (sL i))

      open Flip lab ρ rd df fd j lj

      -- The labels other than c_i keep their values; d is a ⊕ s_L.

      A-kept : ∀ y t → Zᶜ true y (A₁ , t) ≡ Zᶜ false y (A₁ , t)
      A-kept y t = kept y (A₁ , t) refl (blk≢ (λ ()))

      B-kept : ∀ y t → Zᶜ true y (B₁ , t) ≡ Zᶜ false y (B₁ , t)
      B-kept y t = fixed y (B₁ , t) refl refl

      C-kept : ∀ y t → t ≢ i → Zᶜ true y (C₂ , t) ≡ Zᶜ false y (C₂ , t)
      C-kept y t t≢i = go (d t) refl
        where
        go : ∀ b → d t ≡ b → Zᶜ true y (C₂ , t) ≡ Zᶜ false y (C₂ , t)
        go false e = kept y (C₂ , t) (cong not e) (crd≢ t≢i)
        go true  e = fixed y (C₂ , t) (cong not e) refl

      D-kept : ∀ y t → Zᶜ true y (D₂ , t) ≡ Zᶜ false y (D₂ , t)
      D-kept y t = fixed y (D₂ , t) refl (cong (_xor sL t) (A-kept y t))

      E-kept : ∀ y t → Zᶜ true y (E₃ , t) ≡ Zᶜ false y (E₃ , t)
      E-kept y t = go (d t) refl
        where
        go : ∀ b → d t ≡ b → Zᶜ true y (E₃ , t) ≡ Zᶜ false y (E₃ , t)
        go false e = kept y (E₃ , t) (cong not e) (blk≢ (λ ()))
        go true  e = fixed y (E₃ , t) (cong not e) refl

      H-kept : ∀ y t → Zᶜ true y (H₃ , t) ≡ Zᶜ false y (H₃ , t)
      H-kept y t = kept y (H₃ , t) refl (blk≢ (λ ()))

      -- The derivative in c_i is a_i ⊕ d_i ⊕ e_i = e_i ⊕ s_L,i.

      dF : ∀ y → Fblk (Zᶜ true y) xor Fblk (Zᶜ false y) ≡ y iu xor q y
      dF y = trans
        (∂-c (Zᶜ true y) (Zᶜ false y) i (A-kept y) (B-kept y) (C-kept y)
             (flipped y) (D-kept y) (E-kept y) (H-kept y))
        (trans (cong₂ (λ p r → (Zᶜ false y (A₁ , i) xor p) xor r)
                      (dfl false y (D₂ , i) refl) (read y iu li))
          (trans (cong (_xor y iu) (xor-cancelˡ (Zᶜ false y (A₁ , i)) (sL i)))
                 (xor-comm (sL i) (y iu))))

      dG : ∀ w y → Gblk w (Zᶜ true y) ≡ Gblk w (Zᶜ false y)
      dG w y = Gblk-cong {Z = Zᶜ true y} {Z′ = Zᶜ false y}
                         (E-kept y) (H-kept y) w

      ζ : PathSum (m ℕ+ m) k k
      ζ = elim-reduct (front iu (hhᴳ-reduct (front j ξ) iu Q))

      res = hh-elim ξ tr j iu Q q
        (λ x y → eval-liftᵉ (lit (sL i)) x y)
        (Absent-liftᵉ y[ iu ] (lit (sL i)) tt)
        dF dG

      R′ : ∀ ℓ → ℓ ≢ (C₂ , i) → ℓ ≢ (E₃ , i) →
           Ret₂ (d [ i ≔ true ]) ℓ ≡ Ret₂ d ℓ
      R′ (A₁ , t) _  _  = refl
      R′ (B₁ , t) _  _  = refl
      R′ (C₂ , t) ne _  =
        cong not (≔-there d true (λ e → ne (cong (C₂ ,_) e)))
      R′ (D₂ , t) _  _  = refl
      R′ (E₃ , t) _  ne =
        cong not (≔-there d true (λ e → ne (cong (E₃ ,_) e)))
      R′ (H₃ , t) _  _  = refl

      open Advance {Ret′ = Ret₂ (d [ i ≔ true ])} lab ρ rd df fd on ij j iu q
                   lj li (λ _ → refl) (λ _ → refl)
                   (cong not (≔-here d i true))
                   (cong not (≔-here d i true)) R′

    --------------------------------------------------------------------
    -- Pass 3: [HH] at a_i with h_i ← s_R,i, then [Elim] of h_i

    pass₃ : ∀ d i → d i ≡ false →
            State (Ret₃ d) → State (Ret₃ (d [ i ≔ true ]))
    pass₃ d i di (stage zero ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (fin0 (proj₁ (fd (A₁ , i) (cong not di))))
    pass₃ d i di (stage (suc zero) ξ lab ρ ch tr rd df fd on ij) =
      ⊥-elim (one-slot lab fd (A₁ , i) (H₃ , i) (cong not di) (cong not di)
                       (blk≢ (λ ())))
    pass₃ d i di (stage (suc (suc k)) ξ lab ρ ch tr rd df fd on ij) =
      stage k ζ lab″ ρ″ (ch ◅◅ᶠ proj₁ res) (proj₂ res)
            reads″ dflts″ find″ only″ inj″
      where
      j : Fin (suc (suc k))
      j = proj₁ (fd (A₁ , i) (cong not di))

      lj : lab j ≡ (A₁ , i)
      lj = proj₂ (fd (A₁ , i) (cong not di))

      iu : Fin (suc k)
      iu = proj₁ (locate lab fd j lj (H₃ , i) (cong not di) (blk≢ (λ ())))

      li : lab (punchIn j iu) ≡ (H₃ , i)
      li = proj₂ (locate lab fd j lj (H₃ , i) (cong not di) (blk≢ (λ ())))

      q : Assign (suc k) → Bool
      q _ = sR i

      Q : Poly (m ℕ+ m) (suc k)
      Q = liftᵉ (lit (sR i))

      open Flip lab ρ rd df fd j lj

      -- a_i flips, and d_i with it; the other labels keep their values.

      A-kept : ∀ y t → t ≢ i → Zᶜ true y (A₁ , t) ≡ Zᶜ false y (A₁ , t)
      A-kept y t t≢i = go (d t) refl
        where
        go : ∀ b → d t ≡ b → Zᶜ true y (A₁ , t) ≡ Zᶜ false y (A₁ , t)
        go false e = kept y (A₁ , t) (cong not e) (crd≢ t≢i)
        go true  e = fixed y (A₁ , t) (cong not e) refl

      B-kept : ∀ y t → Zᶜ true y (B₁ , t) ≡ Zᶜ false y (B₁ , t)
      B-kept y t = fixed y (B₁ , t) refl refl

      C-kept : ∀ y t → Zᶜ true y (C₂ , t) ≡ Zᶜ false y (C₂ , t)
      C-kept y t = fixed y (C₂ , t) refl refl

      E-kept : ∀ y t → Zᶜ true y (E₃ , t) ≡ Zᶜ false y (E₃ , t)
      E-kept y t = fixed y (E₃ , t) refl refl

      H-kept : ∀ y t → Zᶜ true y (H₃ , t) ≡ Zᶜ false y (H₃ , t)
      H-kept y t = go (d t) refl
        where
        go : ∀ b → d t ≡ b → Zᶜ true y (H₃ , t) ≡ Zᶜ false y (H₃ , t)
        go false e = kept y (H₃ , t) (cong not e) (blk≢ (λ ()))
        go true  e = fixed y (H₃ , t) (cong not e) refl

      -- The derivative in a_i (and d_i) is h_i ⊕ s_R,i.

      dF : ∀ y → Fblk (Zᶜ true y) xor Fblk (Zᶜ false y) ≡ y iu xor q y
      dF y = trans
        (∂-a (Zᶜ true y) (Zᶜ false y) i (A-kept y) (flipped y) (B-kept y)
             (C-kept y) (λ t → dfl true y (D₂ , t) refl)
             (λ t → dfl false y (D₂ , t) refl) (E-kept y) (H-kept y))
        (trans (cong (sR i xor_) (read y iu li)) (xor-comm (sR i) (y iu)))

      dG : ∀ w y → Gblk w (Zᶜ true y) ≡ Gblk w (Zᶜ false y)
      dG w y = Gblk-cong {Z = Zᶜ true y} {Z′ = Zᶜ false y}
                         (E-kept y) (H-kept y) w

      ζ : PathSum (m ℕ+ m) k k
      ζ = elim-reduct (front iu (hhᴳ-reduct (front j ξ) iu Q))

      res = hh-elim ξ tr j iu Q q
        (λ x y → eval-liftᵉ (lit (sR i)) x y)
        (Absent-liftᵉ y[ iu ] (lit (sR i)) tt)
        dF dG

      R′ : ∀ ℓ → ℓ ≢ (A₁ , i) → ℓ ≢ (H₃ , i) →
           Ret₃ (d [ i ≔ true ]) ℓ ≡ Ret₃ d ℓ
      R′ (A₁ , t) ne _  =
        cong not (≔-there d true (λ e → ne (cong (A₁ ,_) e)))
      R′ (B₁ , t) _  _  = refl
      R′ (C₂ , t) _  _  = refl
      R′ (D₂ , t) _  _  = refl
      R′ (E₃ , t) _  _  = refl
      R′ (H₃ , t) _  ne =
        cong not (≔-there d true (λ e → ne (cong (H₃ ,_) e)))

      open Advance {Ret′ = Ret₃ (d [ i ≔ true ])} lab ρ rd df fd on ij j iu q
                   lj li (λ _ → refl) (λ _ → refl)
                   (cong not (≔-here d i true))
                   (cong not (≔-here d i true)) R′

    --------------------------------------------------------------------
    -- The three passes

    -- Every coordinate through pass 1, then pass 2, then pass 3.

    reduced : State (Ret₃ (λ _ → true))
    reduced =
      third (State-resp Ret₂₃ (second (State-resp Ret₁₂ (first initial))))
      where
      first : State (Ret₁ (λ _ → false)) → State (Ret₁ (λ _ → true))
      first = Sweep.all (λ d → State (Ret₁ d))
                        (λ h → State-resp (Ret₁-resp h)) pass₁

      second : State (Ret₂ (λ _ → false)) → State (Ret₂ (λ _ → true))
      second = Sweep.all (λ d → State (Ret₂ d))
                         (λ h → State-resp (Ret₂-resp h)) pass₂

      third : State (Ret₃ (λ _ → false)) → State (Ret₃ (λ _ → true))
      third = Sweep.all (λ d → State (Ret₃ d))
                        (λ h → State-resp (Ret₃-resp h)) pass₃

    -- A complete reduction of ξ₀.

    complete : Σ (PathSum (m ℕ+ m) 0 0) (λ ζ → ξ₀ ⟶ᶠ* ζ)
    complete = finish reduced

  ----------------------------------------------------------------------
  -- The theorems

  -- Every path-sum written as the circuit's reduces, by figure 2's
  -- rules, to one with no path variables ...

  written-reduces : ∀ ξ₀ → Written ξ₀ →
                    Σ (PathSum (m ℕ+ m) 0 0) (λ ζ → ξ₀ ⟶ᶠ* ζ)
  written-reduces ξ₀ w = Reduce.complete ξ₀ (written-tracks ξ₀ w)

  -- ... and that one is |x⟩ ↦ |s⟩, coefficient by coefficient: ξ₀ is
  -- congruent to the circuit on |0⟩ (at0-HS-congruent), hence
  -- equivalent to the specification, and a path-sum with no path
  -- variables equivalent to it is it (spec-only-if).

  written-finds : ∀ ξ₀ → Written ξ₀ →
                  Σ (PathSum (m ℕ+ m) 0 0) (λ ζ →
                    (ξ₀ ⟶ᶠ* ζ) × Congruent ζ (specᴾ s))
  written-finds ξ₀ w =
    ζ , proj₂ (written-reduces ξ₀ w) , proj₂ (spec-only-if s ζ ζ≋spec)
    where
    ζ : PathSum (m ℕ+ m) 0 0
    ζ = proj₁ (written-reduces ξ₀ w)

    c : Congruent (at0 (HS g s)) ξ₀
    c = at0-HS-congruent g s ξ₀ (proj₁ w) (proj₂ w)

    ξ₀≋spec : ξ₀ ≋ specᴾ s
    ξ₀≋spec = ≋-trans {ξ = ξ₀} {ζ = at0 (HS g s)} {χ = specᴾ s}
      (≋-sym {ξ = at0 (HS g s)} {ζ = ξ₀}
             (≈-≋ (at0 (HS g s)) ξ₀ (proj₁ c) (proj₂ c)))
      (hidden-shift-≋ g s)

    ζ≋spec : ζ ≋ specᴾ s
    ζ≋spec = ≋-trans {ξ = ζ} {ζ = ξ₀} {χ = specᴾ s}
      (≋-sym {ξ = ξ₀} {ζ = ζ} (⟶ᶠ*-sound (proj₂ (written-reduces ξ₀ w))))
      ξ₀≋spec

  -- In particular a complete reduction of the circuit on |0⟩ exists ...

  hidden-shift-exists :
    Σ (PathSum (m ℕ+ m) 0 0) (λ ζ → at0 (HS g s) ⟶ᶠ* ζ)
  hidden-shift-exists = written-reduces (at0 (HS g s)) written₀

  -- ... and it is |x⟩ ↦ |s⟩, coefficient by coefficient: the calculus
  -- finds the hidden shift without being given the specification.

  hidden-shift-finds :
    Σ (PathSum (m ℕ+ m) 0 0) (λ ζ →
      (at0 (HS g s) ⟶ᶠ* ζ) × Congruent ζ (specᴾ s))
  hidden-shift-finds =
    proj₁ hidden-shift-exists , proj₂ hidden-shift-exists ,
    proj₂ (hidden-shift-reduces g s (proj₂ hidden-shift-exists))
