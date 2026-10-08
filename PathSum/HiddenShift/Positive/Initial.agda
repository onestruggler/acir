------------------------------------------------------------------------
-- Presentations of groups
--
-- The hidden shift circuit on |0⟩ satisfies the invariant
--
-- PathSum.HiddenShift.Positive.Invariant's Inv holds of the circuit on
-- |0⟩, at0 (HS g s), for every m, g and s (inv₀).  Its values are those
-- of PathSum.HiddenShift.Exists: the phase is ½ Fblk and the outputs are
-- Gblk of the path read by label (Blocks' six blocks a b c d e h, the
-- outputs being e and h).
--
-- * inj: an output variable is an e or an h, and an output reads it
--   directly; every other variable is internal.
-- * The witness T is the block b.  Each b_i is internal, and the
--   derivative of the phase in b_i is a_i ⊕ s_L,i ⊕ d_i, affine
--   (Blocks' ∂-b), so b_i is Clifford.
-- * The sum of (-1)^Fblk over b is stabilizer-like.  b enters Fblk only
--   through b·(a ⊕ s_L ⊕ d), so the sum is 2^m times the indicator of
--   d = a ⊕ s_L times (-1)^Fblk with b = 0 -- and on that subspace the
--   two copies of g, g(a ⊕ s_L) and g(d), cancel, leaving the quadratic
--   form (a⊕s_L)·s_R + a·c + b·d + c·d + c·e + d·h at b = 0 (Rq).  The
--   sum is computed one coordinate of b at a time, with Exists' Sweep:
--   after summing over a set D of them it is 2^e times an indicator I
--   of the equations of D times (-1)^Fblk with D's b cleared.
--
-- This is the only place g's arbitrary degree is met: the invariant
-- needs nothing of g beyond the cancellation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Positive.Initial (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-same; xor-identityʳ)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; splitAt; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ; _≟_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Properties using
  (*-identityˡ; *-zeroˡ; *-zeroʳ; pos-*)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; map; allFin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-allFin)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (zero; suc)
  renaming (_+_ to _ℕ+_; _^_ to _ℕ^_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Vec.Base using (_∷_; lookup; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using (_[_≔_]; ≔-here; ≔-there)
open import PathSum.Base using (PathSum; phase)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift M₀ using (HS; hs-norm; boolᴾ; boolᴾ-resp)
open import PathSum.HiddenShift.Blocks using
  (Blk; A₁; B₁; C₂; D₂; E₃; H₃; Lbl; LAssign; _‹_›; Gblk; Gblk-cong;
   module Phase)
open import PathSum.HiddenShift.Exists M₀ using
  (pos₀; lab₀; lab₀-pos₀; pos₀-lab₀; tracks₀; module Sweep)
open import PathSum.HiddenShift.Positive.Boolean
open import PathSum.HiddenShift.Positive.Class M₀ using (Int; Clifᶜ)
open import PathSum.HiddenShift.Positive.Invariant M₀ using
  (Inv; Indep⇒Int; Cl⇒Clif)
open import PathSum.HiddenShift.Positive.Stabilizer using
  (SL; sl; ind; zero?; Σ[_]; σ; Σ-none; Σ-congᵀ; Σ-grow; setᵀ; setᵀ-agree)
open import PathSum.HiddenShift.Positive.Values M₀ using (VTracks; vtr)
open import PathSum.HiddenShift.Simulation M₀ using (at0)
open import PathSum.HiddenShift.Stuck.Machine M₀ using (tracks-cong)
open import PathSum.HiddenShift.Walsh using (lhalf; rhalf; dot; _⊕ᵃ_; dot-cong)
open import PathSum.Polynomial using (Poly; sgn)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  variable
    N n k : ℕ


------------------------------------------------------------------------
-- Generalities

private
  -- Invariant's conversions, at a number of variables not known to be
  -- a successor.
  Indep⇒Int′ : {ξ : PathSum N k n} {F : Pt n → Bool}
               {G : Fin N → Pt n → Bool} → VTracks ξ F G →
               (v : Fin n) → (∀ w → Indep (G w) v) → Int ξ v
  Indep⇒Int′ {n = suc n} tr v h = Indep⇒Int tr v h
  Indep⇒Int′ {n = zero}  tr () h

  Cl⇒Clif′ : {ξ : PathSum N k n} {F : Pt n → Bool}
             {G : Fin N → Pt n → Bool} → VTracks ξ F G →
             (v : Fin n) → Cl F v → Clifᶜ (phase ξ) v
  Cl⇒Clif′ {n = suc n} tr v c = Cl⇒Clif tr v c
  Cl⇒Clif′ {n = zero}  tr () c

  t≢f : true ≢ false
  t≢f ()

  1≢0 : 1ℤ ≢ 0ℤ
  1≢0 ()

  solve-xor : ∀ {a b e} → a xor b ≡ e → a ≡ b xor e
  solve-xor {false} {false} refl = refl
  solve-xor {false} {true}  refl = refl
  solve-xor {true}  {false} refl = refl
  solve-xor {true}  {true}  refl = refl

  xor-false′ : ∀ {a b} → a xor b ≡ false → a ≡ b
  xor-false′ {false} {false} _ = refl
  xor-false′ {true}  {true}  _ = refl

  -- Summing a sign and the sign flipped by k.
  comb : ∀ (P I : ℤ) a k →
         P * (I * sgn a) + P * (I * sgn (a xor k)) ≡
         ((+ 2) * P) * ((zero? k * I) * sgn a)
  comb P I false false = solve 2 (λ P I →
    P :* (I :* con 1ℤ) :+ P :* (I :* con 1ℤ) :=
    (con (+ 2) :* P) :* ((con 1ℤ :* I) :* con 1ℤ)) refl P I
  comb P I false true  = solve 2 (λ P I →
    P :* (I :* con 1ℤ) :+ P :* (I :* con (- 1ℤ)) :=
    (con (+ 2) :* P) :* ((con 0ℤ :* I) :* con 1ℤ)) refl P I
  comb P I true  false = solve 2 (λ P I →
    P :* (I :* con (- 1ℤ)) :+ P :* (I :* con (- 1ℤ)) :=
    (con (+ 2) :* P) :* ((con 1ℤ :* I) :* con (- 1ℤ))) refl P I
  comb P I true  true  = solve 2 (λ P I →
    P :* (I :* con (- 1ℤ)) :+ P :* (I :* con 1ℤ) :=
    (con (+ 2) :* P) :* ((con 0ℤ :* I) :* con (- 1ℤ))) refl P I

  -- Two copies of t₁ cancel.
  drop : ∀ a b x c → ((a xor b) xor x) xor (a xor c) ≡ (b xor x) xor c
  drop false b x c = refl
  drop true  false false false = refl
  drop true  false false true  = refl
  drop true  false true  false = refl
  drop true  false true  true  = refl
  drop true  true  false false = refl
  drop true  true  false true  = refl
  drop true  true  true  false = refl
  drop true  true  true  true  = refl

  -- An inner product of coordinatewise affine vectors is quadratic.
  Quad-dot : ∀ {k} {U V : Pt n → Fin k → Bool} →
             (∀ i → Aff (λ x → U x i)) → (∀ i → Aff (λ x → V x i)) →
             Quad (λ x → dot (U x) (V x))
  Quad-dot {k = zero}          aU aV = Aff⇒Quad (Aff-const false)
  Quad-dot {k = suc k} {U} {V} aU aV =
    Quad-xor {f = λ x → U x zero ∧ V x zero}
             {g = λ x → dot (λ i → U x (suc i)) (λ i → V x (suc i))}
      (Quad-∧ (aU zero) (aV zero))
      (Quad-dot {U = λ x i → U x (suc i)} {V = λ x i → V x (suc i)}
                (λ i → aU (suc i)) (λ i → aV (suc i)))


------------------------------------------------------------------------
-- The circuit on |0⟩

module _ {m : ℕ} (g : Poly m 0) (s : Assign (m ℕ+ m)) where

  private
    sL sR : Fin m → Bool
    sL = lhalf {m} s
    sR = rhalf {m} s

    L : ℕ
    L = hs-norm (m ℕ+ m)

  open Phase (boolᴾ g) (boolᴾ-resp g) sL sR using
    (Fblk; T₁; T₂; T₃; T₄; T₅; T₆; T₇; T₈; ∂-b)

  -- The path read by label, and the values.

  ρ : Pt L → LAssign m
  ρ p ℓ = lookup p (pos₀ m ℓ)

  F₀ : Pt L → Bool
  F₀ p = Fblk (ρ p)

  G₀ : Fin (m ℕ+ m) → Pt L → Bool
  G₀ w p = Gblk w (ρ p)

  Fblk-cong : {Z Z′ : LAssign m} → (∀ ℓ → Z ℓ ≡ Z′ ℓ) → Fblk Z ≡ Fblk Z′
  Fblk-cong {Z} {Z′} h = cong₂ _xor_
    (cong₂ _xor_ (cong₂ _xor_ (cong₂ _xor_ t₁ t₂) (cong₂ _xor_ t₃ t₄))
                 (cong₂ _xor_ t₅ t₆))
    (cong₂ _xor_ t₇ t₈)
    where
    t₁ : T₁ Z ≡ T₁ Z′
    t₁ = boolᴾ-resp g _ _ (λ i → cong (_xor sL i) (h (A₁ , i)))
    t₂ : T₂ Z ≡ T₂ Z′
    t₂ = dot-cong (λ i → cong (_xor sL i) (h (A₁ , i)))
                  (λ i → cong (_xor sR i) (h (B₁ , i)))
    t₃ : T₃ Z ≡ T₃ Z′
    t₃ = dot-cong (λ i → h (A₁ , i)) (λ i → h (C₂ , i))
    t₄ : T₄ Z ≡ T₄ Z′
    t₄ = dot-cong (λ i → h (B₁ , i)) (λ i → h (D₂ , i))
    t₅ : T₅ Z ≡ T₅ Z′
    t₅ = boolᴾ-resp g _ _ (λ i → h (D₂ , i))
    t₆ : T₆ Z ≡ T₆ Z′
    t₆ = dot-cong (λ i → h (C₂ , i)) (λ i → h (D₂ , i))
    t₇ : T₇ Z ≡ T₇ Z′
    t₇ = dot-cong (λ i → h (C₂ , i)) (λ i → h (E₃ , i))
    t₈ : T₈ Z ≡ T₈ Z′
    t₈ = dot-cong (λ i → h (D₂ , i)) (λ i → h (H₃ , i))

  vt₀ : VTracks (at0 (HS g s)) F₀ G₀
  vt₀ = vtr (tracks-cong (tracks₀ g s)
    (λ y → Fblk-cong (λ ℓ → sym (lookup∘tabulate y (pos₀ m ℓ))))
    (λ w y → Gblk-cong {Z = λ ℓ → y (pos₀ m ℓ)} {Z′ = ρ (tabulate y)}
                       (λ i → sym (lookup∘tabulate y (pos₀ m (E₃ , i))))
                       (λ i → sym (lookup∘tabulate y (pos₀ m (H₃ , i)))) w))

  -- Setting one variable changes one label.

  ρ-other : ∀ p v b ℓ → ℓ ≢ lab₀ m v → ρ (set p v b) ℓ ≡ ρ p ℓ
  ρ-other p v b ℓ ne = lookup-set-there p b
    (λ e → ne (trans (sym (lab₀-pos₀ m ℓ)) (cong (lab₀ m) e)))

  ρ-here : ∀ p v b → ρ (set p v b) (lab₀ m v) ≡ b
  ρ-here p v b = trans (cong (lookup (set p v b)) (pos₀-lab₀ m v))
                       (lookup-set-here p v b)

  -- Labels in different blocks differ.

  private
    blk≢ : ∀ {b b′ : Blk} {i i′ : Fin m} → b ≢ b′ → (b , i) ≢ (b′ , i′)
    blk≢ ne e = ne (cong proj₁ e)

    A≢B : A₁ ≢ B₁
    A≢B ()
    C≢B : C₂ ≢ B₁
    C≢B ()
    D≢B : D₂ ≢ B₁
    D≢B ()
    E≢B : E₃ ≢ B₁
    E≢B ()
    H≢B : H₃ ≢ B₁
    H≢B ()


  ----------------------------------------------------------------------
  -- Internal variables and the outputs

  inner : Blk → Bool
  inner A₁ = true
  inner B₁ = true
  inner C₂ = true
  inner D₂ = true
  inner E₃ = false
  inner H₃ = false

  int-of : ∀ v → inner (proj₁ (lab₀ m v)) ≡ true → Int (at0 (HS g s)) v
  int-of v e = Indep⇒Int′ vt₀ v (λ w p → trans (gout w p true)
                                                (sym (gout w p false)))
    where
    off : ∀ {b} (i : Fin m) → inner b ≡ false → (b , i) ≢ lab₀ m v
    off i nb e′ = t≢f (trans (sym e)
      (trans (cong (λ ℓ → inner (proj₁ ℓ)) (sym e′)) nb))

    gout : ∀ w p b → G₀ w (set p v b) ≡ G₀ w p
    gout w p b = Gblk-cong {Z = ρ (set p v b)} {Z′ = ρ p}
                           (λ i → ρ-other p v b (E₃ , i) (off i refl))
                           (λ i → ρ-other p v b (H₃ , i) (off i refl)) w

  out-E : ∀ p (i : Fin m) → G₀ (i ↑ˡ m) p ≡ ρ p (E₃ , i)
  out-E p i = cong [ (ρ p) ‹ E₃ › , (ρ p) ‹ H₃ › ]′ (splitAt-↑ˡ m i m)

  out-H : ∀ p (i : Fin m) → G₀ (m ↑ʳ i) p ≡ ρ p (H₃ , i)
  out-H p i = cong [ (ρ p) ‹ E₃ › , (ρ p) ‹ H₃ › ]′ (splitAt-↑ʳ m m i)

  inj₀ : ∀ p p′ → (∀ w → G₀ w p ≡ G₀ w p′) →
         ∀ v → ¬ Int (at0 (HS g s)) v → lookup p v ≡ lookup p′ v
  inj₀ p p′ eq v ¬int = go (lab₀ m v) refl
    where
    via : ∀ q ℓ → lab₀ m v ≡ ℓ → lookup q v ≡ ρ q ℓ
    via q ℓ e = trans (cong (lookup q) (sym (pos₀-lab₀ m v)))
                      (cong (λ l → lookup q (pos₀ m l)) e)

    inside : ∀ ℓ → lab₀ m v ≡ ℓ → inner (proj₁ ℓ) ≡ true →
             lookup p v ≡ lookup p′ v
    inside ℓ e i = ⊥-elim (¬int (int-of v
      (trans (cong (λ l → inner (proj₁ l)) e) i)))

    go : ∀ ℓ → lab₀ m v ≡ ℓ → lookup p v ≡ lookup p′ v
    go (A₁ , i) e = inside (A₁ , i) e refl
    go (B₁ , i) e = inside (B₁ , i) e refl
    go (C₂ , i) e = inside (C₂ , i) e refl
    go (D₂ , i) e = inside (D₂ , i) e refl
    go (E₃ , i) e = trans (via p (E₃ , i) e) (trans (sym (out-E p i))
      (trans (eq (i ↑ˡ m)) (trans (out-E p′ i) (sym (via p′ (E₃ , i) e)))))
    go (H₃ , i) e = trans (via p (H₃ , i) e) (trans (sym (out-H p i))
      (trans (eq (m ↑ʳ i)) (trans (out-H p′ i) (sym (via p′ (H₃ , i) e)))))


  ----------------------------------------------------------------------
  -- The witness: the block b

  inB : (Fin m → Bool) → Lbl m → Bool
  inB D (A₁ , i) = false
  inB D (B₁ , i) = D i
  inB D (C₂ , i) = false
  inB D (D₂ , i) = false
  inB D (E₃ , i) = false
  inB D (H₃ , i) = false

  Tᴮ : (Fin m → Bool) → Fin L → Bool
  Tᴮ D v = inB D (lab₀ m v)

  T₀ : Fin L → Bool
  T₀ = Tᴮ (λ _ → true)

  private
    is-b : ∀ ℓ → inB (λ _ → true) ℓ ≡ true → ℓ ≡ (B₁ , proj₂ ℓ)
    is-b (B₁ , i) _ = refl
    is-b (A₁ , i) ()
    is-b (C₂ , i) ()
    is-b (D₂ , i) ()
    is-b (E₃ , i) ()
    is-b (H₃ , i) ()

  -- The equation b_i's derivative gives: a_i ⊕ s_L,i ⊕ d_i.

  u : Fin m → LAssign m → Bool
  u i Z = (Z (A₁ , i) xor sL i) xor Z (D₂ , i)

  Aff-u : ∀ i → Aff (λ x → u i (ρ x))
  Aff-u i = Aff-xor (Aff-xor (Aff-lookup (pos₀ m (A₁ , i))) (Aff-const (sL i)))
                    (Aff-lookup (pos₀ m (D₂ , i)))

  -- Each b_i is internal and Clifford.

  T-int₀ : ∀ v → T₀ v ≡ true → Int (at0 (HS g s)) v
  T-int₀ v e = int-of v (cong (λ ℓ → inner (proj₁ ℓ)) (is-b (lab₀ m v) e))

  Cl-b : ∀ v (i : Fin m) → lab₀ m v ≡ (B₁ , i) → Cl F₀ v
  Cl-b v i e = Aff-cong (λ p → sym (∂b p)) (Aff-u i)
    where
    off : ∀ {b} (j : Fin m) → b ≢ B₁ → (b , j) ≢ lab₀ m v
    off j ne e′ = ne (cong proj₁ (trans e′ e))

    module _ (p : Pt L) where
      Z Z′ : LAssign m
      Z  = ρ (set p v true)
      Z′ = ρ (set p v false)

      agree : ∀ ℓ → ℓ ≢ lab₀ m v → Z ℓ ≡ Z′ ℓ
      agree ℓ ne = trans (ρ-other p v true ℓ ne) (sym (ρ-other p v false ℓ ne))

      at-b : ∀ c → ρ (set p v c) (B₁ , i) ≡ c
      at-b c = trans (cong (ρ (set p v c)) (sym e)) (ρ-here p v c)

      ∂b : ∂ˢ F₀ v p ≡ u i (ρ p)
      ∂b = trans (∂-b Z Z′ i
        (λ j → agree (A₁ , j) (off j A≢B))
        (λ j j≢i → agree (B₁ , j) (λ e′ → j≢i (cong proj₂ (trans e′ e))))
        (cong₂ _xor_ (at-b true) (at-b false))
        (λ j → agree (C₂ , j) (off j C≢B))
        (λ j → agree (D₂ , j) (off j D≢B))
        (λ j → agree (E₃ , j) (off j E≢B))
        (λ j → agree (H₃ , j) (off j H≢B)))
        (cong₂ (λ a b → (a xor sL i) xor b)
               (ρ-other p v false (A₁ , i) (off i A≢B))
               (ρ-other p v false (D₂ , i) (off i D≢B)))

  T-clf₀ : ∀ v → T₀ v ≡ true → Clifᶜ (phase (at0 (HS g s))) v
  T-clf₀ v e = Cl⇒Clif′ vt₀ v
    (Cl-b v (proj₂ (lab₀ m v)) (is-b (lab₀ m v) e))


  ----------------------------------------------------------------------
  -- The sum over b, one coordinate at a time

  sF₀ : Pt L → ℤ
  sF₀ p = sgn (F₀ p)

  -- The labels with D's b cleared.

  clrZ : (Fin m → Bool) → LAssign m → LAssign m
  clrZ D Z ℓ = if inB D ℓ then false else Z ℓ

  private
    inB-cong : ∀ {D D′ : Fin m → Bool} → (∀ i → D i ≡ D′ i) →
               ∀ ℓ → inB D ℓ ≡ inB D′ ℓ
    inB-cong h (A₁ , i) = refl
    inB-cong h (B₁ , i) = h i
    inB-cong h (C₂ , i) = refl
    inB-cong h (D₂ , i) = refl
    inB-cong h (E₃ , i) = refl
    inB-cong h (H₃ , i) = refl

    inB-false : ∀ ℓ → inB (λ _ → false) ℓ ≡ false
    inB-false (A₁ , i) = refl
    inB-false (B₁ , i) = refl
    inB-false (C₂ , i) = refl
    inB-false (D₂ , i) = refl
    inB-false (E₃ , i) = refl
    inB-false (H₃ , i) = refl

  -- I is the indicator of the equations of D.

  Good : (Fin m → Bool) → (LAssign m → ℤ) → Set
  Good D I =
    (∀ Z → (I Z ≡ 0ℤ) ⊎ ((I Z ≡ 1ℤ) × (∀ i → D i ≡ true → u i Z ≡ false))) ×
    (∀ Z → (∀ i → D i ≡ true → u i Z ≡ false) → I Z ≡ 1ℤ)

  -- After summing over D's b: 2^e times that indicator times the sign
  -- with D's b cleared.

  S : (Fin m → Bool) → Set
  S D = Σ ℕ λ e → Σ (LAssign m → ℤ) λ I → Good D I ×
        (∀ p → Σ[ Tᴮ D ] sF₀ p ≡
               (+ (2 ℕ^ e)) * (I (ρ p) * sgn (Fblk (clrZ D (ρ p)))))

  -- An indicator of equations reads only the equations.

  I-resp : ∀ {D I} → Good D I → ∀ Z Z′ → (∀ i → u i Z ≡ u i Z′) → I Z ≡ I Z′
  I-resp {D} {I} (P1 , P2) Z Z′ h = go (P1 Z) (P1 Z′)
    where
    go : (I Z ≡ 0ℤ) ⊎ ((I Z ≡ 1ℤ) × (∀ i → D i ≡ true → u i Z ≡ false)) →
         (I Z′ ≡ 0ℤ) ⊎ ((I Z′ ≡ 1ℤ) × (∀ i → D i ≡ true → u i Z′ ≡ false)) →
         I Z ≡ I Z′
    go (inj₂ (e1 , all)) _ =
      trans e1 (sym (P2 Z′ (λ i di → trans (sym (h i)) (all i di))))
    go (inj₁ e0) (inj₁ e0′) = trans e0 (sym e0′)
    go (inj₁ e0) (inj₂ (e1′ , all′)) = ⊥-elim (1≢0 (trans
      (sym (P2 Z (λ i di → trans (h i) (all′ i di)))) e0))

  S-resp : ∀ {D D′} → (∀ i → D i ≡ D′ i) → S D → S D′
  S-resp {D} {D′} h (e , I , (P1 , P2) , eq) = e , I , (P1′ , P2′) , eq′
    where
    P1′ : ∀ Z → (I Z ≡ 0ℤ) ⊎ ((I Z ≡ 1ℤ) × (∀ i → D′ i ≡ true → u i Z ≡ false))
    P1′ Z with P1 Z
    ... | inj₁ e0         = inj₁ e0
    ... | inj₂ (e1 , all) = inj₂ (e1 , λ i d′i → all i (trans (h i) d′i))

    P2′ : ∀ Z → (∀ i → D′ i ≡ true → u i Z ≡ false) → I Z ≡ 1ℤ
    P2′ Z all′ = P2 Z (λ i di → all′ i (trans (sym (h i)) di))

    eq′ : ∀ p → Σ[ Tᴮ D′ ] sF₀ p ≡
                (+ (2 ℕ^ e)) * (I (ρ p) * sgn (Fblk (clrZ D′ (ρ p))))
    eq′ p = trans (Σ-congᵀ (λ v → inB-cong (λ i → sym (h i)) (lab₀ m v)) sF₀ p)
      (trans (eq p) (cong (λ b → (+ (2 ℕ^ e)) * (I (ρ p) * sgn b))
        (Fblk-cong (λ ℓ → cong (λ c → if c then false else ρ p ℓ)
                               (inB-cong h ℓ)))))

  -- None summed: the sign itself.

  S-base : S (λ _ → false)
  S-base = 0 , (λ _ → 1ℤ) , ((λ Z → inj₂ (refl , λ i ())) , (λ Z _ → refl)) ,
           eq₀
    where
    eq₀ : ∀ p → Σ[ Tᴮ (λ _ → false) ] sF₀ p ≡
                (+ (2 ℕ^ 0)) * (1ℤ * sgn (Fblk (clrZ (λ _ → false) (ρ p))))
    eq₀ p = trans (Σ-none (Tᴮ (λ _ → false)) (λ v → inB-false (lab₀ m v)) sF₀ p)
      (sym (trans (*-identityˡ (1ℤ * sgn (Fblk (clrZ (λ _ → false) (ρ p)))))
        (trans (*-identityˡ (sgn (Fblk (clrZ (λ _ → false) (ρ p)))))
          (cong sgn (Fblk-cong (λ ℓ → cong (λ c → if c then false else ρ p ℓ)
                                           (inB-false ℓ)))))))

  -- One more: b_i's derivative is u_i, so summing over b_i doubles the
  -- sign where u_i = 0 and cancels it elsewhere.

  S-step : ∀ d i → d i ≡ false → S d → S (d [ i ≔ true ])
  S-step d i di (e , I , (P1 , P2) , eq) = suc e , I′ , (P1′ , P2′) , eq′
    where
    d′ : Fin m → Bool
    d′ = d [ i ≔ true ]

    t : Fin L
    t = pos₀ m (B₁ , i)

    lab-t : lab₀ m t ≡ (B₁ , i)
    lab-t = lab₀-pos₀ m (B₁ , i)

    I′ : LAssign m → ℤ
    I′ Z = zero? (u i Z) * I Z

    d′-off : ∀ j → j ≢ i → d′ j ≡ d j
    d′-off j j≢i = ≔-there d true j≢i

    d′-at : d′ i ≡ true
    d′-at = ≔-here d i true

    P1′ : ∀ Z → (I′ Z ≡ 0ℤ) ⊎
                ((I′ Z ≡ 1ℤ) × (∀ j → d′ j ≡ true → u j Z ≡ false))
    P1′ Z = go (u i Z) refl
      where
      go : ∀ b → u i Z ≡ b →
           (I′ Z ≡ 0ℤ) ⊎ ((I′ Z ≡ 1ℤ) × (∀ j → d′ j ≡ true → u j Z ≡ false))
      go true  ui = inj₁ (trans (cong (λ c → zero? c * I Z) ui) (*-zeroˡ (I Z)))
      go false ui with P1 Z
      ... | inj₁ e0 = inj₁ (trans (cong (λ c → zero? c * I Z) ui)
                                  (trans (*-identityˡ (I Z)) e0))
      ... | inj₂ (e1 , all) = inj₂ (trans (cong (λ c → zero? c * I Z) ui)
                                          (trans (*-identityˡ (I Z)) e1) , all′)
        where
        all′ : ∀ j → d′ j ≡ true → u j Z ≡ false
        all′ j d′j = pick (j ≟ i)
          where
          pick : Dec (j ≡ i) → u j Z ≡ false
          pick (yes j≡i) = subst (λ x → u x Z ≡ false) (sym j≡i) ui
          pick (no j≢i)  = all j (trans (sym (d′-off j j≢i)) d′j)

    P2′ : ∀ Z → (∀ j → d′ j ≡ true → u j Z ≡ false) → I′ Z ≡ 1ℤ
    P2′ Z all′ = trans (cong (λ c → zero? c * I Z) (all′ i d′-at))
      (trans (*-identityˡ (I Z)) (P2 Z (λ j dj → all′ j (more j dj))))
      where
      more : ∀ j → d j ≡ true → d′ j ≡ true
      more j dj = pick (j ≟ i)
        where
        pick : Dec (j ≡ i) → d′ j ≡ true
        pick (yes j≡i) = subst (λ x → d′ x ≡ true) (sym j≡i) d′-at
        pick (no j≢i)  = trans (d′-off j j≢i) dj

    -- The witness grows by b_i.

    inB-off : ∀ ℓ → ℓ ≢ (B₁ , i) → inB d′ ℓ ≡ inB d ℓ
    inB-off (A₁ , j) ne = refl
    inB-off (B₁ , j) ne = d′-off j (λ j≡i → ne (cong (B₁ ,_) j≡i))
    inB-off (C₂ , j) ne = refl
    inB-off (D₂ , j) ne = refl
    inB-off (E₃ , j) ne = refl
    inB-off (H₃ , j) ne = refl

    T-step : ∀ v → Tᴮ d′ v ≡ setᵀ (Tᴮ d) t true v
    T-step v = sym (setᵀ-agree (Tᴮ d) (Tᴮ d′) t true
      (trans (cong (inB d′) lab-t) d′-at)
      (λ w w≢t → inB-off (lab₀ m w) (λ e′ →
        w≢t (trans (sym (pos₀-lab₀ m w)) (cong (pos₀ m) e′))))
      v)

    Tdt : Tᴮ d t ≡ false
    Tdt = trans (cong (inB d) lab-t) di

    -- The labels with b_i set to c, D's b cleared.

    Zc : Pt L → Bool → LAssign m
    Zc p c = clrZ d (ρ (set p t c))

    off-t : ∀ ℓ → ℓ ≢ (B₁ , i) → ℓ ≢ lab₀ m t
    off-t ℓ ne e′ = ne (trans e′ lab-t)

    Zc-agree : ∀ p ℓ → ℓ ≢ (B₁ , i) → Zc p true ℓ ≡ Zc p false ℓ
    Zc-agree p ℓ ne = cong (λ b → if inB d ℓ then false else b)
      (trans (ρ-other p t true ℓ (off-t ℓ ne))
             (sym (ρ-other p t false ℓ (off-t ℓ ne))))

    Zc-at : ∀ p c → Zc p c (B₁ , i) ≡ c
    Zc-at p c = trans
      (cong (λ b → if b then false else ρ (set p t c) (B₁ , i)) di)
      (trans (cong (ρ (set p t c)) (sym lab-t)) (ρ-here p t c))

    u-same : ∀ p c j → u j (ρ (set p t c)) ≡ u j (ρ p)
    u-same p c j = cong₂ (λ a b → (a xor sL j) xor b)
      (ρ-other p t c (A₁ , j) (off-t (A₁ , j) (blk≢ A≢B)))
      (ρ-other p t c (D₂ , j) (off-t (D₂ , j) (blk≢ D≢B)))

    -- Clearing b_i as well is setting it to 0.

    clr-step : ∀ p ℓ → clrZ d′ (ρ p) ℓ ≡ Zc p false ℓ
    clr-step p (A₁ , j) =
      sym (ρ-other p t false (A₁ , j) (off-t (A₁ , j) (blk≢ A≢B)))
    clr-step p (B₁ , j) = pick (j ≟ i)
      where
      pick : Dec (j ≡ i) → clrZ d′ (ρ p) (B₁ , j) ≡ Zc p false (B₁ , j)
      pick (yes j≡i) = subst
        (λ x → clrZ d′ (ρ p) (B₁ , x) ≡ Zc p false (B₁ , x))
        (sym j≡i)
        (trans (cong (λ b → if b then false else ρ p (B₁ , i)) d′-at)
               (sym (Zc-at p false)))
      pick (no j≢i)  = trans
        (cong (λ b → if b then false else ρ p (B₁ , j)) (d′-off j j≢i))
        (cong (λ b → if d j then false else b)
              (sym (ρ-other p t false (B₁ , j)
                     (off-t (B₁ , j) (λ e′ → j≢i (cong proj₂ e′))))))
    clr-step p (C₂ , j) =
      sym (ρ-other p t false (C₂ , j) (off-t (C₂ , j) (blk≢ C≢B)))
    clr-step p (D₂ , j) =
      sym (ρ-other p t false (D₂ , j) (off-t (D₂ , j) (blk≢ D≢B)))
    clr-step p (E₃ , j) =
      sym (ρ-other p t false (E₃ , j) (off-t (E₃ , j) (blk≢ E≢B)))
    clr-step p (H₃ , j) =
      sym (ρ-other p t false (H₃ , j) (off-t (H₃ , j) (blk≢ H≢B)))

    -- Flipping b_i flips the phase by u_i.

    flip-b : ∀ p → Fblk (Zc p true) ≡ Fblk (Zc p false) xor u i (ρ p)
    flip-b p = solve-xor (trans (∂-b (Zc p true) (Zc p false) i
        (λ j → Zc-agree p (A₁ , j) (blk≢ A≢B))
        (λ j j≢i → Zc-agree p (B₁ , j) (λ e′ → j≢i (cong proj₂ e′)))
        (cong₂ _xor_ (Zc-at p true) (Zc-at p false))
        (λ j → Zc-agree p (C₂ , j) (blk≢ C≢B))
        (λ j → Zc-agree p (D₂ , j) (blk≢ D≢B))
        (λ j → Zc-agree p (E₃ , j) (blk≢ E≢B))
        (λ j → Zc-agree p (H₃ , j) (blk≢ H≢B)))
      (u-same p false i))

    I-same : ∀ p c → I (ρ (set p t c)) ≡ I (ρ p)
    I-same p c = I-resp (P1 , P2) (ρ (set p t c)) (ρ p) (u-same p c)

    P : ℤ
    P = + (2 ℕ^ e)

    eq′ : ∀ p → Σ[ Tᴮ d′ ] sF₀ p ≡
                (+ (2 ℕ^ suc e)) * (I′ (ρ p) * sgn (Fblk (clrZ d′ (ρ p))))
    eq′ p = trans (Σ-congᵀ T-step sF₀ p)
      (trans (Σ-grow (Tᴮ d) t Tdt sF₀ p)
        (trans (cong₂ _+_ (eq (set p t false)) (eq (set p t true)))
          (trans (cong₂ (λ a b → P * (a * sgn (Fblk (Zc p false))) +
                                 P * (b * sgn (Fblk (Zc p true))))
                        (I-same p false) (I-same p true))
            (trans (cong (λ x → P * (I (ρ p) * sgn (Fblk (Zc p false))) +
                                P * (I (ρ p) * sgn x)) (flip-b p))
              (trans (comb P (I (ρ p)) (Fblk (Zc p false)) (u i (ρ p)))
                (cong₂ (λ a x → a * ((zero? (u i (ρ p)) * I (ρ p)) * sgn x))
                       (sym (pos-* 2 (2 ℕ^ e)))
                       (sym (Fblk-cong (clr-step p)))))))))

  -- All summed.

  S-all : S (λ _ → true)
  S-all = Sweep.all S S-resp S-step S-base


  ----------------------------------------------------------------------
  -- The stabilizer shape

  -- At b = 0 and d = a ⊕ s_L the two copies of g cancel.

  Zb : LAssign m → LAssign m
  Zb = clrZ (λ _ → true)

  Rq : LAssign m → Bool
  Rq Z = ((T₂ (Zb Z) xor (T₃ (Zb Z) xor T₄ (Zb Z))) xor T₆ (Zb Z)) xor
         (T₇ (Zb Z) xor T₈ (Zb Z))

  Rq-eq : ∀ Z → (∀ i → u i Z ≡ false) → Fblk (Zb Z) ≡ Rq Z
  Rq-eq Z all = trans
    (cong (λ t → (((T₁ (Zb Z) xor T₂ (Zb Z)) xor (T₃ (Zb Z) xor T₄ (Zb Z))) xor
                  (t xor T₆ (Zb Z))) xor (T₇ (Zb Z) xor T₈ (Zb Z)))
          (sym t₁₅))
    (cong (_xor (T₇ (Zb Z) xor T₈ (Zb Z)))
          (drop (T₁ (Zb Z)) (T₂ (Zb Z)) (T₃ (Zb Z) xor T₄ (Zb Z)) (T₆ (Zb Z))))
    where
    t₁₅ : T₁ (Zb Z) ≡ T₅ (Zb Z)
    t₁₅ = boolᴾ-resp g _ _ (λ i → xor-false′ (all i))

  -- It is a sum of inner products of affine vectors.

  Quad-R : Quad (λ x → Rq (ρ x))
  Quad-R = Quad-xor (Quad-xor (Quad-xor q₂ (Quad-xor q₃ q₄)) q₆)
                    (Quad-xor q₇ q₈)
    where
    lk : ∀ b (i : Fin m) → Aff (λ (x : Pt L) → lookup x (pos₀ m (b , i)))
    lk b i = Aff-lookup (pos₀ m (b , i))

    q₂ : Quad (λ x → T₂ (Zb (ρ x)))
    q₂ = Quad-dot {U = λ x → Zb (ρ x) ‹ A₁ › ⊕ᵃ sL}
                  {V = λ x → Zb (ρ x) ‹ B₁ › ⊕ᵃ sR}
                  (λ i → Aff-xor (lk A₁ i) (Aff-const (sL i)))
                  (λ i → Aff-const (sR i))

    q₃ : Quad (λ x → T₃ (Zb (ρ x)))
    q₃ = Quad-dot {U = λ x → Zb (ρ x) ‹ A₁ ›} {V = λ x → Zb (ρ x) ‹ C₂ ›}
                  (lk A₁) (lk C₂)

    q₄ : Quad (λ x → T₄ (Zb (ρ x)))
    q₄ = Quad-dot {U = λ x → Zb (ρ x) ‹ B₁ ›} {V = λ x → Zb (ρ x) ‹ D₂ ›}
                  (λ i → Aff-const false) (lk D₂)

    q₆ : Quad (λ x → T₆ (Zb (ρ x)))
    q₆ = Quad-dot {U = λ x → Zb (ρ x) ‹ C₂ ›} {V = λ x → Zb (ρ x) ‹ D₂ ›}
                  (lk C₂) (lk D₂)

    q₇ : Quad (λ x → T₇ (Zb (ρ x)))
    q₇ = Quad-dot {U = λ x → Zb (ρ x) ‹ C₂ ›} {V = λ x → Zb (ρ x) ‹ E₃ ›}
                  (lk C₂) (lk E₃)

    q₈ : Quad (λ x → T₈ (Zb (ρ x)))
    q₈ = Quad-dot {U = λ x → Zb (ρ x) ‹ D₂ ›} {V = λ x → Zb (ρ x) ‹ H₃ ›}
                  (lk D₂) (lk H₃)

  -- The equations, as a list.

  es₀ : List (Pt L → Bool)
  es₀ = map (λ i x → u i (ρ x)) (allFin m)

  private
    All-u : ∀ (is : List (Fin m)) → All Aff (map (λ i x → u i (ρ x)) is)
    All-u []       = []
    All-u (i ∷ is) = Aff-u i ∷ All-u is

    ind-01 : ∀ (is : List (Fin m)) x →
             (ind (map (λ i x → u i (ρ x)) is) x ≡ 0ℤ) ⊎
             ((ind (map (λ i x → u i (ρ x)) is) x ≡ 1ℤ) ×
              (∀ i → i ∈ is → u i (ρ x) ≡ false))
    ind-01 []       x = inj₂ (refl , λ i ())
    ind-01 (i ∷ is) x = go (u i (ρ x)) refl (ind-01 is x)
      where
      R : ℤ
      R = ind (map (λ i x → u i (ρ x)) is) x

      go : ∀ b → u i (ρ x) ≡ b →
           (R ≡ 0ℤ) ⊎ ((R ≡ 1ℤ) × (∀ j → j ∈ is → u j (ρ x) ≡ false)) →
           (zero? (u i (ρ x)) * R ≡ 0ℤ) ⊎
           ((zero? (u i (ρ x)) * R ≡ 1ℤ) ×
            (∀ j → j ∈ (i ∷ is) → u j (ρ x) ≡ false))
      go true  e _ = inj₁ (trans (cong (λ c → zero? c * R) e) (*-zeroˡ R))
      go false e (inj₁ r0) =
        inj₁ (trans (cong (λ c → zero? c * R) e) (trans (*-identityˡ R) r0))
      go false e (inj₂ (r1 , all)) =
        inj₂ (trans (cong (λ c → zero? c * R) e) (trans (*-identityˡ R) r1) ,
              λ { j (here refl) → e ; j (there q) → all j q })

    ind-all : ∀ (is : List (Fin m)) x → (∀ i → u i (ρ x) ≡ false) →
              ind (map (λ i x → u i (ρ x)) is) x ≡ 1ℤ
    ind-all []       x h = refl
    ind-all (i ∷ is) x h =
      cong₂ (λ c r → zero? c * r) (h i) (ind-all is x h)

  T-sl₀ : SL (Σ[ T₀ ] sF₀)
  T-sl₀ = sl 0 (+ (2 ℕ^ e)) es₀ (λ x → Rq (ρ x)) (All-u (allFin m)) Quad-R form
    where
    e = proj₁ S-all
    I = proj₁ (proj₂ S-all)
    P1 = proj₁ (proj₁ (proj₂ (proj₂ S-all)))
    P2 = proj₂ (proj₁ (proj₂ (proj₂ S-all)))
    eq = proj₂ (proj₂ (proj₂ S-all))

    P : ℤ
    P = + (2 ℕ^ e)

    form : ∀ x → (+ (2 ℕ^ 0)) * Σ[ T₀ ] sF₀ x ≡ P * (ind es₀ x * sgn (Rq (ρ x)))
    form x = trans (*-identityˡ (Σ[ T₀ ] sF₀ x))
      (trans (eq x) (go (P1 (ρ x)) (ind-01 (allFin m) x)))
      where
      X : Bool
      X = Fblk (clrZ (λ _ → true) (ρ x))

      go : (I (ρ x) ≡ 0ℤ) ⊎ ((I (ρ x) ≡ 1ℤ) ×
                             (∀ i → true ≡ true → u i (ρ x) ≡ false)) →
           (ind es₀ x ≡ 0ℤ) ⊎ ((ind es₀ x ≡ 1ℤ) ×
                                (∀ i → i ∈ allFin m → u i (ρ x) ≡ false)) →
           P * (I (ρ x) * sgn X) ≡ P * (ind es₀ x * sgn (Rq (ρ x)))
      go (inj₁ i0) (inj₁ n0) =
        trans (cong (λ a → P * (a * sgn X)) i0)
              (cong (λ a → P * (a * sgn (Rq (ρ x)))) (sym n0))
      go (inj₁ i0) (inj₂ (n1 , all)) = ⊥-elim (1≢0 (trans
        (sym (P2 (ρ x) (λ i _ → all i (∈-allFin i)))) i0))
      go (inj₂ (i1 , all)) (inj₁ n0) = ⊥-elim (1≢0 (trans
        (sym (ind-all (allFin m) x (λ i → all i refl))) n0))
      go (inj₂ (i1 , all)) (inj₂ (n1 , _)) =
        cong₂ (λ a b → P * (a * sgn b)) (trans i1 (sym n1))
              (Rq-eq (ρ x) (λ i → all i refl))


  ----------------------------------------------------------------------
  -- The invariant holds

  inv₀ : Inv (at0 (HS g s))
  inv₀ = record
    { F     = F₀
    ; G     = G₀
    ; vt    = vt₀
    ; inj   = inj₀
    ; T     = T₀
    ; T-int = T-int₀
    ; T-clf = T-clf₀
    ; T-sl  = T-sl₀
    }
