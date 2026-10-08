------------------------------------------------------------------------
-- Presentations of groups
--
-- An admissible step applies while path variables remain
--
-- The progress half of PathSum.HiddenShift.Positive: a path-sum that
-- satisfies PathSum.HiddenShift.Positive.Invariant's Inv, is
-- equivalent to the specification |x⟩ ↦ |s⟩ and still has a path
-- variable admits a step of PathSum.HiddenShift.Positive.Class's
-- class (progress: it is not Maximal).  The step is found as follows.
--
-- * Some path variable is internal.  Otherwise the outputs determine
--   the path (Inv's inj), and with a path variable there would be two
--   paths reaching different outputs, both with amplitude ±1
--   (PathSum.HiddenShift.Positive.Amplitude's endgame).
-- * Some internal variable y_j is Clifford: one in the witness T if T
--   is not empty; if it is, the sum over T is (-1)^F itself, so that
--   (-1)^F is stabilizer-like, F differs from a quadratic function by a
--   constant (sl⇒quad), and every variable is Clifford.
-- * At such a y_j the derivative of F is affine, c ⊕ s·y (at-var).  If
--   s = 0 and c = 1, F flips with y_j and every amplitude vanishes --
--   impossible; if s = 0 and c = 0, [Elim] applies at y_j, the
--   amplitudes being even and so the normalisation at least 2
--   (elim-at).  Otherwise [HH] at y_j solves y_j's derivative for a
--   variable y_i of s: an internal Clifford one if there is one, else an
--   internal one, else any (choose).  That choice is what makes the
--   step admissible (hh-at): the quotient, the rest of c ⊕ s·y, mentions
--   an internal variable only if y_i is internal (OutSafe), and an
--   internal Clifford variable only if y_i is internal Clifford, so
--   that substituting for y_i keeps it Clifford (CliffSafe; Boolean's
--   Cl-hh).
--
-- The quotient is the lift of a Z₂-linear form, so every step found
-- here is one of the linear rules (lemma 4.3's) at some variable.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Positive.Progress (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-identityʳ; xor-same)
  renaming (_≟_ to _≟ᵇ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (any?; _≟_)
open import Data.Fin.Subset using (Subset; _∈_; _⊆_) renaming (⊥ to ∅)
open import Data.Fin.Subset.Properties using (∉⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _*_; _-_; ∣_∣)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using
  (*-identityˡ; *-identityʳ; *-zeroˡ; *-zeroʳ; *-assoc; *-cancelˡ-≡)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using
  (zero; suc; _≤_; s≤s; z≤n; NonZero; ≢-nonZero⁻¹)
  renaming (_^_ to _ℕ^_)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Product.Base using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using ([]; _∷_; lookup; tabulate; insertAt; removeAt)
open import Data.Vec.Properties using (lookup∘tabulate; []=⇒lookup)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋; _×?_)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Denotation M₀ using (Assign; _≋_)
open import PathSum.HiddenShift M₀ using (specᴾ)
open import PathSum.HiddenShift.Positive.Amplitude M₀ using (module Spec)
open import PathSum.HiddenShift.Positive.Boolean
open import PathSum.HiddenShift.Positive.Class M₀ using
  (Int; Clifᶜ; Int?; Clifᶜ?; OutSafe; CliffSafe; Maximal)
open import PathSum.HiddenShift.Positive.Invariant M₀ using
  (Inv; module HHᴵ; Int⇒Indep; Clif⇒Cl; Cl⇒Clif)
open import PathSum.HiddenShift.Positive.Stabilizer using
  (SL; sl; ind; zero?; Σ-none; SL-cong; sgn-xor)
open import PathSum.HiddenShift.Positive.Values M₀ using
  (VTracks; tracks; front-vtracks; tab-insertᵃ; quot-val; ∂ᵢ)
open import PathSum.HiddenShift.Track M₀ using (hh-premise)
open import PathSum.Linear using (par; par-⊥; eval-liftXor)
open import PathSum.Polynomial using
  (Poly; y[_]; sgn; liftXor; eval; 0ᴾ; μ; _+ᴾ_; _·ᴾ_; _≈[_]_; 1ᵐ; _≟ᵐ_;
   _⊆ᵐ_; _⊆ᵐ?_)
open import PathSum.Polynomial.Boolean using
  (BoolValued; BoolValued-liftXor; ≈-from-values)
open import PathSum.Polynomial.Product using (eval-0ᴾ)
open import PathSum.Polynomial.Properties using (eval-cong)
open import PathSum.Polynomial.Substitution using (Absent)
open import PathSum.Reorder using (insertᵃ; front; _/ʸ_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Full M using (_⟶ᶠ_; elimAtᶠ; hhAtᶠ)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½)

private
  variable
    N n k m : ℕ


------------------------------------------------------------------------
-- Small facts

private
  t≢f : true ≢ false
  t≢f ()

  flip-of : ∀ {a b} → a xor b ≡ true → a ≡ not b
  flip-of {false} {true}  _ = refl
  flip-of {true}  {false} _ = refl

  same-of : ∀ {a b} → a xor b ≡ false → a ≡ b
  same-of {false} {false} _ = refl
  same-of {true}  {true}  _ = refl

  bits3 : ∀ a b c → a xor (b xor c) ≡ c xor (a xor b)
  bits3 false false false = refl
  bits3 false false true  = refl
  bits3 false true  false = refl
  bits3 false true  true  = refl
  bits3 true  false false = refl
  bits3 true  false true  = refl
  bits3 true  true  false = refl
  bits3 true  true  true  = refl

  solve-xor : ∀ {a b e} → a xor b ≡ e → a ≡ b xor e
  solve-xor {false} {false} refl = refl
  solve-xor {false} {true}  refl = refl
  solve-xor {true}  {false} refl = refl
  solve-xor {true}  {true}  refl = refl

  sgn-sq : ∀ b → sgn b * sgn b ≡ 1ℤ
  sgn-sq false = refl
  sgn-sq true  = refl

  sgn-inj : ∀ {a b} → sgn a ≡ sgn b → a ≡ b
  sgn-inj {false} {false} _ = refl
  sgn-inj {true}  {true}  _ = refl
  sgn-inj {false} {true}  ()
  sgn-inj {true}  {false} ()

  -- A Boolean that is not true is false.
  not-true : ∀ {b} → ¬ (b ≡ true) → b ≡ false
  not-true {false} _ = refl
  not-true {true}  h = ⊥-elim (h refl)

  -- A parity is an inner product.
  par-dot : (s : Subset m) (y : Assign m) → par s y ≡ dotᵥ s (tabulate y)
  par-dot []          y = refl
  par-dot (true  ∷ s) y = cong (y zero xor_) (par-dot s (λ i → y (suc i)))
  par-dot (false ∷ s) y = par-dot s (λ i → y (suc i))

-- The lift of a linear form does not mention a variable outside it.

Absent-liftXor : (c : Bool) (s : Subset m) (v : Fin m) →
                 lookup s v ≡ false → Absent {n} y[ v ] (liftXor c (∅ , s))
Absent-liftXor c s v off (α , β) v∈β = go ((α , β) ≟ᵐ 1ᵐ) ((α , β) ⊆ᵐ? (∅ , s))
  where
  go : ∀ {A B : ℤ} (d₁ : Dec ((α , β) ≡ 1ᵐ))
       (d₂ : Dec ((α , β) ⊆ᵐ (∅ , s))) →
       (if ⌊ d₁ ⌋ then A else (if ⌊ d₂ ⌋ then B else 0ℤ)) ≡ 0ℤ
  go (yes e)  _              = ⊥-elim (∉⊥ (subst (λ γ → v ∈ proj₂ γ) e v∈β))
  go (no _)   (yes (_ , β⊆s)) =
    ⊥-elim (t≢f (trans (sym ([]=⇒lookup (β⊆s v∈β))) off))
  go (no _)   (no _)         = refl


------------------------------------------------------------------------
-- A stabilizer-like sign is a quadratic phase

sl⇒quad : (F : Pt n → Bool) → SL (λ x → sgn (F x)) → Quad F
sl⇒quad {n} F (sl d c es R affs quadR form) =
  Quad-cong (λ x → sym (shape x))
            (Quad-xor quadR (Aff⇒Quad (Aff-const (F 0ᵖ xor R 0ᵖ))))
  where
  P : ℤ
  P = + (2 ℕ^ d)

  instance
    P≢0 : NonZero (2 ℕ^ d)
    P≢0 = m^n≢0 2 d

  ind-01 : ∀ (es : List (Pt n → Bool)) x → (ind es x ≡ 0ℤ) ⊎ (ind es x ≡ 1ℤ)
  ind-01 []       x = inj₂ refl
  ind-01 (e ∷ es) x = go (e x) (ind-01 es x)
    where
    go : ∀ b → (ind es x ≡ 0ℤ) ⊎ (ind es x ≡ 1ℤ) →
         (zero? b * ind es x ≡ 0ℤ) ⊎ (zero? b * ind es x ≡ 1ℤ)
    go true  _        = inj₁ (*-zeroˡ (ind es x))
    go false (inj₁ e) = inj₁ (trans (*-identityˡ (ind es x)) e)
    go false (inj₂ e) = inj₂ (trans (*-identityˡ (ind es x)) e)

  -- 2^d (-1)^b is never 0.
  P-sgn : ∀ b → P * sgn b ≢ 0ℤ
  P-sgn b e = ≢-nonZero⁻¹ (2 ℕ^ d) (cong ∣_∣ (trans (sym (*-identityʳ P))
    (trans (cong (P *_) (sym (sgn-sq b)))
      (trans (sym (*-assoc P (sgn b) (sgn b)))
        (trans (cong (_* sgn b) e) (*-zeroˡ (sgn b)))))))

  one : ∀ x → ind es x ≡ 1ℤ
  one x with ind-01 es x
  ... | inj₂ e = e
  ... | inj₁ e = ⊥-elim (P-sgn (F x) (trans (form x)
        (trans (cong (λ t → c * (t * sgn (R x))) e) (*-zeroʳ c))))

  key : ∀ x → P * (sgn (F x) * sgn (R x)) ≡ c
  key x = trans (sym (*-assoc P (sgn (F x)) (sgn (R x))))
    (trans (cong (_* sgn (R x))
             (trans (form x) (cong (λ t → c * (t * sgn (R x))) (one x))))
      (trans (cong (_* sgn (R x)) (cong (c *_) (*-identityˡ (sgn (R x)))))
        (trans (*-assoc c (sgn (R x)) (sgn (R x)))
          (trans (cong (c *_) (sgn-sq (R x))) (*-identityʳ c)))))

  shape : ∀ x → F x ≡ R x xor (F 0ᵖ xor R 0ᵖ)
  shape x = solve-xor (sgn-inj (trans (sgn-xor (F x) (R x))
    (trans (*-cancelˡ-≡ P _ _ (trans (key x) (sym (key 0ᵖ))))
           (sym (sgn-xor (F 0ᵖ) (R 0ᵖ))))))


------------------------------------------------------------------------
-- [Elim] where F does not depend on y_j

-- A derivative that vanishes makes the quotient 0 modulo 1.

quot-zero : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
            {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
            (j : Fin (suc m)) → (∀ z → ∂ᵢ F j z ≡ false) →
            (phase ξ /ʸ j) ≈[ pow M ] 0ᴾ
quot-zero {ξ = ξ} {F} tr j flat = ≈-from-values (phase ξ /ʸ j) 0ᴾ λ x y →
  subst (pow M ∣_)
    (cong₂ _-_ (eval-cong (phase ξ /ʸ j) {x} {x} {lookup (tabulate y)} {y}
                          (λ _ → refl) (lookup∘tabulate y))
               (trans (cong (λ b → ½ * [ b ]ᶻ) (flat (tabulate y)))
                      (trans (*-zeroʳ ½) (sym (eval-0ᴾ x y)))))
    (quot-val tr j x (tabulate y))

-- The normalisation [Elim] consumes is there: [Elim] at y_j applies.

elim-at : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
          {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G → 2 ≤ k →
          (j : Fin (suc m)) → Int ξ j → (∀ z → ∂ᵢ F j z ≡ false) →
          Maximal ξ → ⊥
elim-at {ξ = ξ} tr (s≤s (s≤s z≤n)) j int flat mx =
  mx (elimAtᶠ ξ j (quot-zero tr j flat) int) tt


------------------------------------------------------------------------
-- [HH] where F's derivative in y_j is c ⊕ s·y with s ≠ 0

-- The variable of s that [HH] solves for: an internal Clifford one if
-- s has one, else an internal one if s has one, else any.  What the
-- step needs of the choice is recorded.

record Choice (χ : PathSum N k (suc (suc m))) (sv : Pt (suc m)) : Set where
  field
    i   : Fin (suc m)
    svi : lookup sv i ≡ true
    os  : ∀ v → Int χ (suc v) → lookup sv v ≡ true → Int χ (suc i)
    cs  : ∀ v → Int χ (suc v) → Clifᶜ (phase χ) (suc v) →
          lookup sv v ≡ true → Clifᶜ (phase χ) (suc i)

choose : (χ : PathSum N k (suc (suc m))) (sv : Pt (suc m))
         (i₀ : Fin (suc m)) → lookup sv i₀ ≡ true → Choice χ sv
choose χ sv i₀ e₀ = first (any? (λ u →
  (lookup sv u ≟ᵇ true) ×? (Int? χ (suc u) ×? Clifᶜ? (phase χ) (suc u))))
  where
  second : ¬ (∃ λ u → lookup sv u ≡ true × Int χ (suc u) ×
                      Clifᶜ (phase χ) (suc u)) →
           Dec (∃ λ u → lookup sv u ≡ true × Int χ (suc u)) → Choice χ sv
  second ¬P₁ (yes (i , svi , int)) = record
    { i = i ; svi = svi ; os = λ _ _ _ → int
    ; cs = λ v int′ cl e → ⊥-elim (¬P₁ (v , e , int′ , cl)) }
  second ¬P₁ (no ¬P₂) = record
    { i = i₀ ; svi = e₀
    ; os = λ v int e → ⊥-elim (¬P₂ (v , e , int))
    ; cs = λ v int cl e → ⊥-elim (¬P₁ (v , e , int , cl)) }

  first : Dec (∃ λ u → lookup sv u ≡ true × Int χ (suc u) ×
                      Clifᶜ (phase χ) (suc u)) → Choice χ sv
  first (yes (i , svi , int , cl)) = record
    { i = i ; svi = svi ; os = λ _ _ _ → int ; cs = λ _ _ _ _ → cl }
  first (no ¬P₁) =
    second ¬P₁ (any? (λ u → (lookup sv u ≟ᵇ true) ×? Int? χ (suc u)))

-- The step: [HH] at y_j with y_i ← c ⊕ (s without y_i)·y, i chosen as
-- above, is admissible.

hh-at : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
        {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
        (j : Fin (suc m)) → Int ξ j → (c : Bool) (sv : Pt m) →
        (∀ z → ∂ᵢ F j z ≡ c xor dotᵥ sv z) →
        (i₀ : Fin m) → lookup sv i₀ ≡ true → Maximal ξ → ⊥
hh-at {N = N} {m = suc m} {ξ = ξ} {F} {G} tr j int c sv dval i₀ e₀ mx =
  mx (hhAtᶠ ξ j i Q bQ absQ eqP int) (os′ , cs′)
  where
  χ : PathSum N _ (suc (suc m))
  χ = front j ξ

  trχ : VTracks χ (λ p → F (unfr j p)) (λ w p → G w (unfr j p))
  trχ = front-vtracks tr j

  open Choice (choose χ sv i₀ e₀)

  s₁ : Subset (suc m)
  s₁ = set sv i false

  Q : Poly N (suc m)
  Q = liftXor c (∅ , s₁)

  q₀ : Pt (suc m) → Bool
  q₀ z = c xor dotᵥ s₁ z

  bQ : BoolValued Q
  bQ = BoolValued-liftXor c (∅ , s₁)

  absQ : Absent y[ i ] Q
  absQ = Absent-liftXor c s₁ i (lookup-set-here sv i false)

  hq : ∀ x y → eval Q x y ≡ [ q₀ (tabulate y) ]ᶻ
  hq x y = trans (eval-liftXor c (∅ , s₁) x y)
    (cong (λ b → [ c xor b ]ᶻ)
          (trans (cong (_xor par s₁ y) (par-⊥ x)) (par-dot s₁ y)))

  d-val : ∀ z → ∂ᵢ F j z ≡ lookup z i xor q₀ z
  d-val z = trans (dval z)
    (trans (cong (c xor_) (trans (dotᵥ-set sv z i)
                     (cong (λ u → dotᵥ s₁ z xor (u ∧ lookup z i)) svi)))
           (bits3 c (dotᵥ s₁ z) (lookup z i)))

  dF : ∀ y → F (tabulate (insertᵃ j true y)) xor
             F (tabulate (insertᵃ j false y)) ≡ y i xor q₀ (tabulate y)
  dF y = trans (cong₂ (λ a b → F a xor F b) (tab-insertᵃ j true y)
                                            (tab-insertᵃ j false y))
    (trans (d-val (tabulate y))
           (cong (_xor q₀ (tabulate y)) (lookup∘tabulate y i)))

  eqP : (phase ξ /ʸ j) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q))
  eqP = hh-premise ξ (tracks tr) j i Q (λ y → q₀ (tabulate y)) hq dF

  open HHᴵ trχ i Q bQ absQ eqP using (q; q-indep; F″; reduct)

  -- Q mentions only variables of s other than y_i.

  present : ∀ v → ¬ Absent y[ v ] Q → lookup sv v ≡ true
  present v ¬abs = go (lookup s₁ v) refl
    where
    go : ∀ b → lookup s₁ v ≡ b → lookup sv v ≡ true
    go false e = ⊥-elim (¬abs (Absent-liftXor c s₁ v e))
    go true  e = in-s (v ≟ i)
      where
      in-s : Dec (v ≡ i) → lookup sv v ≡ true
      in-s (yes v≡i) = ⊥-elim (t≢f (trans (sym e)
        (trans (cong (lookup s₁) v≡i) (lookup-set-here sv i false))))
      in-s (no v≢i)  = trans (sym (lookup-set-there sv false v≢i)) e

  κ-present : ∀ v → κˢ v q ≡ true → lookup sv v ≡ true
  κ-present v κ = present v (λ abs → t≢f (trans (sym κ)
    (trans (cong (_xor q 0ᵖ) (indep-set {f = q} {v} (q-indep v abs) 0ᵖ true))
           (xor-same (q 0ᵖ)))))

  aq : Aff q
  aq = Aff-xor {f = ∂ᵢ F j} {g = λ p → lookup p i}
    (Aff-cong {f = λ z → c xor dotᵥ sv z} {g = ∂ᵢ F j} (λ z → sym (dval z))
              (Aff-dot c sv))
    (Aff-lookup i)

  os′ : OutSafe χ i Q
  os′ v int′ ¬abs = os v int′ (present v ¬abs)

  cs′ : CliffSafe χ i Q
  cs′ v int′ cl = Cl⇒Clif reduct v (by (v ≟ i))
    where
    by : Dec (v ≡ i) → Cl F″ v
    by (yes v≡i) = subst (Cl F″) (sym v≡i)
      (Cl-hh-self {f = λ p → F (unfr j p)} {q} i (q-indep i absQ))
    by (no v≢i)  = Cl-hh {f = λ p → F (unfr j p)} {q} aq i v v≢i
      (Clif⇒Cl trχ (suc v) cl)
      (λ κ → Clif⇒Cl trχ (suc i) (cs v int′ cl (κ-present v κ)))


------------------------------------------------------------------------
-- At an internal Clifford variable

at-var : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
         {G : Fin N → Pt (suc m) → Bool} (s : Assign N) → VTracks ξ F G →
         ξ ≋ specᴾ s → (j : Fin (suc m)) → Int ξ j → Cl F j →
         Maximal ξ → ⊥
at-var {m = m} {ξ = ξ} {F} {G} s tr eqv j int cl mx =
  by-slope (any? (λ u → lookup sv u ≟ᵇ true))
  where
  module S = Spec tr s eqv

  ad : Aff (∂ᵢ F j)
  ad = Aff-cong (λ z → cong₂ (λ a b → F a xor F b)
                             (set-insertAt z j false true)
                             (set-insertAt z j false false))
                (Aff-∘ cl (AffMap-insertAt j false))

  shape = aff-expand ad

  c : Bool
  c = proj₁ shape

  sv : Pt m
  sv = proj₁ (proj₂ shape)

  dval : ∀ z → ∂ᵢ F j z ≡ c xor dotᵥ sv z
  dval = proj₂ (proj₂ shape)

  indep : ∀ w → Indep (G w) j
  indep = Int⇒Indep tr j int

  -- The coordinate derivative, read at every point.
  at-p : ∀ b → (∀ z → ∂ᵢ F j z ≡ b) → ∀ p → ∂ˢ F j p ≡ b
  at-p b h p = trans (cong₂ (λ a a′ → F a xor F a′)
                            (set-as-insertAt p j true)
                            (set-as-insertAt p j false))
                     (h (removeAt p j))

  by-slope : Dec (∃ λ u → lookup sv u ≡ true) → ⊥
  by-slope (yes (i₀ , e₀)) = hh-at tr j int c sv dval i₀ e₀ mx
  by-slope (no ¬sl) = by-c c refl
    where
    const : ∀ z → ∂ᵢ F j z ≡ c
    const z = trans (dval z)
      (trans (cong (c xor_)
               (dotᵥ-null sv z (λ u → not-true (λ e → ¬sl (u , e)))))
             (xor-identityʳ c))

    by-c : ∀ b → c ≡ b → ⊥
    by-c true  e = S.flip⇒⊥ j indep (λ p →
      flip-of {F (set p j true)} {F (set p j false)}
              (at-p true (λ z → trans (const z) e) p))
    by-c false e = elim-at tr
      (S.flat⇒2≤k j indep (λ p →
        same-of {F (set p j true)} {F (set p j false)}
                (at-p false (λ z → trans (const z) e) p)))
      j int (λ z → trans (const z) e) mx


------------------------------------------------------------------------
-- Progress

-- A path-sum satisfying the invariant, equivalent to the
-- specification and with a path variable left, is not maximal.

progress : {ξ : PathSum N k (suc m)} (s : Assign N) → Inv ξ →
           ξ ≋ specᴾ s → Maximal ξ → ⊥
progress {N = N} {m = m} {ξ = ξ} s I eqv mx = by-int (any? (λ v → Int? ξ v))
  where
  open Inv I

  module S = Spec vt s eqv

  by-int : Dec (∃ λ v → Int ξ v) → ⊥
  by-int (no ¬int) = S.endgame
    (λ p p′ eq → vext (λ v → inj p p′ eq v (λ int → ¬int (v , int))))
    0ᵖ (unit zero) (λ e → t≢f (sym (cong (λ t → lookup t zero) e)))
  by-int (yes (u , int-u)) = by-T (any? (λ v → T v ≟ᵇ true))
    where
    by-T : Dec (∃ λ v → T v ≡ true) → ⊥
    by-T (yes (v , e)) =
      at-var s vt eqv v (T-int v e) (Clif⇒Cl vt v (T-clf v e)) mx
    by-T (no ¬T) = at-var s vt eqv u int-u
      (∂⇒Cl {f = F} {u} (Quad⇒Aff-∂ (sl⇒quad F (SL-cong
        (Σ-none T (λ v → not-true (λ e → ¬T (v , e))) (λ p → sgn (F p)))
        T-sl)) (unit u)))
      mx
