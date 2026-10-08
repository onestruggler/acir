------------------------------------------------------------------------
-- Presentations of groups
--
-- Path-sums of order one, read as Boolean functions on bit vectors
--
-- The hidden shift path-sum on |0⟩ and everything its reductions reach
-- have phase ½F modulo 1 and outputs G modulo 2, F and G Boolean
-- functions of the path variables (PathSum.HiddenShift.Track's
-- Tracks).  PathSum.HiddenShift.Positive argues about F and G as
-- functions on bit vectors (PathSum.HiddenShift.Positive.Boolean);
-- VTracks ξ F G is Tracks with F and G read through tabulate.  This
-- module turns figure 2's premises into facts about F and G and back:
--
-- * [Elim] at the head says F does not depend on y₀ (elim-flat), and
--   its reduct reads F and G at y₀ = 0 (elim-vtracks);
-- * [HH] at the head with y_i ← Q says the derivative of F in y₀ is
--   y_i ⊕ q, q the value of Q, which does not depend on y_i (module HH:
--   deriv, q-val, q-off), and its reduct reads F and G at y₀ = 0,
--   y_i = q (HH.reduct);
-- * [ω] and [Case] never apply: their quotients have a quarter where
--   the derivative of a half-phase has a half (ω-impossible,
--   case-impossible);
-- * renumbering is reading F and G through insertAt (front-vtracks);
-- * PathSum.HiddenShift.Positive.Class's syntactic notions are value
--   notions: y_v absent from the outputs modulo 2 is G not depending on
--   y_v (Int⇒flat, flat⇒Int), and the quotient of the phase by y_v
--   linear modulo 1 is the derivative of F in y_v affine (Clif⇒Aff,
--   Aff⇒Clif) -- one way by Möbius inversion against a lifted linear
--   form, the other through coordinate second differences.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Positive.Values (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using
  (xor-comm; xor-assoc; xor-identityʳ; xor-same)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; punchIn)
open import Data.Fin.Subset using (Subset) renaming (⊥ to ∅; ∣_∣ to ∣_∣ˢ)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; divides; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n; ∣n⇒∣m*n; *-cancelˡ-∣; ∣⇒∣ᵤ; ∣-trans;
   ∣m+n∣m⇒∣n)
open import Data.Integer.Properties using (*-identityʳ; +-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _≤_; s≤s; z≤n) renaming
  (_+_ to _ℕ+_)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; tabulate; insertAt)
open import Data.Vec.Properties using
  (tabulate∘lookup; lookup∘tabulate; tabulate-cong)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-there)
open import PathSum.Base using
  (PathSum; ⟨_,_⟩; phase; out; head-part; tail-part)
open import PathSum.Cyclotomic M₀ using (extend)
open import PathSum.Denotation M₀ using (Assign; eval-true; eval-false)
open import PathSum.HiddenShift.Positive.Boolean
open import PathSum.HiddenShift.Positive.Class M₀ using (Int; Clifᶜ)
open import PathSum.HiddenShift.Stuck.Machine M₀ using
  (NoVar-unfront₀; NoVar-flip)
open import PathSum.HiddenShift.Track M₀ using
  (Tracks; phase-at; out-at; eval-head; eval-/ʸ; out-premise)
open import PathSum.Linear using
  (par; parᵐ; par-⊥; eval-liftXor; liftXor-linear)
open import PathSum.Polynomial using
  (Poly; Mon; y[_]; ∥_∥; 0ᴾ; κ; μ; _+ᴾ_; _-ᴾ_; _·ᴾ_; _≈[_]_; NoVar; liftXor;
   eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Boolean using
  (IsBit; BoolValued; IsBit-bool; IsBit-bool-if; ≈-from-values)
open import PathSum.Polynomial.Product using (eval-μᴾ; eval-0ᴾ)
open import PathSum.Polynomial.Properties using
  (eval-∣; eval-+ᴾ; eval-·ᴾ; eval-κ; eval-−ᴾ; eval-off; eval-cong)
open import PathSum.Polynomial.Substitution using
  (Absent; substᴾ; eval-substᴾ-≔; q₁₀; q₀₁)
open import PathSum.Reorder using
  (insertᵃ; insertᵃ-here; insertᵃ-punchIn; unfront; front; frontᴾ; _/ʸ_;
   eval-front; ∣insertAt∣)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Full.Canonical M using (pow∣½·2)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Reduction M using (½; ¼; elim-reduct)
open import PathSum.Reduction.General M using (hhᴳ-reduct)

private
  variable
    N n k m : ℕ


------------------------------------------------------------------------
-- Arithmetic modulo 2^M

private
  2∤1 : ¬ ((+ 2) ∣ 1ℤ)
  2∤1 h with ∣1⇒≡1 (∣⇒∣ᵤ h)
  ... | ()

  pow-suc∤ : ∀ e → ¬ (pow (suc e) ∣ pow e)
  pow-suc∤ e h = 2∤1 (*-cancelˡ-∣ (pow e) {{ℕ.m^n≢0 2 e}}
    (subst₂ _∣_ (pow-suc e) (sym (*-identityʳ (pow e))) h))

  -- 2^M divides neither ½ nor its negative ...
  ∤½ : ¬ (pow M ∣ ½)
  ∤½ = pow-suc∤ (suc (suc M₀))

  ∤-½ : ¬ (pow M ∣ (- ½))
  ∤-½ h = ∤½ (subst (pow M ∣_) (neg-neg ½) (neg-∣ h))
    where
    neg-neg : ∀ a → - (- a) ≡ a
    neg-neg = solve 1 (λ a → :- (:- a) := a) refl
      where open +-*-Solver using (:-_)
    neg-∣ : ∀ {a b} → a ∣ b → a ∣ (- b)
    neg-∣ {a} {b} (divides q eq) = divides (- q)
      (trans (cong -_ eq)
       (solve 2 (λ q a → :- (q :* a) := (:- q) :* a) refl q a))
      where open +-*-Solver using (:-_)

  -- ... nor a quarter plus any multiple of a half.
  ∤¼ : ∀ t → ¬ (pow M ∣ (¼ + ½ * t))
  ∤¼ t h = 2∤1 (∣m+n∣m⇒∣n
    (subst ((+ 2) ∣_) (+-comm′ 1ℤ ((+ 2) * t)) four∣)
    (divides t (*-comm′ (+ 2) t)))
    where
    +-comm′ : ∀ a b → a + b ≡ b + a
    +-comm′ = solve 2 (λ a b → a :+ b := b :+ a) refl
    *-comm′ : ∀ a b → a * b ≡ b * a
    *-comm′ = solve 2 (λ a b → a :* b := b :* a) refl

    ¼-shape : ¼ + ½ * t ≡ ¼ * (1ℤ + (+ 2) * t)
    ¼-shape = trans (cong (λ h → ¼ + h * t) (pow-suc (suc M₀)))
      (solve 2 (λ q t → q :+ (q :* con (+ 2)) :* t :=
                        q :* (con 1ℤ :+ con (+ 2) :* t)) refl ¼ t)

    M-shape : pow M ≡ ¼ * (+ 4)
    M-shape = trans (pow-suc (suc (suc M₀)))
      (trans (cong (_* (+ 2)) (pow-suc (suc M₀)))
             (solve 1 (λ q → (q :* con (+ 2)) :* con (+ 2) := q :* con (+ 4))
                    refl ¼))

    four∣ : (+ 2) ∣ (1ℤ + (+ 2) * t)
    four∣ = ∣-trans (divides (+ 2) refl)
      (*-cancelˡ-∣ ¼ {{ℕ.m^n≢0 2 (suc M₀)}}
        (subst₂ _∣_ M-shape ¼-shape h))

-- A half-bit vanishes modulo 1 only at 0.

half-zero : ∀ b → pow M ∣ (½ * [ b ]ᶻ) → b ≡ false
half-zero false _ = refl
half-zero true  h = ⊥-elim (∤½ (subst (pow M ∣_) (*-identityʳ ½) h))

-- Two half-bits are equal modulo 1 only for equal bits.

half-eq : ∀ a b → pow M ∣ (½ * [ a ]ᶻ - ½ * [ b ]ᶻ) → a ≡ b
half-eq false false _ = refl
half-eq true  true  _ = refl
half-eq true  false h = ⊥-elim (∤½ (subst (pow M ∣_)
  (solve 1 (λ h → h :* con 1ℤ :- h :* con 0ℤ := h) refl ½) h))
half-eq false true  h = ⊥-elim (∤-½ (subst (pow M ∣_)
  (solve 1 (λ h → h :* con 0ℤ :- h :* con 1ℤ := :- h) refl ½) h))
  where open +-*-Solver using (:-_)

-- The difference and the sum of two half-bits are the half of their
-- exclusive or, modulo 1.

half-diff : ∀ a b → pow M ∣ ((½ * [ a ]ᶻ - ½ * [ b ]ᶻ) - ½ * [ a xor b ]ᶻ)
half-diff false false = divides 0ℤ (solve 1 (λ h → (h :* con 0ℤ :- h :* con 0ℤ)
  :- h :* con 0ℤ := con 0ℤ :* (h :* con (+ 2))) refl ½)
half-diff false true  = subst (pow M ∣_) (sym (solve 1 (λ h →
  (h :* con 0ℤ :- h :* con 1ℤ) :- h :* con 1ℤ := con (- (+ 1)) :*
    (h :* con (+ 2)))
  refl ½)) (∣n⇒∣m*n (- (+ 1)) pow∣½·2)
half-diff true  false = divides 0ℤ (solve 1 (λ h → (h :* con 1ℤ :- h :* con 0ℤ)
  :- h :* con 1ℤ := con 0ℤ :* (h :* con (+ 2))) refl ½)
half-diff true  true  = divides 0ℤ (solve 1 (λ h → (h :* con 1ℤ :- h :* con 1ℤ)
  :- h :* con 0ℤ := con 0ℤ :* (h :* con (+ 2))) refl ½)

half-sum : ∀ a b → pow M ∣ (½ * ([ a ]ᶻ + [ b ]ᶻ) - ½ * [ a xor b ]ᶻ)
half-sum false false = divides 0ℤ (solve 1 (λ h → h :* (con 0ℤ :+ con 0ℤ)
  :- h :* con 0ℤ := con 0ℤ :* (h :* con (+ 2))) refl ½)
half-sum false true  = divides 0ℤ (solve 1 (λ h → h :* (con 0ℤ :+ con 1ℤ)
  :- h :* con 1ℤ := con 0ℤ :* (h :* con (+ 2))) refl ½)
half-sum true  false = divides 0ℤ (solve 1 (λ h → h :* (con 1ℤ :+ con 0ℤ)
  :- h :* con 1ℤ := con 0ℤ :* (h :* con (+ 2))) refl ½)
half-sum true  true  = subst (pow M ∣_) (sym (solve 1 (λ h →
  h :* (con 1ℤ :+ con 1ℤ) :- h :* con 0ℤ := con 1ℤ :* (h :* con (+ 2)))
  refl ½)) (∣n⇒∣m*n 1ℤ pow∣½·2)

-- Congruence modulo 2^M chains.

private
  ∣-chain : ∀ {a b c} → pow M ∣ (a - b) → pow M ∣ (b - c) → pow M ∣ (a - c)
  ∣-chain {a} {b} {c} p q = subst (pow M ∣_)
    (solve 3 (λ a b c → (a :- b) :+ (b :- c) := a :- c) refl a b c)
    (∣m∣n⇒∣m+n p q)

  ∣-flip : ∀ {a b} → pow M ∣ (a - b) → pow M ∣ (b - a)
  ∣-flip {a} {b} (divides q eq) = divides (- q)
    (trans (solve 2 (λ a b → b :- a := :- (a :- b)) refl a b)
      (trans (cong -_ eq)
       (solve 2 (λ q p → :- (q :* p) := (:- q) :* p) refl q (pow M))))
    where open +-*-Solver using (:-_)

  -- Congruent coefficients, congruent values.
  ≈⇒val : {P Q : Poly n m} {c : ℤ} → P ≈[ c ] Q →
          ∀ x y → c ∣ (eval P x y - eval Q x y)
  ≈⇒val {P = P} {Q} {c} h x y =
    subst (c ∣_) (eval-−ᴾ P Q x y) (eval-∣ (P -ᴾ Q) h x y)


------------------------------------------------------------------------
-- Vectors and assignments

tab-insertᵃ : (j : Fin (suc m)) (b : Bool) (g : Assign m) →
              tabulate (insertᵃ j b g) ≡ insertAt (tabulate g) j b
tab-insertᵃ          zero    b g = refl
tab-insertᵃ {suc m}  (suc j) b g =
  cong (g zero ∷_) (tab-insertᵃ j b (λ l → g (suc l)))

tab-≔ : (g : Assign m) (i : Fin m) (b : Bool) →
        tabulate (g [ i ≔ b ]) ≡ set (tabulate g) i b
tab-≔ g i b = vext λ j → trans (lookup∘tabulate (g [ i ≔ b ]) j)
  (go j (j Fin.≟ i))
  where
  go : ∀ j → Dec (j ≡ i) → (g [ i ≔ b ]) j ≡ lookup (set (tabulate g) i b) j
  go j (yes refl) = trans (≔-here g j b)
    (sym (lookup-set-here (tabulate g) j b))
  go j (no j≢i)   = trans (≔-there g b j≢i)
    (sym (trans (lookup-set-there (tabulate g) b j≢i) (lookup∘tabulate g j)))


------------------------------------------------------------------------
-- Tracking on vectors

record VTracks (ξ : PathSum N k m) (F : Pt m → Bool)
               (G : Fin N → Pt m → Bool) : Set where
  constructor vtr
  field
    tracks : Tracks ξ (λ y → F (tabulate y)) (λ w y → G w (tabulate y))

open VTracks public

phaseᵥ : {ξ : PathSum N k m} {F : Pt m → Bool} {G : Fin N → Pt m → Bool} →
         VTracks ξ F G → ∀ x p →
         pow M ∣ (eval (phase ξ) x (lookup p) - ½ * [ F p ]ᶻ)
phaseᵥ {ξ = ξ} {F} tr x p =
  subst (λ q → pow M ∣ (eval (phase ξ) x (lookup p) - ½ * [ F q ]ᶻ))
        (tabulate∘lookup p) (phase-at (tracks tr) x (lookup p))

outᵥ : {ξ : PathSum N k m} {F : Pt m → Bool} {G : Fin N → Pt m → Bool} →
       VTracks ξ F G → ∀ w x p → odd (eval (out ξ w) x (lookup p)) ≡ G w p
outᵥ {G = G} tr w x p =
  trans (out-at (tracks tr) w x (lookup p)) (cong (G w) (tabulate∘lookup p))

-- Renumbering.

front-vtracks : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
                {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
                (j : Fin (suc m)) →
                VTracks (front j ξ) (λ p → F (unfr j p))
                  (λ w p → G w (unfr j p))
front-vtracks {ξ = ξ} {F} {G} tr j = vtr record
  { phase-at = λ x y →
      subst (λ t → pow M ∣ (t - ½ * [ F (unfr j (tabulate y)) ]ᶻ))
            (sym (eval-front j (phase ξ) x y))
            (subst
             (λ q → pow M ∣ (eval (phase ξ) x (unfront j y) - ½ * [ F q ]ᶻ))
                   (tab-insertᵃ j (y zero) (λ i → y (suc i)))
                   (phase-at (tracks tr) x (unfront j y)))
  ; out-at = λ w x y → trans (cong odd (eval-front j (out ξ w) x y))
      (trans (out-at (tracks tr) w x (unfront j y))
             (cong (G w) (tab-insertᵃ j (y zero) (λ i → y (suc i)))))
  }


------------------------------------------------------------------------
-- The head quotient

-- Modulo 1 the quotient by the head is half the derivative of F.

head-val : {χ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
           {G : Fin N → Pt (suc m) → Bool} → VTracks χ F G → ∀ x p →
           pow M ∣ (eval (head-part (phase χ)) x (lookup p) -
                    ½ * [ F (true ∷ p) xor F (false ∷ p) ]ᶻ)
head-val {χ = χ} {F} tr x p = subst (pow M ∣_)
  (cong (λ t → t - ½ * [ F (true ∷ p) xor F (false ∷ p) ]ᶻ)
        (sym (eval-head (phase χ) x (lookup p))))
  (∣-chain {a = A - B} {b = a - b} {c = ½ * [ F (true ∷ p) xor F (false ∷ p) ]ᶻ}
    (subst (pow M ∣_)
      (solve 4 (λ A B a b → (A :- a) :- (B :- b) := (A :- B) :- (a :- b))
             refl A B a b)
      (∣m∣n⇒∣m-n (at true) (at false)))
    (half-diff (F (true ∷ p)) (F (false ∷ p))))
  where
  A B a b : ℤ
  A = eval (phase χ) x (extend true (lookup p))
  B = eval (phase χ) x (extend false (lookup p))
  a = ½ * [ F (true ∷ p) ]ᶻ
  b = ½ * [ F (false ∷ p) ]ᶻ

  at : ∀ b → pow M ∣
    (eval (phase χ) x (extend b (lookup p)) - ½ * [ F (b ∷ p) ]ᶻ)
  at b = subst
    (λ q → pow M ∣
     (eval (phase χ) x (extend b (lookup p)) - ½ * [ F (b ∷ q) ]ᶻ))
               (tabulate∘lookup p)
                 (phase-at (tracks tr) x (extend b (lookup p)))


------------------------------------------------------------------------
-- [Elim]

elim-flat : {χ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
            {G : Fin N → Pt (suc m) → Bool} → VTracks χ F G →
            head-part (phase χ) ≈[ pow M ] 0ᴾ →
            ∀ p → F (true ∷ p) ≡ F (false ∷ p)
elim-flat {χ = χ} {F} tr eq p = xor-false (half-zero _
  (subst (pow M ∣_)
    (solve 2 (λ e h → (e :- con 0ℤ) :- (e :- h) := h) refl E
             (½ * [ F (true ∷ p) xor F (false ∷ p) ]ᶻ))
    (∣m∣n⇒∣m-n (subst (λ t → pow M ∣ (E - t)) (eval-0ᴾ x₀ (lookup p))
                      (≈⇒val eq x₀ (lookup p)))
               (head-val tr x₀ p))))
  where
  x₀ : Fin _ → Bool
  x₀ _ = false

  E : ℤ
  E = eval (head-part (phase χ)) x₀ (lookup p)

elim-vtracks : {χ : PathSum N (suc (suc k)) (suc m)} {F : Pt (suc m) → Bool}
               {G : Fin N → Pt (suc m) → Bool} → VTracks χ F G →
               VTracks (elim-reduct χ) (λ p → F (false ∷ p))
                       (λ w p → G w (false ∷ p))
elim-vtracks {χ = χ} {F} {G} tr = vtr record
  { phase-at = λ x y →
      subst (λ t → pow M ∣ (t - ½ * [ F (false ∷ tabulate y) ]ᶻ))
            (eval-false (phase χ) x y) (phase-at (tracks tr) x (extend false y))
  ; out-at = λ w x y →
      trans (cong odd (sym (eval-false (out χ w) x y)))
        (out-at (tracks tr) w x (extend false y))
  }


------------------------------------------------------------------------
-- [HH]

module HH {χ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
          {G : Fin N → Pt (suc m) → Bool} (tr : VTracks χ F G)
          (i : Fin m) (Q : Poly N m) (bQ : BoolValued Q)
          (absQ : Absent y[ i ] Q)
          (eqP : head-part (phase χ) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q))) where

  -- The value substituted for y_i.

  q : Pt m → Bool
  q p = (F (true ∷ p) xor F (false ∷ p)) xor lookup p i

  private
    bit-inj : ∀ {a b} → [ a ]ᶻ ≡ [ b ]ᶻ → a ≡ b
    bit-inj {false} {false} _ = refl
    bit-inj {true}  {true}  _ = refl
    bit-inj {false} {true}  ()
    bit-inj {true}  {false} ()

    solve-c : ∀ d a c → d ≡ a xor c → c ≡ d xor a
    solve-c d false c e = trans (sym e) (sym (xor-identityʳ d))
    solve-c d true  c e = sym (trans (cong (_xor true) e) (bits c))
      where
      bits : ∀ c → (true xor c) xor true ≡ c
      bits false = refl
      bits true  = refl

  q-val : ∀ x p → eval Q x (lookup p) ≡ [ q p ]ᶻ
  q-val x p = trans (sym (IsBit-bool-if (bQ x (lookup p))))
    (cong [_]ᶻ (solve-c (F (true ∷ p) xor F (false ∷ p)) (lookup p i) c
      (half-eq _ _
       (∣-chain {a = ½ * [ d ]ᶻ} {b = ½ * ([ lookup p i ]ᶻ + [ c ]ᶻ)}
        {c = ½ * [ lookup p i xor c ]ᶻ}
        (subst (pow M ∣_)
          (solve 3 (λ h e r → (h :- r) :- (h :- e) := e :- r) refl
                 H (½ * [ d ]ᶻ) (½ * ([ lookup p i ]ᶻ + [ c ]ᶻ)))
          (∣m∣n⇒∣m-n premise (head-val tr x p)))
        (half-sum (lookup p i) c)))))
    where
    c : Bool
    c = IsBit-bool (bQ x (lookup p))

    d : Bool
    d = F (true ∷ p) xor F (false ∷ p)

    H : ℤ
    H = eval (head-part (phase χ)) x (lookup p)

    premise : pow M ∣ (H - ½ * ([ lookup p i ]ᶻ + [ c ]ᶻ))
    premise = subst (λ t → pow M ∣ (H - t))
      (trans (eval-·ᴾ ½ (μ y[ i ] +ᴾ Q) x (lookup p))
        (cong (½ *_) (trans (eval-+ᴾ (μ y[ i ]) Q x (lookup p))
          (cong₂ _+_ (eval-μᴾ y[ i ] x (lookup p))
                     (sym (IsBit-bool-if (bQ x (lookup p))))))))
      (≈⇒val eqP x (lookup p))

  -- So the derivative of F in y₀ is y_i ⊕ q ...

  deriv : ∀ p → F (true ∷ p) xor F (false ∷ p) ≡ lookup p i xor q p
  deriv p = bits (F (true ∷ p) xor F (false ∷ p)) (lookup p i)
    where
    bits : ∀ d a → d ≡ a xor (d xor a)
    bits false false = refl
    bits false true  = refl
    bits true  false = refl
    bits true  true  = refl

  -- ... q reads no variable absent from Q, y_i in particular ...

  q-off : ∀ v → Absent y[ v ] Q → ∀ p b → q (set p v b) ≡ q p
  q-off v absV p b = bit-inj (trans (sym (q-val x₀ (set p v b)))
    (trans (eval-off Q v absV x₀ (lookup (set p v b)) (lookup p)
                     (λ j j≢v → lookup-set-there p b j≢v))
           (q-val x₀ p)))
    where
    x₀ : Fin _ → Bool
    x₀ _ = false

  -- ... and the reduct reads F and G at y₀ = 0 and y_i = q.

  F″ : Pt m → Bool
  F″ p = F (false ∷ set p i (q p))

  G″ : Fin N → Pt m → Bool
  G″ w p = G w (false ∷ set p i (q p))

  reduct : VTracks (hhᴳ-reduct χ i Q) F″ G″
  reduct = vtr record
    { phase-at = λ x y →
        subst (λ t → pow M ∣ (t - ½ * [ F″ (tabulate y) ]ᶻ))
          (sym (val (phase χ) x y))
          (subst (λ s → pow M ∣ (eval (phase χ) x (extend false (y [ i ≔ c y ]))
                                 - ½ * [ F (false ∷ s) ]ᶻ))
                 (tab-≔ y i (c y))
                 (phase-at (tracks tr) x (extend false (y [ i ≔ c y ]))))
    ; out-at = λ w x y →
        trans (cong odd (val (out χ w) x y))
          (trans (out-at (tracks tr) w x (extend false (y [ i ≔ c y ])))
                 (cong (λ s → G w (false ∷ s)) (tab-≔ y i (c y))))
    }
    where
    c : Assign m → Bool
    c y = q (tabulate y)

    val : ∀ P x y → eval (substᴾ (tail-part P) y[ i ] Q) x y ≡
                    eval P x (extend false (y [ i ≔ c y ]))
    val P x y = trans
      (eval-substᴾ-≔ (tail-part P) i Q x y (c y)
        (sym (trans (eval-cong Q {x} {x} {y} {lookup (tabulate y)}
                               (λ _ → refl) (λ j → sym (lookup∘tabulate y j)))
                    (q-val x (tabulate y)))))
      (sym (eval-false P x (y [ i ≔ c y ])))


------------------------------------------------------------------------
-- [ω] and [Case] never apply

private
  -- A difference of two half-bits is never a quarter plus a multiple
  -- of a half, modulo 1.
  quarter : ∀ a b t → pow M ∣ ((½ * [ a ]ᶻ - ½ * [ b ]ᶻ) - (¼ + ½ * t)) → ⊥
  quarter a b t h = ∤¼ ((t - [ a ]ᶻ) + [ b ]ᶻ) (subst (pow M ∣_)
    (solve 5 (λ h q t a b → :- ((h :* a :- h :* b) :- (q :+ h :* t)) :=
                            q :+ h :* ((t :- a) :+ b))
           refl ½ ¼ t [ a ]ᶻ [ b ]ᶻ)
    (neg h))
    where
    open +-*-Solver using (:-_)
    neg : ∀ {z} → pow M ∣ z → pow M ∣ (- z)
    neg {z} (divides r eq) = divides (- r)
      (trans (cong -_ eq)
       (solve 2 (λ r p → :- (r :* p) := (:- r) :* p) refl r (pow M)))

ω-impossible : {χ : PathSum N (suc k) (suc m)} {F : Pt (suc m) → Bool}
               {G : Fin N → Pt (suc m) → Bool} → VTracks χ F G →
               (Q : Poly N m) →
               head-part (phase χ) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ Q)) → ⊥
ω-impossible {χ = χ} {F} tr Q eq = quarter d false (eval Q x₀ (lookup p₀))
  (subst (pow M ∣_)
    (solve 4 (λ h hd r q → (h :- r) :- (h :- hd) := (hd :- q :* con 0ℤ) :- r)
           refl H (½ * [ d ]ᶻ) (¼ + ½ * eval Q x₀ (lookup p₀)) ½)
    (∣m∣n⇒∣m-n (subst (λ t → pow M ∣ (H - t)) R≡ (≈⇒val eq x₀ (lookup p₀)))
               (head-val tr x₀ p₀)))
  where
  x₀ : Fin _ → Bool
  x₀ _ = false

  p₀ : Pt _
  p₀ = 0ᵖ

  d : Bool
  d = F (true ∷ p₀) xor F (false ∷ p₀)

  H : ℤ
  H = eval (head-part (phase χ)) x₀ (lookup p₀)

  R≡ : eval (κ ¼ +ᴾ (½ ·ᴾ Q)) x₀ (lookup p₀) ≡ ¼ + ½ * eval Q x₀ (lookup p₀)
  R≡ = trans (eval-+ᴾ (κ ¼) (½ ·ᴾ Q) x₀ (lookup p₀))
             (cong₂ _+_ (eval-κ ¼ x₀ (lookup p₀)) (eval-·ᴾ ½ Q x₀ (lookup p₀)))

-- The values at the first two variables.

two-val : {χ : PathSum N k (suc (suc m))} {F : Pt (suc (suc m)) → Bool}
          {G : Fin N → Pt (suc (suc m)) → Bool} → VTracks χ F G → ∀ x p b c →
          pow M ∣ (eval (phase χ) x (extend b (extend c (lookup p))) -
                   ½ * [ F (b ∷ c ∷ p) ]ᶻ)
two-val {χ = χ} {F} tr x p b c =
  subst (λ q → pow M ∣ (eval (phase χ) x (extend b (extend c (lookup p))) -
                        ½ * [ F (b ∷ c ∷ q) ]ᶻ))
        (tabulate∘lookup p)
          (phase-at (tracks tr) x (extend b (extend c (lookup p))))

case-impossible : {χ : PathSum N k (suc (suc m))} {F : Pt (suc (suc m)) → Bool}
                  {G : Fin N → Pt (suc (suc m)) → Bool} → VTracks χ F G →
                  (X Q Q′ : Poly N m) → BoolValued X →
                  q₁₀ (phase χ) ≈[ pow M ] ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q)) →
                  q₀₁ (phase χ) ≈[ pow M ] ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′)) →
                  ⊥
case-impossible {χ = χ} {F} tr X Q Q′ bX e₁₀ e₀₁ = go c refl
  where
  x₀ : Fin _ → Bool
  x₀ _ = false

  p₀ : Pt _
  p₀ = 0ᵖ

  y₀ : Fin _ → Bool
  y₀ = lookup p₀

  P = phase χ

  c : Bool
  c = IsBit-bool (bX x₀ y₀)

  X≡ : eval X x₀ y₀ ≡ [ c ]ᶻ
  X≡ = sym (IsBit-bool-if (bX x₀ y₀))

  -- The two quotients as differences of values.
  q₁₀≡ : eval (q₁₀ P) x₀ y₀ ≡
         eval P x₀ (extend true (extend false y₀)) -
         eval P x₀ (extend false (extend false y₀))
  q₁₀≡ = trans (sym (eval-false (head-part P) x₀ y₀))
               (eval-head P x₀ (extend false y₀))

  q₀₁≡ : eval (q₀₁ P) x₀ y₀ ≡
         eval P x₀ (extend false (extend true y₀)) -
         eval P x₀ (extend false (extend false y₀))
  q₀₁≡ = trans (eval-head (tail-part P) x₀ y₀)
    (cong₂ _-_ (sym (eval-false P x₀ (extend true y₀)))
               (sym (eval-false P x₀ (extend false y₀))))

  -- A congruence of a difference of two half-bit values with a quarter
  -- plus a multiple of a half is impossible.
  clash : ∀ (A B : ℤ) (a b : Bool) (E R t : ℤ) →
          pow M ∣ (A - ½ * [ a ]ᶻ) → pow M ∣ (B - ½ * [ b ]ᶻ) →
          E ≡ A - B → pow M ∣ (E - R) → R ≡ ¼ * 1ℤ + ½ * t → ⊥
  clash A B a b E R t hA hB eE hER eR = quarter a b t (subst (pow M ∣_)
    (trans (cong (λ e → (e - R) - ((A - ½ * [ a ]ᶻ) - (B - ½ * [ b ]ᶻ))) eE)
      (trans
       (cong (λ r → ((A - B) - r) - ((A - ½ * [ a ]ᶻ) - (B - ½ * [ b ]ᶻ))) eR)
        (solve 7 (λ A B hA hB q h t →
           ((A :- B) :- (q :* con 1ℤ :+ h :* t)) :- ((A :- hA) :- (B :- hB)) :=
           (hA :- hB) :- (q :+ h :* t))
          refl A B (½ * [ a ]ᶻ) (½ * [ b ]ᶻ) ¼ ½ t)))
    (∣m∣n⇒∣m-n hER (∣m∣n⇒∣m-n hA hB)))

  go : ∀ b → c ≡ b → ⊥
  go true  cb = clash (eval P x₀ (extend true (extend false y₀)))
    (eval P x₀ (extend false (extend false y₀)))
    (F (true ∷ false ∷ p₀)) (F (false ∷ false ∷ p₀))
    (eval (q₁₀ P) x₀ y₀) (eval ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q)) x₀ y₀) (eval Q x₀ y₀)
    (two-val tr x₀ p₀ true false) (two-val tr x₀ p₀ false false)
    q₁₀≡ (≈⇒val e₁₀ x₀ y₀)
    (trans (eval-+ᴾ (¼ ·ᴾ X) (½ ·ᴾ Q) x₀ y₀)
      (cong₂ _+_ (trans (eval-·ᴾ ¼ X x₀ y₀)
                        (cong (¼ *_) (trans X≡ (cong [_]ᶻ cb))))
                 (eval-·ᴾ ½ Q x₀ y₀)))
  go false cb = clash (eval P x₀ (extend false (extend true y₀)))
    (eval P x₀ (extend false (extend false y₀)))
    (F (false ∷ true ∷ p₀)) (F (false ∷ false ∷ p₀))
    (eval (q₀₁ P) x₀ y₀) (eval ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′)) x₀ y₀)
    (eval Q′ x₀ y₀)
    (two-val tr x₀ p₀ false true) (two-val tr x₀ p₀ false false)
    q₀₁≡ (≈⇒val e₀₁ x₀ y₀)
    (trans (eval-+ᴾ (¼ ·ᴾ (κ 1ℤ -ᴾ X)) (½ ·ᴾ Q′) x₀ y₀)
      (cong₂ _+_ (trans (eval-·ᴾ ¼ (κ 1ℤ -ᴾ X) x₀ y₀)
                        (cong (¼ *_) (trans (eval-−ᴾ (κ 1ℤ) X x₀ y₀)
                          (cong₂ _-_ (eval-κ 1ℤ x₀ y₀)
                           (trans X≡ (cong [_]ᶻ cb))))))
                 (eval-·ᴾ ½ Q′ x₀ y₀)))


------------------------------------------------------------------------
-- Internal variables

-- A variable absent from the outputs modulo 2 is one no output reads,
-- and conversely.

Int⇒flat : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
           {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
           (v : Fin (suc m)) → Int ξ v →
           ∀ w z → G w (insertAt z v true) ≡ G w (insertAt z v false)
Int⇒flat {ξ = ξ} {F} {G} tr v int w z = trans (sym (at true))
  (trans (NoVar-flip v (out ξ w) (int w) (λ _ → false) (lookup z)) (at false))
  where
  at : ∀ b → odd (eval (out ξ w) (λ _ → false) (insertᵃ v b (lookup z))) ≡
             G w (insertAt z v b)
  at b = trans (out-at (tracks tr) w (λ _ → false) (insertᵃ v b (lookup z)))
    (cong (G w) (trans (tab-insertᵃ v b (lookup z))
                       (cong (λ t → insertAt t v b) (tabulate∘lookup z))))

flat⇒Int : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
           {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
           (v : Fin (suc m)) →
           (∀ w z → G w (insertAt z v true) ≡ G w (insertAt z v false)) →
           Int ξ v
flat⇒Int {ξ = ξ} {F} {G} tr v flat w = NoVar-unfront₀ v (out ξ w)
  (out-premise ξ (tracks tr) v
    (λ w′ y → trans (cong (G w′) (tab-insertᵃ v true y))
      (trans (flat w′ (tabulate y))
       (cong (G w′) (sym (tab-insertᵃ v false y)))))
    w)


------------------------------------------------------------------------
-- Clifford variables

-- The derivative of F in coordinate v, as a function of the others.

∂ᵢ : (Pt (suc m) → Bool) → Fin (suc m) → Pt m → Bool
∂ᵢ F v z = F (insertAt z v true) xor F (insertAt z v false)

-- The quotient of the phase by y_v is half that derivative, modulo 1.

quot-val : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
           {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
           (v : Fin (suc m)) → ∀ x z →
           pow M ∣ (eval (phase ξ /ʸ v) x (lookup z) - ½ * [ ∂ᵢ F v z ]ᶻ)
quot-val {ξ = ξ} {F} tr v x z = subst (pow M ∣_)
  (cong (λ t → t - ½ * [ ∂ᵢ F v z ]ᶻ) (sym (eval-/ʸ (phase ξ) v x (lookup z))))
  (∣-chain {a = A - B} {b = a - b} {c = ½ * [ ∂ᵢ F v z ]ᶻ}
    (subst (pow M ∣_)
      (solve 4 (λ A B a b → (A :- a) :- (B :- b) := (A :- B) :- (a :- b))
             refl A B a b)
      (∣m∣n⇒∣m-n (at true) (at false)))
    (half-diff (F (insertAt z v true)) (F (insertAt z v false))))
  where
  A B a b : ℤ
  A = eval (phase ξ) x (insertᵃ v true (lookup z))
  B = eval (phase ξ) x (insertᵃ v false (lookup z))
  a = ½ * [ F (insertAt z v true) ]ᶻ
  b = ½ * [ F (insertAt z v false) ]ᶻ

  at : ∀ c → pow M ∣ (eval (phase ξ) x (insertᵃ v c (lookup z)) -
                      ½ * [ F (insertAt z v c) ]ᶻ)
  at c = subst (λ q → pow M ∣ (eval (phase ξ) x (insertᵃ v c (lookup z)) -
                               ½ * [ F q ]ᶻ))
    (trans (tab-insertᵃ v c (lookup z))
           (cong (λ t → insertAt t v c) (tabulate∘lookup z)))
    (phase-at (tracks tr) x (insertᵃ v c (lookup z)))

private
  -- A parity is an inner product.
  par-dot : (s : Subset m) (y : Assign m) → par s y ≡ dotᵥ s (tabulate y)
  par-dot []          y = refl
  par-dot (true  ∷ s) y = cong (y zero xor_) (par-dot s (λ i → y (suc i)))
  par-dot (false ∷ s) y = par-dot s (λ i → y (suc i))

  -- Four half-bits combine into the half of their exclusive or.
  half4 : ∀ p q r s →
          pow M ∣ (((½ * [ p ]ᶻ - ½ * [ q ]ᶻ) - (½ * [ r ]ᶻ - ½ * [ s ]ᶻ)) -
                   ½ * [ ((p xor q) xor r) xor s ]ᶻ)
  half4 p q r s =
    subst
      (λ b → pow M ∣ (((½ * [ p ]ᶻ - ½ * [ q ]ᶻ) - (½ * [ r ]ᶻ - ½ * [ s ]ᶻ)) -
                          ½ * [ b ]ᶻ))
          (sym (xor-assoc (p xor q) r s))
          (∣-chain {a = (½ * [ p ]ᶻ - ½ * [ q ]ᶻ) - (½ * [ r ]ᶻ - ½ * [ s ]ᶻ)}
                   {b = ½ * [ p xor q ]ᶻ - ½ * [ r xor s ]ᶻ}
                   {c = ½ * [ (p xor q) xor (r xor s) ]ᶻ}
            (subst (pow M ∣_)
              (solve 6 (λ a b c d e f → ((a :- b) :- e) :- ((c :- d) :- f) :=
                                        ((a :- b) :- (c :- d)) :- (e :- f))
                     refl (½ * [ p ]ᶻ) (½ * [ q ]ᶻ) (½ * [ r ]ᶻ) (½ * [ s ]ᶻ)
                     (½ * [ p xor q ]ᶻ) (½ * [ r xor s ]ᶻ))
              (∣m∣n⇒∣m-n (half-diff p q) (half-diff r s)))
            (half-diff (p xor q) (r xor s)))

-- An affine derivative makes the quotient linear modulo 1: the
-- quotient agrees modulo 1, coefficient by coefficient, with half the
-- lift of the affine form, whose coefficients of degree at least two
-- are even.

Aff⇒Clif : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
           {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
           (v : Fin (suc m)) → Aff (∂ᵢ F v) → Clifᶜ (phase ξ) v
Aff⇒Clif {N = N} {m = m} {ξ = ξ} {F} tr v af γ 2≤γ = subst (pow M ∣_)
  (solve 2 (λ d h → (d :- h) :+ h := d) refl (D γ) (½ * L γ))
  (∣m∣n⇒∣m+n (D≈ γ) half-even)
  where
  shape = aff-expand af
  c  = proj₁ shape
  s  = proj₁ (proj₂ shape)
  eq = proj₂ (proj₂ shape)

  D : Poly N m
  D = phase ξ /ʸ v

  L : Poly N m
  L = liftXor c (∅ , s)

  vals : ∀ x y → pow M ∣ (eval D x y - eval (½ ·ᴾ L) x y)
  vals x y = subst₂ (λ a b → pow M ∣ (a - b))
    (eval-cong D {x} {x} {lookup (tabulate y)} {y} (λ _ → refl)
               (lookup∘tabulate y))
    (sym (trans (eval-·ᴾ ½ L x y)
      (cong (½ *_) (trans (eval-liftXor c (∅ , s) x y)
        (cong (λ b → [ c xor b ]ᶻ)
          (trans (cong (_xor par s y) (par-⊥ x)) (par-dot s y)))))))
    (subst (λ b → pow M ∣ (eval D x (lookup (tabulate y)) - ½ * [ b ]ᶻ))
           (eq (tabulate y)) (quot-val tr v x (tabulate y)))

  D≈ : D ≈[ pow M ] (½ ·ᴾ L)
  D≈ = ≈-from-values D (½ ·ᴾ L) vals

  half-even : pow M ∣ (½ * L γ)
  half-even with liftXor-linear c (∅ , s) γ 2≤γ
  ... | divides r e = subst (pow M ∣_)
    (sym (trans (cong (½ *_) e)
                (solve 2
                 (λ h r → h :* (r :* con (+ 2)) := r :* (h :* con (+ 2)))
                       refl ½ r)))
    (∣n⇒∣m*n r pow∣½·2)

-- Conversely a quotient linear modulo 1 makes the derivative affine:
-- its coordinate second differences are values of the twice-repeated
-- quotient, all of whose coefficients vanish modulo 1.

Clif⇒Aff : {ξ : PathSum N k (suc m)} {F : Pt (suc m) → Bool}
           {G : Fin N → Pt (suc m) → Bool} → VTracks ξ F G →
           (v : Fin (suc m)) → Clifᶜ (phase ξ) v → Aff (∂ᵢ F v)
Clif⇒Aff {m = zero}        tr v cl = Aff-0 _
Clif⇒Aff {m = suc zero}    tr v cl = Aff-1 _
Clif⇒Aff {N = N} {m = suc (suc m)} {ξ = ξ} {F} tr v cl = CSD⇒Aff (∂ᵢ F v) csd
  where
  D : Poly N (suc (suc m))
  D = phase ξ /ʸ v

  ℓ : Pt (suc (suc m)) → Bool
  ℓ = ∂ᵢ F v

  csd : CSD ℓ
  csd a b z = half-zero x (subst (pow M ∣_)
    (solve 2 (λ s h → s :- (s :- h) := h) refl S (½ * [ x ]ᶻ))
    (∣m∣n⇒∣m-n S∣ step2))
    where
    x₀ : Fin N → Bool
    x₀ _ = false

    -- The point with coordinate a set to c and b to e.
    w : Bool → Bool → Pt (suc (suc m))
    w c e = insertAt (insertAt z b e) a c

    y : Bool → Bool → Assign (suc (suc m))
    y c e = insertᵃ a c (insertᵃ b e (lookup z))

    tab-y : ∀ c e → tabulate (y c e) ≡ w c e
    tab-y c e = trans (tab-insertᵃ a c (insertᵃ b e (lookup z)))
      (cong (λ t → insertAt t a c)
            (trans (tab-insertᵃ b e (lookup z))
                   (cong (λ t → insertAt t b e) (tabulate∘lookup z))))

    x : Bool
    x = ((ℓ (w true true) xor ℓ (w false true)) xor ℓ (w true false)) xor
        ℓ (w false false)

    d : Bool → Bool → ℤ
    d c e = eval D x₀ (y c e)

    h : Bool → Bool → ℤ
    h c e = ½ * [ ℓ (w c e) ]ᶻ

    S HS : ℤ
    S  = (d true true - d false true) - (d true false - d false false)
    HS = (h true true - h false true) - (h true false - h false false)

    val : ∀ c e → pow M ∣ (d c e - h c e)
    val c e = subst₂ (λ t p → pow M ∣ (t - ½ * [ ℓ p ]ᶻ))
      (eval-cong D {x₀} {x₀} {lookup (tabulate (y c e))} {y c e}
                 (λ _ → refl) (lookup∘tabulate (y c e)))
      (tab-y c e)
      (quot-val tr v x₀ (tabulate (y c e)))

    step1 : pow M ∣ (S - HS)
    step1 = subst (pow M ∣_)
      (solve 8 (λ a b c d p q r s →
                  ((a :- p) :- (b :- q)) :- ((c :- r) :- (d :- s)) :=
                  ((a :- b) :- (c :- d)) :- ((p :- q) :- (r :- s)))
             refl (d true true) (d false true) (d true false) (d false false)
                  (h true true) (h false true) (h true false) (h false false))
      (∣m∣n⇒∣m-n (∣m∣n⇒∣m-n (val true true) (val false true))
                 (∣m∣n⇒∣m-n (val true false) (val false false)))

    step2 : pow M ∣ (S - ½ * [ x ]ᶻ)
    step2 = ∣-chain {a = S} {b = HS} {c = ½ * [ x ]ᶻ} step1
      (half4 (ℓ (w true true)) (ℓ (w false true))
             (ℓ (w true false)) (ℓ (w false false)))

    -- The repeated quotient's value is S, and its coefficients are
    -- coefficients of D of degree at least two.
    S∣ : pow M ∣ S
    S∣ = subst (pow M ∣_)
      (trans (eval-/ʸ (D /ʸ a) b x₀ (lookup z))
        (cong₂ _-_ (eval-/ʸ D a x₀ (insertᵃ b true (lookup z)))
                   (eval-/ʸ D a x₀ (insertᵃ b false (lookup z)))))
      (eval-∣ ((D /ʸ a) /ʸ b) coeff x₀ (lookup z))
      where
      coeff : ∀ γ → pow M ∣ ((D /ʸ a) /ʸ b) γ
      coeff (α , β) = cl (α , insertAt (insertAt β b true) a true)
        (subst (2 ≤_)
          (sym
           (trans (cong (∣ α ∣ˢ ℕ+_) (∣insertAt∣ (insertAt β b true) a true))
                      (cong (λ t → ∣ α ∣ˢ ℕ+ suc t) (∣insertAt∣ β b true))))
          (ℕ.≤-trans (s≤s (s≤s z≤n)) (ℕ.m≤n+m (suc (suc ∣ β ∣ˢ)) ∣ α ∣ˢ)))