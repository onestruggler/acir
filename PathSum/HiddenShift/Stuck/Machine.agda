------------------------------------------------------------------------
-- Presentations of groups
--
-- Reducing a path-sum known by values in algebraic normal form, and
-- certifying that the end is stuck
--
-- PathSum.HiddenShift.Track follows a path-sum through [HH] and [Elim]
-- of figure 2 (Amy, QPL 2018) by its values: Tracks ξ F G says its
-- phase is ½F modulo 1 and its outputs G modulo 2, and hh-elim turns a
-- derivative of F of the form y_i ⊕ q, with G free of the variable,
-- into a two-step chain and the values of the reduct.  Here F and G
-- are given in algebraic normal form (PathSum.Polynomial.ANF), so that
-- at a fixed instance everything a step needs is computed: the
-- quotient q is read off the derivative (quotᴿ), the side conditions
-- are Boolean checks proved by refl (HHOk: the derivative is y_i ⊕ q
-- with q free of y_i; OutOk: no output depends on the variable), and
-- the reduct's values are the normal forms nextᴿ.  A Stage of the
-- reduction of ξ₀ is a path-sum, a chain to it, and its values (step).
-- The quotient may be any Boolean polynomial -- figure 2's [HH] takes
-- a Boolean-valued Q, which is the lift of q (liftᵉ) -- and need not
-- be linear.
--
-- The end of a reduction is certified irreducible (stuck) when every
-- path variable occurs in some output: each rule of figure 2 needs the
-- variable it eliminates to be internal, absent from every output
-- modulo 2.  Occurs checks it on the normal forms of the outputs -- for
-- every variable some output whose derivative in it has a point where
-- it is 1 (ANF.witness) -- and occurs⇒irreducible turns that into
-- PathSum.Full.Match's Irreducibleᶠ: no rule of figure 2 applies at
-- any variable or pair.  (PathSum.Full.Obstruction's certificate reads
-- four coefficients of the phase and ignores the side condition on the
-- outputs, so it cannot certify such a path-sum: at order 1 its
-- condition always holds.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Stuck.Machine (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _xor_)
open import Data.Empty using (⊥)
open import Data.Bool.Properties using (xor-same)
open import Data.Fin.Base using (Fin; zero; suc; punchIn; punchOut)
open import Data.Fin.Properties using (punchInᵢ≢i; punchIn-punchOut; _≟_)
open import Data.Fin.Subset using (inside)
open import Data.Integer.Base using (ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (_∷_; here; there; insertAt; removeAt; lookup)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

import Data.Vec.Properties as Vec

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-there)
open import PathSum.Base using
  (PathSum; phase; out; y₀; head-part; tail-part)
open import PathSum.Denotation M₀ using (Assign; eval-true; eval-false)
open import PathSum.HiddenShift.Sign M₀ using (odd-+)
open import PathSum.HiddenShift.Track M₀ using
  (Tracks; phase-at; out-at; hh-elim; eval-at)
open import PathSum.Polynomial using (Poly; y[_]; NoVar; eval)
open import PathSum.Polynomial.ANF using
  (RM; 𝟘; 𝟙; node; evalᴿ; evalᴿ-cong; _⊕ᴿ_; eval-⊕ᴿ; restrict; weaken;
   eval-weaken; eval-restrict; derivᴿ; eval-derivᴿ; substitute; eval-substitute; eqᴿ;
   eqᴿ-sound; allFin; allFin-sound; anyFin; anyFin-sound; witness;
   Found; found)
  renaming (var to varᴿ; eval-var to eval-varᴿ)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Boolean using
  (BExp; var; lit; _⊕ᵉ_; _∧ᵉ_; ⟦_⟧ᵉ; liftᵉ; eval-liftᵉ; _∉ᵉ_;
   Absent-liftᵉ)
open import PathSum.Polynomial.Properties using (eval-∣)
open import PathSum.Reorder using
  (insertᵃ; insertᵃ-here; insertᵃ-punchIn; front; frontᴾ; NoVar-front)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Full M using (_⟶ᶠ*_; εᶠ; _◅◅ᶠ_)
open import PathSum.Full.Match M using
  (Irreducibleᶠ; HeadStepᴳ; head⇒Irreducibleᶠ)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½; elim-reduct)
open import PathSum.Reduction.General M using
  (_⟶ᴳ_; elimᴳ; ωᴳ; hhᴳ; caseᴳ; hhᴳ-reduct)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- Small facts

-- Tracking is about values, so pointwise equal values track alike.

tracks-cong : {ξ : PathSum n k m} {F F′ : Assign m → Bool}
              {G G′ : Fin n → Assign m → Bool} → Tracks ξ F G →
              (∀ y → F y ≡ F′ y) → (∀ w y → G w y ≡ G′ w y) →
              Tracks ξ F′ G′
tracks-cong {ξ = ξ} tr hF hG = record
  { phase-at = λ x y →
      subst (λ b → pow M ∣ (eval (phase ξ) x y - ½ * [ b ]ᶻ)) (hF y)
            (phase-at tr x y)
  ; out-at = λ w x y → trans (out-at tr w x y) (hG w y)
  }

-- Two bits whose sum is 0 are equal.

xor-false : ∀ {a b} → a xor b ≡ false → a ≡ b
xor-false {false} {false} _ = refl
xor-false {true}  {true}  _ = refl

-- An even number has parity 0.

odd-even : ∀ {z} → (+ 2) ∣ z → odd z ≡ false
odd-even {z} d with (+ 2) ∣? z
... | yes _  = refl
... | no ¬d = contradiction d ¬d

y-inj : ∀ {i j : Fin m} → y[_] {n} i ≡ y[ j ] → i ≡ j
y-inj refl = refl

-- Inserting a bit respects pointwise equality.

insertᵃ-cong : (j : Fin (suc k)) (c : Bool) {a b : Fin k → Bool} →
               (∀ p → a p ≡ b p) → ∀ p → insertᵃ j c a p ≡ insertᵃ j c b p
insertᵃ-cong         zero    c h zero    = refl
insertᵃ-cong         zero    c h (suc p) = h p
insertᵃ-cong {zero}  (suc ()) c h p
insertᵃ-cong {suc k} (suc j) c h zero    = h zero
insertᵃ-cong {suc k} (suc j) c h (suc p) =
  insertᵃ-cong j c (λ l → h (suc l)) p

-- Overwriting the inserted bit is inserting the new one.

insertᵃ-≔ : (i : Fin (suc k)) (b c : Bool) (y : Fin k → Bool) →
            ∀ p → (insertᵃ i b y [ i ≔ c ]) p ≡ insertᵃ i c y p
insertᵃ-≔ i b c y p = aux p (p ≟ i)
  where
  aux : ∀ p → Dec (p ≡ i) →
        (insertᵃ i b y [ i ≔ c ]) p ≡ insertᵃ i c y p
  aux .i (yes refl) =
    trans (≔-here (insertᵃ i b y) i c) (sym (insertᵃ-here i c y))
  aux p  (no p≢i)   = trans (≔-there (insertᵃ i b y) c p≢i)
    (trans (cong (insertᵃ i b y) (sym (punchIn-punchOut i≢p)))
      (trans (insertᵃ-punchIn i b y (punchOut i≢p))
        (trans (sym (insertᵃ-punchIn i c y (punchOut i≢p)))
               (cong (insertᵃ i c y) (punchIn-punchOut i≢p)))))
    where
    i≢p : i ≢ p
    i≢p e = p≢i (sym e)


------------------------------------------------------------------------
-- Quotients as Boolean expressions

-- A normal form over k variables, read through f : Fin k → Fin K.

toBExp : RM k → (Fin k → Fin m) → BExp n m
toBExp 𝟘          f = lit false
toBExp 𝟙          f = lit true
toBExp (node p q) f = toBExp p (λ i → f (suc i)) ⊕ᵉ
                      (var y[ f zero ] ∧ᵉ toBExp q (λ i → f (suc i)))

⟦toBExp⟧ : (p : RM k) (f : Fin k → Fin m) (x : Fin n → Bool)
           (y : Fin m → Bool) →
           ⟦ toBExp p f ⟧ᵉ x y ≡ evalᴿ p (λ v → y (f v))
⟦toBExp⟧ 𝟘          f x y = refl
⟦toBExp⟧ 𝟙          f x y = refl
⟦toBExp⟧ (node p q) f x y = cong₂ _xor_ (⟦toBExp⟧ p (λ i → f (suc i)) x y)
  (cong (y (f zero) ∧_) (⟦toBExp⟧ q (λ i → f (suc i)) x y))

-- It does not mention a variable outside the image of f.

∉-toBExp : (p : RM k) (f : Fin k → Fin m) {i : Fin m} →
           (∀ v → f v ≢ i) → y[_] {n} i ∉ᵉ toBExp p f
∉-toBExp 𝟘          f h = _
∉-toBExp 𝟙          f h = _
∉-toBExp (node p q) f h =
  ∉-toBExp p (λ v → f (suc v)) (λ v → h (suc v)) ,
  (λ e → h zero (sym (y-inj e))) ,
  ∉-toBExp q (λ v → f (suc v)) (λ v → h (suc v))


------------------------------------------------------------------------
-- One step

-- [HH] at y_j, substituting for y_i (in the numbering without y_j),
-- needs the derivative of the phase in y_j to be y_i ⊕ q with q free
-- of y_i.  q is the derivative with y_i cleared; HHOk checks the rest.

quotᴿ : Fin (suc (suc k)) → Fin (suc k) → RM (suc (suc k)) → RM k
quotᴿ j i p = restrict i false (derivᴿ j p)

HHOk : Fin (suc (suc k)) → Fin (suc k) → RM (suc (suc k)) → Bool
HHOk j i p = eqᴿ (derivᴿ j p) (varᴿ i ⊕ᴿ weaken i (quotᴿ j i p))

-- No output depends on y_j.

OutOk : Fin (suc (suc k)) → (Fin n → RM (suc (suc k))) → Bool
OutOk j G = allFin (λ w → eqᴿ (derivᴿ j (G w)) 𝟘)

-- The reduct reads any value at y_j = 0 and y_i = q.

nextᴿ : Fin (suc (suc k)) → Fin (suc k) → RM (suc (suc k)) →
        RM (suc (suc k)) → RM k
nextᴿ j i p r = substitute i (quotᴿ j i p) (restrict j false r)

-- The phase and the outputs of the reduct, the phase passed once so
-- that a computation of it is shared.

nextF : Fin (suc (suc k)) → Fin (suc k) → RM (suc (suc k)) → RM k
nextF j i p = nextᴿ j i p p

nextG : Fin (suc (suc k)) → Fin (suc k) → RM (suc (suc k)) →
        (Fin n → RM (suc (suc k))) → Fin n → RM k
nextG j i p G w = nextᴿ j i p (G w)

module Reduce {N K K′ : ℕ} (ξ₀ : PathSum N K K′) where

  -- A stage: a path-sum reached from ξ₀, with the values pF and pG.

  record Stage (k : ℕ) (pF : RM k) (pG : Fin N → RM k) : Set where
    constructor stage
    field
      ξ      : PathSum N k k
      chain  : ξ₀ ⟶ᶠ* ξ
      tracks : Tracks ξ (evalᴿ pF) (λ w → evalᴿ (pG w))

  open Stage public

  -- [HH] at y_j with y_i ← q, then [Elim] of y_i.

  step : ∀ {k} {pF : RM (suc (suc k))} {pG : Fin N → RM (suc (suc k))} →
         Stage (suc (suc k)) pF pG →
         (j : Fin (suc (suc k))) (i : Fin (suc k)) →
         HHOk j i pF ≡ true → OutOk j pG ≡ true →
         Stage k (nextF j i pF) (nextG j i pF pG)
  step {k} {pF} {pG} (stage ξ ch tr) j i okF okG =
    stage _ (ch ◅◅ᶠ proj₁ res)
          (tracks-cong (proj₂ res) (value pF) (λ w → value (pG w)))
    where
    qR : RM k
    qR = quotᴿ j i pF

    q : Assign (suc k) → Bool
    q y = evalᴿ qR (λ v → y (punchIn i v))

    B : BExp N (suc k)
    B = toBExp qR (punchIn i)

    hq : ∀ x y → eval (liftᵉ B) x y ≡ [ q y ]ᶻ
    hq x y = trans (eval-liftᵉ B x y) (cong [_]ᶻ (⟦toBExp⟧ qR (punchIn i) x y))

    dF : ∀ y → evalᴿ pF (insertᵃ j true y) xor evalᴿ pF (insertᵃ j false y) ≡
               y i xor q y
    dF y = trans (sym (eval-derivᴿ j pF y))
      (trans (cong (λ t → evalᴿ t y)
                   (eqᴿ-sound (derivᴿ j pF) (varᴿ i ⊕ᴿ weaken i qR) okF))
        (trans (eval-⊕ᴿ (varᴿ i) (weaken i qR) y)
               (cong₂ _xor_ (eval-varᴿ i y) (eval-weaken i qR y))))

    dG : ∀ w y → evalᴿ (pG w) (insertᵃ j true y) ≡
                 evalᴿ (pG w) (insertᵃ j false y)
    dG w y = xor-false (trans (sym (eval-derivᴿ j (pG w) y))
      (cong (λ t → evalᴿ t y)
            (eqᴿ-sound (derivᴿ j (pG w)) 𝟘
                       (allFin-sound (λ w′ → eqᴿ (derivᴿ j (pG w′)) 𝟘) okG w))))

    res = hh-elim ξ tr j i (liftᵉ B) q hq
            (Absent-liftᵉ y[ i ] B (∉-toBExp qR (punchIn i) (punchInᵢ≢i i)))
            dF dG

    -- The reduct's values are the normal forms nextᴿ.

    value : ∀ r y →
            evalᴿ r (insertᵃ j false (insertᵃ i false y
                                       [ i ≔ q (insertᵃ i false y) ])) ≡
            evalᴿ (nextᴿ j i pF r) y
    value r y = trans
      (evalᴿ-cong r (insertᵃ-cong j false (λ p → trans
        (insertᵃ-≔ i false (q (insertᵃ i false y)) y p)
        (cong (λ c → insertᵃ i c y p)
              (evalᴿ-cong qR (insertᵃ-punchIn i false y))))))
      (sym (trans (eval-substitute i qR (restrict j false r) y)
                  (eval-restrict j false r (insertᵃ i (evalᴿ qR y) y))))


------------------------------------------------------------------------
-- Stuck: every variable occurs in an output

-- The premise of a head rule on the outputs: y₀ is internal.

private
  head-internal : {χ : PathSum n k (suc m)} {ζ : PathSum n k′ m′} →
                  χ ⟶ᴳ ζ → ∀ w → NoVar (+ 2) y₀ (out χ w)
  head-internal (elimᴳ _ _ o)                   = o
  head-internal (ωᴳ _ _ _ _ o)                  = o
  head-internal (hhᴳ _ _ _ _ _ _ o)             = o
  head-internal (caseᴳ _ _ _ _ _ _ _ _ _ _ o _) = o

-- The converse of PathSum.Reorder's NoVar-front and NoVar-front-suc:
-- absence of a renumbered variable is absence of the original one.

NoVar-unfront₀ : {c : ℤ} (j : Fin (suc m)) (P : Poly n (suc m)) →
                 NoVar c y[ zero ] (frontᴾ j P) → NoVar c y[ j ] P
NoVar-unfront₀ {c = c} j P h (α , β) j∈β =
  subst (c ∣_) (cong (λ β′ → P (α , β′))
    (trans (cong (insertAt (removeAt β j) j) (sym (Vec.[]=⇒lookup j∈β)))
           (Vec.insertAt-removeAt β j)))
    (h (α , inside ∷ removeAt β j) here)

NoVar-unfront-suc : {c : ℤ} (j : Fin (suc m)) (i : Fin m)
                    (P : Poly n (suc m)) →
                    NoVar c y[ suc i ] (frontᴾ j P) →
                    NoVar c y[ punchIn j i ] P
NoVar-unfront-suc {c = c} j i P h (α , β) p∈β =
  subst (c ∣_) (cong (λ β′ → P (α , β′)) (Vec.insertAt-removeAt β j))
    (h (α , lookup β j ∷ removeAt β j)
       (there (Vec.lookup⇒[]= i (removeAt β j) at-i)))
  where
  at-i : lookup (removeAt β j) i ≡ inside
  at-i = trans (sym (Vec.insertAt-punchIn (removeAt β j) j (lookup β j) i))
    (trans (cong (λ v → lookup v (punchIn j i)) (Vec.insertAt-removeAt β j))
           (Vec.[]=⇒lookup p∈β))

-- The variable a double renumbering front j′ (front j ·) puts first.

pos : Fin (suc m) → Fin (suc m) → Fin (suc m)
pos j zero    = j
pos j (suc l) = punchIn j l

NoVar-unfront₂ : {c : ℤ} (j j′ : Fin (suc m)) (P : Poly n (suc m)) →
                 NoVar c y[ zero ] (frontᴾ j′ (frontᴾ j P)) →
                 NoVar c y[ pos j j′ ] P
NoVar-unfront₂ j zero    P h = NoVar-unfront₀ j P (NoVar-unfront₀ zero (frontᴾ j P) h)
NoVar-unfront₂ j (suc l) P h =
  NoVar-unfront-suc j l P (NoVar-unfront₀ (suc l) (frontᴾ j P) h)

-- A variable absent modulo 2 does not change the parity of the value.

NoVar-flip : (p : Fin (suc m)) (P : Poly n (suc m)) →
             NoVar (+ 2) y[ p ] P → ∀ x y →
             odd (eval P x (insertᵃ p true y)) ≡
             odd (eval P x (insertᵃ p false y))
NoVar-flip p P h x y = trans
  (cong odd (trans (sym (eval-at p P true x y))
                   (eval-true (frontᴾ p P) x y)))
  (trans (odd-+ (eval (head-part (frontᴾ p P)) x y)
                (eval (tail-part (frontᴾ p P)) x y))
    (trans (cong (_xor odd (eval (tail-part (frontᴾ p P)) x y)) even)
           (cong odd (trans (sym (eval-false (frontᴾ p P) x y))
                            (eval-at p P false x y)))))
  where
  even : odd (eval (head-part (frontᴾ p P)) x y) ≡ false
  even = odd-even
    (eval-∣ (head-part (frontᴾ p P))
            (λ { (α , s) → NoVar-front p P h (α , inside ∷ s) here }) x y)

-- The certificate: for every variable p some output whose derivative
-- in p is 1 somewhere.

Occurs : (Fin n → RM (suc m)) → Bool
Occurs G =
  allFin (λ p → anyFin (λ w → Found (witness (derivᴿ p (G w)))))

occurs⇒irreducible : (ζ : PathSum n k (suc m)) {pF : RM (suc m)}
                     {pG : Fin n → RM (suc m)} →
                     Tracks ζ (evalᴿ pF) (λ w → evalᴿ (pG w)) →
                     Occurs pG ≡ true → Irreducibleᶠ ζ
occurs⇒irreducible ζ {pF} {pG} tr occ =
  head⇒Irreducibleᶠ ζ (λ j j′ (_ , _ , _ , s) → stuck j j′ s)
  where
  stuck : ∀ {k′ m′} {χ : PathSum _ k′ m′} (j j′ : Fin _) →
          front j′ (front j ζ) ⟶ᴳ χ → ⊥
  stuck j j′ s = absurd
    where
    p = pos j j′

    w-found = anyFin-sound (λ w → Found (witness (derivᴿ p (pG w))))
      (allFin-sound (λ p′ → anyFin (λ w → Found (witness (derivᴿ p′ (pG w)))))
                    occ p)
    w = proj₁ w-found

    ρ-found = found (derivᴿ p (pG w)) (proj₂ w-found)
    ρ = proj₁ ρ-found

    x : Fin _ → Bool
    x _ = false

    same : evalᴿ (pG w) (insertᵃ p true ρ) ≡ evalᴿ (pG w) (insertᵃ p false ρ)
    same = trans (sym (out-at tr w x (insertᵃ p true ρ)))
      (trans (NoVar-flip p (out ζ w)
               (NoVar-unfront₂ j j′ (out ζ w) (head-internal s w)) x ρ)
             (out-at tr w x (insertᵃ p false ρ)))

    absurd : ⊥
    absurd = false≢true (trans (sym (xor-same (evalᴿ (pG w) (insertᵃ p false ρ))))
      (trans (cong (_xor evalᴿ (pG w) (insertᵃ p false ρ)) (sym same))
        (trans (sym (eval-derivᴿ p (pG w) ρ)) (proj₂ ρ-found))))
      where
      false≢true : false ≡ true → ⊥
      false≢true ()
