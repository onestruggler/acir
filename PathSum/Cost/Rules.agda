------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules [Elim], [ω] and [HH] on sparse path-sums, and their cost
-- (Amy, QPL 2018, figure 2 and proposition 3.2)
--
-- Figure 2's linear rules, at any path variable y_j as
-- PathSum.Anywhere states them (elimAt, ωAt, hhAt), computed on the
-- sparse representation PathSum.Size.Sparse.Rep: a list of terms for
-- the phase and a Z₂-linear form per output.  Each rule is a program
-- in PathSum.Cost's monad, in two parts:
--
--  * a matcher reads the premises off the representation: y_j absent
--    from every form (formsFreeᶜ), and the quotient of the phase by
--    y_j (quotᶜ) of the rule's shape -- empty for [Elim]; for [ω] and
--    [HH] no term of degree 2 or more, linear coefficients 0 or ½, and
--    the constant ¼ + ½c or ½c (PathSum.Cost.Linear) -- which also
--    determines the rule's parameters: c and S, and for [HH] a path
--    variable y_i of S (the first one);
--  * a stepper computes the reduct: the rest of the phase with y_j
--    removed (restᶜ), for [ω] with ⅛ - ¼(c ⊕ ⨁S) added (the lifting
--    truncated at degree 2, the rest vanishing modulo 1), for [HH]
--    with y_i ← c ⊕ ⨁(S ∖ y_i) substituted (PathSum.Cost.Subst),
--    canonicalised at degree d; and the forms with y_j removed and,
--    for [HH], y_i substituted.
--
-- elimˢ, ωˢ and hhˢ put them together and return nothing when the rule
-- does not apply.  The soundness theorems say: for any dense path-sum
-- ξ that the input R represents (PathSum.Size.Sparse.Represents: the
-- phases agree modulo 2^M and the outputs are the liftings of the
-- forms) -- in particular for psʳ k R, the path-sum R stands for
-- (psʳ-represents) -- if every term of R has order at most d (Ordᵀ),
-- and the sparse rule returns R′, then ξ steps by that rule at y_j,
--
--    ξ ⟶ᵍ elim-reduct (front j ξ),  ω-reduct (front j ξ) c S,
--          hh-reduct (front j ξ) i c S,
--
-- R′ represents that reduct, and every term of R′ again has order at
-- most d.  (PathSum.Size.Equivalence.represents-≋ turns "represents"
-- into ≋.)  [ω] needs d ≥ 2: its reduct adds ⅛ and ¼(c ⊕ ⨁S), of
-- order 2.  The order bound is what makes the steps exact: it makes
-- the reduct's phase of degree at most d modulo 1 (lemma 2.13), so that
-- canonicalising at degree d loses nothing, and it is what truncates
-- [HH]'s substitution.  Whatever the input, R′ is canonical
-- (elimˢ-canonical, ωˢ-canonical, hhˢ-canonical): each stepper
-- computes the new phase last, with canonᶜ.
--
-- The matchers are sound for any representation.  They are not proved
-- complete here: on a representation that is not canonical (a
-- monomial repeated, a coefficient 0 modulo 2^M kept) they may miss a
-- rule that applies to the path-sum represented.  Completeness on
-- canonical representations belongs to the next phase (see the plan
-- in PathSum.Cost).
--
-- The costs are polynomial in n + m for fixed d: with B = n + m + 3
-- (Bᴿ) for a path-sum with n inputs and m + 1 path variables, and L
-- terms,
--
--    elimˢ  at most 13 (L + 1) B^(d+2)    (cost-elimˢ),
--    ωˢ     at most 39 (L + 1) B^(d+3)    (cost-ωˢ),
--    hhˢ    at most 46 (L + 1) B^(2d+2)   (cost-hhˢ),
--
-- all three at most ruleBound = 46 (L + 1) B^(2d+3).  On a list with
-- at most (n + m + 2)^d terms -- every canonical one, at most one term
-- per monomial of degree at most d (PathSum.Cost.Canon.
-- canonical-length) -- that is at most 92 B^(3d+3) (ruleBound-small;
-- canonical-cost states it for a canonical representation).
-- [HH] dominates: each of the L terms may expand into B^d, which are
-- then canonicalised.  These are bounds in the cost model of
-- PathSum.Cost, not running times of a machine, and they are not
-- claimed to be tight.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Rules (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_)
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Divisibility.Signed using (_∣_; ∣-refl; ∣m⇒∣-m)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _∸_; _^_; _≤_; z≤n; s≤s; >-nonZero)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; insertAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Anywhere M using (_⟶ᵍ_; elimAt; ωAt; hhAt; Ord≤-front)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out; tail-part)
open import PathSum.CRK.Circuit M using (Ord≤⇒Deg≤; Ord≤-weaken)
open import PathSum.Cost
open import PathSum.Cost.Bound using
  (Bnd; _≤[_]_; bound; unbound; ≤-1ᶜ; ≤-*ᶜ; ≤-+ᶜ; ≤-0ᶜ; ≤-weakenᶜ; ≤ᶜ-mono;
   lift-B; lift-LB; ^-pos; ^-mono; B*B; Bnd-≤; Bnd-small)
open import PathSum.Cost.Canon M using
  (canonᶜ; canonical; value-canonᶜ; canonical-≈; canonical-Ordᵀ; Ordᵀ;
   Ordᵀ⇒Ord≤; ∣-≡ᴹ; cost-canonᶜ; Canonical; canonical-length;
   canonᶜ-Canonical)
open import PathSum.Cost.Coeff M using
  (Coeff; 0ᶠ; coeff-0ᶠ; _==ᶠ_; ==ᶠ-true; eqᶠᶜ; _≡ᴹ_; modᴹ; ∣diff;
   ≡ᴹ-refl; ≡ᴹ-reflexive; ≡ᴹ-sym; ≡ᴹ-trans; +-≡ᴹ; *-≡ᴹ; coeff-residue)
open import PathSum.Cost.Linear M using
  (halfᶠ; Linearity; linearity; linear?; const; support; linearᶜ;
   linear-≈; cost-linearᶜ)
open import PathSum.Cost.Monomial using
  (oneᶜ; value-oneᶜ; cost-oneᶜ; clearʸᶜ; value-clearʸᶜ; cost-clearʸᶜ)
open import PathSum.Cost.Split M using
  (coeffsᶜ; value-coeffsᶜ; reading; reading-≗; reading-≈;
   quot; rest; quotᶜ; restᶜ; value-quotᶜ; value-restᶜ; ⟦quot⟧; ⟦rest⟧;
   rest-Ordᵀ; formsFreeᶜ; formsFreeᶜ-NoVar; dropForm; dropFormsᶜ;
   value-dropFormsᶜ; drop-lift; cost-formsFreeᶜ; cost-quotᶜ; cost-restᶜ;
   cost-dropFormsᶜ; length-quot; length-rest)
open import PathSum.Cost.Subst M using
  (liftTermsᶜ; value-liftTermsᶜ; deg-lift; substᶜ; subst-≈; substᶜ-≈;
   substᶜ-Ordᵀ; substForm; substFormsᶜ; value-substFormsᶜ; subst-lift;
   cost-liftTermsᶜ; cost-substᶜ; cost-substFormsᶜ; expandᶜ)
open import PathSum.Linear using (Lin; liftᴸ)
open import PathSum.Order M using
  (Ord≤; Ord≤-cong; Ord≤-+; Ord≤-∸; Ord≤-κ; Ord≤-liftXor; pow)
open import PathSum.Polynomial using
  (Mon; Poly; Var; y[_]; ⟪_⟫; 1ᵐ; _≟ᵐ_; _∈ᵐ_; _∈ᵐ?_; _∪ᵐ_; _∖ᵐ_; κ; 0ᴾ; _+ᴾ_;
   _-ᴾ_; _·ᴾ_; _≈[_]_; liftXor; NoVar)
  renaming (subst to psubst)
open import PathSum.Polynomial.Product using (monoᴾ; ≈-refl; ≈-trans; ≈-sym)
open import PathSum.Polynomial.Properties using (Σmon-cong)
open import PathSum.Reduction M using
  (elim-reduct; ω-reduct; hh-reduct; ⅛; ¼; ½; tail-Ord≤)
open import PathSum.Reorder using (front; frontᴾ; _/ʸ_; _∖ʸ_)
open import PathSum.Size.Sparse M using
  (Term; coeff; ⟦_⟧ˢ; residue; Rep; rep; terms; forms; Represents; psʳ)
open import PathSum.Size.Terms M using
  (⟦++⟧ˢ; liftTerms; liftTerms-≈; liftTerms-length≤)

import Data.Integer.Properties as ℤP
import Data.List.Properties as List
import Data.Nat.Properties as ℕ
import Data.Vec.Properties as Vec

open +-*-Solver using (solve; _:+_; _:*_; _:^_; con; _:=_)

private
  variable
    d k n m : ℕ


------------------------------------------------------------------------
-- A representation, split at y_j

-- The path-sum a representation stands for is represented by it.

psʳ-represents : (R : Rep n m) → Represents (psʳ k R) R
psʳ-represents R = (λ γ → ∣diff (≡ᴹ-refl {⟦ terms R ⟧ˢ γ})) , (λ w γ → refl)

-- The quotient and the rest of a represented phase are those of the
-- representation.

quot-≈ : (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) → Represents ξ R →
         (j : Fin (suc m)) → (phase ξ /ʸ j) ≈[ pow M ] ⟦ quot j (terms R) ⟧ˢ
quot-≈ ξ R (eqP , _) j (α , β) =
  subst (λ z → pow M ∣ (phase ξ (α , insertAt β j inside) -ℤ z))
        (sym (⟦quot⟧ j (terms R) α β)) (eqP (α , insertAt β j inside))

rest-≈ : (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) → Represents ξ R →
         (j : Fin (suc m)) →
         tail-part (frontᴾ j (phase ξ)) ≈[ pow M ] ⟦ rest j (terms R) ⟧ˢ
rest-≈ ξ R (eqP , _) j (α , β) =
  subst (λ z → pow M ∣ (phase ξ (α , insertAt β j outside) -ℤ z))
        (sym (⟦rest⟧ j (terms R) α β)) (eqP (α , insertAt β j outside))

-- So the coefficients read off the representation (coeffsᶜ) are those
-- of the represented phase: the coefficient of y_j (the quotient's
-- constant) and those of its quadratic partners u · y_j (the
-- quotient's linear coefficients), modulo 2^M.

coeffs-represents : (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
                    Represents ξ R → (j : Fin (suc m)) →
                    value (coeffsᶜ j (terms R)) ≡ reading (phase ξ /ʸ j)
coeffs-represents ξ R rp j = trans (value-coeffsᶜ j (terms R))
  (trans (reading-≗ {P = ⟦ terms R ⟧ˢ /ʸ j} {Q = ⟦ quot j (terms R) ⟧ˢ}
                    (λ γ → sym (⟦quot⟧ j (terms R) (proj₁ γ) (proj₂ γ))))
         (sym (reading-≈ {P = phase ξ /ʸ j} {Q = ⟦ quot j (terms R) ⟧ˢ}
                         (quot-≈ ξ R rp j))))

-- The represented outputs are free of y_j when the forms are.

free-NoVar : (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) → Represents ξ R →
             (j : Fin (suc m)) → value (formsFreeᶜ j (forms R)) ≡ true →
             ∀ w → NoVar (+ 2) y[ j ] (out ξ w)
free-NoVar ξ R (_ , eqf) j eq w γ j∈γ =
  subst ((+ 2) ∣_) (sym (eqf w γ))
        (formsFreeᶜ-NoVar j (forms R) eq w γ j∈γ)

-- Their parts free of y_j are the liftings of the renumbered forms.

drop-outs : (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) → Represents ξ R →
            (j : Fin (suc m)) → ∀ w γ →
            tail-part (frontᴾ j (out ξ w)) γ ≡ liftᴸ (dropForm j (forms R w)) γ
drop-outs ξ R (_ , eqf) j w (α , β) =
  trans (eqf w (α , insertAt β j outside)) (drop-lift j (forms R w) α β)

drop-outsᶜ : (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) → Represents ξ R →
             (j : Fin (suc m)) → ∀ w γ →
             tail-part (frontᴾ j (out ξ w)) γ ≡
             liftᴸ (value (dropFormsᶜ j (forms R)) w) γ
drop-outsᶜ ξ R rp j w γ = trans (drop-outs ξ R rp j w γ)
  (cong (λ l → liftᴸ l γ) (sym (value-dropFormsᶜ j (forms R) w)))

-- The represented phase has the order of the terms.

phase-Ord≤ : (ξ : PathSum n k m) (R : Rep n m) → Represents ξ R →
             Ordᵀ d (terms R) → Ord≤ d (phase ξ)
phase-Ord≤ ξ R (eqP , _) ord =
  Ord≤-cong {P = ⟦ terms R ⟧ˢ} {Q = phase ξ}
    (≈-sym {P = phase ξ} {Q = ⟦ terms R ⟧ˢ} eqP) (Ordᵀ⇒Ord≤ ord)

-- A polynomial of order at most d that a list stands for is stood for
-- by the list's canonical form, whose terms have order at most d.

canon-represents : (d : ℕ) {X : Poly n m} (ts : List (Term n m)) →
                   X ≈[ pow M ] ⟦ ts ⟧ˢ → Ord≤ d X →
                   (X ≈[ pow M ] ⟦ value (canonᶜ d ts) ⟧ˢ) ×
                   Ordᵀ d (value (canonᶜ d ts))
canon-represents d {X} ts X≈ ordX =
  ≈-trans {P = X} {Q = ⟦ ts ⟧ˢ} {R = ⟦ value (canonᶜ d ts) ⟧ˢ} X≈
    (subst (λ us → ⟦ ts ⟧ˢ ≈[ pow M ] ⟦ us ⟧ˢ) (sym (value-canonᶜ d ts))
           (canonical-≈ d ⟦ ts ⟧ˢ (Ord≤⇒Deg≤ ordT))) ,
  subst (Ordᵀ d) (sym (value-canonᶜ d ts)) (canonical-Ordᵀ d ⟦ ts ⟧ˢ ordT)
  where
  ordT : Ord≤ d ⟦ ts ⟧ˢ
  ordT = Ord≤-cong {P = X} {Q = ⟦ ts ⟧ˢ} X≈ ordX

private
  ∧-true : ∀ a b → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
  ∧-true true true _ = refl , refl

  branch-just : ∀ {A : Set} (b : Bool) (X : Cost A) {a : A} →
                value (if b then (just <$> X) else pure nothing) ≡ just a →
                (b ≡ true) × (value X ≡ a)
  branch-just true  X refl = refl , refl
  branch-just false X ()


------------------------------------------------------------------------
-- [Elim]

-- It applies when y_j is in no output and in no term of the phase.

matchElimᶜ : Fin (suc m) → Rep n (suc m) → Cost Bool
matchElimᶜ j R = do
  free ← formsFreeᶜ j (forms R)
  q    ← quotᶜ j (terms R)
  e    ← nullᶜ q
  pure (free ∧ e)

stepElimᶜ : ℕ → Fin (suc m) → Rep n (suc m) → Cost (Rep n m)
stepElimᶜ d j R = do
  r   ← restᶜ j (terms R)
  ts′ ← canonᶜ d r
  fs  ← dropFormsᶜ j (forms R)
  pure (rep ts′ fs)

elimBranchᶜ : ℕ → Fin (suc m) → Rep n (suc m) → Bool →
              Cost (Maybe (Rep n m))
elimBranchᶜ d j R b = if b then (just <$> stepElimᶜ d j R) else pure nothing

elimˢ : ℕ → Fin (suc m) → Rep n (suc m) → Cost (Maybe (Rep n m))
elimˢ d j R = matchElimᶜ j R >>= elimBranchᶜ d j R

elimˢ-sound : (d : ℕ) (j : Fin (suc m)) (ξ : PathSum n (suc (suc k)) (suc m))
              (R : Rep n (suc m)) → Represents ξ R → Ordᵀ d (terms R) →
              ∀ {R′} → value (elimˢ d j R) ≡ just R′ →
              (ξ ⟶ᵍ elim-reduct (front j ξ)) ×
              Represents (elim-reduct (front j ξ)) R′ × Ordᵀ d (terms R′)
elimˢ-sound d j ξ R rp ord {R′} eq = finish R′ (proj₂ bj)
  where
  bj = branch-just (value (matchElimᶜ j R)) (stepElimᶜ d j R) eq
  mt = ∧-true _ _ (proj₁ bj)

  q≡[] : quot j (terms R) ≡ []
  q≡[] = trans (sym (value-quotᶜ j (terms R)))
               (nullᶜ-true (value (quotᶜ j (terms R))) (proj₂ mt))

  eqP : (phase ξ /ʸ j) ≈[ pow M ] 0ᴾ
  eqP = subst (λ us → (phase ξ /ʸ j) ≈[ pow M ] ⟦ us ⟧ˢ) q≡[]
              (quot-≈ ξ R rp j)

  r = value (restᶜ j (terms R))

  X≈ : tail-part (frontᴾ j (phase ξ)) ≈[ pow M ] ⟦ r ⟧ˢ
  X≈ = subst (λ us → tail-part (frontᴾ j (phase ξ)) ≈[ pow M ] ⟦ us ⟧ˢ)
             (sym (value-restᶜ j (terms R))) (rest-≈ ξ R rp j)

  ordX : Ord≤ d (tail-part (frontᴾ j (phase ξ)))
  ordX = tail-Ord≤ (Ord≤-front j (phase-Ord≤ ξ R rp ord))

  cr = canon-represents d r X≈ ordX

  finish : ∀ R′ → value (stepElimᶜ d j R) ≡ R′ →
           (ξ ⟶ᵍ elim-reduct (front j ξ)) ×
           Represents (elim-reduct (front j ξ)) R′ × Ordᵀ d (terms R′)
  finish _ refl = elimAt ξ j eqP (free-NoVar ξ R rp j (proj₁ mt)) ,
                  (proj₁ cr , drop-outsᶜ ξ R rp j) , proj₂ cr


------------------------------------------------------------------------
-- [ω]

-- The constants: ¼ + ½c, ⅛, and -¼, as coefficients.

quarterᶠ : Bool → Coeff
quarterᶠ c = residue (¼ +ℤ ½ *ℤ [ c ]ᶻ)

eighthᶠ : Coeff
eighthᶠ = residue ⅛

mquarterᶠ : Coeff
mquarterᶠ = residue (- ¼)

-- The quotient is ¼ + ½(c ⊕ ⨁S) for c read off its constant.

ωVerdict : Bool → Linearity n m → Bool → Bool → Maybe (Bool × Mon n m)
ωVerdict free lin e₀ e₁ =
  if free ∧ linear? lin
  then (if e₀ then just (false , support lin)
        else (if e₁ then just (true , support lin) else nothing))
  else nothing

matchωᶜ : Fin (suc m) → Rep n (suc m) → Cost (Maybe (Bool × Mon n m))
matchωᶜ j R = do
  free ← formsFreeᶜ j (forms R)
  q    ← quotᶜ j (terms R)
  lin  ← linearᶜ q
  e₀   ← eqᶠᶜ (const lin) (quarterᶠ false)
  e₁   ← eqᶠᶜ (const lin) (quarterᶠ true)
  pure (ωVerdict free lin e₀ e₁)

-- The reduct: ⅛ - ¼(c ⊕ ⨁S), truncated at degree 2, and the rest.

stepωᶜ : ℕ → Fin (suc m) → Bool → Mon n m → Rep n (suc m) → Cost (Rep n m)
stepωᶜ d j c S R = do
  r   ← restᶜ j (terms R)
  o   ← oneᶜ
  us  ← liftTermsᶜ mquarterᶠ 2 (c , S)
  ts  ← appendᶜ us r
  ts′ ← canonᶜ d ((o , eighthᶠ) ∷ ts)
  fs  ← dropFormsᶜ j (forms R)
  pure (rep ts′ fs)

ωCont : ℕ → Fin (suc m) → Rep n (suc m) → Maybe (Bool × Mon n m) →
        Cost (Maybe (Bool × Mon n m × Rep n m))
ωCont d j R nothing        = pure nothing
ωCont d j R (just (c , S)) = (λ R′ → just (c , S , R′)) <$> stepωᶜ d j c S R

ωˢ : ℕ → Fin (suc m) → Rep n (suc m) → Cost (Maybe (Bool × Mon n m × Rep n m))
ωˢ d j R = matchωᶜ j R >>= ωCont d j R

private
  ωVerdict-just : ∀ free (lin : Linearity n m) e₀ e₁ {c S} →
                  ωVerdict free lin e₀ e₁ ≡ just (c , S) →
                  (free ≡ true) × (linear? lin ≡ true) × (S ≡ support lin) ×
                  ((if c then e₁ else e₀) ≡ true)
  ωVerdict-just true  (linearity true  a s) true  e₁    refl =
    refl , refl , refl , refl
  ωVerdict-just true  (linearity true  a s) false true  refl =
    refl , refl , refl , refl
  ωVerdict-just true  (linearity true  a s) false false ()
  ωVerdict-just true  (linearity false a s) e₀    e₁    ()
  ωVerdict-just false lin                   e₀    e₁    ()

  ωCont-just : ∀ d (j : Fin (suc m)) (R : Rep n (suc m))
               (mc : Maybe (Bool × Mon n m)) {c S R′} →
               value (ωCont d j R mc) ≡ just (c , S , R′) →
               (mc ≡ just (c , S)) × (value (stepωᶜ d j c S R) ≡ R′)
  ωCont-just d j R nothing        ()
  ωCont-just d j R (just (c , S)) refl = refl , refl

  pick : (a : Coeff) (x : Bool → Coeff) (c : Bool) →
         (if c then (a ==ᶠ x true) else (a ==ᶠ x false)) ≡ true → a ≡ x c
  pick a x true  eq = ==ᶠ-true a (x true) eq
  pick a x false eq = ==ᶠ-true a (x false) eq

  -- -a·z modulo 2^M, with the scalar on the left.
  *-≡ᴹʳ : ∀ {a b} (z : ℤ) → a ≡ᴹ b → (a *ℤ z) ≡ᴹ (b *ℤ z)
  *-≡ᴹʳ {a} {b} z h = ≡ᴹ-trans (≡ᴹ-reflexive (ℤP.*-comm a z))
    (≡ᴹ-trans (*-≡ᴹ z h) (≡ᴹ-reflexive (ℤP.*-comm z b)))

  -- κ ⅛ is the single term ⅛ at 1.
  κ-term : ∀ (b : Bool) →
           (if b then ⅛ else 0ℤ) ≡ᴹ coeff eighthᶠ *ℤ (if b then 1ℤ else 0ℤ)
  κ-term true  = ≡ᴹ-trans (≡ᴹ-sym (coeff-residue ⅛))
                          (≡ᴹ-reflexive (sym (ℤP.*-identityʳ (coeff eighthᶠ))))
  κ-term false = ≡ᴹ-reflexive (sym (ℤP.*-zeroʳ (coeff eighthᶠ)))

  -- ¼ divides -¼ modulo 2^M, so -¼ ⊕-lifted vanishes above degree 2.
  mquarter-∣ : pow (M ∸ 2) ∣ coeff mquarterᶠ
  mquarter-∣ = ∣-≡ᴹ (ℕ.m∸n≤m M 2) (∣m⇒∣-m ∣-refl)
                   (≡ᴹ-sym (coeff-residue (- ¼)))

ωˢ-sound : (d : ℕ) → 2 ≤ d → (j : Fin (suc m))
           (ξ : PathSum n (suc k) (suc m)) (R : Rep n (suc m)) →
           Represents ξ R → Ordᵀ d (terms R) →
           ∀ {c S R′} → value (ωˢ d j R) ≡ just (c , S , R′) →
           (ξ ⟶ᵍ ω-reduct (front j ξ) c S) ×
           Represents (ω-reduct (front j ξ) c S) R′ × Ordᵀ d (terms R′)
ωˢ-sound {m = m} {n = n} d 2≤d j ξ R rp ord {c} {S} {R′} eq =
  finish R′ (proj₂ cj)
  where
  cj = ωCont-just d j R (value (matchωᶜ j R)) eq

  q    = value (quotᶜ j (terms R))
  lin  = value (linearᶜ q)
  free = value (formsFreeᶜ j (forms R))

  vj = ωVerdict-just free lin (const lin ==ᶠ quarterᶠ false)
                     (const lin ==ᶠ quarterᶠ true) (proj₁ cj)

  S≡ : S ≡ support lin
  S≡ = proj₁ (proj₂ (proj₂ vj))

  hc : coeff (const lin) ≡ᴹ ¼ +ℤ ½ *ℤ [ c ]ᶻ
  hc = ≡ᴹ-trans (≡ᴹ-reflexive (cong coeff
                  (pick (const lin) quarterᶠ c (proj₂ (proj₂ (proj₂ vj))))))
                (coeff-residue (¼ +ℤ ½ *ℤ [ c ]ᶻ))

  eqP : (phase ξ /ʸ j) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c S))
  eqP = ≈-trans {P = phase ξ /ʸ j} {Q = ⟦ quot j (terms R) ⟧ˢ}
                {R = κ ¼ +ᴾ (½ ·ᴾ liftXor c S)}
    (quot-≈ ξ R rp j)
    (subst (λ us → ⟦ us ⟧ˢ ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c S)))
           (value-quotᶜ j (terms R))
           (subst (λ T → ⟦ q ⟧ˢ ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c T)))
                  (sym S≡)
                  (linear-≈ q (proj₁ (proj₂ vj)) ¼ c hc)))

  -- The reduct's phase and the list the stepper canonicalises.
  X : Poly n m
  X = (κ ⅛ -ᴾ (¼ ·ᴾ liftXor c S)) +ᴾ tail-part (frontᴾ j (phase ξ))

  r  = value (restᶜ j (terms R))
  us = value (liftTermsᶜ mquarterᶠ 2 (c , S))
  T  = (value (oneᶜ {n} {m}) , eighthᶠ) ∷ value (appendᶜ us r)

  us≈ : (coeff mquarterᶠ ·ᴾ liftᴸ (c , S)) ≈[ pow M ] ⟦ us ⟧ˢ
  us≈ = subst (λ vs → (coeff mquarterᶠ ·ᴾ liftᴸ (c , S)) ≈[ pow M ] ⟦ vs ⟧ˢ)
              (sym (value-liftTermsᶜ mquarterᶠ 2 (c , S)))
              (liftTerms-≈ (coeff mquarterᶠ) 2 (c , S)
                           (deg-lift mquarterᶠ 2 (c , S) mquarter-∣))

  r≈ : tail-part (frontᴾ j (phase ξ)) ≈[ pow M ] ⟦ r ⟧ˢ
  r≈ = subst (λ vs → tail-part (frontᴾ j (phase ξ)) ≈[ pow M ] ⟦ vs ⟧ˢ)
             (sym (value-restᶜ j (terms R))) (rest-≈ ξ R rp j)

  X≈ : X ≈[ pow M ] ⟦ T ⟧ˢ
  X≈ γ = ∣diff (≡ᴹ-trans
    (+-≡ᴹ (+-≡ᴹ (≡ᴹ-trans (≡ᴹ-reflexive refl) (κ-term ⌊ γ ≟ᵐ 1ᵐ ⌋))
                (≡ᴹ-trans (≡ᴹ-reflexive (ℤP.neg-distribˡ-* ¼ (liftXor c S γ)))
                  (≡ᴹ-trans (*-≡ᴹʳ (liftXor c S γ)
                               (≡ᴹ-sym (coeff-residue (- ¼))))
                            (modᴹ (us≈ γ)))))
          (modᴹ (r≈ γ)))
    (≡ᴹ-reflexive (trans (ℤP.+-assoc (coeff eighthᶠ *ℤ monoᴾ 1ᵐ γ)
                                     (⟦ us ⟧ˢ γ) (⟦ r ⟧ˢ γ))
      (sym (cong₂ _+ℤ_
        (cong (λ δ → coeff eighthᶠ *ℤ monoᴾ δ γ) (value-oneᶜ {n} {m}))
        (trans (cong (λ vs → ⟦ vs ⟧ˢ γ) (value-appendᶜ us r))
               (⟦++⟧ˢ us r γ)))))))

  ordX : Ord≤ d X
  ordX = Ord≤-+ {P = κ ⅛ -ᴾ (¼ ·ᴾ liftXor c S)}
                {Q = tail-part (frontᴾ j (phase ξ))}
    (Ord≤-∸ {P = κ ⅛} {Q = ¼ ·ᴾ liftXor c S}
      (Ord≤-weaken 2≤d (Ord≤-κ {d = 2} {c = ⅛} ∣-refl))
      (Ord≤-weaken 2≤d (Ord≤-liftXor 2 c S)))
    (tail-Ord≤ (Ord≤-front j (phase-Ord≤ ξ R rp ord)))

  cr = canon-represents d T X≈ ordX

  finish : ∀ R′ → value (stepωᶜ d j c S R) ≡ R′ →
           (ξ ⟶ᵍ ω-reduct (front j ξ) c S) ×
           Represents (ω-reduct (front j ξ) c S) R′ × Ordᵀ d (terms R′)
  finish _ refl = ωAt ξ j c S eqP (free-NoVar ξ R rp j (proj₁ vj)) ,
                  (proj₁ cr , drop-outsᶜ ξ R rp j) , proj₂ cr


------------------------------------------------------------------------
-- [HH]

-- The constant of ½(c ⊕ ⨁S): ½c.

hhConst : Bool → Coeff
hhConst c = if c then halfᶠ else 0ᶠ

-- The quotient is ½(c ⊕ ⨁S), and S has a path variable y_i.

hhVerdict : Bool → Linearity n m → Bool → Bool → Maybe (Fin m) →
            Maybe (Fin m × Bool × Mon n m)
hhVerdict free lin e₀ e₁ nothing  = nothing
hhVerdict free lin e₀ e₁ (just i) =
  if free ∧ linear? lin
  then (if e₀ then just (i , false , support lin)
        else (if e₁ then just (i , true , support lin) else nothing))
  else nothing

matchHHᶜ : Fin (suc m) → Rep n (suc m) → Cost (Maybe (Fin m × Bool × Mon n m))
matchHHᶜ j R = do
  free ← formsFreeᶜ j (forms R)
  q    ← quotᶜ j (terms R)
  lin  ← linearᶜ q
  e₀   ← eqᶠᶜ (const lin) 0ᶠ
  e₁   ← eqᶠᶜ (const lin) halfᶠ
  mi   ← firstᶜ (proj₂ (support lin))
  pure (hhVerdict free lin e₀ e₁ mi)

-- The reduct: y_i ← c ⊕ ⨁(S ∖ y_i) in the rest and in the forms.

stepHHᶜ : ℕ → Fin (suc m) → Fin m → Bool → Mon n m → Rep n (suc m) →
          Cost (Rep n m)
stepHHᶜ d j i c S R = do
  r   ← restᶜ j (terms R)
  S′  ← clearʸᶜ S i
  ts′ ← substᶜ d i (c , S′) r
  fs  ← dropFormsᶜ j (forms R)
  fs′ ← substFormsᶜ i (c , S′) fs
  pure (rep ts′ fs′)

hhCont : ℕ → Fin (suc m) → Rep n (suc m) → Maybe (Fin m × Bool × Mon n m) →
         Cost (Maybe (Fin m × Bool × Mon n m × Rep n m))
hhCont d j R nothing            = pure nothing
hhCont d j R (just (i , c , S)) =
  (λ R′ → just (i , c , S , R′)) <$> stepHHᶜ d j i c S R

hhˢ : ℕ → Fin (suc m) → Rep n (suc m) →
      Cost (Maybe (Fin m × Bool × Mon n m × Rep n m))
hhˢ d j R = matchHHᶜ j R >>= hhCont d j R

private
  hhVerdict-just : ∀ free (lin : Linearity n m) e₀ e₁ mi {i c S} →
                   hhVerdict free lin e₀ e₁ mi ≡ just (i , c , S) →
                   (free ≡ true) × (linear? lin ≡ true) × (S ≡ support lin) ×
                   (mi ≡ just i) × ((if c then e₁ else e₀) ≡ true)
  hhVerdict-just free  lin                   e₀    e₁    nothing  ()
  hhVerdict-just true  (linearity true  a s) true  e₁    (just i) refl =
    refl , refl , refl , refl , refl
  hhVerdict-just true  (linearity true  a s) false true  (just i) refl =
    refl , refl , refl , refl , refl
  hhVerdict-just true  (linearity true  a s) false false (just i) ()
  hhVerdict-just true  (linearity false a s) e₀    e₁    (just i) ()
  hhVerdict-just false lin                   e₀    e₁    (just i) ()

  hhCont-just : ∀ d (j : Fin (suc m)) (R : Rep n (suc m))
                (mc : Maybe (Fin m × Bool × Mon n m)) {i c S R′} →
                value (hhCont d j R mc) ≡ just (i , c , S , R′) →
                (mc ≡ just (i , c , S)) × (value (stepHHᶜ d j i c S R) ≡ R′)
  hhCont-just d j R nothing            ()
  hhCont-just d j R (just (i , c , S)) refl = refl , refl

  pickᴴ : (a : Coeff) (c : Bool) →
          (if c then (a ==ᶠ halfᶠ) else (a ==ᶠ 0ᶠ)) ≡ true → a ≡ hhConst c
  pickᴴ a true  eq = ==ᶠ-true a halfᶠ eq
  pickᴴ a false eq = ==ᶠ-true a 0ᶠ eq

  hh-const : (c : Bool) → coeff (hhConst c) ≡ᴹ 0ℤ +ℤ ½ *ℤ [ c ]ᶻ
  hh-const true  = ≡ᴹ-trans (coeff-residue ½) (≡ᴹ-reflexive (sym (trans
    (ℤP.+-identityˡ (½ *ℤ 1ℤ)) (ℤP.*-identityʳ ½))))
  hh-const false = ≡ᴹ-reflexive (trans coeff-0ᶠ (sym (trans
    (ℤP.+-identityˡ (½ *ℤ 0ℤ)) (ℤP.*-zeroʳ ½))))

  κ0 : ∀ (γ : Mon n m) (z : ℤ) → κ 0ℤ γ +ℤ z ≡ z
  κ0 γ z = by ⌊ γ ≟ᵐ 1ᵐ ⌋
    where
    by : ∀ b → (if b then 0ℤ else 0ℤ) +ℤ z ≡ z
    by true  = ℤP.+-identityˡ z
    by false = ℤP.+-identityˡ z

  -- Substitution reads a polynomial only through its coefficients.
  psubst-≗ : (v : Var n m) (c : Bool) (S : Mon n m) {P Q : Poly n m} →
             (∀ γ → P γ ≡ Q γ) → ∀ γ → psubst P v c S γ ≡ psubst Q v c S γ
  psubst-≗ v c S {P} {Q} h γ = cong₂ _+ℤ_
    (cong (λ z → if ⌊ v ∈ᵐ? γ ⌋ then 0ℤ else z) (h γ))
    (Σmon-cong (λ δ → Σmon-cong (λ β →
      cong (λ z → if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ
                  else (if ⌊ (δ ∪ᵐ β) ≟ᵐ γ ⌋ then z *ℤ liftXor c S β
                        else 0ℤ))
           (h (δ ∪ᵐ ⟪ v ⟫)))))

hhˢ-sound : (d : ℕ) (j : Fin (suc m)) (ξ : PathSum n k (suc m))
            (R : Rep n (suc m)) → Represents ξ R → Ordᵀ d (terms R) →
            ∀ {i c S R′} → value (hhˢ d j R) ≡ just (i , c , S , R′) →
            (ξ ⟶ᵍ hh-reduct (front j ξ) i c S) ×
            Represents (hh-reduct (front j ξ) i c S) R′ × Ordᵀ d (terms R′)
hhˢ-sound {m = m} {n = n} d j ξ R rp ord {i} {c} {S} {R′} eq =
  finish R′ (proj₂ cj)
  where
  cj = hhCont-just d j R (value (matchHHᶜ j R)) eq

  q    = value (quotᶜ j (terms R))
  lin  = value (linearᶜ q)
  free = value (formsFreeᶜ j (forms R))
  mi   = value (firstᶜ (proj₂ (support lin)))

  vj = hhVerdict-just free lin (const lin ==ᶠ 0ᶠ) (const lin ==ᶠ halfᶠ) mi
                      (proj₁ cj)

  S≡ : S ≡ support lin
  S≡ = proj₁ (proj₂ (proj₂ vj))

  i∈S : y[ i ] ∈ᵐ S
  i∈S = Vec.lookup⇒[]= i (proj₂ S)
    (trans (cong (λ T → lookup (proj₂ T) i) S≡)
           (firstᶜ-just (proj₂ (support lin))
                        (proj₁ (proj₂ (proj₂ (proj₂ vj))))))

  hc : coeff (const lin) ≡ᴹ 0ℤ +ℤ ½ *ℤ [ c ]ᶻ
  hc = ≡ᴹ-trans (≡ᴹ-reflexive (cong coeff
                  (pickᴴ (const lin) c (proj₂ (proj₂ (proj₂ (proj₂ vj)))))))
                (hh-const c)

  eqP : (phase ξ /ʸ j) ≈[ pow M ] (½ ·ᴾ liftXor c S)
  eqP γ = subst (λ z → pow M ∣ ((phase ξ /ʸ j) γ -ℤ z))
    (κ0 γ (½ *ℤ liftXor c S γ))
    (≈-trans {P = phase ξ /ʸ j} {Q = ⟦ quot j (terms R) ⟧ˢ}
             {R = κ 0ℤ +ᴾ (½ ·ᴾ liftXor c S)}
      (quot-≈ ξ R rp j)
      (subst (λ us → ⟦ us ⟧ˢ ≈[ pow M ] (κ 0ℤ +ᴾ (½ ·ᴾ liftXor c S)))
             (value-quotᶜ j (terms R))
             (subst (λ T → ⟦ q ⟧ˢ ≈[ pow M ] (κ 0ℤ +ᴾ (½ ·ᴾ liftXor c T)))
                    (sym S≡)
                    (linear-≈ q (proj₁ (proj₂ vj)) 0ℤ c hc)))
      γ)

  S″ = S ∖ᵐ y[ i ]
  r  = rest j (terms R)

  ordr : Ordᵀ d r
  ordr = rest-Ordᵀ d j (terms R) ord

  tail≈ : tail-part (frontᴾ j (phase ξ)) ≈[ pow M ] ⟦ r ⟧ˢ
  tail≈ = rest-≈ ξ R rp j

  -- The phase: substitute in the rest, then canonicalise.
  phase≈ : ∀ r′ → r′ ≡ r → ∀ S′ → S′ ≡ S″ →
           psubst (tail-part (frontᴾ j (phase ξ))) y[ i ] c S″ ≈[ pow M ]
           ⟦ value (substᶜ d i (c , S′) r′) ⟧ˢ
  phase≈ _ refl _ refl =
    ≈-trans {P = psubst (tail-part (frontᴾ j (phase ξ))) y[ i ] c S″}
            {Q = psubst ⟦ r ⟧ˢ y[ i ] c S″}
            {R = ⟦ value (substᶜ d i (c , S″) r) ⟧ˢ}
      (subst-≈ i c S″ {P = tail-part (frontᴾ j (phase ξ))} {Q = ⟦ r ⟧ˢ} tail≈)
      (substᶜ-≈ d i c S″ r ordr)

  ord′ : ∀ r′ → r′ ≡ r → ∀ S′ → S′ ≡ S″ →
         Ordᵀ d (value (substᶜ d i (c , S′) r′))
  ord′ _ refl _ refl = substᶜ-Ordᵀ d i c S″ r ordr

  -- The outputs: substitute in the renumbered forms.
  outs : ∀ S′ → S′ ≡ S″ → ∀ w γ →
         psubst (tail-part (frontᴾ j (out ξ w))) y[ i ] c S″ γ ≡
         liftᴸ (value (substFormsᶜ i (c , S′)
                                   (value (dropFormsᶜ j (forms R)))) w) γ
  outs _ refl w γ = trans
    (psubst-≗ y[ i ] c S″ (drop-outs ξ R rp j w) γ)
    (trans (subst-lift i c S″ (dropForm j (forms R w)) γ)
      (cong (λ l → liftᴸ l γ) (sym (trans
        (value-substFormsᶜ i (c , S″) (value (dropFormsᶜ j (forms R))) w)
        (cong (substForm i (c , S″)) (value-dropFormsᶜ j (forms R) w))))))

  finish : ∀ R′ → value (stepHHᶜ d j i c S R) ≡ R′ →
           (ξ ⟶ᵍ hh-reduct (front j ξ) i c S) ×
           Represents (hh-reduct (front j ξ) i c S) R′ × Ordᵀ d (terms R′)
  finish _ refl =
    hhAt ξ j i c S i∈S eqP (free-NoVar ξ R rp j (proj₁ vj)) ,
    (phase≈ (value (restᶜ j (terms R))) (value-restᶜ j (terms R))
            (value (clearʸᶜ S i)) (value-clearʸᶜ S i) ,
     outs (value (clearʸᶜ S i)) (value-clearʸᶜ S i)) ,
    ord′ (value (restᶜ j (terms R))) (value-restᶜ j (terms R))
         (value (clearʸᶜ S i)) (value-clearʸᶜ S i)


------------------------------------------------------------------------
-- The outputs are canonical

-- Each stepper computes the new phase last, with canonᶜ (for [HH]
-- inside substᶜ), so what a rule returns is canonical
-- (PathSum.Cost.Canon.Canonical), whatever its input: rewriting keeps
-- a representation canonical, and with it canonical-length's bound on
-- the number of terms.

elimˢ-canonical : (d : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
                  ∀ {R′} → value (elimˢ d j R) ≡ just R′ →
                  Canonical d (terms R′)
elimˢ-canonical d j R eq =
  subst (λ R₁ → Canonical d (terms R₁))
        (proj₂ (branch-just (value (matchElimᶜ j R)) (stepElimᶜ d j R) eq))
        (canonᶜ-Canonical d (value (restᶜ j (terms R))))

ωˢ-canonical : (d : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
               ∀ {c S R′} → value (ωˢ d j R) ≡ just (c , S , R′) →
               Canonical d (terms R′)
ωˢ-canonical {m = m} {n = n} d j R {c} {S} eq =
  subst (λ R₁ → Canonical d (terms R₁))
        (proj₂ (ωCont-just d j R (value (matchωᶜ j R)) eq))
        (canonᶜ-Canonical d ((value (oneᶜ {n} {m}) , eighthᶠ) ∷
          value (appendᶜ (value (liftTermsᶜ mquarterᶠ 2 (c , S)))
                         (value (restᶜ j (terms R))))))

hhˢ-canonical : (d : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
                ∀ {i c S R′} → value (hhˢ d j R) ≡ just (i , c , S , R′) →
                Canonical d (terms R′)
hhˢ-canonical d j R {i} {c} {S} eq =
  subst (λ R₁ → Canonical d (terms R₁))
        (proj₂ (hhCont-just d j R (value (matchHHᶜ j R)) eq))
        (canonᶜ-Canonical d
          (value (expandᶜ d i (c , value (clearʸᶜ S i))
                          (value (restᶜ j (terms R))))))


------------------------------------------------------------------------
-- Costs

-- B = n + m + 3, for a path-sum with n inputs and m + 1 path
-- variables: it bounds n, m + 3, and the n + m + 2 steps a
-- canonicalisation pays per term and monomial.  Every part of a rule
-- costs at most a constant times Bnd L B e = (L + 1) B^e, L the number
-- of terms; the constants add up.

Bᴿ : ℕ → ℕ → ℕ
Bᴿ n m = 3 + (n + m)

private
  sq≤ : ∀ {a b B} → a ≤ B → b ≤ B → a * b ≤ B ^ 2
  sq≤ {B = B} a≤ b≤ = ℕ.≤-trans (ℕ.*-mono-≤ a≤ b≤) (ℕ.≤-reflexive (B*B B))

  B≤B¹ : ∀ B → B ≤ B ^ 1
  B≤B¹ B = ℕ.≤-reflexive (sym (ℕ.*-identityʳ B))

  -- The parts, for a rule on n inputs and m + 1 path variables with L
  -- terms, bounded at the exponent e.
  module Parts (n m L e : ℕ) where

    B : ℕ
    B = Bᴿ n m

    1≤B : 1 ≤ B
    1≤B = s≤s z≤n

    n≤B : n ≤ B
    n≤B = ℕ.≤-trans (ℕ.m≤m+n n m) (ℕ.m≤n+m (n + m) 3)

    m≤B¹ : m ≤ B ^ 1
    m≤B¹ = ℕ.≤-trans (ℕ.m≤n+m m n)
             (ℕ.≤-trans (ℕ.m≤n+m (n + m) 3) (B≤B¹ B))

    3m≤B : 3 + m ≤ B
    3m≤B = ℕ.+-monoʳ-≤ 3 (ℕ.m≤n+m m n)

    2N≤B : 2 + (n + m) ≤ B
    2N≤B = ℕ.n≤1+n _

    1N≤B : suc (n + m) ≤ B
    1N≤B = ℕ.≤-trans (ℕ.n≤1+n _) (ℕ.n≤1+n _)

    -- The forms: a pass over the n wires, m + 3 steps each.
    forms≤ : 2 ≤ e → ∀ {x k} → k ≤ 3 + m → x ≤ n * k → x ≤[ 1 ] Bnd L B e
    forms≤ 2≤e k≤ x≤ = ≤-1ᶜ (lift-B L B 2 e 1≤B 2≤e
      (ℕ.≤-trans x≤ (sq≤ n≤B (ℕ.≤-trans k≤ 3m≤B))))

    -- A pass over the terms, m + 3 steps each, twice.
    pass≤ : 1 ≤ e → ∀ {x} → x ≤ 2 * (L * (3 + m)) → x ≤[ 2 ] Bnd L B e
    pass≤ 1≤e x≤ = ≤-weakenᶜ x≤ (≤-*ᶜ 2 (lift-LB L B 1 e 1≤B 1≤e
      (ℕ.*-monoʳ-≤ L (ℕ.≤-trans 3m≤B (B≤B¹ B)))))

    -- A single step.
    one≤ : ∀ {x} → x ≤ 1 → x ≤[ 1 ] Bnd L B e
    one≤ x≤ = ≤-1ᶜ (lift-B L B 0 e 1≤B z≤n x≤)

    -- At most m, or n + m, steps.
    lin≤ : 1 ≤ e → ∀ {x} → x ≤ B ^ 1 → x ≤[ 1 ] Bnd L B e
    lin≤ 1≤e x≤ = ≤-1ᶜ (lift-B L B 1 e 1≤B 1≤e x≤)

    -- Reading a quotient of at most L terms.
    read≤ : 2 ≤ e → ∀ {x L′} → L′ ≤ L → x ≤ 11 * Bnd L′ B 2 →
            x ≤[ 11 ] Bnd L B e
    read≤ 2≤e L′≤ x≤ = ≤ᶜ-mono 1≤B L′≤ 2≤e (bound x≤)

    -- Canonicalising at most L terms over n + m variables.
    canon≤ : ∀ d → suc d ≤ e → ∀ {x L′} → L′ ≤ L →
             x ≤ (L′ + 5) * suc (suc (n + m)) * suc (n + m) ^ d →
             x ≤[ 6 ] Bnd L B e
    canon≤ d d<e {x} {L′} L′≤ x≤ = ≤-weakenᶜ
      (ℕ.≤-trans x≤ (ℕ.≤-trans
        (ℕ.*-mono-≤ (ℕ.*-mono-≤ (ℕ.+-monoˡ-≤ 5 L′≤) 2N≤B)
                    (ℕ.^-monoˡ-≤ d 1N≤B))
        (ℕ.≤-reflexive (split L B (B ^ d)))))
      (≤-+ᶜ (≤-1ᶜ (lift-LB L B (suc d) e 1≤B d<e ℕ.≤-refl))
            (≤-*ᶜ 5 (lift-B L B (suc d) e 1≤B d<e ℕ.≤-refl)))
      where
      split : ∀ L B P → (L + 5) * B * P ≡ L * (B * P) + 5 * (B * P)
      split = solve 3 (λ L B P → (L :+ con 5) :* B :* P :=
                                 L :* (B :* P) :+ con 5 :* (B :* P)) refl



------------------------------------------------------------------------
-- The cost of [Elim]

-- At most 13 (L + 1) B^(d+2): two passes over the terms, one over the
-- wires, and a canonicalisation at degree d.

cost-elimˢ : (d : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
             cost (elimˢ d j R) ≤
             13 * Bnd (length (terms R)) (Bᴿ n m) (2 + d)
cost-elimˢ {m} {n} d j R = unbound
  (≤-+ᶜ match≤ (≤-weakenᶜ (branch≤ (value (matchElimᶜ j R))) step≤))
  where
  L = length (terms R)
  e = 2 + d
  open Parts n m L e

  2≤e : 2 ≤ e
  2≤e = ℕ.m≤m+n 2 d

  r = value (restᶜ j (terms R))

  lenr : length r ≤ L
  lenr = ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-restᶜ j (terms R))))
                   (length-rest j (terms R))

  match≤ : cost (matchElimᶜ j R) ≤[ 4 ] Bnd L B e
  match≤ = ≤-+ᶜ (forms≤ 2≤e ℕ.≤-refl (cost-formsFreeᶜ j (forms R)))
    (≤-+ᶜ (pass≤ (s≤s z≤n) (cost-quotᶜ j (terms R)))
      (≤-+ᶜ (one≤ (cost-nullᶜ (value (quotᶜ j (terms R))))) ≤-0ᶜ))

  step≤ : cost (stepElimᶜ d j R) ≤[ 9 ] Bnd L B e
  step≤ = ≤-+ᶜ (pass≤ (s≤s z≤n) (cost-restᶜ j (terms R)))
    (≤-+ᶜ (canon≤ d (ℕ.n≤1+n (suc d)) lenr (cost-canonᶜ d r))
      (≤-+ᶜ (forms≤ 2≤e (ℕ.n≤1+n (2 + m)) (cost-dropFormsᶜ j (forms R)))
            ≤-0ᶜ))

  branch≤ : ∀ b → cost (elimBranchᶜ d j R b) ≤ cost (stepElimᶜ d j R)
  branch≤ true  = ℕ.≤-refl
  branch≤ false = z≤n


------------------------------------------------------------------------
-- The cost of [ω]

-- At most 39 (L + 1) B^(d+3): the matcher reads the quotient, and the
-- stepper adds the at most B² terms of ¼(c ⊕ ⨁S) truncated at degree
-- 2 before canonicalising.

cost-ωˢ : (d : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
          cost (ωˢ d j R) ≤ 39 * Bnd (length (terms R)) (Bᴿ n m) (3 + d)
cost-ωˢ {m} {n} d j R = unbound
  (≤-+ᶜ match≤ (cont≤ (value (matchωᶜ j R))))
  where
  L = length (terms R)
  e = 3 + d
  open Parts n m L e

  2≤e : 2 ≤ e
  2≤e = ℕ.≤-trans (ℕ.n≤1+n 2) (ℕ.m≤m+n 3 d)

  1≤e : 1 ≤ e
  1≤e = s≤s z≤n

  q = value (quotᶜ j (terms R))

  lenq : length q ≤ L
  lenq = ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-quotᶜ j (terms R))))
                   (length-quot j (terms R))

  lin = value (linearᶜ q)

  match≤ : cost (matchωᶜ j R) ≤[ 16 ] Bnd L B e
  match≤ = ≤-+ᶜ (forms≤ 2≤e ℕ.≤-refl (cost-formsFreeᶜ j (forms R)))
    (≤-+ᶜ (pass≤ 1≤e (cost-quotᶜ j (terms R)))
      (≤-+ᶜ (read≤ 2≤e lenq (cost-linearᶜ q B 2N≤B))
        (≤-+ᶜ (one≤ ℕ.≤-refl) (≤-+ᶜ (one≤ ℕ.≤-refl) ≤-0ᶜ))))

  -- The truncated lifting: at most B² (6B + 4) ≤ 10 B³ steps, B² terms.
  cube : ∀ B → B ^ 2 * (6 * B + 4) ≡ 6 * B ^ 3 + 4 * B ^ 2
  cube = solve 1 (λ B → B :^ 2 :* (con 6 :* B :+ con 4) :=
                        con 6 :* B :^ 3 :+ con 4 :* B :^ 2) refl

  ten : ∀ B → 6 * B ^ 3 + 4 * B ^ 3 ≡ 10 * B ^ 3
  ten = solve 1 (λ B → con 6 :* B :^ 3 :+ con 4 :* B :^ 3 :=
                       con 10 :* B :^ 3) refl

  lift≤ : ∀ c S → cost (liftTermsᶜ mquarterᶠ 2 (c , S)) ≤[ 10 ] Bnd L B e
  lift≤ c S = ≤-weakenᶜ
    (ℕ.≤-trans (cost-liftTermsᶜ mquarterᶠ 2 (c , S))
      (ℕ.≤-trans (ℕ.*-mono-≤ (ℕ.^-monoˡ-≤ 2 1N≤B)
                             (ℕ.+-monoˡ-≤ 4 (ℕ.*-monoʳ-≤ 6 1N≤B)))
        (ℕ.≤-trans (ℕ.≤-reflexive (cube B))
          (ℕ.≤-trans (ℕ.+-monoʳ-≤ (6 * B ^ 3)
                        (ℕ.*-monoʳ-≤ 4 (^-mono {k = 2} {e = 3} 1≤B
                                                (s≤s (s≤s z≤n)))))
                     (ℕ.≤-reflexive (ten B))))))
    (≤-*ᶜ 10 (lift-B L B 3 e 1≤B (ℕ.m≤m+n 3 d) ℕ.≤-refl))

  lenus : ∀ c S → length (value (liftTermsᶜ mquarterᶠ 2 (c , S))) ≤ B ^ 2
  lenus c S = ℕ.≤-trans
    (ℕ.≤-reflexive (cong length (value-liftTermsᶜ mquarterᶠ 2 (c , S))))
    (ℕ.≤-trans (liftTerms-length≤ (coeff mquarterᶠ) 2 (c , S))
               (ℕ.^-monoˡ-≤ 2 1N≤B))

  r = value (restᶜ j (terms R))

  lenr : length r ≤ L
  lenr = ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-restᶜ j (terms R))))
                   (length-rest j (terms R))

  -- The list canonicalised: ⅛, the lifting, and the rest.
  lenT : ∀ c S → length ((value (oneᶜ {n} {m}) , eighthᶠ) ∷
                          value (appendᶜ
                                  (value (liftTermsᶜ mquarterᶠ 2 (c , S)))
                                  r)) ≤ L + (B ^ 2 + 1)
  lenT c S = ℕ.≤-trans
    (ℕ.≤-reflexive (cong (λ ts → suc (length ts))
      (value-appendᶜ (value (liftTermsᶜ mquarterᶠ 2 (c , S))) r)))
    (ℕ.≤-trans (s≤s (ℕ.≤-reflexive (List.length-++
                  (value (liftTermsᶜ mquarterᶠ 2 (c , S))))))
      (ℕ.≤-trans (s≤s (ℕ.+-mono-≤ (lenus c S) lenr))
        (ℕ.≤-reflexive (shuffle (B ^ 2) L))))
    where
    shuffle : ∀ X L → suc (X + L) ≡ L + (X + 1)
    shuffle = solve 2 (λ X L → con 1 :+ (X :+ L) := L :+ (X :+ con 1)) refl

  canonω≤ : ∀ c S → cost (canonᶜ d ((value (oneᶜ {n} {m}) , eighthᶠ) ∷
                     value (appendᶜ
                             (value (liftTermsᶜ mquarterᶠ 2 (c , S))) r)))
            ≤[ 8 ] Bnd L B e
  canonω≤ c S = ≤-weakenᶜ
    (ℕ.≤-trans (cost-canonᶜ d ((value (oneᶜ {n} {m}) , eighthᶠ) ∷
                 value (appendᶜ (value (liftTermsᶜ mquarterᶠ 2 (c , S))) r)))
      (ℕ.≤-trans (ℕ.*-mono-≤ (ℕ.*-mono-≤ (ℕ.+-monoˡ-≤ 5 (lenT c S)) 2N≤B)
                             (ℕ.^-monoˡ-≤ d 1N≤B))
        (ℕ.≤-reflexive (trans (split L (B ^ 2) B (B ^ d))
          (cong (λ z → L * (B * B ^ d) + 6 * (B * B ^ d) + z)
                (sym (ℕ.^-distribˡ-+-* B 2 (suc d))))))))
    (≤-+ᶜ (≤-+ᶜ (≤-1ᶜ (lift-LB L B (suc d) e 1≤B (ℕ.m≤n+m (suc d) 2)
                                ℕ.≤-refl))
                (≤-*ᶜ 6 (lift-B L B (suc d) e 1≤B (ℕ.m≤n+m (suc d) 2)
                                 ℕ.≤-refl)))
          (≤-1ᶜ (lift-B L B (2 + suc d) e 1≤B ℕ.≤-refl ℕ.≤-refl)))
    where
    split : ∀ L X B P → (L + (X + 1) + 5) * B * P ≡
                        L * (B * P) + 6 * (B * P) + X * (B * P)
    split = solve 4 (λ L X B P → (L :+ (X :+ con 1) :+ con 5) :* B :* P :=
                     L :* (B :* P) :+ con 6 :* (B :* P) :+ X :* (B :* P)) refl

  step≤ : ∀ c S → cost (stepωᶜ d j c S R) ≤[ 23 ] Bnd L B e
  step≤ c S = ≤-+ᶜ (pass≤ 1≤e (cost-restᶜ j (terms R)))
    (≤-+ᶜ (lin≤ 1≤e (ℕ.≤-trans (cost-oneᶜ {n} {m})
                                (ℕ.≤-trans (ℕ.n≤1+n _)
                                  (ℕ.≤-trans 1N≤B (B≤B¹ B)))))
      (≤-+ᶜ (lift≤ c S)
        (≤-+ᶜ (≤-1ᶜ (lift-B L B 2 e 1≤B 2≤e
                (ℕ.≤-trans (cost-appendᶜ
                              (value (liftTermsᶜ mquarterᶠ 2 (c , S))) r)
                           (lenus c S))))
          (≤-+ᶜ (canonω≤ c S)
            (≤-+ᶜ (forms≤ 2≤e (ℕ.n≤1+n (2 + m)) (cost-dropFormsᶜ j (forms R)))
                  ≤-0ᶜ)))))

  cont≤ : ∀ mc → cost (ωCont d j R mc) ≤[ 23 ] Bnd L B e
  cont≤ nothing        = bound z≤n
  cont≤ (just (c , S)) = step≤ c S


------------------------------------------------------------------------
-- The cost of [HH]

-- At most 46 (L + 1) B^(2d+2): the matcher, and the substitution --
-- up to B^d new terms for each of the L old ones, each costing up to
-- 13 B^(d+1), and the canonicalisation of the L B^d terms that result.

cost-hhˢ : (d : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
           cost (hhˢ d j R) ≤ 46 * Bnd (length (terms R)) (Bᴿ n m) (2 + (d + d))
cost-hhˢ {m} {n} d j R = unbound
  (≤-+ᶜ match≤ (cont≤ (value (matchHHᶜ j R))))
  where
  L = length (terms R)
  e = 2 + (d + d)
  open Parts n m L e

  2≤e : 2 ≤ e
  2≤e = ℕ.m≤m+n 2 (d + d)

  1≤e : 1 ≤ e
  1≤e = s≤s z≤n

  d1≤e : suc d ≤ e
  d1≤e = s≤s (ℕ.≤-trans (ℕ.m≤m+n d d) (ℕ.n≤1+n (d + d)))

  dd1≤e : suc (d + d) ≤ e
  dd1≤e = ℕ.n≤1+n (suc (d + d))

  q = value (quotᶜ j (terms R))

  lenq : length q ≤ L
  lenq = ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-quotᶜ j (terms R))))
                   (length-quot j (terms R))

  lin = value (linearᶜ q)

  match≤ : cost (matchHHᶜ j R) ≤[ 17 ] Bnd L B e
  match≤ = ≤-+ᶜ (forms≤ 2≤e ℕ.≤-refl (cost-formsFreeᶜ j (forms R)))
    (≤-+ᶜ (pass≤ 1≤e (cost-quotᶜ j (terms R)))
      (≤-+ᶜ (read≤ 2≤e lenq (cost-linearᶜ q B 2N≤B))
        (≤-+ᶜ (one≤ ℕ.≤-refl) (≤-+ᶜ (one≤ ℕ.≤-refl)
          (≤-+ᶜ (lin≤ 1≤e (ℕ.≤-trans (cost-firstᶜ (proj₂ (support lin))) m≤B¹))
                ≤-0ᶜ)))))

  r = value (restᶜ j (terms R))

  lenr : length r ≤ L
  lenr = ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-restᶜ j (terms R))))
                   (length-rest j (terms R))

  -- The substitution: 15 + 6 copies.
  B₀ = suc (n + m)

  fifteen : ∀ X → X + (13 * X + X) ≡ 15 * X
  fifteen = solve 1 (λ X → X :+ (con 13 :* X :+ X) := con 15 :* X) refl

  per≤ : suc (13 * (B * B ^ d) + B ^ d) ≤ 15 * (B * B ^ d)
  per≤ = ℕ.≤-trans
    (ℕ.+-mono-≤ (^-pos {k = suc d} 1≤B)
                (ℕ.+-monoʳ-≤ (13 * (B * B ^ d))
                  (^-mono {k = d} {e = suc d} 1≤B (ℕ.n≤1+n d))))
    (ℕ.≤-reflexive (fifteen (B * B ^ d)))

  exp≤ : length r * suc (13 * (B₀ * B₀ ^ d) + B₀ ^ d) ≤[ 15 ] Bnd L B e
  exp≤ = ≤-weakenᶜ
    (ℕ.≤-trans (ℕ.*-mono-≤ lenr
      (s≤s (ℕ.+-mono-≤ (ℕ.*-monoʳ-≤ 13 (ℕ.*-mono-≤ 1N≤B (ℕ.^-monoˡ-≤ d 1N≤B)))
                       (ℕ.^-monoˡ-≤ d 1N≤B))))
      (ℕ.≤-trans (ℕ.*-monoʳ-≤ L per≤)
        (ℕ.≤-reflexive (comm L (B * B ^ d)))))
    (≤-*ᶜ 15 (lift-LB L B (suc d) e 1≤B d1≤e ℕ.≤-refl))
    where
    comm : ∀ L X → L * (15 * X) ≡ 15 * (L * X)
    comm = solve 2 (λ L X → L :* (con 15 :* X) := con 15 :* (L :* X)) refl

  sq-split : ∀ L B P → (L * P + 5) * B * P ≡ L * (B * (P * P)) + 5 * (B * P)
  sq-split = solve 3 (λ L B P → (L :* P :+ con 5) :* B :* P :=
                                L :* (B :* (P :* P)) :+ con 5 :* (B :* P)) refl

  can≤ : (length r * B₀ ^ d + 5) * suc (suc (n + m)) * B₀ ^ d ≤[ 6 ] Bnd L B e
  can≤ = ≤-weakenᶜ
    (ℕ.≤-trans (ℕ.*-mono-≤ (ℕ.*-mono-≤ (ℕ.+-monoˡ-≤ 5
                              (ℕ.*-mono-≤ lenr (ℕ.^-monoˡ-≤ d 1N≤B)))
                            2N≤B)
                           (ℕ.^-monoˡ-≤ d 1N≤B))
      (ℕ.≤-reflexive (trans (sq-split L B (B ^ d))
        (cong (λ z → L * (B * z) + 5 * (B * B ^ d))
              (sym (ℕ.^-distribˡ-+-* B d d))))))
    (≤-+ᶜ (≤-1ᶜ (lift-LB L B (suc (d + d)) e 1≤B dd1≤e ℕ.≤-refl))
          (≤-*ᶜ 5 (lift-B L B (suc d) e 1≤B d1≤e ℕ.≤-refl)))

  subst≤ : ∀ i c S′ → cost (substᶜ d i (c , S′) r) ≤[ 21 ] Bnd L B e
  subst≤ i c S′ = ≤-weakenᶜ (cost-substᶜ d i (c , S′) r) (≤-+ᶜ exp≤ can≤)

  -- The outputs: at most B (3B + 1) ≤ 4B² steps.
  four : ∀ B → B * suc (3 * B) ≡ B + 3 * (B * B)
  four = solve 1 (λ B → B :* (con 1 :+ con 3 :* B) := B :+ con 3 :* (B :* B))
                 refl

  sforms≤ : ∀ i l fs → cost (substFormsᶜ i l fs) ≤[ 4 ] Bnd L B e
  sforms≤ i l fs = ≤-weakenᶜ
    (ℕ.≤-trans (cost-substFormsᶜ i l fs)
      (ℕ.≤-trans (ℕ.*-mono-≤ n≤B (s≤s (ℕ.*-monoʳ-≤ 3 1N≤B)))
        (ℕ.≤-trans (ℕ.≤-reflexive (four B))
          (ℕ.≤-trans (ℕ.+-monoˡ-≤ (3 * (B * B))
                        (ℕ.m≤m*n B B {{>-nonZero 1≤B}}))
            (ℕ.≤-reflexive (trans (solve 1 (λ X → X :+ con 3 :* X :=
                                              con 4 :* X) refl (B * B))
                                  (cong (4 *_) (B*B B))))))))
    (≤-*ᶜ 4 (lift-B L B 2 e 1≤B 2≤e ℕ.≤-refl))

  step≤ : ∀ i c S → cost (stepHHᶜ d j i c S R) ≤[ 29 ] Bnd L B e
  step≤ i c S = ≤-+ᶜ (pass≤ 1≤e (cost-restᶜ j (terms R)))
    (≤-+ᶜ (lin≤ 1≤e (ℕ.≤-trans (cost-clearʸᶜ S i) m≤B¹))
      (≤-+ᶜ (subst≤ i c (value (clearʸᶜ S i)))
        (≤-+ᶜ (forms≤ 2≤e (ℕ.n≤1+n (2 + m)) (cost-dropFormsᶜ j (forms R)))
          (≤-+ᶜ (sforms≤ i (c , value (clearʸᶜ S i))
                         (value (dropFormsᶜ j (forms R))))
                ≤-0ᶜ))))

  cont≤ : ∀ mc → cost (hhCont d j R mc) ≤[ 29 ] Bnd L B e
  cont≤ nothing            = bound z≤n
  cont≤ (just (i , c , S)) = step≤ i c S


------------------------------------------------------------------------
-- One bound for every rule

-- Each rule costs at most 46 (L + 1) B^(2d+3).

ruleBound : ℕ → ℕ → ℕ → ℕ → ℕ
ruleBound n m d L = 46 * Bnd L (Bᴿ n m) (3 + (d + d))

private
  weaken : ∀ {x} (B L c c′ e e′ : ℕ) → 1 ≤ B → c ≤ c′ → e ≤ e′ →
           x ≤ c * Bnd L B e → x ≤ c′ * Bnd L B e′
  weaken B L c c′ e e′ 1≤B c≤ e≤ x≤ = ℕ.≤-trans x≤
    (ℕ.*-mono-≤ c≤ (Bnd-≤ {L = L} {L′ = L} 1≤B ℕ.≤-refl e≤))

cost-elimˢ≤ : (d : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
              cost (elimˢ d j R) ≤ ruleBound n m d (length (terms R))
cost-elimˢ≤ {m} {n} d j R = weaken (Bᴿ n m) (length (terms R)) 13 46
  (2 + d) (3 + (d + d)) (s≤s z≤n) (ℕ.m≤m+n 13 33)
  (ℕ.+-monoʳ-≤ 2 (ℕ.≤-trans (ℕ.m≤m+n d d) (ℕ.n≤1+n _)))
  (cost-elimˢ d j R)

cost-ωˢ≤ : (d : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
           cost (ωˢ d j R) ≤ ruleBound n m d (length (terms R))
cost-ωˢ≤ {m} {n} d j R = weaken (Bᴿ n m) (length (terms R)) 39 46
  (3 + d) (3 + (d + d)) (s≤s z≤n) (ℕ.m≤m+n 39 7)
  (ℕ.+-monoʳ-≤ 3 (ℕ.m≤m+n d d)) (cost-ωˢ d j R)

cost-hhˢ≤ : (d : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
            cost (hhˢ d j R) ≤ ruleBound n m d (length (terms R))
cost-hhˢ≤ {m} {n} d j R = weaken (Bᴿ n m) (length (terms R)) 46 46
  (2 + (d + d)) (3 + (d + d)) (s≤s z≤n) ℕ.≤-refl
  (ℕ.n≤1+n (2 + (d + d))) (cost-hhˢ d j R)

-- On a list with at most (n + m + 2)^d terms -- a canonical one has at
-- most one term per monomial of degree at most d -- that is at most
-- 92 B^(3d+3): polynomial in n + m for fixed d.

ruleBound-small : ∀ n m d L → L ≤ suc (n + suc m) ^ d →
                  ruleBound n m d L ≤ 92 * Bᴿ n m ^ (3 * d + 3)
ruleBound-small n m d L L≤ = ℕ.≤-trans
  (ℕ.*-monoʳ-≤ 46 (Bnd-small {B = Bᴿ n m} {e = 3 + (d + d)} {L = L} {d = d}
    (s≤s z≤n)
    (ℕ.≤-trans L≤ (ℕ.^-monoˡ-≤ d
      (ℕ.≤-trans (ℕ.≤-reflexive (cong suc (ℕ.+-suc n m))) (ℕ.n≤1+n _))))))
  (ℕ.≤-reflexive (trans (sym (ℕ.*-assoc 46 2 (Bᴿ n m ^ (d + (3 + (d + d))))))
    (cong (λ z → 92 * Bᴿ n m ^ z) (exps d))))
  where
  exps : ∀ d → d + (3 + (d + d)) ≡ 3 * d + 3
  exps = solve 1 (λ d → d :+ (con 3 :+ (d :+ d)) := con 3 :* d :+ con 3) refl

-- So on a canonical representation (PathSum.Cost.Canon.Canonical: the
-- terms are the canonical form of their own sum) each rule costs at
-- most 92 (n + m + 3)^(3d+3), whatever the phase: a polynomial in
-- n + m for fixed d.

canonical-cost : (d : ℕ) (j : Fin (suc m)) (R : Rep n (suc m)) →
                 Canonical d (terms R) →
                 (cost (elimˢ d j R) ≤ 92 * Bᴿ n m ^ (3 * d + 3)) ×
                 (cost (ωˢ d j R) ≤ 92 * Bᴿ n m ^ (3 * d + 3)) ×
                 (cost (hhˢ d j R) ≤ 92 * Bᴿ n m ^ (3 * d + 3))
canonical-cost {m} {n} d j R can =
  ℕ.≤-trans (cost-elimˢ≤ d j R) small ,
  ℕ.≤-trans (cost-ωˢ≤ d j R) small ,
  ℕ.≤-trans (cost-hhˢ≤ d j R) small
  where
  L≤ : length (terms R) ≤ suc (n + suc m) ^ d
  L≤ = subst (λ ts → length ts ≤ suc (n + suc m) ^ d) (sym can)
             (canonical-length d ⟦ terms R ⟧ˢ)

  small : ruleBound n m d (length (terms R)) ≤ 92 * Bᴿ n m ^ (3 * d + 3)
  small = ruleBound-small n m d (length (terms R)) L≤
