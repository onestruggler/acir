------------------------------------------------------------------------
-- Presentations of groups
--
-- The sparse matchers are complete on canonical representations (for
-- Amy, QPL 2018, proposition 3.2)
--
-- Phase B of the plan in PathSum.Cost: matching and normalisation in
-- the cost model.  Its design, in three modules:
--
--  * Completeness (this module).  PathSum.Cost.Rules proves every
--    sparse rule sound: when it succeeds, the dense path-sum it stands
--    for steps.  Here is the converse for a canonical representation:
--    when the premises of a dense rule hold at y_j, for any
--    parameters c, S (and i), the sparse rule at y_j succeeds
--    (elimˢ-complete, ωˢ-complete, hhˢ-complete).  The parameters it
--    returns need not be the ones given.  In particular [HH]'s matcher
--    substitutes for the first path variable of the support of the
--    quotient; that is enough, because when some y_i of some S works
--    the support has a path variable, so the matcher succeeds.
--    Canonicity is used for one fact only: a canonical list has no
--    coefficient 0 modulo 2^M (represented-nonzero).  So the quotient
--    by y_j keeps a term exactly where the phase has a nonzero
--    coefficient.  Under [Elim]'s premise it is then empty
--    (quot-empty), and under [ω]'s and [HH]'s of degree at most 1
--    (quot-low), where the linear matcher is exact (linear-complete).
--    On a list that is not canonical the matchers can miss a rule that
--    applies: a repeated monomial whose coefficients cancel, or a term
--    with coefficient 0 that contains y_j.
--  * Search (PathSum.Cost.Search).  At y_j try [HH], then [ω] if the
--    normalisation allows it, then [Elim] -- the order of
--    PathSum.Anywhere.Match.head? -- and try y_0, y_1, ... until one
--    succeeds.  The search is sound (the dense path-sum steps by
--    _⟶ᵍ_), complete (when it finds nothing, every path-sum the
--    representation stands for is irreducible: no rule of
--    PathSum.Anywhere applies at any variable), and costs at most
--    m + 1 times three rules.
--  * Normalisation (PathSum.Cost.Normalise).  Canonicalise, then search
--    and step until nothing is found: at most m rounds, since each
--    step removes a path variable.  The result comes with a dense
--    chain to a path-sum it represents, which is irreducible.  After
--    the canonicalisation the loop costs at most 279 (n + m + 3)^(3d+5),
--    a polynomial in n + m for every fixed order bound d.  That is
--    proposition 3.2's time claim in this cost model
--    (proposition-3-2), for the rules PathSum.Anywhere formalises:
--    [Elim], [ω] and [HH] with Z₂-linear quotients.  Its header says
--    why [Case] and quotients that are not linear are left out.
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Complete (M : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _∨_; if_then_else_; T)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Fin.Subset.Properties using (x∈⁅x⁆)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_)
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Divisibility.Signed using (_∣_; ∣m∣n⇒∣m+n; ∣⇒∣ᵤ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (zero; suc; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Vec.Base using (Vec; lookup; insertAt; removeAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Cost
open import PathSum.Cost.Canon M using
  (canonical; nonzero; Canonical; canonical-nonzero; ∣-≡ᴹ)
open import PathSum.Cost.Coeff M using
  (Coeff; 0ᶠ; _==ᶠ_; isZero; isZero-false; _≡ᴹ_; modᴹ; ≡ᴹ-reflexive;
   ≡ᴹ-sym; ≡ᴹ-trans; coeff-residue; residue-≡ᴹ; residue-0)
open import PathSum.Cost.Linear M using
  (halfᶠ; zeroOrHalf; lowᶜ; Linearity; linearity; linear?; const; support;
   linearᶜ; bitᵛ; liftXor-var; half-sgn; half-big)
open import PathSum.Cost.Monomial using (value-degᵐᶜ)
open import PathSum.Cost.Rules M using
  (matchElimᶜ; stepElimᶜ; elimBranchᶜ; elimˢ; quarterᶠ; ωVerdict; matchωᶜ;
   stepωᶜ; ωCont; ωˢ; hhConst; hhVerdict; matchHHᶜ; stepHHᶜ; hhCont; hhˢ;
   quot-≈)
open import PathSum.Cost.Split M using
  (hasʸ; dropᵀ; quot; quotᶜ; value-quotᶜ; freeᶜ; formsFreeᶜ; readᶜ;
   value-readᶜ)
open import PathSum.Linear using (Lin; liftᴸ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Mon; Poly; Var; x[_]; y[_]; ⟪_⟫; 1ᵐ; ∥_∥; _≟ᵐ_; _∈ᵐ_; κ; 0ᴾ; _+ᴾ_; _·ᴾ_;
   _≈[_]_; NoVar; liftXor; sgn; negpow)
open import PathSum.Polynomial.Product using (≈-trans; ≈-sym)
open import PathSum.Polynomial.Properties using
  (∥1ᵐ∥≡0; ∥⟪v⟫∥≡1; liftXor-1ᵐ)
open import PathSum.Reduction M using (¼; ½)
open import PathSum.Reorder using (_/ʸ_)
open import PathSum.Size.Monomials using (monomials≤)
open import PathSum.Size.Sparse M using
  (Term; coeff; ⟦_⟧ˢ; residue; sparse; Rep; terms; forms; Represents)

import Data.Integer.Properties as ℤP
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllP
import Data.Nat.Properties as ℕ
import Data.Vec.Properties as Vec

open +-*-Solver using (solve; _:+_; _:-_; _:=_)

private
  variable
    d k n m : ℕ


------------------------------------------------------------------------
-- Small facts

private
  zipᴬ : ∀ {A : Set} {P Q : A → Set} {as : List A} →
         All P as → All Q as → All (λ a → P a × Q a) as
  zipᴬ []       []       = []
  zipᴬ (p ∷ ps) (q ∷ qs) = (p , q) ∷ zipᴬ ps qs

  not-true : ∀ b → not b ≡ true → b ≡ false
  not-true false _ = refl

  T-true : ∀ b → T b → b ≡ true
  T-true true _ = refl

  ≡ᵇ-refl : ∀ x → (x ≡ᵇ x) ≡ true
  ≡ᵇ-refl zero    = refl
  ≡ᵇ-refl (suc x) = ≡ᵇ-refl x

  true≢false : true ≡ false → ⊥
  true≢false ()

-- Comparing a coefficient with itself.

==ᶠ-refl : (r : Coeff) → (r ==ᶠ r) ≡ true
==ᶠ-refl r = ≡ᵇ-refl (toℕ r)

-- The constant polynomial at 1, and away from 1.

κ-one : (z : ℤ) → κ {n} {m} z 1ᵐ ≡ z
κ-one {n} {m} z with (1ᵐ {n} {m}) ≟ᵐ 1ᵐ
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

κ-off : (z : ℤ) (γ : Mon n m) → 1 ≤ ∥ γ ∥ → κ z γ ≡ 0ℤ
κ-off {n} {m} z γ 1≤ with γ ≟ᵐ 1ᵐ
... | yes refl = ⊥-elim (absurd (subst (1 ≤_) (∥1ᵐ∥≡0 {n} {m}) 1≤))
  where
  absurd : ¬ (1 ≤ 0)
  absurd ()
... | no  _    = refl

κ-zero : (γ : Mon n m) (z : ℤ) → κ 0ℤ γ +ℤ z ≡ z
κ-zero γ z = by (γ ≟ᵐ 1ᵐ)
  where
  by : ∀ t → (if ⌊ t ⌋ then 0ℤ else 0ℤ) +ℤ z ≡ z
  by (yes _) = ℤP.+-identityˡ z
  by (no  _) = ℤP.+-identityˡ z

-- ±1 is odd.

2∤±1 : (c : Bool) → ¬ ((+ 2) ∣ (sgn c *ℤ negpow 0))
2∤±1 true  h with ∣1⇒≡1 (∣⇒∣ᵤ h)
... | ()
2∤±1 false h with ∣1⇒≡1 (∣⇒∣ᵤ h)
... | ()


------------------------------------------------------------------------
-- A canonical list has no coefficient 0 modulo 2^M

-- Every term of the canonical form carries its polynomial's
-- coefficient at its monomial, as a residue, and that coefficient is
-- not 0 modulo 2^M.

canonical-coeffs : (d : ℕ) (P : Poly n m) →
                   All (λ t → proj₂ t ≡ residue (P (proj₁ t))) (canonical d P)
canonical-coeffs {n} {m} d P = keep-All nonzero (sparse d P)
  (AllP.map⁺ {f = λ δ → δ , residue (P δ)}
    (All.universal (λ δ → refl) (monomials≤ n m d)))

private
  nonzero-at : (P : Poly n m) (t : Term n m) →
               proj₂ t ≡ residue (P (proj₁ t)) → nonzero t ≡ true →
               ¬ (pow M ∣ P (proj₁ t))
  nonzero-at P (δ , a) a≡ nz div = isZero-false a (not-true (isZero a) nz)
    (subst (λ r → pow M ∣ coeff r) (sym a≡)
      (∣-≡ᴹ ℕ.≤-refl div (≡ᴹ-sym (coeff-residue (P δ)))))

canonical-nonzero-at : (d : ℕ) (P : Poly n m) →
                       All (λ t → ¬ (pow M ∣ P (proj₁ t))) (canonical d P)
canonical-nonzero-at d P =
  All.map (λ {t} h → nonzero-at P t (proj₁ h) (proj₂ h))
          (zipᴬ (canonical-coeffs d P) (canonical-nonzero d P))

-- So a canonical list has no coefficient 0 modulo 2^M in its own sum,
-- nor in the phase of a path-sum it represents.

Canonical-nonzero : {ts : List (Term n m)} → Canonical d ts →
                    All (λ t → ¬ (pow M ∣ ⟦ ts ⟧ˢ (proj₁ t))) ts
Canonical-nonzero {d = d} {ts = ts} can =
  subst (All (λ t → ¬ (pow M ∣ ⟦ ts ⟧ˢ (proj₁ t)))) (sym can)
        (canonical-nonzero-at d ⟦ ts ⟧ˢ)

represented-nonzero : (ξ : PathSum n k m) (R : Rep n m) → Represents ξ R →
                      Canonical d (terms R) →
                      All (λ t → ¬ (pow M ∣ phase ξ (proj₁ t))) (terms R)
represented-nonzero ξ R (eqP , _) can =
  All.map (λ {t} ¬div div → ¬div (∣-≡ᴹ ℕ.≤-refl div (modᴹ (eqP (proj₁ t)))))
          (Canonical-nonzero can)


------------------------------------------------------------------------
-- The quotient of a canonical representation

-- A monomial containing y_j carries the coefficient of its quotient at
-- the monomial with y_j removed.

/ʸ-at : (P : Poly n (suc m)) (j : Fin (suc m)) (α : Subset n)
        (β : Subset (suc m)) → lookup β j ≡ true →
        (P /ʸ j) (α , removeAt β j) ≡ P (α , β)
/ʸ-at P j α β eq = cong (λ β′ → P (α , β′))
  (trans (cong (insertAt (removeAt β j) j) (sym eq))
         (Vec.insertAt-removeAt β j))

-- Under [Elim]'s premise no term contains y_j: the quotient is empty.

quot-empty : (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
             Represents ξ R → Canonical d (terms R) → (j : Fin (suc m)) →
             (phase ξ /ʸ j) ≈[ pow M ] 0ᴾ → quot j (terms R) ≡ []
quot-empty {n = n} {m = m} ξ R rp can j eq =
  cong (map (dropᵀ j))
       (keep-none (hasʸ j) (terms R)
                  (lacks (terms R) (represented-nonzero ξ R rp can)))
  where
  zero-at : ∀ γ → pow M ∣ (phase ξ /ʸ j) γ
  zero-at γ = subst (pow M ∣_) (ℤP.+-identityʳ ((phase ξ /ʸ j) γ)) (eq γ)

  lacks : (ts : List (Term n (suc m))) →
          All (λ t → ¬ (pow M ∣ phase ξ (proj₁ t))) ts →
          All (λ t → hasʸ j t ≡ false) ts
  lacks []                   []       = []
  lacks (((α , β) , a) ∷ ts) (h ∷ hs) = by (lookup β j) refl ∷ lacks ts hs
    where
    by : ∀ b → lookup β j ≡ b → b ≡ false
    by false _ = refl
    by true  e = ⊥-elim (h (subst (pow M ∣_) (/ʸ-at (phase ξ) j α β e)
                                  (zero-at (α , removeAt β j))))

-- Under [ω]'s and [HH]'s premise, κ base + ½·liftXor c S, the quotient
-- vanishes modulo 1 above degree 1, so its terms have degree at most 1.

quot-low : (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
           Represents ξ R → Canonical d (terms R) → (j : Fin (suc m))
           (base : ℤ) (c : Bool) (S : Mon n m) →
           (phase ξ /ʸ j) ≈[ pow M ] (κ base +ᴾ (½ ·ᴾ liftXor c S)) →
           All (λ t → ∥ proj₁ t ∥ ≤ 1) (quot j (terms R))
quot-low {n = n} {m = m} ξ R rp can j base c S eq =
  AllP.map⁺ {f = dropᵀ j}
    (All.map (λ {t} h → proj₁ h (proj₂ h))
      (zipᴬ (keep-All (hasʸ j) (terms R)
                      (per (terms R) (represented-nonzero ξ R rp can)))
            (keep-true (hasʸ j) (terms R))))
  where
  shape : ∀ h x → (h -ℤ x) +ℤ x ≡ h
  shape = solve 2 (λ h x → (h :- x) :+ x := h) refl

  big-zero : (γ : Mon n m) → 2 ≤ ∥ γ ∥ → pow M ∣ (phase ξ /ʸ j) γ
  big-zero γ 2≤ = subst (pow M ∣_) (shape _ _) (∣m∣n⇒∣m+n (eq γ) rhs)
    where
    rhs : pow M ∣ (κ base γ +ℤ ½ *ℤ liftXor c S γ)
    rhs = subst (pow M ∣_)
      (sym (trans (cong (_+ℤ ½ *ℤ liftXor c S γ)
                        (κ-off base γ (ℕ.≤-trans (s≤s z≤n) 2≤)))
                  (ℤP.+-identityˡ (½ *ℤ liftXor c S γ))))
      (half-big c S γ 2≤)

  one : (t : Term n (suc m)) → ¬ (pow M ∣ phase ξ (proj₁ t)) →
        hasʸ j t ≡ true → ∥ proj₁ (dropᵀ j t) ∥ ≤ 1
  one ((α , β) , a) ¬div e with ∥ (α , removeAt β j) ∥ ℕ.≤? 1
  ... | yes le = le
  ... | no  gt = ⊥-elim (¬div (subst (pow M ∣_) (/ʸ-at (phase ξ) j α β e)
                                     (big-zero (α , removeAt β j)
                                               (ℕ.≰⇒> gt))))

  per : (ts : List (Term n (suc m))) →
        All (λ t → ¬ (pow M ∣ phase ξ (proj₁ t))) ts →
        All (λ t → hasʸ j t ≡ true → ∥ proj₁ (dropᵀ j t) ∥ ≤ 1) ts
  per []       []       = []
  per (t ∷ ts) (h ∷ hs) = one t h ∷ per ts hs

-- The quotient read off the representation stands for what the phase's
-- quotient is congruent to.

quot-target : (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
              Represents ξ R → (j : Fin (suc m)) {T : Poly n m} →
              (phase ξ /ʸ j) ≈[ pow M ] T →
              ⟦ value (quotᶜ j (terms R)) ⟧ˢ ≈[ pow M ] T
quot-target ξ R rp j {T} eq =
  subst (λ us → ⟦ us ⟧ˢ ≈[ pow M ] T) (sym (value-quotᶜ j (terms R)))
    (≈-trans {P = ⟦ quot j (terms R) ⟧ˢ} {Q = phase ξ /ʸ j} {R = T}
      (≈-sym {P = phase ξ /ʸ j} {Q = ⟦ quot j (terms R) ⟧ˢ} (quot-≈ ξ R rp j))
      eq)


------------------------------------------------------------------------
-- The outputs

-- A form containing y_j lifts to a polynomial whose coefficient at y_j
-- is ±1, so if y_j is absent from the lifting modulo 2 it is absent
-- from the form.

freeᶜ-complete : (j : Fin (suc m)) (l : Lin n (suc m)) →
                 NoVar (+ 2) y[ j ] (liftᴸ l) → value (freeᶜ j l) ≡ true
freeᶜ-complete j (c , (α , β)) nv =
  cong not (trans (value-lookupᶜ β j) (off (lookup β j) refl))
  where
  off : ∀ b → lookup β j ≡ b → b ≡ false
  off false _ = refl
  off true  e = ⊥-elim (2∤±1 c (subst ((+ 2) ∣_) at
                                      (nv ⟪ y[ j ] ⟫ (x∈⁅x⁆ j))))
    where
    at : liftᴸ (c , (α , β)) ⟪ y[ j ] ⟫ ≡ sgn c *ℤ negpow 0
    at = trans (liftXor-var c (α , β) y[ j ])
               (cong (λ b → if b then sgn c *ℤ negpow 0 else 0ℤ) e)

formsFree-complete : (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
                     Represents ξ R → (j : Fin (suc m)) →
                     (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
                     value (formsFreeᶜ j (forms R)) ≡ true
formsFree-complete ξ R (_ , eqf) j nv =
  allFinᶜ-complete (λ w → freeᶜ j (forms R w))
    (λ w → freeᶜ-complete j (forms R w)
             (λ γ j∈γ → subst ((+ 2) ∣_) (eqf w γ) (nv w γ j∈γ)))


------------------------------------------------------------------------
-- The linear matcher is exact

-- Congruent to κ base + ½·liftXor c S, a list has the residue
-- base + ½c at 1, and ½ or 0 at a variable, as it is in S or not.

residue-one : (q : List (Term n m)) (base : ℤ) (c : Bool) (S : Mon n m) →
              ⟦ q ⟧ˢ ≈[ pow M ] (κ base +ᴾ (½ ·ᴾ liftXor c S)) →
              residue (⟦ q ⟧ˢ 1ᵐ) ≡ residue (base +ℤ ½ *ℤ [ c ]ᶻ)
residue-one {n} {m} q base c S eq =
  residue-≡ᴹ {a = ⟦ q ⟧ˢ 1ᵐ} (≡ᴹ-trans (modᴹ (eq 1ᵐ))
  (≡ᴹ-reflexive (cong₂ _+ℤ_ (κ-one {n} {m} base)
                            (cong (½ *ℤ_) (liftXor-1ᵐ c S)))))

residue-var : (q : List (Term n m)) (base : ℤ) (c : Bool) (S : Mon n m) →
              ⟦ q ⟧ˢ ≈[ pow M ] (κ base +ᴾ (½ ·ᴾ liftXor c S)) →
              (v : Var n m) →
              residue (⟦ q ⟧ˢ ⟪ v ⟫) ≡ (if bitᵛ S v then halfᶠ else 0ᶠ)
residue-var q base c S eq v = by (bitᵛ S v) refl
  where
  L : Bool → ℤ
  L b = 0ℤ +ℤ ½ *ℤ (if b then sgn c *ℤ negpow 0 else 0ℤ)

  at : ⟦ q ⟧ˢ ⟪ v ⟫ ≡ᴹ L (bitᵛ S v)
  at = ≡ᴹ-trans (modᴹ (eq ⟪ v ⟫)) (≡ᴹ-reflexive (cong₂ _+ℤ_
    (κ-off base ⟪ v ⟫ (ℕ.≤-reflexive (sym (∥⟪v⟫∥≡1 v))))
    (cong (½ *ℤ_) (liftXor-var c S v))))

  by : ∀ b → bitᵛ S v ≡ b →
       residue (⟦ q ⟧ˢ ⟪ v ⟫) ≡ (if b then halfᶠ else 0ᶠ)
  by true  e = residue-≡ᴹ (≡ᴹ-trans at (≡ᴹ-trans
    (≡ᴹ-reflexive (trans (cong L e)
                         (ℤP.+-identityˡ (½ *ℤ (sgn c *ℤ negpow 0)))))
    (≡ᴹ-sym (half-sgn c))))
  by false e = trans (residue-≡ᴹ (≡ᴹ-trans at (≡ᴹ-reflexive (trans (cong L e)
    (trans (ℤP.+-identityˡ (½ *ℤ 0ℤ)) (ℤP.*-zeroʳ ½))))))
    residue-0

-- 0 and ½ both pass the test for a linear coefficient.

private
  zoh : ∀ b → zeroOrHalf (if b then halfᶠ else 0ᶠ) ≡ true
  zoh true  = trans (cong ((halfᶠ ==ᶠ 0ᶠ) ∨_) (==ᶠ-refl halfᶠ))
                    (∨-zeroʳ (halfᶠ ==ᶠ 0ᶠ))
  zoh false = cong (_∨ (0ᶠ ==ᶠ halfᶠ)) (==ᶠ-refl 0ᶠ)

  ≤ᵇ-yes : ∀ {x y} → x ≤ y → (x ≤ᵇ y) ≡ true
  ≤ᵇ-yes {x} {y} le = T-true (x ≤ᵇ y) (ℕ.≤⇒≤ᵇ le)

-- So on a list of terms of degree at most 1 congruent to
-- κ base + ½·liftXor c S the matcher passes, reads the constant
-- base + ½c, and puts every variable of S in its support.

linear-complete : (q : List (Term n m)) → All (λ t → ∥ proj₁ t ∥ ≤ 1) q →
                  (base : ℤ) (c : Bool) (S : Mon n m) →
                  ⟦ q ⟧ˢ ≈[ pow M ] (κ base +ᴾ (½ ·ᴾ liftXor c S)) →
                  (linear? (value (linearᶜ q)) ≡ true) ×
                  (const (value (linearᶜ q)) ≡ residue (base +ℤ ½ *ℤ [ c ]ᶻ)) ×
                  (∀ v → bitᵛ S v ≡ true →
                         bitᵛ (support (value (linearᶜ q))) v ≡ true)
linear-complete {n} {m} q small base c S eq =
  cong₂ _∧_ low≡ (cong₂ _∧_ okx≡ oky≡) , const≡ , bits
  where
  r  = value (readᶜ q)
  xs = proj₁ (proj₂ r)
  ys = proj₂ (proj₂ r)

  xs-at : ∀ i → lookup xs i ≡ residue (⟦ q ⟧ˢ ⟪ x[ i ] ⟫)
  xs-at i = trans (cong (λ v → lookup (proj₁ (proj₂ v)) i) (value-readᶜ q))
                  (Vec.lookup∘tabulate _ i)

  ys-at : ∀ l → lookup ys l ≡ residue (⟦ q ⟧ˢ ⟪ y[ l ] ⟫)
  ys-at l = trans (cong (λ v → lookup (proj₂ (proj₂ v)) l) (value-readᶜ q))
                  (Vec.lookup∘tabulate _ l)

  -- Every term has degree at most 1.
  low≡ : value (allᶜ lowᶜ q) ≡ true
  low≡ = trans (value-allᶜ lowᶜ q)
               (all-true⁻ (λ t → value (lowᶜ t)) q (go q small))
    where
    go : (ts : List (Term n m)) → All (λ t → ∥ proj₁ t ∥ ≤ 1) ts →
         All (λ t → value (lowᶜ t) ≡ true) ts
    go []             []       = []
    go ((γ , a) ∷ ts) (h ∷ hs) =
      trans (cong (_≤ᵇ 1) (value-degᵐᶜ γ)) (≤ᵇ-yes h) ∷ go ts hs

  -- Every linear coefficient is 0 or ½.
  okx≡ : value (allVᶜ (λ b → step (zeroOrHalf b)) xs) ≡ true
  okx≡ = allVᶜ-complete (λ b → step (zeroOrHalf b)) xs (λ i →
    trans (cong zeroOrHalf (trans (xs-at i)
                                  (residue-var q base c S eq x[ i ])))
          (zoh (bitᵛ S x[ i ])))

  oky≡ : value (allVᶜ (λ b → step (zeroOrHalf b)) ys) ≡ true
  oky≡ = allVᶜ-complete (λ b → step (zeroOrHalf b)) ys (λ l →
    trans (cong zeroOrHalf (trans (ys-at l)
                                  (residue-var q base c S eq y[ l ])))
          (zoh (bitᵛ S y[ l ])))

  const≡ : const (value (linearᶜ q)) ≡ residue (base +ℤ ½ *ℤ [ c ]ᶻ)
  const≡ = trans (cong proj₁ (value-readᶜ q)) (residue-one q base c S eq)

  -- A variable of S has coefficient ½, so its bit is set.
  sx-at : ∀ i → lookup (proj₁ (support (value (linearᶜ q)))) i ≡
                (lookup xs i ==ᶠ halfᶠ)
  sx-at i = trans (cong (λ v → lookup v i)
                        (value-mapVᶜ (λ b → step (b ==ᶠ halfᶠ)) xs))
                  (Vec.lookup-map i (λ b → b ==ᶠ halfᶠ) xs)

  sy-at : ∀ l → lookup (proj₂ (support (value (linearᶜ q)))) l ≡
                (lookup ys l ==ᶠ halfᶠ)
  sy-at l = trans (cong (λ v → lookup v l)
                        (value-mapVᶜ (λ b → step (b ==ᶠ halfᶠ)) ys))
                  (Vec.lookup-map l (λ b → b ==ᶠ halfᶠ) ys)

  bits : ∀ v → bitᵛ S v ≡ true →
         bitᵛ (support (value (linearᶜ q))) v ≡ true
  bits x[ i ] e = trans (sx-at i) (trans (cong (_==ᶠ halfᶠ)
    (trans (xs-at i) (trans (residue-var q base c S eq x[ i ])
                            (cong (λ b → if b then halfᶠ else 0ᶠ) e))))
    (==ᶠ-refl halfᶠ))
  bits y[ l ] e = trans (sy-at l) (trans (cong (_==ᶠ halfᶠ)
    (trans (ys-at l) (trans (residue-var q base c S eq y[ l ])
                            (cong (λ b → if b then halfᶠ else 0ᶠ) e))))
    (==ᶠ-refl halfᶠ))


------------------------------------------------------------------------
-- The verdicts

private
  -- The two constants a rule compares with: the one that is taken.
  ifs : ∀ {A : Set} (c e₀ e₁ : Bool) (a₀ a₁ : A) →
        (if c then e₁ else e₀) ≡ true →
        ∃ λ v → (if e₀ then just a₀ else (if e₁ then just a₁ else nothing))
                ≡ just v
  ifs false true  e₁    a₀ a₁ _  = a₀ , refl
  ifs false false e₁    a₀ a₁ ()
  ifs true  true  e₁    a₀ a₁ _  = a₀ , refl
  ifs true  false true  a₀ a₁ _  = a₁ , refl
  ifs true  false false a₀ a₁ ()

  sel : (x : Bool → Coeff) (c : Bool) →
        (if c then (x c ==ᶠ x true) else (x c ==ᶠ x false)) ≡ true
  sel x true  = ==ᶠ-refl (x true)
  sel x false = ==ᶠ-refl (x false)

-- [ω]: the constant is ¼ + ½c for some c.

ωVerdict-complete : (lin : Linearity n m) (c : Bool) →
                    linear? lin ≡ true → const lin ≡ quarterᶠ c →
                    ∃ λ v → ωVerdict true lin (const lin ==ᶠ quarterᶠ false)
                                              (const lin ==ᶠ quarterᶠ true)
                            ≡ just v
ωVerdict-complete (linearity true  a s) c refl refl =
  ifs c _ _ (false , s) (true , s) (sel quarterᶠ c)
ωVerdict-complete (linearity false a s) c ()   _

-- [HH]: the constant is ½c, and the support has a path variable.

hhVerdict-complete : (lin : Linearity n m) (c : Bool) (mi : Maybe (Fin m)) →
                     linear? lin ≡ true → const lin ≡ hhConst c →
                     (∃ λ i → mi ≡ just i) →
                     ∃ λ v → hhVerdict true lin (const lin ==ᶠ 0ᶠ)
                                                (const lin ==ᶠ halfᶠ) mi
                             ≡ just v
hhVerdict-complete (linearity true  a s) c mi refl refl (i , refl) =
  ifs c _ _ (i , false , s) (i , true , s) (sel hhConst c)
hhVerdict-complete (linearity false a s) c mi ()   _    _

-- ½c as the residue the matcher reads.

hhConst-residue : (c : Bool) → residue (0ℤ +ℤ ½ *ℤ [ c ]ᶻ) ≡ hhConst c
hhConst-residue true  =
  cong residue (trans (ℤP.+-identityˡ (½ *ℤ 1ℤ)) (ℤP.*-identityʳ ½))
hhConst-residue false = trans
  (cong residue (trans (ℤP.+-identityˡ (½ *ℤ 0ℤ)) (ℤP.*-zeroʳ ½)))
  residue-0


------------------------------------------------------------------------
-- Completeness of the rules

-- [Elim]: y_j absent from the outputs and from the phase.

matchElim-complete : (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
                     Represents ξ R → Canonical d (terms R) →
                     (j : Fin (suc m)) → (phase ξ /ʸ j) ≈[ pow M ] 0ᴾ →
                     (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
                     value (matchElimᶜ j R) ≡ true
matchElim-complete ξ R rp can j eq nv =
  cong₂ _∧_ (formsFree-complete ξ R rp j nv)
    (cong (λ q → value (nullᶜ q))
          (trans (value-quotᶜ j (terms R)) (quot-empty ξ R rp can j eq)))

elimˢ-complete : (d : ℕ) (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
                 Represents ξ R → Canonical d (terms R) →
                 (j : Fin (suc m)) → (phase ξ /ʸ j) ≈[ pow M ] 0ᴾ →
                 (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
                 ∃ λ R′ → value (elimˢ d j R) ≡ just R′
elimˢ-complete d ξ R rp can j eq nv =
  value (stepElimᶜ d j R) ,
  cong (λ b → value (elimBranchᶜ d j R b))
       (matchElim-complete ξ R rp can j eq nv)

-- [ω]: the quotient is ¼ + ½(c ⊕ ⨁S) for some c and S.

matchω-complete : (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
                  Represents ξ R → Canonical d (terms R) →
                  (j : Fin (suc m)) (c : Bool) (S : Mon n m) →
                  (phase ξ /ʸ j) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c S)) →
                  (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
                  ∃ λ v → value (matchωᶜ j R) ≡ just v
matchω-complete ξ R rp can j c S eq nv =
  subst (λ free → ∃ λ v → ωVerdict free lin (const lin ==ᶠ quarterᶠ false)
                                            (const lin ==ᶠ quarterᶠ true)
                          ≡ just v)
        (sym (formsFree-complete ξ R rp j nv))
        (ωVerdict-complete lin c (proj₁ lc) (proj₁ (proj₂ lc)))
  where
  q   = value (quotᶜ j (terms R))
  lin = value (linearᶜ q)

  small : All (λ t → ∥ proj₁ t ∥ ≤ 1) q
  small = subst (All (λ t → ∥ proj₁ t ∥ ≤ 1)) (sym (value-quotᶜ j (terms R)))
                (quot-low ξ R rp can j ¼ c S eq)

  lc = linear-complete q small ¼ c S (quot-target ξ R rp j eq)

ωˢ-complete : (d : ℕ) (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
              Represents ξ R → Canonical d (terms R) →
              (j : Fin (suc m)) (c : Bool) (S : Mon n m) →
              (phase ξ /ʸ j) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c S)) →
              (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
              ∃ λ v → value (ωˢ d j R) ≡ just v
ωˢ-complete d ξ R rp can j c S eq nv =
  cont (proj₁ mc) (proj₂ mc)
  where
  mc = matchω-complete ξ R rp can j c S eq nv

  cont : ∀ v → value (matchωᶜ j R) ≡ just v →
         ∃ λ w → value (ωˢ d j R) ≡ just w
  cont (c′ , S′) e = (c′ , S′ , value (stepωᶜ d j c′ S′ R)) ,
                     cong (λ mv → value (ωCont d j R mv)) e

-- [HH]: the quotient is ½(c ⊕ ⨁S) for some c and some S containing a
-- path variable y_i.  The matcher may pick another variable of S, but
-- it always finds one.

matchHH-complete : (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
                   Represents ξ R → Canonical d (terms R) →
                   (j : Fin (suc m)) (i : Fin m) (c : Bool) (S : Mon n m) →
                   y[ i ] ∈ᵐ S →
                   (phase ξ /ʸ j) ≈[ pow M ] (½ ·ᴾ liftXor c S) →
                   (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
                   ∃ λ v → value (matchHHᶜ j R) ≡ just v
matchHH-complete ξ R rp can j i c S i∈S eq nv =
  subst (λ free → ∃ λ v → hhVerdict free lin (const lin ==ᶠ 0ᶠ)
                                             (const lin ==ᶠ halfᶠ) mi ≡ just v)
        (sym (formsFree-complete ξ R rp j nv))
        (hhVerdict-complete lin c mi (proj₁ lc)
          (trans (proj₁ (proj₂ lc)) (hhConst-residue c)) some)
  where
  q   = value (quotᶜ j (terms R))
  lin = value (linearᶜ q)
  mi  = value (firstᶜ (proj₂ (support lin)))

  eq′ : (phase ξ /ʸ j) ≈[ pow M ] (κ 0ℤ +ᴾ (½ ·ᴾ liftXor c S))
  eq′ γ = subst (λ z → pow M ∣ ((phase ξ /ʸ j) γ -ℤ z))
                (sym (κ-zero γ (½ *ℤ liftXor c S γ))) (eq γ)

  small : All (λ t → ∥ proj₁ t ∥ ≤ 1) q
  small = subst (All (λ t → ∥ proj₁ t ∥ ≤ 1)) (sym (value-quotᶜ j (terms R)))
                (quot-low ξ R rp can j 0ℤ c S eq′)

  lc = linear-complete q small 0ℤ c S (quot-target ξ R rp j eq′)

  bit : lookup (proj₂ (support lin)) i ≡ true
  bit = proj₂ (proj₂ lc) y[ i ] (Vec.[]=⇒lookup i∈S)

  some : ∃ λ i′ → mi ≡ just i′
  some = by mi refl
    where
    by : ∀ r → mi ≡ r → ∃ λ i′ → mi ≡ just i′
    by (just i′) e = i′ , e
    by nothing   e = ⊥-elim (true≢false (trans (sym bit)
                      (firstᶜ-nothing (proj₂ (support lin)) e i)))

hhˢ-complete : (d : ℕ) (ξ : PathSum n k (suc m)) (R : Rep n (suc m)) →
               Represents ξ R → Canonical d (terms R) →
               (j : Fin (suc m)) (i : Fin m) (c : Bool) (S : Mon n m) →
               y[ i ] ∈ᵐ S →
               (phase ξ /ʸ j) ≈[ pow M ] (½ ·ᴾ liftXor c S) →
               (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
               ∃ λ v → value (hhˢ d j R) ≡ just v
hhˢ-complete d ξ R rp can j i c S i∈S eq nv =
  cont (proj₁ mc) (proj₂ mc)
  where
  mc = matchHH-complete ξ R rp can j i c S i∈S eq nv

  cont : ∀ v → value (matchHHᶜ j R) ≡ just v →
         ∃ λ w → value (hhˢ d j R) ≡ just w
  cont (i′ , c′ , S′) e = (i′ , c′ , S′ , value (stepHHᶜ d j i′ c′ S′ R)) ,
                          cong (λ mv → value (hhCont d j R mv)) e
