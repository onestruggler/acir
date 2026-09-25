------------------------------------------------------------------------
-- Presentations of groups
--
-- Expanding a generator into basic ones does not raise the level
-- (§3.3): the ExpLevel hypothesis of Reduction.
--
-- The expansions of X and i are words of transpositions and i's on
-- indices ≤ b, the top index of the generator, so by mono-level every
-- state along them lies below any bound that the level of the source
-- and (b + 1 , 0 , 1) lie below.  The expansions of K are conjugates
-- P Y P by such words P with P P = 1, around a single K; the states
-- after the middle are then P applied to the target.  And (b + 1 , 0 ,
-- 1) lies below any bound that both ends of the edge lie below.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.Clifford+CS-TwoLevel.ExpLevel {n : ℕ} where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (recompute)

open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Scale using (sc ; sc-0 ; sc-injective)
open import Examples.Groups.Clifford+CS-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count-one)
open import Examples.Groups.Clifford+CS-TwoLevel.Norm using (lde0 ; Σℕ ; Nℕ)
open import Examples.Groups.Clifford+CS-TwoLevel.Column using (nodd ; unit-odd)
open import Examples.Groups.Clifford+CS-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Clifford+CS-TwoLevel.Pivot
  using (pivot ; pivot-just ; pivot-nothing ; pivot-char ; Beyond ; Lvl ; level ; level-just ; _<ₗ_ ; _<ₗ?_)
open import Examples.Groups.Clifford+CS-TwoLevel.Syllable
  using (top ; Beyond-actM ; eᶻ ; eᶻ-! ; δᶻ-refl ; δᶻ-≢ ; col𝕀≡)
open import Examples.Groups.Clifford+CS-TwoLevel.Step using (col-norm)
open import Examples.Groups.Clifford+CS-TwoLevel.Levels using (mono-level ; mono-e ; <ₗ-trans ; Bℓ)
open import Examples.Groups.Clifford+CS-TwoLevel.Basic {n}
  using (Letters≤ ; KShape ; single ; sandwich ; expand ; expand-≈ ; expand-letters-X ; expand-letters-i ; expand-shape-K)
open import Examples.Groups.Clifford+CS-TwoLevel.Reduction {n} using (BelowSrc ; ExpLevel ; sound-act)

------------------------------------------------------------------------
-- Along words of transpositions and i's

word-level : ∀ {b : Fin n} (w : Word (Gen n)) → Letters≤ b w → (M : Matrix n n D) {L : Lvl} →
             level M <ₗ L → Bℓ b <ₗ L → level (actMʷ w M) <ₗ L
word-level [ X-gen a c p ]ʷ h M lM lB = mono-level (X-gen a c p) tt h M lM lB
word-level [ i-gen c ]ʷ h M lM lB = mono-level (i-gen c) tt h M lM lB
word-level ε _ M lM lB = lM
word-level (u • v) (hu , hv) M lM lB = word-level u hu (actMʷ v M) (word-level v hv M lM lB) lB

word-below : ∀ {b : Fin n} (w : Word (Gen n)) → Letters≤ b w → (M : Matrix n n D) {L : Lvl} →
             level M <ₗ L → Bℓ b <ₗ L → BelowSrc L w M
word-below [ X-gen a c p ]ʷ _ M lM lB = lM
word-below [ i-gen c ]ʷ _ M lM lB = lM
word-below ε _ M lM lB = tt
word-below (u • v) (hu , hv) M lM lB =
  word-below v hv M lM lB , word-below u hu (actMʷ v M) (word-level v hv M lM lB) lB

-- A K expansion from M to r: the states after the middle are P r.
kshape-below : ∀ {b : Fin n} {w : Word (Gen n)} → KShape b w → (M : Matrix n n D) {L : Lvl} →
               level M <ₗ L → level (actMʷ w M) <ₗ L → Bℓ b <ₗ L → BelowSrc L w M
kshape-below (single h) M lM lr lB = lM
kshape-below {w = P • Y • P} (sandwich hP PP kY) M {L} lM lr lB =
  (word-below P hP M lM lB , kshape-below kY (actMʷ P M) lPM lYPM lB) ,
  word-below P hP (actMʷ Y (actMʷ P M)) lYPM lB
  where
  lPM : level (actMʷ P M) <ₗ L
  lPM = word-level P hP M lM lB
  lYPM : level (actMʷ Y (actMʷ P M)) <ₗ L
  lYPM = subst (_<ₗ L) (cong level (sound-act PP (actMʷ Y (actMʷ P M))))
           (word-level P hP (actMʷ P (actMʷ Y (actMʷ P M))) lr lB)

------------------------------------------------------------------------
-- The generators move the basis vector at their top index

private
  δ-a : (a : Fin n) → col 𝕀 a ! a ≡ DR.1#
  δ-a a = trans (ent-𝕀 a a) (δ-refl a)

  δ-≢′ : {a c : Fin n} → a ≢ c → col 𝕀 c ! a ≡ DR.0#
  δ-≢′ {a} {c} a≢c = trans (ent-𝕀 a c) (δ-≢ a≢c)

  0≢1 : DR.0# ≢ DR.1#
  0≢1 ()

  ⅈ≢1 : ⅈ DR.* DR.1# ≢ DR.1#
  ⅈ≢1 ()

  1≢0ᶻ : ZR.1# ≢ ZR.0#
  1≢0ᶻ ()

  e-≢ᶻ : {a x : Fin n} → x ≢ a → eᶻ a ! x ≡ ZR.0#
  e-≢ᶻ {a} {x} x≢a = trans (eᶻ-! a x) (δᶻ-≢ x≢a)

  e-aᶻ : (a : Fin n) → eᶻ a ! a ≡ ZR.1#
  e-aᶻ a = trans (eᶻ-! a a) (δᶻ-refl a)

top-moves : (g : Gen n) → actV g (col 𝕀 (top g)) ≢ col 𝕀 (top g)
top-moves (X-gen a b p) eq =
  0≢1 (trans (sym (δ-≢′ (<⇒≢ p))) (trans (sym (actV-Xb p (col 𝕀 b))) (trans (cong (_! b) eq) (δ-a b))))
top-moves (K-gen a b p) eq =
  1≢0ᶻ (sc-injective 1 (trans chain (sym (sc-0 1))))
  where
  w = Kᶻ a b (eᶻ b)
  w-a : w ! a ≡ ZR.1#
  w-a = trans (set₂-a a b (eᶻ b ! a ZR.+ eᶻ b ! b) (eᶻ b ! a ZR.- eᶻ b ! b) (Vec.map (γᶻ ZR.*_) (eᶻ b)))
              (trans (cong₂ ZR._+_ (e-≢ᶻ (<⇒≢ p)) (e-aᶻ b)) (ZR.+-identityˡ ZR.1#))
  col≡ : actV (K-gen a b p) (col 𝕀 b) ≡ scV 1 w
  col≡ = trans (cong (actV (K-gen a b p)) (col𝕀≡ b)) (actV-K a b p 0 (eᶻ b))
  chain : sc 1 ZR.1# ≡ DR.0#
  chain = trans (cong (sc 1) (sym w-a))
            (trans (sym (scV-! 1 w a))
              (trans (cong (_! a) (sym col≡))
                (trans (cong (_! a) eq) (δ-≢′ (<⇒≢ p)))))
top-moves (i-gen a) eq =
  ⅈ≢1 (trans (cong (ⅈ DR.*_) (sym (δ-a a))) (trans (sym (actV-ia a (col 𝕀 a))) (trans (cong (_! a) eq) (δ-a a))))

-- The level data of g e_top is at least (0 , 1).
top-data : (g : Gen n) {L : Lvl} →
           (suc (toℕ (top g)) , lde (actV g (col 𝕀 (top g))) , nodd (num (actV g (col 𝕀 (top g))))) <ₗ L →
           Bℓ (top g) <ₗ L
top-data (X-gen a b p) {L} lt =
  subst (_<ₗ L) (cong₂ (λ k m → suc (toℕ b) , k , m) (proj₁ (mono-e (X-gen a b p) tt b)) (proj₂ (mono-e (X-gen a b p) tt b))) lt
top-data (i-gen a) {L} lt =
  subst (_<ₗ L) (cong₂ (λ k m → suc (toℕ a) , k , m) (proj₁ (mono-e (i-gen a) tt a)) (proj₂ (mono-e (i-gen a) tt a))) lt
top-data (K-gen a b p) {L} lt =
  <ₗ-trans (inj₂ (refl , subst (λ k → (0 , 1) <₂ (k , nodd (num (actV (K-gen a b p) (col 𝕀 b))))) (sym k1)
                             (inj₁ (ℕ.s≤s ℕ.z≤n)))) lt
  where
  open import Examples.Groups.Clifford+CS-TwoLevel.Pivot using (_<₂_)
  w = Kᶻ a b (eᶻ b)
  w-a : w ! a ≡ ZR.1#
  w-a = trans (set₂-a a b (eᶻ b ! a ZR.+ eᶻ b ! b) (eᶻ b ! a ZR.- eᶻ b ! b) (Vec.map (γᶻ ZR.*_) (eᶻ b)))
              (trans (cong₂ ZR._+_ (e-≢ᶻ (<⇒≢ p)) (e-aᶻ b)) (ZR.+-identityˡ ZR.1#))
  k1 : lde (actV (K-gen a b p) (col 𝕀 b)) ≡ 1
  k1 = proj₁ (lde-char 1 w (trans (cong (actV (K-gen a b p)) (col𝕀≡ b)) (actV-K a b p 0 (eᶻ b)))
                              (inj₂ (a , cong oddᶻ w-a)))

------------------------------------------------------------------------
-- (top g + 1 , 0 , 1) lies below any bound both ends lie below

private
  -- A unit column of exponent 0 has one odd entry.
  nodd-unit : {M : Matrix n n D} → ColOrth M → ∀ p → lde (col M p) ≡ 0 → nodd (num (col M p)) ≡ 1
  nodd-unit {M} o p k0 =
    at (lde0 (num (col M p)) (subst (λ k → Σℕ (λ x → Nℕ (num (col M p) ! x)) ≡ 2 ℕ.^ k) k0 (col-norm o p)))
    where
    open import Data.Product.Base using (∃)
    at : (∃ λ m → _) → nodd (num (col M p)) ≡ 1
    at (m , (t , t<4 , um) , rest) =
      count-one (λ x → oddᶻ (num (col M p) ! x)) m (trans (cong oddᶻ um) (unit-odd t t<4))
                (λ x x≢m → cong oddᶻ (rest x x≢m))

private
  B-bound′ : (g : Gen n) (M : Matrix n n D) → ColOrth M → {L : Lvl} →
            level M <ₗ L → level (actM g M) <ₗ L → Bℓ (top g) <ₗ L
  B-bound′ g M o {L} lM lg = by (pivot M) refl
    where
    t = top g
    gM = actM g M

    -- M agrees with I from column t on: then gM has pivot t.
    low : col M t ≡ col 𝕀 t → Beyond t M → Bℓ t <ₗ L
    low et bt = top-data g (subst (_<ₗ L) (trans (level-just gM pv) (cong (λ v → suc (toℕ t) , lde v , nodd (num v)) col-t)) lg)
      where
      col-t : col gM t ≡ actV g (col 𝕀 t)
      col-t = trans (col-actM g M t) (cong (actV g) et)
      pv : pivot gM ≡ just t
      pv = pivot-char gM (λ eq → top-moves g (trans (sym col-t) eq)) (Beyond-actM g {M = M} ℕP.≤-refl bt)

    by : (r : Maybe (Fin n)) → pivot M ≡ r → Bℓ t <ₗ L
    by nothing em = low (cong (λ N → col N t) (pivot-nothing M em)) (λ c _ → cong (λ N → col N c) (pivot-nothing M em))
    by (just p) em = cmp (FinP.<-cmp t p)
      where
      lvl : level M ≡ (suc (toℕ p) , lde (col M p) , nodd (num (col M p)))
      lvl = level-just M em
      cmp : Tri (t < p) (t ≡ p) (p < t) → Bℓ t <ₗ L
      cmp (tri< t<p _ _) = <ₗ-trans (subst (Bℓ t <ₗ_) (sym lvl) (inj₁ (ℕ.s≤s t<p))) lM
      cmp (tri≈ _ refl _) = exp (lde (col M p)) refl
        where
        exp : (k : ℕ) → lde (col M p) ≡ k → Bℓ t <ₗ L
        exp zero k0 = subst (_<ₗ L) (trans lvl (cong₂ (λ k m → suc (toℕ p) , k , m) k0 (nodd-unit o p k0))) lM
        exp (suc k) ek = <ₗ-trans (subst (Bℓ t <ₗ_) (sym lvl)
                           (inj₂ (refl , subst (λ k′ → (0 , 1) <₂ (k′ , nodd (num (col M p)))) (sym ek) (inj₁ (ℕ.s≤s ℕ.z≤n))))) lM
          where open import Examples.Groups.Clifford+CS-TwoLevel.Pivot using (_<₂_)
      cmp (tri> _ _ p<t) =
        low (proj₂ (pivot-just M em) t p<t) (λ c t<c → proj₂ (pivot-just M em) c (ℕP.<-trans p<t t<c))

-- The same, from an irrelevant proof of column-orthonormality: the
-- conclusion is decidable, so it can be recomputed.
B-bound : (g : Gen n) (M : Matrix n n D) → .(ColOrth M) → {L : Lvl} →
          level M <ₗ L → level (actM g M) <ₗ L → Bℓ (top g) <ₗ L
B-bound g M o {L} lM lg = recompute (Bℓ (top g) <ₗ? L) (B-bound′ g M o lM lg)

------------------------------------------------------------------------
-- The hypothesis

exp-level : ExpLevel
exp-level (X-gen a b p) M o L lM lg =
  word-below (expand (X-gen a b p)) (expand-letters-X a b p) M lM (B-bound (X-gen a b p) M o lM lg)
exp-level (K-gen a b p) M o L lM lg =
  kshape-below (expand-shape-K a b p) M lM
    (subst (_<ₗ L) (cong level (sound-act (expand-≈ (K-gen a b p)) M)) lg)
    (B-bound (K-gen a b p) M o lM lg)
exp-level (i-gen a) M o L lM lg =
  word-below (expand (i-gen a)) (expand-letters-i a) M lM (B-bound (i-gen a) M o lM lg)
