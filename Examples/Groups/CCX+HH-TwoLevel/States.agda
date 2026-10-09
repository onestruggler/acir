------------------------------------------------------------------------
-- Presentations of groups
--
-- Facts about states that the edges at a level use: generators are
-- injective on vectors, the normal syllable is a path, the syllable
-- and the level of a state from a representation of its pivot column,
-- pivots kept by generators below them, and the levels of states
-- reached by words of X's and (-1)'s (they keep a state below L when the
-- basis vector levels they can create are below L).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; suc ; s≤s ; z≤n)

module Examples.Groups.CCX+HH-TwoLevel.States {n : ℕ} where

open import Data.Bool.Base using (false)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
open import Data.Integer.Base using (ℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D ; oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Lde
  using (scV ; lde ; num ; lde-char ; lde-≤ ; Minimal ; Odd ; Even ; ¬Even⇒Odd ; halveV ; scV-halve ; all-even?)
open import Examples.Groups.CCX+HH-TwoLevel.Column using (sylData ; nodd)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
open import Examples.Groups.CCX+HH-TwoLevel.Soundness using (sound-axiom)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot
  using (pivot ; pivot-just ; pivot-char ; Beyond ; Lvl ; lvlAt ; level ; level-just ; _<ₗ_ ; _<₂_ ; _<ₗ?_)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable
  using (syl ; syl-just ; step ; top ; Within ; Beyond-actM ; actV-e-beyond ; eᶻ ; col𝕀≡)
open import Examples.Groups.CCX+HH-TwoLevel.Step using (step-lt)
open import Examples.Groups.CCX+HH-TwoLevel.Synthesis using (synth-step)
open import Examples.Groups.CCX+HH-TwoLevel.Derived {n} using (_⁻¹ ; inverseˡ)
open import Examples.Groups.CCX+HH-TwoLevel.Levels using (Mono ; mono-level ; Bℓ ; <ₗ-trans)
open import Examples.Groups.CCX+HH-TwoLevel.Reduction {n} using (Path ; Low ; nw ; sound-act)

open PB (_===_ {n}) using (_≈_)
open PB (_===_ {n}) using (refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

------------------------------------------------------------------------
-- Soundness on vectors, and the generators are injective

sound-vec : {w v : Word (Gen n)} → w ≈ v → (u : Vec D n) → actVʷ w u ≡ actVʷ v u
sound-vec refl u = ≡.refl
sound-vec (sym h) u = ≡.sym (sound-vec h u)
sound-vec (trans h k) u = ≡.trans (sound-vec h u) (sound-vec k u)
sound-vec (cong {w} {w′} {v} {v′} h k) u =
  ≡.trans (≡.cong (actVʷ w) (sound-vec k u)) (sound-vec h (actVʷ v′ u))
sound-vec assoc u = ≡.refl
sound-vec left-unit u = ≡.refl
sound-vec right-unit u = ≡.refl
sound-vec (axiom {w} {v} a) u = same-action w v (sound-axiom a) u

act-inj : (g : Gen n) {u v : Vec D n} → actV g u ≡ actV g v → u ≡ v
act-inj g {u} {v} eq =
  ≡.trans (≡.sym (sound-vec (inverseˡ {[ g ]ʷ}) u))
    (≡.trans (≡.cong (actVʷ ([ g ]ʷ ⁻¹)) eq) (sound-vec (inverseˡ {[ g ]ʷ}) v))

-- A generator below the pivot keeps it.
pivot-keep : (g : Gen n) {p : Fin n} (M : Matrix n n D) → top g < p → pivot M ≡ just p →
             pivot (actM g M) ≡ just p
pivot-keep g {p} M tg pv = pivot-char (actM g M) ne (Beyond-actM g {M = M} (ℕP.<⇒≤ tg) (proj₂ (pivot-just M pv)))
  where
  ne : col (actM g M) p ≢ col 𝕀 p
  ne eq = proj₁ (pivot-just M pv)
    (act-inj g (≡.trans (≡.sym (col-actM g M p)) (≡.trans eq (≡.sym (actV-e-beyond g FinP.≤-refl tg)))))

-- A generator acting on indices ≤ p keeps the pivot p if the pivot
-- column stays off I.
pivot-stay : (g : Gen n) {p : Fin n} (M : Matrix n n D) → top g ≤ p → pivot M ≡ just p →
             col (actM g M) p ≢ col 𝕀 p → pivot (actM g M) ≡ just p
pivot-stay g M tg pv ne = pivot-char (actM g M) ne (Beyond-actM g {M = M} tg (proj₂ (pivot-just M pv)))

------------------------------------------------------------------------
-- Normal edges

-- The level drops along a normal edge (from an irrelevant proof of
-- orthogonality: the conclusion is decidable).
lt-step : (s : Matrix n n D) → .(ColOrth s) → ∀ {p} → pivot s ≡ just p → level (step s) <ₗ level s
lt-step s o pv = recompute (level (step s) <ₗ? level s) (step-lt o pv)

-- One normal edge is a path.
path-normal : (M : Matrix n n D) .(o : ColOrth M) {p : Fin n} → pivot M ≡ just p → Path (syl M) M o
path-normal M o pv = refl′ (≡.sym (synth-step M o pv))

------------------------------------------------------------------------
-- The syllable and the level, from a representation of the pivot
-- column

syl-of : (M : Matrix n n D) {p : Fin n} → pivot M ≡ just p → (K : ℕ) (W : Vec ℤ n) →
         col M p ≡ scV K W → Minimal K W → syl M ≡ sylData p K W
syl-of M {p} pv K W eq min =
  ≡.trans (syl-just M pv) (≡.cong₂ (sylData p) (proj₁ (lde-char K W eq min)) (proj₂ (lde-char K W eq min)))

level-of : (M : Matrix n n D) {p : Fin n} → pivot M ≡ just p → (K : ℕ) (W : Vec ℤ n) →
           col M p ≡ scV K W → Minimal K W → level M ≡ (suc (toℕ p) , K , nodd W)
level-of M {p} pv K W eq min =
  ≡.trans (level-just M pv)
    (≡.cong₂ (λ k w → suc (toℕ p) , k , nodd w) (proj₁ (lde-char K W eq min)) (proj₂ (lde-char K W eq min)))

-- A column with a positive exponent is not a column of I.
ne-𝕀 : (M : Matrix n n D) (c : Fin n) (k : ℕ) (W : Vec ℤ n) → col M c ≡ scV (suc k) W →
       Minimal (suc k) W → col M c ≢ col 𝕀 c
ne-𝕀 M c k W eq min e =
  ℕP.0≢1+n (≡.trans (≡.sym (proj₁ (lde-char 0 (eᶻ c) (col𝕀≡ c) (inj₁ ≡.refl))))
                    (proj₁ (lde-char (suc k) W (≡.trans (≡.sym e) eq) min)))

-- A column whose numerator differs from that of I at some entry is not
-- a column of I.
ne-𝕀-at : (M : Matrix n n D) (c : Fin n) (k : ℕ) (U : Vec ℤ n) → col M c ≡ scV k U → Minimal k U →
          (x : Fin n) → U ! x ≢ eᶻ c ! x → col M c ≢ col 𝕀 c
ne-𝕀-at M c k U eq min x ne e =
  ne (≡.cong (_! x) (≡.trans (≡.sym (proj₂ (lde-char k U (≡.trans (≡.sym e) eq) min)))
                             (proj₂ (lde-char 0 (eᶻ c) (col𝕀≡ c) (inj₁ ≡.refl)))))

------------------------------------------------------------------------
-- Levels from representations

-- A matrix that agrees with I beyond p, and whose column p is w / 2ᵏ
-- with fewer than m odd entries in w, lies below (p + 1 , k , m).
level-le : (M : Matrix n n D) {p : Fin n} → Beyond p M → (k : ℕ) (N : Vec ℤ n) → col M p ≡ scV k N →
           ∀ {m} → nodd N ℕ.< m → level M <ₗ (suc (toℕ p) , k , m)
level-le M {p} be k N eq {m} lt = by-pivot (pivot M) ≡.refl
  where
  L : Lvl
  L = suc (toℕ p) , k , m

  exact : Minimal k N → (lde (col M p) , nodd (num (col M p))) <₂ (k , m)
  exact mn = inj₂ (proj₁ (lde-char k N eq mn) ,
                   ≡.subst (λ w → nodd w ℕ.< m) (≡.sym (proj₂ (lde-char k N eq mn))) lt)

  rep< : (lde (col M p) , nodd (num (col M p))) <₂ (k , m)
  rep< = by-even (all-even? N)
    where
    by-even : Dec (∀ x → Even (N ! x)) → (lde (col M p) , nodd (num (col M p))) <₂ (k , m)
    by-even (no ¬ev) = exact (inj₂ (odd (FinP.¬∀⇒∃¬ n (λ x → Even (N ! x)) (λ x → oddℤ (N ! x) BoolP.≟ false) ¬ev)))
      where
      odd : (∃ λ x → ¬ Even (N ! x)) → ∃ λ x → Odd (N ! x)
      odd (x , ¬e) = x , ¬Even⇒Odd {N ! x} ¬e
    by-even (yes ev) = halve k ≡.refl
      where
      halve : ∀ k′ → k′ ≡ k → (lde (col M p) , nodd (num (col M p))) <₂ (k , m)
      halve ℕ.zero e = exact (inj₁ (≡.sym e))
      halve (suc k′) e =
        inj₁ (≡.subst (λ x → lde (col M p) ℕ.< x) e
               (s≤s (lde-≤ k′ (halveV N ev) (≡.trans eq (≡.trans (≡.cong (λ x → scV x N) (≡.sym e)) (scV-halve k′ N ev))))))

  by-pivot : (r : Maybe (Fin n)) → pivot M ≡ r → level M <ₗ L
  by-pivot nothing pv = ≡.subst (_<ₗ L) (≡.sym (≡.cong (λ x → lvlAt x M) pv)) (inj₁ (s≤s z≤n))
  by-pivot (just p′) pv = by-cmp (FinP.<-cmp p′ p)
    where
    by-cmp : Tri (p′ < p) (p′ ≡ p) (p < p′) → level M <ₗ L
    by-cmp (tri< p′<p _ _) = ≡.subst (_<ₗ L) (≡.sym (level-just M pv)) (inj₁ (s≤s p′<p))
    by-cmp (tri≈ _ p′≡p _) =
      ≡.subst (_<ₗ L) (≡.sym (level-just M (≡.trans pv (≡.cong just p′≡p)))) (inj₂ (≡.refl , rep<))
    by-cmp (tri> _ _ p<p′) = ⊥-elim (proj₁ (pivot-just M pv) (be p′ p<p′))

-- (x + 1 , 0 , 1) lies below a level with pivot p ≥ x and a positive
-- exponent.
bℓ-below : ∀ {x p : Fin n} {k : ℕ} (m : ℕ) → 0 ℕ.< k → toℕ x ℕ.≤ toℕ p → Bℓ x <ₗ (suc (toℕ p) , k , m)
bℓ-below {x} {p} {k} m 0<k x≤p = aux (ℕP.m≤n⇒m<n∨m≡n x≤p)
  where
  aux : toℕ x ℕ.< toℕ p ⊎ toℕ x ≡ toℕ p → Bℓ x <ₗ (suc (toℕ p) , k , m)
  aux (inj₁ lt) = inj₁ (s≤s lt)
  aux (inj₂ eq) = inj₂ (≡.cong suc eq , inj₁ 0<k)

------------------------------------------------------------------------
-- Words of X's and (-1)'s

-- Every letter is X or (-1), on indices ≤ b.
MonoWord : Fin n → Word (Gen n) → Set
MonoWord b [ X-gen x y p ]ʷ = y ≤ b
MonoWord b [ M-gen x ]ʷ     = x ≤ b
MonoWord b [ K-gen _ _ _ _ _ _ _ ]ʷ = Data.Empty.⊥
  where import Data.Empty
MonoWord b ε = ⊤
MonoWord b (u • v) = MonoWord b u × MonoWord b v

-- They keep a state below L.
mono-word-level : ∀ {b : Fin n} (w : Word (Gen n)) → MonoWord b w → (M : Matrix n n D) {L : Lvl} →
                  level M <ₗ L → Bℓ b <ₗ L → level (actMʷ w M) <ₗ L
mono-word-level [ X-gen x y p ]ʷ h M lM lB = mono-level (X-gen x y p) tt h M lM lB
mono-word-level [ M-gen x ]ʷ h M lM lB = mono-level (M-gen x) tt h M lM lB
mono-word-level [ K-gen _ _ _ _ _ _ _ ]ʷ () M lM lB
mono-word-level ε _ M lM lB = lM
mono-word-level (u • v) (hu , hv) M lM lB = mono-word-level u hu (actMʷ v M) (mono-word-level v hv M lM lB) lB

-- Every state along them lies below L.
mono-word-below : ∀ {b : Fin n} (w : Word (Gen n)) → MonoWord b w → (M : Matrix n n D) {L : Lvl} →
                  level M <ₗ L → Bℓ b <ₗ L → Low L w M
mono-word-below [ X-gen x y p ]ʷ h M lM lB = lM , mono-level (X-gen x y p) tt h M lM lB
mono-word-below [ M-gen x ]ʷ h M lM lB = lM , mono-level (M-gen x) tt h M lM lB
mono-word-below [ K-gen _ _ _ _ _ _ _ ]ʷ () M lM lB
mono-word-below ε _ M lM lB = tt
mono-word-below (u • v) (hu , hv) M lM lB =
  mono-word-below v hv M lM lB , mono-word-below u hu (actMʷ v M) (mono-word-level v hv M lM lB) lB
