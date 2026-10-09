------------------------------------------------------------------------
-- Presentations of groups
--
-- Levels under the monomial generators X_[a,b] and (-1)_[a]: they permute
-- the entries of a column and change their signs, so they keep its
-- least denominator exponent and its number of odd entries, and a word
-- of them acting on indices ≤ b keeps a state below any level that it
-- and (b + 1 , 0 , 1) lie below.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Levels where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (⊤)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no)


open import Examples.Groups.CCX+HH-TwoLevel.Ring
open import Examples.Groups.CCX+HH-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count ; count-cong ; count-drop ; count-one)
open import Examples.Groups.CCX+HH-TwoLevel.Column using (nodd)
open import Examples.Groups.CCX+HH-TwoLevel.ColumnAction
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable
  using (eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡ ; top ; actV-e-beyond ; Beyond-actM)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot
  using (pivot ; pivot-just ; pivot-nothing ; pivot-char ; Beyond ; Lvl ; lvlAt ; level ; level-just ; _<ₗ_ ; _<₂_)
open import Examples.Groups.CCX+HH-TwoLevel.Soundness using (sound-axiom)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Word.Base using ([_]ʷ ; ε ; _•_)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The number of odd entries

-- X swaps two entries.
nodd-X : (a b : Fin n) → a ≢ b → (w : Vec ℤ n) → nodd (Xᶻ a b w) ≡ nodd w
nodd-X a b a≢b w = by (oddℤ (w ! a)) (oddℤ (w ! b)) refl refl
  where
  P Q : Fin _ → Bool
  P x = oddℤ (w ! x)
  Q x = oddℤ (Xᶻ a b w ! x)
  Qa : Q a ≡ P b
  Qa = cong oddℤ (set₂-a a b (w ! b) (w ! a) w)
  Qb : Q b ≡ P a
  Qb = cong oddℤ (set₂-b a b (w ! b) (w ! a) w a≢b)
  Q≢ : ∀ x → x ≢ a → x ≢ b → Q x ≡ P x
  Q≢ x xa xb = cong oddℤ (set₂-≢ a b (w ! b) (w ! a) w xa xb)
  -- Both odd: the entries odd in both.
  Both : Fin _ → Bool
  Both x = P x ∧ Q x
  by : (pa pb : Bool) → P a ≡ pa → P b ≡ pb → count Q ≡ count P
  -- Equal parities at a and b: pointwise equal.
  by true true ea eb = count-cong Q P (λ x → same x (x FinP.≟ a) (x FinP.≟ b))
    where
    same : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Q x ≡ P x
    same x (yes refl) _ = trans Qa (trans eb (sym ea))
    same x (no xa) (yes refl) = trans Qb (trans ea (sym eb))
    same x (no xa) (no xb) = Q≢ x xa xb
  by false false ea eb = count-cong Q P (λ x → same x (x FinP.≟ a) (x FinP.≟ b))
    where
    same : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Q x ≡ P x
    same x (yes refl) _ = trans Qa (trans eb (sym ea))
    same x (no xa) (yes refl) = trans Qb (trans ea (sym eb))
    same x (no xa) (no xb) = Q≢ x xa xb
  -- Different parities: both counts exceed that of Both by one.
  by true false ea eb =
    trans (count-drop Q Both b (trans Qb ea) (cong (_∧ Q b) eb) (λ x xb → sym (atQ x xb (x FinP.≟ a))))
          (sym (count-drop P Both a ea (trans (cong (_∧ Q a) ea) (trans Qa eb)) (λ x xa → sym (atP x xa (x FinP.≟ b)))))
    where
    atP : ∀ x → x ≢ a → Dec (x ≡ b) → Both x ≡ P x
    atP x xa (yes refl) = trans (cong (_∧ Q x) eb) (sym eb)
    atP x xa (no xb) = trans (cong (P x ∧_) (Q≢ x xa xb)) (∧-idem (P x))
      where
      ∧-idem : ∀ c → c ∧ c ≡ c
      ∧-idem true = refl
      ∧-idem false = refl
    atQ : ∀ x → x ≢ b → Dec (x ≡ a) → Both x ≡ Q x
    atQ x xb (yes refl) = trans (cong (λ c → c ∧ Q x) ea) (refl)
    atQ x xb (no xa) = trans (cong (_∧ Q x) (sym (Q≢ x xa xb))) (∧-idem (Q x))
      where
      ∧-idem : ∀ c → c ∧ c ≡ c
      ∧-idem true = refl
      ∧-idem false = refl
  by false true ea eb =
    trans (count-drop Q Both a (trans Qa eb) (trans (cong (_∧ Q a) ea) refl) (λ x xa → sym (atQ x xa (x FinP.≟ b))))
          (sym (count-drop P Both b eb (trans (cong (_∧ Q b) eb) (trans (cong (true ∧_) Qb) ea))
                                    (λ x xb → sym (atP x xb (x FinP.≟ a)))))
    where
    atP : ∀ x → x ≢ b → Dec (x ≡ a) → Both x ≡ P x
    atP x xb (yes refl) = trans (cong (_∧ Q x) ea) (sym ea)
    atP x xb (no xa) = trans (cong (P x ∧_) (Q≢ x xa xb)) (∧-idem (P x))
      where
      ∧-idem : ∀ c → c ∧ c ≡ c
      ∧-idem true = refl
      ∧-idem false = refl
    atQ : ∀ x → x ≢ a → Dec (x ≡ b) → Both x ≡ Q x
    atQ x xa (yes refl) = trans (cong (_∧ Q x) eb) refl
    atQ x xa (no xb) = trans (cong (_∧ Q x) (sym (Q≢ x xa xb))) (∧-idem (Q x))
      where
      ∧-idem : ∀ c → c ∧ c ≡ c
      ∧-idem true = refl
      ∧-idem false = refl

-- (-1) negates an entry, which keeps its parity.
odd-M : (a : Fin n) (w : Vec ℤ n) (x : Fin n) → oddℤ (Mᶻ a w ! x) ≡ oddℤ (w ! x)
odd-M a w x = at (x FinP.≟ a)
  where
  at : Dec (x ≡ a) → oddℤ (Mᶻ a w ! x) ≡ oddℤ (w ! x)
  at (yes refl) = trans (cong oddℤ (set₁-a x (ℤ.- (w ! x)) w)) (oddℤ-neg (w ! x))
  at (no xa) = cong oddℤ (set₁-≢ a (ℤ.- (w ! a)) w xa)

nodd-M : (a : Fin n) (w : Vec ℤ n) → nodd (Mᶻ a w) ≡ nodd w
nodd-M a w = count-cong (λ x → oddℤ (Mᶻ a w ! x)) (λ x → oddℤ (w ! x)) (odd-M a w)

-- A standard basis vector has one odd entry.
nodd-e : (c : Fin n) → nodd (eᶻ c) ≡ 1
nodd-e c = count-one (λ x → oddℤ (eᶻ c ! x)) c
  (trans (cong oddℤ (trans (eᶻ-! c c) (eδ-refl c))) refl)
  (λ x x≢c → trans (cong oddℤ (trans (eᶻ-! c x) (eδ-≢ x≢c))) refl)

------------------------------------------------------------------------
-- The least denominator exponent

-- Minimality is kept.
Minimal-X : ∀ {k} (a b : Fin n) → a ≢ b → (w : Vec ℤ n) → Minimal k w → Minimal k (Xᶻ a b w)
Minimal-X a b a≢b w (inj₁ k0) = inj₁ k0
Minimal-X a b a≢b w (inj₂ (x , ox)) = inj₂ (at (x FinP.≟ a) (x FinP.≟ b))
  where
  open import Data.Product.Base using (∃)
  at : Dec (x ≡ a) → Dec (x ≡ b) → ∃ λ y → Odd (Xᶻ a b w ! y)
  at (yes refl) _ = b , trans (cong oddℤ (set₂-b x b (w ! b) (w ! x) w a≢b)) ox
  at (no xa) (yes refl) = a , trans (cong oddℤ (set₂-a a x (w ! x) (w ! a) w)) ox
  at (no xa) (no xb) = x , trans (cong oddℤ (set₂-≢ a b (w ! b) (w ! a) w xa xb)) ox

Minimal-M : ∀ {k} (a : Fin n) (w : Vec ℤ n) → Minimal k w → Minimal k (Mᶻ a w)
Minimal-M a w (inj₁ k0) = inj₁ k0
Minimal-M a w (inj₂ (x , ox)) = inj₂ (x , trans (odd-M a w x) ox)

-- X and (-1) keep the exponent, and act on the numerator.
lde-X : (a b : Fin n) .(p : a < b) (v : Vec D n) →
        lde (actV (X-gen a b p) v) ≡ lde v × num (actV (X-gen a b p) v) ≡ Xᶻ a b (num v)
lde-X a b p v = lde-char (lde v) (Xᶻ a b (num v))
  (trans (cong (actV (X-gen a b p)) (lde-eq v)) (actV-X a b p (lde v) (num v)))
  (Minimal-X a b (<⇒≢ p) (num v) (lde-min v))

lde-M : (a : Fin n) (v : Vec D n) →
        lde (actV (M-gen a) v) ≡ lde v × num (actV (M-gen a) v) ≡ Mᶻ a (num v)
lde-M a v = lde-char (lde v) (Mᶻ a (num v))
  (trans (cong (actV (M-gen a)) (lde-eq v)) (actV-M a (lde v) (num v)))
  (Minimal-M a (num v) (lde-min v))

------------------------------------------------------------------------
-- The monomial generators

Mono : Gen n → Set
Mono (X-gen _ _ _) = ⊤
Mono (K-gen _ _ _ _ _ _ _) = ⊥
Mono (M-gen _)     = ⊤

-- The level data of a column is kept.
mono-col : (g : Gen n) → Mono g → (v : Vec D n) →
           lde (actV g v) ≡ lde v × nodd (num (actV g v)) ≡ nodd (num v)
mono-col (X-gen a b p) _ v =
  proj₁ (lde-X a b p v) , trans (cong nodd (proj₂ (lde-X a b p v))) (nodd-X a b (<⇒≢ p) (num v))
mono-col (M-gen a) _ v =
  proj₁ (lde-M a v) , trans (cong nodd (proj₂ (lde-M a v))) (nodd-M a (num v))

-- A standard basis vector goes to one of level data (0 , 1).
mono-e : (g : Gen n) → Mono g → (c : Fin n) →
         lde (actV g (col 𝕀 c)) ≡ 0 × nodd (num (actV g (col 𝕀 c))) ≡ 1
mono-e g m c =
  trans (proj₁ (mono-col g m (col 𝕀 c))) (proj₁ e₀) ,
  trans (proj₂ (mono-col g m (col 𝕀 c))) (trans (cong nodd (proj₂ e₀)) (nodd-e c))
  where
  e₀ : lde (col 𝕀 c) ≡ 0 × num (col 𝕀 c) ≡ eᶻ c
  e₀ = lde-char 0 (eᶻ c) (col𝕀≡ c) (inj₁ refl)

-- X and (-1) are involutions.
private
  X-X-act : (a b : Fin n) .(p : a < b) (v : Vec D n) → actV (X-gen a b p) (actV (X-gen a b p) v) ≡ v
  X-X-act a b p v = same-action (X a b p • X a b p) ε (sound-axiom (r1a p)) v

  M-M-act : (a : Fin n) (v : Vec D n) → actV (M-gen a) (actV (M-gen a) v) ≡ v
  M-M-act a v = same-action (M a • M a) ε (sound-axiom r1b) v

mono-inj : (g : Gen n) → Mono g → {u v : Vec D n} → actV g u ≡ actV g v → u ≡ v
mono-inj (X-gen a b p) _ {u} {v} eq =
  trans (sym (X-X-act a b p u)) (trans (cong (actV (X-gen a b p)) eq) (X-X-act a b p v))
mono-inj (M-gen a) _ {u} {v} eq =
  trans (sym (M-M-act a u)) (trans (cong (actV (M-gen a)) eq) (M-M-act a v))

------------------------------------------------------------------------
-- Levels

private
  <₂-trans : {x y z : ℕ × ℕ} → x <₂ y → y <₂ z → x <₂ z
  <₂-trans (inj₁ a) (inj₁ b) = inj₁ (ℕP.<-trans a b)
  <₂-trans (inj₁ a) (inj₂ (refl , b)) = inj₁ a
  <₂-trans (inj₂ (refl , a)) (inj₁ b) = inj₁ b
  <₂-trans (inj₂ (refl , a)) (inj₂ (refl , b)) = inj₂ (refl , ℕP.<-trans a b)

<ₗ-trans : {x y z : Lvl} → x <ₗ y → y <ₗ z → x <ₗ z
<ₗ-trans (inj₁ a) (inj₁ b) = inj₁ (ℕP.<-trans a b)
<ₗ-trans (inj₁ a) (inj₂ (refl , b)) = inj₁ a
<ₗ-trans (inj₂ (refl , a)) (inj₁ b) = inj₁ b
<ₗ-trans (inj₂ (refl , a)) (inj₂ (refl , b)) = inj₂ (refl , <₂-trans a b)

-- The level of a matrix whose pivot column is the image of a basis
-- vector under g: (c + 1 , 0 , 1).
Bℓ : Fin n → Lvl
Bℓ b = suc (toℕ b) , 0 , 1

-- A monomial generator acting on indices ≤ b keeps the level below
-- any bound that both the level of M and (b + 1 , 0 , 1) lie below.
mono-level : (g : Gen n) → Mono g → {b : Fin n} → top g ≤ b → (M : Matrix n n D) {L : Lvl} →
             level M <ₗ L → Bℓ b <ₗ L → level (actM g M) <ₗ L
mono-level {n} g m {b} tg M {L} lM lB = go (pivot (actM g M)) refl
  where
  gM = actM g M

  col-g : ∀ c → col gM c ≡ actV g (col M c)
  col-g c = col-actM g M c

  -- The level of gM, given its pivot c and that col gM c comes from
  -- col M c, compared to a level of the same pivot.
  same-as : ∀ {c} → pivot gM ≡ just c → pivot M ≡ just c → level gM ≡ level M
  same-as {c} eg em = trans (level-just gM eg) (trans (cong₂ (λ k m′ → suc (toℕ c) , k , m′)
      (trans (cong lde (col-g c)) (proj₁ (mono-col g m (col M c))))
      (trans (cong (λ v → nodd (num v)) (col-g c)) (proj₂ (mono-col g m (col M c)))))
    (sym (level-just M em)))

  -- The pivot column of gM is g applied to a basis vector.
  from-e : ∀ {c} → pivot gM ≡ just c → col M c ≡ col 𝕀 c → level gM ≡ (suc (toℕ c) , 0 , 1)
  from-e {c} eg ec = trans (level-just gM eg) (cong₂ (λ k m′ → suc (toℕ c) , k , m′)
      (trans (cong lde (trans (col-g c) (cong (actV g) ec))) (proj₁ (mono-e g m c)))
      (trans (cong (λ v → nodd (num v)) (trans (col-g c) (cong (actV g) ec))) (proj₂ (mono-e g m c))))

  below-B : ∀ {c} → toℕ c ℕ.≤ toℕ b → (suc (toℕ c) , 0 , 1) <ₗ L
  below-B {c} c≤b = at (ℕP.m≤n⇒m<n∨m≡n c≤b)
    where
    at : toℕ c ℕ.< toℕ b ⊎ toℕ c ≡ toℕ b → (suc (toℕ c) , 0 , 1) <ₗ L
    at (inj₁ c<b) = <ₗ-trans (inj₁ (ℕ.s≤s c<b)) lB
    at (inj₂ c≡b) = subst (λ k → (suc k , 0 , 1) <ₗ L) (sym c≡b) lB


  -- Beyond b, g changes nothing: a pivot of gM there is one of M.
  back : ∀ {c} → b < c → pivot gM ≡ just c → pivot M ≡ just c
  back {c} b<c eg = pivot-char M ne be
    where
    ne : col M c ≢ col 𝕀 c
    ne eq = proj₁ (pivot-just gM eg) (trans (col-g c) (trans (cong (actV g) eq) (actV-e-beyond g tg b<c)))
    be : Beyond c M
    be d c<d = mono-inj g m (trans (sym (col-g d))
                 (trans (proj₂ (pivot-just gM eg) d c<d)
                   (sym (actV-e-beyond g tg (ℕP.<-trans b<c c<d)))))

  -- The pivot c of gM is at most b: compare with the pivot of M.
  low : ∀ {c} → toℕ c ℕ.≤ toℕ b → pivot gM ≡ just c → (r : Maybe (Fin n)) → pivot M ≡ r → level gM <ₗ L
  low {c} c≤b eg nothing em =
    subst (_<ₗ L) (sym (from-e eg (cong (λ N → col N c) (pivot-nothing M em)))) (below-B c≤b)
  low {c} c≤b eg (just p) em = by (FinP.<-cmp c p)
    where
    by : Tri (c < p) (c ≡ p) (p < c) → level gM <ₗ L
    by (tri< c<p _ _) = <ₗ-trans (subst (_<ₗ level M) (sym (level-just gM eg))
                                   (subst ((suc (toℕ c) , lde (col gM c) , nodd (num (col gM c))) <ₗ_)
                                          (sym (level-just M em)) (inj₁ (ℕ.s≤s c<p)))) lM
    by (tri≈ _ refl _) = subst (_<ₗ L) (sym (same-as eg em)) lM
    by (tri> _ _ p<c) = subst (_<ₗ L) (sym (from-e eg (proj₂ (pivot-just M em) c p<c))) (below-B c≤b)

  go : (r : Maybe (Fin n)) → pivot gM ≡ r → level gM <ₗ L
  go nothing e = subst (_<ₗ L) (sym (cong (λ x → lvlAt x gM) e)) (<ₗ-trans (inj₁ (ℕ.s≤s ℕ.z≤n)) lB)
  go (just c) e = cmp (FinP.<-cmp b c)
    where
    cmp : Tri (b < c) (b ≡ c) (c < b) → level gM <ₗ L
    cmp (tri< b<c _ _) = subst (_<ₗ L) (sym (same-as e (back b<c e))) lM
    cmp (tri≈ _ refl _) = low ℕP.≤-refl e (pivot M) refl
    cmp (tri> _ _ c<b) = low (ℕP.<⇒≤ c<b) e (pivot M) refl

------------------------------------------------------------------------
-- Levels, non-strictly

infix 4 _≤ₗ′_

_≤ₗ′_ : Lvl → Lvl → Set
x ≤ₗ′ y = x <ₗ y ⊎ x ≡ y

≤ₗ′-trans : {x y z : Lvl} → x ≤ₗ′ y → y ≤ₗ′ z → x ≤ₗ′ z
≤ₗ′-trans (inj₁ a) (inj₁ b) = inj₁ (<ₗ-trans a b)
≤ₗ′-trans (inj₁ a) (inj₂ refl) = inj₁ a
≤ₗ′-trans (inj₂ refl) b = b

-- A monomial generator acting on indices ≤ b does not raise the level
-- of M beyond the larger of it and (b + 1 , 0 , 1).
mono-le : (g : Gen n) → Mono g → {b : Fin n} → top g ≤ b → (M : Matrix n n D) →
          level (actM g M) ≤ₗ′ level M ⊎ level (actM g M) ≤ₗ′ Bℓ b
mono-le {n} g m {b} tg M = go (pivot (actM g M)) refl
  where
  gM = actM g M

  col-g : ∀ c → col gM c ≡ actV g (col M c)
  col-g c = col-actM g M c

  same-as : ∀ {c} → pivot gM ≡ just c → pivot M ≡ just c → level gM ≡ level M
  same-as {c} eg em = trans (level-just gM eg) (trans (cong₂ (λ k m′ → suc (toℕ c) , k , m′)
      (trans (cong lde (col-g c)) (proj₁ (mono-col g m (col M c))))
      (trans (cong (λ v → nodd (num v)) (col-g c)) (proj₂ (mono-col g m (col M c)))))
    (sym (level-just M em)))

  from-e : ∀ {c} → pivot gM ≡ just c → col M c ≡ col 𝕀 c → level gM ≡ (suc (toℕ c) , 0 , 1)
  from-e {c} eg ec = trans (level-just gM eg) (cong₂ (λ k m′ → suc (toℕ c) , k , m′)
      (trans (cong lde (trans (col-g c) (cong (actV g) ec))) (proj₁ (mono-e g m c)))
      (trans (cong (λ v → nodd (num v)) (trans (col-g c) (cong (actV g) ec))) (proj₂ (mono-e g m c))))

  le-B : ∀ {c} → toℕ c ℕ.≤ toℕ b → (suc (toℕ c) , 0 , 1) ≤ₗ′ Bℓ b
  le-B {c} c≤b = at (ℕP.m≤n⇒m<n∨m≡n c≤b)
    where
    at : toℕ c ℕ.< toℕ b ⊎ toℕ c ≡ toℕ b → (suc (toℕ c) , 0 , 1) ≤ₗ′ Bℓ b
    at (inj₁ c<b) = inj₁ (inj₁ (ℕ.s≤s c<b))
    at (inj₂ c≡b) = inj₂ (cong (λ k → suc k , 0 , 1) c≡b)

  back : ∀ {c} → b < c → pivot gM ≡ just c → pivot M ≡ just c
  back {c} b<c eg = pivot-char M ne be
    where
    ne : col M c ≢ col 𝕀 c
    ne eq = proj₁ (pivot-just gM eg) (trans (col-g c) (trans (cong (actV g) eq) (actV-e-beyond g tg b<c)))
    be : Beyond c M
    be d c<d = mono-inj g m (trans (sym (col-g d))
                 (trans (proj₂ (pivot-just gM eg) d c<d)
                   (sym (actV-e-beyond g tg (ℕP.<-trans b<c c<d)))))

  low : ∀ {c} → toℕ c ℕ.≤ toℕ b → pivot gM ≡ just c → (r : Maybe (Fin n)) → pivot M ≡ r →
        level gM ≤ₗ′ level M ⊎ level gM ≤ₗ′ Bℓ b
  low {c} c≤b eg nothing em =
    inj₂ (subst (_≤ₗ′ Bℓ b) (sym (from-e eg (cong (λ N → col N c) (pivot-nothing M em)))) (le-B c≤b))
  low {c} c≤b eg (just p) em = by (FinP.<-cmp c p)
    where
    by : Tri (c < p) (c ≡ p) (p < c) → level gM ≤ₗ′ level M ⊎ level gM ≤ₗ′ Bℓ b
    by (tri< c<p _ _) = inj₁ (inj₁ (subst (_<ₗ level M) (sym (level-just gM eg))
                                   (subst ((suc (toℕ c) , lde (col gM c) , nodd (num (col gM c))) <ₗ_)
                                          (sym (level-just M em)) (inj₁ (ℕ.s≤s c<p)))))
    by (tri≈ _ refl _) = inj₁ (inj₂ (same-as eg em))
    by (tri> _ _ p<c) = inj₂ (subst (_≤ₗ′ Bℓ b) (sym (from-e eg (proj₂ (pivot-just M em) c p<c))) (le-B c≤b))

  go : (r : Maybe (Fin n)) → pivot gM ≡ r → level gM ≤ₗ′ level M ⊎ level gM ≤ₗ′ Bℓ b
  go nothing e = inj₂ (inj₁ (subst (_<ₗ Bℓ b) (sym (cong (λ x → lvlAt x gM) e)) (inj₁ (ℕ.s≤s ℕ.z≤n))))
  go (just c) e = cmp (FinP.<-cmp b c)
    where
    cmp : Tri (b < c) (b ≡ c) (c < b) → level gM ≤ₗ′ level M ⊎ level gM ≤ₗ′ Bℓ b
    cmp (tri< b<c _ _) = inj₁ (inj₂ (same-as e (back b<c e)))
    cmp (tri≈ _ refl _) = low ℕP.≤-refl e (pivot M) refl
    cmp (tri> _ _ c<b) = low (ℕP.<⇒≤ c<b) e (pivot M) refl

-- So it keeps a state at most at L at most at L, if (b + 1 , 0 , 1) is.
mono-level-≤ : (g : Gen n) → Mono g → {b : Fin n} → top g ≤ b → (M : Matrix n n D) {L : Lvl} →
               level M ≤ₗ′ L → Bℓ b ≤ₗ′ L → level (actM g M) ≤ₗ′ L
mono-level-≤ g m tg M lM lB with mono-le g m tg M
... | inj₁ x = ≤ₗ′-trans x lM
... | inj₂ x = ≤ₗ′-trans x lB
