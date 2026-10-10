------------------------------------------------------------------------
-- Presentations of groups
--
-- States and their pivot columns, for the proof of Lemma 4.4.
--
-- * Clément's levels and those of Real-Clifford+CH-TwoLevel (Pivot)
--   differ only in the count of a unit column, so they compare alike
--   with a level whose exponent is positive (Pos): the lemmas on levels
--   there (States, Levels) serve here.
-- * The syllable and the level of a state, from a representation of
--   its pivot column (sylᶜ-of, levelᶜ-of).
-- * At s: the data of a state with pivot p, and of g·s for X and Z on
--   indices at most p, which act on the numerator of column p alone.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.State {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; not ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; recompute)
import Data.Nat.Properties as ℕP
import Data.Integer.Base as ℤ
import Data.Integer.Properties as ℤP
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (tri-elim ; dec-elim ; count ; count-one ; count-drop ; count-drop₂)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (first-cong ; count-cong)
open import Relation.Nullary using (¬_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; oddᶻ ; rbit ; oddᶻ-neg ; rbit-neg ; _≟ᶻ_ ; oddℕ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde
  using (_!_ ; scV ; Minimal ; Odd ; Even ; Odd⇒¬Even ; lde ; num ; lde-eq ; lde-min ; lde-char)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm using (NA ; NB ; Σℕ ; Σℤ ; lde0 ; evenodd ; evenclass)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
  using (nodd ; firstOdd ; nextSame ; negᶻ ; Same ; firstOdd-spec ; firstOdd-nothing ; nextSame-spec ; nextSame-nothing)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Zᶻ ; Xᶻ ; actV-Z ; actV-X)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot
  using (pivot ; pivot-just ; pivot-char ; Beyond ; Lvl ; lvlAt ; level ; level-just ; _<ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable using (top ; Beyond-actM ; set₁-self ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step
  using (pivot-zero> ; col-norm ; col-normB ; odd⇒≤ ; same-class ; pairW ; H-action ; pairW-j ; pairW-ℓ ; pairW-≢)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (level-le)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Levels using (Minimal-X ; Minimal-Z ; nodd-X ; nodd-Z)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} as R
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Algorithm
  using (third ; lvlAtᶜ ; levelᶜ ; levelᶜ-just ; sylᶜ ; sylᶜ-just ; sylDataᶜ ; partner)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction {n} using (Low)

------------------------------------------------------------------------
-- Levels with a positive exponent

private
  -- The two levels of M: equal, or both with exponent 0 and one pivot.
  Shape : Matrix n n D → Set
  Shape M = levelᶜ M ≡ level M ⊎
            (proj₁ (levelᶜ M) ≡ proj₁ (level M) × proj₁ (proj₂ (levelᶜ M)) ≡ 0 × proj₁ (proj₂ (level M)) ≡ 0)

  shape : (M : Matrix n n D) → Shape M
  shape M = by (pivot M) ≡.refl
    where
    by : (r : Maybe (Fin n)) → pivot M ≡ r → Shape M
    by nothing e = inj₁ (≡.trans (≡.cong (λ x → lvlAtᶜ x M) e) (≡.sym (≡.cong (λ x → lvlAt x M) e)))
    by (just q) e = by-k (lde (col M q)) ≡.refl
      where
      by-k : ∀ K → lde (col M q) ≡ K → Shape M
      by-k zero eK = inj₂ ( ≡.trans (≡.cong proj₁ (levelᶜ-just M e)) (≡.sym (≡.cong proj₁ (level-just M e)))
                          , ≡.trans (≡.cong (λ t → proj₁ (proj₂ t)) (levelᶜ-just M e)) eK
                          , ≡.trans (≡.cong (λ t → proj₁ (proj₂ t)) (level-just M e)) eK )
      by-k (suc K′) eK = inj₁ (≡.trans (levelᶜ-just M e) (≡.trans mid (≡.sym (level-just M e))))
        where
        mid : (suc (toℕ q) , lde (col M q) , third (lde (col M q)) (num (col M q))) ≡
              (suc (toℕ q) , lde (col M q) , nodd (num (col M q)))
        mid = ≡.cong (λ k → suc (toℕ q) , lde (col M q) , third k (num (col M q))) eK

module Pos {a k′ ℓ : ℕ} where

  private
    L : Lvl
    L = a , suc k′ , ℓ

    zero-mid : (t t′ : Lvl) → proj₁ t ≡ proj₁ t′ → proj₁ (proj₂ t) ≡ 0 → proj₁ (proj₂ t′) ≡ 0 → t <ₗ L → t′ <ₗ L
    zero-mid (x , y , z) (x′ , y′ , z′) ≡.refl ≡.refl ≡.refl (inj₁ lt) = inj₁ lt
    zero-mid (x , y , z) (x′ , y′ , z′) ≡.refl ≡.refl ≡.refl (inj₂ (e , _)) = inj₂ (e , inj₁ (s≤s z≤n))

    zero-≢ : (t : Lvl) → proj₁ (proj₂ t) ≡ 0 → t ≢ L
    zero-≢ (x , .0 , z) ≡.refl ()

  conv< : (M : Matrix n n D) → level M <ₗ L → levelᶜ M <ₗ L
  conv< M lt = go (shape M)
    where
    go : Shape M → levelᶜ M <ₗ L
    go (inj₁ e) = ≡.subst (_<ₗ L) (≡.sym e) lt
    go (inj₂ (e₁ , e₂ , e₃)) = zero-mid (level M) (levelᶜ M) (≡.sym e₁) e₃ e₂ lt

  conv> : (M : Matrix n n D) → levelᶜ M <ₗ L → level M <ₗ L
  conv> M lt = go (shape M)
    where
    go : Shape M → level M <ₗ L
    go (inj₁ e) = ≡.subst (_<ₗ L) e lt
    go (inj₂ (e₁ , e₂ , e₃)) = zero-mid (levelᶜ M) (level M) e₁ e₂ e₃ lt

  conv≡ : (M : Matrix n n D) → levelᶜ M ≡ L → level M ≡ L
  conv≡ M eq = go (shape M)
    where
    go : Shape M → level M ≡ L
    go (inj₁ e) = ≡.trans (≡.sym e) eq
    go (inj₂ (e₁ , e₂ , e₃)) = ⊥-elim (zero-≢ (levelᶜ M) e₂ eq)

  conv≡′ : (M : Matrix n n D) → level M ≡ L → levelᶜ M ≡ L
  conv≡′ M eq = go (shape M)
    where
    go : Shape M → levelᶜ M ≡ L
    go (inj₁ e) = ≡.trans e eq
    go (inj₂ (e₁ , e₂ , e₃)) = ⊥-elim (zero-≢ (level M) e₃ eq)

  low-conv : (w : Word (Gen n)) (M : Matrix n n D) → R.Low L w M → Low L w M
  low-conv [ g ]ʷ M (l₁ , l₂) = conv< M l₁ , conv< (actM g M) l₂
  low-conv ε M _ = tt
  low-conv (u • v) M (lv , lu) = low-conv v M lv , low-conv u (actMʷ v M) lu

------------------------------------------------------------------------
-- The syllable and the level, from a representation of the pivot
-- column

sylᶜ-of : (M : Matrix n n D) {p : Fin n} → pivot M ≡ just p → (K : ℕ) (W : Vec Z n) →
          col M p ≡ scV K W → Minimal K W → sylᶜ M ≡ sylDataᶜ p K W
sylᶜ-of M {p} pv K W eq min =
  ≡.trans (sylᶜ-just M pv) (≡.cong₂ (sylDataᶜ p) (proj₁ (lde-char K W eq min)) (proj₂ (lde-char K W eq min)))

levelᶜ-of : (M : Matrix n n D) {p : Fin n} → pivot M ≡ just p → (K : ℕ) (W : Vec Z n) →
            col M p ≡ scV K W → Minimal K W → levelᶜ M ≡ (suc (toℕ p) , K , third K W)
levelᶜ-of M {p} pv K W eq min =
  ≡.trans (levelᶜ-just M pv)
    (≡.cong₂ (λ k w → suc (toℕ p) , k , third k w) (proj₁ (lde-char K W eq min)) (proj₂ (lde-char K W eq min)))

------------------------------------------------------------------------
-- Parities after X and Z

odd-Z : (a : Fin n) (w : Vec Z n) (x : Fin n) → oddᶻ (Zᶻ a w ! x) ≡ oddᶻ (w ! x)
odd-Z a w x with x FinP.≟ a
... | yes ≡.refl = ≡.trans (≡.cong oddᶻ (set₁-a x (ZR.- (w ! x)) w)) (oddᶻ-neg (w ! x))
... | no x≢a = ≡.cong oddᶻ (set₁-≢ a (ZR.- (w ! a)) w x≢a)

rbit-Z : (a : Fin n) (w : Vec Z n) (x : Fin n) → rbit (Zᶻ a w ! x) ≡ rbit (w ! x)
rbit-Z a w x with x FinP.≟ a
... | yes ≡.refl = ≡.trans (≡.cong rbit (set₁-a x (ZR.- (w ! x)) w)) (rbit-neg (w ! x))
... | no x≢a = ≡.cong rbit (set₁-≢ a (ZR.- (w ! a)) w x≢a)

-- Z keeps the first odd entry and the next one in each class.
firstOdd-Z : (a : Fin n) (w : Vec Z n) → firstOdd (Zᶻ a w) ≡ firstOdd w
firstOdd-Z a w = first-cong _ _ (odd-Z a w)

nextSame-Z : (a j : Fin n) (w : Vec Z n) → nextSame j (Zᶻ a w) ≡ nextSame j w
nextSame-Z a j w = first-cong _ _ λ x →
  ≡.cong₂ (λ o r → does (j FinP.<? x) ∧ (o ∧ r))
    (odd-Z a w x) (≡.cong₂ (λ u v → not (u xor v)) (rbit-Z a w x) (rbit-Z a w j))

-- Z at an entry 0 changes nothing.
Zᶻ-0 : (a : Fin n) (w : Vec Z n) → w ! a ≡ ZR.0# → Zᶻ a w ≡ w
Zᶻ-0 a w e = ≡.trans (≡.cong (λ z → set₁ a (ZR.- z) w) e) (≡.trans (≡.cong (λ z → set₁ a z w) (≡.sym e)) (set₁-self a w))

------------------------------------------------------------------------
-- H on two odd entries of one class, at a fixed scale

-- Both become even, the others stay, and the count drops by two.
valid-step : (M : Matrix n n D) (p : Fin n) (K : ℕ) (w : Vec Z n) → col M p ≡ scV K w →
             (i i′ : Fin n) .(ii′ : i < i′) → Odd (w ! i) → Odd (w ! i′) → rbit (w ! i) ≡ rbit (w ! i′) →
             ∃ λ w′ → col (actM (H-gen i i′ ii′) M) p ≡ scV K w′ × nodd w ≡ suc (suc (nodd w′)) ×
                      (∀ x → x ≢ i → x ≢ i′ → w′ ! x ≡ w ! x) × Even (w′ ! i) × Even (w′ ! i′)
valid-step M p K w eq i i′ ii′ oi oi′ rb =
  w′ , col′ , cnt , pairW-≢ w i i′ z , pairW-j w i i′ z , pairW-ℓ w i i′ z i≢i′
  where
  i≢i′ : i ≢ i′
  i≢i′ = <⇒≢ ii′
  zc = same-class (w ! i) (w ! i′) oi oi′ rb
  z = proj₁ zc
  w′ = pairW w i i′ z
  col′ : col (actM (H-gen i i′ ii′) M) p ≡ scV K w′
  col′ = ≡.trans (col-actM (H-gen i i′ ii′) M p)
           (≡.trans (≡.cong (actV (H-gen i i′ ii′)) eq) (H-action K w i i′ ii′ z (proj₂ zc)))
  cnt : nodd w ≡ suc (suc (nodd w′))
  cnt = count-drop₂ (λ x → oddᶻ (w ! x)) (λ x → oddᶻ (w′ ! x)) i i′ i≢i′ oi oi′
          (pairW-j w i i′ z) (pairW-ℓ w i i′ z i≢i′)
          (λ x x≢i x≢i′ → ≡.sym (≡.cong oddᶻ (pairW-≢ w i i′ z x x≢i x≢i′)))

-- A state agreeing with I beyond p, whose column p is w / √2^(k′+1)
-- with fewer than m odd entries in w, lies below (p + 1, k′ + 1, m).
lowᶜ : (M : Matrix n n D) {p : Fin n} → Beyond p M → (k′ : ℕ) (w : Vec Z n) → col M p ≡ scV (suc k′) w →
       ∀ {m} → nodd w ℕ.< m → levelᶜ M <ₗ (suc (toℕ p) , suc k′ , m)
lowᶜ M be k′ w eq lt = Pos.conv< M (level-le M be (suc k′) w eq lt)

-- X at two entries 0 changes nothing.
Xᶻ-00 : (a b : Fin n) (w : Vec Z n) → a ≢ b → w ! a ≡ ZR.0# → w ! b ≡ ZR.0# → Xᶻ a b w ≡ w
Xᶻ-00 a b w a≢b ea eb = vec-ext λ x → dec-elim (x FinP.≟ a)
  (λ { ≡.refl → ≡.trans (set₂-a x b (w ! b) (w ! x) w) (≡.trans eb (≡.sym ea)) })
  (λ x≢a → dec-elim (x FinP.≟ b)
    (λ { ≡.refl → ≡.trans (set₂-b a x (w ! x) (w ! a) w a≢b) (≡.trans ea (≡.sym eb)) })
    (λ x≢b → set₂-≢ a b (w ! b) (w ! a) w x≢a x≢b))

------------------------------------------------------------------------
-- The first odd entry of a class has a partner (Lemma 2.1)

partner′ : ∀ k′ (w : Vec Z n) → Σℕ (λ x → NA (w ! x)) ≡ 2 ℕ.^ suc k′ → Σℤ (λ x → NB (w ! x)) ≡ ℤ.+ 0 →
           ∀ {j} → Odd (w ! j) → (∀ y → y < j → ¬ Same w j y) → nextSame j w ≡ nothing → ⊥
partner′ k′ w norm normB {j} oj before nx = by-class (rbit (w ! j)) ≡.refl
  where
  t≢f : true ≢ false
  t≢f ()
  -- No other entry is odd in the class of j.
  others : ∀ y → y ≢ j → Odd (w ! y) → rbit (w ! y) ≢ rbit (w ! j)
  others y y≢j oy rb = tri-elim (FinP.<-cmp y j)
    (λ y<j → before y y<j (oy , rb))
    (λ y≡j → y≢j y≡j)
    (λ j<y → nextSame-nothing w nx y j<y (oy , rb))
  by-class : ∀ b → rbit (w ! j) ≡ b → ⊥
  by-class true rb = t≢f (≡.trans (≡.sym (≡.cong oddℕ one)) (evenclass w normB))
    where
    P : Fin n → Bool
    P y = oddᶻ (w ! y) ∧ rbit (w ! y)
    noP : ∀ y → y ≢ j → P y ≡ false
    noP y y≢j with oddᶻ (w ! y) in oy | rbit (w ! y) in ry
    ... | false | _ = ≡.refl
    ... | true | false = ≡.refl
    ... | true | true = ⊥-elim (others y y≢j oy (≡.trans ry (≡.sym rb)))
    one : count P ≡ 1
    one = count-one P j (≡.cong₂ _∧_ oj rb) noP
  by-class false rb = t≢f (≡.trans (≡.sym oddsum) (evenodd k′ w norm))
    where
    P Q : Fin n → Bool
    P y = oddᶻ (w ! y)
    Q y = oddᶻ (w ! y) ∧ rbit (w ! y)
    ∧-false : ∀ b → b ∧ false ≡ false
    ∧-false true = ≡.refl
    ∧-false false = ≡.refl
    agree : ∀ y → y ≢ j → P y ≡ Q y
    agree y y≢j with oddᶻ (w ! y) in oy | rbit (w ! y) in ry
    ... | false | _ = ≡.refl
    ... | true | true = ≡.refl
    ... | true | false = ⊥-elim (others y y≢j oy (≡.trans ry (≡.sym rb)))
    PQ : count P ≡ suc (count Q)
    PQ = count-drop P Q j oj (≡.trans (≡.cong (oddᶻ (w ! j) ∧_) rb) (∧-false (oddᶻ (w ! j)))) agree
    oddsum : oddℕ (count P) ≡ true
    oddsum = ≡.trans (≡.cong oddℕ PQ) (≡.cong not (evenclass w normB))

------------------------------------------------------------------------
-- The pivot column: −e_m, e_m (m < p), or a first odd entry i₁ and the
-- next one i₂ in its class

data View (p : Fin n) : ℕ → Vec Z n → Set where
  neg  : ∀ {W} m → W ! m ≡ ZR.- ZR.1# → (∀ y → y ≢ m → W ! y ≡ ZR.0#) → View p 0 W
  pos  : ∀ {W} m → m < p → W ! m ≡ ZR.1# → (∀ y → y ≢ m → W ! y ≡ ZR.0#) → View p 0 W
  pair : ∀ {k′ W} i₁ i₂ → firstOdd W ≡ just i₁ → nextSame i₁ W ≡ just i₂ → i₁ < i₂ → i₂ ≤ p →
         View p (suc k′) W

------------------------------------------------------------------------
-- A state and its pivot column

module At (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (pv : pivot s ≡ just p) where

  v : Vec D n
  v = col s p

  k : ℕ
  k = lde v

  W : Vec Z n
  W = num v

  colW : col s p ≡ scV k W
  colW = lde-eq v

  min : Minimal k W
  min = lde-min v

  be : Beyond p s
  be = proj₂ (pivot-just s pv)

  ne : col s p ≢ col 𝕀 p
  ne = proj₁ (pivot-just s pv)

  lvl : levelᶜ s ≡ (suc (toℕ p) , k , third k W)
  lvl = levelᶜ-just s pv

  syl : sylᶜ s ≡ sylDataᶜ p k W
  syl = sylᶜ-just s pv

  -- Beyond p the pivot column vanishes, and it is a unit vector.
  zero> : ∀ x → p < x → W ! x ≡ ZR.0#
  zero> x lt = recompute (W ! x ≟ᶻ ZR.0#) (pivot-zero> o pv x lt)

  norm : Σℕ (λ x → NA (W ! x)) ≡ 2 ℕ.^ k
  norm = recompute (Σℕ (λ x → NA (W ! x)) ℕP.≟ 2 ℕ.^ k) (col-norm o p)

  normB : Σℤ (λ x → NB (W ! x)) ≡ ℤ.+ 0
  normB = recompute (Σℤ (λ x → NB (W ! x)) ℤP.≟ ℤ.+ 0) (col-normB o p)

  view : View p k W
  view = by k ≡.refl
    where
    by : ∀ K → k ≡ K → View p k W
    by zero eK = ≡.subst (λ K → View p K W) (≡.sym eK) (unit (lde0 W (≡.subst (λ K → Σℕ (λ x → NA (W ! x)) ≡ 2 ℕ.^ K) eK norm)))
      where
      unit : (∃ λ m → (W ! m ≡ ZR.1# ⊎ W ! m ≡ ZR.- ZR.1#) × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) → View p 0 W
      unit (m , inj₂ e , rest) = neg m e rest
      unit (m , inj₁ e , rest) = tri-elim (FinP.<-cmp m p) (λ m<p → pos m m<p e rest)
        (λ { ≡.refl → ⊥-elim (ne (≡.trans colW (≡.trans (≡.cong (λ K → scV K W) eK) (≡.trans (≡.cong (scV 0) We) (≡.sym (col𝕀≡ m)))))) })
        (λ p<m → ⊥-elim (one≢zero (≡.trans (≡.sym e) (zero> m p<m))))
        where
        one≢zero : ZR.1# ≢ ZR.0#
        one≢zero ()
        We : W ≡ eᶻ m
        We = vec-ext λ x → tri-elim (FinP.<-cmp x m)
          (λ x<m → ≡.trans (rest x (λ { ≡.refl → FinP.<-irrefl ≡.refl x<m })) (≡.sym (≡.trans (eᶻ-! m x) (eδ-≢ {x = x} {c = m} (λ { ≡.refl → FinP.<-irrefl ≡.refl x<m })))))
          (λ { ≡.refl → ≡.trans e (≡.sym (≡.trans (eᶻ-! x x) (eδ-refl x))) })
          (λ m<x → ≡.trans (rest x (λ { ≡.refl → FinP.<-irrefl ≡.refl m<x })) (≡.sym (≡.trans (eᶻ-! m x) (eδ-≢ {x = x} {c = m} (λ { ≡.refl → FinP.<-irrefl ≡.refl m<x })))))
    by (suc k′) eK = ≡.subst (λ K → View p K W) (≡.sym eK) (two (≡.subst (λ K → Minimal K W) eK min))
      where
      two : Minimal (suc k′) W → View p (suc k′) W
      two (inj₁ ())
      two (inj₂ (x , ox)) = first (firstOdd W) ≡.refl
        where
        first : (r : Maybe (Fin n)) → firstOdd W ≡ r → View p (suc k′) W
        first nothing fo = ⊥-elim (Odd⇒¬Even {W ! x} ox (firstOdd-nothing W fo x))
        first (just i₁) fo = next (nextSame i₁ W) ≡.refl
          where
          next : (r : Maybe (Fin n)) → nextSame i₁ W ≡ r → View p (suc k′) W
          next nothing nx = ⊥-elim (partner k′ W (≡.subst (λ K → Σℕ (λ x → NA (W ! x)) ≡ 2 ℕ.^ K) eK norm) normB fo nx)
          next (just i₂) nx = pair i₁ i₂ fo nx (proj₁ (nextSame-spec W nx))
                                (odd⇒≤ {p = p} {W} zero> (proj₁ (proj₁ (proj₂ (nextSame-spec W nx)))))

  ----------------------------------------------------------------------
  -- g · s, for g on indices ≤ p

  module Act (g : Gen n) (tg : top g ≤ p) where

    r : Matrix n n D
    r = actM g s

    be′ : Beyond p r
    be′ = Beyond-actM g {p} {s} tg be

    col-r : col r p ≡ actV g (col s p)
    col-r = col-actM g s p

    -- With its column p not that of I, r has pivot p, and its syllable
    -- and level come from a representation of that column.
    module Rep (K : ℕ) (W′ : Vec Z n) (eq : col r p ≡ scV K W′) (min′ : Minimal K W′) (ne′ : col r p ≢ col 𝕀 p) where

      pv′ : pivot r ≡ just p
      pv′ = pivot-char r ne′ be′

      syl′ : sylᶜ r ≡ sylDataᶜ p K W′
      syl′ = sylᶜ-of r pv′ K W′ eq min′

      lvl′ : levelᶜ r ≡ (suc (toℕ p) , K , third K W′)
      lvl′ = levelᶜ-of r pv′ K W′ eq min′

  -- The column of Z_[a] · s and of X_[a,b] · s.
  colZ : (a : Fin n) → col (actM (Z-gen a) s) p ≡ scV k (Zᶻ a W)
  colZ a = ≡.trans (col-actM (Z-gen a) s p) (≡.trans (≡.cong (actV (Z-gen a)) colW) (actV-Z a k W))

  colX : (a b : Fin n) .(ab : a < b) → col (actM (X-gen a b ab) s) p ≡ scV k (Xᶻ a b W)
  colX a b ab = ≡.trans (col-actM (X-gen a b ab) s p) (≡.trans (≡.cong (actV (X-gen a b ab)) colW) (actV-X a b ab k W))
