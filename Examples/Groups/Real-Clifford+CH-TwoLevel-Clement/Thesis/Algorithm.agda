------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément's real Giles–Selinger algorithm (Algorithm 1), its levels
-- (Definition 2.6), and its correctness (Theorem 2.7).
--
-- Let j be the pivot of M (the last column that is not e_j), v = M e_j,
-- and k the least denominator exponent of v.
--
-- * k = 0: v = ε e_l (Lemma 2.3).  The syllable is (-1)[l] if ε = −1,
--   and X[l,j] if ε = 1 (then l < j).
-- * k ≥ 1: l is the first odd entry of √2ᵏ v and m the next one in its
--   residue class modulo 2; the syllable is H[l,m].
--
-- Unlike Algorithm 1 of Hadamard-Pi (Real-Clifford+CH-TwoLevel.Column),
-- every syllable is a single generator.  The level of M is
-- (j + 1, k, m), with m the number of odd entries of √2ᵏ v, except that
-- for k = 0 it is the number of entries equal to −1, which is 1 for
-- v = −e_l and 0 for v = e_l; the identity has level (0, 0, 0).  Each
-- syllable lowers the level (Lemma 2.5): (-1)[l] makes v positive or
-- e_j, X[l,j] makes it e_j, and H[l,m] makes the entries l and m even.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Algorithm where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (+_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; ∃₂ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Vec.Base as Vec using (Vec)
open import Function.Base using (_∘_)
open import Induction.WellFounded using (Acc ; acc)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.Clifford+CS-TwoLevel.Search
  using (count ; count-one ; count-drop ; count-drop₂ ; count-false ; dec-elim ; tri-elim)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (D ; Z ; module ZR ; oddᶻ ; rbit ; oddℕ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde
  using (_!_ ; scV ; Odd ; Even ; Odd⇒¬Even ; Minimal ; lde ; num ; lde-eq ; lde-min ; lde-char ; lde-≤)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm
  using (NA ; NB ; Σℕ ; Σℤ ; evenodd ; evenclass ; lde0)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
  using ( nodd ; firstOdd ; nextSame ; negᶻ ; Same
        ; firstOdd-char ; firstOdd-spec ; firstOdd-nothing ; nextSame-spec ; nextSame-nothing )
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Zᶻ ; Xᶻ ; actV-Z ; actV-X)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot
  using (_≟ᵛ_ ; pivot ; pivot-just ; pivot-nothing ; pivot-below ; pivot-char ; Beyond ; Lvl ; _<ₗ_ ; _<₂_ ; _<ₗ?_ ; <ₗ-wellFounded)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable
  using (Within ; Beyond-actMʷ ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡ ; set₁-self)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step
  using (pivot-zero> ; col-norm ; col-normB ; odd⇒≤ ; same-class ; pairW ; H-action ; pairW-j ; pairW-ℓ ; pairW-≢ ; scV-injective)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Levels (Definition 2.6)

-- The number of entries equal to −1.
nneg : Vec Z n → ℕ
nneg w = count (λ x → negᶻ (w ! x))

-- The third component of a level, from the exponent and numerator.
third : ℕ → Vec Z n → ℕ
third zero    w = nneg w
third (suc _) w = nodd w

lvlAtᶜ : Maybe (Fin n) → Matrix n n D → Lvl
lvlAtᶜ nothing  M = 0 , 0 , 0
lvlAtᶜ (just p) M = suc (toℕ p) , lde (col M p) , third (lde (col M p)) (num (col M p))

levelᶜ : Matrix n n D → Lvl
levelᶜ M = lvlAtᶜ (pivot M) M

levelᶜ-just : (M : Matrix n n D) {p : Fin n} → pivot M ≡ just p →
              levelᶜ M ≡ (suc (toℕ p) , lde (col M p) , third (lde (col M p)) (num (col M p)))
levelᶜ-just M eq = cong (λ x → lvlAtᶜ x M) eq

-- A matrix that is the identity from column p on has level below any
-- level with pivot p.
levelᶜ-below : (M : Matrix n n D) {p : Fin n} → col M p ≡ col 𝕀 p → Beyond p M →
               ∀ k m → levelᶜ M <ₗ (suc (toℕ p) , k , m)
levelᶜ-below M {p} Mp be k m =
  [ (λ eq → subst (λ x → lvlAtᶜ x M <ₗ (suc (toℕ p) , k , m)) (sym eq) (inj₁ (ℕ.s≤s ℕ.z≤n)))
  , (λ { (p′ , eq , p′<p) → subst (λ x → lvlAtᶜ x M <ₗ (suc (toℕ p) , k , m)) (sym eq) (inj₁ (ℕ.s≤s p′<p)) }) ]′
  (pivot-below M Mp be)

-- With the same pivot, the level compares the exponent and the count.
levelᶜ-same : (M : Matrix n n D) {p : Fin n} → col M p ≢ col 𝕀 p → Beyond p M →
              ∀ {k m} → (lde (col M p) , third (lde (col M p)) (num (col M p))) <₂ (k , m) →
              levelᶜ M <ₗ (suc (toℕ p) , k , m)
levelᶜ-same M {p} ne be {k} {m} lt =
  subst (λ x → lvlAtᶜ x M <ₗ (suc (toℕ p) , k , m)) (sym (pivot-char M ne be)) (inj₂ (refl , lt))

------------------------------------------------------------------------
-- The syllables (Algorithm 1, step 3)

-- k = 0: the unit ε at index m, with ε = −1 iff τ.
unitSylᶜ : (p m : Fin n) → Bool → Dec (m < p) → Word (Gen n)
unitSylᶜ p m true  _         = Zʷ m
unitSylᶜ p m false (yes m<p) = X m p m<p
unitSylᶜ p m false (no _)    = ε

private
  unitStepᶜ : Fin n → Vec Z n → Maybe (Fin n) → Word (Gen n)
  unitStepᶜ p w (just m) = unitSylᶜ p m (negᶻ (w ! m)) (m FinP.<? p)
  unitStepᶜ p w nothing  = ε

  pairDecᶜ : (i₁ i₂ : Fin n) → Dec (i₁ < i₂) → Word (Gen n)
  pairDecᶜ i₁ i₂ (yes lt) = H i₁ i₂ lt
  pairDecᶜ i₁ i₂ (no _)   = ε

  pairStep₂ᶜ : Fin n → Maybe (Fin n) → Word (Gen n)
  pairStep₂ᶜ i₁ (just i₂) = pairDecᶜ i₁ i₂ (i₁ FinP.<? i₂)
  pairStep₂ᶜ i₁ nothing   = ε

  pairStepᶜ : Vec Z n → Maybe (Fin n) → Word (Gen n)
  pairStepᶜ w (just i₁) = pairStep₂ᶜ i₁ (nextSame i₁ w)
  pairStepᶜ w nothing   = ε

sylDataᶜ : Fin n → ℕ → Vec Z n → Word (Gen n)
sylDataᶜ p zero    w = unitStepᶜ p w (firstOdd w)
sylDataᶜ p (suc k) w = pairStepᶜ w (firstOdd w)

-- The syllable, from the facts that determine it.
sylDataᶜ-neg : ∀ {p m : Fin n} (w : Vec Z n) → firstOdd w ≡ just m → negᶻ (w ! m) ≡ true →
               sylDataᶜ p 0 w ≡ Zʷ m
sylDataᶜ-neg w fo ng rewrite fo | ng = refl

sylDataᶜ-pos : ∀ {p m : Fin n} (w : Vec Z n) → firstOdd w ≡ just m → negᶻ (w ! m) ≡ false →
               (m<p : m < p) → sylDataᶜ p 0 w ≡ X m p m<p
sylDataᶜ-pos {p = p} {m} w fo ng m<p rewrite fo | ng with m FinP.<? p
... | yes _ = refl
... | no ¬m<p = ⊥-elim (¬m<p m<p)

sylDataᶜ-pair : ∀ {p i₁ i₂ : Fin n} k (w : Vec Z n) → firstOdd w ≡ just i₁ → nextSame i₁ w ≡ just i₂ →
                (lt : i₁ < i₂) → sylDataᶜ p (suc k) w ≡ H i₁ i₂ lt
sylDataᶜ-pair {i₁ = i₁} {i₂} k w fo nx lt rewrite fo | nx with i₁ FinP.<? i₂
... | yes _ = refl
... | no ¬lt = ⊥-elim (¬lt lt)

sylAtᶜ : Maybe (Fin n) → Matrix n n D → Word (Gen n)
sylAtᶜ nothing  M = ε
sylAtᶜ (just p) M = sylDataᶜ p (lde (col M p)) (num (col M p))

sylᶜ : Matrix n n D → Word (Gen n)
sylᶜ M = sylAtᶜ (pivot M) M

sylᶜ-just : (M : Matrix n n D) {p : Fin n} → pivot M ≡ just p →
            sylᶜ M ≡ sylDataᶜ p (lde (col M p)) (num (col M p))
sylᶜ-just M eq = cong (λ x → sylAtᶜ x M) eq

sylᶜ-nothing : (M : Matrix n n D) → pivot M ≡ nothing → sylᶜ M ≡ ε
sylᶜ-nothing M eq = cong (λ x → sylAtᶜ x M) eq

-- Step 4: apply the syllable.
stepᶜ : Matrix n n D → Matrix n n D
stepᶜ M = actMʷ (sylᶜ M) M

------------------------------------------------------------------------
-- k ≥ 1: the first odd entry has a partner (Lemma 2.1)

-- The odd entries of each residue class are evenly many, so the first
-- odd entry is not alone in its class.
partner : ∀ k′ (w : Vec Z n) → Σℕ (λ x → NA (w ! x)) ≡ 2 ℕ.^ suc k′ → Σℤ (λ x → NB (w ! x)) ≡ + 0 →
          ∀ {j} → firstOdd w ≡ just j → nextSame j w ≡ nothing → ⊥
partner {n} k′ w norm normB {j} fo nx = by-class (rbit (w ! j)) refl
  where
  true≢false : true ≢ false
  true≢false ()
  oj : Odd (w ! j)
  oj = proj₁ (firstOdd-spec w fo)
  -- No other entry is odd in the class of j.
  others : ∀ y → y ≢ j → Odd (w ! y) → rbit (w ! y) ≢ rbit (w ! j)
  others y y≢j oy rb = tri-elim (FinP.<-cmp y j)
    (λ y<j → Odd⇒¬Even {w ! y} oy (proj₂ (firstOdd-spec w fo) y y<j))
    (λ y≡j → y≢j y≡j)
    (λ j<y → nextSame-nothing w nx y j<y (oy , rb))
  by-class : ∀ b → rbit (w ! j) ≡ b → ⊥
  -- Class 1 + √2: j is the only entry odd with rbit.
  by-class true rb = true≢false (trans (sym (cong oddℕ one)) (evenclass w normB))
    where
    P : Fin n → Bool
    P y = oddᶻ (w ! y) ∧ rbit (w ! y)
    Pj : P j ≡ true
    Pj = trans (cong₂ _∧_ oj rb) refl
    noP : ∀ y → y ≢ j → P y ≡ false
    noP y y≢j with oddᶻ (w ! y) in oy | rbit (w ! y) in ry
    ... | false | _ = refl
    ... | true | false = refl
    ... | true | true = ⊥-elim (others y y≢j oy (trans ry (sym rb)))
    one : count P ≡ 1
    one = count-one P j Pj noP
  -- Class 1: the odd entries other than j are all in class 1 + √2, an
  -- even number of them, so the total is odd.
  by-class false rb = true≢false (trans (sym oddsum) (evenodd k′ w norm))
    where
    P Q : Fin n → Bool
    P y = oddᶻ (w ! y)
    Q y = oddᶻ (w ! y) ∧ rbit (w ! y)
    ∧-false : ∀ b → b ∧ false ≡ false
    ∧-false true = refl
    ∧-false false = refl
    agree : ∀ y → y ≢ j → P y ≡ Q y
    agree y y≢j with oddᶻ (w ! y) in oy | rbit (w ! y) in ry
    ... | false | _ = refl
    ... | true | true = refl
    ... | true | false = ⊥-elim (others y y≢j oy (trans ry (sym rb)))
    PQ : count P ≡ suc (count Q)
    PQ = count-drop P Q j oj (trans (cong (oddᶻ (w ! j) ∧_) rb) (∧-false (oddᶻ (w ! j)))) agree
    oddsum : oddℕ (count P) ≡ true
    oddsum = trans (cong oddℕ PQ) (cong Data.Bool.Base.not (evenclass w normB))
      where import Data.Bool.Base

------------------------------------------------------------------------
-- Each syllable lowers the level (Lemma 2.5, Theorem 2.7)

private
  -- A vector that is 1 at m and 0 elsewhere is e_m.
  set₁-e : (m : Fin n) (w : Vec Z n) → (∀ y → y ≢ m → w ! y ≡ ZR.0#) → set₁ m ZR.1# w ≡ eᶻ m
  set₁-e m w rest = vec-ext λ x → dec-elim (x FinP.≟ m)
    (λ { refl → trans (set₁-a x ZR.1# w) (sym (trans (eᶻ-! x x) (eδ-refl x))) })
    (λ x≢m → trans (set₁-≢ m ZR.1# w x≢m) (trans (rest x x≢m) (sym (trans (eᶻ-! m x) (eδ-≢ x≢m)))))

  -- e_m swapped to p is e_p.
  Xᶻ-e : (m p : Fin n) → m ≢ p → Xᶻ m p (eᶻ m) ≡ eᶻ p
  Xᶻ-e m p m≢p = vec-ext λ x → dec-elim (x FinP.≟ m)
    (λ { refl → trans (set₂-a x p (eᶻ x ! p) (eᶻ x ! x) (eᶻ x))
                  (trans (eᶻ-! x p) (trans (eδ-≢ (m≢p ∘ sym)) (sym (trans (eᶻ-! p x) (eδ-≢ m≢p))))) })
    (λ x≢m → dec-elim (x FinP.≟ p)
      (λ { refl → trans (set₂-b m x (eᶻ m ! x) (eᶻ m ! m) (eᶻ m) m≢p)
                    (trans (eᶻ-! m m) (trans (eδ-refl m) (sym (trans (eᶻ-! x x) (eδ-refl x))))) })
      (λ x≢p → trans (set₂-≢ m p (eᶻ m ! p) (eᶻ m ! m) (eᶻ m) x≢m x≢p)
                 (trans (eᶻ-! m x) (trans (eδ-≢ x≢m) (sym (trans (eᶻ-! p x) (eδ-≢ x≢p)))))))

  nneg-e : (m : Fin n) → nneg (eᶻ m) ≡ 0
  nneg-e m = count-false _ λ x → dec-elim (x FinP.≟ m)
    (λ { refl → cong negᶻ (trans (eᶻ-! x x) (eδ-refl x)) })
    (λ x≢m → cong negᶻ (trans (eᶻ-! m x) (eδ-≢ x≢m)))

  e-≢ : (m p : Fin n) → m ≢ p → scV 0 (eᶻ m) ≢ col 𝕀 p
  e-≢ m p m≢p eq = one≢zero (trans (sym (eᶻ-at m)) (trans (cong (_! m) (scV-injective 0 (eᶻ m) (eᶻ p) (trans eq (col𝕀≡ p))))
                                                          (trans (eᶻ-! p m) (eδ-≢ m≢p))))
    where
    eᶻ-at : ∀ c → eᶻ c ! c ≡ ZR.1#
    eᶻ-at c = trans (eᶻ-! c c) (eδ-refl c)
    one≢zero : ZR.1# ≢ ZR.0#
    one≢zero ()

  cong-actVʷ : (u : Word (Gen n)) (x y : Vec D n) → x ≡ y → actVʷ u x ≡ actVʷ u y
  cong-actVʷ u x y refl = refl

  col-step : (M : Matrix n n D) (p : Fin n) (S : Word (Gen n)) (K : ℕ) (W : Vec Z n) →
             col M p ≡ scV K W → col (actMʷ S M) p ≡ actVʷ S (scV K W)
  col-step M p S K W eq = trans (col-actMʷ S M p) (cong-actVʷ S (col M p) (scV K W) eq)

-- k = 0.
lt-unit : (M : Matrix n n D) (p : Fin n) (W : Vec Z n) → Beyond p M → col M p ≡ scV 0 W → col M p ≢ col 𝕀 p →
          (∀ x → p < x → W ! x ≡ ZR.0#) → Σℕ (λ x → NA (W ! x)) ≡ 1 →
          Within p (sylDataᶜ p 0 W) × levelᶜ (actMʷ (sylDataᶜ p 0 W) M) <ₗ (suc (toℕ p) , 0 , nneg W)
lt-unit M p W be eq ne zero> norm = go (lde0 W norm)
  where
  go : (∃ λ m → (W ! m ≡ ZR.1# ⊎ W ! m ≡ ZR.- ZR.1#) × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) →
       Within p (sylDataᶜ p 0 W) × levelᶜ (actMʷ (sylDataᶜ p 0 W) M) <ₗ (suc (toℕ p) , 0 , nneg W)
  go (m , um , rest) = by um
    where
    odd-m : Odd (W ! m)
    odd-m = [ (λ e → cong oddᶻ e) , (λ e → cong oddᶻ e) ]′ um
    fo : firstOdd W ≡ just m
    fo = firstOdd-char W odd-m (λ x x<m → cong oddᶻ (rest x (λ { refl → ℕP.<-irrefl refl x<m })))
    m≤p : m ≤ p
    m≤p = odd⇒≤ {p = p} {W} zero> odd-m
    by : (W ! m ≡ ZR.1# ⊎ W ! m ≡ ZR.- ZR.1#) →
         Within p (sylDataᶜ p 0 W) × levelᶜ (actMʷ (sylDataᶜ p 0 W) M) <ₗ (suc (toℕ p) , 0 , nneg W)
    -- −e_m: (−1)[m] makes it e_m.
    by (inj₂ e) = subst (λ S → Within p S × levelᶜ (actMʷ S M) <ₗ (suc (toℕ p) , 0 , nneg W)) (sym syl≡) (m≤p , lt)
      where
      ng : negᶻ (W ! m) ≡ true
      ng = cong negᶻ e
      syl≡ : sylDataᶜ p 0 W ≡ Zʷ m
      syl≡ = sylDataᶜ-neg W fo ng
      ZW : Zᶻ m W ≡ eᶻ m
      ZW = trans (cong (λ z → set₁ m (ZR.- z) W) e) (set₁-e m W rest)
      col′ : col (actMʷ (Zʷ m) M) p ≡ scV 0 (eᶻ m)
      col′ = trans (col-step M p (Zʷ m) 0 W eq) (trans (actV-Z m 0 W) (cong (scV 0) ZW))
      be′ : Beyond p (actMʷ (Zʷ m) M)
      be′ = Beyond-actMʷ (Zʷ m) {p} {M} m≤p be
      one : nneg W ≡ 1
      one = count-one _ m ng (λ y y≢m → cong negᶻ (rest y y≢m))
      lt : levelᶜ (actMʷ (Zʷ m) M) <ₗ (suc (toℕ p) , 0 , nneg W)
      lt = dec-elim (m FinP.≟ p)
        (λ { refl → levelᶜ-below (actMʷ (Zʷ m) M) (trans col′ (sym (col𝕀≡ m))) be′ 0 (nneg W) })
        (λ m≢p → levelᶜ-same (actMʷ (Zʷ m) M) (λ e′ → e-≢ m p m≢p (trans (sym col′) e′)) be′
                   (subst (λ c → (lde c , third (lde c) (num c)) <₂ (0 , nneg W)) (sym col′)
                     (subst₂ (λ k u → (k , third k u) <₂ (0 , nneg W))
                       (sym (proj₁ (lde-char 0 (eᶻ m) refl (inj₁ refl))))
                       (sym (proj₂ (lde-char 0 (eᶻ m) refl (inj₁ refl))))
                       (inj₂ (refl , subst₂ ℕ._<_ (sym (nneg-e m)) (sym one) (ℕ.s≤s ℕ.z≤n))))))
    -- e_m with m < p: X[m,p] makes it e_p.
    by (inj₁ e) = tri-elim (FinP.<-cmp m p) case< (λ { refl → ⊥-elim (ne (trans eq (trans (cong (scV 0) We) (sym (col𝕀≡ m))))) })
                    (λ p<m → ⊥-elim (ℕP.<⇒≱ p<m m≤p))
      where
      We : W ≡ eᶻ m
      We = trans (sym (set₁-self m W)) (trans (cong (λ z → set₁ m z W) e) (set₁-e m W rest))
      case< : m < p → Within p (sylDataᶜ p 0 W) × levelᶜ (actMʷ (sylDataᶜ p 0 W) M) <ₗ (suc (toℕ p) , 0 , nneg W)
      case< m<p = subst (λ S → Within p S × levelᶜ (actMʷ S M) <ₗ (suc (toℕ p) , 0 , nneg W)) (sym syl≡)
                    (FinP.≤-refl , levelᶜ-below (actMʷ (X m p m<p) M) col≡ be′ 0 (nneg W))
        where
        syl≡ : sylDataᶜ p 0 W ≡ X m p m<p
        syl≡ = sylDataᶜ-pos W fo (cong negᶻ e) m<p
        col≡ : col (actMʷ (X m p m<p) M) p ≡ col 𝕀 p
        col≡ = trans (col-step M p (X m p m<p) 0 W eq)
                 (trans (actV-X m p m<p 0 W) (trans (cong (scV 0 ∘ Xᶻ m p) We) (trans (cong (scV 0) (Xᶻ-e m p (<⇒≢ m<p))) (sym (col𝕀≡ p)))))
        be′ : Beyond p (actMʷ (X m p m<p) M)
        be′ = Beyond-actMʷ (X m p m<p) {p} {M} FinP.≤-refl be

-- k ≥ 1.
lt-pair : (M : Matrix n n D) (p : Fin n) (K′ : ℕ) (W : Vec Z n) → Beyond p M → col M p ≡ scV (suc K′) W →
          Minimal (suc K′) W → (∀ x → p < x → W ! x ≡ ZR.0#) →
          Σℕ (λ x → NA (W ! x)) ≡ 2 ℕ.^ suc K′ → Σℤ (λ x → NB (W ! x)) ≡ + 0 →
          Within p (sylDataᶜ p (suc K′) W) × levelᶜ (actMʷ (sylDataᶜ p (suc K′) W) M) <ₗ (suc (toℕ p) , suc K′ , nodd W)
lt-pair M p K′ W be eq (inj₁ ()) zero> norm normB
lt-pair {n} M p K′ W be eq (inj₂ (x , ox)) zero> norm normB = withFirst (firstOdd W) refl
  where
  Goal = Within p (sylDataᶜ p (suc K′) W) × levelᶜ (actMʷ (sylDataᶜ p (suc K′) W) M) <ₗ (suc (toℕ p) , suc K′ , nodd W)
  withFirst : (r : Maybe (Fin n)) → firstOdd W ≡ r → Goal
  withFirst nothing fo = ⊥-elim (Odd⇒¬Even {W ! x} ox (firstOdd-nothing W fo x))
  withFirst (just i₁) fo = withNext (nextSame i₁ W) refl
    where
    withNext : (r : Maybe (Fin n)) → nextSame i₁ W ≡ r → Goal
    withNext nothing nx = ⊥-elim (partner K′ W norm normB fo nx)
    withNext (just i₂) nx = subst (λ S → Within p S × levelᶜ (actMʷ S M) <ₗ (suc (toℕ p) , suc K′ , nodd W)) (sym syl≡)
                              (i₂≤p , decide (col (actMʷ S M) p ≟ᵛ col 𝕀 p))
      where
      i₁<i₂ = proj₁ (nextSame-spec W nx)
      o₁ = proj₁ (firstOdd-spec W fo)
      sm = proj₁ (proj₂ (nextSame-spec W nx))
      i₂≤p : i₂ ≤ p
      i₂≤p = odd⇒≤ {p = p} {W} zero> (proj₁ sm)
      zc = same-class (W ! i₁) (W ! i₂) o₁ (proj₁ sm) (sym (proj₂ sm))
      z = proj₁ zc
      W′ = pairW W i₁ i₂ z
      S = H i₁ i₂ i₁<i₂
      syl≡ : sylDataᶜ p (suc K′) W ≡ S
      syl≡ = sylDataᶜ-pair {p = p} K′ W fo nx i₁<i₂
      cnt : nodd W ≡ suc (suc (nodd W′))
      cnt = count-drop₂ (λ x → oddᶻ (W ! x)) (λ x → oddᶻ (W′ ! x)) i₁ i₂ (<⇒≢ i₁<i₂) o₁ (proj₁ sm)
              (pairW-j W i₁ i₂ z) (pairW-ℓ W i₁ i₂ z (<⇒≢ i₁<i₂))
              (λ x x≢1 x≢2 → sym (cong oddᶻ (pairW-≢ W i₁ i₂ z x x≢1 x≢2)))
      be′ : Beyond p (actMʷ S M)
      be′ = Beyond-actMʷ S {p} {M} i₂≤p be
      col′ : col (actMʷ S M) p ≡ scV (suc K′) W′
      col′ = trans (col-step M p S (suc K′) W eq) (H-action (suc K′) W i₁ i₂ i₁<i₂ z (proj₂ zc))
      v = col (actMʷ S M) p
      same : lde v ≡ suc K′ → num v ≡ W′
      same e = scV-injective (suc K′) (num v) W′
        (trans (cong (λ k → scV k (num v)) (sym e)) (trans (sym (lde-eq v)) col′))
      lt₂ : (lde v , third (lde v) (num v)) <₂ (suc K′ , nodd W)
      lt₂ = [ inj₁
            , (λ e → inj₂ (e , subst (λ c → third c (num v) ℕ.< nodd W) (sym e)
                                 (subst (λ u → nodd u ℕ.< nodd W) (sym (same e))
                                   (subst (nodd W′ ℕ.<_) (sym cnt) (ℕ.s≤s (ℕP.n≤1+n (nodd W′))))))) ]′
            (ℕP.m≤n⇒m<n∨m≡n (lde-≤ (suc K′) W′ col′))
      decide : Dec (col (actMʷ S M) p ≡ col 𝕀 p) → levelᶜ (actMʷ S M) <ₗ (suc (toℕ p) , suc K′ , nodd W)
      decide (yes e) = levelᶜ-below (actMʷ S M) e be′ (suc K′) (nodd W)
      decide (no ne) = levelᶜ-same (actMʷ S M) ne be′ lt₂

-- The syllable acts on indices ≤ p, and the level drops.
step-ltᶜ : {M : Matrix n n D} → ColOrth M → ∀ {p} → pivot M ≡ just p →
           Within p (sylᶜ M) × levelᶜ (stepᶜ M) <ₗ levelᶜ M
step-ltᶜ {M = M} o {p} pv =
  subst₂ (λ S L → Within p S × levelᶜ (actMʷ S M) <ₗ L) (sym (sylᶜ-just M pv)) (sym (levelᶜ-just M pv))
    (by (lde v) refl)
  where
  v = col M p
  be = proj₂ (pivot-just M pv)
  ne = proj₁ (pivot-just M pv)
  by : ∀ K → lde v ≡ K → Within p (sylDataᶜ p (lde v) (num v)) ×
       levelᶜ (actMʷ (sylDataᶜ p (lde v) (num v)) M) <ₗ (suc (toℕ p) , lde v , third (lde v) (num v))
  by zero e rewrite e =
    lt-unit M p (num v) be (subst (λ k → v ≡ scV k (num v)) e (lde-eq v)) ne (pivot-zero> o pv)
      (subst (λ k → Σℕ (λ x → NA (num v ! x)) ≡ 2 ℕ.^ k) e (col-norm o p))
  by (suc K′) e rewrite e =
    lt-pair M p K′ (num v) be (subst (λ k → v ≡ scV k (num v)) e (lde-eq v))
      (subst (λ k → Minimal k (num v)) e (lde-min v)) (pivot-zero> o pv)
      (subst (λ k → Σℕ (λ x → NA (num v ! x)) ≡ 2 ℕ.^ k) e (col-norm o p)) (col-normB o p)

------------------------------------------------------------------------
-- The algorithm (Theorem 2.7)

-- One step preserves column-orthonormality.
ColOrth-stepᶜ : (M : Matrix n n D) → ColOrth M → ColOrth (stepᶜ M)
ColOrth-stepᶜ M o = ColOrth-actMʷ (sylᶜ M) o

private
  -- The level drops, as a proof recomputed from the decision, so that
  -- the proof of column-orthonormality may be irrelevant.
  lt : (M : Matrix n n D) → .(ColOrth M) → ∀ {p} → pivot M ≡ just p → levelᶜ (stepᶜ M) <ₗ levelᶜ M
  lt M o pv = recompute (levelᶜ (stepᶜ M) <ₗ? levelᶜ M) (proj₂ (step-ltᶜ o pv))

-- Given the pivot r of M.
synthAtᶜ : (M : Matrix n n D) → .(ColOrth M) → Acc _<ₗ_ (levelᶜ M) →
           (r : Maybe (Fin n)) → pivot M ≡ r → Word (Gen n)
synthAtᶜ M o a nothing pv = ε
synthAtᶜ M o (acc rs) (just p) pv =
  synthAtᶜ (stepᶜ M) (ColOrth-stepᶜ M o) (rs (lt M o pv)) (pivot (stepᶜ M)) refl • sylᶜ M

synthAtᶜ-correct : (M : Matrix n n D) .(o : ColOrth M) (a : Acc _<ₗ_ (levelᶜ M))
                   (r : Maybe (Fin n)) (pv : pivot M ≡ r) → actMʷ (synthAtᶜ M o a r pv) M ≡ 𝕀
synthAtᶜ-correct M o a nothing pv = pivot-nothing M pv
synthAtᶜ-correct M o (acc rs) (just p) pv =
  synthAtᶜ-correct (stepᶜ M) (ColOrth-stepᶜ M o) (rs (lt M o pv)) (pivot (stepᶜ M)) refl

synthAtᶜ-irr : (M : Matrix n n D) .(o : ColOrth M) (a a′ : Acc _<ₗ_ (levelᶜ M))
               (r : Maybe (Fin n)) (pv : pivot M ≡ r) → synthAtᶜ M o a r pv ≡ synthAtᶜ M o a′ r pv
synthAtᶜ-irr M o a a′ nothing pv = refl
synthAtᶜ-irr M o (acc rs) (acc rs′) (just p) pv =
  cong (_• sylᶜ M) (synthAtᶜ-irr (stepᶜ M) (ColOrth-stepᶜ M o) (rs (lt M o pv)) (rs′ (lt M o pv)) (pivot (stepᶜ M)) refl)

-- Opaque: comparing two normal words then compares the matrices, where
-- unfolding them would compare their accessibility proofs.
opaque
  synthᶜ : (M : Matrix n n D) → .(ColOrth M) → Word (Gen n)
  synthᶜ M o = synthAtᶜ M o (<ₗ-wellFounded (levelᶜ M)) (pivot M) refl

  -- Correctness: ⟦ synth M ⟧ M = I.
  synthᶜ-correct : (M : Matrix n n D) .(o : ColOrth M) → actMʷ (synthᶜ M o) M ≡ 𝕀
  synthᶜ-correct M o = synthAtᶜ-correct M o (<ₗ-wellFounded (levelᶜ M)) (pivot M) refl

  -- The identity's word is empty.
  synthᶜ-𝕀 : (M : Matrix n n D) .(o : ColOrth M) → pivot M ≡ nothing → synthᶜ M o ≡ ε
  synthᶜ-𝕀 M o pv = aux (pivot M) refl pv (<ₗ-wellFounded (levelᶜ M))
    where
    aux : (r : Maybe (Fin _)) (e : pivot M ≡ r) → r ≡ nothing → (a : Acc _<ₗ_ (levelᶜ M)) → synthAtᶜ M o a r e ≡ ε
    aux nothing e refl a = refl

  -- A normal edge M ⇒ step M, with syllable syl M.
  synthᶜ-step : (M : Matrix n n D) .(o : ColOrth M) {p : Fin n} → pivot M ≡ just p →
                synthᶜ M o ≡ synthᶜ (stepᶜ M) (ColOrth-stepᶜ M o) • sylᶜ M
  synthᶜ-step M o {p} pv = aux (pivot M) refl pv (<ₗ-wellFounded (levelᶜ M))
    where
    aux : (r : Maybe (Fin _)) (e : pivot M ≡ r) → r ≡ just p → (a : Acc _<ₗ_ (levelᶜ M)) →
          synthAtᶜ M o a r e ≡ synthᶜ (stepᶜ M) (ColOrth-stepᶜ M o) • sylᶜ M
    aux (just .p) e refl (acc rs) =
      cong (_• sylᶜ M) (synthAtᶜ-irr (stepᶜ M) (ColOrth-stepᶜ M o) (rs (lt M o e)) (<ₗ-wellFounded (levelᶜ (stepᶜ M)))
                                    (pivot (stepᶜ M)) refl)
