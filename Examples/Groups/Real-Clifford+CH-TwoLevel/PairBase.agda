------------------------------------------------------------------------
-- Presentations of groups
--
-- The states at a level L = (p + 1, k, ℓ) with k > 0, and their
-- valid pairs: two odd entries of the pivot column's numerator in the
-- same residue class.  H on a valid pair keeps the scale and makes
-- both entries even, so it goes down.
--
-- * The odd entries of each class are evenly many (Norm), so every
--   odd entry has a partner in its class; the canonical pair is the
--   first odd entry and the next one in its class, which Algorithm 1
--   removes (its syllable is H_[0,i₂] X_[0,i₁] = X_[0,i₁] H_[i₁,i₂]).
-- * canonical: the edge H on the canonical pair, from the normal
--   syllable and the edge X_[0,i₁] below L.
-- * square: the edges H on two disjoint valid pairs commute, so one
--   gives the other (a commuting square below L).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Product.Base using (_,_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction using (EdgesBelow)

module Examples.Groups.Real-Clifford+CH-TwoLevel.PairBase {n : ℕ} (p : Fin n) (k′ ℓ : ℕ)
  (ih : EdgesBelow {n} (suc (toℕ p) , suc k′ , ℓ)) where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _xor_ ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (_<_ ; _≤_)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (∃ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; dec-true ; dec-false ; recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (oddℕ ; oddℕ-+)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; oddᶻ ; rbit)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (scV ; lde ; num ; Odd ; Even)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count ; count-one ; count-lt)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Counting using (count-split ; search)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm using (evenodd ; evenclass ; 2ᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot
  using (pivot ; pivot-just ; Beyond ; Lvl ; lvlAt ; level ; level-just ; _<ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable using (syl ; Beyond-actM)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step using (same-class ; pairW ; H-action ; pairW-j ; pairW-ℓ ; pairW-≢)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Levels using (mono-level ; Bℓ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (flip-X ; comm-gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (Path ; Low)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PathTools {n} using (path-cong ; peel ; module Below)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (path-normal ; syl-of ; level-le ; bℓ-below)
import Examples.Groups.Real-Clifford+CH-TwoLevel.PivotColumn as PC

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid
open Below {L = suc (toℕ p) , suc k′ , ℓ} ih using (bridge)

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

  rc : ∀ {a b : Fin n} → .(a < b) → a < b
  rc {a} {b} lt = recompute (a FinP.<? b) lt

  true≢false : true ≢ false
  true≢false ()

k : ℕ
k = suc k′

L : Lvl
L = suc (toℕ p) , k , ℓ

------------------------------------------------------------------------
-- Lowness

-- A state agreeing with I beyond p, whose column p has a numerator at
-- scale k with fewer than ℓ odd entries, lies below L.
low : (N : Matrix n n D) → Beyond p N → (w : Vec Z n) → col N p ≡ scV k w → nodd w ℕ.< ℓ → level N <ₗ L
low N be w eq lt = level-le N be k w eq lt

-- (x + 1 , 0 , 1) lies below L for x ≤ p.
bℓ : ∀ {x} → x ≤ p → Bℓ x <ₗ L
bℓ x≤p = bℓ-below ℓ (s≤s z≤n) x≤p

-- X and Z on indices ≤ p keep a state below L.
X-low : ∀ {x y} .(xy : x < y) → y ≤ p → (N : Matrix n n D) → level N <ₗ L → level (actM (X-gen x y xy) N) <ₗ L
X-low {x} {y} xy y≤p N lt = mono-level (X-gen x y xy) tt FinP.≤-refl N lt (bℓ y≤p)

Z-low : ∀ {x} → x ≤ p → (N : Matrix n n D) → level N <ₗ L → level (actM (Z-gen x) N) <ₗ L
Z-low {x} x≤p N lt = mono-level (Z-gen x) tt FinP.≤-refl N lt (bℓ x≤p)

------------------------------------------------------------------------
-- Valid pairs, and H on them

Valid : Vec Z n → Fin n → Fin n → Set
Valid w i j = Odd (w ! i) × Odd (w ! j) × rbit (w ! i) ≡ rbit (w ! j)

record PairStep (N : Matrix n n D) (w : Vec Z n) (i j : Fin n) .(ij : i < j) : Set where
  field
    w′    : Vec Z n
    col′  : col (actM (H-gen i j ij) N) p ≡ scV k w′
    fewer : nodd w′ ℕ.< nodd w
    same  : ∀ x → x ≢ i → x ≢ j → w′ ! x ≡ w ! x
    ev-i  : Even (w′ ! i)
    ev-j  : Even (w′ ! j)

pair-step : (N : Matrix n n D) (w : Vec Z n) → col N p ≡ scV k w → ∀ i j .(ij : i < j) → Valid w i j → PairStep N w i j ij
pair-step N w eq i j ij (oi , oj , rb) = from (same-class (w ! i) (w ! j) oi oj rb)
  where
  i≢j : i ≢ j
  i≢j = <⇒≢ ij
  from : (∃ λ z → w ! i ≡ w ! j ZR.+ 2ᶻ ZR.* z) → PairStep N w i j ij
  from (z , ez) = record
    { w′ = pairW w i j z
    ; col′ = ≡.trans (col-actM (H-gen i j ij) N p) (≡.trans (≡.cong (actV (H-gen i j ij)) eq) (H-action k w i j ij z ez))
    ; fewer = count-lt (λ x → oddᶻ (w ! x)) (λ x → oddᶻ (pairW w i j z ! x)) i imp oi (pairW-j w i j z)
    ; same = λ x x≢i x≢j → pairW-≢ w i j z x x≢i x≢j
    ; ev-i = pairW-j w i j z
    ; ev-j = pairW-ℓ w i j z i≢j
    }
    where
    imp : ∀ x → oddᶻ (pairW w i j z ! x) ≡ true → oddᶻ (w ! x) ≡ true
    imp x ox = at (x FinP.≟ i) (x FinP.≟ j)
      where
      at : Dec (x ≡ i) → Dec (x ≡ j) → oddᶻ (w ! x) ≡ true
      at (yes ≡.refl) _ = ⊥-elim (true≢false (≡.trans (≡.sym ox) (pairW-j w i j z)))
      at (no _) (yes ≡.refl) = ⊥-elim (true≢false (≡.trans (≡.sym ox) (pairW-ℓ w i j z i≢j)))
      at (no x≢i) (no x≢j) = ≡.trans (≡.cong oddᶻ (≡.sym (pairW-≢ w i j z x x≢i x≢j))) ox

------------------------------------------------------------------------
-- A state at level L

module State (M : Matrix n n D) .(o : ColOrth M) (eq : level M ≡ L) where

  pv : pivot M ≡ just p
  pv = at (pivot M) ≡.refl
    where
    0≢suc : ∀ {m} → 0 ≢ suc m
    0≢suc ()
    at : (r : Maybe (Fin n)) → pivot M ≡ r → pivot M ≡ just p
    at nothing e = ⊥-elim (0≢suc (≡.cong proj₁ (≡.trans (≡.sym (≡.cong (λ r → lvlAt r M) e)) eq)))
    at (just p′) e =
      ≡.trans e (≡.cong just (FinP.toℕ-injective (ℕP.suc-injective (≡.cong proj₁ (≡.trans (≡.sym (level-just M e)) eq)))))

  open PC M o pv public using (W ; v ; v≡ ; syl≡ ; lvl ; zero> ; norm ; normB ; odd≤)
  open PC M o pv using (first)

  private
    lvl′ : (suc (toℕ p) , lde v , nodd W) ≡ L
    lvl′ = ≡.trans (≡.sym lvl) eq

  kM : lde v ≡ k
  kM = ≡.cong (λ x → proj₁ (proj₂ x)) lvl′

  ℓM : nodd W ≡ ℓ
  ℓM = ≡.cong (λ x → proj₂ (proj₂ x)) lvl′

  colM : col M p ≡ scV k W
  colM = ≡.trans v≡ (≡.cong (λ k → scV k W) kM)

  be : Beyond p M
  be = proj₂ (pivot-just M pv)

  ----------------------------------------------------------------------
  -- The residue classes of the odd entries have evenly many members

  Cls : Bool → Fin n → Bool
  Cls b x = oddᶻ (W ! x) ∧ (if b then rbit (W ! x) else not (rbit (W ! x)))

  even-odd : oddℕ (nodd W) ≡ false
  even-odd = evenodd k′ W (≡.trans norm (≡.cong (2 ℕ.^_) kM))

  cls-even : ∀ b → oddℕ (count (Cls b)) ≡ false
  cls-even true = evenclass W normB
  cls-even false =
    ≡.trans (≡.cong (_xor oddℕ c₀) (≡.sym (cls-even true)))
      (≡.trans (≡.sym (oddℕ-+ c₁ c₀)) (≡.trans (≡.cong oddℕ (≡.sym split)) even-odd))
    where
    c₁ = count (Cls true)
    c₀ = count (Cls false)
    split : nodd W ≡ c₁ ℕ.+ c₀
    split = count-split (λ x → oddᶻ (W ! x)) (λ x → rbit (W ! x))

  cls-true : ∀ x → Odd (W ! x) → Cls (rbit (W ! x)) x ≡ true
  cls-true x ox = go (oddᶻ (W ! x)) (rbit (W ! x)) ox
    where
    go : ∀ o r → o ≡ true → o ∧ (if r then r else not r) ≡ true
    go true true _ = ≡.refl
    go true false _ = ≡.refl

  cls-spec : ∀ b y → Cls b y ≡ true → Odd (W ! y) × rbit (W ! y) ≡ b
  cls-spec b y c = go b (oddᶻ (W ! y)) (rbit (W ! y)) c
    where
    go : ∀ b o r → o ∧ (if b then r else not r) ≡ true → o ≡ true × r ≡ b
    go true true true _ = ≡.refl , ≡.refl
    go false true false _ = ≡.refl , ≡.refl

  private
    does⇒≡ : ∀ {x y : Fin n} → does (x FinP.≟ y) ≡ true → x ≡ y
    does⇒≡ {x} {y} e = at (x FinP.≟ y) e
      where
      at : (d : Dec (x ≡ y)) → does d ≡ true → x ≡ y
      at (yes e) _ = e
      at (no _) ()

    does⇒≢ : ∀ {x y : Fin n} → does (x FinP.≟ y) ≡ false → x ≢ y
    does⇒≢ {x} {y} e = at (x FinP.≟ y) e
      where
      at : (d : Dec (x ≡ y)) → does d ≡ false → x ≢ y
      at (yes _) ()
      at (no ne) _ = ne

  -- Every odd entry has a partner in its class.
  partner : ∀ x → Odd (W ! x) → ∃ λ y → y ≢ x × Odd (W ! y) × rbit (W ! y) ≡ rbit (W ! x)
  partner x ox = from (search (Cls b) (λ y → does (y FinP.≟ x)))
    where
    b = rbit (W ! x)
    from : (∃ λ y → Cls b y ≡ true × does (y FinP.≟ x) ≡ false) ⊎ (∀ y → Cls b y ≡ true → does (y FinP.≟ x) ≡ true) →
           ∃ λ y → y ≢ x × Odd (W ! y) × rbit (W ! y) ≡ b
    from (inj₁ (y , cy , ne)) = y , does⇒≢ ne , cls-spec b y cy
    from (inj₂ all) = ⊥-elim (true≢false (≡.trans (≡.sym (≡.cong oddℕ one)) (cls-even b)))
      where
      off : ∀ y → y ≢ x → Cls b y ≡ false
      off y y≢x = at (Cls b y) ≡.refl
        where
        at : ∀ c → Cls b y ≡ c → Cls b y ≡ false
        at true e = ⊥-elim (y≢x (does⇒≡ (all y e)))
        at false e = e
      one : count (Cls b) ≡ 1
      one = count-one (Cls b) x (cls-true x ox) off

  ----------------------------------------------------------------------
  -- The canonical pair

  private
    F = first kM

  i₁ : Fin n
  i₁ = proj₁ F

  fo : firstOdd W ≡ just i₁
  fo = proj₂ F

  oi₁ : Odd (W ! i₁)
  oi₁ = proj₁ (firstOdd-spec W fo)

  -- Every odd entry is at or after i₁.
  odd-≥ : ∀ x → Odd (W ! x) → i₁ ≤ x
  odd-≥ x ox = ℕP.≮⇒≥ λ x<i₁ → true≢false (≡.trans (≡.sym ox) (proj₂ (firstOdd-spec W fo) x x<i₁))

  private
    NX : ∃ λ i₂ → nextSame i₁ W ≡ just i₂
    NX = at (nextSame i₁ W) ≡.refl
      where
      at : (r : Maybe (Fin n)) → nextSame i₁ W ≡ r → ∃ λ i₂ → nextSame i₁ W ≡ just i₂
      at (just j) e = j , e
      at nothing e = ⊥-elim (nextSame-nothing W e y i₁<y (oy , rb))
        where
        P = partner i₁ oi₁
        y = proj₁ P
        oy = proj₁ (proj₂ (proj₂ P))
        rb = proj₂ (proj₂ (proj₂ P))
        i₁<y : i₁ < y
        i₁<y = FinP.≤∧≢⇒< (odd-≥ y oy) (λ e → proj₁ (proj₂ P) (≡.sym e))

  i₂ : Fin n
  i₂ = proj₁ NX

  nx : nextSame i₁ W ≡ just i₂
  nx = proj₂ NX

  private
    spec = nextSame-spec W nx

  i₁<i₂ : i₁ < i₂
  i₁<i₂ = proj₁ spec

  -- No odd entry of i₁'s class lies strictly between i₁ and i₂.
  between : ∀ x → i₁ < x → x < i₂ → Odd (W ! x) → rbit (W ! x) ≢ rbit (W ! i₁)
  between x a b ox rb = proj₂ (proj₂ spec) x a b (ox , rb)

  valid₁₂ : Valid W i₁ i₂
  valid₁₂ = oi₁ , proj₁ (proj₁ (proj₂ spec)) , ≡.sym (proj₂ (proj₁ (proj₂ spec)))

  sylM : syl M ≡ pairSyl i₁ i₂ i₁<i₂
  sylM = ≡.trans syl≡ (≡.trans (≡.cong (λ k → sylData p k W) kM) (sylData-pair {p = p} k′ W fo nx i₁<i₂))

  ----------------------------------------------------------------------
  -- H on valid pairs

  stepM : ∀ i j .(ij : i < j) → Valid W i j → PairStep M W i j ij
  stepM i j ij vl = pair-step M W colM i j ij vl

  below : ∀ i j .(ij : i < j) → Valid W i j → level (actM (H-gen i j ij) M) <ₗ L
  below i j ij vl =
    low (actM (H-gen i j ij) M) (Beyond-actM (H-gen i j ij) {p} {M} (odd≤ (proj₁ (proj₂ vl))) be)
        (PairStep.w′ S) (PairStep.col′ S) (≡.subst (nodd (PairStep.w′ S) ℕ.<_) ℓM (PairStep.fewer S))
    where
    S = stepM i j ij vl

  -- Two disjoint valid pairs, one after the other.
  below₂ : ∀ i j .(ij : i < j) i′ j′ .(ij′ : i′ < j′) → Valid W i j → Valid W i′ j′ →
           i′ ≢ i → i′ ≢ j → j′ ≢ i → j′ ≢ j →
           level (actM (H-gen i′ j′ ij′) (actM (H-gen i j ij) M)) <ₗ L
  below₂ i j ij i′ j′ ij′ vl (oi′ , oj′ , rb′) a b c d =
    low N₂ (Beyond-actM (H-gen i′ j′ ij′) {p} {N₁} (odd≤ oj′) (Beyond-actM (H-gen i j ij) {p} {M} (odd≤ (proj₁ (proj₂ vl))) be))
        (PairStep.w′ S₂) (PairStep.col′ S₂)
        (≡.subst (nodd (PairStep.w′ S₂) ℕ.<_) ℓM (ℕP.<-trans (PairStep.fewer S₂) (PairStep.fewer S₁)))
    where
    S₁ = stepM i j ij vl
    N₁ = actM (H-gen i j ij) M
    N₂ = actM (H-gen i′ j′ ij′) N₁
    w₁ = PairStep.w′ S₁
    si′ : w₁ ! i′ ≡ W ! i′
    si′ = PairStep.same S₁ i′ a b
    sj′ : w₁ ! j′ ≡ W ! j′
    sj′ = PairStep.same S₁ j′ c d
    vl′ : Valid w₁ i′ j′
    vl′ = ≡.trans (≡.cong oddᶻ si′) oi′ , ≡.trans (≡.cong oddᶻ sj′) oj′ ,
          ≡.trans (≡.cong rbit si′) (≡.trans rb′ (≡.cong rbit (≡.sym sj′)))
    S₂ = pair-step N₁ w₁ (PairStep.col′ S₁) i′ j′ ij′ vl′

  ----------------------------------------------------------------------
  -- The canonical edge

  canonical : Path [ H-gen i₁ i₂ i₁<i₂ ]ʷ M o
  canonical = by (toℕ i₁ ℕP.≟ 0)
    where
    pN : Path (syl M) M o
    pN = path-normal M o pv
    by : Dec (toℕ i₁ ≡ 0) → Path [ H-gen i₁ i₂ i₁<i₂ ]ʷ M o
    by (yes z) = ≡.subst (λ w → Path w M o) (≡.trans sylM (pairSyl-0 i₁ i₂ i₁<i₂ z)) pN
    by (no nz) = peel (X z₀ i₁ 0<i₁) (H i₁ i₂ i₁<i₂) M o pXH pX
      where
      pos : 0 ℕ.< toℕ i₁
      pos = ℕP.n≢0⇒n>0 nz
      z₀ = zeroOf i₁
      0<i₁ : z₀ < i₁
      0<i₁ = zeroOf-< i₁ pos
      0<i₂ = ℕP.<-trans 0<i₁ i₁<i₂
      c4′ : H z₀ i₂ 0<i₂ • X z₀ i₁ 0<i₁ ≈ X z₀ i₁ 0<i₁ • H i₁ i₂ i₁<i₂
      c4′ = flip-X 0<i₁ (axiom (c4 0<i₁ i₁<i₂))
      pXH : Path (X z₀ i₁ 0<i₁ • H i₁ i₂ i₁<i₂) M o
      pXH = path-cong (trans (refl′ (≡.trans sylM (pairSyl-s i₁ i₂ i₁<i₂ pos))) c4′) M o pN
      HM = actM (H-gen i₁ i₂ i₁<i₂) M
      l₁ : level HM <ₗ L
      l₁ = below i₁ i₂ i₁<i₂ valid₁₂
      pX : Path (X z₀ i₁ 0<i₁) HM (ColOrth-actMʷ [ H-gen i₁ i₂ i₁<i₂ ]ʷ o)
      pX = ih (X-gen z₀ i₁ 0<i₁) HM (ColOrth-actMʷ [ H-gen i₁ i₂ i₁<i₂ ]ʷ o) l₁ (X-low 0<i₁ (odd≤ oi₁) HM l₁)

  ----------------------------------------------------------------------
  -- Squares

  square : ∀ i j .(ij : i < j) i′ j′ .(ij′ : i′ < j′) → Valid W i j → Valid W i′ j′ →
           i′ ≢ i → i′ ≢ j → j′ ≢ i → j′ ≢ j → Path [ H-gen i j ij ]ʷ M o → Path [ H-gen i′ j′ ij′ ]ʷ M o
  square i j ij i′ j′ ij′ vl vl′ a b c d pP =
    bridge (H-gen i′ j′ ij′) M o (H i j ij) (H i j ij) (H i′ j′ ij′) pP pP′ lowV rel
    where
    sym≢ : ∀ {x y : Fin n} → x ≢ y → y ≢ x
    sym≢ ne e = ne (≡.sym e)
    H′M = actM (H-gen i′ j′ ij′) M
    pP′ : Path (H i j ij) H′M (ColOrth-actMʷ [ H-gen i′ j′ ij′ ]ʷ o)
    pP′ = ih (H-gen i j ij) H′M (ColOrth-actMʷ [ H-gen i′ j′ ij′ ]ʷ o) (below i′ j′ ij′ vl′)
             (below₂ i′ j′ ij′ i j ij vl′ vl (sym≢ a) (sym≢ c) (sym≢ b) (sym≢ d))
    lowV : Low L (H i′ j′ ij′) (actMʷ (H i j ij) M)
    lowV = below i j ij vl , below₂ i j ij i′ j′ ij′ vl vl′ a b c d
    rel : H i′ j′ ij′ • H i j ij ≈ H i j ij • H i′ j′ ij′
    rel = comm-gen (H-gen i′ j′ ij′) (H-gen i j ij) ((a ∷ b ∷ []) ∷ (c ∷ d ∷ []) ∷ [])
