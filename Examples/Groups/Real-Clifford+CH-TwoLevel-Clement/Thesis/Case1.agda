------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 4.4, Case 1: G = X[j,j+1], at a state s of level L with pivot
-- p ≥ j + 1 (Subcase 1.1, j + 1 > p, raises the level).  N is the
-- syllable of s; that of r = G·s comes from Swap.
--
-- * Unit columns ±e_m:
--   - 1.2, −e_m with m ∉ {j, j+1}: (-1)[m] commutes with G (6);
--   - 1.5, 1.6, −e_j and −e_{j+1}: G conjugates (-1)[j] and (-1)[j+1]
--     ((10), (11));
--   - 1.3.1, e_m with m ∉ {j, j+1}, p ≠ j+1: X[m,p] commutes with G (9);
--   - 1.3.2, the same with p = j+1: X[m,j] completes it (12);
--   - 1.7, e_j with p = j+1: G is the syllable (prograde);
--   - 1.8, 1.9, e_j (p > j+1) and e_{j+1}: G conjugates X[j,p] and
--     X[j+1,p] (12).
-- * k > 0, N = H[i₁,i₂]:
--   - 1.4, i₁, i₂ ∉ {j, j+1}: N commutes with G (8);
--   - 1.10, (i₁, i₂) = (j, j+1): (-1)[j+1] completes it (18);
--   - 1.11.1, 1.12, 1.13, 1.14.1: G conjugates N into the syllable of r
--     ((14), (15));
--   - 1.11.2, i₁ = j, entry j+1 odd of the other class, b the next in
--     its class: H[j+1,b] G H[j+1,i₂] from H[j,b]·r (Equations.sq1112),
--     whose states lie below L as H on two odd entries of one class
--     makes them even;
--   - 1.14.2, i₂ = j and entry j+1 in the class of i₁: a hypothesis
--     here (Hyp1142), proved in Case1142.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (Lvl)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction as TR

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case1 {n : ℕ} {L : Lvl} (ih : TR.EdgesBelow {n} L) where

open import Data.Bool.Base using (true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (_×-dec_)
import Data.Bool.Properties as BoolP
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; oddᶻ ; rbit)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (_!_ ; scV ; Minimal ; Odd ; Even ; Odd⇒¬Even ; lde ; num)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm using (NA ; Σℕ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
  using (nodd ; firstOdd ; nextSame ; negᶻ ; Same ; firstOdd-char ; firstOdd-spec ; nextSame-spec)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Xᶻ ; actV-X)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; _<ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable using (eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; Beyond-actM)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Levels using (Minimal-X ; nodd-X)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step using (odd⇒≤)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (sound-act ; _≤ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (ne-𝕀 ; ne-𝕀-at)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Algorithm
  using (levelᶜ ; sylᶜ ; sylDataᶜ ; sylDataᶜ-neg ; sylDataᶜ-pos ; sylDataᶜ-pair ; third)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Squares {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.State {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Equations {n}
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Swap as Swap

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid
open Close ih

private
  sym≢ : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
  sym≢ ne e = ne (≡.sym e)

  <-≢ : ∀ {x y : Fin n} → x < y → x ≢ y
  <-≢ lt ≡.refl = FinP.<-irrefl ≡.refl lt

  X-≡ : ∀ {a b a′ b′ : Fin n} .{ab : a < b} .{ab′ : a′ < b′} → a ≡ a′ → b ≡ b′ → X a b ab ≡ X a′ b′ ab′
  X-≡ ≡.refl ≡.refl = ≡.refl

  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

  -- A vector that is u at x and 0 elsewhere, u odd: x is its first odd
  -- entry.
  unit-first : (w : Vec Z n) (x : Fin n) → Odd (w ! x) → (∀ y → y ≢ x → w ! y ≡ ZR.0#) → firstOdd w ≡ just x
  unit-first w x ox rest = firstOdd-char w ox (λ y y<x → ≡.cong oddᶻ (rest y (<-≢ y<x)))

  -- −1 is not an entry of e_p.
  neg≢e : (p x : Fin n) → ZR.- ZR.1# ≢ eᶻ p ! x
  neg≢e p x e = dec-elim (x FinP.≟ p)
    (λ { ≡.refl → c₁ (≡.trans e (≡.trans (eᶻ-! x x) (eδ-refl x))) })
    (λ x≢p → c₀ (≡.trans e (≡.trans (eᶻ-! p x) (eδ-≢ x≢p))))
    where
    c₁ : ZR.- ZR.1# ≢ ZR.1#
    c₁ ()
    c₀ : ZR.- ZR.1# ≢ ZR.0#
    c₀ ()

  -- 1 is not the entry x ≠ p of e_p.
  one≢e : (p x : Fin n) → x ≢ p → ZR.1# ≢ eᶻ p ! x
  one≢e p x x≢p e = c₀ (≡.trans e (≡.trans (eᶻ-! p x) (eδ-≢ x≢p)))
    where
    c₀ : ZR.1# ≢ ZR.0#
    c₀ ()

------------------------------------------------------------------------
-- Subcase 1.14.2, left to Case1142

Hyp1142 : Set
Hyp1142 = ∀ (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (pv : pivot s ≡ just p) → levelᶜ s ≡ L →
          ∀ {j j′ : Fin n} (adj : toℕ j′ ≡ suc (toℕ j)) → j′ ≤ p →
          levelᶜ (actM (X-gen j j′ (Swap.jj′ adj)) s) ≤ₗ L →
          ∀ k′ → lde (col s p) ≡ suc k′ → ∀ {i₁} → firstOdd (num (col s p)) ≡ just i₁ →
          nextSame i₁ (num (col s p)) ≡ just j → Same (num (col s p)) i₁ j′ →
          Path [ X-gen j j′ (Swap.jj′ adj) ]ʷ s o

------------------------------------------------------------------------
-- The edge X[j,j+1] out of s

module Edge (h1142 : Hyp1142) (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (pv : pivot s ≡ just p) (eqL : levelᶜ s ≡ L)
            {j j′ : Fin n} (adj : toℕ j′ ≡ suc (toℕ j)) (j′≤p : j′ ≤ p)
            (le : levelᶜ (actM (X-gen j j′ (Swap.jj′ adj)) s) ≤ₗ L) where

  open Swap adj
  open At s o pv

  G : Gen n
  G = X-gen j j′ jj′

  Xj = X j j′ jj′

  open Act G j′≤p

  j<p : j < p
  j<p = ℕP.<-≤-trans jj′ j′≤p

  -- The normal steps out of s and r land below L.
  below-s : (h : Word (Gen n)) → sylᶜ s ≡ h → levelᶜ (actMʷ h s) <ₗ L
  below-s h e = ≡.subst (λ w → levelᶜ (actMʷ w s) <ₗ L) e (normal-below s o pv (inj₂ eqL))

  below-r : pivot r ≡ just p → (h : Word (Gen n)) → sylᶜ r ≡ h → levelᶜ (actMʷ h r) <ₗ L
  below-r pv′ h e = ≡.subst (λ w → levelᶜ (actMʷ w r) <ₗ L) e (normal-below r (ColOrth-actMʷ Xj o) pv′ le)

  -- The end of a relation W • N′ • G ≈ N lies below L.
  end-below : ∀ {Wd N′ N} → Wd • N′ • Xj ≈ N → sylᶜ s ≡ N → levelᶜ (actMʷ Wd (actMʷ N′ r)) <ₗ L
  end-below {Wd} {N′} {N} rel e = ≡.subst (λ M → levelᶜ M <ₗ L) (≡.sym (sound-act rel s)) (below-s N e)

  W′ : Vec Z n
  W′ = Xᶻ j j′ W

  ----------------------------------------------------------------------
  -- Unit columns

  module Unit (eK : k ≡ 0) where

    colW₀ : col s p ≡ scV 0 W
    colW₀ = ≡.trans colW (≡.cong (λ K → scV K W) eK)

    colr : col r p ≡ scV 0 W′
    colr = ≡.trans (colX j j′ jj′) (≡.cong (λ K → scV K W′) eK)

    -- When the unit is away from j and j′, r has the column of s.
    same-col : ∀ {m} → (∀ y → y ≢ m → W ! y ≡ ZR.0#) → m ≢ j → m ≢ j′ → col r p ≡ scV 0 W
    same-col rest m≢j m≢j′ = ≡.trans colr (≡.cong (scV 0) (Xᶻ-00 j j′ W j≢j′ (rest j (sym≢ m≢j)) (rest j′ (sym≢ m≢j′))))

    -- When it is at j (at j′), it moves to j′ (to j).
    from-j : ∀ {m} → (∀ y → y ≢ m → W ! y ≡ ZR.0#) → m ≡ j → W′ ! j′ ≡ W ! m × (∀ y → y ≢ j′ → W′ ! y ≡ ZR.0#)
    from-j {m} rest m≡j =
      ≡.trans (sw-j′ W) (≡.cong (W !_) (≡.sym m≡j)) ,
      λ y y≢j′ → dec-elim (y FinP.≟ j)
        (λ { ≡.refl → ≡.trans (sw-j W) (rest j′ (λ e → j≢j′ (≡.trans (≡.sym m≡j) (≡.sym e)))) })
        (λ y≢j → ≡.trans (sw-o W y≢j y≢j′) (rest y (λ e → y≢j (≡.trans e m≡j))))

    from-j′ : ∀ {m} → (∀ y → y ≢ m → W ! y ≡ ZR.0#) → m ≡ j′ → W′ ! j ≡ W ! m × (∀ y → y ≢ j → W′ ! y ≡ ZR.0#)
    from-j′ {m} rest m≡j′ =
      ≡.trans (sw-j W) (≡.cong (W !_) (≡.sym m≡j′)) ,
      λ y y≢j → dec-elim (y FinP.≟ j′)
        (λ { ≡.refl → ≡.trans (sw-j′ W) (rest j (λ e → j≢j′ (≡.trans e m≡j′))) })
        (λ y≢j′ → ≡.trans (sw-o W y≢j y≢j′) (rest y (λ e → y≢j′ (≡.trans e m≡j′))))

  ----------------------------------------------------------------------
  -- k > 0

  -- Is entry x odd and in the class of entry i?
  same? : ∀ i x → Dec (Same W i x)
  same? i x = (oddᶻ (W ! x) BoolP.≟ true) ×-dec (rbit (W ! x) BoolP.≟ rbit (W ! i))

  module Pair (k′ : ℕ) (eK : k ≡ suc k′) where

    colr : col r p ≡ scV (suc k′) W′
    colr = ≡.trans (colX j j′ jj′) (≡.cong (λ K → scV K W′) eK)

    min′ : Minimal (suc k′) W′
    min′ = Minimal-X j j′ j≢j′ W (≡.subst (λ K → Minimal K W) eK min)

    module Rr = Rep (suc k′) W′ colr min′ (ne-𝕀 r p k′ W′ colr min′)

    -- L, with its exponent.
    L≡ : L ≡ (suc (toℕ p) , suc k′ , nodd W)
    L≡ = ≡.trans (≡.sym eqL) (≡.trans lvl (≡.cong (λ K → suc (toℕ p) , K , third K W) eK))

    sylN-of : ∀ {a b} (ab : a < b) → firstOdd W ≡ just a → nextSame a W ≡ just b → sylᶜ s ≡ H a b ab
    sylN-of ab fo nx = ≡.trans syl (≡.trans (≡.cong (λ K → sylDataᶜ p K W) eK) (sylDataᶜ-pair {p = p} k′ W fo nx ab))

    sylR-of : ∀ {a b} (ab : a < b) → firstOdd W′ ≡ just a → nextSame a W′ ≡ just b → sylᶜ r ≡ H a b ab
    sylR-of ab fo′ nx′ = ≡.trans Rr.syl′ (sylDataᶜ-pair {p = p} k′ W′ fo′ nx′ ab)

    pr-s : ∀ {a b} (ab : a < b) → sylᶜ s ≡ H a b ab → Path (H a b ab) s o
    pr-s ab e = prograde (H-gen _ _ ab) s o pv e

    pr-r : ∀ {a b} (ab : a < b) → sylᶜ r ≡ H a b ab → Path (H a b ab) r (ColOrth-actMʷ Xj o)
    pr-r ab e = prograde (H-gen _ _ ab) r (ColOrth-actMʷ Xj o) Rr.pv′ e

    -- A square completed by one generator g from N′·r to N·s.
    by-one : ∀ {a b c d} (ab : a < b) (cd : c < d) (g : Gen n) →
             sylᶜ s ≡ H a b ab → sylᶜ r ≡ H c d cd → [ g ]ʷ • H c d cd • Xj ≈ H a b ab → Path [ G ]ʷ s o
    by-one ab cd g eN eN′ rel = close G s o (H _ _ ab) (H _ _ cd) [ g ]ʷ (pr-s ab eN) (pr-r cd eN′)
                                  (below-r Rr.pv′ (H _ _ cd) eN′ , end-below rel eN) rel

    -- 1.4
    c14 : ∀ {i₁ i₂} → firstOdd W ≡ just i₁ → nextSame i₁ W ≡ just i₂ → (lt : i₁ < i₂) →
          i₁ ≢ j → i₁ ≢ j′ → i₂ ≢ j → i₂ ≢ j′ → Path [ G ]ʷ s o
    c14 fo nx lt i₁≢j i₁≢j′ i₂≢j i₂≢j′ =
      commute G (H-gen _ _ lt) ((i₁≢j ∷ i₁≢j′ ∷ []) ∷ (i₂≢j ∷ i₂≢j′ ∷ []) ∷ []) s o (pr-s lt eN) (pr-r lt eN′)
        (below-r Rr.pv′ (H _ _ lt) eN′) (below-s (H _ _ lt) eN)
      where
      eN = sylN-of lt fo nx
      eN′ = sylR-of lt (fo-out W fo i₁≢j i₁≢j′) (ns-out W nx i₁≢j i₁≢j′ i₂≢j i₂≢j′)

    -- 1.10
    c110 : firstOdd W ≡ just j → nextSame j W ≡ just j′ → Path [ G ]ʷ s o
    c110 fo nx = by-one jj′ jj′ (Z-gen j′) eN eN′ (ZHX jj′)
      where
      oj = proj₁ (firstOdd-spec W fo)
      oj′ = proj₁ (proj₁ (proj₂ (nextSame-spec W nx)))
      eN = sylN-of jj′ fo nx
      eN′ = sylR-of jj′ (fo-jj W fo oj′) (ns-jj W oj nx)

    -- 1.11.1
    c1111 : firstOdd W ≡ just j → ∀ {i₂} → nextSame j W ≡ just i₂ → (j′<i₂ : j′ < i₂) → Even (W ! j′) → Path [ G ]ʷ s o
    c1111 fo nx j′<i₂ ev = by-one (proj₁ (nextSame-spec W nx)) j′<i₂ G eN eN′ (XHbcX jj′ j′<i₂)
      where
      eN = sylN-of (proj₁ (nextSame-spec W nx)) fo nx
      eN′ = sylR-of j′<i₂ (fo-to-j′ W fo ev) (ns-to-j′ W nx j′<i₂)

    -- 1.12
    c112 : firstOdd W ≡ just j′ → ∀ {i₂} → nextSame j′ W ≡ just i₂ → Path [ G ]ʷ s o
    c112 fo nx = by-one j′<i₂ (gt-j′ j′<i₂) G eN eN′ (XHacX jj′ j′<i₂)
      where
      j′<i₂ = proj₁ (nextSame-spec W nx)
      ¬s : ¬ Same W j′ j
      ¬s (oj , _) = Odd⇒¬Even {W ! j} oj (proj₂ (firstOdd-spec W fo) j jj′)
      eN = sylN-of j′<i₂ fo nx
      eN′ = sylR-of (gt-j′ j′<i₂) (fo-from-j′ W fo) (ns-from-j′ W ¬s nx)

    -- 1.13
    c113 : ∀ {i₁} → firstOdd W ≡ just i₁ → nextSame i₁ W ≡ just j′ → i₁ ≢ j → i₁ ≢ j′ → Path [ G ]ʷ s o
    c113 fo nx i₁≢j i₁≢j′ = by-one (proj₁ (nextSame-spec W nx)) i₁<j G eN eN′ (XHabX i₁<j jj′)
      where
      i₁<j = lt-j′ i₁≢j (proj₁ (nextSame-spec W nx))
      eN = sylN-of (proj₁ (nextSame-spec W nx)) fo nx
      eN′ = sylR-of i₁<j (fo-out W fo i₁≢j i₁≢j′) (ns-to-j W nx i₁<j)

    -- 1.14.1
    c1141 : ∀ {i₁} → firstOdd W ≡ just i₁ → nextSame i₁ W ≡ just j → i₁ ≢ j → i₁ ≢ j′ → ¬ Same W i₁ j′ → Path [ G ]ʷ s o
    c1141 fo nx i₁≢j i₁≢j′ ¬s = by-one i₁<j (lt-j i₁<j) G eN eN′ (XHacX′ i₁<j jj′)
      where
      i₁<j = proj₁ (nextSame-spec W nx)
      eN = sylN-of i₁<j fo nx
      eN′ = sylR-of (lt-j i₁<j) (fo-out W fo i₁≢j i₁≢j′) (ns-j-to-j′ W nx ¬s)

    -- 1.14.2
    c1142 : ∀ {i₁} → firstOdd W ≡ just i₁ → nextSame i₁ W ≡ just j → Same W i₁ j′ → Path [ G ]ʷ s o
    c1142 fo nx sm = h1142 s o pv eqL adj j′≤p le k′ eK fo nx sm

    -- 1.11.2
    c1112 : firstOdd W ≡ just j → ∀ {i₂} → nextSame j W ≡ just i₂ → j′ < i₂ → Odd (W ! j′) → Path [ G ]ʷ s o
    c1112 fo {i₂} nx j′<i₂ oj′ = with-b (nextSame j′ W) ≡.refl
      where
      j<i₂ = proj₁ (nextSame-spec W nx)
      oj = proj₁ (firstOdd-spec W fo)
      sj = proj₁ (proj₂ (nextSame-spec W nx))
      -- Entry j′ is not in the class of j.
      ¬s : ¬ Same W j′ j
      ¬s (_ , rb) = proj₂ (proj₂ (nextSame-spec W nx)) j′ jj′ j′<i₂ (oj′ , ≡.sym rb)
      with-b : (m : Maybe (Fin n)) → nextSame j′ W ≡ m → Path [ G ]ʷ s o
      with-b nothing nxb = ⊥-elim (partner′ k′ W norm₁ normB oj′ before nxb)
        where
        norm₁ = ≡.subst (λ K → Σℕ (λ x → NA (W ! x)) ≡ 2 ℕ.^ K) eK norm
        before : ∀ y → y < j′ → ¬ Same W j′ y
        before y y<j′ sy = dec-elim (y FinP.≟ j)
          (λ y≡j → ¬s (≡.subst (Same W j′) y≡j sy))
          (λ y≢j → Odd⇒¬Even {W ! y} (proj₁ sy) (proj₂ (firstOdd-spec W fo) y (lt-j′ y≢j y<j′)))
      with-b (just b) nxb = close G s o (H j i₂ j<i₂) (H j b jb) Wd (pr-s j<i₂ eN) (pr-r jb eN′) low rel
        where
        spb = nextSame-spec W nxb
        j′<b = proj₁ spb
        jb : j < b
        jb = gt-j′ j′<b
        sb = proj₁ (proj₂ spb)
        i₂≢b : i₂ ≢ b
        i₂≢b e = ¬s (oj , ≡.trans (≡.sym (proj₂ sj)) (≡.trans (≡.cong (λ x → rbit (W ! x)) e) (proj₂ sb)))
        b≢j = sym≢ (<-≢ jb)
        b≢j′ = sym≢ (<-≢ j′<b)
        i₂≢j = sym≢ (<-≢ j<i₂)
        i₂≢j′ = sym≢ (<-≢ j′<i₂)
        eN = sylN-of j<i₂ fo nx
        eN′ = sylR-of jb (fo-jj W fo oj′) (ns-from-j′ W ¬s nxb)
        Wd = H j′ b j′<b • Xj • H j′ i₂ j′<i₂
        rel : Wd • H j b jb • Xj ≈ H j i₂ j<i₂
        rel = sq1112 jj′ j′<i₂ j′<b i₂≢b
        -- The states along Wd: H[j,b] and H[j′,i₂] pair odd entries of
        -- one class, and X keeps the count.
        b≤p = odd⇒≤ {p = p} {W} zero> (proj₁ sb)
        i₂≤p = odd⇒≤ {p = p} {W} zero> (proj₁ sj)
        r₁ = actM (H-gen j b jb) r
        vs₁ = valid-step r p (suc k′) W′ colr j b jb
                (≡.trans (≡.cong oddᶻ (sw-j W)) oj′) (≡.trans (≡.cong oddᶻ (sw-o W b≢j b≢j′)) (proj₁ sb))
                (≡.trans (≡.cong rbit (sw-j W)) (≡.trans (≡.sym (proj₂ sb)) (≡.sym (≡.cong rbit (sw-o W b≢j b≢j′)))))
        w₁ = proj₁ vs₁
        col₁ = proj₁ (proj₂ vs₁)
        keep₁ = proj₁ (proj₂ (proj₂ (proj₂ vs₁)))
        e₁j′ : w₁ ! j′ ≡ W ! j
        e₁j′ = ≡.trans (keep₁ j′ (sym≢ j≢j′) (sym≢ b≢j′)) (sw-j′ W)
        e₁i₂ : w₁ ! i₂ ≡ W ! i₂
        e₁i₂ = ≡.trans (keep₁ i₂ i₂≢j i₂≢b) (sw-o W i₂≢j i₂≢j′)
        r₂ = actM (H-gen j′ i₂ j′<i₂) r₁
        vs₂ = valid-step r₁ p (suc k′) w₁ col₁ j′ i₂ j′<i₂
                (≡.trans (≡.cong oddᶻ e₁j′) oj) (≡.trans (≡.cong oddᶻ e₁i₂) (proj₁ sj))
                (≡.trans (≡.cong rbit e₁j′) (≡.trans (≡.sym (proj₂ sj)) (≡.sym (≡.cong rbit e₁i₂))))
        w₂ = proj₁ vs₂
        col₂ = proj₁ (proj₂ vs₂)
        cnt : nodd W ≡ suc (suc (suc (suc (nodd w₂))))
        cnt = ≡.trans (≡.sym (nodd-X j j′ j≢j′ W))
                (≡.trans (proj₁ (proj₂ (proj₂ vs₁))) (≡.cong (λ c → suc (suc c)) (proj₁ (proj₂ (proj₂ vs₂)))))
        fewer : nodd w₂ ℕ.< nodd W
        fewer = ≡.subst (nodd w₂ ℕ.<_) (≡.sym cnt)
                  (ℕP.≤-trans (ℕP.n≤1+n (suc (nodd w₂))) (ℕP.≤-trans (ℕP.n≤1+n (suc (suc (nodd w₂)))) (ℕP.n≤1+n (suc (suc (suc (nodd w₂)))))))
        be₁ = Beyond-actM (H-gen j b jb) {p} {r} b≤p be′
        be₂ = Beyond-actM (H-gen j′ i₂ j′<i₂) {p} {r₁} i₂≤p be₁
        col₃ : col (actM G r₂) p ≡ scV (suc k′) (Xᶻ j j′ w₂)
        col₃ = ≡.trans (col-actM G r₂ p) (≡.trans (≡.cong (actV G) col₂) (actV-X j j′ jj′ (suc k′) w₂))
        l₂ : levelᶜ r₂ <ₗ L
        l₂ = ≡.subst (levelᶜ r₂ <ₗ_) (≡.sym L≡) (lowᶜ r₂ be₂ k′ w₂ col₂ fewer)
        l₃ : levelᶜ (actM G r₂) <ₗ L
        l₃ = ≡.subst (levelᶜ (actM G r₂) <ₗ_) (≡.sym L≡)
               (lowᶜ (actM G r₂) (Beyond-actM G {p} {r₂} j′≤p be₂) k′ (Xᶻ j j′ w₂) col₃
                 (≡.subst (ℕ._< nodd W) (≡.sym (nodd-X j j′ j≢j′ w₂)) fewer))
        l₁ : levelᶜ r₁ <ₗ L
        l₁ = below-r Rr.pv′ (H j b jb) eN′
        low : Low L Wd r₁
        low = ((l₁ , l₂) , (l₂ , l₃)) , (l₃ , end-below rel eN)

  ----------------------------------------------------------------------
  -- The case analysis

  case1 : Path [ G ]ʷ s o
  case1 = by view ≡.refl
    where
    by : ∀ {K} → View p K W → k ≡ K → Path [ G ]ʷ s o

    -- −e_m: N = (-1)[m]
    by (neg m e rest) eK = dec-elim (m FinP.≟ j) at-j (λ m≢j → dec-elim (m FinP.≟ j′) at-j′ (apart m≢j))
      where
      open Unit eK
      fo : firstOdd W ≡ just m
      fo = unit-first W m (≡.cong oddᶻ e) rest
      sylN : sylᶜ s ≡ Zʷ m
      sylN = ≡.trans syl (≡.trans (≡.cong (λ K → sylDataᶜ p K W) eK) (sylDataᶜ-neg W fo (≡.cong negᶻ e)))
      pN = prograde (Z-gen m) s o pv sylN
      -- 1.2
      apart : m ≢ j → m ≢ j′ → Path [ G ]ʷ s o
      apart m≢j m≢j′ = commute G (Z-gen m) ((m≢j ∷ m≢j′ ∷ []) ∷ []) s o pN
                         (prograde (Z-gen m) r (ColOrth-actMʷ Xj o) Rr.pv′ sylR) (below-r Rr.pv′ (Zʷ m) sylR) (below-s (Zʷ m) sylN)
        where
        colr′ = same-col rest m≢j m≢j′
        module Rr = Rep 0 W colr′ (inj₁ ≡.refl) (λ e′ → ne (≡.trans colW₀ (≡.trans (≡.sym colr′) e′)))
        sylR : sylᶜ r ≡ Zʷ m
        sylR = ≡.trans Rr.syl′ (sylDataᶜ-neg W fo (≡.cong negᶻ e))
      -- 1.5, 1.6: the unit moves to x, and X conjugates (-1)[x] into (-1)[m].
      moved : ∀ x → W′ ! x ≡ ZR.- ZR.1# → (∀ y → y ≢ x → W′ ! y ≡ ZR.0#) → Xj • Zʷ x • Xj ≈ Zʷ m → Path [ G ]ʷ s o
      moved x ex restx rel = close G s o (Zʷ m) (Zʷ x) Xj pN pN′ (below-r Rr.pv′ (Zʷ x) sylR , end-below rel sylN) rel
        where
        module Rr = Rep 0 W′ colr (inj₁ ≡.refl) (ne-𝕀-at r p 0 W′ colr (inj₁ ≡.refl) x (λ e′ → neg≢e p x (≡.trans (≡.sym ex) e′)))
        sylR : sylᶜ r ≡ Zʷ x
        sylR = ≡.trans Rr.syl′ (sylDataᶜ-neg W′ (unit-first W′ x (≡.cong oddᶻ ex) restx) (≡.cong negᶻ ex))
        pN′ = prograde (Z-gen x) r (ColOrth-actMʷ Xj o) Rr.pv′ sylR
      at-j : m ≡ j → Path [ G ]ʷ s o
      at-j m≡j = moved j′ (≡.trans (proj₁ mv) e) (proj₂ mv) (≡.subst (λ y → Xj • Zʷ j′ • Xj ≈ Zʷ y) (≡.sym m≡j) (XZbX jj′))
        where mv = from-j rest m≡j
      at-j′ : m ≡ j′ → Path [ G ]ʷ s o
      at-j′ m≡j′ = moved j (≡.trans (proj₁ mv) e) (proj₂ mv) (≡.subst (λ y → Xj • Zʷ j • Xj ≈ Zʷ y) (≡.sym m≡j′) (XZaX jj′))
        where mv = from-j′ rest m≡j′

    -- e_m, m < p: N = X[m,p]
    by (pos m m<p e rest) eK = dec-elim (m FinP.≟ j) at-j (λ m≢j → dec-elim (m FinP.≟ j′) at-j′ (apart m≢j))
      where
      open Unit eK
      fo : firstOdd W ≡ just m
      fo = unit-first W m (≡.cong oddᶻ e) rest
      Xm = X m p m<p
      sylN : sylᶜ s ≡ Xm
      sylN = ≡.trans syl (≡.trans (≡.cong (λ K → sylDataᶜ p K W) eK) (sylDataᶜ-pos W fo (≡.cong negᶻ e) m<p))
      pN = prograde (X-gen m p m<p) s o pv sylN
      -- 1.3
      apart : m ≢ j → m ≢ j′ → Path [ G ]ʷ s o
      apart m≢j m≢j′ = dec-elim (j′ FinP.≟ p) at-p not-p
        where
        colr′ = same-col rest m≢j m≢j′
        module Rr = Rep 0 W colr′ (inj₁ ≡.refl) (λ e′ → ne (≡.trans colW₀ (≡.trans (≡.sym colr′) e′)))
        sylR : sylᶜ r ≡ Xm
        sylR = ≡.trans Rr.syl′ (sylDataᶜ-pos W fo (≡.cong negᶻ e) m<p)
        pN′ = prograde (X-gen m p m<p) r (ColOrth-actMʷ Xj o) Rr.pv′ sylR
        -- 1.3.1
        not-p : j′ ≢ p → Path [ G ]ʷ s o
        not-p j′≢p = commute G (X-gen m p m<p) ((m≢j ∷ m≢j′ ∷ []) ∷ (sym≢ (<-≢ j<p) ∷ sym≢ j′≢p ∷ []) ∷ []) s o pN pN′
                       (below-r Rr.pv′ Xm sylR) (below-s Xm sylN)
        -- 1.3.2
        at-p : j′ ≡ p → Path [ G ]ʷ s o
        at-p j′≡p = close G s o Xm Xm (X m j m<j) pN pN′ (below-r Rr.pv′ Xm sylR , end-below rel sylN) rel
          where
          m<j : m < j
          m<j = lt-j′ m≢j (≡.subst (m <_) (≡.sym j′≡p) m<p)
          rel : X m j m<j • Xm • Xj ≈ Xm
          rel = begin
            X m j m<j • Xm • Xj                               ≈⟨ cright cleft refl′ (X-≡ ≡.refl (≡.sym j′≡p)) ⟩
            X m j m<j • X m j′ (lt-j m<j) • Xj                ≈⟨ XXX m<j jj′ ⟩
            X m j′ (lt-j m<j)                                 ≈⟨ refl′ (X-≡ ≡.refl j′≡p) ⟩
            Xm                                                ∎
      -- 1.8, 1.9: the unit moves to x < p, and X conjugates X[x,p] into
      -- X[m,p].
      moved : ∀ x (x<p : x < p) → W′ ! x ≡ ZR.1# → (∀ y → y ≢ x → W′ ! y ≡ ZR.0#) → Xj • X x p x<p • Xj ≈ Xm →
              Path [ G ]ʷ s o
      moved x x<p ex restx rel = close G s o Xm (X x p x<p) Xj pN pN′ (below-r Rr.pv′ (X x p x<p) sylR , end-below rel sylN) rel
        where
        module Rr = Rep 0 W′ colr (inj₁ ≡.refl)
                      (ne-𝕀-at r p 0 W′ colr (inj₁ ≡.refl) x (λ e′ → one≢e p x (<-≢ x<p) (≡.trans (≡.sym ex) e′)))
        sylR : sylᶜ r ≡ X x p x<p
        sylR = ≡.trans Rr.syl′ (sylDataᶜ-pos W′ (unit-first W′ x (≡.cong oddᶻ ex) restx) (≡.cong negᶻ ex) x<p)
        pN′ = prograde (X-gen x p x<p) r (ColOrth-actMʷ Xj o) Rr.pv′ sylR
      -- 1.7, 1.8
      at-j : m ≡ j → Path [ G ]ʷ s o
      at-j m≡j = dec-elim (j′ FinP.≟ p) at-p not-p
        where
        at-p : j′ ≡ p → Path [ G ]ʷ s o
        at-p j′≡p = prograde G s o pv (≡.trans sylN (X-≡ m≡j (≡.sym j′≡p)))
        not-p : j′ ≢ p → Path [ G ]ʷ s o
        not-p j′≢p = moved j′ j′<p (≡.trans (proj₁ mv) e) (proj₂ mv) rel
          where
          mv = from-j rest m≡j
          j′<p : j′ < p
          j′<p = ℕP.≤∧≢⇒< j′≤p (λ e′ → j′≢p (FinP.toℕ-injective e′))
          rel : Xj • X j′ p j′<p • Xj ≈ Xm
          rel = trans (XXbcX jj′ j′<p) (refl′ (X-≡ (≡.sym m≡j) ≡.refl))
      -- 1.9
      at-j′ : m ≡ j′ → Path [ G ]ʷ s o
      at-j′ m≡j′ = moved j j<p (≡.trans (proj₁ mv) e) (proj₂ mv) rel
        where
        mv = from-j′ rest m≡j′
        j′<p : j′ < p
        j′<p = ≡.subst (_< p) m≡j′ m<p
        rel : Xj • X j p j<p • Xj ≈ Xm
        rel = trans (XXacX jj′ j′<p) (refl′ (X-≡ (≡.sym m≡j′) ≡.refl))

    -- k > 0: N = H[i₁,i₂]
    by {suc k′} (pair i₁ i₂ fo nx i₁<i₂ i₂≤p) eK =
      dec-elim (i₁ FinP.≟ j) at-j λ i₁≢j → dec-elim (i₁ FinP.≟ j′) (at-j′ i₁≢j) λ i₁≢j′ →
      dec-elim (i₂ FinP.≟ j′) (to-j′ i₁≢j i₁≢j′) λ i₂≢j′ → dec-elim (i₂ FinP.≟ j) (to-j i₁≢j i₁≢j′) (λ i₂≢j → P.c14 fo nx i₁<i₂ i₁≢j i₁≢j′ i₂≢j i₂≢j′)
      where
      module P = Pair k′ eK
      ss = proj₁ (proj₂ (nextSame-spec W nx))
      at-j : i₁ ≡ j → Path [ G ]ʷ s o
      at-j i₁≡j = dec-elim (i₂ FinP.≟ j′) (λ i₂≡j′ → P.c110 fo′ (≡.subst₂ (λ a b → nextSame a W ≡ just b) i₁≡j i₂≡j′ nx))
                    λ i₂≢j′ → by-odd (oddᶻ (W ! j′)) ≡.refl i₂≢j′
        where
        fo′ : firstOdd W ≡ just j
        fo′ = ≡.subst (λ a → firstOdd W ≡ just a) i₁≡j fo
        nx′ : nextSame j W ≡ just i₂
        nx′ = ≡.subst (λ a → nextSame a W ≡ just i₂) i₁≡j nx
        by-odd : ∀ b → oddᶻ (W ! j′) ≡ b → i₂ ≢ j′ → Path [ G ]ʷ s o
        by-odd false ev i₂≢j′ = P.c1111 fo′ nx′ (gt-j i₂≢j′ (proj₁ (nextSame-spec W nx′))) ev
        by-odd true od i₂≢j′ = P.c1112 fo′ nx′ (gt-j i₂≢j′ (proj₁ (nextSame-spec W nx′))) od
      at-j′ : i₁ ≢ j → i₁ ≡ j′ → Path [ G ]ʷ s o
      at-j′ _ i₁≡j′ = P.c112 (≡.subst (λ a → firstOdd W ≡ just a) i₁≡j′ fo) (≡.subst (λ a → nextSame a W ≡ just i₂) i₁≡j′ nx)
      to-j′ : i₁ ≢ j → i₁ ≢ j′ → i₂ ≡ j′ → Path [ G ]ʷ s o
      to-j′ i₁≢j i₁≢j′ i₂≡j′ = P.c113 fo (≡.subst (λ b → nextSame i₁ W ≡ just b) i₂≡j′ nx) i₁≢j i₁≢j′
      to-j : i₁ ≢ j → i₁ ≢ j′ → i₂ ≡ j → Path [ G ]ʷ s o
      to-j i₁≢j i₁≢j′ i₂≡j = dec-elim (same? i₁ j′) (P.c1142 fo nx′) (P.c1141 fo nx′ i₁≢j i₁≢j′)
        where
        nx′ : nextSame i₁ W ≡ just j
        nx′ = ≡.subst (λ b → nextSame i₁ W ≡ just b) i₂≡j nx
