------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 4.4, Subcase 3.4: H[0,1] on two odd entries v₀, v₁ of
-- different classes, at a state s of level L = (p + 1, k, ℓ), k > 0.
--
-- Let j be the partner of 0 (the next odd entry in its class, so that
-- H[0,j] is the syllable of s) and l that of 1.  H[0,1] keeps both
-- entries odd and of different classes, so r = H[0,1]·s lies at L, and
-- its syllable is H[0,j′] with j′ the first entry after 1 in the class
-- of the new entry 0: j or l.
--
-- * ℓ > 4 (Lemma 5.11 with Lemma 5.3): the other odd entries contain
--   two of one class, u < v, which the algorithm pairs after H[0,j] and
--   H[1,l].  H[u,v] commutes with H[0,j], H[0,j′] and H[0,1], so it is
--   an edge out of s and out of r (commuting squares with their
--   syllables), and H[0,1] out of H[u,v]·s lies below L.
-- * ℓ = 4: the decision trees of Clément's diagrams (20) and (30) and
--   normal forms (38) (Hard), over Clément's normal words, with the
--   plain edges at L (Plain).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Product.Base using (_,_)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction as TR
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case1 as Case1

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case34 {n : ℕ} (p : Fin n) (k′ ℓ : ℕ)
  (ih : TR.EdgesBelow {n} (suc (toℕ p) , suc k′ , ℓ)) (h1142 : Case1.Hyp1142 ih) where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (_<_ ; _≤_)
import Data.Fin.Properties as FinP
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Maybe.Properties using (just-injective)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)
import Data.Bool.Properties as BoolP
import Data.Integer.Base as ℤ
import Data.Integer.Properties as ℤP

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim ; tri-elim ; count-false)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; module DR ; oddᶻ ; rbit)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde
  using (_!_ ; scV ; Minimal ; Odd ; Even ; Odd⇒¬Even ; ¬Even⇒Odd ; lde ; num ; lde-char ; all-even?)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm using (NA ; NB ; Σℕ ; Σℤ ; unit-norm ; unit-normB)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
  using (nodd ; firstOdd ; nextSame ; Same ; firstOdd-char ; firstOdd-spec ; firstOdd-nothing ; nextSame-spec ; nextSame-nothing)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; pivot-char ; _<ₗ_ ; level)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable using (Beyond-actM)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step using (odd⇒≤)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (_≤ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (ne-𝕀)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Algorithm
  using (synthᶜ ; levelᶜ ; levelᶜ-just ; sylᶜ ; sylDataᶜ ; sylDataᶜ-pair ; third ; partner)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Squares {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.State {n}
  using (module Pos ; module At ; View ; neg ; pos ; pair ; valid-step ; lowᶜ ; partner′ ; sylᶜ-of ; levelᶜ-of)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case3 as Case3
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Plain as Plain
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Hard as Hard

private
  module P = Plain p k′ ℓ ih h1142
  open Close ih

  sym≢ : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
  sym≢ ne e = ne (≡.sym e)

  <-≢ : ∀ {x y : Fin n} → x < y → x ≢ y
  <-≢ lt ≡.refl = FinP.<-irrefl ≡.refl lt

  t≢f : true ≢ false
  t≢f ()

k : ℕ
k = suc k′

L = P.L

------------------------------------------------------------------------
-- The hard edge at s

module At34 (s : Matrix n n D) .(o : ColOrth s) (pv : pivot s ≡ just p) (eqL : levelᶜ s ≡ L)
            {z₀ z₁ : Fin n} (t0 : toℕ z₀ ≡ 0) (t1 : toℕ z₁ ≡ 1) .(z01 : z₀ < z₁) (z₁≤p : z₁ ≤ p)
            (le : levelᶜ (actM (H-gen z₀ z₁ z01) s) ≤ₗ L)
            (o0 : Odd (num (col s p) ! z₀)) (o1 : Odd (num (col s p) ! z₁))
            (r01 : rbit (num (col s p) ! z₀) ≢ rbit (num (col s p) ! z₁)) where

  open At s o pv using (W ; colW ; be ; lvl ; zero> ; norm ; normB)

  G = H-gen z₀ z₁ z01
  r = actM G s

  kM : lde (col s p) ≡ k
  kM = ≡.cong (λ t → proj₁ (proj₂ t)) (≡.trans (≡.sym lvl) eqL)

  ℓM : nodd W ≡ ℓ
  ℓM = ≡.trans (≡.cong (λ K → third K W) (≡.sym kM)) (≡.cong (λ t → proj₂ (proj₂ t)) (≡.trans (≡.sym lvl) eqL))

  colk : col s p ≡ scV k W
  colk = ≡.trans colW (≡.cong (λ K → scV K W) kM)

  z₀≢z₁ : z₀ ≢ z₁
  z₀≢z₁ e = r01 (≡.cong (λ x → rbit (W ! x)) e)

  none<0 : ∀ {x : Fin n} → ¬ (x < z₀)
  none<0 {x} x<0 = ℕP.n≮0 (≡.subst (toℕ x ℕ.<_) t0 x<0)

  -- Indices other than z₀ come after it.
  after0 : ∀ {x : Fin n} → x ≢ z₀ → z₀ < x
  after0 {x} x≢0 = ≡.subst (ℕ._< toℕ x) (≡.sym t0) (ℕP.n≢0⇒n>0 (λ e → x≢0 (FinP.toℕ-injective (≡.trans e (≡.sym t0)))))

  ----------------------------------------------------------------------
  -- ℓ = 4: the trees

  four : nodd W ≡ 4 → Path [ G ]ʷ s o
  four ℓ4 = Hard.hard p k′ ℓ synthᶜ P.ihF P.plain s o (Pos.conv≡ s eqL) ℓ4 z₀ z₁ z01 o0 o1 r01

  ----------------------------------------------------------------------
  -- ℓ > 4

  module Many (ℓ≢4 : nodd W ≢ 4) where

    -- The first odd entry of a column at scale k, and its partner.
    pair-of : (N : Matrix n n D) .(oN : ColOrth N) (w : Vec Z n) → col N p ≡ scV k w → (∃ λ x → Odd (w ! x)) →
              ∃ λ u → ∃ λ v → firstOdd w ≡ just u × nextSame u w ≡ just v
    pair-of N oN w eq (x , ox) = first (firstOdd w) ≡.refl
      where
      nA : Σℕ (λ y → NA (w ! y)) ≡ 2 ℕ.^ k
      nA = recompute (Σℕ (λ y → NA (w ! y)) ℕP.≟ 2 ℕ.^ k) (unit-norm k w (≡.subst (λ c → ⟨ c , c ⟩ ≡ DR.1#) eq (col-unit oN p)))
      nB : Σℤ (λ y → NB (w ! y)) ≡ ℤ.+ 0
      nB = recompute (Σℤ (λ y → NB (w ! y)) ℤP.≟ ℤ.+ 0) (unit-normB k w (≡.subst (λ c → ⟨ c , c ⟩ ≡ DR.1#) eq (col-unit oN p)))
      first : (m : Maybe (Fin n)) → firstOdd w ≡ m → ∃ λ u → ∃ λ v → firstOdd w ≡ just u × nextSame u w ≡ just v
      first nothing fo = ⊥-elim (Odd⇒¬Even {w ! x} ox (firstOdd-nothing w fo x))
      first (just u) fo = next (nextSame u w) ≡.refl
        where
        next : (m : Maybe (Fin n)) → nextSame u w ≡ m → ∃ λ u′ → ∃ λ v → firstOdd w ≡ just u′ × nextSame u′ w ≡ just v
        next nothing nx = ⊥-elim (partner k′ w nA nB fo nx)
        next (just v) nx = u , v , fo , nx

    -- j and l, the partners of 0 and 1.
    fo0 : firstOdd W ≡ just z₀
    fo0 = firstOdd-char W o0 (λ x x<0 → ⊥-elim (none<0 x<0))

    nA₀ : Σℕ (λ y → NA (W ! y)) ≡ 2 ℕ.^ k
    nA₀ = ≡.subst (λ K → Σℕ (λ y → NA (W ! y)) ≡ 2 ℕ.^ K) kM norm

    with-j : (m : Maybe (Fin n)) → nextSame z₀ W ≡ m → ∃ λ j → nextSame z₀ W ≡ just j
    with-j nothing nx = ⊥-elim (partner k′ W nA₀ normB fo0 nx)
    with-j (just j) nx = j , nx

    j = proj₁ (with-j (nextSame z₀ W) ≡.refl)
    nxj = proj₂ (with-j (nextSame z₀ W) ≡.refl)
    specj = nextSame-spec W nxj

    with-l : (m : Maybe (Fin n)) → nextSame z₁ W ≡ m → ∃ λ l → nextSame z₁ W ≡ just l
    with-l nothing nx = ⊥-elim (partner′ k′ W nA₀ normB o1 before nx)
      where
      before : ∀ y → y < z₁ → ¬ Same W z₁ y
      before y y<1 (_ , ry) = dec-elim (y FinP.≟ z₀)
        (λ y≡0 → r01 (≡.trans (≡.sym (≡.cong (λ x → rbit (W ! x)) y≡0)) ry))
        (λ y≢0 → ℕP.<-irrefl ≡.refl (ℕP.<-≤-trans (≡.subst (ℕ._< toℕ y) t0 (after0 y≢0)) (ℕP.≤-pred (≡.subst (toℕ y ℕ.<_) t1 y<1))))
    with-l (just l) nx = l , nx

    l = proj₁ (with-l (nextSame z₁ W) ≡.refl)
    nxl = proj₂ (with-l (nextSame z₁ W) ≡.refl)
    specl = nextSame-spec W nxl

    z₀<j : z₀ < j
    z₀<j = proj₁ specj
    z₁<l : z₁ < l
    z₁<l = proj₁ specl
    sj = proj₁ (proj₂ specj)
    sl = proj₁ (proj₂ specl)
    oj : Odd (W ! j)
    oj = proj₁ sj
    ol : Odd (W ! l)
    ol = proj₁ sl
    j≤p = odd⇒≤ {p = p} {W} zero> oj
    l≤p = odd⇒≤ {p = p} {W} zero> ol

    -- Entries of the class of 0 and of 1.
    class-of : ∀ x → Odd (W ! x) → rbit (W ! x) ≡ rbit (W ! z₀) ⊎ rbit (W ! x) ≡ rbit (W ! z₁)
    class-of x ox = by (rbit (W ! x)) (rbit (W ! z₀)) (rbit (W ! z₁)) ≡.refl ≡.refl ≡.refl r01
      where
      by : ∀ a b c → rbit (W ! x) ≡ a → rbit (W ! z₀) ≡ b → rbit (W ! z₁) ≡ c → b ≢ c →
           rbit (W ! x) ≡ rbit (W ! z₀) ⊎ rbit (W ! x) ≡ rbit (W ! z₁)
      by true true _ ex e0 _ _ = inj₁ (≡.trans ex (≡.sym e0))
      by false false _ ex e0 _ _ = inj₁ (≡.trans ex (≡.sym e0))
      by true false true ex _ e1 _ = inj₂ (≡.trans ex (≡.sym e1))
      by false true false ex _ e1 _ = inj₂ (≡.trans ex (≡.sym e1))
      by true false false _ e0 e1 ne = ⊥-elim (ne ≡.refl)
      by false true true _ e0 e1 ne = ⊥-elim (ne ≡.refl)

    j≢z₁ : j ≢ z₁
    j≢z₁ e = r01 (≡.trans (≡.sym (proj₂ sj)) (≡.cong (λ x → rbit (W ! x)) e))
    l≢z₀ : l ≢ z₀
    l≢z₀ e = r01 (≡.trans (≡.cong (λ x → rbit (W ! x)) (≡.sym e)) (proj₂ sl))
    j≢l : j ≢ l
    j≢l e = r01 (≡.trans (≡.sym (proj₂ sj)) (≡.trans (≡.cong (λ x → rbit (W ! x)) e) (proj₂ sl)))
    z₀≢j = <-≢ z₀<j
    z₁≢l = <-≢ z₁<l

    -- Indices other than 0 and 1 come after 1.
    after1 : ∀ {x : Fin n} → x ≢ z₀ → x ≢ z₁ → z₁ < x
    after1 {x} x≢0 x≢1 =
      ≡.subst (ℕ._< toℕ x) (≡.sym t1)
        (two≤ (toℕ x) (λ e → x≢0 (FinP.toℕ-injective (≡.trans e (≡.sym t0))))
                      (λ e → x≢1 (FinP.toℕ-injective (≡.trans e (≡.sym t1)))))
      where
      two≤ : ∀ m → m ≢ 0 → m ≢ 1 → 1 ℕ.< m
      two≤ zero ne0 _ = ⊥-elim (ne0 ≡.refl)
      two≤ (suc zero) _ ne1 = ⊥-elim (ne1 ≡.refl)
      two≤ (suc (suc m)) _ _ = s≤s (s≤s z≤n)

    -- An odd entry of the class of a, after a, but not its partner b,
    -- comes after b.
    gt : ∀ {a b x} → nextSame a W ≡ just b → Same W a x → a < x → x ≢ b → b < x
    gt {a} {b} {x} nx sx a<x x≢b = tri-elim (FinP.<-cmp x b)
      (λ x<b → ⊥-elim (proj₂ (proj₂ (nextSame-spec W nx)) x a<x x<b sx))
      (λ x≡b → ⊥-elim (x≢b x≡b))
      (λ b<x → b<x)

    -- Every other odd entry has j or l before it in its class.
    first-class : ∀ x → Odd (W ! x) → x ≢ z₀ → x ≢ z₁ → x ≢ j → x ≢ l →
                  ∃ λ y → (y ≡ j ⊎ y ≡ l) × y < x × rbit (W ! y) ≡ rbit (W ! x)
    first-class x ox x≢0 x≢1 x≢j x≢l = by (class-of x ox)
      where
      by : rbit (W ! x) ≡ rbit (W ! z₀) ⊎ rbit (W ! x) ≡ rbit (W ! z₁) →
           ∃ λ y → (y ≡ j ⊎ y ≡ l) × y < x × rbit (W ! y) ≡ rbit (W ! x)
      by (inj₁ rx) = j , inj₁ ≡.refl , gt nxj (ox , rx) (after0 x≢0) x≢j , ≡.trans (proj₂ sj) (≡.sym rx)
      by (inj₂ rx) = l , inj₂ ≡.refl , gt nxl (ox , rx) (after1 x≢0 x≢1) x≢l , ≡.trans (proj₂ sl) (≡.sym rx)

    -- A count two below another is below it.
    lt2 : ∀ {a b} → b ≡ suc (suc a) → a ℕ.< b
    lt2 {a} e = ≡.subst (a ℕ.<_) (≡.sym e) (ℕP.≤-trans (ℕP.n<1+n a) (ℕP.n≤1+n (suc a)))

    -- H[0,j], then H[1,l]: what remains odd lies apart from 0, 1, j, l.
    vs₁ = valid-step s p k W colk z₀ j z₀<j o0 oj (≡.sym (proj₂ sj))
    W₁ = proj₁ vs₁
    col₁ = proj₁ (proj₂ vs₁)
    keep₁ = proj₁ (proj₂ (proj₂ (proj₂ vs₁)))
    s₁ = actM (H-gen z₀ j z₀<j) s
    e₁1 : W₁ ! z₁ ≡ W ! z₁
    e₁1 = keep₁ z₁ (sym≢ z₀≢z₁) (sym≢ j≢z₁)
    e₁l : W₁ ! l ≡ W ! l
    e₁l = keep₁ l l≢z₀ (sym≢ j≢l)
    vs₂ = valid-step s₁ p k W₁ col₁ z₁ l z₁<l (≡.trans (≡.cong oddᶻ e₁1) o1) (≡.trans (≡.cong oddᶻ e₁l) ol)
            (≡.trans (≡.cong rbit e₁1) (≡.trans (≡.sym (proj₂ sl)) (≡.sym (≡.cong rbit e₁l))))
    W₂ = proj₁ vs₂
    col₂ = proj₁ (proj₂ vs₂)
    keep₂ = proj₁ (proj₂ (proj₂ (proj₂ vs₂)))
    s₂ = actM (H-gen z₁ l z₁<l) s₁
    cnt₂ : nodd W ≡ suc (suc (suc (suc (nodd W₂))))
    cnt₂ = ≡.trans (proj₁ (proj₂ (proj₂ vs₁))) (≡.cong (λ c → suc (suc c)) (proj₁ (proj₂ (proj₂ vs₂))))
    ev₂ : ∀ x → x ≡ z₀ ⊎ x ≡ j ⊎ x ≡ z₁ ⊎ x ≡ l → Even (W₂ ! x)
    ev₂ x (inj₁ ≡.refl) = ≡.trans (≡.cong oddᶻ (keep₂ x z₀≢z₁ (sym≢ l≢z₀))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ vs₁)))))
    ev₂ x (inj₂ (inj₁ ≡.refl)) = ≡.trans (≡.cong oddᶻ (keep₂ x j≢z₁ j≢l)) (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ vs₁)))))
    ev₂ x (inj₂ (inj₂ (inj₁ ≡.refl))) = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ vs₂))))
    ev₂ x (inj₂ (inj₂ (inj₂ ≡.refl))) = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ vs₂))))
    -- An odd entry of W₂ is none of 0, j, 1, l, and is that of W.
    apart₂ : ∀ {x} → Odd (W₂ ! x) → x ≢ z₀ × x ≢ j × x ≢ z₁ × x ≢ l
    apart₂ {x} ox = (λ e → none (inj₁ e)) , (λ e → none (inj₂ (inj₁ e))) , (λ e → none (inj₂ (inj₂ (inj₁ e)))) , (λ e → none (inj₂ (inj₂ (inj₂ e))))
      where
      none : x ≡ z₀ ⊎ x ≡ j ⊎ x ≡ z₁ ⊎ x ≡ l → ⊥
      none w = t≢f (≡.trans (≡.sym ox) (ev₂ x w))
    W₂≡ : ∀ {x} → Odd (W₂ ! x) → W₂ ! x ≡ W ! x
    W₂≡ {x} ox = let (a , b , c , d) = apart₂ ox in ≡.trans (keep₂ x c d) (keep₁ x a b)
    -- Since ℓ ≠ 4, some entry of W₂ is odd.
    some : ∃ λ x → Odd (W₂ ! x)
    some = by (all-even? W₂)
      where
      by : Dec (∀ x → Even (W₂ ! x)) → ∃ λ x → Odd (W₂ ! x)
      by (yes ev) = ⊥-elim (ℓ≢4 (≡.trans cnt₂ (≡.cong (λ c → suc (suc (suc (suc c)))) (count-false _ ev))))
      by (no ¬ev) = let (x , ¬e) = FinP.¬∀⇒∃¬ n (λ x → Even (W₂ ! x)) (λ x → oddᶻ (W₂ ! x) BoolP.≟ false) ¬ev
                    in x , ¬Even⇒Odd {W₂ ! x} ¬e

    -- The pair u < v that the algorithm takes next.
    uv = pair-of s₂ (ColOrth-actMʷ (H z₁ l z₁<l • H z₀ j z₀<j) o) W₂ col₂ some
    u = proj₁ uv
    v = proj₁ (proj₂ uv)
    fou = proj₁ (proj₂ (proj₂ uv))
    specv = nextSame-spec W₂ (proj₂ (proj₂ (proj₂ uv)))
    u<v : u < v
    u<v = proj₁ specv
    ou₂ = proj₁ (firstOdd-spec W₂ fou)
    ov₂ = proj₁ (proj₁ (proj₂ specv))
    au = apart₂ ou₂
    av = apart₂ ov₂
    u≢z₀ = proj₁ au
    u≢j = proj₁ (proj₂ au)
    u≢z₁ = proj₁ (proj₂ (proj₂ au))
    u≢l = proj₂ (proj₂ (proj₂ au))
    v≢z₀ = proj₁ av
    v≢j = proj₁ (proj₂ av)
    v≢z₁ = proj₁ (proj₂ (proj₂ av))
    v≢l = proj₂ (proj₂ (proj₂ av))
    ou : Odd (W ! u)
    ou = ≡.trans (≡.cong oddᶻ (≡.sym (W₂≡ ou₂))) ou₂
    ov : Odd (W ! v)
    ov = ≡.trans (≡.cong oddᶻ (≡.sym (W₂≡ ov₂))) ov₂
    ruv : rbit (W ! u) ≡ rbit (W ! v)
    ruv = ≡.trans (≡.cong rbit (≡.sym (W₂≡ ou₂))) (≡.trans (≡.sym (proj₂ (proj₁ (proj₂ specv)))) (≡.cong rbit (W₂≡ ov₂)))
    v≤p = odd⇒≤ {p = p} {W} zero> ov

    K = H-gen u v u<v

    ----------------------------------------------------------------------
    -- H[u,v] out of s: a commuting square with the syllable H[0,j]

    sylN : sylᶜ s ≡ H z₀ j z₀<j
    sylN = ≡.trans syl (≡.trans (≡.cong (λ K′ → sylDataᶜ p K′ W) kM) (sylDataᶜ-pair {p = p} k′ W fo0 nxj z₀<j))
      where open At s o pv using (syl)

    vsK = valid-step s p k W colk u v u<v ou ov ruv
    WK = proj₁ vsK
    colK = proj₁ (proj₂ vsK)
    keepK = proj₁ (proj₂ (proj₂ (proj₂ vsK)))
    beK = Beyond-actM K {p} {s} v≤p be

    lKs : levelᶜ (actM K s) <ₗ L
    lKs = lowᶜ (actM K s) beK k′ WK colK (≡.subst (nodd WK ℕ.<_) ℓM (lt2 (proj₁ (proj₂ (proj₂ vsK)))))

    vsNK = valid-step (actM K s) p k WK colK z₀ j z₀<j
             (≡.trans (≡.cong oddᶻ (keepK z₀ (sym≢ u≢z₀) (sym≢ v≢z₀))) o0)
             (≡.trans (≡.cong oddᶻ (keepK j (sym≢ u≢j) (sym≢ v≢j))) oj)
             (≡.trans (≡.cong rbit (keepK z₀ (sym≢ u≢z₀) (sym≢ v≢z₀)))
               (≡.trans (≡.sym (proj₂ sj)) (≡.sym (≡.cong rbit (keepK j (sym≢ u≢j) (sym≢ v≢j))))))

    lNKs : levelᶜ (actM (H-gen z₀ j z₀<j) (actM K s)) <ₗ L
    lNKs = lowᶜ (actM (H-gen z₀ j z₀<j) (actM K s)) (Beyond-actM (H-gen z₀ j z₀<j) {p} {actM K s} j≤p beK) k′
             (proj₁ vsNK) (proj₁ (proj₂ vsNK))
             (≡.subst (nodd (proj₁ vsNK) ℕ.<_) ℓM
               (ℕP.<-trans (lt2 (proj₁ (proj₂ (proj₂ vsNK)))) (lt2 (proj₁ (proj₂ (proj₂ vsK))))))

    lNs : levelᶜ (actM (H-gen z₀ j z₀<j) s) <ₗ L
    lNs = ≡.subst (λ w → levelᶜ (actMʷ w s) <ₗ L) sylN (normal-below s o pv (inj₂ eqL))

    pKs : Path [ K ]ʷ s o
    pKs = commute K (H-gen z₀ j z₀<j) ((sym≢ u≢z₀ ∷ sym≢ v≢z₀ ∷ []) ∷ (sym≢ u≢j ∷ sym≢ v≢j ∷ []) ∷ []) s o
            (prograde (H-gen z₀ j z₀<j) s o pv sylN)
            (ih (H-gen z₀ j z₀<j) (actM K s) (ColOrth-actMʷ [ K ]ʷ o) lKs lNKs) lNKs lNs

    ----------------------------------------------------------------------
    -- H[u,v] out of r: a commuting square with its syllable H[0,j′]

    hc = P.hard-col s o eqL z₀ z₁ z01 (o0 , o1 , r01)
    module HC = P.HardCol hc
    WR = HC.W″

    eqR : levelᶜ r ≡ L
    eqR = P.hard-level s o eqL z₀ z₁ z01 (o0 , o1 , r01)

    beR = proj₂ (Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot.pivot-just r HC.pvH)

    foR : firstOdd WR ≡ just z₀
    foR = firstOdd-char WR HC.odd-a (λ x x<0 → ⊥-elim (none<0 x<0))

    uv′ = pair-of r (ColOrth-actMʷ [ G ]ʷ o) WR HC.colH (z₀ , HC.odd-a)
    j′ = proj₁ (proj₂ uv′)
    nxR : nextSame z₀ WR ≡ just j′
    nxR = ≡.subst (λ a → nextSame a WR ≡ just j′) (just-injective (≡.trans (≡.sym (proj₁ (proj₂ (proj₂ uv′)))) foR))
            (proj₂ (proj₂ (proj₂ uv′)))
    specR = nextSame-spec WR nxR
    z₀<j′ : z₀ < j′
    z₀<j′ = proj₁ specR
    sj′ = proj₁ (proj₂ specR)

    sylR : sylᶜ r ≡ H z₀ j′ z₀<j′
    sylR = ≡.trans (sylᶜ-of r HC.pvH k WR HC.colH (inj₂ (z₀ , HC.odd-a))) (sylDataᶜ-pair {p = p} k′ WR foR nxR z₀<j′)

    -- j′ is neither u nor v: j or l comes before either in its class.
    j′≢ : ∀ {x} → Odd (W ! x) → x ≢ z₀ → x ≢ z₁ → x ≢ j → x ≢ l → j′ ≢ x
    j′≢ {x} ox x≢0 x≢1 x≢j x≢l j′≡x = proj₂ (proj₂ specR) y (after0 y≢0) (≡.subst (y <_) (≡.sym j′≡x) y<x) (oy , ry)
      where
      fc = first-class x ox x≢0 x≢1 x≢j x≢l
      y = proj₁ fc
      y<x = proj₁ (proj₂ (proj₂ fc))
      y∈ = proj₁ (proj₂ fc)
      y≢0 : y ≢ z₀
      y≢0 e = Data.Sum.Base.[_,_]′ (λ y≡j → z₀≢j (≡.trans (≡.sym e) y≡j)) (λ y≡l → l≢z₀ (≡.trans (≡.sym y≡l) e)) y∈
        where import Data.Sum.Base
      y≢1 : y ≢ z₁
      y≢1 e = Data.Sum.Base.[_,_]′ (λ y≡j → j≢z₁ (≡.trans (≡.sym y≡j) e)) (λ y≡l → z₁≢l (≡.trans (≡.sym e) y≡l)) y∈
        where import Data.Sum.Base
      eRy : WR ! y ≡ W ! y
      eRy = HC.keep y y≢0 y≢1
      eRx : WR ! x ≡ W ! x
      eRx = HC.keep x x≢0 x≢1
      oWy : Odd (W ! y)
      oWy = Data.Sum.Base.[_,_]′ (λ y≡j → ≡.subst (λ z → Odd (W ! z)) (≡.sym y≡j) oj)
                                 (λ y≡l → ≡.subst (λ z → Odd (W ! z)) (≡.sym y≡l) ol) y∈
        where import Data.Sum.Base
      oy : Odd (WR ! y)
      oy = ≡.trans (≡.cong oddᶻ eRy) oWy
      ry : rbit (WR ! y) ≡ rbit (WR ! z₀)
      ry = ≡.trans (≡.cong rbit eRy) (≡.trans (proj₂ (proj₂ (proj₂ fc)))
             (≡.trans (≡.cong rbit (≡.sym eRx)) (≡.trans (≡.cong (λ z → rbit (WR ! z)) (≡.sym j′≡x)) (proj₂ sj′))))

    j′≢u : j′ ≢ u
    j′≢u = j′≢ ou u≢z₀ u≢z₁ u≢j u≢l
    j′≢v : j′ ≢ v
    j′≢v = j′≢ ov v≢z₀ v≢z₁ v≢j v≢l

    eRu : WR ! u ≡ W ! u
    eRu = HC.keep u u≢z₀ u≢z₁
    eRv : WR ! v ≡ W ! v
    eRv = HC.keep v v≢z₀ v≢z₁

    vsKr = valid-step r p k WR HC.colH u v u<v (≡.trans (≡.cong oddᶻ eRu) ou) (≡.trans (≡.cong oddᶻ eRv) ov)
             (≡.trans (≡.cong rbit eRu) (≡.trans ruv (≡.sym (≡.cong rbit eRv))))
    WKr = proj₁ vsKr
    colKr = proj₁ (proj₂ vsKr)
    keepKr = proj₁ (proj₂ (proj₂ (proj₂ vsKr)))
    beKr = Beyond-actM K {p} {r} v≤p beR

    lKr : levelᶜ (actM K r) <ₗ L
    lKr = lowᶜ (actM K r) beKr k′ WKr colKr (≡.subst (nodd WKr ℕ.<_) HC.cnt (lt2 (proj₁ (proj₂ (proj₂ vsKr)))))

    eKr0 : WKr ! z₀ ≡ WR ! z₀
    eKr0 = keepKr z₀ (sym≢ u≢z₀) (sym≢ v≢z₀)
    eKrj : WKr ! j′ ≡ WR ! j′
    eKrj = keepKr j′ j′≢u j′≢v

    vsNKr = valid-step (actM K r) p k WKr colKr z₀ j′ z₀<j′
              (≡.trans (≡.cong oddᶻ eKr0) HC.odd-a) (≡.trans (≡.cong oddᶻ eKrj) (proj₁ sj′))
              (≡.trans (≡.cong rbit eKr0) (≡.trans (≡.sym (proj₂ sj′)) (≡.sym (≡.cong rbit eKrj))))

    j′≤p = odd⇒≤ {p = p} {WR} beyond (proj₁ sj′)
      where
      beyond : ∀ x → p < x → WR ! x ≡ ZR.0#
      beyond x p<x = ≡.trans (HC.keep x (sym≢ (<-≢ (ℕP.≤-<-trans (≡.subst (ℕ._≤ toℕ p) (≡.sym t0) z≤n) p<x)))
                                        (sym≢ (<-≢ (ℕP.≤-<-trans z₁≤p p<x))))
                             (zero> x p<x)

    lNKr : levelᶜ (actM (H-gen z₀ j′ z₀<j′) (actM K r)) <ₗ L
    lNKr = lowᶜ (actM (H-gen z₀ j′ z₀<j′) (actM K r)) (Beyond-actM (H-gen z₀ j′ z₀<j′) {p} {actM K r} j′≤p beKr) k′
             (proj₁ vsNKr) (proj₁ (proj₂ vsNKr))
             (≡.subst (nodd (proj₁ vsNKr) ℕ.<_) HC.cnt
               (ℕP.<-trans (lt2 (proj₁ (proj₂ (proj₂ vsNKr)))) (lt2 (proj₁ (proj₂ (proj₂ vsKr))))))

    lNr : levelᶜ (actM (H-gen z₀ j′ z₀<j′) r) <ₗ L
    lNr = ≡.subst (λ w → levelᶜ (actMʷ w r) <ₗ L) sylR (normal-below r (ColOrth-actMʷ [ G ]ʷ o) HC.pvH (inj₂ eqR))

    pKr : Path [ K ]ʷ r (ColOrth-actMʷ [ G ]ʷ o)
    pKr = commute K (H-gen z₀ j′ z₀<j′) ((sym≢ u≢z₀ ∷ sym≢ v≢z₀ ∷ []) ∷ (j′≢u ∷ j′≢v ∷ []) ∷ []) r (ColOrth-actMʷ [ G ]ʷ o)
            (prograde (H-gen z₀ j′ z₀<j′) r (ColOrth-actMʷ [ G ]ʷ o) HC.pvH sylR)
            (ih (H-gen z₀ j′ z₀<j′) (actM K r) (ColOrth-actMʷ [ K ]ʷ (ColOrth-actMʷ [ G ]ʷ o)) lKr lNKr) lNKr lNr

    ----------------------------------------------------------------------
    -- H[0,1] out of s: a commuting square with H[u,v]

    many : Path [ G ]ʷ s o
    many = commute G K ((u≢z₀ ∷ u≢z₁ ∷ []) ∷ (v≢z₀ ∷ v≢z₁ ∷ []) ∷ []) s o pKs pKr lKr lKs

  ----------------------------------------------------------------------
  -- Subcase 3.4

  case34 : Path [ G ]ʷ s o
  case34 = dec-elim (nodd W ℕP.≟ 4) four (λ ℓ≢4 → Many.many ℓ≢4)

------------------------------------------------------------------------
-- Subcase 3.4 at every state of L

hyp34 : Case3.Hyp34 ih
hyp34 s o {q} pvq eqL {z₀} {z₁} t0 t1 z01 z₁≤q le k″ eK o0 o1 r01 = at q pvq z₁≤q o0 o1 r01 q≡p
  where
  q≡p : q ≡ p
  q≡p = FinP.toℕ-injective (ℕP.suc-injective (≡.cong proj₁ (≡.trans (≡.sym (levelᶜ-just s pvq)) eqL)))
  at : ∀ (q′ : Fin n) → pivot s ≡ just q′ → z₁ ≤ q′ → Odd (num (col s q′) ! z₀) → Odd (num (col s q′) ! z₁) →
       rbit (num (col s q′) ! z₀) ≢ rbit (num (col s q′) ! z₁) → q′ ≡ p → Path [ H-gen z₀ z₁ z01 ]ʷ s o
  at .p pv z₁≤p o0′ o1′ r′ ≡.refl = At34.case34 s o pv eqL t0 t1 z01 z₁≤p le o0′ o1′ r′
