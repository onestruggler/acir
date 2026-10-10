------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 4.4, Case 3: G = H[0,1], at a state s of level L with pivot
-- p ≥ 1.  Let v₀, v₁ be the entries 0 and 1 of the numerator of its
-- pivot column (at the exponent k of s).
--
-- * 3.1: both even, of one residue modulo 2 (for k = 0: both 0).  H
--   keeps them even, so G·s has the syllable N of s, apart from G:
--   they commute ((5), (7), (8)).
-- * 3.2: one odd and one even, or both even of different residues.
--   Then G·s lies above s (it is retrograde), and does not occur
--   here: only the edges that do not go up are asked for.
-- * 3.3: both odd, of one class: G is the syllable of s (prograde).
-- * 3.4: both odd, of different classes: a hypothesis here (Hyp34),
--   proved in Case34.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (Lvl)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction as TR

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case3 {n : ℕ} {L : Lvl} (ih : TR.EdgesBelow {n} L) where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Maybe.Base using (just)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (¬_)
import Data.Bool.Properties as BoolP

open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring using (RootTwo)

open import Word.Base
import Presentation.Base as PB
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim ; first-cong ; count-drop₂)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (D ; Z ; module ZR ; oddᶻ ; rbit ; √2ᶻ ; √2*≡ ; oddᶻ-+ ; rbit-+ ; oddᶻ-neg ; rbit-neg ; even⇒δ∣)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (_!_ ; scV ; Minimal ; Odd ; Even ; Odd⇒¬Even ; lde ; num)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
  using (nodd ; firstOdd ; nextSame ; negᶻ ; Same ; firstOdd-char ; firstOdd-spec ; firstOdd-cong ; nextSame-char ; nextSame-spec)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Hᶻ ; actV-H)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; _<ₗ_ ; <ₗ-irrefl)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (Apart)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Levels using (<ₗ-trans)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Local {n} using (actV-H-same)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (_≤ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (ne-𝕀)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Algorithm
  using (levelᶜ ; sylᶜ ; sylDataᶜ ; sylDataᶜ-neg ; sylDataᶜ-pos ; sylDataᶜ-pair ; third)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Squares {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.State {n}

open Close ih

private
  sym≢ : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
  sym≢ ne e = ne (≡.sym e)

  <-≢ : ∀ {x y : Fin n} → x < y → x ≢ y
  <-≢ lt ≡.refl = FinP.<-irrefl ≡.refl lt

  t≢f : true ≢ false
  t≢f ()

  xor-self : ∀ b → b xor b ≡ false
  xor-self true = ≡.refl
  xor-self false = ≡.refl

  xor-≢ : ∀ {a b} → a ≢ b → a xor b ≡ true
  xor-≢ {true} {true} ne = ⊥-elim (ne ≡.refl)
  xor-≢ {true} {false} _ = ≡.refl
  xor-≢ {false} {true} _ = ≡.refl
  xor-≢ {false} {false} ne = ⊥-elim (ne ≡.refl)

  -- A multiple of √2 has the parity of the cofactor in its √2-part.
  rbit-√2 : ∀ y → rbit (√2ᶻ ZR.* y) ≡ oddᶻ y
  rbit-√2 (RootTwo a b) = ≡.cong rbit (√2*≡ a b)

------------------------------------------------------------------------
-- Subcase 3.4, left to Case34

Hyp34 : Set
Hyp34 = ∀ (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (pv : pivot s ≡ just p) → levelᶜ s ≡ L →
        ∀ {z₀ z₁ : Fin n} → toℕ z₀ ≡ 0 → toℕ z₁ ≡ 1 → .(z01 : z₀ < z₁) → z₁ ≤ p →
        levelᶜ (actM (H-gen z₀ z₁ z01) s) ≤ₗ L →
        ∀ k′ → lde (col s p) ≡ suc k′ →
        Odd (num (col s p) ! z₀) → Odd (num (col s p) ! z₁) → rbit (num (col s p) ! z₀) ≢ rbit (num (col s p) ! z₁) →
        Path [ H-gen z₀ z₁ z01 ]ʷ s o

------------------------------------------------------------------------
-- The edge H[0,1] out of s

module Edge (h34 : Hyp34) (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (pv : pivot s ≡ just p) (eqL : levelᶜ s ≡ L)
            {z₀ z₁ : Fin n} (t0 : toℕ z₀ ≡ 0) (t1 : toℕ z₁ ≡ 1) (z₁≤p : z₁ ≤ p)
            (le : levelᶜ (actM (H-gen z₀ z₁ (≡.subst₂ ℕ._<_ (≡.sym t0) (≡.sym t1) (s≤s z≤n))) s) ≤ₗ L) where

  z01 : z₀ < z₁
  z01 = ≡.subst₂ ℕ._<_ (≡.sym t0) (≡.sym t1) (s≤s z≤n)

  G : Gen n
  G = H-gen z₀ z₁ z01

  Hz = [ G ]ʷ

  z₀≢z₁ : z₀ ≢ z₁
  z₀≢z₁ = <-≢ z01

  open At s o pv
  open Act G z₁≤p

  -- Nothing lies below z₀, nor between z₀ and z₁.
  none<0 : ∀ {x : Fin n} → ¬ (x < z₀)
  none<0 {x} x<0 = ℕP.n≮0 (≡.subst (toℕ x ℕ.<_) t0 x<0)

  none01 : ∀ {x : Fin n} → z₀ < x → x < z₁ → ⊥
  none01 {x} 0<x x<1 = ℕP.<-irrefl ≡.refl (ℕP.<-≤-trans (≡.subst (ℕ._< toℕ x) t0 0<x) (ℕP.≤-pred (≡.subst (toℕ x ℕ.<_) t1 x<1)))
    where open import Data.Empty using (⊥)

  -- Indices other than z₀ and z₁ come after both.
  after : ∀ {x : Fin n} → x ≢ z₀ → x ≢ z₁ → z₁ < x
  after {x} x≢0 x≢1 =
    ≡.subst (ℕ._< toℕ x) (≡.sym t1)
      (two≤ (toℕ x) (λ e → x≢0 (FinP.toℕ-injective (≡.trans e (≡.sym t0))))
                    (λ e → x≢1 (FinP.toℕ-injective (≡.trans e (≡.sym t1)))))
    where
    two≤ : ∀ m → m ≢ 0 → m ≢ 1 → 1 ℕ.< m
    two≤ zero ne0 _ = ⊥-elim (ne0 ≡.refl)
    two≤ (suc zero) _ ne1 = ⊥-elim (ne1 ≡.refl)
    two≤ (suc (suc m)) _ _ = s≤s (s≤s z≤n)

  z₀≤p : z₀ ≤ p
  z₀≤p = ℕP.<⇒≤ (ℕP.<-≤-trans z01 z₁≤p)

  set₂-00 : ∀ {w : Vec Z n} → w ! z₀ ≡ ZR.0# → w ! z₁ ≡ ZR.0# → set₂ z₀ z₁ ZR.0# ZR.0# w ≡ w
  set₂-00 {w} e0 e1 = vec-ext λ x → dec-elim (x FinP.≟ z₀)
    (λ { ≡.refl → ≡.trans (set₂-a x z₁ ZR.0# ZR.0# w) (≡.sym e0) })
    (λ x≢0 → dec-elim (x FinP.≟ z₁)
      (λ { ≡.refl → ≡.trans (set₂-b z₀ x ZR.0# ZR.0# w z₀≢z₁) (≡.sym e1) })
      (λ x≢1 → set₂-≢ z₀ z₁ ZR.0# ZR.0# w x≢0 x≢1))

  -- The normal steps out of s and r land below L.
  below-s : (h : Word (Gen n)) → sylᶜ s ≡ h → levelᶜ (actMʷ h s) <ₗ L
  below-s h e = ≡.subst (λ w → levelᶜ (actMʷ w s) <ₗ L) e (normal-below s o pv (inj₂ eqL))

  below-r : pivot r ≡ just p → (h : Word (Gen n)) → sylᶜ r ≡ h → levelᶜ (actMʷ h r) <ₗ L
  below-r pv′ h e = ≡.subst (λ w → levelᶜ (actMʷ w r) <ₗ L) e (normal-below r (ColOrth-actMʷ Hz o) pv′ le)

  -- An edge that goes up does not occur.
  up : ∀ {K c K′ c′} → L ≡ (suc (toℕ p) , K , c) → levelᶜ r ≡ (suc (toℕ p) , K′ , c′) →
       (K , c) Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot.<₂ (K′ , c′) → ⊥
  up {K} {c} {K′} {c′} eL er lt = by le
    where
    L<r : L <ₗ levelᶜ r
    L<r = ≡.subst₂ _<ₗ_ (≡.sym eL) (≡.sym er) (inj₂ (≡.refl , lt))
    by : levelᶜ r ≤ₗ L → ⊥
    by (inj₁ r<L) = <ₗ-irrefl (<ₗ-trans L<r r<L)
    by (inj₂ r≡L) = <ₗ-irrefl (≡.subst (L <ₗ_) r≡L L<r)

  -- The level of s.
  L≡ : L ≡ (suc (toℕ p) , k , third k W)
  L≡ = ≡.trans (≡.sym eqL) lvl

  colH : col r p ≡ scV (suc k) (Hᶻ z₀ z₁ W)
  colH = ≡.trans col-r (≡.trans (≡.cong (actV G) colW) (actV-H z₀ z₁ z01 k W))

  -- An odd entry of the column of r at exponent k + 1 raises the level.
  up-odd : ∀ x → Odd (Hᶻ z₀ z₁ W ! x) → ⊥
  up-odd x ox = up L≡ R.lvl′ (inj₁ (ℕP.n<1+n k))
    where
    min′ : Minimal (suc k) (Hᶻ z₀ z₁ W)
    min′ = inj₂ (x , ox)
    module R = Rep (suc k) (Hᶻ z₀ z₁ W) colH min′ (ne-𝕀 r p k (Hᶻ z₀ z₁ W) colH min′)

  -- When r has the syllable h of s, apart from G, they commute.
  same-syl : ∀ K → k ≡ K → (W′ : Vec Z n) → col r p ≡ scV K W′ → Minimal K W′ → col r p ≢ col 𝕀 p →
             sylDataᶜ p K W′ ≡ sylDataᶜ p K W → (h : Gen n) → sylᶜ s ≡ [ h ]ʷ → Apart h G → Path Hz s o
  same-syl K eK W′ colr′ min′ ne′ eS h e ap =
    commute G h ap s o (prograde h s o pv e) (prograde h r (ColOrth-actMʷ Hz o) R.pv′ e′)
      (below-r R.pv′ [ h ]ʷ e′) (below-s [ h ]ʷ e)
    where
    module R = Rep K W′ colr′ min′ ne′
    e′ : sylᶜ r ≡ [ h ]ʷ
    e′ = ≡.trans R.syl′ (≡.trans eS (≡.trans (≡.cong (λ K′ → sylDataᶜ p K′ W) (≡.sym eK)) (≡.trans (≡.sym syl) e)))

  -- Entry 0 of the column of r, at exponent k + 1.
  Hsum : Hᶻ z₀ z₁ W ! z₀ ≡ W ! z₀ ZR.+ W ! z₁
  Hsum = set₂-a z₀ z₁ _ _ _

  -- k = 0: a unit at 0 or 1 goes up (3.2); elsewhere G keeps the
  -- column (3.1.1).
  unit : ∀ m → Odd (W ! m) → (∀ y → y ≢ m → W ! y ≡ ZR.0#) → k ≡ 0 → (h : Gen n) → sylᶜ s ≡ [ h ]ʷ →
         (m ≢ z₀ → m ≢ z₁ → Apart h G) → Path Hz s o
  unit m om rest eK h e ap =
    dec-elim (m FinP.≟ z₀) (λ m≡0 → ⊥-elim (up-odd z₀ (odd0 m≡0))) λ m≢0 →
    dec-elim (m FinP.≟ z₁) (λ m≡1 → ⊥-elim (up-odd z₀ (odd1 m≡1))) λ m≢1 →
    same-syl 0 eK W (colr′ m≢0 m≢1) (inj₁ ≡.refl) (ne′ m≢0 m≢1) ≡.refl h e (ap m≢0 m≢1)
    where
    odd0 : m ≡ z₀ → Odd (Hᶻ z₀ z₁ W ! z₀)
    odd0 m≡0 = ≡.trans (≡.cong oddᶻ Hsum) (≡.trans (oddᶻ-+ (W ! z₀) (W ! z₁))
                 (≡.cong₂ _xor_ (≡.subst (λ x → Odd (W ! x)) m≡0 om)
                                (≡.cong oddᶻ (rest z₁ (λ e′ → z₀≢z₁ (≡.trans (≡.sym m≡0) (≡.sym e′)))))))
    odd1 : m ≡ z₁ → Odd (Hᶻ z₀ z₁ W ! z₀)
    odd1 m≡1 = ≡.trans (≡.cong oddᶻ Hsum) (≡.trans (oddᶻ-+ (W ! z₀) (W ! z₁))
                 (≡.cong₂ _xor_ (≡.cong oddᶻ (rest z₀ (λ e′ → z₀≢z₁ (≡.trans e′ m≡1))))
                                (≡.subst (λ x → Odd (W ! x)) m≡1 om)))
    colr′ : m ≢ z₀ → m ≢ z₁ → col r p ≡ scV 0 W
    colr′ m≢0 m≢1 =
      ≡.trans col-r (≡.trans (≡.cong (actV G) (≡.trans colW (≡.cong (λ K → scV K W) eK)))
        (≡.trans (actV-H-same z₀ z₁ z01 0 W ZR.0# ZR.0#
                    (≡.cong₂ ZR._+_ (rest z₀ (sym≢ m≢0)) (rest z₁ (sym≢ m≢1)))
                    (≡.cong₂ ZR._-_ (rest z₀ (sym≢ m≢0)) (rest z₁ (sym≢ m≢1))))
                 (≡.cong (scV 0) (set₂-00 (rest z₀ (sym≢ m≢0)) (rest z₁ (sym≢ m≢1))))))
    ne′ : m ≢ z₀ → m ≢ z₁ → col r p ≢ col 𝕀 p
    ne′ m≢0 m≢1 e″ = ne (≡.trans colW (≡.trans (≡.cong (λ K → scV K W) eK) (≡.trans (≡.sym (colr′ m≢0 m≢1)) e″)))

  case3 : Path Hz s o
  case3 = by view ≡.refl
    where
    by : ∀ {K} → View p K W → k ≡ K → Path Hz s o

    -- Unit columns: 3.1.1, or the unit at 0 or 1 (3.2).
    by (neg m e rest) eK = unit m (≡.cong oddᶻ e) rest eK (Z-gen m) sylN
      (λ m≢0 m≢1 → (m≢0 ∷ m≢1 ∷ []) ∷ [])
      where
      fo : firstOdd W ≡ just m
      fo = firstOdd-char W (≡.cong oddᶻ e) (λ x x<m → ≡.cong oddᶻ (rest x (<-≢ x<m)))
      sylN : sylᶜ s ≡ Zʷ m
      sylN = ≡.trans syl (≡.trans (≡.cong (λ K → sylDataᶜ p K W) eK) (sylDataᶜ-neg W fo (≡.cong negᶻ e)))
    by (pos m m<p e rest) eK = unit m (≡.cong oddᶻ e) rest eK (X-gen m p m<p) sylN
      (λ m≢0 m≢1 → (m≢0 ∷ m≢1 ∷ []) ∷ (sym≢ (<-≢ (ℕP.<-≤-trans z01 z₁≤p)) ∷ p≢1 m≢0 m≢1 ∷ []) ∷ [])
      where
      fo : firstOdd W ≡ just m
      fo = firstOdd-char W (≡.cong oddᶻ e) (λ x x<m → ≡.cong oddᶻ (rest x (<-≢ x<m)))
      sylN : sylᶜ s ≡ X m p m<p
      sylN = ≡.trans syl (≡.trans (≡.cong (λ K → sylDataᶜ p K W) eK) (sylDataᶜ-pos W fo (≡.cong negᶻ e) m<p))
      -- p = 1 would put m at 0.
      p≢1 : m ≢ z₀ → m ≢ z₁ → p ≢ z₁
      p≢1 m≢0 m≢1 p≡1 = ⊥-elim (ℕP.<-asym (after m≢0 m≢1) (≡.subst (m <_) p≡1 m<p))

    -- k > 0: by the parities of v₀ and v₁.
    by {suc k′} (pair i₁ i₂ fo nx i₁<i₂ i₂≤p) eK = by-par (oddᶻ (W ! z₀)) ≡.refl (oddᶻ (W ! z₁)) ≡.refl
      where
      L≡′ : L ≡ (suc (toℕ p) , suc k′ , nodd W)
      L≡′ = ≡.trans L≡ (≡.cong (λ K → suc (toℕ p) , K , third K W) eK)
      sylN : sylᶜ s ≡ H i₁ i₂ i₁<i₂
      sylN = ≡.trans syl (≡.trans (≡.cong (λ K → sylDataᶜ p K W) eK) (sylDataᶜ-pair {p = p} k′ W fo nx i₁<i₂))
      by-par : ∀ a → oddᶻ (W ! z₀) ≡ a → ∀ b → oddᶻ (W ! z₁) ≡ b → Path Hz s o
      -- 3.3 and 3.4
      by-par true o0 true o1 = dec-elim (rbit (W ! z₀) BoolP.≟ rbit (W ! z₁)) prog (h34 s o pv eqL t0 t1 z01 z₁≤p le k′ eK o0 o1)
        where
        prog : rbit (W ! z₀) ≡ rbit (W ! z₁) → Path Hz s o
        prog rb = prograde G s o pv
          (≡.trans syl (≡.trans (≡.cong (λ K → sylDataᶜ p K W) eK) (sylDataᶜ-pair {p = p} k′ W fo₀ nx₀ z01)))
          where
          fo₀ : firstOdd W ≡ just z₀
          fo₀ = firstOdd-char W o0 (λ x x<0 → ⊥-elim (none<0 x<0))
          nx₀ : nextSame z₀ W ≡ just z₁
          nx₀ = nextSame-char W z01 (o1 , ≡.sym rb) (λ x 0<x x<1 _ → none01 0<x x<1)
      -- 3.2: one odd entry
      by-par true o0 false e1 = ⊥-elim (up-odd z₀ (≡.trans (≡.cong oddᶻ Hsum) (≡.trans (oddᶻ-+ (W ! z₀) (W ! z₁)) (≡.cong₂ _xor_ o0 e1))))
      by-par false e0 true o1 = ⊥-elim (up-odd z₀ (≡.trans (≡.cong oddᶻ Hsum) (≡.trans (oddᶻ-+ (W ! z₀) (W ! z₁)) (≡.cong₂ _xor_ e0 o1))))
      -- Both even: G keeps them even if they have one residue (3.1.2),
      -- and makes them odd otherwise (3.2).
      by-par false e0 false e1 = dec-elim (rbit (W ! z₀) BoolP.≟ rbit (W ! z₁)) c312 c32
        where
        sumE : oddᶻ (W ! z₀ ZR.+ W ! z₁) ≡ false
        sumE = ≡.trans (oddᶻ-+ (W ! z₀) (W ! z₁)) (≡.cong₂ _xor_ e0 e1)
        difE : oddᶻ (W ! z₀ ZR.- W ! z₁) ≡ false
        difE = ≡.trans (oddᶻ-+ (W ! z₀) (ZR.- (W ! z₁))) (≡.cong₂ _xor_ e0 (≡.trans (oddᶻ-neg (W ! z₁)) e1))
        δα = even⇒δ∣ (W ! z₀ ZR.+ W ! z₁) sumE
        δβ = even⇒δ∣ (W ! z₀ ZR.- W ! z₁) difE
        α = proj₁ δα
        β = proj₁ δβ
        W″ = set₂ z₀ z₁ α β W
        colr″ : col r p ≡ scV (suc k′) W″
        colr″ = ≡.trans col-r (≡.trans (≡.cong (actV G) (≡.trans colW (≡.cong (λ K → scV K W) eK)))
                  (actV-H-same z₀ z₁ z01 (suc k′) W α β (proj₂ δα) (proj₂ δβ)))
        oα : oddᶻ α ≡ rbit (W ! z₀) xor rbit (W ! z₁)
        oα = ≡.trans (≡.sym (rbit-√2 α)) (≡.trans (≡.cong rbit (≡.sym (proj₂ δα))) (rbit-+ (W ! z₀) (W ! z₁)))
        oβ : oddᶻ β ≡ rbit (W ! z₀) xor rbit (W ! z₁)
        oβ = ≡.trans (≡.sym (rbit-√2 β)) (≡.trans (≡.cong rbit (≡.sym (proj₂ δβ)))
               (≡.trans (rbit-+ (W ! z₀) (ZR.- (W ! z₁))) (≡.cong (rbit (W ! z₀) xor_) (rbit-neg (W ! z₁)))))
        W″0 : W″ ! z₀ ≡ α
        W″0 = set₂-a z₀ z₁ α β W
        W″1 : W″ ! z₁ ≡ β
        W″1 = set₂-b z₀ z₁ α β W z₀≢z₁
        W″o : ∀ {x} → x ≢ z₀ → x ≢ z₁ → W″ ! x ≡ W ! x
        W″o x≢0 x≢1 = set₂-≢ z₀ z₁ α β W x≢0 x≢1
        -- 3.1.2
        c312 : rbit (W ! z₀) ≡ rbit (W ! z₁) → Path Hz s o
        c312 rb = same-syl (suc k′) eK W″ colr″ min″ (ne-𝕀 r p k′ W″ colr″ min″) eS (H-gen i₁ i₂ i₁<i₂) sylN
                    ((i₁≢0 ∷ i₁≢1 ∷ []) ∷ (i₂≢0 ∷ i₂≢1 ∷ []) ∷ [])
          where
          xo : rbit (W ! z₀) xor rbit (W ! z₁) ≡ false
          xo = ≡.trans (≡.cong (_xor rbit (W ! z₁)) rb) (xor-self (rbit (W ! z₁)))
          oddeq : ∀ x → oddᶻ (W ! x) ≡ oddᶻ (W″ ! x)
          oddeq x = dec-elim (x FinP.≟ z₀)
            (λ { ≡.refl → ≡.trans e0 (≡.sym (≡.trans (≡.cong oddᶻ W″0) (≡.trans oα xo))) })
            (λ x≢0 → dec-elim (x FinP.≟ z₁)
              (λ { ≡.refl → ≡.trans e1 (≡.sym (≡.trans (≡.cong oddᶻ W″1) (≡.trans oβ xo))) })
              (λ x≢1 → ≡.cong oddᶻ (≡.sym (W″o x≢0 x≢1))))
          o₁ = proj₁ (firstOdd-spec W fo)
          sm₂ = proj₁ (proj₂ (nextSame-spec W nx))
          ev≢ : ∀ {x y} → Odd (W ! x) → Even (W ! y) → x ≢ y
          ev≢ ox ey ≡.refl = t≢f (≡.trans (≡.sym ox) ey)
          i₁≢0 = ev≢ o₁ e0
          i₁≢1 = ev≢ o₁ e1
          i₂≢0 = ev≢ (proj₁ sm₂) e0
          i₂≢1 = ev≢ (proj₁ sm₂) e1
          fo″ : firstOdd W″ ≡ just i₁
          fo″ = ≡.trans (≡.sym (firstOdd-cong W W″ oddeq)) fo
          nx″ : nextSame i₁ W″ ≡ just i₂
          nx″ = nextSame-char W″ i₁<i₂
                  (≡.trans (≡.cong oddᶻ (W″o i₂≢0 i₂≢1)) (proj₁ sm₂) ,
                   ≡.trans (≡.cong rbit (W″o i₂≢0 i₂≢1)) (≡.trans (proj₂ sm₂) (≡.sym (≡.cong rbit (W″o i₁≢0 i₁≢1)))))
                  between
            where
            between : ∀ x → i₁ < x → x < i₂ → ¬ Same W″ i₁ x
            between x i₁<x x<i₂ (ox , rx) = dec-elim (x FinP.≟ z₀)
              (λ x≡0 → t≢f (≡.trans (≡.sym ox) (≡.trans (≡.sym (oddeq x)) (≡.subst (λ y → Even (W ! y)) (≡.sym x≡0) e0))))
              (λ x≢0 → dec-elim (x FinP.≟ z₁)
                (λ x≡1 → t≢f (≡.trans (≡.sym ox) (≡.trans (≡.sym (oddeq x)) (≡.subst (λ y → Even (W ! y)) (≡.sym x≡1) e1))))
                (λ x≢1 → proj₂ (proj₂ (nextSame-spec W nx)) x i₁<x x<i₂
                  (≡.trans (≡.sym (≡.cong oddᶻ (W″o x≢0 x≢1))) ox ,
                   ≡.trans (≡.sym (≡.cong rbit (W″o x≢0 x≢1))) (≡.trans rx (≡.cong rbit (W″o i₁≢0 i₁≢1))))))
          min″ : Minimal (suc k′) W″
          min″ = inj₂ (i₁ , ≡.trans (≡.cong oddᶻ (W″o i₁≢0 i₁≢1)) o₁)
          eS : sylDataᶜ p (suc k′) W″ ≡ sylDataᶜ p (suc k′) W
          eS = ≡.trans (sylDataᶜ-pair {p = p} k′ W″ fo″ nx″ i₁<i₂) (≡.sym (sylDataᶜ-pair {p = p} k′ W fo nx i₁<i₂))
        -- 3.2
        c32 : rbit (W ! z₀) ≢ rbit (W ! z₁) → Path Hz s o
        c32 rb = ⊥-elim (up L≡′ R.lvl′ (inj₂ (≡.refl , ≡.subst (nodd W ℕ.<_) (≡.sym cnt) (ℕP.≤-trans (ℕP.n<1+n (nodd W)) (ℕP.n≤1+n (suc (nodd W)))))))
          where
          xo : rbit (W ! z₀) xor rbit (W ! z₁) ≡ true
          xo = xor-≢ rb
          o0″ : Odd (W″ ! z₀)
          o0″ = ≡.trans (≡.cong oddᶻ W″0) (≡.trans oα xo)
          o1″ : Odd (W″ ! z₁)
          o1″ = ≡.trans (≡.cong oddᶻ W″1) (≡.trans oβ xo)
          cnt : nodd W″ ≡ suc (suc (nodd W))
          cnt = count-drop₂ (λ x → oddᶻ (W″ ! x)) (λ x → oddᶻ (W ! x)) z₀ z₁ z₀≢z₁ o0″ o1″ e0 e1
                  (λ x x≢0 x≢1 → ≡.cong oddᶻ (W″o x≢0 x≢1))
          min″ : Minimal (suc k′) W″
          min″ = inj₂ (z₀ , o0″)
          module R = Rep (suc k′) W″ colr″ min″ (ne-𝕀 r p k′ W″ colr″ min″)
