------------------------------------------------------------------------
-- Presentations of groups
--
-- The Main Lemma for the basic generator G = K_[0,1] (Case 2 of the
-- Appendix).  With w the numerator of the pivot column of s, k its
-- least denominator exponent, and j < ℓ the first odd entries of w:
--
-- * k = 0 and j ≥ 2, or k > 0, j ≥ 2 and G keeps w₀, w₁ even:
--   disjoint;
-- * k = 0 and j ≤ 1; k > 0, j = 0 and ℓ > 1; k > 0 and j = 1; and
--   k > 0, j ≥ 2 where G makes w₀, w₁ odd: retrograde, the normal
--   edge from G s is K†_[0,1];
-- * k > 0, j = 0 and ℓ = 1: the square closes through i_[0]³ i_[1]³
--   when q = 0 (case 2.2.1a) and through i_[1]³ X_[0,1] when q = 1
--   (case 2.2.1b).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)

module Examples.Groups.Clifford+CS-TwoLevel.CaseK {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base using (+_)
open import Data.List.Relation.Unary.All using ([] ; _∷_)
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count-cong)
open import Examples.Groups.Clifford+CS-TwoLevel.Column
open import Examples.Groups.Clifford+CS-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Clifford+CS-TwoLevel.Pivot using (pivot ; pivot-just ; pivot-char ; level ; _<ₗ_)
open import Examples.Groups.Clifford+CS-TwoLevel.Syllable
  using (syl ; step ; Beyond-actM ; eᶻ ; eᶻ-! ; δᶻ-refl ; δᶻ-≢ ; col𝕀≡)
open import Examples.Groups.Clifford+CS-TwoLevel.Step using (scV-γmap)
open import Examples.Groups.Clifford+CS-TwoLevel.Levels using (Bℓ)
open import Examples.Groups.Clifford+CS-TwoLevel.Derived {n}
  using (K†-K ; K≈i³i³K† ; K†LK≈L³XK†L ; Apartʷ ; Apartʷʷ)
open import Examples.Groups.Clifford+CS-TwoLevel.Basic {n} using (Letters≤)
open import Examples.Groups.Clifford+CS-TwoLevel.Reduction {n} using (Square ; Below ; path-ε)
open import Examples.Groups.Clifford+CS-TwoLevel.MainTools {n}
  using (pivot-keep ; lt-step ; square-by ; square-disjoint′ ; square-retro ; square-syl ;
         syl-of ; level-of ; word-below-all ; above-apart′ ; pivot-stay ; ne-𝕀 ; bℓ-below)
import Examples.Groups.Clifford+CS-TwoLevel.PivotColumn as PivotColumn

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

  open ZS using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

  -- γ x = i x + x and γ (i x) = i x - x.
  γ*≡ : ∀ x → γᶻ ZR.* x ≡ ⅈᶻ ZR.* x ZR.+ x
  γ*≡ x = ZS.solve 2 (λ ι x → (ι :+ con (+ 1)) :* x := ι :* x :+ x) ≡.refl ⅈᶻ x

  γⅈ*≡ : ∀ x → γᶻ ZR.* (ⅈᶻ ZR.* x) ≡ ⅈᶻ ZR.* x ZR.- x
  γⅈ*≡ x = ≡.trans (≡.sym (ZR.*-assoc γᶻ ⅈᶻ x))
                   (ZS.solve 2 (λ ι x → (ι :- con (+ 1)) :* x := ι :* x :- x) ≡.refl ⅈᶻ x)

  -- Parities of sums and differences.
  odd-sum : ∀ x y → oddᶻ x xor oddᶻ y ≡ true → Odd (x ZR.+ y)
  odd-sum x y e = ≡.trans (oddᶻ-+ x y) e

  par-dif : ∀ x y → oddᶻ (x ZR.- y) ≡ oddᶻ (x ZR.+ y)
  par-dif x y = ≡.trans (oddᶻ-+ x (ZR.- y)) (≡.trans (≡.cong (oddᶻ x xor_) (oddᶻ-neg y)) (≡.sym (oddᶻ-+ x y)))

------------------------------------------------------------------------
-- The case

module _ (a b : Fin n) (a0 : toℕ a ≡ 0) (b1 : toℕ b ≡ 1)
         (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p) where

  open PivotColumn s o ps

  private
    ab : a < b
    ab = ≡.subst₂ ℕ._<_ (≡.sym a0) (≡.sym b1) (s≤s z≤n)

    G : Gen n
    G = K-gen a b ab

    r = actM G s

    a≢b : a ≢ b
    a≢b e = FinP.<-irrefl e ab

    none<a : ∀ {x : Fin n} → x < a → ⊥
    none<a {x} x<a = ℕP.n≮0 (≡.subst (toℕ x ℕ.<_) a0 x<a)

    none-ab : ∀ {x : Fin n} → a < x → x < b → ⊥
    none-ab {x} a<x x<b =
      ℕP.<-irrefl (≡.trans a0 (≡.sym (ℕP.n<1⇒n≡0 (≡.subst (toℕ x ℕ.<_) b1 x<b)))) a<x

    -- An index above 0 other than 1 is above 1.
    b< : ∀ {x : Fin n} → a < x → toℕ x ≢ 1 → b < x
    b< {x} a<x x≢1 = ≡.subst (ℕ._< toℕ x) (≡.sym b1)
                       (ℕP.≤∧≢⇒< (≡.subst (ℕ._< toℕ x) a0 a<x) (λ e → x≢1 (≡.sym e)))

    ------------------------------------------------------------------
    -- G on numerators

    -- The column of r = K_[0,1] s at p.
    col-r : ∀ {K} {U : Vec Z n} → v ≡ scV K U → col r p ≡ scV (suc K) (Kᶻ a b U)
    col-r {K} {U} e = ≡.trans (col-actM G s p) (≡.trans (≡.cong (actV G) e) (actV-K a b ab K U))

    Kᶻ-a : (U : Vec Z n) → Kᶻ a b U ! a ≡ U ! a ZR.+ U ! b
    Kᶻ-a U = set₂-a a b (U ! a ZR.+ U ! b) (U ! a ZR.- U ! b) (Vec.map (γᶻ ZR.*_) U)

    Kᶻ-b : (U : Vec Z n) → Kᶻ a b U ! b ≡ U ! a ZR.- U ! b
    Kᶻ-b U = set₂-b a b (U ! a ZR.+ U ! b) (U ! a ZR.- U ! b) (Vec.map (γᶻ ZR.*_) U) a≢b

    -- When γ divides the new entries a and b, K at scale k + 1 is the
    -- vector with those entries divided at scale k.
    Kᶻ-γ : (U : Vec Z n) (y y′ : Z) → U ! a ZR.+ U ! b ≡ γᶻ ZR.* y → U ! a ZR.- U ! b ≡ γᶻ ZR.* y′ →
           Kᶻ a b U ≡ Vec.map (γᶻ ZR.*_) (set₂ a b y y′ U)
    Kᶻ-γ U y y′ ey ey′ = vec-ext λ x → at x (x FinP.≟ a) (x FinP.≟ b)
      where
      V = set₂ a b y y′ U
      at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Kᶻ a b U ! x ≡ Vec.map (γᶻ ZR.*_) V ! x
      at x (yes ≡.refl) _ =
        ≡.trans (Kᶻ-a U) (≡.trans ey (≡.trans (≡.cong (γᶻ ZR.*_) (≡.sym (set₂-a a b y y′ U)))
                                                (≡.sym (VecP.lookup-map a (γᶻ ZR.*_) V))))
      at x (no _) (yes ≡.refl) =
        ≡.trans (Kᶻ-b U) (≡.trans ey′ (≡.trans (≡.cong (γᶻ ZR.*_) (≡.sym (set₂-b a b y y′ U a≢b)))
                                                 (≡.sym (VecP.lookup-map b (γᶻ ZR.*_) V))))
      at x (no x≢a) (no x≢b) =
        ≡.trans (set₂-≢ a b (U ! a ZR.+ U ! b) (U ! a ZR.- U ! b) (Vec.map (γᶻ ZR.*_) U) x≢a x≢b)
          (≡.trans (VecP.lookup-map x (γᶻ ZR.*_) U)
            (≡.trans (≡.cong (γᶻ ZR.*_) (≡.sym (set₂-≢ a b y y′ U x≢a x≢b)))
                     (≡.sym (VecP.lookup-map x (γᶻ ZR.*_) V))))

    -- Entries a and b of w even: w_a = γ u, w_b = γ z.
    Kᶻ-even : (u z : Z) → W ! a ≡ γᶻ ZR.* u → W ! b ≡ γᶻ ZR.* z →
              Kᶻ a b W ≡ Vec.map (γᶻ ZR.*_) (set₂ a b (u ZR.+ z) (u ZR.- z) W)
    Kᶻ-even u z eu ez = Kᶻ-γ W (u ZR.+ z) (u ZR.- z)
      (≡.trans (≡.cong₂ ZR._+_ eu ez) (≡.sym (ZR.distribˡ γᶻ u z)))
      (≡.trans (≡.cong₂ ZR._-_ eu ez) (ZS.solve 3 (λ g u z → g :* u :- g :* z := g :* (u :- z)) ≡.refl γᶻ u z))

    -- Entries a and b of w odd with w_a - i w_b = 2 c.
    Kᶻ-odd : (c : Z) → W ! a ZR.- ⅈᶻ ZR.* (W ! b) ≡ 2ᶻ ZR.* c →
             Kᶻ a b W ≡ Vec.map (γᶻ ZR.*_) (set₂ a b ((ZR.1# ZR.- ⅈᶻ) ZR.* c ZR.+ W ! b)
                                                      ((ZR.1# ZR.- ⅈᶻ) ZR.* c ZR.+ ⅈᶻ ZR.* (W ! b)) W)
    Kᶻ-odd c ec = Kᶻ-γ W _ _ sum-eq dif-eq
      where
      m = ZR.1# ZR.- ⅈᶻ
      x = W ! b
      split : ∀ (d : Z) → W ! a ZR.+ d ≡ (W ! a ZR.- ⅈᶻ ZR.* x) ZR.+ (ⅈᶻ ZR.* x ZR.+ d)
      split d = ZS.solve 3 (λ a′ y d → a′ :+ d := (a′ :- y) :+ (y :+ d)) ≡.refl (W ! a) (ⅈᶻ ZR.* x) d
      sum-eq : W ! a ZR.+ x ≡ γᶻ ZR.* (m ZR.* c ZR.+ x)
      sum-eq = ≡.trans (split x) (≡.trans (≡.cong (ZR._+ (ⅈᶻ ZR.* x ZR.+ x)) ec)
        (≡.trans (≡.cong (2ᶻ ZR.* c ZR.+_) (≡.sym (γ*≡ x)))
          (≡.sym (ZS.solve 4 (λ g m c x → g :* (m :* c :+ x) := (g :* m) :* c :+ g :* x) ≡.refl γᶻ m c x))))
      dif-eq : W ! a ZR.- x ≡ γᶻ ZR.* (m ZR.* c ZR.+ ⅈᶻ ZR.* x)
      dif-eq = ≡.trans (split (ZR.- x)) (≡.trans (≡.cong (ZR._+ (ⅈᶻ ZR.* x ZR.- x)) ec)
        (≡.trans (≡.cong (2ᶻ ZR.* c ZR.+_) (≡.sym (γⅈ*≡ x)))
          (≡.sym (ZS.solve 4 (λ g m c y → g :* (m :* c :+ y) := (g :* m) :* c :+ g :* y) ≡.refl γᶻ m c (ⅈᶻ ZR.* x)))))

    ------------------------------------------------------------------
    -- The syllable K†_[0,1] i_[1]ᑫ

    syl-ab : (M : Matrix n n D) {p′ : Fin n} → pivot M ≡ just p′ → ∀ k′ (U : Vec Z n) →
             col M p′ ≡ scV (suc k′) U → Odd (U ! a) → Odd (U ! b) →
             syl M ≡ K† a b ab • i b ^ qOf (U ! a) (U ! b)
    syl-ab M {p′} pv k′ U eq oa ob =
      ≡.trans (syl-of M pv (suc k′) U eq (inj₂ (a , oa))) (sylData-pair {p = p′} k′ U fo nx ab)
      where
      fo : firstOdd U ≡ just a
      fo = firstOdd-char U oa (λ x x<a → ⊥-elim (none<a x<a))
      nx : nextOdd a U ≡ just b
      nx = nextOdd-char U ab ob (λ x a<x x<b → ⊥-elim (none-ab a<x x<b))

    ------------------------------------------------------------------
    -- Retrograde: the normal edge from r is K†_[0,1]

    retro : ∀ {p′} → pivot r ≡ just p′ → ∀ k′ (U : Vec Z n) → col r p′ ≡ scV (suc k′) U →
            Odd (U ! a) → Odd (U ! b) → qOf (U ! a) (U ! b) ≡ 0 → Square G s o
    retro pr k′ U eq oa ob q0 = square-retro G s o ps pr back
      where
      back : syl r • [ G ]ʷ ≈ ε
      back = trans (cleft refl′ (≡.trans (syl-ab r pr k′ U eq oa ob) (≡.cong (λ z → K† a b ab • i b ^ z) q0)))
                   (trans (cleft right-unit) (K†-K ab))

    -- Exactly one of U_a, U_b is odd.
    retro-K : ∀ {p′} → pivot r ≡ just p′ → ∀ k′ (U : Vec Z n) → col r p′ ≡ scV (suc k′) (Kᶻ a b U) →
              oddᶻ (U ! a) xor oddᶻ (U ! b) ≡ true → Square G s o
    retro-K pr k′ U eq e = retro pr k′ (Kᶻ a b U) eq
      (≡.subst Odd (≡.sym (Kᶻ-a U)) (odd-sum (U ! a) (U ! b) e))
      (≡.subst Odd (≡.sym (Kᶻ-b U)) (≡.trans (par-dif (U ! a) (U ! b)) (odd-sum (U ! a) (U ! b) e)))
      (≡.trans (≡.cong₂ qOf (Kᶻ-a U) (Kᶻ-b U)) (qOf-+- (U ! a) (U ! b)))

    ------------------------------------------------------------------
    -- Disjoint: w_a, w_b and the new entries even

    disjoint : ∀ {j} (u z : Z) → W ! a ≡ γᶻ ZR.* u → W ! b ≡ γᶻ ZR.* z → Even (u ZR.+ z) →
               firstOdd W ≡ just j → b < j → Square G s o
    disjoint {j} u z eu ez ev fo b<j = square-disjoint′ G s o ps pr syl-r apart lv
      where
      W″ = set₂ a b (u ZR.+ z) (u ZR.- z) W
      j≤p : j ≤ p
      j≤p = odd≤ (proj₁ (firstOdd-spec W fo))
      pr : pivot r ≡ just p
      pr = pivot-keep G s (ℕP.<-≤-trans b<j j≤p) ps
      col-r″ : col r p ≡ scV (lde v) W″
      col-r″ = ≡.trans (col-r v≡) (≡.trans (≡.cong (scV (suc (lde v))) (Kᶻ-even u z eu ez)) (scV-γmap (lde v) W″))
      par : ∀ x → oddᶻ (W″ ! x) ≡ oddᶻ (W ! x)
      par x = at x (x FinP.≟ a) (x FinP.≟ b)
        where
        at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → oddᶻ (W″ ! x) ≡ oddᶻ (W ! x)
        at x (yes ≡.refl) _ = ≡.trans (≡.cong oddᶻ (set₂-a a b (u ZR.+ z) (u ZR.- z) W))
                                (≡.trans ev (≡.sym (≡.trans (≡.cong oddᶻ eu) (γ∣⇒even (u , ≡.refl)))))
        at x (no _) (yes ≡.refl) = ≡.trans (≡.cong oddᶻ (set₂-b a b (u ZR.+ z) (u ZR.- z) W a≢b))
                                     (≡.trans (≡.trans (par-dif u z) ev)
                                              (≡.sym (≡.trans (≡.cong oddᶻ ez) (γ∣⇒even (z , ≡.refl)))))
        at x (no x≢a) (no x≢b) = ≡.cong oddᶻ (set₂-≢ a b (u ZR.+ z) (u ZR.- z) W x≢a x≢b)
      agree : ∀ x → Odd (W″ ! x) → W″ ! x ≡ W ! x
      agree x ox = at (x FinP.≟ a) (x FinP.≟ b)
        where
        at : Dec (x ≡ a) → Dec (x ≡ b) → W″ ! x ≡ W ! x
        at (yes x≡a) _ = ⊥-elim (Odd⇒¬Even {W″ ! x} ox
                           (≡.trans (par x) (≡.trans (≡.cong (λ y → oddᶻ (W ! y)) x≡a)
                                                     (≡.trans (≡.cong oddᶻ eu) (γ∣⇒even (u , ≡.refl))))))
        at (no _) (yes x≡b) = ⊥-elim (Odd⇒¬Even {W″ ! x} ox
                                (≡.trans (par x) (≡.trans (≡.cong (λ y → oddᶻ (W ! y)) x≡b)
                                                          (≡.trans (≡.cong oddᶻ ez) (γ∣⇒even (z , ≡.refl))))))
        at (no x≢a) (no x≢b) = set₂-≢ a b (u ZR.+ z) (u ZR.- z) W x≢a x≢b
      min″ : Minimal (lde v) W″
      min″ = at min
        where
        at : Minimal (lde v) W → Minimal (lde v) W″
        at (inj₁ e) = inj₁ e
        at (inj₂ (x , ox)) = inj₂ (x , ≡.trans (par x) ox)
      syl-r : syl r ≡ syl s
      syl-r = ≡.trans (syl-of r pr (lde v) W″ col-r″ min″)
                (≡.trans (sylData-agree p (lde v) W″ W par agree) (≡.sym syl≡))
      lv : level r ≡ level s
      lv = ≡.trans (level-of r pr (lde v) W″ col-r″ min″)
             (≡.trans (≡.cong (λ m → (suc (toℕ p) , lde v , m))
                              (count-cong (λ x → oddᶻ (W″ ! x)) (λ x → oddᶻ (W ! x)) par))
                      (≡.sym lvl))
      apart : Apartʷʷ (syl s) [ G ]ʷ
      apart = ≡.subst (λ w → Apartʷ w G) (≡.sym syl≡)
                (above-apart′ (sylData p (lde v) W) (sylData-above p (lde v) W fo j≤p) G
                  (ℕP.<-trans ab b<j ∷ b<j ∷ []))

  ----------------------------------------------------------------------
  -- k = 0

  private
    case0 : lde v ≡ 0 → Square G s o
    case0 k0 = go (unit k0)
      where
      v≡₀ : v ≡ scV 0 W
      v≡₀ = ≡.trans v≡ (≡.cong (λ k → scV k W) k0)

      -- The unit at a or b: retrograde, with the pivot at p or, if
      -- p = 0, at 1.
      retro0 : oddᶻ (W ! a) xor oddᶻ (W ! b) ≡ true → Square G s o
      retro0 e = by-p (FinP.<-cmp p b)
        where
        stay : b ≤ p → Square G s o
        stay b≤p = retro-K pr 0 W (col-r v≡₀) e
          where
          pr : pivot r ≡ just p
          pr = pivot-stay G s b≤p ps
                 (ne-𝕀 r p 0 (Kᶻ a b W) (col-r v≡₀)
                   (inj₂ (a , ≡.subst Odd (≡.sym (Kᶻ-a W)) (odd-sum (W ! a) (W ! b) e))))
        low : p < b → Square G s o
        low p<b = retro-K pr′ 0 (eᶻ b) colb e′
          where
          colb : col r b ≡ scV 1 (Kᶻ a b (eᶻ b))
          colb = ≡.trans (col-actM G s b)
                   (≡.trans (≡.cong (actV G) (≡.trans (proj₂ (pivot-just s ps) b p<b) (col𝕀≡ b)))
                            (actV-K a b ab 0 (eᶻ b)))
          e′ : oddᶻ (eᶻ b ! a) xor oddᶻ (eᶻ b ! b) ≡ true
          e′ = ≡.cong₂ _xor_ (≡.cong oddᶻ (≡.trans (eᶻ-! b a) (δᶻ-≢ a≢b)))
                             (≡.cong oddᶻ (≡.trans (eᶻ-! b b) (δᶻ-refl b)))
          pr′ : pivot r ≡ just b
          pr′ = pivot-char r
                  (ne-𝕀 r b 0 (Kᶻ a b (eᶻ b)) colb
                    (inj₂ (a , ≡.subst Odd (≡.sym (Kᶻ-a (eᶻ b))) (odd-sum (eᶻ b ! a) (eᶻ b ! b) e′))))
                  (Beyond-actM G {M = s} FinP.≤-refl
                    (λ c b<c → proj₂ (pivot-just s ps) c (ℕP.<-trans p<b b<c)))
        by-p : Tri (p < b) (p ≡ b) (b < p) → Square G s o
        by-p (tri< p<b _ _) = low p<b
        by-p (tri≈ _ p≡b _) = stay (≡.subst (b ≤_) (≡.sym p≡b) FinP.≤-refl)
        by-p (tri> _ _ b<p) = stay (ℕP.<⇒≤ b<p)

      go : (∃ λ m → firstOdd W ≡ just m × ∃ λ t → t ℕ.< 4 × W ! m ≡ ⅈᶻ ^ᶻ t × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) →
           Square G s o
      go (m , fo , t , t<4 , um , rest) = by-m (FinP.<-cmp b m)
        where
        om : Odd (W ! m)
        om = proj₁ (firstOdd-spec W fo)
        by-m : Tri (b < m) (b ≡ m) (m < b) → Square G s o
        by-m (tri< b<m _ _) =
          disjoint ZR.0# ZR.0# (rest a (λ e → FinP.<-irrefl e (ℕP.<-trans ab b<m)))
                               (rest b (λ e → FinP.<-irrefl e b<m)) ≡.refl fo b<m
        by-m (tri≈ _ b≡m _) =
          retro0 (≡.cong₂ _xor_ (≡.cong oddᶻ (rest a (λ e → a≢b (≡.trans e (≡.sym b≡m)))))
                                (≡.subst (λ y → oddᶻ (W ! y) ≡ true) (≡.sym b≡m) om))
        by-m (tri> _ _ m<b) =
          retro0 (≡.cong₂ _xor_ (≡.subst (λ y → oddᶻ (W ! y) ≡ true) m≡a om)
                                (≡.cong oddᶻ (rest b (λ e → a≢b (≡.trans (≡.sym m≡a) (≡.sym e))))))
          where
          m≡a : m ≡ a
          m≡a = FinP.toℕ-injective (≡.trans (ℕP.n<1⇒n≡0 (≡.subst (toℕ m ℕ.<_) b1 m<b)) (≡.sym a0))

  ----------------------------------------------------------------------
  -- k > 0

  private
    case+ : ∀ {K′} → lde v ≡ suc K′ → Square G s o
    case+ {K′} ks = at-j first
      where
      v≡ₖ : v ≡ scV (suc K′) W
      v≡ₖ = ≡.trans v≡ (≡.cong (λ k → scV k W) ks)

      bb : b ≤ p → Bℓ b <ₗ level s
      bb b≤p = ≡.subst (Bℓ b <ₗ_) (≡.sym lvl) (bℓ-below (nodd W) (≡.subst (0 ℕ.<_) (≡.sym ks) (s≤s z≤n)) b≤p)

      below : b ≤ p → (G′ : Word (Gen n)) → Letters≤ b G′ → Below (level s) G′ (step s)
      below b≤p G′ h = word-below-all G′ h (step s) (lt-step s o ps) (bb b≤p)

      -- j = 0, ℓ = 1.
      pair01 : firstOdd W ≡ just a → nextOdd a W ≡ just b → Square G s o
      pair01 fo nx = by-q (qOf (W ! a) (W ! b)) (qOf-≤1 (W ! a) (W ! b)) ≡.refl
        where
        oa : Odd (W ! a)
        oa = proj₁ (firstOdd-spec W fo)
        ob : Odd (W ! b)
        ob = proj₁ (proj₂ (nextOdd-spec W nx))
        b≤p : b ≤ p
        b≤p = odd≤ ob
        a≤b : toℕ a ℕ.≤ toℕ b
        a≤b = ℕP.<⇒≤ ab
        syl-s : syl s ≡ K† a b ab • i b ^ qOf (W ! a) (W ! b)
        syl-s = ≡.trans syl≡ (≡.trans (≡.cong (λ k → sylData p k W) ks) (sylData-pair {p = p} K′ W fo nx ab))

        by-q : ∀ q → q ℕ.≤ 1 → qOf (W ! a) (W ! b) ≡ q → Square G s o
        -- q = 0: K_[0,1] = i_[0]³ i_[1]³ K†_[0,1], and r is reached from t.
        by-q 0 _ e =
          square-by G s o ε (i a ^ 3 • i b ^ 3) (path-ε r (ColOrth-actMʷ [ G ]ʷ o))
            (below b≤p (i a ^ 3 • i b ^ 3) ((a≤b , a≤b , a≤b) , (ℕP.≤-refl , ℕP.≤-refl , ℕP.≤-refl)))
            (trans rel (cright refl′ (≡.sym (≡.trans syl-s (≡.cong (λ z → K† a b ab • i b ^ z) e)))))
          where
          rel : ε • K a b ab ≈ (i a ^ 3 • i b ^ 3) • (K† a b ab • ε)
          rel = trans left-unit (trans (K≈i³i³K† ab) (by-assoc auto))
        -- q = 1: the normal edge from r is K†_[0,1] i_[1] too.
        by-q 1 _ e = with-c (≡.subst (λ q → 2∣ (W ! a ZR.- (ⅈᶻ ^ᶻ q) ZR.* (W ! b))) e
                                     (qOf-spec (W ! a) (W ! b) oa ob))
          where
          with-c : 2∣ (W ! a ZR.- ⅈᶻ ZR.* (W ! b)) → Square G s o
          with-c (c , ec) =
            square-syl G s o (K† a b ab • i b) (i b ^ 3 • X a b ab) pr syl-r
              (below b≤p (i b ^ 3 • X a b ab) ((ℕP.≤-refl , ℕP.≤-refl , ℕP.≤-refl) , ℕP.≤-refl))
              (trans rel (cright refl′ (≡.sym (≡.trans syl-s (≡.cong (λ z → K† a b ab • i b ^ z) e)))))
            where
            m = ZR.1# ZR.- ⅈᶻ
            y = m ZR.* c ZR.+ W ! b
            y′ = m ZR.* c ZR.+ ⅈᶻ ZR.* (W ! b)
            W″ = set₂ a b y y′ W
            col-r″ : col r p ≡ scV (suc K′) W″
            col-r″ = ≡.trans (col-r v≡ₖ) (≡.trans (≡.cong (scV (suc (suc K′))) (Kᶻ-odd c ec)) (scV-γmap (suc K′) W″))
            -- m c is even.
            even-mc : Even (m ZR.* c)
            even-mc = oddᶻ-* m c
            oy : Odd (W″ ! a)
            oy = ≡.trans (≡.cong oddᶻ (set₂-a a b y y′ W))
                   (≡.trans (oddᶻ-+ (m ZR.* c) (W ! b)) (≡.cong₂ _xor_ even-mc ob))
            oy′ : Odd (W″ ! b)
            oy′ = ≡.trans (≡.cong oddᶻ (set₂-b a b y y′ W a≢b))
                    (≡.trans (oddᶻ-+ (m ZR.* c) (ⅈᶻ ZR.* (W ! b)))
                      (≡.cong₂ _xor_ even-mc (≡.trans (oddᶻ-* ⅈᶻ (W ! b)) (≡.cong (true Data.Bool.Base.∧_) ob))))
            pr : pivot r ≡ just p
            pr = pivot-stay G s b≤p ps (ne-𝕀 r p K′ W″ col-r″ (inj₂ (a , oy)))
            syl-r : syl r ≡ K† a b ab • i b
            syl-r = ≡.trans (syl-ab r pr K′ W″ col-r″ oy oy′)
                      (≡.cong (λ z → K† a b ab • i b ^ z)
                        (≡.trans (≡.cong₂ qOf (set₂-a a b y y′ W) (set₂-b a b y y′ W a≢b))
                                 (qOf-shift (m ZR.* c) (W ! b) ob)))
            rel : (K† a b ab • i b) • K a b ab ≈ (i b ^ 3 • X a b ab) • (K† a b ab • i b)
            rel = trans assoc (trans (K†LK≈L³XK†L ab) (by-assoc auto))
        by-q (suc (suc _)) (s≤s ()) _

      -- j = 0.
      at-a : firstOdd W ≡ just a → Square G s o
      at-a fo = go (second ks fo)
        where
        oa : Odd (W ! a)
        oa = proj₁ (firstOdd-spec W fo)
        go : (∃ λ ℓ → nextOdd a W ≡ just ℓ) → Square G s o
        go (ℓ , nx) = by-ℓ (toℕ ℓ ℕP.≟ 1)
          where
          a<ℓ : a < ℓ
          a<ℓ = proj₁ (nextOdd-spec W nx)
          ℓ≤p : ℓ ≤ p
          ℓ≤p = odd≤ (proj₁ (proj₂ (nextOdd-spec W nx)))
          by-ℓ : Dec (toℕ ℓ ≡ 1) → Square G s o
          by-ℓ (yes ℓ1) =
            pair01 fo (≡.subst (λ x → nextOdd a W ≡ just x) (FinP.toℕ-injective (≡.trans ℓ1 (≡.sym b1))) nx)
          -- ℓ > 1: retrograde.
          by-ℓ (no ℓ≢1) = retro-K (pivot-keep G s (ℕP.<-≤-trans b<ℓ ℓ≤p) ps) (suc K′) W (col-r v≡ₖ)
                            (≡.cong₂ _xor_ oa (proj₂ (proj₂ (nextOdd-spec W nx)) b ab b<ℓ))
            where
            b<ℓ : b < ℓ
            b<ℓ = b< a<ℓ ℓ≢1

      -- j = 1: retrograde.
      at-b : firstOdd W ≡ just b → Square G s o
      at-b fo = go (second ks fo)
        where
        go : (∃ λ ℓ → nextOdd b W ≡ just ℓ) → Square G s o
        go (ℓ , nx) = retro-K (pivot-keep G s (ℕP.<-≤-trans (proj₁ (nextOdd-spec W nx))
                                                            (odd≤ (proj₁ (proj₂ (nextOdd-spec W nx))))) ps)
                              (suc K′) W (col-r v≡ₖ)
                              (≡.cong₂ _xor_ (proj₂ (firstOdd-spec W fo) a ab) (proj₁ (firstOdd-spec W fo)))

      -- j > 1: w_a and w_b are even.
      above : ∀ {j} → firstOdd W ≡ just j → b < j → Square G s o
      above {j} fo b<j = go (even⇒γ∣ (W ! a) (proj₂ (firstOdd-spec W fo) a (ℕP.<-trans ab b<j)))
                            (even⇒γ∣ (W ! b) (proj₂ (firstOdd-spec W fo) b b<j))
        where
        j≤p : j ≤ p
        j≤p = odd≤ (proj₁ (firstOdd-spec W fo))
        go : γ∣ (W ! a) → γ∣ (W ! b) → Square G s o
        go (u , eu) (z , ez) = by-par (oddᶻ (u ZR.+ z)) ≡.refl
          where
          W″ = set₂ a b (u ZR.+ z) (u ZR.- z) W
          by-par : (x : Bool) → oddᶻ (u ZR.+ z) ≡ x → Square G s o
          by-par false ev = disjoint u z eu ez ev fo b<j
          -- The new entries a and b are odd: retrograde.
          by-par true od =
            retro (pivot-keep G s (ℕP.<-≤-trans b<j j≤p) ps) K′ W″ col-r″
              (≡.trans (≡.cong oddᶻ (set₂-a a b (u ZR.+ z) (u ZR.- z) W)) od)
              (≡.trans (≡.cong oddᶻ (set₂-b a b (u ZR.+ z) (u ZR.- z) W a≢b)) (≡.trans (par-dif u z) od))
              (≡.trans (≡.cong₂ qOf (set₂-a a b (u ZR.+ z) (u ZR.- z) W) (set₂-b a b (u ZR.+ z) (u ZR.- z) W a≢b))
                       (qOf-+- u z))
            where
            col-r″ : col r p ≡ scV (suc K′) W″
            col-r″ = ≡.trans (col-r v≡ₖ) (≡.trans (≡.cong (scV (suc (suc K′))) (Kᶻ-even u z eu ez))
                                                  (scV-γmap (suc K′) W″))

      at-j : (∃ λ j → firstOdd W ≡ just j) → Square G s o
      at-j (j , fo) = by-j (toℕ j ℕP.≟ 0) (toℕ j ℕP.≟ 1)
        where
        by-j : Dec (toℕ j ≡ 0) → Dec (toℕ j ≡ 1) → Square G s o
        by-j (yes j0) _ =
          at-a (≡.subst (λ x → firstOdd W ≡ just x) (FinP.toℕ-injective (≡.trans j0 (≡.sym a0))) fo)
        by-j (no _) (yes j1) =
          at-b (≡.subst (λ x → firstOdd W ≡ just x) (FinP.toℕ-injective (≡.trans j1 (≡.sym b1))) fo)
        by-j (no j≢0) (no j≢1) = above fo (b< (≡.subst (ℕ._< toℕ j) (≡.sym a0) (ℕP.n≢0⇒n>0 j≢0)) j≢1)

  ----------------------------------------------------------------------
  -- The case

  caseK : Square (K-gen a b ab) s o
  caseK = by-k (lde v) ≡.refl
    where
    by-k : ∀ k → lde v ≡ k → Square G s o
    by-k zero k0 = case0 k0
    by-k (suc K′) ks = case+ ks
