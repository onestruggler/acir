------------------------------------------------------------------------
-- Presentations of groups
--
-- The Main Lemma for the basic generator G = H_[0,1] (Case 1 of the
-- proof of Lemma 3.10).  With w the numerator of the pivot column of
-- s, k its least δ-exponent, and j < ℓ the first odd entries of w.  H
-- takes the entries w₀, w₁ to λω (w₀ ± w₁) at the exponent k + 2:
--
-- * exactly one of w₀, w₁ odd (k = 0 and j ≤ 1; k > 0, j = 0 and
--   ℓ > 1; k > 0 and j = 1): the new entries are odd and congruent
--   modulo δ³, so the normal edge from G s is H_[0,1]: retrograde;
-- * w₀ = δ u, w₁ = δ z even (j ≥ 2): if u + z is odd the new entries
--   are δ times odd congruent ones, retrograde; if u ± z = δ c± with
--   c± odd, retrograde at the exponent k; with c± even, disjoint;
-- * j = 0, ℓ = 1, with the exponent z of the syllable: for z = 0,
--   G s is the normal step from s; for z odd the new entries are δ
--   times odd congruent ones, retrograde; for z = 2 they are δ² times
--   odd ones with the exponent 2, and the square closes through
--   X_[0,1] ω_[1]⁷ ω_[0] by (r).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.CaseH {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_ ; _∧_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base using (+_)
open import Data.List.Relation.Unary.All using ([] ; _∷_)
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Scale using (sc-δ ; λωᶻ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Residue
  using (δ²ᶻ ; δ³ᶻ ; g1 ; g2 ; g3 ; _∣_ ; _,_ ; ∣-* ; δ³∣g1 ; par ; par-+ ; par-- ; oddP-par ; c0 ; c1 ; c2 ; _⊕_ ;
         odd-quot1 ; odd-quot2 ; δ²∣-par ; δ-cancel ; δ²-cancel ; zOf-cong3 ; zOf-plus2 ; zOf-odd-c1 ; zOf-2-c)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count-cong)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Column
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Pivot using (pivot ; pivot-just ; pivot-char ; level ; _<ₗ_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syllable
  using (syl ; step ; Beyond-actM ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Step using (scV-δ²map)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Levels using (Bℓ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Derived {n}
  using (H-H ; Hω²H≈Xω⁷ωHω² ; Apartʷ ; Apartʷʷ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Basic {n} using (Letters≤)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Reduction {n} using (Square ; Below ; path-ε)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.MainTools {n}
  using (pivot-keep ; lt-step ; square-by ; square-disjoint′ ; square-retro ; square-syl ;
         syl-of ; level-of ; word-below-all ; above-apart′ ; pivot-stay ; ne-𝕀 ; bℓ-below)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.PivotColumn as PivotColumn

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

  open ZG using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

  -- Parities of sums and differences.
  odd-sum : ∀ x y → oddᶻ x xor oddᶻ y ≡ true → Odd (x ZR.+ y)
  odd-sum x y e = ≡.trans (oddᶻ-+ x y) e

  par-dif : ∀ x y → oddᶻ (x ZR.- y) ≡ oddᶻ (x ZR.+ y)
  par-dif x y = ≡.trans (oddᶻ-+ x (ZR.- y)) (≡.trans (≡.cong (oddᶻ x xor_) (oddᶻ-neg y)) (≡.sym (oddᶻ-+ x y)))

  -- λω is odd.
  oddλ : ∀ x → oddᶻ (λωᶻ ZR.* x) ≡ oddᶻ x
  oddλ x = oddᶻ-* λωᶻ x

  -- λω (x + y) − λω (x − y) = δ³ (λω g₃ y).
  λω±-δ³ : ∀ x y → δ³ᶻ ∣ (λωᶻ ZR.* (x ZR.+ y) ZR.- λωᶻ ZR.* (x ZR.- y))
  λω±-δ³ x y = λωᶻ ZR.* (g3 ZR.* y) ,
    ZG.solve 2 (λ x y → con λωᶻ :* (x :+ y) :- con λωᶻ :* (x :- y) := con δ³ᶻ :* (con λωᶻ :* (con g3 :* y)))
               ≡.refl x y

  -- λω y − λω y′ with y − y′ = g₁ z is a multiple of δ³.
  λω-g1 : ∀ y y′ z → y ZR.- y′ ≡ g1 ZR.* z → δ³ᶻ ∣ (λωᶻ ZR.* y ZR.- λωᶻ ZR.* y′)
  λω-g1 y y′ z e = ≡.subst (δ³ᶻ ∣_) (≡.sym eq) (∣-* (λωᶻ ZR.* z) δ³∣g1)
    where
    eq : λωᶻ ZR.* y ZR.- λωᶻ ZR.* y′ ≡ (λωᶻ ZR.* z) ZR.* g1
    eq = ≡.trans (ZG.solve 2 (λ y y′ → con λωᶻ :* y :- con λωᶻ :* y′ := con λωᶻ :* (y :- y′)) ≡.refl y y′)
           (≡.trans (≡.cong (λωᶻ ZR.*_) e)
             (ZG.solve 1 (λ z → con λωᶻ :* (con g1 :* z) := (con λωᶻ :* z) :* con g1) ≡.refl z))

------------------------------------------------------------------------
-- The case

module _ (a b : Fin n) (a0 : toℕ a ≡ 0) (b1 : toℕ b ≡ 1)
         (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p) where

  open PivotColumn s o ps

  private
    ab : a < b
    ab = ≡.subst₂ ℕ._<_ (≡.sym a0) (≡.sym b1) (s≤s z≤n)

    G : Gen n
    G = H-gen a b ab

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

    -- The column of r = H_[0,1] s at p.
    col-r : ∀ {K} {U : Vec Z n} → v ≡ scV K U → col r p ≡ scV (suc (suc K)) (Hᶻ a b U)
    col-r {K} {U} e = ≡.trans (col-actM G s p) (≡.trans (≡.cong (actV G) e) (actV-H a b ab K U))

    Hᶻ-a : (U : Vec Z n) → Hᶻ a b U ! a ≡ λωᶻ ZR.* (U ! a ZR.+ U ! b)
    Hᶻ-a U = set₂-a a b (λωᶻ ZR.* (U ! a ZR.+ U ! b)) (λωᶻ ZR.* (U ! a ZR.- U ! b)) (Vec.map (δ²ᶻ ZR.*_) U)

    Hᶻ-b : (U : Vec Z n) → Hᶻ a b U ! b ≡ λωᶻ ZR.* (U ! a ZR.- U ! b)
    Hᶻ-b U = set₂-b a b (λωᶻ ZR.* (U ! a ZR.+ U ! b)) (λωᶻ ZR.* (U ! a ZR.- U ! b)) (Vec.map (δ²ᶻ ZR.*_) U) a≢b

    Hᶻ-≢ : (U : Vec Z n) {x : Fin n} → x ≢ a → x ≢ b → Hᶻ a b U ! x ≡ δ²ᶻ ZR.* (U ! x)
    Hᶻ-≢ U x≢a x≢b =
      ≡.trans (set₂-≢ a b (λωᶻ ZR.* (U ! a ZR.+ U ! b)) (λωᶻ ZR.* (U ! a ZR.- U ! b)) (Vec.map (δ²ᶻ ZR.*_) U) x≢a x≢b)
              (VecP.lookup-map _ (δ²ᶻ ZR.*_) U)

    -- When δ² divides the new entries a and b, H at scale k + 2 is the
    -- vector with those entries divided, at scale k.
    Hᶻ-δ² : (U : Vec Z n) (y y′ : Z) → λωᶻ ZR.* (U ! a ZR.+ U ! b) ≡ δ²ᶻ ZR.* y →
            λωᶻ ZR.* (U ! a ZR.- U ! b) ≡ δ²ᶻ ZR.* y′ → Hᶻ a b U ≡ Vec.map (δ²ᶻ ZR.*_) (set₂ a b y y′ U)
    Hᶻ-δ² U y y′ ey ey′ = vec-ext λ x → at x (x FinP.≟ a) (x FinP.≟ b)
      where
      V = set₂ a b y y′ U
      at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Hᶻ a b U ! x ≡ Vec.map (δ²ᶻ ZR.*_) V ! x
      at x (yes ≡.refl) _ =
        ≡.trans (Hᶻ-a U) (≡.trans ey (≡.trans (≡.cong (δ²ᶻ ZR.*_) (≡.sym (set₂-a a b y y′ U)))
                                                (≡.sym (VecP.lookup-map a (δ²ᶻ ZR.*_) V))))
      at x (no _) (yes ≡.refl) =
        ≡.trans (Hᶻ-b U) (≡.trans ey′ (≡.trans (≡.cong (δ²ᶻ ZR.*_) (≡.sym (set₂-b a b y y′ U a≢b)))
                                                 (≡.sym (VecP.lookup-map b (δ²ᶻ ZR.*_) V))))
      at x (no x≢a) (no x≢b) =
        ≡.trans (Hᶻ-≢ U x≢a x≢b)
          (≡.trans (≡.cong (δ²ᶻ ZR.*_) (≡.sym (set₂-≢ a b y y′ U x≢a x≢b)))
                   (≡.sym (VecP.lookup-map x (δ²ᶻ ZR.*_) V)))

    -- When δ divides the new entries a and b, H at scale k + 2 is the
    -- vector with those entries divided, and the others times δ, at
    -- scale k + 1.
    Hᶻ-δ : (U : Vec Z n) (y y′ : Z) → λωᶻ ZR.* (U ! a ZR.+ U ! b) ≡ δᶻ ZR.* y →
           λωᶻ ZR.* (U ! a ZR.- U ! b) ≡ δᶻ ZR.* y′ →
           Hᶻ a b U ≡ Vec.map (δᶻ ZR.*_) (set₂ a b y y′ (Vec.map (δᶻ ZR.*_) U))
    Hᶻ-δ U y y′ ey ey′ = vec-ext λ x → at x (x FinP.≟ a) (x FinP.≟ b)
      where
      δU = Vec.map (δᶻ ZR.*_) U
      V = set₂ a b y y′ δU
      at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Hᶻ a b U ! x ≡ Vec.map (δᶻ ZR.*_) V ! x
      at x (yes ≡.refl) _ =
        ≡.trans (Hᶻ-a U) (≡.trans ey (≡.trans (≡.cong (δᶻ ZR.*_) (≡.sym (set₂-a a b y y′ δU)))
                                                (≡.sym (VecP.lookup-map a (δᶻ ZR.*_) V))))
      at x (no _) (yes ≡.refl) =
        ≡.trans (Hᶻ-b U) (≡.trans ey′ (≡.trans (≡.cong (δᶻ ZR.*_) (≡.sym (set₂-b a b y y′ δU a≢b)))
                                                 (≡.sym (VecP.lookup-map b (δᶻ ZR.*_) V))))
      at x (no x≢a) (no x≢b) =
        ≡.trans (Hᶻ-≢ U x≢a x≢b)
          (≡.trans (ZR.*-assoc δᶻ δᶻ (U ! x))
            (≡.trans (≡.cong (δᶻ ZR.*_) (≡.trans (≡.sym (VecP.lookup-map x (δᶻ ZR.*_) U))
                                                (≡.sym (set₂-≢ a b y y′ δU x≢a x≢b))))
                     (≡.sym (VecP.lookup-map x (δᶻ ZR.*_) V))))

    scV-δmap : ∀ k (U : Vec Z n) → scV (suc k) (Vec.map (δᶻ ZR.*_) U) ≡ scV k U
    scV-δmap k U = vec-ext λ x →
      ≡.trans (scV-! (suc k) (Vec.map (δᶻ ZR.*_) U) x)
        (≡.trans (≡.cong (sc (suc k)) (VecP.lookup-map x (δᶻ ZR.*_) U))
          (≡.trans (sc-δ k (U ! x)) (≡.sym (scV-! k U x))))
      where open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Scale using (sc)

    ------------------------------------------------------------------
    -- The syllable H_[0,1] ω_[0]ᶻ

    syl-ab : (M : Matrix n n D) {p′ : Fin n} → pivot M ≡ just p′ → ∀ k′ (U : Vec Z n) →
             col M p′ ≡ scV (suc k′) U → Odd (U ! a) → Odd (U ! b) →
             syl M ≡ H a b ab • ω a ^ zOf (U ! a) (U ! b)
    syl-ab M {p′} pv k′ U eq oa ob =
      ≡.trans (syl-of M pv (suc k′) U eq (inj₂ (a , oa))) (sylData-pair {p = p′} k′ U fo nx ab)
      where
      fo : firstOdd U ≡ just a
      fo = firstOdd-char U oa (λ x x<a → ⊥-elim (none<a x<a))
      nx : nextOdd a U ≡ just b
      nx = nextOdd-char U ab ob (λ x a<x x<b → ⊥-elim (none-ab a<x x<b))

    ------------------------------------------------------------------
    -- Retrograde: the normal edge from r is H_[0,1]

    retro : ∀ {p′} → pivot r ≡ just p′ → ∀ k′ (U : Vec Z n) → col r p′ ≡ scV (suc k′) U →
            Odd (U ! a) → Odd (U ! b) → zOf (U ! a) (U ! b) ≡ 0 → Square G s o
    retro pr k′ U eq oa ob z0 = square-retro G s o ps pr back
      where
      back : syl r • [ G ]ʷ ≈ ε
      back = trans (cleft refl′ (≡.trans (syl-ab r pr k′ U eq oa ob) (≡.cong (λ z → H a b ab • ω a ^ z) z0)))
                   (trans (cleft right-unit) (H-H ab))

    -- Two new entries λω y, λω y′, odd and congruent modulo δ³.
    retro-λω : ∀ {p′} → pivot r ≡ just p′ → ∀ k′ (U : Vec Z n) → col r p′ ≡ scV (suc k′) U →
               ∀ y y′ → U ! a ≡ λωᶻ ZR.* y → U ! b ≡ λωᶻ ZR.* y′ → Odd y → Odd y′ →
               δ³ᶻ ∣ (λωᶻ ZR.* y ZR.- λωᶻ ZR.* y′) → Square G s o
    retro-λω pr k′ U eq y y′ ey ey′ oy oy′ d =
      retro pr k′ U eq (≡.trans (≡.cong oddᶻ ey) (≡.trans (oddλ y) oy))
                       (≡.trans (≡.cong oddᶻ ey′) (≡.trans (oddλ y′) oy′))
                       (≡.trans (≡.cong₂ zOf ey ey′) (zOf-cong3 (λωᶻ ZR.* y) (λωᶻ ZR.* y′) d))

    -- Exactly one of U_a, U_b is odd: the new entries at scale k + 2.
    retro-H : ∀ {p′} → pivot r ≡ just p′ → ∀ k (U : Vec Z n) → col r p′ ≡ scV (suc (suc k)) (Hᶻ a b U) →
              oddᶻ (U ! a) xor oddᶻ (U ! b) ≡ true → Square G s o
    retro-H pr k U eq e =
      retro-λω pr (suc k) (Hᶻ a b U) eq (U ! a ZR.+ U ! b) (U ! a ZR.- U ! b) (Hᶻ-a U) (Hᶻ-b U)
        (odd-sum (U ! a) (U ! b) e) (≡.trans (par-dif (U ! a) (U ! b)) (odd-sum (U ! a) (U ! b) e))
        (λω±-δ³ (U ! a) (U ! b))

    ------------------------------------------------------------------
    -- Disjoint: w_a, w_b and the new entries even

    disjoint : ∀ {j} (y y′ : Z) → λωᶻ ZR.* (W ! a ZR.+ W ! b) ≡ δ²ᶻ ZR.* y →
               λωᶻ ZR.* (W ! a ZR.- W ! b) ≡ δ²ᶻ ZR.* y′ → Even y → Even y′ →
               firstOdd W ≡ just j → b < j → Square G s o
    disjoint {j} y y′ ey ey′ ev ev′ fo b<j = square-disjoint′ G s o ps pr syl-r apart lv
      where
      W″ = set₂ a b y y′ W
      j≤p : j ≤ p
      j≤p = odd≤ (proj₁ (firstOdd-spec W fo))
      pr : pivot r ≡ just p
      pr = pivot-keep G s (ℕP.<-≤-trans b<j j≤p) ps
      col-r″ : col r p ≡ scV (lde v) W″
      col-r″ = ≡.trans (col-r v≡) (≡.trans (≡.cong (scV (suc (suc (lde v)))) (Hᶻ-δ² W y y′ ey ey′))
                                            (scV-δ²map (lde v) W″))
      ea : Even (W ! a)
      ea = proj₂ (firstOdd-spec W fo) a (ℕP.<-trans ab b<j)
      eb : Even (W ! b)
      eb = proj₂ (firstOdd-spec W fo) b b<j
      par″ : ∀ x → oddᶻ (W″ ! x) ≡ oddᶻ (W ! x)
      par″ x = at x (x FinP.≟ a) (x FinP.≟ b)
        where
        at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → oddᶻ (W″ ! x) ≡ oddᶻ (W ! x)
        at x (yes ≡.refl) _ = ≡.trans (≡.cong oddᶻ (set₂-a a b y y′ W)) (≡.trans ev (≡.sym ea))
        at x (no _) (yes ≡.refl) = ≡.trans (≡.cong oddᶻ (set₂-b a b y y′ W a≢b)) (≡.trans ev′ (≡.sym eb))
        at x (no x≢a) (no x≢b) = ≡.cong oddᶻ (set₂-≢ a b y y′ W x≢a x≢b)
      agree : ∀ x → Odd (W″ ! x) → W″ ! x ≡ W ! x
      agree x ox = at (x FinP.≟ a) (x FinP.≟ b)
        where
        at : Dec (x ≡ a) → Dec (x ≡ b) → W″ ! x ≡ W ! x
        at (yes x≡a) _ = ⊥-elim (Odd⇒¬Even {W″ ! x} ox
                           (≡.trans (par″ x) (≡.trans (≡.cong (λ z → oddᶻ (W ! z)) x≡a) ea)))
        at (no _) (yes x≡b) = ⊥-elim (Odd⇒¬Even {W″ ! x} ox
                                (≡.trans (par″ x) (≡.trans (≡.cong (λ z → oddᶻ (W ! z)) x≡b) eb)))
        at (no x≢a) (no x≢b) = set₂-≢ a b y y′ W x≢a x≢b
      min″ : Minimal (lde v) W″
      min″ = at min
        where
        at : Minimal (lde v) W → Minimal (lde v) W″
        at (inj₁ e) = inj₁ e
        at (inj₂ (x , ox)) = inj₂ (x , ≡.trans (par″ x) ox)
      syl-r : syl r ≡ syl s
      syl-r = ≡.trans (syl-of r pr (lde v) W″ col-r″ min″)
                (≡.trans (sylData-agree p (lde v) W″ W par″ agree) (≡.sym syl≡))
      lv : level r ≡ level s
      lv = ≡.trans (level-of r pr (lde v) W″ col-r″ min″)
             (≡.trans (≡.cong (λ m → (suc (toℕ p) , lde v , m))
                              (count-cong (λ x → oddᶻ (W″ ! x)) (λ x → oddᶻ (W ! x)) par″))
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
        stay b≤p = retro-H pr 0 W (col-r v≡₀) e
          where
          pr : pivot r ≡ just p
          pr = pivot-stay G s b≤p ps
                 (ne-𝕀 r p 1 (Hᶻ a b W) (col-r v≡₀)
                   (inj₂ (a , ≡.subst Odd (≡.sym (Hᶻ-a W)) (≡.trans (oddλ (W ! a ZR.+ W ! b)) (odd-sum (W ! a) (W ! b) e)))))
        low : p < b → Square G s o
        low p<b = retro-H pr′ 0 (eᶻ b) colb e′
          where
          colb : col r b ≡ scV 2 (Hᶻ a b (eᶻ b))
          colb = ≡.trans (col-actM G s b)
                   (≡.trans (≡.cong (actV G) (≡.trans (proj₂ (pivot-just s ps) b p<b) (col𝕀≡ b)))
                            (actV-H a b ab 0 (eᶻ b)))
          e′ : oddᶻ (eᶻ b ! a) xor oddᶻ (eᶻ b ! b) ≡ true
          e′ = ≡.cong₂ _xor_ (≡.cong oddᶻ (≡.trans (eᶻ-! b a) (eδ-≢ a≢b)))
                             (≡.cong oddᶻ (≡.trans (eᶻ-! b b) (eδ-refl b)))
          pr′ : pivot r ≡ just b
          pr′ = pivot-char r
                  (ne-𝕀 r b 1 (Hᶻ a b (eᶻ b)) colb
                    (inj₂ (a , ≡.subst Odd (≡.sym (Hᶻ-a (eᶻ b)))
                                 (≡.trans (oddλ (eᶻ b ! a ZR.+ eᶻ b ! b)) (odd-sum (eᶻ b ! a) (eᶻ b ! b) e′)))))
                  (Beyond-actM G {M = s} FinP.≤-refl
                    (λ c b<c → proj₂ (pivot-just s ps) c (ℕP.<-trans p<b b<c)))
        by-p : Tri (p < b) (p ≡ b) (b < p) → Square G s o
        by-p (tri< p<b _ _) = low p<b
        by-p (tri≈ _ p≡b _) = stay (≡.subst (b ≤_) (≡.sym p≡b) FinP.≤-refl)
        by-p (tri> _ _ b<p) = stay (ℕP.<⇒≤ b<p)

      go : (∃ λ m → firstOdd W ≡ just m × ∃ λ t → t ℕ.< 8 × W ! m ≡ ωᶻ ^ᶻ t × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) →
           Square G s o
      go (m , fo , t , t<8 , um , rest) = by-m (FinP.<-cmp b m)
        where
        om : Odd (W ! m)
        om = proj₁ (firstOdd-spec W fo)
        wa0 : b < m → W ! a ≡ ZR.0#
        wa0 b<m = rest a (λ e → FinP.<-irrefl e (ℕP.<-trans ab b<m))
        wb0 : b < m → W ! b ≡ ZR.0#
        wb0 b<m = rest b (λ e → FinP.<-irrefl e b<m)
        by-m : Tri (b < m) (b ≡ m) (m < b) → Square G s o
        by-m (tri< b<m _ _) =
          disjoint ZR.0# ZR.0#
            (≡.trans (≡.cong₂ (λ x y → λωᶻ ZR.* (x ZR.+ y)) (wa0 b<m) (wb0 b<m)) ≡.refl)
            (≡.trans (≡.cong₂ (λ x y → λωᶻ ZR.* (x ZR.- y)) (wa0 b<m) (wb0 b<m)) ≡.refl)
            ≡.refl ≡.refl fo b<m
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
      pair01 fo nx = by-z (zOf (W ! a) (W ! b)) (zOf-< (W ! a) (W ! b)) ≡.refl
        where
        oa : Odd (W ! a)
        oa = proj₁ (firstOdd-spec W fo)
        ob : Odd (W ! b)
        ob = proj₁ (proj₂ (nextOdd-spec W nx))
        b≤p : b ≤ p
        b≤p = odd≤ ob
        syl-s : syl s ≡ H a b ab • ω a ^ zOf (W ! a) (W ! b)
        syl-s = ≡.trans syl≡ (≡.trans (≡.cong (λ k → sylData p k W) ks) (sylData-pair {p = p} K′ W fo nx ab))

        -- The parity vectors of W_a ± W_b.
        par+ : par (W ! a ZR.+ W ! b) ≡ par (W ! a) ⊕ par (W ! b)
        par+ = par-+ (W ! a) (W ! b)
        par- : par (W ! a ZR.- W ! b) ≡ par (W ! a) ⊕ par (W ! b)
        par- = par-- (W ! a) (W ! b)

        -- z odd: W_a ± W_b = δ y± with y± odd, y₊ − y₋ = g₁ W_b.
        odd-z : oddℕ (zOf (W ! a) (W ! b)) ≡ true → Square G s o
        odd-z oz = go (even⇒δ∣ (W ! a ZR.+ W ! b) ev+) (even⇒δ∣ (W ! a ZR.- W ! b) (≡.trans (par-dif (W ! a) (W ! b)) ev+))
          where
          ev+ : Even (W ! a ZR.+ W ! b)
          ev+ = ≡.trans (oddᶻ-+ (W ! a) (W ! b)) (≡.cong₂ _xor_ oa ob)
          c1± : c1 (par (W ! a) ⊕ par (W ! b)) ≡ true
          c1± = zOf-odd-c1 (W ! a) (W ! b) oa ob oz
          go : δ∣ (W ! a ZR.+ W ! b) → δ∣ (W ! a ZR.- W ! b) → Square G s o
          go (y , ey) (y′ , ey′) =
            retro-λω pr (suc K′) W″ col-r″ y y′ (set₂-a a b (λωᶻ ZR.* y) (λωᶻ ZR.* y′) δW)
                     (set₂-b a b (λωᶻ ZR.* y) (λωᶻ ZR.* y′) δW a≢b) oy oy′ (λω-g1 y y′ (W ! b) dif)
            where
            δW = Vec.map (δᶻ ZR.*_) W
            W″ = set₂ a b (λωᶻ ZR.* y) (λωᶻ ZR.* y′) δW
            oy : Odd y
            oy = ≡.trans (odd-quot1 (W ! a ZR.+ W ! b) y ey) (≡.trans (≡.cong c1 par+) c1±)
            oy′ : Odd y′
            oy′ = ≡.trans (odd-quot1 (W ! a ZR.- W ! b) y′ ey′) (≡.trans (≡.cong c1 par-) c1±)
            -- δ (y − y′) = 2 W_b = δ g₁ W_b.
            dif : y ZR.- y′ ≡ g1 ZR.* (W ! b)
            dif = δ-cancel (y ZR.- y′) (g1 ZR.* (W ! b)) (begin′)
              where
              open ≡.≡-Reasoning renaming (begin_ to begin≡_ ; _∎ to _∎≡)
              begin′ : δᶻ ZR.* (y ZR.- y′) ≡ δᶻ ZR.* (g1 ZR.* (W ! b))
              begin′ = ≡.trans (ZG.solve 2 (λ y y′ → con δᶻ :* (y :- y′) := con δᶻ :* y :- con δᶻ :* y′) ≡.refl y y′)
                         (≡.trans (≡.cong₂ ZR._-_ (≡.sym ey) (≡.sym ey′))
                           (ZG.solve 2 (λ x z → (x :+ z) :- (x :- z) := con δᶻ :* (con g1 :* z)) ≡.refl (W ! a) (W ! b)))
            eH : λωᶻ ZR.* (W ! a ZR.+ W ! b) ≡ δᶻ ZR.* (λωᶻ ZR.* y)
            eH = ≡.trans (≡.cong (λωᶻ ZR.*_) ey) (ZG.solve 1 (λ y → con λωᶻ :* (con δᶻ :* y) := con δᶻ :* (con λωᶻ :* y)) ≡.refl y)
            eH′ : λωᶻ ZR.* (W ! a ZR.- W ! b) ≡ δᶻ ZR.* (λωᶻ ZR.* y′)
            eH′ = ≡.trans (≡.cong (λωᶻ ZR.*_) ey′) (ZG.solve 1 (λ y → con λωᶻ :* (con δᶻ :* y) := con δᶻ :* (con λωᶻ :* y)) ≡.refl y′)
            col-r″ : col r p ≡ scV (suc (suc K′)) W″
            col-r″ = ≡.trans (col-r v≡ₖ) (≡.trans (≡.cong (scV (suc (suc (suc K′)))) (Hᶻ-δ W (λωᶻ ZR.* y) (λωᶻ ZR.* y′) eH eH′))
                                                  (scV-δmap (suc (suc K′)) W″))
            pr : pivot r ≡ just p
            pr = pivot-stay G s b≤p ps
                   (ne-𝕀 r p (suc K′) W″ col-r″
                     (inj₂ (a , ≡.trans (≡.cong oddᶻ (set₂-a a b (λωᶻ ZR.* y) (λωᶻ ZR.* y′) δW)) (≡.trans (oddλ y) oy))))

        -- z = 2: W_a ± W_b = δ² y± with y± odd, y₋ = y₊ − g₂ W_b; the
        -- normal edge from r is H_[0,1] ω_[0]² too, and the square closes
        -- by (r).
        two-z : zOf (W ! a) (W ! b) ≡ 2 → Square G s o
        two-z z2 = go (δ²∣-par (W ! a ZR.+ W ! b) c0+ c1+) (δ²∣-par (W ! a ZR.- W ! b) c0- c1-)
          where
          ev+ : Even (W ! a ZR.+ W ! b)
          ev+ = ≡.trans (oddᶻ-+ (W ! a) (W ! b)) (≡.cong₂ _xor_ oa ob)
          cs = zOf-2-c (W ! a) (W ! b) oa ob z2
          c0+ : c0 (par (W ! a ZR.+ W ! b)) ≡ false
          c0+ = ≡.trans (oddP-par (W ! a ZR.+ W ! b)) ev+
          c1+ : c1 (par (W ! a ZR.+ W ! b)) ≡ false
          c1+ = ≡.trans (≡.cong c1 par+) (proj₁ cs)
          c0- : c0 (par (W ! a ZR.- W ! b)) ≡ false
          c0- = ≡.trans (oddP-par (W ! a ZR.- W ! b)) (≡.trans (par-dif (W ! a) (W ! b)) ev+)
          c1- : c1 (par (W ! a ZR.- W ! b)) ≡ false
          c1- = ≡.trans (≡.cong c1 par-) (proj₁ cs)
          go : δ²ᶻ ∣ (W ! a ZR.+ W ! b) → δ²ᶻ ∣ (W ! a ZR.- W ! b) → Square G s o
          go (y , ey) (y′ , ey′) =
            square-syl G s o (H a b ab • ω a ^ 2) (X a b ab • ω b ^ 7 • ω a) pr syl-r
              (below b≤p (X a b ab • ω b ^ 7 • ω a)
                         (ℕP.≤-refl , (ℕP.≤-refl , ℕP.≤-refl , ℕP.≤-refl , ℕP.≤-refl , ℕP.≤-refl , ℕP.≤-refl , ℕP.≤-refl) ,
                          ℕP.<⇒≤ ab))
              (trans rel (cright refl′ (≡.sym (≡.trans syl-s (≡.cong (λ z → H a b ab • ω a ^ z) z2)))))
            where
            W″ = set₂ a b (λωᶻ ZR.* y) (λωᶻ ZR.* y′) W
            oy : Odd y
            oy = ≡.trans (odd-quot2 (W ! a ZR.+ W ! b) y ey) (≡.trans (≡.cong c2 par+) (proj₂ cs))
            oy′ : Odd y′
            oy′ = ≡.trans (odd-quot2 (W ! a ZR.- W ! b) y′ ey′) (≡.trans (≡.cong c2 par-) (proj₂ cs))
            -- δ² (y − y′) = 2 W_b = δ² g₂ W_b.
            dif : y′ ≡ y ZR.- g2 ZR.* (W ! b)
            dif = δ²-cancel y′ (y ZR.- g2 ZR.* (W ! b))
                    (≡.trans (≡.sym ey′)
                      (≡.trans (ZG.solve 2 (λ x z → x :- z := (x :+ z) :- con δ²ᶻ :* (con g2 :* z)) ≡.refl (W ! a) (W ! b))
                        (≡.trans (≡.cong (λ t → t ZR.- δ²ᶻ ZR.* (g2 ZR.* (W ! b))) ey)
                          (ZG.solve 2 (λ y z → con δ²ᶻ :* y :- con δ²ᶻ :* (con g2 :* z) := con δ²ᶻ :* (y :- con g2 :* z))
                                      ≡.refl y (W ! b)))))
            eH : λωᶻ ZR.* (W ! a ZR.+ W ! b) ≡ δ²ᶻ ZR.* (λωᶻ ZR.* y)
            eH = ≡.trans (≡.cong (λωᶻ ZR.*_) ey) (ZG.solve 1 (λ y → con λωᶻ :* (con δ²ᶻ :* y) := con δ²ᶻ :* (con λωᶻ :* y)) ≡.refl y)
            eH′ : λωᶻ ZR.* (W ! a ZR.- W ! b) ≡ δ²ᶻ ZR.* (λωᶻ ZR.* y′)
            eH′ = ≡.trans (≡.cong (λωᶻ ZR.*_) ey′) (ZG.solve 1 (λ y → con λωᶻ :* (con δ²ᶻ :* y) := con δ²ᶻ :* (con λωᶻ :* y)) ≡.refl y′)
            col-r″ : col r p ≡ scV (suc K′) W″
            col-r″ = ≡.trans (col-r v≡ₖ) (≡.trans (≡.cong (scV (suc (suc (suc K′)))) (Hᶻ-δ² W (λωᶻ ZR.* y) (λωᶻ ZR.* y′) eH eH′))
                                                  (scV-δ²map (suc K′) W″))
            oλy : Odd (W″ ! a)
            oλy = ≡.trans (≡.cong oddᶻ (set₂-a a b (λωᶻ ZR.* y) (λωᶻ ZR.* y′) W)) (≡.trans (oddλ y) oy)
            oλy′ : Odd (W″ ! b)
            oλy′ = ≡.trans (≡.cong oddᶻ (set₂-b a b (λωᶻ ZR.* y) (λωᶻ ZR.* y′) W a≢b)) (≡.trans (oddλ y′) oy′)
            pr : pivot r ≡ just p
            pr = pivot-stay G s b≤p ps (ne-𝕀 r p K′ W″ col-r″ (inj₂ (a , oλy)))
            -- λω y′ = λω y − g₂ (λω W_b).
            z″ : zOf (W″ ! a) (W″ ! b) ≡ 2
            z″ = ≡.trans (≡.cong₂ zOf (set₂-a a b (λωᶻ ZR.* y) (λωᶻ ZR.* y′) W) (set₂-b a b (λωᶻ ZR.* y) (λωᶻ ZR.* y′) W a≢b))
                   (≡.trans (≡.cong (zOf (λωᶻ ZR.* y))
                              (≡.trans (≡.cong (λωᶻ ZR.*_) dif)
                                (ZG.solve 2 (λ y z → con λωᶻ :* (y :- con g2 :* z) := con λωᶻ :* y :- con g2 :* (con λωᶻ :* z))
                                            ≡.refl y (W ! b))))
                            (zOf-plus2 (λωᶻ ZR.* y) (λωᶻ ZR.* (W ! b)) (≡.trans (oddλ y) oy) (≡.trans (oddλ (W ! b)) ob)))
            syl-r : syl r ≡ H a b ab • ω a ^ 2
            syl-r = ≡.trans (syl-ab r pr K′ W″ col-r″ oλy oλy′) (≡.cong (λ z → H a b ab • ω a ^ z) z″)
            rel : (H a b ab • ω a ^ 2) • H a b ab ≈ (X a b ab • ω b ^ 7 • ω a) • (H a b ab • ω a ^ 2)
            rel = trans assoc (trans (Hω²H≈Xω⁷ωHω² ab) (by-assoc auto))

        by-z : ∀ z → z ℕ.< 4 → zOf (W ! a) (W ! b) ≡ z → Square G s o
        -- z = 0: r is the normal step from s.
        by-z 0 _ e =
          square-by G s o ε ε (path-ε r (ColOrth-actMʷ [ G ]ʷ o)) tt
            (trans (cright sym right-unit)
                   (cright refl′ (≡.sym (≡.trans syl-s (≡.cong (λ z → H a b ab • ω a ^ z) e)))))
        by-z 1 _ e = odd-z (≡.cong oddℕ e)
        by-z 2 _ e = two-z e
        by-z 3 _ e = odd-z (≡.cong oddℕ e)
        by-z (suc (suc (suc (suc _)))) (s≤s (s≤s (s≤s (s≤s ())))) _

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
          by-ℓ (no ℓ≢1) = retro-H (pivot-keep G s (ℕP.<-≤-trans b<ℓ ℓ≤p) ps) (suc K′) W (col-r v≡ₖ)
                            (≡.cong₂ _xor_ oa (proj₂ (proj₂ (nextOdd-spec W nx)) b ab b<ℓ))
            where
            b<ℓ : b < ℓ
            b<ℓ = b< a<ℓ ℓ≢1

      -- j = 1: retrograde.
      at-b : firstOdd W ≡ just b → Square G s o
      at-b fo = go (second ks fo)
        where
        go : (∃ λ ℓ → nextOdd b W ≡ just ℓ) → Square G s o
        go (ℓ , nx) = retro-H (pivot-keep G s (ℕP.<-≤-trans (proj₁ (nextOdd-spec W nx))
                                                            (odd≤ (proj₁ (proj₂ (nextOdd-spec W nx))))) ps)
                              (suc K′) W (col-r v≡ₖ)
                              (≡.cong₂ _xor_ (proj₂ (firstOdd-spec W fo) a ab) (proj₁ (firstOdd-spec W fo)))

      -- j > 1: w_a = δ u and w_b = δ z are even.
      above : ∀ {j} → firstOdd W ≡ just j → b < j → Square G s o
      above {j} fo b<j = go (even⇒δ∣ (W ! a) (proj₂ (firstOdd-spec W fo) a (ℕP.<-trans ab b<j)))
                            (even⇒δ∣ (W ! b) (proj₂ (firstOdd-spec W fo) b b<j))
        where
        j≤p : j ≤ p
        j≤p = odd≤ (proj₁ (firstOdd-spec W fo))
        pr : pivot r ≡ just p
        pr = pivot-keep G s (ℕP.<-≤-trans b<j j≤p) ps
        go : δ∣ (W ! a) → δ∣ (W ! b) → Square G s o
        go (u , eu) (z , ez) = by-par (oddᶻ (u ZR.+ z)) ≡.refl
          where
          -- λω (w_a ± w_b) = δ λω (u ± z).
          eH : λωᶻ ZR.* (W ! a ZR.+ W ! b) ≡ δᶻ ZR.* (λωᶻ ZR.* (u ZR.+ z))
          eH = ≡.trans (≡.cong₂ (λ x y → λωᶻ ZR.* (x ZR.+ y)) eu ez)
                 (ZG.solve 2 (λ u z → con λωᶻ :* (con δᶻ :* u :+ con δᶻ :* z) := con δᶻ :* (con λωᶻ :* (u :+ z))) ≡.refl u z)
          eH′ : λωᶻ ZR.* (W ! a ZR.- W ! b) ≡ δᶻ ZR.* (λωᶻ ZR.* (u ZR.- z))
          eH′ = ≡.trans (≡.cong₂ (λ x y → λωᶻ ZR.* (x ZR.- y)) eu ez)
                  (ZG.solve 2 (λ u z → con λωᶻ :* (con δᶻ :* u :- con δᶻ :* z) := con δᶻ :* (con λωᶻ :* (u :- z))) ≡.refl u z)

          by-par : (x : Bool) → oddᶻ (u ZR.+ z) ≡ x → Square G s o
          -- u + z odd: retrograde at scale k + 1.
          by-par true od =
            retro-λω pr (suc K′) W″ col-r″ (u ZR.+ z) (u ZR.- z) (set₂-a a b (λωᶻ ZR.* (u ZR.+ z)) (λωᶻ ZR.* (u ZR.- z)) δW) (set₂-b a b (λωᶻ ZR.* (u ZR.+ z)) (λωᶻ ZR.* (u ZR.- z)) δW a≢b)
                     od (≡.trans (par-dif u z) od) (λω±-δ³ u z)
            where
            δW = Vec.map (δᶻ ZR.*_) W
            W″ = set₂ a b (λωᶻ ZR.* (u ZR.+ z)) (λωᶻ ZR.* (u ZR.- z)) δW
            col-r″ : col r p ≡ scV (suc (suc K′)) W″
            col-r″ = ≡.trans (col-r v≡ₖ) (≡.trans (≡.cong (scV (suc (suc (suc K′)))) (Hᶻ-δ W (λωᶻ ZR.* (u ZR.+ z)) (λωᶻ ZR.* (u ZR.- z)) eH eH′))
                                                  (scV-δmap (suc (suc K′)) W″))
          -- u + z = δ c₊, u − z = δ c₋ with c₋ = c₊ − g₁ z.
          by-par false ev = go′ (even⇒δ∣ (u ZR.+ z) ev)
            where
            go′ : δ∣ (u ZR.+ z) → Square G s o
            go′ (c , ec) = by-c (oddᶻ c) ≡.refl
              where
              c′ = c ZR.- g1 ZR.* z
              ec′ : u ZR.- z ≡ δᶻ ZR.* c′
              ec′ = ≡.trans (ZG.solve 2 (λ u z → u :- z := (u :+ z) :- con δᶻ :* (con g1 :* z)) ≡.refl u z)
                      (≡.trans (≡.cong (λ t → t ZR.- δᶻ ZR.* (g1 ZR.* z)) ec)
                        (ZG.solve 2 (λ c z → con δᶻ :* c :- con δᶻ :* (con g1 :* z) := con δᶻ :* (c :- con g1 :* z)) ≡.refl c z))
              e2 : λωᶻ ZR.* (W ! a ZR.+ W ! b) ≡ δ²ᶻ ZR.* (λωᶻ ZR.* c)
              e2 = ≡.trans eH (≡.trans (≡.cong (λ t → δᶻ ZR.* (λωᶻ ZR.* t)) ec)
                     (ZG.solve 1 (λ c → con δᶻ :* (con λωᶻ :* (con δᶻ :* c)) := con δ²ᶻ :* (con λωᶻ :* c)) ≡.refl c))
              e2′ : λωᶻ ZR.* (W ! a ZR.- W ! b) ≡ δ²ᶻ ZR.* (λωᶻ ZR.* c′)
              e2′ = ≡.trans eH′ (≡.trans (≡.cong (λ t → δᶻ ZR.* (λωᶻ ZR.* t)) ec′)
                      (ZG.solve 1 (λ c → con δᶻ :* (con λωᶻ :* (con δᶻ :* c)) := con δ²ᶻ :* (con λωᶻ :* c)) ≡.refl c′))
              -- c′ has the parity of c: g₁ is even.
              par-c′ : oddᶻ c′ ≡ oddᶻ c
              par-c′ = ≡.trans (oddᶻ-+ c (ZR.- (g1 ZR.* z)))
                         (≡.trans (≡.cong (oddᶻ c xor_) (≡.trans (oddᶻ-neg (g1 ZR.* z)) (oddᶻ-* g1 z)))
                                  (xor-f (oddᶻ c)))
                where
                xor-f : ∀ x → x xor false ≡ x
                xor-f true = ≡.refl
                xor-f false = ≡.refl
              by-c : (x : Bool) → oddᶻ c ≡ x → Square G s o
              by-c false ec0 = disjoint (λωᶻ ZR.* c) (λωᶻ ZR.* c′) e2 e2′
                                 (≡.trans (oddλ c) ec0) (≡.trans (oddλ c′) (≡.trans par-c′ ec0)) fo b<j
              -- c odd: retrograde at scale k.
              by-c true oc =
                retro-λω pr K′ W″ col-r″ c c′ (set₂-a a b (λωᶻ ZR.* c) (λωᶻ ZR.* c′) W) (set₂-b a b (λωᶻ ZR.* c) (λωᶻ ZR.* c′) W a≢b) oc (≡.trans par-c′ oc)
                         (λω-g1 c c′ z (ZG.solve 2 (λ c t → c :- (c :- t) := t) ≡.refl c (g1 ZR.* z)))
                where
                W″ = set₂ a b (λωᶻ ZR.* c) (λωᶻ ZR.* c′) W
                col-r″ : col r p ≡ scV (suc K′) W″
                col-r″ = ≡.trans (col-r v≡ₖ) (≡.trans (≡.cong (scV (suc (suc (suc K′)))) (Hᶻ-δ² W (λωᶻ ZR.* c) (λωᶻ ZR.* c′) e2 e2′))
                                                      (scV-δ²map (suc K′) W″))

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

  caseH : Square (H-gen a b ab) s o
  caseH = by-k (lde v) ≡.refl
    where
    by-k : ∀ k → lde v ≡ k → Square G s o
    by-k zero k0 = case0 k0
    by-k (suc K′) ks = case+ ks
