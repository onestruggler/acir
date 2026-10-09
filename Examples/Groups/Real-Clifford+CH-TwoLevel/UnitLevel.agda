------------------------------------------------------------------------
-- Presentations of groups
--
-- The edges at a level with exponent 0 (Lemma A.8 at k = 0).
--
-- There the pivot column of s is a unit ±e_m with m ≤ p (Norm.lde0),
-- and the normal syllable N is X_[m,p] Z_[m]^τ (m < p) or Z_[p]
-- (m = p, where the unit is -1).  For a generator g acting on indices
-- ≤ p (the others are in Above):
--
-- * if g does not touch m, g·s has the same syllable N, and the
--   square closes with g conjugated by N's X_[m,p]: a word below p;
-- * Z_[m] and the X_[c,d] that move m make g·s a unit state again,
--   and the two syllables differ by g, up to X_[c,d] below p (or g·s
--   is below the level: the unit came to e_p);
-- * H_[c,d] touching m makes the column a pair, whose syllable undoes
--   H_[c,d] up to X_[0,c] (EdgeTools.edge-H-pair).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.Real-Clifford+CH-TwoLevel.UnitLevel {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false ; not)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; module DR ; oddᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Scale using (sc ; sc-0)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (scV ; scV-! ; lde ; num ; Minimal ; Odd)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot
  using (pivot ; pivot-just ; pivot-char ; Beyond ; level ; level-below ; _<ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable
  using (syl ; syl-just ; top ; Within ; Beyond-actM ; Beyond-actMʷ ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡ ; zeroV ; actV-0)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step using (unit-step)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (Z-Z ; X-X ; flip-X ; Apart ; comm-gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric {n}
  using (τ ; τ-p ; τ-q ; τ-o ; τ-τ ; relabel-Z ; relabel-X ; relabel-H ; Xs ; Hs ; Xs-< ; conj-•)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (Path ; BelowSrc ; EdgesBelow)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PathTools {n} using (via ; module Below)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (path-normal ; syl-of ; ne-𝕀 ; ne-𝕀-at)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.EdgeTools {n}
import Examples.Groups.Real-Clifford+CH-TwoLevel.Above {n} as Above
import Examples.Groups.Real-Clifford+CH-TwoLevel.PivotColumn as PC

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

  rc : ∀ {a b : Fin n} → .(a < b) → a < b
  rc {a} {b} lt = recompute (a FinP.<? b) lt

  e-a : (a : Fin n) → eᶻ a ! a ≡ ZR.1#
  e-a a = ≡.trans (eᶻ-! a a) (eδ-refl a)

  e-≢ : {a x : Fin n} → x ≢ a → eᶻ a ! x ≡ ZR.0#
  e-≢ {a} {x} x≢a = ≡.trans (eᶻ-! a x) (eδ-≢ x≢a)

  -1≢1 : ZR.- ZR.1# ≢ ZR.1#
  -1≢1 ()

  ≢-sym : {a b : Fin n} → a ≢ b → b ≢ a
  ≢-sym ne e = ne (≡.sym e)

------------------------------------------------------------------------
-- Unit vectors

-- w is the unit u at m, and 0 elsewhere.
record UV (m : Fin n) (u : Z) (w : Vec Z n) : Set where
  constructor mkUV
  field
    unit : Unit1 u
    at   : w ! m ≡ u
    off  : ∀ y → y ≢ m → w ! y ≡ ZR.0#

unit-neg : ∀ {u} → Unit1 u → Unit1 (ZR.- u)
unit-neg (inj₁ ≡.refl) = inj₂ ≡.refl
unit-neg (inj₂ ≡.refl) = inj₁ ≡.refl

unit-negᶻ : ∀ {u} → Unit1 u → negᶻ (ZR.- u) ≡ not (negᶻ u)
unit-negᶻ (inj₁ ≡.refl) = ≡.refl
unit-negᶻ (inj₂ ≡.refl) = ≡.refl

UV-first : ∀ {m u w} → UV m u w → firstOdd w ≡ just m
UV-first {m} {u} {w} (mkUV uu wm z) =
  firstOdd-char w (≡.subst Odd (≡.sym wm) (unit-odd uu))
    (λ x x<m → ≡.cong oddᶻ (z x (λ { ≡.refl → FinP.<-irrefl ≡.refl x<m })))

UV-Z≡ : ∀ {m u w} → UV m u w → UV m (ZR.- u) (Zᶻ m w)
UV-Z≡ {m} {u} {w} (mkUV uu wm z) = mkUV
  (unit-neg uu)
  (≡.trans (set₁-a m (ZR.- (w ! m)) w) (≡.cong ZR.-_ wm))
  (λ y y≢m → ≡.trans (set₁-≢ m (ZR.- (w ! m)) w y≢m) (z y y≢m))

UV-Z≢ : ∀ {m u w} (c : Fin n) → c ≢ m → UV m u w → UV m u (Zᶻ c w)
UV-Z≢ {m} {u} {w} c c≢m (mkUV uu wm z) =
  mkUV uu (≡.trans (set₁-≢ c _ w (≢-sym c≢m)) wm) (λ y y≢m → at y y≢m (y FinP.≟ c))
  where
  at : ∀ y → y ≢ m → Dec (y ≡ c) → Zᶻ c w ! y ≡ ZR.0#
  at y y≢m (yes ≡.refl) = ≡.trans (set₁-a y (ZR.- (w ! y)) w) (≡.cong ZR.-_ (z y y≢m))
  at y y≢m (no y≢c) = ≡.trans (set₁-≢ c _ w y≢c) (z y y≢m)

-- X_[c,d] permutes the entries along τ = (c d).
Xᶻ-τ : (c d : Fin n) → c ≢ d → (w : Vec Z n) (x : Fin n) → Xᶻ c d w ! x ≡ w ! τ c d x
Xᶻ-τ c d c≢d w x = at (x FinP.≟ c) (x FinP.≟ d)
  where
  at : Dec (x ≡ c) → Dec (x ≡ d) → Xᶻ c d w ! x ≡ w ! τ c d x
  at (yes ≡.refl) _ = ≡.trans (set₂-a x d (w ! d) (w ! x) w) (≡.cong (w !_) (≡.sym (τ-p x d)))
  at (no x≢c) (yes ≡.refl) = ≡.trans (set₂-b c x (w ! x) (w ! c) w c≢d) (≡.cong (w !_) (≡.sym (τ-q c x c≢d)))
  at (no x≢c) (no x≢d) = ≡.trans (set₂-≢ c d (w ! d) (w ! c) w x≢c x≢d) (≡.cong (w !_) (≡.sym (τ-o c d x x≢c x≢d)))

UV-X : ∀ {m u w} (c d : Fin n) → c ≢ d → UV m u w → UV (τ c d m) u (Xᶻ c d w)
UV-X {m} {u} {w} c d c≢d (mkUV uu wm z) = mkUV uu
  (≡.trans (Xᶻ-τ c d c≢d w (τ c d m)) (≡.trans (≡.cong (w !_) (τ-τ c d m c≢d)) wm))
  (λ y y≢ → ≡.trans (Xᶻ-τ c d c≢d w y)
              (z (τ c d y) (λ e → y≢ (≡.trans (≡.sym (τ-τ c d y c≢d)) (≡.cong (τ c d) e)))))

UV-e : ∀ {m w} → UV m ZR.1# w → w ≡ eᶻ m
UV-e {m} {w} (mkUV _ wm z) = vec-ext λ x → at x (x FinP.≟ m)
  where
  at : ∀ x → Dec (x ≡ m) → w ! x ≡ eᶻ m ! x
  at x (yes ≡.refl) = ≡.trans wm (≡.sym (e-a x))
  at x (no x≢m) = ≡.trans (z x x≢m) (≡.sym (e-≢ x≢m))

-- Unless it is e_p, a unit vector differs from e_p somewhere.
UV-ne : ∀ {m u w} (p : Fin n) → UV m u w → m ≢ p ⊎ u ≡ ZR.- ZR.1# → ∃ λ x → w ! x ≢ eᶻ p ! x
UV-ne {m} {u} {w} p (mkUV uu wm z) h = by (m FinP.≟ p) h
  where
  by : Dec (m ≡ p) → m ≢ p ⊎ u ≡ ZR.- ZR.1# → ∃ λ x → w ! x ≢ eᶻ p ! x
  by (no m≢p) _ = m , λ e → unit≢0 uu (≡.trans (≡.sym wm) (≡.trans e (e-≢ m≢p)))
  by (yes m≡p) (inj₁ m≢p) = ⊥-elim (m≢p m≡p)
  by (yes ≡.refl) (inj₂ u≡) = m , λ e → -1≢1 (≡.trans (≡.sym u≡) (≡.trans (≡.sym wm) (≡.trans e (e-a m))))

-- The syllable of a unit column.
unitSyl< : ∀ {p m u w} → UV m u w → (lt : m < p) → sylData p 0 w ≡ X m p lt • Zτ m (negᶻ u)
unitSyl< {p} {m} {u} {w} uv lt =
  ≡.trans (sylData-unit< w (UV-first uv) lt) (≡.cong (λ z → X m p lt • Zτ m (negᶻ z)) (UV.at uv))

unitSyl≡ : ∀ {p u w} → UV p u w → sylData p 0 w ≡ Zτ p (negᶻ u)
unitSyl≡ {p} {u} {w} uv = ≡.trans (sylData-unit≡ w (UV-first uv)) (≡.cong (λ z → Zτ p (negᶻ z)) (UV.at uv))

------------------------------------------------------------------------
-- Generators fix the vectors that vanish on their indices

actV-vanish : (g : Gen n) (u : Vec D n) → (∀ y → y ∈ₛ g → u ! y ≡ DR.0#) → actV g u ≡ u
actV-vanish g u van = vec-ext λ x → at x (∈ₛ? x g)
  where
  at : ∀ x → Dec (x ∈ₛ g) → actV g u ! x ≡ u ! x
  at x (yes x∈g) =
    ≡.trans (actV-local g u zeroV (λ y y∈g → ≡.trans (van y y∈g) (≡.sym (VecP.lookup-replicate y DR.0#))) x x∈g)
      (≡.trans (≡.cong (_! x) (actV-0 g)) (≡.trans (VecP.lookup-replicate x DR.0#) (≡.sym (van x x∈g))))
  at x (no x∉g) = actV-off g u x x∉g

------------------------------------------------------------------------
-- Relations

-- X A X ≈ B gives X A ≈ B X.
conj-right : ∀ {A B : Word (Gen n)} {x y : Fin n} .(xy : x < y) →
             X x y xy • A • X x y xy ≈ B → X x y xy • A ≈ B • X x y xy
conj-right {A} {B} xy h = begin
  X′ • A                     ≈⟨ sym right-unit ⟩
  (X′ • A) • ε               ≈⟨ cright sym (X-X xy) ⟩
  (X′ • A) • (X′ • X′)       ≈⟨ sym assoc ⟩
  ((X′ • A) • X′) • X′       ≈⟨ cleft assoc ⟩
  (X′ • A • X′) • X′         ≈⟨ cleft h ⟩
  B • X′                     ∎
  where X′ = X _ _ xy

-- With T commuting with A, and X A X ≈ V: V (X T) ≈ (X T) A.
slide : ∀ {A T V : Word (Gen n)} {x y : Fin n} .(xy : x < y) →
        X x y xy • A • X x y xy ≈ V → T • A ≈ A • T → V • (X x y xy • T) ≈ (X x y xy • T) • A
slide {A} {T} {V} xy conj comm = begin
  V • (X′ • T)                          ≈⟨ cleft sym conj ⟩
  (X′ • A • X′) • (X′ • T)              ≈⟨ assoc ⟩
  X′ • ((A • X′) • (X′ • T))            ≈⟨ cright assoc ⟩
  X′ • (A • (X′ • (X′ • T)))            ≈⟨ cright cright sym assoc ⟩
  X′ • (A • ((X′ • X′) • T))            ≈⟨ cright cright cleft X-X xy ⟩
  X′ • (A • (ε • T))                    ≈⟨ cright cright left-unit ⟩
  X′ • (A • T)                          ≈⟨ cright sym comm ⟩
  X′ • (T • A)                          ≈⟨ sym assoc ⟩
  (X′ • T) • A                          ∎
  where X′ = X _ _ xy

Zτ-comm : ∀ (a : Fin n) t (g : Gen n) → Apart (Z-gen a) g → Zτ a t • [ g ]ʷ ≈ [ g ]ʷ • Zτ a t
Zτ-comm a true g ap = comm-gen (Z-gen a) g ap
Zτ-comm a false g ap = trans left-unit (sym right-unit)

Zτ-flip : ∀ (a : Fin n) t → Zτ a (not t) • Zʷ a ≈ Zτ a t
Zτ-flip a true = left-unit
Zτ-flip a false = Z-Z

relabel-Zτ : ∀ {x y : Fin n} (xy : x < y) a t → X x y xy • Zτ a t • X x y xy ≈ Zτ (τ x y a) t
relabel-Zτ xy a true = relabel-Z xy a
relabel-Zτ xy a false = trans (cright left-unit) (X-X xy)

-- X_[c,d] (X_[m,p] Zτ_[m]) ≈ (X_[m′,p] Zτ_[m′]) X_[c,d], m′ the image of m.
move-X : ∀ {c d m p m′ : Fin n} .(cd : c < d) (mp : m < p) (m′p : m′ < p) t → τ c d m ≡ m′ → τ c d p ≡ p →
         X c d cd • (X m p mp • Zτ m t) ≈ (X m′ p m′p • Zτ m′ t) • X c d cd
move-X {c} {d} {m} {p} {m′} cd mp m′p t τm τp = conj-right cd (begin
  X′ • (X m p mp • Zτ m t) • X′                 ≈⟨ conj-• cd (X m p mp) (Zτ m t) ⟩
  (X′ • X m p mp • X′) • (X′ • Zτ m t • X′)     ≈⟨ cong (relabel-X (rc cd) mp) (relabel-Zτ (rc cd) m t) ⟩
  Xs (τ c d m) (τ c d p) • Zτ (τ c d m) t       ≈⟨ refl′ (≡.cong₂ (λ a b → Xs a b • Zτ a t) τm τp) ⟩
  Xs m′ p • Zτ m′ t                             ≈⟨ cleft refl′ (Xs-< m′p) ⟩
  X m′ p m′p • Zτ m′ t                          ∎)
  where X′ = X c d cd

-- τ_[m,p] takes an index ≤ p other than m below p.
τ-below : ∀ {m p c : Fin n} → m < p → c ≤ p → c ≢ m → τ m p c < p
τ-below {m} {p} {c} m<p c≤p c≢m = at (c FinP.≟ p)
  where
  at : Dec (c ≡ p) → τ m p c < p
  at (yes ≡.refl) = ≡.subst (_< c) (≡.sym (τ-q m c (<⇒≢ m<p))) m<p
  at (no c≢p) = ≡.subst (_< p) (≡.sym (τ-o m p c c≢m c≢p)) (FinP.≤∧≢⇒< c≤p c≢p)

------------------------------------------------------------------------
-- The edges out of a state whose pivot column is a unit

module At (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p)
          (k0 : lde (col s p) ≡ 0) (ih : EdgesBelow (level s)) where

  open PC s o ps using (v ; W ; v≡ ; syl≡ ; lvl ; zero> ; norm ; unit)
  open Below {L = level s} ih

  private
    be : Beyond p s
    be = proj₂ (pivot-just s ps)

    ne-s : col s p ≢ col 𝕀 p
    ne-s = proj₁ (pivot-just s ps)

    U = unit k0

  m : Fin n
  m = proj₁ U

  uW : UV m (W ! m) W
  uW = mkUV (proj₁ (proj₂ (proj₂ U))) ≡.refl (proj₁ (proj₂ (proj₂ (proj₂ U))))

  m≤p : m ≤ p
  m≤p = proj₂ (proj₂ (proj₂ (proj₂ U)))

  col0 : col s p ≡ scV 0 W
  col0 = ≡.trans v≡ (≡.cong (λ k → scV k W) k0)

  N≡ : syl s ≡ sylData p 0 W
  N≡ = ≡.trans syl≡ (≡.cong (λ k → sylData p k W) k0)

  pN : Path (syl s) s o
  pN = path-normal s o ps

  -- After the normal syllable, s is I from p on.
  NsAtI : AtI p (actMʷ (syl s) s)
  NsAtI = Beyond-actMʷ (syl s) {p} {s} within be , colN
    where
    us = unit-step {p = p} W (≡.trans norm (≡.cong (2 ℕ.^_) k0)) zero>
    within : Within p (syl s)
    within = ≡.subst (Within p) (≡.sym N≡) (proj₁ us)
    colN : col (actMʷ (syl s) s) p ≡ col 𝕀 p
    colN = ≡.trans (col-actMʷ (syl s) s p)
             (≡.trans (≡.cong₂ actVʷ N≡ col0) (≡.trans (proj₂ us) (≡.sym (col𝕀≡ p))))

  lowL : ∀ {L} → L <ₗ (suc (toℕ p) , lde v , nodd W) → L <ₗ level s
  lowL {L} lt = ≡.subst (L <ₗ_) (≡.sym lvl) lt

  lowS : (V : Word (Gen n)) → Under p V → BelowSrc (level s) V (actMʷ (syl s) s)
  lowS V uV = ≡.subst (λ L → BelowSrc L V (actMʷ (syl s) s)) (≡.sym lvl) (under-below V uV NsAtI (lde v) (nodd W))

  colg : (g : Gen n) → col (actM g s) p ≡ actV g (scV 0 W)
  colg g = ≡.trans (col-actM g s p) (≡.cong (actV g) col0)

  --------------------------------------------------------------------
  -- The three kinds of edge

  -- g does not touch m: the same syllable, and V N ≈ N g.
  same : (g : Gen n) → top g ≤ p → (∀ y → y ∈ₛ g → y ≢ m) → (V : Word (Gen n)) → Under p V →
         V • syl s ≈ syl s • [ g ]ʷ → Path [ g ]ʷ s o
  same g tg off V uV rel = bridge g s o (syl s) (syl s) V pN pN′ (lowS V uV) rel
    where
    gs = actM g s
    van : ∀ y → y ∈ₛ g → col s p ! y ≡ DR.0#
    van y y∈g = ≡.trans (≡.cong (_! y) col0)
                  (≡.trans (scV-! 0 W y) (≡.trans (≡.cong (sc 0) (UV.off uW y (off y y∈g))) (sc-0 0)))
    colg′ : col gs p ≡ col s p
    colg′ = ≡.trans (col-actM g s p) (actV-vanish g (col s p) van)
    pv′ : pivot gs ≡ just p
    pv′ = pivot-char gs (λ e → ne-s (≡.trans (≡.sym colg′) e)) (Beyond-actM g {M = s} tg be)
    sylg : syl gs ≡ syl s
    sylg = ≡.trans (syl-just gs pv′)
             (≡.trans (≡.cong (λ u → sylData p (lde u) (num u)) colg′) (≡.sym (syl-just s ps)))
    pN′ : Path (syl s) gs (ColOrth-actMʷ [ g ]ʷ o)
    pN′ = ≡.subst (λ w → Path w gs (ColOrth-actMʷ [ g ]ʷ o)) sylg (path-normal gs (ColOrth-actMʷ [ g ]ʷ o) pv′)

  -- g takes the unit to e_p: g·s lies below.
  drop : (g : Gen n) → top g ≤ p → actV g (scV 0 W) ≡ scV 0 (eᶻ p) → Path [ g ]ʷ s o
  drop g tg e = back-below g s o (lowL (level-below (actM g s) (≡.trans (colg g) (≡.trans e (≡.sym (col𝕀≡ p))))
                                                      (Beyond-actM g {M = s} tg be) (lde v) (nodd W)))

  -- g moves the unit: g·s is a unit state, with its normal syllable.
  moved : (g : Gen n) → top g ≤ p → (m′ : Fin n) (u′ : Z) (W′ : Vec Z n) → actV g (scV 0 W) ≡ scV 0 W′ →
          UV m′ u′ W′ → m′ ≢ p ⊎ u′ ≡ ZR.- ZR.1# → Path (sylData p 0 W′) (actM g s) (ColOrth-actMʷ [ g ]ʷ o)
  moved g tg m′ u′ W′ e uv h =
    ≡.subst (λ w → Path w gs (ColOrth-actMʷ [ g ]ʷ o)) sylg (path-normal gs (ColOrth-actMʷ [ g ]ʷ o) pv′)
    where
    gs = actM g s
    eq : col gs p ≡ scV 0 W′
    eq = ≡.trans (colg g) e
    x≢ = UV-ne p uv h
    pv′ : pivot gs ≡ just p
    pv′ = pivot-char gs (ne-𝕀-at gs p 0 W′ eq (inj₁ ≡.refl) (proj₁ x≢) (proj₂ x≢)) (Beyond-actM g {M = s} tg be)
    sylg : syl gs ≡ sylData p 0 W′
    sylg = syl-of gs pv′ 0 W′ eq (inj₁ ≡.refl)

  -- H_[c,d] touching m: a pair.
  pair : (c d : Fin n) .(cd : c < d) → d ≤ p → c ≡ m ⊎ d ≡ m →
         ((pos : 0 ℕ.< toℕ c) → Path (X (zeroOf c) c (zeroOf-< c pos)) s o) → Path [ H-gen c d cd ]ʷ s o
  pair c d cd d≤p mem xedge = edge-H-pair s o c d cd pv′ (Pair.syl≡ w (rc cd) uc ud zw gs pv′ eq) xedge
    where
    c≢d : c ≢ d
    c≢d = <⇒≢ cd
    gs = actM (H-gen c d cd) s
    w = Hᶻ c d W
    eq : col gs p ≡ scV 1 w
    eq = ≡.trans (colg (H-gen c d cd)) (actV-H c d cd 0 W)
    z0 : ∀ x → x ≢ c → x ≢ d → W ! x ≡ ZR.0#
    z0 x x≢c x≢d = UV.off uW x (at mem)
      where
      at : c ≡ m ⊎ d ≡ m → x ≢ m
      at (inj₁ c≡m) e = x≢c (≡.trans e (≡.sym c≡m))
      at (inj₂ d≡m) e = x≢d (≡.trans e (≡.sym d≡m))
    units : (Unit1 (W ! c) × W ! d ≡ ZR.0#) ⊎ (W ! c ≡ ZR.0# × Unit1 (W ! d))
    units = at mem
      where
      um = UV.unit uW
      at : c ≡ m ⊎ d ≡ m → (Unit1 (W ! c) × W ! d ≡ ZR.0#) ⊎ (W ! c ≡ ZR.0# × Unit1 (W ! d))
      at (inj₁ c≡m) = inj₁ (≡.subst (λ x → Unit1 (W ! x)) (≡.sym c≡m) um ,
                            UV.off uW d (λ e → c≢d (≡.trans c≡m (≡.sym e))))
      at (inj₂ d≡m) = inj₂ (UV.off uW c (λ e → c≢d (≡.trans e (≡.sym d≡m))) ,
                            ≡.subst (λ x → Unit1 (W ! x)) (≡.sym d≡m) um)
    hp = H-pair W c≢d z0 units
    uc = proj₁ hp
    ud = proj₁ (proj₂ hp)
    zw = proj₂ (proj₂ hp)
    pv′ : pivot gs ≡ just p
    pv′ = pivot-char gs (ne-𝕀 gs p 0 w eq (Pair.min w (rc cd) uc ud zw)) (Beyond-actM (H-gen c d cd) {M = s} d≤p be)

  --------------------------------------------------------------------
  -- m < p: N = X_[m,p] Zτ_[m]

  module Lt (m<p : m < p) where

    σ = negᶻ (W ! m)

    m≢p : m ≢ p
    m≢p = <⇒≢ m<p

    N≡′ : syl s ≡ X m p m<p • Zτ m σ
    N≡′ = ≡.trans N≡ (unitSyl< uW m<p)

    relS : ∀ {g : Gen n} {V : Word (Gen n)} → X m p m<p • [ g ]ʷ • X m p m<p ≈ V →
           Zτ m σ • [ g ]ʷ ≈ [ g ]ʷ • Zτ m σ → V • syl s ≈ syl s • [ g ]ʷ
    relS conj comm = trans (cright refl′ N≡′) (trans (slide m<p conj comm) (cleft refl′ (≡.sym N≡′)))

    edge-Z : (c : Fin n) → c ≤ p → Path (Zʷ c) s o
    edge-Z c c≤p = by (c FinP.≟ m)
      where
      by : Dec (c ≡ m) → Path (Zʷ c) s o
      by (no c≢m) =
        same (Z-gen c) c≤p (λ { _ i-a → c≢m }) (Zʷ (τ m p c)) (τ-below m<p c≤p c≢m)
             (relS (relabel-Z m<p c) (Zτ-comm m σ (Z-gen c) ((≢-sym c≢m ∷ []) ∷ [])))
      by (yes ≡.refl) =
        via (Z-gen c) s o (sylData p 0 (Zᶻ c W)) (syl s)
            (moved (Z-gen c) c≤p c (ZR.- (W ! c)) (Zᶻ c W) (actV-Z c 0 W) (UV-Z≡ uW) (inj₁ m≢p)) rel pN
        where
        rel : sylData p 0 (Zᶻ c W) • Zʷ c ≈ syl s
        rel = begin
          sylData p 0 (Zᶻ c W) • Zʷ c                   ≈⟨ cleft refl′ (unitSyl< (UV-Z≡ uW) m<p) ⟩
          (X c p m<p • Zτ c (negᶻ (ZR.- (W ! c)))) • Zʷ c ≈⟨ cleft cright refl′ (≡.cong (Zτ c) (unit-negᶻ (UV.unit uW))) ⟩
          (X c p m<p • Zτ c (not σ)) • Zʷ c            ≈⟨ assoc ⟩
          X c p m<p • (Zτ c (not σ) • Zʷ c)            ≈⟨ cright Zτ-flip c σ ⟩
          X c p m<p • Zτ c σ                           ≈⟨ refl′ (≡.sym N≡′) ⟩
          syl s                                        ∎

    -- X_[m,p]: the unit goes to ±e_p.
    edge-Xmp : Path [ X-gen m p m<p ]ʷ s o
    edge-Xmp = by (UV.unit uW)
      where
      W′ = Xᶻ m p W
      act : actV (X-gen m p m<p) (scV 0 W) ≡ scV 0 W′
      act = actV-X m p m<p 0 W
      uv′ : UV p (W ! m) W′
      uv′ = ≡.subst (λ x → UV x (W ! m) W′) (τ-p m p) (UV-X m p m≢p uW)
      by : Unit1 (W ! m) → Path [ X-gen m p m<p ]ʷ s o
      by (inj₁ e1) = drop (X-gen m p m<p) FinP.≤-refl
        (≡.trans act (≡.cong (scV 0) (UV-e (mkUV (inj₁ ≡.refl) (≡.trans (UV.at uv′) e1) (UV.off uv′)))))
      by (inj₂ e1) =
        via (X-gen m p m<p) s o (sylData p 0 W′) (syl s) (moved (X-gen m p m<p) FinP.≤-refl p (W ! m) W′ act uv′ (inj₂ e1)) rel pN
        where
        rel : sylData p 0 W′ • X m p m<p ≈ syl s
        rel = begin
          sylData p 0 W′ • X m p m<p            ≈⟨ cleft refl′ (≡.trans (unitSyl≡ uv′) (≡.cong (λ z → Zτ p (negᶻ z)) e1)) ⟩
          Zʷ p • X m p m<p                      ≈⟨ flip-X m<p (axiom (c1 m<p)) ⟩
          X m p m<p • Zʷ m                      ≈⟨ cright refl′ (≡.cong (λ z → Zτ m (negᶻ z)) (≡.sym e1)) ⟩
          X m p m<p • Zτ m σ                    ≈⟨ refl′ (≡.sym N≡′) ⟩
          syl s                                 ∎

    to-mp : (c d : Fin n) .(cd : c < d) → c ≡ m → d ≡ p → Path [ X-gen c d cd ]ʷ s o
    to-mp c d cd ≡.refl ≡.refl = edge-Xmp

    edge-X : (c d : Fin n) .(cd : c < d) → d ≤ p → Path [ X-gen c d cd ]ʷ s o
    edge-X c d cd d≤p = by (c FinP.≟ m) (d FinP.≟ m)
      where
      cd′ = rc cd
      c≢d : c ≢ d
      c≢d = <⇒≢ cd
      c≤p : c ≤ p
      c≤p = ℕP.<⇒≤ (ℕP.<-≤-trans cd′ d≤p)
      -- m moves to m′.
      moving : c ≡ m ⊎ d ≡ m → Path [ X-gen c d cd ]ʷ s o
      moving mem = by′ (τ c d m FinP.≟ p)
        where
        m′ = τ c d m
        W′ = Xᶻ c d W
        uv′ : UV m′ (W ! m) W′
        uv′ = UV-X c d c≢d uW
        -- m′ is the other index.
        m′≤d : m′ ≤ d
        m′≤d = at mem
          where
          at : c ≡ m ⊎ d ≡ m → m′ ≤ d
          at (inj₁ ≡.refl) = ≡.subst (_≤ d) (≡.sym (τ-p c d)) FinP.≤-refl
          at (inj₂ ≡.refl) = ≡.subst (_≤ d) (≡.sym (τ-q c d c≢d)) (ℕP.<⇒≤ cd′)
        by′ : Dec (m′ ≡ p) → Path [ X-gen c d cd ]ʷ s o
        by′ (yes m′≡p) = at mem
          where
          at : c ≡ m ⊎ d ≡ m → Path [ X-gen c d cd ]ʷ s o
          at (inj₁ c≡m) = to-mp c d cd c≡m
            (≡.trans (≡.sym (τ-p c d)) (≡.trans (≡.cong (τ c d) c≡m) m′≡p))
          at (inj₂ d≡m) = ⊥-elim (FinP.<-irrefl c≡p (ℕP.<-≤-trans cd′ d≤p))
            where
            c≡p : c ≡ p
            c≡p = ≡.trans (≡.sym (τ-q c d c≢d)) (≡.trans (≡.cong (τ c d) d≡m) m′≡p)
        by′ (no m′≢p) =
          bridge (X-gen c d cd) s o (syl s) (sylData p 0 W′) (X c d cd) pN
            (moved (X-gen c d cd) d≤p m′ (W ! m) W′ (actV-X c d cd 0 W) uv′ (inj₁ m′≢p)) (lowS (X c d cd) d<p) rel
          where
          m′<p : m′ < p
          m′<p = FinP.≤∧≢⇒< (FinP.≤-trans m′≤d d≤p) m′≢p
          d≢p : d ≢ p
          d≢p d≡p = at mem
            where
            at : c ≡ m ⊎ d ≡ m → ⊥
            at (inj₁ c≡m) = m′≢p (≡.trans (≡.cong (τ c d) (≡.sym c≡m)) (≡.trans (τ-p c d) d≡p))
            at (inj₂ d≡m) = m≢p (≡.trans (≡.sym d≡m) d≡p)
          d<p : d < p
          d<p = FinP.≤∧≢⇒< d≤p d≢p
          τp : τ c d p ≡ p
          τp = τ-o c d p (λ e → FinP.<-irrefl (≡.sym e) (ℕP.<-≤-trans cd′ d≤p)) (≢-sym d≢p)
          rel : X c d cd • syl s ≈ sylData p 0 W′ • X c d cd
          rel = trans (cright refl′ N≡′)
                  (trans (move-X cd m<p m′<p σ ≡.refl τp) (cleft refl′ (≡.sym (unitSyl< uv′ m′<p))))
      by : Dec (c ≡ m) → Dec (d ≡ m) → Path [ X-gen c d cd ]ʷ s o
      by (yes c≡m) _ = moving (inj₁ c≡m)
      by (no c≢m) (yes d≡m) = moving (inj₂ d≡m)
      by (no c≢m) (no d≢m) =
        same (X-gen c d cd) d≤p (λ { _ X-a → c≢m ; _ X-b → d≢m }) (Xs (τ m p c) (τ m p d))
             (Under-Xs (τ m p c) (τ m p d) (τ-below m<p c≤p c≢m) (τ-below m<p d≤p d≢m))
             (relS (relabel-X m<p cd′) (Zτ-comm m σ (X-gen c d cd) ((≢-sym c≢m ∷ ≢-sym d≢m ∷ []) ∷ [])))

    edge-H : (c d : Fin n) .(cd : c < d) → d ≤ p → c ≢ m → d ≢ m → Path [ H-gen c d cd ]ʷ s o
    edge-H c d cd d≤p c≢m d≢m =
      same (H-gen c d cd) d≤p (λ { _ K-a → c≢m ; _ K-b → d≢m }) (Hs (τ m p c) (τ m p d))
           (Under-Hs (τ m p c) (τ m p d) (τ-below m<p c≤p c≢m) (τ-below m<p d≤p d≢m))
           (relS (relabel-H m<p cd′) (Zτ-comm m σ (H-gen c d cd) ((≢-sym c≢m ∷ ≢-sym d≢m ∷ []) ∷ [])))
      where
      cd′ = rc cd
      c≤p : c ≤ p
      c≤p = ℕP.<⇒≤ (ℕP.<-≤-trans cd′ d≤p)

  --------------------------------------------------------------------
  -- m = p: the unit is -1, and N = Z_[p]

  module Eq (m≡p : m ≡ p) where

    uWp : UV p (W ! p) W
    uWp = ≡.subst (λ x → UV x (W ! x) W) m≡p uW

    Wp : W ! p ≡ ZR.- ZR.1#
    Wp = by (UV.unit uWp)
      where
      by : Unit1 (W ! p) → W ! p ≡ ZR.- ZR.1#
      by (inj₁ e1) = ⊥-elim (ne-s (≡.trans col0 (≡.trans
        (≡.cong (scV 0) (UV-e (mkUV (inj₁ ≡.refl) (≡.trans (UV.at uWp) e1) (UV.off uWp)))) (≡.sym (col𝕀≡ p)))))
      by (inj₂ e1) = e1

    uW₋ : UV p (ZR.- ZR.1#) W
    uW₋ = mkUV (inj₂ ≡.refl) Wp (UV.off uWp)

    N≡″ : syl s ≡ Zʷ p
    N≡″ = ≡.trans N≡ (unitSyl≡ uW₋)

    sameE : (g : Gen n) → top g < p → Apart g (Z-gen p) → (∀ y → y ∈ₛ g → y ≢ p) → Path [ g ]ʷ s o
    sameE g tg ap off = same g (ℕP.<⇒≤ tg) (λ y y∈g e → off y y∈g (≡.trans e m≡p)) [ g ]ʷ tg
      (trans (cright refl′ N≡″) (trans (comm-gen g (Z-gen p) ap) (cleft refl′ (≡.sym N≡″))))

    edge-Z : (c : Fin n) → c ≤ p → Path (Zʷ c) s o
    edge-Z c c≤p = by (c FinP.≟ p)
      where
      by : Dec (c ≡ p) → Path (Zʷ c) s o
      by (yes ≡.refl) = drop (Z-gen c) c≤p (≡.trans (actV-Z c 0 W) (≡.cong (scV 0) (UV-e (UV-Z≡ uW₋))))
      by (no c≢p) = sameE (Z-gen c) (FinP.≤∧≢⇒< c≤p c≢p) ((c≢p ∷ []) ∷ []) (λ { _ i-a → c≢p })

    edge-X : (c d : Fin n) .(cd : c < d) → d ≤ p → Path [ X-gen c d cd ]ʷ s o
    edge-X c d cd d≤p = by (d FinP.≟ p)
      where
      cd′ = rc cd
      c≢d : c ≢ d
      c≢d = <⇒≢ cd
      onto : (d′ : Fin n) .(cd : c < d′) → d′ ≡ p → Path [ X-gen c d′ cd ]ʷ s o
      onto d′ cd ≡.refl =
        via (X-gen c d′ cd) s o (sylData d′ 0 W′) (syl s) (moved (X-gen c d′ cd) FinP.≤-refl c (ZR.- ZR.1#) W′ act uv′ (inj₁ c≢d′)) rel pN
        where
        c≢d′ : c ≢ d′
        c≢d′ = <⇒≢ cd
        W′ = Xᶻ c d′ W
        act : actV (X-gen c d′ cd) (scV 0 W) ≡ scV 0 W′
        act = actV-X c d′ cd 0 W
        uv′ : UV c (ZR.- ZR.1#) W′
        uv′ = ≡.subst (λ x → UV x (ZR.- ZR.1#) W′) (τ-q c d′ c≢d′) (UV-X c d′ c≢d′ uW₋)
        rel : sylData d′ 0 W′ • X c d′ cd ≈ syl s
        rel = begin
          sylData d′ 0 W′ • X c d′ cd               ≈⟨ cleft refl′ (unitSyl< uv′ (rc cd)) ⟩
          (X c d′ cd • Zʷ c) • X c d′ cd            ≈⟨ assoc ⟩
          X c d′ cd • Zʷ c • X c d′ cd              ≈⟨ relabel-Z (rc cd) c ⟩
          Zʷ (τ c d′ c)                             ≈⟨ refl′ (≡.cong Zʷ (τ-p c d′)) ⟩
          Zʷ d′                                     ≈⟨ refl′ (≡.sym N≡″) ⟩
          syl s                                     ∎
      by : Dec (d ≡ p) → Path [ X-gen c d cd ]ʷ s o
      by (yes d≡p) = onto d cd d≡p
      by (no d≢p) = sameE (X-gen c d cd) d<p ((c≢p ∷ []) ∷ (d≢p ∷ []) ∷ []) (λ { _ X-a → c≢p ; _ X-b → d≢p })
        where
        d<p : d < p
        d<p = FinP.≤∧≢⇒< d≤p d≢p
        c≢p : c ≢ p
        c≢p e = FinP.<-irrefl e (ℕP.<-trans cd′ d<p)

    edge-H : (c d : Fin n) .(cd : c < d) → d ≤ p → c ≢ m → d ≢ m → Path [ H-gen c d cd ]ʷ s o
    edge-H c d cd d≤p c≢m d≢m = sameE (H-gen c d cd) d<p ((c≢p ∷ []) ∷ (d≢p ∷ []) ∷ []) (λ { _ K-a → c≢p ; _ K-b → d≢p })
      where
      cd′ = rc cd
      d≢p : d ≢ p
      d≢p e = d≢m (≡.trans e (≡.sym m≡p))
      c≢p : c ≢ p
      c≢p e = c≢m (≡.trans e (≡.sym m≡p))
      d<p : d < p
      d<p = FinP.≤∧≢⇒< d≤p d≢p

  --------------------------------------------------------------------
  -- All edges

  private
    mcase : m < p ⊎ m ≡ p
    mcase = at (m FinP.≟ p)
      where
      at : Dec (m ≡ p) → m < p ⊎ m ≡ p
      at (yes e) = inj₂ e
      at (no ne) = inj₁ (FinP.≤∧≢⇒< m≤p ne)

    module Ab = Above.At s o p be

  edge-Z : (c : Fin n) → Path (Zʷ c) s o
  edge-Z c = by (p FinP.<? c)
    where
    by : Dec (p < c) → Path (Zʷ c) s o
    by (yes p<c) = Ab.edge-Z c p<c
    by (no p≮c) = at mcase
      where
      at : m < p ⊎ m ≡ p → Path (Zʷ c) s o
      at (inj₁ lt) = Lt.edge-Z lt c (ℕP.≮⇒≥ p≮c)
      at (inj₂ eq) = Eq.edge-Z eq c (ℕP.≮⇒≥ p≮c)

  edge-X : (c d : Fin n) .(cd : c < d) → Path [ X-gen c d cd ]ʷ s o
  edge-X c d cd = by (p FinP.<? d)
    where
    by : Dec (p < d) → Path [ X-gen c d cd ]ʷ s o
    by (yes p<d) = Ab.edge-X c d cd p<d
    by (no p≮d) = at mcase
      where
      at : m < p ⊎ m ≡ p → Path [ X-gen c d cd ]ʷ s o
      at (inj₁ lt) = Lt.edge-X lt c d cd (ℕP.≮⇒≥ p≮d)
      at (inj₂ eq) = Eq.edge-X eq c d cd (ℕP.≮⇒≥ p≮d)

  edge-H : (c d : Fin n) .(cd : c < d) → Path [ H-gen c d cd ]ʷ s o
  edge-H c d cd = by (p FinP.<? d)
    where
    xedge : (pos : 0 ℕ.< toℕ c) → Path (X (zeroOf c) c (zeroOf-< c pos)) s o
    xedge pos = edge-X (zeroOf c) c (zeroOf-< c pos)
    by : Dec (p < d) → Path [ H-gen c d cd ]ʷ s o
    by (yes p<d) = Ab.edge-H c d cd p<d edge-X
    by (no p≮d) = on (c FinP.≟ m) (d FinP.≟ m)
      where
      d≤p = ℕP.≮⇒≥ p≮d
      on : Dec (c ≡ m) → Dec (d ≡ m) → Path [ H-gen c d cd ]ʷ s o
      on (yes c≡m) _ = pair c d cd d≤p (inj₁ c≡m) xedge
      on (no c≢m) (yes d≡m) = pair c d cd d≤p (inj₂ d≡m) xedge
      on (no c≢m) (no d≢m) = at mcase
        where
        at : m < p ⊎ m ≡ p → Path [ H-gen c d cd ]ʷ s o
        at (inj₁ lt) = Lt.edge-H lt c d cd d≤p c≢m d≢m
        at (inj₂ eq) = Eq.edge-H eq c d cd d≤p c≢m d≢m

  edges : ∀ (g : Gen n) → Path [ g ]ʷ s o
  edges (Z-gen c) = edge-Z c
  edges (X-gen c d cd) = edge-X c d cd
  edges (H-gen c d cd) = edge-H c d cd
