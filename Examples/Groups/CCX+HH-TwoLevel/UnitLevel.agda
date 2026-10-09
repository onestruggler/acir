------------------------------------------------------------------------
-- Presentations of groups
--
-- The basic edges at the levels with exponent 0 (Lemma A.20, the cases
-- k = 0: Subcases 1.1, 2.1 and 3.1).
--
-- There the pivot column of s is a unit ±e_m with m ≤ p (Lemma 3.3),
-- and the normal syllable N is X_[m,p] (-1)_[m]^τ (m < p) or (-1)_[p]
-- (m = p, where the unit is -1).  For a basic generator g acting on
-- indices ≤ p:
--
-- * if g does not touch m, g·s has the same syllable N, and the square
--   closes with a word below p (g itself, or g conjugated by X_[m,p]);
-- * if g moves the unit, g·s is a unit state again, and its syllable
--   undoes g, up to an adjacent X below p (or g is the normal
--   syllable: it takes the unit to e_p);
-- * K_[0,1,2,3] touching m raises the exponent: that edge goes up.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.CCX+HH-TwoLevel.UnitLevel {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D ; module DR ; oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Scale using (sc ; sc-0)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (scV ; scV-! ; lde ; num ; lde-char ; Minimal ; Odd)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.ColumnAction
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
open import Examples.Groups.CCX+HH-TwoLevel.Pivot
  using (pivot ; pivot-just ; pivot-char ; Beyond ; level ; level-just ; _<ₗ_ ; <ₗ-irrefl)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable
  using (syl ; syl-just ; top ; Within ; Beyond-actM ; Beyond-actMʷ ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡ ; zeroV ; actV-0)
open import Examples.Groups.CCX+HH-TwoLevel.Step using (unit-step)
open import Examples.Groups.CCX+HH-TwoLevel.Derived {n} using (gen-gen ; conj ; conj′)
open import Examples.Groups.CCX+HH-TwoLevel.Signs {n}
open import Examples.Groups.CCX+HH-TwoLevel.Levels using (<ₗ-trans)
open import Examples.Groups.CCX+HH-TwoLevel.Reduction {n} using (Path ; Low ; EdgesBelow ; _≤ₗ_)
open import Examples.Groups.CCX+HH-TwoLevel.PathTools {n} using (via ; path-cong ; module Below)
open import Examples.Groups.CCX+HH-TwoLevel.States {n} using (path-normal ; syl-of ; level-of ; ne-𝕀 ; ne-𝕀-at)
open import Examples.Groups.CCX+HH-TwoLevel.UnitTools {n}
import Examples.Groups.CCX+HH-TwoLevel.PivotColumn as PC

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

  rc : ∀ {a b : Fin n} → .(a < b) → a < b
  rc {a} {b} lt = recompute (a FinP.<? b) lt

  e-a : (a : Fin n) → eᶻ a ! a ≡ + 1
  e-a a = ≡.trans (eᶻ-! a a) (eδ-refl a)

  e-≢ : {a x : Fin n} → x ≢ a → eᶻ a ! x ≡ + 0
  e-≢ {a} {x} x≢a = ≡.trans (eᶻ-! a x) (eδ-≢ x≢a)

  ≢-sym : {a b : Fin n} → a ≢ b → b ≢ a
  ≢-sym ne e = ne (≡.sym e)

  ≤∧≢⇒< : {a b : Fin n} → a ≤ b → a ≢ b → a < b
  ≤∧≢⇒< a≤b a≢b = ℕP.≤∧≢⇒< a≤b (λ e → a≢b (FinP.toℕ-injective e))

------------------------------------------------------------------------
-- Relations among X's on three indices

-- m < x < p: X_[m,p] X_[x,p] = X_[m,x] X_[m,p].
XX-lt : {m x p : Fin n} .(mx : m < x) .(xp : x < p) .(mp : m < p) → X m p mp • X x p xp ≈ X m x mx • X m p mp
XX-lt mx xp mp = trans (sym (axiom (r3b mx xp mp))) (sym (axiom (r3a mx xp mp)))

-- x < m < p: X_[m,p] X_[x,p] = X_[x,m] X_[m,p].
XX-gt : {m x p : Fin n} .(xm : x < m) .(mp : m < p) .(xp : x < p) → X m p mp • X x p xp ≈ X x m xm • X m p mp
XX-gt {m} {x} {p} xm mp xp = begin
  Xmp • X x p xp                        ≈⟨ cright conj′ (X-gen m p mp) (axiom (r3b xm mp xp)) ⟩
  Xmp • (Xmp • (X x m xm • Xmp))        ≈⟨ sym assoc ⟩
  (Xmp • Xmp) • (X x m xm • Xmp)        ≈⟨ cleft gen-gen (X-gen m p mp) ⟩
  ε • (X x m xm • Xmp)                  ≈⟨ left-unit ⟩
  X x m xm • Xmp                        ∎
  where Xmp = X m p mp

-- x < y < p: X_[y,p] X_[x,y] = X_[x,y] X_[x,p].
XX-up : {x y p : Fin n} .(xy : x < y) .(yp : y < p) .(xp : x < p) → X y p yp • X x y xy ≈ X x y xy • X x p xp
XX-up xy yp xp = sym (axiom (r3a xy yp xp))

-- x < y < p: X_[x,p] X_[x,y] = X_[x,y] X_[y,p].
XX-down : {x y p : Fin n} .(xy : x < y) .(yp : y < p) .(xp : x < p) → X x p xp • X x y xy ≈ X x y xy • X y p yp
XX-down {x} {y} {p} xy yp xp = begin
  X x p xp • Xxy                         ≈⟨ cleft conj (X-gen x y xy) (axiom (r3a xy yp xp)) ⟩
  (Xxy • (X y p yp • Xxy)) • Xxy         ≈⟨ assoc ⟩
  Xxy • ((X y p yp • Xxy) • Xxy)         ≈⟨ cright assoc ⟩
  Xxy • (X y p yp • (Xxy • Xxy))         ≈⟨ cright cright gen-gen (X-gen x y xy) ⟩
  Xxy • (X y p yp • ε)                   ≈⟨ cright right-unit ⟩
  Xxy • X y p yp                         ∎
  where Xxy = X x y xy

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

  σ : Bool
  σ = negℤ (W ! m)

  -- If m = p, the unit is -1 (s is not I at p).
  m≡p⇒neg : m ≡ p → σ ≡ true
  m≡p⇒neg m≡p = at (UV.unit uW)
    where
    at : Unit1 (W ! m) → σ ≡ true
    at (inj₂ e) = ≡.cong negℤ e
    at (inj₁ e) = ⊥-elim (ne-s (≡.trans col0 (≡.trans (≡.cong (scV 0) W≡) (≡.sym (col𝕀≡ p)))))
      where
      W≡ : W ≡ eᶻ p
      W≡ = vec-ext λ x → atx x (x FinP.≟ p)
        where
        atx : ∀ x → Dec (x ≡ p) → W ! x ≡ eᶻ p ! x
        atx x (yes ≡.refl) = ≡.trans (≡.cong (W !_) (≡.sym m≡p)) (≡.trans e (≡.sym (e-a x)))
        atx x (no x≢p) = ≡.trans (UV.off uW x (λ x≡m → x≢p (≡.trans x≡m m≡p))) (≡.sym (e-≢ x≢p))

  -- After the normal syllable, s is I from p on.
  NsAtI : AtI p (actMʷ (syl s) s)
  NsAtI = Beyond-actMʷ (syl s) {p} {s} within be , colN
    where
    us = unit-step {p = p} W (≡.trans norm (≡.cong (4 ℕ.^_) k0)) zero>
    within : Within p (syl s)
    within = ≡.subst (Within p) (≡.sym N≡) (proj₁ us)
    colN : col (actMʷ (syl s) s) p ≡ col 𝕀 p
    colN = ≡.trans (col-actMʷ (syl s) s p)
             (≡.trans (≡.cong₂ actVʷ N≡ col0) (≡.trans (proj₂ us) (≡.sym (col𝕀≡ p))))

  lowS : (V : Word (Gen n)) → Under p V → Low (level s) V (actMʷ (syl s) s)
  lowS V uV = ≡.subst (λ L → Low L V (actMʷ (syl s) s)) (≡.sym lvl) (under-below V uV NsAtI (lde v) (nodd W))

  colg : (g : Gen n) → col (actM g s) p ≡ actV g (scV 0 W)
  colg g = ≡.trans (col-actM g s p) (≡.cong (actV g) col0)

  --------------------------------------------------------------------
  -- The kinds of edge

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

  -- g is the normal syllable (it takes the unit to e_p).
  normal : (g : Gen n) → syl s ≈ [ g ]ʷ → Path [ g ]ʷ s o
  normal g eq = path-cong eq s o pN

  -- g moves the unit: g·s is a unit state, with its normal syllable.
  moved : (g : Gen n) → top g ≤ p → (m′ : Fin n) (u′ : ℤ) (W′ : Vec ℤ n) → actV g (scV 0 W) ≡ scV 0 W′ →
          UV m′ u′ W′ → m′ ≢ p ⊎ u′ ≡ -[1+ 0 ] → Path (sylData p 0 W′) (actM g s) (ColOrth-actMʷ [ g ]ʷ o)
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

  --------------------------------------------------------------------
  -- The normal syllable, by the position of the unit

  N< : (m<p : m < p) → syl s ≡ X m p m<p • Mτ m σ
  N< m<p = ≡.trans N≡ (unitSyl< uW m<p)

  N≡p : m ≡ p → syl s ≡ M p
  N≡p e = ≡.trans N≡ (≡.trans (unitSyl≡ (≡.subst (λ q → UV q (W ! m) W) e uW)) (≡.cong (Mτ p) (m≡p⇒neg e)))

  -- A generator apart from m and p commutes with the normal syllable.
  comm-N : (g : Gen n) → Apart m g → Apart p g → [ g ]ʷ • syl s ≈ syl s • [ g ]ʷ
  comm-N g am ap = by (FinP.<-cmp m p)
    where
    comm-X : ∀ {a b : Fin n} .(ab : a < b) → Apart a g → Apart b g → [ g ]ʷ • X a b ab ≈ X a b ab • [ g ]ʷ
    comm-X {a} {b} ab aa ab′ = comm-gX g aa ab′
      where
      comm-gX : (g : Gen n) → Apart a g → Apart b g → [ g ]ʷ • X a b ab ≈ X a b ab • [ g ]ʷ
      comm-gX (M-gen c) ca cb = sym (axiom (r2b ab (≢-sym ca) (≢-sym cb)))
      comm-gX (X-gen c d q) (ac , ad) (bc , bd) = axiom (r2a q ab (≢-sym ac) (≢-sym bc) (≢-sym ad) (≢-sym bd))
      comm-gX (K-gen c d e f q r t) (ac , ad , ae , af) (bc , bd , be′ , bf) =
        sym (axiom (r2c ab q r t ac ad ae af bc bd be′ bf))
    by : Tri (m < p) (m ≡ p) (p < m) → [ g ]ʷ • syl s ≈ syl s • [ g ]ʷ
    by (tri< m<p _ _) = begin
      G • syl s                        ≈⟨ cright refl′ (N< m<p) ⟩
      G • (X m p m<p • Mτ m σ)         ≈⟨ sym assoc ⟩
      (G • X m p m<p) • Mτ m σ         ≈⟨ cleft comm-X m<p am ap ⟩
      (X m p m<p • G) • Mτ m σ         ≈⟨ assoc ⟩
      X m p m<p • (G • Mτ m σ)         ≈⟨ cright sym (Mτ-comm m σ g am) ⟩
      X m p m<p • (Mτ m σ • G)         ≈⟨ sym assoc ⟩
      (X m p m<p • Mτ m σ) • G         ≈⟨ cleft refl′ (≡.sym (N< m<p)) ⟩
      syl s • G                        ∎
      where G = [ g ]ʷ
    by (tri≈ _ m≡p _) = trans (cright refl′ (N≡p m≡p))
                          (trans (sym (comm-M p g ap)) (cleft refl′ (≡.sym (N≡p m≡p))))
    by (tri> _ _ p<m) = ⊥-elim (FinP.<-irrefl ≡.refl (ℕP.<-≤-trans p<m m≤p))

  --------------------------------------------------------------------
  -- (-1)_[a], a = 0 (Case 2.1)

  edge-M : (a : Fin n) → toℕ a ≡ 0 → a ≤ p → Path (M a) s o
  edge-M a a0 a≤p = by (a FinP.≟ m)
    where
    by : Dec (a ≡ m) → Path (M a) s o
    by (no a≢m) = same (M-gen a) a≤p (λ { y M-a → a≢m }) (M a) a<p (comm-N (M-gen a) (≢-sym a≢m) (≢-sym a≢p))
      where
      a≢p : a ≢ p
      a≢p ≡.refl = a≢m (FinP.toℕ-injective (≡.trans a0 (≡.sym (ℕP.n≤0⇒n≡0 (≡.subst (toℕ m ℕ.≤_) a0 m≤p)))))
      a<p : a < p
      a<p = ≤∧≢⇒< a≤p a≢p
    by (yes ≡.refl) = at (FinP.<-cmp a p)
      where
      at : Tri (a < p) (a ≡ p) (p < a) → Path (M a) s o
      at (tri≈ _ a≡p _) = normal (M-gen a) (trans (refl′ (N≡p a≡p)) (refl′ (≡.cong M (≡.sym a≡p))))
      at (tri> _ _ p<a) = ⊥-elim (FinP.<-irrefl ≡.refl (ℕP.<-≤-trans p<a a≤p))
      at (tri< a<p _ _) =
        via (M-gen a) s o (sylData p 0 (Mᶻ a W)) (syl s)
            (moved (M-gen a) a≤p a (ℤ.- (W ! a)) (Mᶻ a W) (actV-M a 0 W) (UV-M≡ uW) (inj₁ (<⇒≢ a<p))) rel pN
        where
        rel : sylData p 0 (Mᶻ a W) • M a ≈ syl s
        rel = begin
          sylData p 0 (Mᶻ a W) • M a                       ≈⟨ cleft refl′ (unitSyl< (UV-M≡ uW) a<p) ⟩
          (X a p a<p • Mτ a (negℤ (ℤ.- (W ! a)))) • M a    ≈⟨ cleft cright refl′ (≡.cong (Mτ a) (unit-negℤ (UV.unit uW))) ⟩
          (X a p a<p • Mτ a (not σ)) • M a                 ≈⟨ assoc ⟩
          X a p a<p • (Mτ a (not σ) • M a)                 ≈⟨ cright Mτ-flip a σ ⟩
          X a p a<p • Mτ a σ                               ≈⟨ refl′ (≡.sym (N< a<p)) ⟩
          syl s                                            ∎

  --------------------------------------------------------------------
  -- X_[x,y], y = x + 1 (Case 1.1)

  private
    X≡ : {a b a′ b′ : Fin n} .{q : a < b} .{q′ : a′ < b′} → a ≡ a′ → b ≡ b′ → X a b q ≡ X a′ b′ q′
    X≡ ≡.refl ≡.refl = ≡.refl

    -- The unit is -1 when its syllable has the sign.
    neg-1 : negℤ (W ! m) ≡ true → W ! m ≡ -[1+ 0 ]
    neg-1 e = at (UV.unit uW) e
      where
      at : Unit1 (W ! m) → negℤ (W ! m) ≡ true → W ! m ≡ -[1+ 0 ]
      at (inj₂ e′) _ = e′
      at (inj₁ e′) t = ⊥-elim (f≢t (≡.trans (≡.sym (≡.cong negℤ e′)) t))
        where
        f≢t : false ≢ true
        f≢t ()

  edge-X : (x y : Fin n) .(xy : x < y) → toℕ y ≡ suc (toℕ x) → y ≤ p → Path (X x y xy) s o
  edge-X x y xy adj y≤p = by (m FinP.≟ x) (m FinP.≟ y)
    where
    x≢y = <⇒≢ xy
    x<p : x < p
    x<p = ℕP.<-≤-trans (rc xy) y≤p
    gX = X-gen x y xy
    XW = Xᶻ x y W
    eX : actV gX (scV 0 W) ≡ scV 0 XW
    eX = actV-X x y xy 0 W
    by : Dec (m ≡ x) → Dec (m ≡ y) → Path (X x y xy) s o
    -- The unit at x.
    by (yes m≡x) _ = at-y (y FinP.≟ p)
      where
      uX : UV y (W ! m) XW
      uX = UV-X-x x≢y (≡.subst (λ q → UV q (W ! m) W) m≡x uW)
      m<p : m < p
      m<p = ≡.subst (_< p) (≡.sym m≡x) x<p
      Nx : syl s ≡ X x p x<p • Mτ x σ
      Nx = ≡.trans (N< m<p) (≡.cong₂ _•_ (X≡ m≡x ≡.refl) (≡.cong (λ q → Mτ q σ) m≡x))
      at-y : Dec (y ≡ p) → Path (X x y xy) s o
      at-y (yes y≡p) = by-σ σ ≡.refl
        where
        by-σ : (t : Bool) → σ ≡ t → Path (X x y xy) s o
        by-σ false e = normal gX (begin
          syl s                       ≈⟨ refl′ Nx ⟩
          X x p x<p • Mτ x σ          ≈⟨ cright refl′ (≡.cong (Mτ x) e) ⟩
          X x p x<p • ε               ≈⟨ right-unit ⟩
          X x p x<p                   ≈⟨ refl′ (X≡ ≡.refl (≡.sym y≡p)) ⟩
          X x y xy                    ∎)
        by-σ true e =
          via gX s o (sylData p 0 XW) (syl s)
              (moved gX y≤p y (W ! m) XW eX uX (inj₂ (neg-1 e))) rel pN
          where
          uX′ : UV p (W ! m) XW
          uX′ = ≡.subst (λ q → UV q (W ! m) XW) y≡p uX
          rel : sylData p 0 XW • X x y xy ≈ syl s
          rel = begin
            sylData p 0 XW • X x y xy              ≈⟨ cleft refl′ (≡.trans (unitSyl≡ uX′) (≡.cong (Mτ p) e)) ⟩
            M p • X x y xy                         ≈⟨ cright refl′ (X≡ ≡.refl y≡p) ⟩
            M p • X x p x<p                        ≈⟨ sym (X-M′ x<p) ⟩
            X x p x<p • M x                        ≈⟨ cright refl′ (≡.cong (Mτ x) (≡.sym e)) ⟩
            X x p x<p • Mτ x σ                     ≈⟨ refl′ (≡.sym Nx) ⟩
            syl s                                  ∎
      at-y (no y≢p) =
        bridge gX s o (syl s) (sylData p 0 XW) (X x y xy) pN
               (moved gX y≤p y (W ! m) XW eX uX (inj₁ y≢p)) (lowS (X x y xy) y<p) rel
        where
        y<p : y < p
        y<p = ≤∧≢⇒< y≤p y≢p
        rel : X x y xy • syl s ≈ sylData p 0 XW • X x y xy
        rel = begin
          X x y xy • syl s                           ≈⟨ cright refl′ Nx ⟩
          X x y xy • (X x p x<p • Mτ x σ)            ≈⟨ sym assoc ⟩
          (X x y xy • X x p x<p) • Mτ x σ            ≈⟨ cleft sym (XX-up xy y<p x<p) ⟩
          (X y p y<p • X x y xy) • Mτ x σ            ≈⟨ assoc ⟩
          X y p y<p • (X x y xy • Mτ x σ)            ≈⟨ cright Mτ-X′ xy σ ⟩
          X y p y<p • (Mτ y σ • X x y xy)            ≈⟨ sym assoc ⟩
          (X y p y<p • Mτ y σ) • X x y xy            ≈⟨ cleft refl′ (≡.sym (unitSyl< uX y<p)) ⟩
          sylData p 0 XW • X x y xy                  ∎
    -- The unit at y.
    by (no m≢x) (yes m≡y) = at-y (y FinP.≟ p)
      where
      uY : UV x (W ! m) XW
      uY = UV-X-y x≢y (≡.subst (λ q → UV q (W ! m) W) m≡y uW)
      at-y : Dec (y ≡ p) → Path (X x y xy) s o
      at-y (yes y≡p) =
        via gX s o (sylData p 0 XW) (syl s)
            (moved gX y≤p x (W ! m) XW eX uY (inj₁ (<⇒≢ x<p))) rel pN
        where
        m≡p = ≡.trans m≡y y≡p
        rel : sylData p 0 XW • X x y xy ≈ syl s
        rel = begin
          sylData p 0 XW • X x y xy              ≈⟨ cleft refl′ (≡.trans (unitSyl< uY x<p) (≡.cong (λ t → X x p x<p • Mτ x t) (m≡p⇒neg m≡p))) ⟩
          (X x p x<p • M x) • X x y xy           ≈⟨ cleft X-M′ x<p ⟩
          (M p • X x p x<p) • X x y xy           ≈⟨ cright refl′ (X≡ ≡.refl y≡p) ⟩
          (M p • X x p x<p) • X x p x<p          ≈⟨ assoc ⟩
          M p • (X x p x<p • X x p x<p)          ≈⟨ cright gen-gen (X-gen x p x<p) ⟩
          M p • ε                                ≈⟨ right-unit ⟩
          M p                                    ≈⟨ refl′ (≡.sym (N≡p m≡p)) ⟩
          syl s                                  ∎
      at-y (no y≢p) =
        bridge gX s o (syl s) (sylData p 0 XW) (X x y xy) pN
               (moved gX y≤p x (W ! m) XW eX uY (inj₁ (<⇒≢ x<p))) (lowS (X x y xy) y<p) rel
        where
        y<p : y < p
        y<p = ≤∧≢⇒< y≤p y≢p
        m<p : m < p
        m<p = ≡.subst (_< p) (≡.sym m≡y) y<p
        Ny : syl s ≡ X y p y<p • Mτ y σ
        Ny = ≡.trans (N< m<p) (≡.cong₂ _•_ (X≡ m≡y ≡.refl) (≡.cong (λ q → Mτ q σ) m≡y))
        rel : X x y xy • syl s ≈ sylData p 0 XW • X x y xy
        rel = begin
          X x y xy • syl s                           ≈⟨ cright refl′ Ny ⟩
          X x y xy • (X y p y<p • Mτ y σ)            ≈⟨ sym assoc ⟩
          (X x y xy • X y p y<p) • Mτ y σ            ≈⟨ cleft sym (XX-down xy y<p x<p) ⟩
          (X x p x<p • X x y xy) • Mτ y σ            ≈⟨ assoc ⟩
          X x p x<p • (X x y xy • Mτ y σ)            ≈⟨ cright Mτ-X xy σ ⟩
          X x p x<p • (Mτ x σ • X x y xy)            ≈⟨ sym assoc ⟩
          (X x p x<p • Mτ x σ) • X x y xy            ≈⟨ cleft refl′ (≡.sym (unitSyl< uY x<p)) ⟩
          sylData p 0 XW • X x y xy                  ∎
    -- The unit elsewhere.
    by (no m≢x) (no m≢y) = at-p (FinP.<-cmp m p)
      where
      off : ∀ t → t ∈ₛ gX → t ≢ m
      off t X-a = λ e → m≢x (≡.sym e)
      off t X-b = λ e → m≢y (≡.sym e)
      at-p : Tri (m < p) (m ≡ p) (p < m) → Path (X x y xy) s o
      at-p (tri> _ _ p<m) = ⊥-elim (FinP.<-irrefl ≡.refl (ℕP.<-≤-trans p<m m≤p))
      at-p (tri≈ _ m≡p _) =
        same gX y≤p off (X x y xy) y<p
             (comm-N gX (m≢x , m≢y) (≡.subst (λ q → Apart q gX) m≡p (m≢x , m≢y)))
        where
        y<p : y < p
        y<p = ≤∧≢⇒< y≤p (λ y≡p → m≢y (≡.trans m≡p (≡.sym y≡p)))
      at-p (tri< m<p _ _) = at-y (y FinP.≟ p)
        where
        at-y : Dec (y ≡ p) → Path (X x y xy) s o
        at-y (no y≢p) = same gX y≤p off (X x y xy) y<p (comm-N gX (m≢x , m≢y) (p≢x , ≢-sym y≢p))
          where
          y<p : y < p
          y<p = ≤∧≢⇒< y≤p y≢p
          p≢x : p ≢ x
          p≢x e = <⇒≢ x<p (≡.sym e)
        at-y (yes y≡p) = by-mx (FinP.<-cmp m x)
          where
          -- Through the syllable: N X_[x,p] = V N.
          slide : (V : Word (Gen n)) → X m p m<p • X x p x<p ≈ V • X m p m<p → V • syl s ≈ syl s • X x y xy
          slide V h = begin
            V • syl s                                  ≈⟨ cright refl′ (N< m<p) ⟩
            V • (X m p m<p • Mτ m σ)                   ≈⟨ sym assoc ⟩
            (V • X m p m<p) • Mτ m σ                   ≈⟨ cleft sym h ⟩
            (X m p m<p • X x p x<p) • Mτ m σ           ≈⟨ assoc ⟩
            X m p m<p • (X x p x<p • Mτ m σ)           ≈⟨ cright sym (Mτ-comm m σ (X-gen x p x<p) (m≢x , <⇒≢ m<p)) ⟩
            X m p m<p • (Mτ m σ • X x p x<p)           ≈⟨ sym assoc ⟩
            (X m p m<p • Mτ m σ) • X x p x<p           ≈⟨ cong (refl′ (≡.sym (N< m<p))) (refl′ (X≡ ≡.refl (≡.sym y≡p))) ⟩
            syl s • X x y xy                           ∎
          by-mx : Tri (m < x) (m ≡ x) (x < m) → Path (X x y xy) s o
          by-mx (tri< m<x _ _) = same gX y≤p off (X m x m<x) x<p (slide (X m x m<x) (XX-lt m<x x<p m<p))
          by-mx (tri≈ _ m≡x _) = ⊥-elim (m≢x m≡x)
          by-mx (tri> _ _ x<m) = same gX y≤p off (X x m x<m) m<p (slide (X x m x<m) (XX-gt x<m m<p x<p))

  --------------------------------------------------------------------
  -- K_[a,b,c,d] on 0, 1, 2, 3 (Case 3.1)

  edge-K : (a b c d : Fin n) .(ab : a < b) .(bc : b < c) .(cd : c < d) →
           toℕ a ≡ 0 → toℕ b ≡ 1 → toℕ c ≡ 2 → toℕ d ≡ 3 → d ≤ p →
           level (actM (K-gen a b c d ab bc cd) s) ≤ₗ level s → Path (K a b c d ab bc cd) s o
  edge-K a b c d ab bc cd a0 b1 c2 d3 d≤p le = by (m FinP.≟ a) (m FinP.≟ b) (m FinP.≟ c) (m FinP.≟ d)
    where
    gK = K-gen a b c d ab bc cd
    D₄ = distinct₄ ab bc cd
    open Distinct₄ D₄ renaming (ab to a≢b ; ac to a≢c ; ad to a≢d ; bc to b≢c ; bd to b≢d ; cd to c≢d)
    KW = Kᶻ a b c d W
    -- K touching the unit raises the exponent: that edge goes up.
    up : oddℤ (KW ! a) ≡ true → ⊥
    up oa = no-le (≡.subst₂ _≤ₗ_ lv′ lv le)
      where
      gs = actM gK s
      eq : col gs p ≡ scV 1 KW
      eq = ≡.trans (colg gK) (actV-K a b c d ab bc cd 0 W)
      mn : Minimal 1 KW
      mn = inj₂ (a , oa)
      pv′ : pivot gs ≡ just p
      pv′ = pivot-char gs (ne-𝕀 gs p 0 KW eq mn) (Beyond-actM gK {M = s} d≤p be)
      lv′ : level gs ≡ (suc (toℕ p) , 1 , nodd KW)
      lv′ = level-of gs pv′ 1 KW eq mn
      lv : level s ≡ (suc (toℕ p) , 0 , nodd W)
      lv = ≡.trans lvl (≡.cong (λ k → suc (toℕ p) , k , nodd W) k0)
      no-le : (suc (toℕ p) , 1 , nodd KW) ≤ₗ (suc (toℕ p) , 0 , nodd W) → ⊥
      no-le (inj₁ (inj₁ lt)) = ℕP.<-irrefl ≡.refl lt
      no-le (inj₁ (inj₂ (_ , inj₁ ())))
      no-le (inj₁ (inj₂ (_ , inj₂ (() , _))))
      no-le (inj₂ ())
    P : Fin n → Bool
    P t = oddℤ (W ! t)
    on : ∀ t → m ≡ t → P t ≡ true
    on t m≡t = ≡.subst (λ q → P q ≡ true) m≡t (unit-odd (UV.unit uW))
    off′ : ∀ t → m ≢ t → P t ≡ false
    off′ t m≢t = ≡.cong oddℤ (UV.off uW t (λ e → m≢t (≡.sym e)))
    xor4 : ((P a xor P b) xor P c) xor P d ≡ true → ⊥
    xor4 h = up (≡.trans (≡.trans (≡.cong oddℤ (set₄-a D₄ _ _ _ _ _)) (odd-rowA (W ! a) (W ! b) (W ! c) (W ! d))) h)
    -- Two indices equal to m are equal.
    via≡ : ∀ {t u : Fin n} → m ≡ t → m ≡ u → t ≡ u
    via≡ e e′ = ≡.trans (≡.sym e) e′
    -- toℕ m ≤ 3 puts m among a, b, c, d.
    small : toℕ m ℕ.≤ 3 → m ≢ a → m ≢ b → m ≢ c → m ≢ d → ⊥
    small h ma mb mc md = at (toℕ m) ≡.refl h
      where
      at : ∀ k → toℕ m ≡ k → k ℕ.≤ 3 → ⊥
      at 0 e _ = ma (FinP.toℕ-injective (≡.trans e (≡.sym a0)))
      at 1 e _ = mb (FinP.toℕ-injective (≡.trans e (≡.sym b1)))
      at 2 e _ = mc (FinP.toℕ-injective (≡.trans e (≡.sym c2)))
      at 3 e _ = md (FinP.toℕ-injective (≡.trans e (≡.sym d3)))
      at (suc (suc (suc (suc k)))) _ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ())))
    by : Dec (m ≡ a) → Dec (m ≡ b) → Dec (m ≡ c) → Dec (m ≡ d) → Path (K a b c d ab bc cd) s o
    by (yes ma) _ _ _ = ⊥-elim (xor4 (≡.trans (≡.cong₂ (λ u v → ((u xor v) xor P c) xor P d) (on a ma)
      (off′ b (λ mb → a≢b (via≡ ma mb)))) (≡.cong₂ (λ u v → ((true xor false) xor u) xor v)
      (off′ c (λ mc → a≢c (via≡ ma mc))) (off′ d (λ md → a≢d (via≡ ma md))))))
    by (no ma) (yes mb) _ _ = ⊥-elim (xor4 (≡.trans (≡.cong₂ (λ u v → ((u xor v) xor P c) xor P d)
      (off′ a ma) (on b mb)) (≡.cong₂ (λ u v → ((false xor true) xor u) xor v)
      (off′ c (λ mc → b≢c (via≡ mb mc))) (off′ d (λ md → b≢d (via≡ mb md))))))
    by (no ma) (no mb) (yes mc) _ = ⊥-elim (xor4 (≡.trans (≡.cong₂ (λ u v → ((u xor v) xor P c) xor P d)
      (off′ a ma) (off′ b mb)) (≡.cong₂ (λ u v → ((false xor false) xor u) xor v)
      (on c mc) (off′ d (λ md → c≢d (via≡ mc md))))))
    by (no ma) (no mb) (no mc) (yes md) = ⊥-elim (xor4 (≡.trans (≡.cong₂ (λ u v → ((u xor v) xor P c) xor P d)
      (off′ a ma) (off′ b mb)) (≡.cong₂ (λ u v → ((false xor false) xor u) xor v)
      (off′ c mc) (on d md))))
    by (no ma) (no mb) (no mc) (no md) =
      same gK d≤p off (K a b c d ab bc cd) d<p (comm-N gK (ma , mb , mc , md) (pa , pb , pc , pd))
      where
      off : ∀ t → t ∈ₛ gK → t ≢ m
      off t K-a = λ e → ma (≡.sym e)
      off t K-b = λ e → mb (≡.sym e)
      off t K-c = λ e → mc (≡.sym e)
      off t K-d = λ e → md (≡.sym e)
      d<p : d < p
      d<p = ≤∧≢⇒< d≤p (λ d≡p → small (≡.subst (toℕ m ℕ.≤_) (≡.trans (≡.cong toℕ (≡.sym d≡p)) d3) m≤p) ma mb mc md)
      pa : p ≢ a
      pa e = <⇒≢ (FinP.<-trans (rc ab) (FinP.<-trans (rc bc) (ℕP.<-≤-trans (rc cd) d≤p))) (≡.sym e)
      pb : p ≢ b
      pb e = <⇒≢ (FinP.<-trans (rc bc) (ℕP.<-≤-trans (rc cd) d≤p)) (≡.sym e)
      pc : p ≢ c
      pc e = <⇒≢ (ℕP.<-≤-trans (rc cd) d≤p) (≡.sym e)
      pd : p ≢ d
      pd e = <⇒≢ d<p (≡.sym e)
