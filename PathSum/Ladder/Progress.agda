------------------------------------------------------------------------
-- Presentations of groups
--
-- A path-sum reachable from the ladder that has a path variable left
-- is reducible (for Amy, QPL 2018, proposition 3.2)
--
-- PathSum.Ladder.Steps shows that every path-sum reachable from the
-- ladder ξ n satisfies PathSum.Ladder.Invariant's Inv.  Here: every
-- such path-sum with a path variable left has a step of figure 2
-- (progress), so every normal form reachable from ξ n has no path
-- variables (reducible, used by PathSum.Ladder.Size).
--
-- Take any path variable; its gadget g is live or half (a dead gadget
-- has none).
--
-- * Half: the variable is v_g, which nothing mentions.  [Elim] applies
--   at it: the quotient is 0 and no output mentions it (HalfV), and
--   the normalisation has the 2 it needs, half gadgets weighing 2
--   (elim-step).
-- * Live: [HH] applies at u_g, with v_g as the substituted variable and
--   as quotient the lifting of c_g = a_g ⊕ (¬x_g ∧ V_(g-1)), written as
--   a Boolean expression (PathSum.Polynomial.Boolean.BExp) over the
--   inputs and the v's of the live gadgets before g (gE): its lifting
--   is Boolean-valued and free of v_g by construction (Absent-liftᵉ),
--   the quotient by u_g is ½(v_g ⊕ c_g) (Steps.LiveU.head-val), and no
--   output mentions u_g (hh-step).  The rule is applied at the
--   variable u_g, after renumbering it to the front.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Ladder.Progress (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _xor_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Fin.Subset using (inside)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_)
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just; _>>=_)
open import Data.Nat.Base using (zero; suc; _+_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (_∷_; here)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Nat.Base as ℕ

private
  M : ℕ
  M = ℕ.suc (ℕ.suc (ℕ.suc M₀))

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using
  (PathSum; phase; out; head-part; tail-part; y₀)
open import PathSum.Ladder M₀ using
  (_≡ᴹ_; mk≡ᴹ; ≡ᴹ⇒∣; ≡ᴹ-trans; ≡ᴹ-sym; ≡⇒≡ᴹ; hb; xw; aw)
open import PathSum.Ladder.Gadget using
  (State; live; half; dead; Kind; U; V; present; Gad; gad; gval; step;
   prevAt; prevAt-cong; wsum; wsum-split; upd; weight)
open import PathSum.Ladder.Invariant M₀ using
  (Layout; st; role; loc; loc-role; role-loc; loc-present; rd; gads; Inv;
   lay; k-eq; Inv-front; _◂_; eval-head; pred; rd-drop)
open import PathSum.Ladder.Steps M₀ using
  (module LiveU; module HalfV; module Zero; eval-½q; half-bits)
open import PathSum.Mobius using (values⇒coefficientsᵐ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Poly; Var; x[_]; y[_]; 0ᴾ; μ; _+ᴾ_; _·ᴾ_; _≈[_]_; NoVar; eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Boolean using
  (BExp; var; lit; _⊕ᵉ_; _∧ᵉ_; ⟦_⟧ᵉ; liftᵉ; eval-liftᵉ; BoolValued-liftᵉ;
   _∉ᵉ_; Absent-liftᵉ; ≈-from-values)
open import PathSum.Polynomial.Parity using (odd-≡)
open import PathSum.Polynomial.Product using (eval-0ᴾ)
open import PathSum.Reduction M using (elim-reduct; ½)
open import PathSum.Reduction.General M using
  (_⟶ᴳ_; elimᴳ; hhᴳ; hhᴳ-reduct)
open import PathSum.Reorder using (front)
open import PathSum.Anywhere M using (plain; at)
open import PathSum.Full M using (_⟶ᶠ_)

private
  variable
    n k m N : ℕ


------------------------------------------------------------------------
-- Outputs that ignore y₀ do not mention it modulo 2

novar-from-odd : (P : Poly N (suc m)) →
                 (∀ x y → odd (eval P x (true ◂ y)) ≡ odd (eval P x (false ◂ y))) →
                 NoVar (+ 2) y₀ P
novar-from-odd P h (α , .inside ∷ β) here =
  values⇒coefficientsᵐ (+ 2) (head-part P)
    (λ x y → subst ((+ 2) ∣_) (sym (eval-head P x y))
                   (odd-≡ _ _ (h x y)))
    (α , β)


------------------------------------------------------------------------
-- The quotient c_g as a Boolean expression

-- One gadget's hand-on value, and the value reaching gadget g, built as
-- expressions from expressions for x_h, a_h and v_h.

stepE : State → BExp N m → BExp N m → BExp N m → BExp N m → BExp N m
stepE live x a v p = v
stepE half x a v p = a ⊕ᵉ ((lit true ⊕ᵉ x) ∧ᵉ p)
stepE dead x a v p = a ⊕ᵉ ((lit true ⊕ᵉ x) ∧ᵉ p)

prevE : BExp N m → (Fin n → State) → (xe ae ve : Fin n → BExp N m) →
        Fin n → BExp N m
prevE p s xe ae ve zero    = p
prevE p s xe ae ve (suc g) =
  prevE (stepE (s zero) (xe zero) (ae zero) (ve zero) p)
        (λ h → s (suc h)) (λ h → xe (suc h)) (λ h → ae (suc h))
        (λ h → ve (suc h)) g

gE : (Fin n → State) → (xe ae ve : Fin n → BExp N m) → Fin n → BExp N m
gE s xe ae ve g =
  ae g ⊕ᵉ ((lit true ⊕ᵉ xe g) ∧ᵉ prevE (lit true) s xe ae ve g)

-- Their values.

module _ {N m : ℕ} (X : Fin N → Bool) (Y : Fin m → Bool) where

  -- The gadgets the expressions stand for (u_g is irrelevant).
  Gᵉ : (Fin n → State) → (xe ae ve : Fin n → BExp N m) → Fin n → Gad
  Gᵉ s xe ae ve h =
    gad (s h) (⟦ xe h ⟧ᵉ X Y) (⟦ ae h ⟧ᵉ X Y) false (⟦ ve h ⟧ᵉ X Y)

  stepE-val : (s : State) (x a v p : BExp N m) (u : Bool) →
              ⟦ stepE s x a v p ⟧ᵉ X Y ≡
              step (gad s (⟦ x ⟧ᵉ X Y) (⟦ a ⟧ᵉ X Y) u (⟦ v ⟧ᵉ X Y))
                   (⟦ p ⟧ᵉ X Y)
  stepE-val live x a v p u = refl
  stepE-val half x a v p u = refl
  stepE-val dead x a v p u = refl

  prevE-val : (p : BExp N m) (s : Fin n → State) (xe ae ve : Fin n → BExp N m)
              (g : Fin n) →
              ⟦ prevE p s xe ae ve g ⟧ᵉ X Y ≡
              prevAt (⟦ p ⟧ᵉ X Y) (Gᵉ s xe ae ve) g
  prevE-val p s xe ae ve zero    = refl
  prevE-val p s xe ae ve (suc g) = trans
    (prevE-val (stepE (s zero) (xe zero) (ae zero) (ve zero) p)
               (λ h → s (suc h)) (λ h → xe (suc h)) (λ h → ae (suc h))
               (λ h → ve (suc h)) g)
    (cong (λ q → prevAt q (λ h → Gᵉ s xe ae ve (suc h)) g)
          (stepE-val (s zero) (xe zero) (ae zero) (ve zero) p false))

  gE-val : (s : Fin n → State) (xe ae ve : Fin n → BExp N m) (g : Fin n) →
           ⟦ gE s xe ae ve g ⟧ᵉ X Y ≡
           gval (Gᵉ s xe ae ve g) (prevAt true (Gᵉ s xe ae ve) g)
  gE-val s xe ae ve g =
    cong (λ q → ⟦ ae g ⟧ᵉ X Y xor (not (⟦ xe g ⟧ᵉ X Y) ∧ q))
         (prevE-val (lit true) s xe ae ve g)

-- A variable missing from the expressions of every gadget but g is
-- missing from c_g.

module _ {N m : ℕ} (v : Var N m) where

  stepE-∉ : (s : State) {x a w p : BExp N m} → v ∉ᵉ x → v ∉ᵉ a → v ∉ᵉ w →
            v ∉ᵉ p → v ∉ᵉ stepE s x a w p
  stepE-∉ live hx ha hw hp = hw
  stepE-∉ half hx ha hw hp = ha , ((tt , hx) , hp)
  stepE-∉ dead hx ha hw hp = ha , ((tt , hx) , hp)

  prevE-∉ : {p : BExp N m} (s : Fin n → State) (xe ae ve : Fin n → BExp N m)
            (g : Fin n) →
            (∀ h → h ≢ g → (v ∉ᵉ xe h) × (v ∉ᵉ ae h) × (v ∉ᵉ ve h)) →
            v ∉ᵉ p → v ∉ᵉ prevE p s xe ae ve g
  prevE-∉ s xe ae ve zero    hs hp = hp
  prevE-∉ s xe ae ve (suc g) hs hp =
    prevE-∉ (λ h → s (suc h)) (λ h → xe (suc h)) (λ h → ae (suc h))
            (λ h → ve (suc h)) g
            (λ h h≢g → hs (suc h) (λ e → h≢g (suc-inj e)))
            (stepE-∉ (s zero) (proj₁ h₀) (proj₁ (proj₂ h₀)) (proj₂ (proj₂ h₀))
                     hp)
    where
    h₀ = hs zero (λ ())

    suc-inj : ∀ {a b : Fin _} → suc a ≡ suc b → a ≡ b
    suc-inj refl = refl

  gE-∉ : (s : Fin n → State) (xe ae ve : Fin n → BExp N m) (g : Fin n) →
         (∀ h → h ≢ g → (v ∉ᵉ xe h) × (v ∉ᵉ ae h) × (v ∉ᵉ ve h)) →
         v ∉ᵉ xe g → v ∉ᵉ ae g → v ∉ᵉ gE s xe ae ve g
  gE-∉ s xe ae ve g hs hx ha = ha , ((tt , hx) , prevE-∉ s xe ae ve g hs tt)


------------------------------------------------------------------------
-- [Elim] at a half v_g

private
  elim-from : {k k″ : ℕ} {φ : PathSum (n + n) k (suc m)} → k ≡ suc (suc k″) →
              head-part (phase φ) ≈[ pow M ] 0ᴾ →
              (∀ w → NoVar (+ 2) y₀ (out φ w)) →
              Σ ℕ λ k′ → Σ (PathSum (n + n) k′ m) λ ζ → φ ⟶ᴳ ζ
  elim-from {k″ = k″} {φ = φ} refl eqP eqf = k″ , elim-reduct φ , elimᴳ φ eqP eqf

elim-step : {φ : PathSum (n + n) k (suc m)} (I : Inv n φ) (g : Fin n) →
            role (lay I) zero ≡ (g , V) → st (lay I) g ≡ half →
            Σ ℕ λ k′ → Σ (PathSum (n + n) k′ m) λ ζ → φ ⟶ᴳ ζ
elim-step {n = n} {φ = φ} I g r0 half? = elim-from {n = n} {φ = φ}
  (trans (k-eq I) (trans (wsum-split (st (lay I)) g)
    (cong (λ s → weight s + wsum′) half?)))
  (≈-from-values (head-part (phase φ)) 0ᴾ λ x y →
    ≡ᴹ⇒∣ (≡ᴹ-trans (HalfV.head-zero I g r0 half? x y)
                   (≡⇒≡ᴹ (sym (eval-0ᴾ x y)))))
  (λ w → novar-from-odd (out φ w) (HalfV.out-same I g r0 half? w))
  where
  wsum′ : ℕ
  wsum′ = wsum (upd (st (lay I)) g dead)


------------------------------------------------------------------------
-- [HH] at a live u_g

module _ {n k m : ℕ} {φ : PathSum (n + n) k (suc m)} (I : Inv n φ)
         (g : Fin n) (r0 : role (lay I) zero ≡ (g , U))
         (live? : st (lay I) g ≡ live) where

  private
    L : Layout n (suc m)
    L = lay I

    -- v_g is a path variable, not the first.
    vg : Σ (Fin m) λ i → loc L g V ≡ just (suc i)
    vg = by (loc L g V) refl
      where
      by : (mc : Maybe (Fin (suc m))) → loc L g V ≡ mc →
           Σ (Fin m) λ i → loc L g V ≡ just (suc i)
      by (just (suc i)) e = i , e
      by (just zero)    e = ⊥-elim (U≢V (cong proj₂
        (trans (sym r0) (role-loc L g V zero e))))
        where
        U≢V : ¬ (U ≡ V)
        U≢V ()
      by nothing        e = ⊥-elim (false≢true
        (trans (sym (cong is-just e))
               (trans (loc-present L g V) (cong (λ s → present s V) live?))))
        where
        false≢true : ¬ (false ≡ true)
        false≢true ()

    i : Fin m
    i = proj₁ vg

    loc-gV : loc L g V ≡ just (suc i)
    loc-gV = proj₂ vg

    -- The expressions: inputs as variables, v_h as the variable that
    -- holds it (if any).
    vref : Maybe (Fin m) → BExp (n + n) m
    vref (just l) = var y[ l ]
    vref nothing  = lit false

    xe ae ve : Fin n → BExp (n + n) m
    xe h = var x[ xw h ]
    ae h = var x[ aw h ]
    ve h = vref (loc L h V >>= pred)

    E : BExp (n + n) m
    E = gE (st L) xe ae ve g

    -- No v_h of another gadget is v_g's variable.
    other-i : ∀ h → h ≢ g → y[ i ] ∉ᵉ ve h
    other-i h h≢g = by (loc L h V >>= pred) refl
      where
      by : (mc : Maybe (Fin m)) → (loc L h V >>= pred) ≡ mc → y[ i ] ∉ᵉ vref mc
      by (just l) e y≡ = h≢g (cong proj₁ (trans
        (sym (role-loc L h V (suc l) (pred-just (loc L h V) l e)))
        (role-loc L g V (suc l)
          (trans loc-gV (cong (λ l′ → just (suc l′)) (y-inj y≡))))))
        where
        y-inj : ∀ {a b : Fin m} → _≡_ {A = Var (n + n) m} y[ a ] y[ b ] → a ≡ b
        y-inj refl = refl

        pred-just : (mc : Maybe (Fin (suc m))) (l : Fin m) →
                    (mc >>= pred) ≡ just l → mc ≡ just (suc l)
        pred-just (just (suc l)) l refl = refl
        pred-just (just zero)    l ()
        pred-just nothing        l ()
      by nothing  e = tt

    E-absent : y[ i ] ∉ᵉ E
    E-absent = gE-∉ y[ i ] (st L) xe ae ve g
      (λ h h≢g → (λ ()) , (λ ()) , other-i h h≢g) (λ ()) (λ ())

    -- The expression's value is c_g at the point read with y₀ = 0.
    rd-ve : ∀ X Y h → ⟦ ve h ⟧ᵉ X Y ≡ rd (false ◂ Y) (loc L h V)
    rd-ve X Y h = sym (trans (rd-drop Y false (loc L h V) not-zero)
                             (by (loc L h V >>= pred)))
      where
      not-zero : loc L h V ≢ just zero
      not-zero e = U≢V′ (cong proj₂ (trans (sym r0) (role-loc L h V zero e)))
        where
        U≢V′ : ¬ (U ≡ V)
        U≢V′ ()

      by : (mc : Maybe (Fin m)) → rd Y mc ≡ ⟦ vref mc ⟧ᵉ X Y
      by (just l) = refl
      by nothing  = refl

    E-val : ∀ X Y → ⟦ E ⟧ᵉ X Y ≡
            gval (gads L X (false ◂ Y) g)
                 (prevAt true (gads L X (false ◂ Y)) g)
    E-val X Y = trans (gE-val X Y (st L) xe ae ve g)
      (cong (gval (gads L X (false ◂ Y) g))
        (prevAt-cong (Gᵉ X Y (st L) xe ae ve) (gads L X (false ◂ Y))
          (λ h q → cong (λ v → step (gad (st L h) (X (xw h)) (X (aw h))
                                          false v) q)
                        (rd-ve X Y h))
          true g))

    -- [HH]'s premises.
    Q : Poly (n + n) m
    Q = liftᵉ E

    eqP : head-part (phase φ) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q))
    eqP = ≈-from-values (head-part (phase φ)) (½ ·ᴾ (μ y[ i ] +ᴾ Q))
      λ X Y → ≡ᴹ⇒∣ (≡ᴹ-trans (LiveU.head-val I g r0 live? X Y)
        (≡ᴹ-trans (≡⇒≡ᴹ (cong hb (cong₂ _xor_
                     (cong (rd (false ◂ Y)) loc-gV) (sym (E-val X Y)))))
          (≡ᴹ-sym (≡ᴹ-trans
            (≡⇒≡ᴹ (trans (eval-½q i Q X Y)
                         (cong (λ t → ½ *ℤ ([ Y i ]ᶻ +ℤ t))
                               (eval-liftᵉ E X Y))))
            (half-bits (Y i) (⟦ E ⟧ᵉ X Y))))))

  hh-step : Σ (Fin m) λ i → Σ (Poly (n + n) m) λ Q → φ ⟶ᴳ hhᴳ-reduct φ i Q
  hh-step = i , Q , hhᴳ φ i Q (BoolValued-liftᵉ E)
    (Absent-liftᵉ y[ i ] E E-absent) eqP
    (λ w → novar-from-odd (out φ w) (LiveU.out-same I g r0 live? w))


------------------------------------------------------------------------
-- Progress

-- A path-sum satisfying the invariant with a path variable left has a
-- step of figure 2.

progress : {ψ : PathSum (n + n) k (suc m)} → Inv n ψ →
           Σ ℕ λ k′ → Σ ℕ λ m′ → Σ (PathSum (n + n) k′ m′) λ ζ → ψ ⟶ᶠ ζ
progress {n = n} {k = k} {m = m} {ψ = ψ} I = by (role L zero) refl
  where
  L : Layout n (suc m)
  L = lay I

  by : ∀ r → role L zero ≡ r →
       Σ ℕ λ k′ → Σ ℕ λ m′ → Σ (PathSum (n + n) k′ m′) λ ζ → ψ ⟶ᶠ ζ
  by (g , b₀) r0 = bys (st L g) refl
    where
    open Zero I g b₀ r0

    -- Live: u_g is a path variable c; renumber it to the front.
    live-case : st L g ≡ live →
                Σ ℕ λ k′ → Σ ℕ λ m′ → Σ (PathSum (n + n) k′ m′) λ ζ → ψ ⟶ᶠ ζ
    live-case live? = byc (loc L g U) refl
      where
      byc : (mc : Maybe (Fin (suc m))) → loc L g U ≡ mc →
            Σ ℕ λ k′ → Σ ℕ λ m′ → Σ (PathSum (n + n) k′ m′) λ ζ → ψ ⟶ᶠ ζ
      byc (just c) e = k , m , _ , at c (plain (proj₂ (proj₂ hstep)))
        where
        I′ : Inv n (front c ψ)
        I′ = Inv-front c I

        r0′ : role (lay I′) zero ≡ (g , U)
        r0′ = role-loc L g U c e

        hstep = hh-step I′ g r0′ live?
      byc nothing e = ⊥-elim (absent′ live? (trans (sym (cong is-just e))
                               (loc-present L g U)))
        where
        absent′ : st L g ≡ live → false ≡ present (st L g) U → ⊥
        absent′ live? p = false≢true (trans p (cong (λ s → present s U) live?))
          where
          false≢true : ¬ (false ≡ true)
          false≢true ()

    bys : (s : State) → st L g ≡ s →
          Σ ℕ λ k′ → Σ ℕ λ m′ → Σ (PathSum (n + n) k′ m′) λ ζ → ψ ⟶ᶠ ζ
    bys live e = live-case e
    bys half e = byk b₀ r0
      where
      byk : (b : Kind) → role L zero ≡ (g , b) →
            Σ ℕ λ k′ → Σ ℕ λ m′ → Σ (PathSum (n + n) k′ m′) λ ζ → ψ ⟶ᶠ ζ
      byk U r = ⊥-elim (Zero.absent I g U r e refl)
      byk V r = proj₁ es , m , proj₁ (proj₂ es) , plain (plain (proj₂ (proj₂ es)))
        where
        es = elim-step I g r e
    bys dead e = ⊥-elim (absent e (absent-dead b₀))
      where
      absent-dead : ∀ b → present dead b ≡ false
      absent-dead U = refl
      absent-dead V = refl
