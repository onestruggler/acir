------------------------------------------------------------------------
-- Presentations of groups
--
-- Every step of figure 2 keeps the ladder's invariant (for Amy, QPL
-- 2018, proposition 3.2)
--
-- PathSum.Ladder.Invariant describes the path-sums reachable from the
-- ladder ξ n.  Here it is proved that the description is right: every
-- step of PathSum.Full's _⟶ᶠ_ -- all four rules of figure 2, with
-- any Boolean-valued quotients, at any variables -- takes a path-sum
-- satisfying Inv to one satisfying Inv (Inv-step), hence so does every
-- chain (Inv-steps).  A step of _⟶ᶠ_ is a head rule of
-- PathSum.Reduction.General after at most two renumberings, and
-- renumbering keeps Inv (Invariant.Inv-front), so the work is at the
-- head (Inv-head), where the first path variable has some role
-- (g , kind) and gadget g some state:
--
-- * [ω] and [Case] never apply.  Every value of the phase is a
--   multiple of ½ (half-valued), so its quotient by y₀ and its
--   quarters are too; [ω] asks the quotient to be ¼ + ½Q and [Case]
--   asks ¼X + ½Q and ¼(1 - X) + ½Q′ of two quarters, and ½ divides
--   neither ¼ nor both of ¼X and ¼(1 - X) for a bit X (no-ω, no-case).
-- * A live v_g is an output (the a wire's value is v_g), so neither
--   [Elim] nor [HH] applies at it (LiveV.no-novar).
-- * A half v_g is mentioned nowhere: the quotient by it is 0
--   (HalfV.head-zero), so [HH] does not apply there (½(y_i + Q) is
--   not 0 for both values of y_i when Q is free of y_i), and [Elim]
--   does: it makes the gadget dead (elim-half).
-- * At a live u_g the quotient is ½(v_g ⊕ c_g) (LiveU.head-val), not
--   0, so [Elim] does not apply.  [HH] does, and its substituted
--   variable is forced: at a point with x_g = 1 the quotient is
--   ½(v_g ⊕ a_g), which ignores every other variable, while ½(y_i + Q)
--   changes with y_i (LiveU.partner).  Its quotient Q then takes the
--   values of c_g (LiveU.quotient-bit), and the reduct, whose v_g is
--   substituted by Q and stays as a variable nothing mentions, is the
--   ladder with gadget g half (hh-live).
-- * The states u or v absent from a gadget's state cannot be the first
--   variable's role (Invariant.Layout.loc-present).
--
-- The values at the two settings of y₀ are compared with
-- PathSum.Ladder.Gadget.one-change, which gives both the phase bits
-- and the outputs.  The reducts' values are read through
-- Invariant.eval-false and PathSum.Polynomial.Boolean.
-- eval-substᴾ-bool; nothing about their coefficients is computed.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Ladder.Steps (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-identityʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; splitAt; _↑ʳ_)
open import Data.Fin.Properties using (splitAt-↑ʳ)
  renaming (_≟_ to _≟ᶠ_)
open import Data.Fin.Subset using (inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_)
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; divides; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n; ∣-trans; *-cancelˡ-∣; ∣⇒∣ᵤ;
   ∣m+n∣n⇒∣m; ∣m⇒∣m*n)
open import Data.Integer.Properties using
  (+-identityʳ; +-inverseʳ; *-identityʳ; *-zeroʳ; *-distribˡ-+)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just; _>>=_)
open import Data.Nat.Base using (zero; suc; _+_)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Vec.Base using (_∷_; here)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  M : ℕ
  M = ℕ.suc (ℕ.suc (ℕ.suc M₀))

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-there)
open import PathSum.Base using
  (PathSum; ⟨_,_⟩; phase; out; head-part; tail-part; y₀)
open import PathSum.Ladder M₀ using
  (_≡ᴹ_; mk≡ᴹ; ≡ᴹ⇒∣; ≡ᴹ-refl; ≡ᴹ-sym; ≡ᴹ-trans; ≡⇒≡ᴹ; ≡ᴹ-+; hb; hb-xor;
   xw; aw)
open import PathSum.Ladder.Gadget using
  (State; live; half; dead; Kind; U; V; Role; _≟ʳ_; present; Gad; gad;
   state; xb; ab; ub; vb; gval; step; term; prevAt; Vs; Bsum;
   step-live; step-half; step-dead; term-live; term-half; term-dead;
   one-change; prevAt-off; upd; upd-here; upd-there; wsum; wsum-split;
   wsum-upd; weight)
open import PathSum.Ladder.Invariant M₀ using
  (Layout; st; role; loc; loc-role; role-loc; loc-present; rd; gads; outF;
   outF-≗; Inv; lay; k-eq; phase-ok; out-ok; Inv-front; _◂_; eval-false;
   eval-head; pred; drop0; rd-drop; half-valued; ½∣2^M)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Polynomial using
  (Poly; y[_]; 0ᴾ; κ; μ; _+ᴾ_; _-ᴾ_; _·ᴾ_; _≈[_]_; NoVar; eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Boolean using
  (IsBit; BoolValued; IsBit-bool; IsBit-bool-if; eval-substᴾ-bool)
open import PathSum.Polynomial.Parity using (≡-odd)
open import PathSum.Polynomial.Product using (eval-μᴾ; eval-0ᴾ)
open import PathSum.Polynomial.Properties using
  (eval-∣; eval-≈; eval-+ᴾ; eval-−ᴾ; eval-·ᴾ; eval-κ; eval-off; i∣0)
open import PathSum.Polynomial.Substitution using
  (Absent; substᴾ; q₀₁; q₁₀; q₁₁)
open import PathSum.Reduction M using (elim-reduct; ¼; ½)
open import PathSum.Reduction.General M using
  (_⟶ᴳ_; elimᴳ; ωᴳ; hhᴳ; caseᴳ; ωᴳ-reduct; hhᴳ-reduct; case-reduct)
open import PathSum.Anywhere M using (plain; at)
open import PathSum.Full M using (_⟶ᶠ_; _⟶ᶠ*_; εᶠ; _◅ᶠ_)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- Arithmetic

private
  2∤1 : ¬ ((+ 2) ∣ 1ℤ)
  2∤1 h with ∣1⇒≡1 (∣⇒∣ᵤ h)
  ... | ()

  minus0 : ∀ a → a -ℤ 0ℤ ≡ a
  minus0 = solve 1 (λ a → a :- con 0ℤ := a) refl

-- 2^(e+1) does not divide 2^e.

pow-suc∤ : ∀ e → ¬ (pow (suc e) ∣ pow e)
pow-suc∤ e h = 2∤1 (*-cancelˡ-∣ (pow e) {{ℕ.m^n≢0 2 e}}
  (subst₂ _∣_ (pow-suc e) (sym (*-identityʳ (pow e))) h))

-- So ½ is not 0 modulo 1, and ½ does not divide ¼.

½≢0 : ¬ (½ ≡ᴹ 0ℤ)
½≢0 (mk≡ᴹ h) = pow-suc∤ (ℕ.suc (ℕ.suc M₀)) (subst (pow M ∣_) (minus0 ½) h)

½∤¼ : ¬ (½ ∣ ¼)
½∤¼ = pow-suc∤ (ℕ.suc M₀)

-- If ½ divides ¼z, z is even.

quarter : ∀ z → ½ ∣ (¼ *ℤ z) → (+ 2) ∣ z
quarter z h = *-cancelˡ-∣ ¼ {{ℕ.m^n≢0 2 (ℕ.suc M₀)}}
  (subst (_∣ (¼ *ℤ z)) (pow-suc (ℕ.suc M₀)) h)

-- Subtraction respects congruence modulo 2^M.

≡ᴹ-- : ∀ {a b c d} → a ≡ᴹ b → c ≡ᴹ d → (a -ℤ c) ≡ᴹ (b -ℤ d)
≡ᴹ-- {a} {b} {c} {d} (mk≡ᴹ p) (mk≡ᴹ q) =
  mk≡ᴹ (subst (pow M ∣_) (shape a b c d) (∣m∣n⇒∣m-n p q))
  where
  shape : ∀ a b c d → (a -ℤ b) -ℤ (c -ℤ d) ≡ (a -ℤ c) -ℤ (b -ℤ d)
  shape = solve 4 (λ a b c d →
    (a :- b) :- (c :- d) := (a :- c) :- (b :- d)) refl

-- Halves of bits are equal modulo 1 only for equal bits.

hb-inj : ∀ c d → hb c ≡ᴹ hb d → c ≡ d
hb-inj true  true  _ = refl
hb-inj false false _ = refl
hb-inj true  false h = ⊥-elim (½≢0 h)
hb-inj false true  h = ⊥-elim (½≢0 (≡ᴹ-sym h))

-- ½(a + b) is ½(a ⊕ b) modulo 1, for bits.

half-bits : ∀ a b → (½ *ℤ ([ a ]ᶻ +ℤ [ b ]ᶻ)) ≡ᴹ hb (a xor b)
half-bits a b = ≡ᴹ-trans
  (≡⇒≡ᴹ (trans (*-distribˡ-+ ½ [ a ]ᶻ [ b ]ᶻ)
               (cong₂ _+ℤ_ (½[] a) (½[] b))))
  (hb-xor a b)
  where
  ½[] : ∀ c → ½ *ℤ [ c ]ᶻ ≡ hb c
  ½[] true  = *-identityʳ ½
  ½[] false = *-zeroʳ ½

-- Adding Δ to a phase bit adds ½Δ to its half.

diff-xor : ∀ B Δ → (hb (B xor Δ) -ℤ hb B) ≡ᴹ hb Δ
diff-xor B Δ = ≡ᴹ-trans (≡ᴹ-- (≡ᴹ-sym (hb-xor B Δ)) (≡ᴹ-refl {hb B}))
  (≡⇒≡ᴹ (cancel (hb B) (hb Δ)))
  where
  cancel : ∀ a d → (a +ℤ d) -ℤ a ≡ d
  cancel = solve 2 (λ a d → (a :+ d) :- a := d) refl

xor-cancel : ∀ a c d → a xor c ≡ a xor d → c ≡ d
xor-cancel true  true  true  _ = refl
xor-cancel true  false false _ = refl
xor-cancel false true  true  _ = refl
xor-cancel false false false _ = refl
xor-cancel true  true  false ()
xor-cancel true  false true  ()
xor-cancel false true  false ()
xor-cancel false false true  ()

private
  true≢false : ¬ (true ≡ false)
  true≢false ()

  U≢V : ¬ (U ≡ V)
  U≢V ()


------------------------------------------------------------------------
-- Polynomial readings

-- The value of [HH]'s right-hand side.

eval-½q : (i : Fin m) (Q : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
          eval (½ ·ᴾ (μ y[ i ] +ᴾ Q)) x y ≡ ½ *ℤ ([ y i ]ᶻ +ℤ eval Q x y)
eval-½q i Q x y = trans (eval-·ᴾ ½ (μ y[ i ] +ᴾ Q) x y)
  (cong (½ *ℤ_) (trans (eval-+ᴾ (μ y[ i ]) Q x y)
                       (cong (_+ℤ eval Q x y) (eval-μᴾ y[ i ] x y))))

-- A polynomial without y₀ modulo 2 has the same parity at both
-- settings of y₀ ...

novar-odd : {P : Poly n (suc m)} → NoVar (+ 2) y₀ P →
            ∀ x y → odd (eval P x (true ◂ y)) ≡ odd (eval P x (false ◂ y))
novar-odd {P = P} nv x y = ≡-odd _ _
  (subst ((+ 2) ∣_) (eval-head P x y)
         (eval-∣ (head-part P) (λ { (α , β) → nv (α , inside ∷ β) here })
                 x y))

-- An assignment no wire's role reads at i.

rd-≔ : (y : Fin m → Bool) (i : Fin m) (c : Bool) (mc : Maybe (Fin m)) →
       mc ≢ just i → rd (y [ i ≔ c ]) mc ≡ rd y mc
rd-≔ y i c (just l) ne = ≔-there y c (λ l≡i → ne (cong just l≡i))
rd-≔ y i c nothing  ne = refl

-- Every role reads 0 at the all-0 point.

rd-false : (mc : Maybe (Fin (suc m))) → rd (false ◂ (λ _ → false)) mc ≡ false
rd-false (just zero)    = refl
rd-false (just (suc l)) = refl
rd-false nothing        = refl

private
  pred-just : (mc : Maybe (Fin (suc m))) (l : Fin m) →
              (mc >>= pred) ≡ just l → mc ≡ just (suc l)
  pred-just (just (suc l)) l refl = refl
  pred-just (just zero)    l ()
  pred-just nothing        l ()

-- Gadget data with the same state and equal readings.

gad-≡₃ : ∀ {s s′ x a u v u′ v′} → s ≡ s′ → u ≡ u′ → v ≡ v′ →
         gad s x a u v ≡ gad s′ x a u′ v′
gad-≡₃ refl refl refl = refl

-- The a wire's output is the gadget's value.

outF-aw : (L : Layout n m) (x : Fin (n + n) → Bool) (y : Fin m → Bool)
          (g : Fin n) → outF L x y (aw g) ≡ Vs true (gads L x y) g
outF-aw {n = n} L x y g =
  cong [ (λ h → x (xw {n} h)) , Vs true (gads L x y) ]′ (splitAt-↑ʳ n n g)


------------------------------------------------------------------------
-- The first path variable, by its role

module _ {n k m : ℕ} {ψ : PathSum (n + n) k (suc m)} (I : Inv n ψ) where

  private
    L : Layout n (suc m)
    L = lay I

  -- The first variable has role (g , b₀).

  module Zero (g : Fin n) (b₀ : Kind) (r0 : role L zero ≡ (g , b₀)) where

    loc0 : loc L g b₀ ≡ just zero
    loc0 = subst (λ r → loc L (proj₁ r) (proj₂ r) ≡ just zero) r0
                 (loc-role L zero)

    present0 : present (st L g) b₀ ≡ true
    present0 = trans (sym (loc-present L g b₀)) (cong is-just loc0)

    -- A state without that role is impossible.

    absent : ∀ {s} → st L g ≡ s → present s b₀ ≡ false → ⊥
    absent e p = true≢false
      (trans (sym present0) (trans (cong (λ s → present s b₀) e) p))

    -- Every other role is another variable's.

    other : ∀ h b → (h , b) ≢ (g , b₀) → loc L h b ≢ just zero
    other h b ne e = ne (trans (sym (role-loc L h b zero e)) r0)

    rd-here : ∀ c y → rd (c ◂ y) (loc L g b₀) ≡ c
    rd-here c y = cong (rd (c ◂ y)) loc0

    rd-other : ∀ h b → (h , b) ≢ (g , b₀) → ∀ c c′ y →
               rd (c ◂ y) (loc L h b) ≡ rd (c′ ◂ y) (loc L h b)
    rd-other h b ne c c′ y =
      trans (rd-drop y c (loc L h b) (other h b ne))
            (sym (rd-drop y c′ (loc L h b) (other h b ne)))

    -- Off gadget g, the readings at c ◂ y do not depend on c.

    off-g : ∀ x y c c′ h → h ≢ g →
            gads L x (c ◂ y) h ≡ gads L x (c′ ◂ y) h
    off-g x y c c′ h h≢g =
      gad-≡₃ refl (rd-other h U (λ e → h≢g (cong proj₁ e)) c c′ y)
                  (rd-other h V (λ e → h≢g (cong proj₁ e)) c c′ y)

  -- The outputs at both settings of the first variable: equal values
  -- give equal outputs.

  private
    outs : ∀ x y c c′ →
           (∀ g → Vs true (gads L x (c ◂ y)) g ≡ Vs true (gads L x (c′ ◂ y)) g) →
           ∀ w → odd (eval (out ψ w) x (c ◂ y)) ≡ odd (eval (out ψ w) x (c′ ◂ y))
    outs x y c c′ h w = trans (out-ok I w x (c ◂ y))
      (trans (outF-≗ L L x (c ◂ y) (c′ ◂ y) h w) (sym (out-ok I w x (c′ ◂ y))))

  -- A live u_g: the quotient by it is ½(v_g ⊕ c_g), and the outputs
  -- ignore it.

  module LiveU (g : Fin n) (r0 : role L zero ≡ (g , U))
               (live? : st L g ≡ live) where

    open Zero g U r0

    private
      G : (x : Fin (n + n) → Bool) (c : Bool) (y : Fin m → Bool) →
          Fin n → Gad
      G x c y = gads L x (c ◂ y)

      vb-same : ∀ x y c c′ → vb (G x c y g) ≡ vb (G x c′ y g)
      vb-same x y c c′ =
        rd-other g V (λ e → U≢V (sym (cong proj₂ e))) c c′ y

      change : ∀ x y →
        (Bsum true (G x true y) ≡
         Bsum true (G x false y) xor
           (term (G x true y g) (prevAt true (G x true y) g) xor
            term (G x false y g) (prevAt true (G x true y) g))) ×
        (∀ h → Vs true (G x true y) h ≡ Vs true (G x false y) h)
      change x y = one-change (G x true y) (G x false y) g true
        (λ h h≢g q → cong (λ γ → step γ q) (off-g x y true false h h≢g))
        (λ h h≢g q → cong (λ γ → term γ q) (off-g x y true false h h≢g))
        (trans (step-live (G x true y g) q live?)
          (trans (vb-same x y true false)
                 (sym (step-live (G x false y g) q live?))))
        where
        q : Bool
        q = prevAt true (G x true y) g

    -- The quotient's bit: v_g ⊕ c_g, read with y₀ = 0.

    qv : (x : Fin (n + n) → Bool) (y : Fin m → Bool) → Bool
    qv x y = vb (G x false y g) xor
             gval (G x false y g) (prevAt true (G x false y) g)

    private
      Δ-eq : ∀ x y →
             (term (G x true y g) (prevAt true (G x true y) g) xor
              term (G x false y g) (prevAt true (G x true y) g)) ≡ qv x y
      Δ-eq x y = trans
        (cong₂ _xor_
          (trans (term-live (G x true y g) q live?)
                 (cong (λ u → u ∧ (vb (G x true y g) xor
                                   gval (G x true y g) q))
                       (rd-here true y)))
          (trans (term-live (G x false y g) q live?)
                 (cong (λ u → u ∧ (vb (G x false y g) xor
                                   gval (G x false y g) q))
                       (rd-here false y))))
        (trans (xor-identityʳ _)
          (cong₂ _xor_ (vb-same x y true false)
            (cong (gval (G x false y g))
              (prevAt-off (G x true y) (G x false y) g true
                (λ h h≢g q′ → cong (λ γ → step γ q′)
                                   (off-g x y true false h h≢g))))))
        where
        q : Bool
        q = prevAt true (G x true y) g

    head-val : ∀ x y → eval (head-part (phase ψ)) x y ≡ᴹ hb (qv x y)
    head-val x y = ≡ᴹ-trans (≡⇒≡ᴹ (eval-head (phase ψ) x y))
      (≡ᴹ-trans (≡ᴹ-- (phase-ok I x (true ◂ y)) (phase-ok I x (false ◂ y)))
        (≡ᴹ-trans
          (≡⇒≡ᴹ (cong (λ B → hb B -ℤ hb (Bsum true (G x false y)))
                      (proj₁ (change x y))))
          (≡ᴹ-trans (diff-xor (Bsum true (G x false y)) _)
                    (≡⇒≡ᴹ (cong hb (Δ-eq x y))))))

    out-same : ∀ w x y → odd (eval (out ψ w) x (true ◂ y)) ≡
                         odd (eval (out ψ w) x (false ◂ y))
    out-same w x y = outs x y true false (proj₂ (change x y)) w

  -- A half v_g: nothing mentions it.

  module HalfV (g : Fin n) (r0 : role L zero ≡ (g , V))
               (half? : st L g ≡ half) where

    open Zero g V r0

    private
      G : (x : Fin (n + n) → Bool) (c : Bool) (y : Fin m → Bool) →
          Fin n → Gad
      G x c y = gads L x (c ◂ y)

      ub-same : ∀ x y c c′ → ub (G x c y g) ≡ ub (G x c′ y g)
      ub-same x y c c′ = rd-other g U (λ e → U≢V (cong proj₂ e)) c c′ y

      change : ∀ x y →
        (Bsum true (G x true y) ≡
         Bsum true (G x false y) xor
           (term (G x true y g) (prevAt true (G x true y) g) xor
            term (G x false y g) (prevAt true (G x true y) g))) ×
        (∀ h → Vs true (G x true y) h ≡ Vs true (G x false y) h)
      change x y = one-change (G x true y) (G x false y) g true
        (λ h h≢g q → cong (λ γ → step γ q) (off-g x y true false h h≢g))
        (λ h h≢g q → cong (λ γ → term γ q) (off-g x y true false h h≢g))
        (trans (step-half (G x true y g) q half?)
               (sym (step-half (G x false y g) q half?)))
        where
        q : Bool
        q = prevAt true (G x true y) g

      bsum-same : ∀ x y → Bsum true (G x true y) ≡ Bsum true (G x false y)
      bsum-same x y = trans (proj₁ (change x y))
        (trans (cong (Bsum true (G x false y) xor_)
                 (cong₂ _xor_ (term-half (G x true y g) q half?)
                              (term-half (G x false y g) q half?)))
               (xor-identityʳ _))
        where
        q : Bool
        q = prevAt true (G x true y) g

    head-zero : ∀ x y → eval (head-part (phase ψ)) x y ≡ᴹ 0ℤ
    head-zero x y = ≡ᴹ-trans (≡⇒≡ᴹ (eval-head (phase ψ) x y))
      (≡ᴹ-trans (≡ᴹ-- (phase-ok I x (true ◂ y)) (phase-ok I x (false ◂ y)))
        (≡ᴹ-trans
          (≡⇒≡ᴹ (cong (λ B → hb B -ℤ hb (Bsum true (G x false y)))
                      (bsum-same x y)))
          (≡⇒≡ᴹ (+-inverseʳ (hb (Bsum true (G x false y)))))))

    out-same : ∀ w x y → odd (eval (out ψ w) x (true ◂ y)) ≡
                         odd (eval (out ψ w) x (false ◂ y))
    out-same w x y = outs x y true false (proj₂ (change x y)) w

  -- A live v_g is an output: no rule can treat it as internal.

  module LiveV (g : Fin n) (r0 : role L zero ≡ (g , V))
               (live? : st L g ≡ live) where

    open Zero g V r0

    no-novar : NoVar (+ 2) y₀ (out ψ (aw g)) → ⊥
    no-novar nv = true≢false (trans (sym (at-c true)) (trans eq (at-c false)))
      where
      x : Fin (n + n) → Bool
      x _ = false

      y : Fin m → Bool
      y _ = false

      eq : odd (eval (out ψ (aw g)) x (true ◂ y)) ≡
           odd (eval (out ψ (aw g)) x (false ◂ y))
      eq = novar-odd nv x y

      at-c : ∀ c → odd (eval (out ψ (aw g)) x (c ◂ y)) ≡ c
      at-c c = trans (out-ok I (aw g) x (c ◂ y))
        (trans (outF-aw L x (c ◂ y) g)
          (trans (step-live (gads L x (c ◂ y) g) _ live?) (rd-here c y)))


------------------------------------------------------------------------
-- [ω] and [Case] never apply

module _ {n k m : ℕ} {ψ : PathSum (n + n) k (suc m)} (I : Inv n ψ) where

  -- The quotient by y₀ takes values in ½ℤ.

  private
    ½∣head : ∀ x y → ½ ∣ eval (head-part (phase ψ)) x y
    ½∣head x y = subst (½ ∣_) (sym (eval-head (phase ψ) x y))
      (∣m∣n⇒∣m-n (half-valued I x (true ◂ y)) (half-valued I x (false ◂ y)))

  no-ω : (Q : Poly (n + n) m) →
         head-part (phase ψ) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ Q)) → ⊥
  no-ω Q eqP = ½∤¼ (∣m+n∣n⇒∣m ½∣¼+½q (∣m⇒∣m*n (eval Q x y) ½∣½))
    where
    x : Fin (n + n) → Bool
    x _ = false

    y : Fin m → Bool
    y _ = false

    ½∣½ : ½ ∣ ½
    ½∣½ = divides (+ 1) (sym (*-identityˡ′ ½))
      where
      *-identityˡ′ : ∀ z → (+ 1) *ℤ z ≡ z
      *-identityˡ′ = solve 1 (λ z → con (+ 1) :* z := z) refl

    rhs : eval (κ ¼ +ᴾ (½ ·ᴾ Q)) x y ≡ ¼ +ℤ ½ *ℤ eval Q x y
    rhs = trans (eval-+ᴾ (κ ¼) (½ ·ᴾ Q) x y)
                (cong₂ _+ℤ_ (eval-κ ¼ x y) (eval-·ᴾ ½ Q x y))

    ½∣¼+½q : ½ ∣ (¼ +ℤ ½ *ℤ eval Q x y)
    ½∣¼+½q = subst (½ ∣_)
      (trans (shape (eval (head-part (phase ψ)) x y)
                    (eval (κ ¼ +ᴾ (½ ·ᴾ Q)) x y)) rhs)
      (∣m∣n⇒∣m-n (½∣head x y)
        (∣-trans ½∣2^M (eval-≈ (head-part (phase ψ)) (κ ¼ +ᴾ (½ ·ᴾ Q))
                                eqP x y)))
      where
      shape : ∀ h r → h -ℤ (h -ℤ r) ≡ r
      shape = solve 2 (λ h r → h :- (h :- r) := r) refl

module _ {n k m : ℕ} {ψ : PathSum (n + n) k (suc (suc m))}
         (I : Inv n ψ) where

  no-case : (X Q Q′ : Poly (n + n) m) → BoolValued X →
            q₁₀ (phase ψ) ≈[ pow M ] ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q)) →
            q₀₁ (phase ψ) ≈[ pow M ]
              ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′)) → ⊥
  no-case X Q Q′ bX e₁₀ e₀₁ = bits (bX x y) X-even X-odd
    where
    x : Fin (n + n) → Bool
    x _ = false

    y : Fin m → Bool
    y _ = false

    P : Poly (n + n) (suc (suc m))
    P = phase ψ

    ½∣½z : ∀ z → ½ ∣ (½ *ℤ z)
    ½∣½z z = divides z refl′
      where
      refl′ : ½ *ℤ z ≡ z *ℤ ½
      refl′ = solve 2 (λ h z → h :* z := z :* h) refl ½ z

    -- The two quarters' values are differences of values of the phase.
    ½∣q₁₀ : ½ ∣ eval (q₁₀ P) x y
    ½∣q₁₀ = subst (½ ∣_)
      (trans (sym (eval-head P x (false ◂ y)))
             (eval-false (head-part P) x y))
      (∣m∣n⇒∣m-n (half-valued I x (true ◂ false ◂ y))
                 (half-valued I x (false ◂ false ◂ y)))

    ½∣q₀₁ : ½ ∣ eval (q₀₁ P) x y
    ½∣q₀₁ = subst (½ ∣_)
      (trans (cong₂ _-ℤ_ (eval-false P x (true ◂ y))
                         (eval-false P x (false ◂ y)))
             (sym (eval-head (tail-part P) x y)))
      (∣m∣n⇒∣m-n (half-valued I x (false ◂ true ◂ y))
                 (half-valued I x (false ◂ false ◂ y)))

    -- ½ divides ¼ z when it divides ¼ z + ½ w and differs from it by a
    -- multiple of 2^M.
    from : ∀ {A} z w → A ≈[ pow M ] ((¼ ·ᴾ z) +ᴾ (½ ·ᴾ w)) →
           ½ ∣ eval A x y → ½ ∣ (¼ *ℤ eval z x y)
    from {A} z w eqA ½∣A = ∣m+n∣n⇒∣m (subst (½ ∣_) value
        (∣m∣n⇒∣m-n ½∣A (∣-trans ½∣2^M
           (eval-≈ A ((¼ ·ᴾ z) +ᴾ (½ ·ᴾ w)) eqA x y))))
      (½∣½z (eval w x y))
      where
      value : eval A x y -ℤ (eval A x y -ℤ eval ((¼ ·ᴾ z) +ᴾ (½ ·ᴾ w)) x y)
              ≡ ¼ *ℤ eval z x y +ℤ ½ *ℤ eval w x y
      value = trans (shape (eval A x y) _)
        (trans (eval-+ᴾ (¼ ·ᴾ z) (½ ·ᴾ w) x y)
               (cong₂ _+ℤ_ (eval-·ᴾ ¼ z x y) (eval-·ᴾ ½ w x y)))
        where
        shape : ∀ h r → h -ℤ (h -ℤ r) ≡ r
        shape = solve 2 (λ h r → h :- (h :- r) := r) refl

    X-even : (+ 2) ∣ eval X x y
    X-even = quarter (eval X x y) (from X Q e₁₀ ½∣q₁₀)

    X-odd : (+ 2) ∣ (1ℤ -ℤ eval X x y)
    X-odd = quarter (1ℤ -ℤ eval X x y)
      (subst (λ t → ½ ∣ (¼ *ℤ t))
             (trans (eval-−ᴾ (κ 1ℤ) X x y)
                    (cong (_-ℤ eval X x y) (eval-κ 1ℤ x y)))
             (from (κ 1ℤ -ᴾ X) Q′ e₀₁ ½∣q₀₁))

    bits : ∀ {z} → IsBit z → (+ 2) ∣ z → (+ 2) ∣ (1ℤ -ℤ z) → ⊥
    bits (inj₁ refl) _ h = 2∤1 h
    bits (inj₂ refl) h _ = 2∤1 h


------------------------------------------------------------------------
-- Reading the reduct

-- A reduct whose values are those of ψ at a point built from the
-- reduct's, and whose gadgets there are those of a new layout: the
-- invariant carries over.

transfer : {ψ : PathSum (n + n) k m} {ζ : PathSum (n + n) k′ m′}
           (I : Inv n ψ) (L′ : Layout n m′) → k′ ≡ wsum (st L′) →
           (pt : (Fin (n + n) → Bool) → (Fin m′ → Bool) → Fin m → Bool) →
           (∀ x y → eval (phase ζ) x y ≡ eval (phase ψ) x (pt x y)) →
           (∀ w x y → eval (out ζ w) x y ≡ eval (out ψ w) x (pt x y)) →
           (∀ x y → Bsum true (gads (lay I) x (pt x y)) ≡
                    Bsum true (gads L′ x y)) →
           (∀ x y g → Vs true (gads (lay I) x (pt x y)) g ≡
                      Vs true (gads L′ x y) g) →
           Inv n ζ
transfer {ψ = ψ} {ζ} I L′ keq pt ph ou bs vs = record
  { lay      = L′
  ; k-eq     = keq
  ; phase-ok = λ x y → ≡ᴹ-trans (≡⇒≡ᴹ (ph x y))
      (≡ᴹ-trans (phase-ok I x (pt x y)) (≡⇒≡ᴹ (cong hb (bs x y))))
  ; out-ok   = λ w x y → trans (cong odd (ou w x y))
      (trans (out-ok I w x (pt x y))
             (outF-≗ (lay I) L′ x (pt x y) y (vs x y) w))
  }


------------------------------------------------------------------------
-- [Elim] at a half v_g: the gadget dies

module _ {n k m : ℕ} {ψ : PathSum (n + n) (suc (suc k)) (suc m)}
         (I : Inv n ψ) (g : Fin n) (r0 : role (lay I) zero ≡ (g , V))
         (half? : st (lay I) g ≡ half) where

  private
    L : Layout n (suc m)
    L = lay I

    open Zero I g V r0

    st′ : Fin n → State
    st′ = upd (st L) g dead

    keep : ∀ h b → loc L h b ≢ just zero → present (st′ h) b ≡ present (st L h) b
    keep h b ne = by (h ≟ᶠ g)
      where
      byk : ∀ b → loc L g b ≢ just zero →
            present (st′ g) b ≡ present (st L g) b
      byk U _   = trans (cong (λ s → present s U) (upd-here (st L) g dead))
                        (sym (cong (λ s → present s U) half?))
      byk V ne′ = contradiction loc0 ne′

      by : Dec (h ≡ g) → present (st′ h) b ≡ present (st L h) b
      by (no h≢g)  = cong (λ s → present s b) (upd-there (st L) dead h≢g)
      by (yes h≡g) = subst (λ h′ → loc L h′ b ≢ just zero →
                                   present (st′ h′) b ≡ present (st L h′) b)
                           (sym h≡g) (byk b) ne

    gone : present (st′ (proj₁ (role L zero))) (proj₂ (role L zero)) ≡ false
    gone = subst (λ r → present (st′ (proj₁ r)) (proj₂ r) ≡ false) (sym r0)
                 (cong (λ s → present s V) (upd-here (st L) g dead))

    L′ : Layout n m
    L′ = drop0 L st′ keep gone

    keq : k ≡ wsum st′
    keq = ℕ.suc-injective (ℕ.suc-injective
      (trans (k-eq I) (trans (wsum-split (st L) g)
                             (cong (λ s → weight s + wsum st′) half?))))

    G G′ : (x : Fin (n + n) → Bool) (y : Fin m → Bool) → Fin n → Gad
    G x y = gads L x (false ◂ y)
    G′ x y = gads L′ x y

    same-off : ∀ x y h → h ≢ g → G x y h ≡ G′ x y h
    same-off x y h h≢g = gad-≡₃ (sym (upd-there (st L) dead h≢g))
      (rd-drop y false (loc L h U) (other h U (λ e → h≢g (cong proj₁ e))))
      (rd-drop y false (loc L h V) (other h V (λ e → h≢g (cong proj₁ e))))

    dead′ : st′ g ≡ dead
    dead′ = upd-here (st L) g dead

    change : ∀ x y →
      (Bsum true (G x y) ≡
       Bsum true (G′ x y) xor
         (term (G x y g) (prevAt true (G x y) g) xor
          term (G′ x y g) (prevAt true (G x y) g))) ×
      (∀ h → Vs true (G x y) h ≡ Vs true (G′ x y) h)
    change x y = one-change (G x y) (G′ x y) g true
      (λ h h≢g q → cong (λ γ → step γ q) (same-off x y h h≢g))
      (λ h h≢g q → cong (λ γ → term γ q) (same-off x y h h≢g))
      (trans (step-half (G x y g) q half?)
             (sym (step-dead (G′ x y g) q dead′)))
      where
      q : Bool
      q = prevAt true (G x y) g

  elim-half : Inv n (elim-reduct ψ)
  elim-half = transfer I L′ keq (λ x y → false ◂ y)
    (λ x y → sym (eval-false (phase ψ) x y))
    (λ w x y → sym (eval-false (out ψ w) x y))
    (λ x y → trans (proj₁ (change x y))
      (trans (cong (Bsum true (G′ x y) xor_)
               (cong₂ _xor_ (term-half (G x y g) (q x y) half?)
                            (term-dead (G′ x y g) (q x y) dead′)))
             (xor-identityʳ _)))
    (λ x y → proj₂ (change x y))
    where
    q : (x : Fin (n + n) → Bool) (y : Fin m → Bool) → Bool
    q x y = prevAt true (G x y) g



------------------------------------------------------------------------
-- [HH]'s premise, read as bits

private
  []-inj : ∀ a b → [ a ]ᶻ ≡ [ b ]ᶻ → a ≡ b
  []-inj true  true  _ = refl
  []-inj false false _ = refl
  []-inj true  false ()
  []-inj false true  ()

  b≢notb : ∀ b → ¬ (b ≡ not b)
  b≢notb true  ()
  b≢notb false ()

-- The bit a Boolean-valued Q takes.

qbit : {N m : ℕ} (Q : Poly N m) → BoolValued Q →
       (Fin N → Bool) → (Fin m → Bool) → Bool
qbit Q bQ x y = IsBit-bool (bQ x y)

qbit-cong : {N m : ℕ} (Q : Poly N m) (bQ : BoolValued Q) →
            ∀ x y y′ → eval Q x y ≡ eval Q x y′ →
            qbit Q bQ x y ≡ qbit Q bQ x y′
qbit-cong Q bQ x y y′ e = []-inj (qbit Q bQ x y) (qbit Q bQ x y′)
  (trans (IsBit-bool-if (bQ x y)) (trans e (sym (IsBit-bool-if (bQ x y′)))))

-- [HH]'s premise: the quotient by y₀ is ½(y_i ⊕ Q), modulo 1.

hh-premise : {N k m : ℕ} {ψ : PathSum N k (suc m)}
             (i : Fin m) (Q : Poly N m) (bQ : BoolValued Q) →
             head-part (phase ψ) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q)) →
             ∀ x y → eval (head-part (phase ψ)) x y ≡ᴹ
                     hb (y i xor qbit Q bQ x y)
hh-premise {ψ = ψ} i Q bQ eqP x y = ≡ᴹ-trans
  (mk≡ᴹ (eval-≈ (head-part (phase ψ)) (½ ·ᴾ (μ y[ i ] +ᴾ Q)) eqP x y))
  (≡ᴹ-trans (≡⇒≡ᴹ (trans (eval-½q i Q x y)
                         (cong (λ t → ½ *ℤ ([ y i ]ᶻ +ℤ t))
                               (sym (IsBit-bool-if (bQ x y))))))
            (half-bits (y i) (qbit Q bQ x y)))


------------------------------------------------------------------------
-- [HH] at a half v_g is impossible

module _ {n k m : ℕ} {ψ : PathSum (n + n) k (suc m)}
         (I : Inv n ψ) (g : Fin n) (r0 : role (lay I) zero ≡ (g , V))
         (half? : st (lay I) g ≡ half)
         (i : Fin m) (Q : Poly (n + n) m) (bQ : BoolValued Q)
         (absQ : Absent y[ i ] Q)
         (eqP : head-part (phase ψ) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q)))
         where

  private
    qb : (x : Fin (n + n) → Bool) (y : Fin m → Bool) → Bool
    qb = qbit Q bQ

  no-hh-half : ⊥
  no-hh-half = true≢false (trans (sym q₁≡true) (trans (sym same) q₀≡false))
    where
    x : Fin (n + n) → Bool
    x _ = false

    y₀′ y₁′ : Fin m → Bool
    y₀′ _ = false
    y₁′ = y₀′ [ i ≔ true ]

    -- At both points the quotient is 0 and ½(y_i ⊕ Q).
    zero-at : ∀ y → false ≡ y i xor qb x y
    zero-at y = hb-inj false _
      (≡ᴹ-trans (≡ᴹ-sym (HalfV.head-zero I g r0 half? x y))
                (hh-premise {ψ = ψ} i Q bQ eqP x y))

    q₀≡false : qb x y₀′ ≡ false
    q₀≡false = sym (zero-at y₀′)

    q₁≡true : qb x y₁′ ≡ true
    q₁≡true = sym (xor-cancel true true (qb x y₁′)
      (trans (zero-at y₁′) (cong (_xor qb x y₁′) (≔-here y₀′ i true))))

    same : qb x y₀′ ≡ qb x y₁′
    same = qbit-cong Q bQ x y₀′ y₁′
      (eval-off Q i absQ x y₀′ y₁′ (λ j j≢i → sym (≔-there y₀′ true j≢i)))


------------------------------------------------------------------------
-- [Elim] at a live u_g is impossible

no-elim-live-u : {ψ : PathSum (n + n) (suc (suc k)) (suc m)} (I : Inv n ψ)
                 (g : Fin n) → role (lay I) zero ≡ (g , U) →
                 st (lay I) g ≡ live →
                 head-part (phase ψ) ≈[ pow M ] 0ᴾ → ⊥
no-elim-live-u {n = n} {m = m} {ψ = ψ} I g r0 live? eqP =
  ½≢0 (≡ᴹ-trans (≡ᴹ-sym (≡ᴹ-trans (LiveU.head-val I g r0 live? x y)
                                  (≡⇒≡ᴹ (cong hb qv-true))))
                (≡ᴹ-trans (mk≡ᴹ (eval-≈ (head-part (phase ψ)) 0ᴾ eqP x y))
                          (≡⇒≡ᴹ (eval-0ᴾ x y))))
  where
  x : Fin (n + n) → Bool
  x _ = true

  y : Fin m → Bool
  y _ = false

  qv-true : LiveU.qv I g r0 live? x y ≡ true
  qv-true = cong (_xor true) (rd-false (loc (lay I) g V))


------------------------------------------------------------------------
-- [HH] at a live u_g: the gadget becomes half

module _ {n k m : ℕ} {ψ : PathSum (n + n) k (suc m)}
         (I : Inv n ψ) (g : Fin n) (r0 : role (lay I) zero ≡ (g , U))
         (live? : st (lay I) g ≡ live)
         (i : Fin m) (Q : Poly (n + n) m) (bQ : BoolValued Q)
         (absQ : Absent y[ i ] Q)
         (eqP : head-part (phase ψ) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q)))
         where

  private
    L : Layout n (suc m)
    L = lay I

    qb : (x : Fin (n + n) → Bool) (y : Fin m → Bool) → Bool
    qb = qbit Q bQ

    -- The quotient's two readings agree, bit for bit.
    key : ∀ x y → LiveU.qv I g r0 live? x y ≡ y i xor qb x y
    key x y = hb-inj _ _ (≡ᴹ-trans (≡ᴹ-sym (LiveU.head-val I g r0 live? x y))
                                   (hh-premise {ψ = ψ} i Q bQ eqP x y))

    gV≢gU : (g , V) ≢ (g , U)
    gV≢gU e = U≢V (sym (cong proj₂ e))

  open Zero I g U r0

  -- The substituted variable is v_g: at a point with x_g = 1 the
  -- quotient is v_g ⊕ a_g, which any other y_i leaves alone, while
  -- y_i ⊕ Q changes with it.

  partner : role L (suc i) ≡ (g , V)
  partner = by (role L (suc i) ≟ʳ (g , V))
    where
    by : Dec (role L (suc i) ≡ (g , V)) → role L (suc i) ≡ (g , V)
    by (yes e) = e
    by (no ne) = ⊥-elim (b≢notb q₁ (trans (sym q₀≡q₁) q₀≡notq₁))
      where
      x : Fin (n + n) → Bool
      x _ = true

      y₀′ y₁′ : Fin m → Bool
      y₀′ _ = false
      y₁′ = y₀′ [ i ≔ true ]

      not-i : (loc L g V >>= pred) ≢ just i
      not-i e = ne (role-loc L g V (suc i) (pred-just (loc L g V) i e))

      qv-same : LiveU.qv I g r0 live? x y₀′ ≡ LiveU.qv I g r0 live? x y₁′
      qv-same = cong (_xor true)
        (trans (rd-drop y₀′ false (loc L g V) (other g V gV≢gU))
          (trans (sym (rd-≔ y₀′ i true (loc L g V >>= pred) not-i))
                 (sym (rd-drop y₁′ false (loc L g V) (other g V gV≢gU)))))

      q₀ q₁ : Bool
      q₀ = qb x y₀′
      q₁ = qb x y₁′

      q₀≡q₁ : q₀ ≡ q₁
      q₀≡q₁ = qbit-cong Q bQ x y₀′ y₁′
        (eval-off Q i absQ x y₀′ y₁′ (λ j j≢i → sym (≔-there y₀′ true j≢i)))

      -- q₀ is the quotient at y₀′ (where y_i = 0), which is the quotient
      -- at y₁′, which is ¬q₁ (y_i = 1 there).
      q₀≡notq₁ : q₀ ≡ not q₁
      q₀≡notq₁ = trans (sym (key x y₀′))
        (trans qv-same (trans (key x y₁′)
                              (cong (_xor q₁) (≔-here y₀′ i true))))

  loc-gV : loc L g V ≡ just (suc i)
  loc-gV = subst (λ r → loc L (proj₁ r) (proj₂ r) ≡ just (suc i)) partner
                 (loc-role L (suc i))

  private
    -- Q takes the values of c_g.
    G₀ : (x : Fin (n + n) → Bool) (y : Fin m → Bool) → Fin n → Gad
    G₀ x y = gads L x (false ◂ y)

    qb-gval : ∀ x y → qb x y ≡ gval (G₀ x y g) (prevAt true (G₀ x y) g)
    qb-gval x y = sym (xor-cancel (y i) _ _
      (trans (cong (_xor gval (G₀ x y g) (prevAt true (G₀ x y) g))
                   (sym (cong (rd (false ◂ y)) loc-gV)))
             (key x y)))

    -- The new layout: gadget g half.
    st′ : Fin n → State
    st′ = upd (st L) g half

    keep : ∀ h b → loc L h b ≢ just zero →
           present (st′ h) b ≡ present (st L h) b
    keep h b ne = by (h ≟ᶠ g)
      where
      byk : ∀ b → loc L g b ≢ just zero →
            present (st′ g) b ≡ present (st L g) b
      byk U ne′ = contradiction loc0 ne′
      byk V _   = trans (cong (λ s → present s V) (upd-here (st L) g half))
                        (sym (cong (λ s → present s V) live?))

      by : Dec (h ≡ g) → present (st′ h) b ≡ present (st L h) b
      by (no h≢g)  = cong (λ s → present s b) (upd-there (st L) half h≢g)
      by (yes h≡g) = subst (λ h′ → loc L h′ b ≢ just zero →
                                   present (st′ h′) b ≡ present (st L h′) b)
                           (sym h≡g) (byk b) ne

    gone : present (st′ (proj₁ (role L zero))) (proj₂ (role L zero)) ≡ false
    gone = subst (λ r → present (st′ (proj₁ r)) (proj₂ r) ≡ false) (sym r0)
                 (cong (λ s → present s U) (upd-here (st L) g half))

    L′ : Layout n m
    L′ = drop0 L st′ keep gone

    keq : k ≡ wsum st′
    keq = trans (k-eq I)
      (trans (wsum-split (st L) g)
        (trans (cong (λ s → weight s + wsum (upd (st L) g dead)) live?)
               (sym (wsum-upd (st L) g half))))

    -- The point of ψ a point of the reduct stands for.
    pt : (x : Fin (n + n) → Bool) (y : Fin m → Bool) → Fin (suc m) → Bool
    pt x y = false ◂ (y [ i ≔ qb x y ])

    G G′ : (x : Fin (n + n) → Bool) (y : Fin m → Bool) → Fin n → Gad
    G x y = gads L x (pt x y)
    G′ x y = gads L′ x y

    -- Off v_g, the substitution changes no reading.
    not-i : ∀ h b → h ≢ g → (loc L h b >>= pred) ≢ just i
    not-i h b h≢g e = h≢g (cong proj₁
      (trans (sym (role-loc L h b (suc i) (pred-just (loc L h b) i e)))
             partner))

    rd-off : ∀ x y h b → h ≢ g → (h , b) ≢ (g , U) →
             rd (pt x y) (loc L h b) ≡ rd y (loc L h b >>= pred)
    rd-off x y h b h≢g ne =
      trans (rd-drop (y [ i ≔ qb x y ]) false (loc L h b) (other h b ne))
            (rd-≔ y i (qb x y) (loc L h b >>= pred) (not-i h b h≢g))

    same-off : ∀ x y h → h ≢ g → G x y h ≡ G′ x y h
    same-off x y h h≢g = gad-≡₃ (sym (upd-there (st L) half h≢g))
      (rd-off x y h U h≢g (λ e → h≢g (cong proj₁ e)))
      (rd-off x y h V h≢g (λ e → h≢g (cong proj₁ e)))

    -- And the value reaching g is the same as before the substitution.
    same-G₀ : ∀ x y h → h ≢ g → G₀ x y h ≡ G x y h
    same-G₀ x y h h≢g = gad-≡₃ refl
      (trans (rd-drop y false (loc L h U)
                      (other h U (λ e → h≢g (cong proj₁ e))))
             (sym (rd-off x y h U h≢g (λ e → h≢g (cong proj₁ e)))))
      (trans (rd-drop y false (loc L h V)
                      (other h V (λ e → h≢g (cong proj₁ e))))
             (sym (rd-off x y h V h≢g (λ e → h≢g (cong proj₁ e)))))

    half′ : st′ g ≡ half
    half′ = upd-here (st L) g half

    -- Gadget g hands on Q = c_g before and c_g after.
    hg : ∀ x y → step (G x y g) (prevAt true (G x y) g) ≡
                 step (G′ x y g) (prevAt true (G x y) g)
    hg x y = trans (step-live (G x y g) q live?)
      (trans (cong (rd (pt x y)) loc-gV)
        (trans (≔-here y i (qb x y))
          (trans (qb-gval x y)
            (trans (cong (gval (G₀ x y g))
                         (prevAt-off (G₀ x y) (G x y) g true
                           (λ h h≢g q′ → cong (λ γ → step γ q′)
                                              (same-G₀ x y h h≢g))))
                   (sym (step-half (G′ x y g) q half′))))))
      where
      q : Bool
      q = prevAt true (G x y) g

    change : ∀ x y →
      (Bsum true (G x y) ≡
       Bsum true (G′ x y) xor
         (term (G x y g) (prevAt true (G x y) g) xor
          term (G′ x y g) (prevAt true (G x y) g))) ×
      (∀ h → Vs true (G x y) h ≡ Vs true (G′ x y) h)
    change x y = one-change (G x y) (G′ x y) g true
      (λ h h≢g q → cong (λ γ → step γ q) (same-off x y h h≢g))
      (λ h h≢g q → cong (λ γ → term γ q) (same-off x y h h≢g))
      (hg x y)

    ub-false : ∀ x y → ub (G x y g) ≡ false
    ub-false x y = rd-here false (y [ i ≔ qb x y ])

  hh-live : Inv n (hhᴳ-reduct ψ i Q)
  hh-live = transfer I L′ keq pt
    (λ x y → trans (eval-substᴾ-bool (tail-part (phase ψ)) i Q bQ x y)
                   (sym (eval-false (phase ψ) x (y [ i ≔ qb x y ]))))
    (λ w x y → trans (eval-substᴾ-bool (tail-part (out ψ w)) i Q bQ x y)
                     (sym (eval-false (out ψ w) x (y [ i ≔ qb x y ]))))
    (λ x y → trans (proj₁ (change x y))
      (trans (cong (Bsum true (G′ x y) xor_)
               (cong₂ _xor_
                 (trans (term-live (G x y g) (q x y) live?)
                        (cong (λ u → u ∧ (vb (G x y g) xor
                                          gval (G x y g) (q x y)))
                              (ub-false x y)))
                 (term-half (G′ x y g) (q x y) half′)))
             (xor-identityʳ _)))
    (λ x y → proj₂ (change x y))
    where
    q : (x : Fin (n + n) → Bool) (y : Fin m → Bool) → Bool
    q x y = prevAt true (G x y) g


------------------------------------------------------------------------
-- Every step of figure 2 keeps the invariant

-- At the head, by the role of the first path variable and the state
-- of its gadget.

Inv-head : {ψ : PathSum (n + n) k m} {ζ : PathSum (n + n) k′ m′} →
           Inv n ψ → ψ ⟶ᴳ ζ → Inv n ζ
Inv-head {n = n} I (elimᴳ ψ eqP eqf) = go (role (lay I) zero) refl
  where
  go : (r : Role n) → role (lay I) zero ≡ r → Inv n (elim-reduct ψ)
  go (g , b₀) r0 = by b₀ (st (lay I) g) r0 refl
    where
    by : (b : Kind) (s : State) → role (lay I) zero ≡ (g , b) →
         st (lay I) g ≡ s → Inv n (elim-reduct ψ)
    by U live r e = ⊥-elim (no-elim-live-u I g r e eqP)
    by U half r e = ⊥-elim (Zero.absent I g U r e refl)
    by U dead r e = ⊥-elim (Zero.absent I g U r e refl)
    by V live r e = ⊥-elim (LiveV.no-novar I g r e (eqf (aw g)))
    by V half r e = elim-half I g r e
    by V dead r e = ⊥-elim (Zero.absent I g V r e refl)
Inv-head I (ωᴳ ψ Q bQ eqP eqf) = ⊥-elim (no-ω I Q eqP)
Inv-head {n = n} I (hhᴳ ψ i Q bQ absQ eqP eqf) = go (role (lay I) zero) refl
  where
  go : (r : Role n) → role (lay I) zero ≡ r → Inv n (hhᴳ-reduct ψ i Q)
  go (g , b₀) r0 = by b₀ (st (lay I) g) r0 refl
    where
    by : (b : Kind) (s : State) → role (lay I) zero ≡ (g , b) →
         st (lay I) g ≡ s → Inv n (hhᴳ-reduct ψ i Q)
    by U live r e = hh-live I g r e i Q bQ absQ eqP
    by U half r e = ⊥-elim (Zero.absent I g U r e refl)
    by U dead r e = ⊥-elim (Zero.absent I g U r e refl)
    by V live r e = ⊥-elim (LiveV.no-novar I g r e (eqf (aw g)))
    by V half r e = ⊥-elim (no-hh-half I g r e i Q bQ absQ eqP)
    by V dead r e = ⊥-elim (Zero.absent I g V r e refl)
Inv-head I (caseᴳ ψ X Q Q′ bX bQ bQ′ e₁₁ e₁₀ e₀₁ f₀ f₁) =
  ⊥-elim (no-case I X Q Q′ bX e₁₀ e₀₁)

-- At any variables: renumber, then the head.

Inv-step : {ψ : PathSum (n + n) k m} {ζ : PathSum (n + n) k′ m′} →
           Inv n ψ → ψ ⟶ᶠ ζ → Inv n ζ
Inv-step I (plain (plain s)) = Inv-head I s
Inv-step I (plain (at j s))  = Inv-head (Inv-front j I) s
Inv-step I (at j (plain s))  = Inv-head (Inv-front j I) s
Inv-step I (at j (at j′ s))  = Inv-head (Inv-front j′ (Inv-front j I)) s

-- Along any chain.

Inv-steps : {ψ : PathSum (n + n) k m} {ζ : PathSum (n + n) k′ m′} →
            Inv n ψ → ψ ⟶ᶠ* ζ → Inv n ζ
Inv-steps I εᶠ        = I
Inv-steps I (s ◅ᶠ ss) = Inv-steps (Inv-step I s) ss
