------------------------------------------------------------------------
-- Presentations of groups
--
-- Every auxiliary atom is decoded.
--
-- `classify` sends every atom of GeneralN/DecodingPlans on 4 + k + c
-- wires to AtomDecoder's `Decoded`.  An atom that acts as the identity
-- — M_a M_a, or X_[a,b] X_[a,b] — decodes to ε.  Otherwise its points
-- are listed so that its exchanges and K increase along them (AtomAt),
-- and routed by Route4: the first point to 0 and the others to the
-- unit vectors of the top four wires, in order, except that a fourth
-- point coplanar with the first three goes to the sum of the first two
-- unit vectors.  The canonical states are then 0, 1, 2, and 4 or 3, as
-- indices of the four-wire window.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; _^_)

module Examples.Groups.CCX+HH.NaturalP.AtomCases (k c : ℕ) where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (z≤n ; s≤s)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; _++_ ; lookup ; map ; tabulate)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong₂ ; subst)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Notations using (₄₊)

open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (actVʷ ; actV-invol ; <⇒≢)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (M-gen ; X-gen)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (idx ; bits ; idx-cong ; idx-bits)
open import Examples.Groups.CCX+HH.GeneralN.DecodingPlans using (Atom ; MM ; XX ; J ; e)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute using (A⟦_⟧ ; _⊕_ ; unit)
open import Examples.Groups.CCX+HH.NaturalP.Span using (≈s? ; InSpan ; E4 ; e4 ; Fill)
open import Examples.Groups.CCX+HH.NaturalP.SpanEmb
  using (NZ ; indep₁ ; indep₂ ; indep₃ ; diff-nz ; elem-span ; span-⊕ ; span-++ˡ ; lookup-++-all ; e4-span)
open import Examples.Groups.CCX+HH.NaturalP.RouteTo using (span-trans)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.AtCalc using (Op ; AtI ; Inj)
open import Examples.Groups.CCX+HH.NaturalP.AtomAt
open import Examples.Groups.CCX+HH.NaturalP.Route4 using (bot ; stack ; module Route)
open import Examples.Groups.CCX+HH.NaturalP.AtomDecoder k c

------------------------------------------------------------------------
-- Canonical states and their indices

c2 : Fin 2 → State 4
c2 zero       = zeros
c2 (suc zero) = unit zero

c3 : Fin 3 → State 4
c3 zero             = zeros
c3 (suc zero)       = unit zero
c3 (suc (suc zero)) = unit (suc zero)

-- Four points in general position, and coplanar.
c4 c4′ : Fin 4 → State 4
c4 zero                   = zeros
c4 (suc zero)             = unit zero
c4 (suc (suc zero))       = unit (suc zero)
c4 (suc (suc (suc zero))) = unit (suc (suc zero))
c4′ zero                   = zeros
c4′ (suc zero)             = unit zero
c4′ (suc (suc zero))       = unit (suc zero)
c4′ (suc (suc (suc zero))) = unit zero ⊕ unit (suc zero)

private
  inj-c2 : Inj (λ y → idx 4 (c2 y))
  inj-c2 {zero}     {zero}     e = refl
  inj-c2 {zero}     {suc zero} ()
  inj-c2 {suc zero} {zero}     ()
  inj-c2 {suc zero} {suc zero} e = refl

  inj-c3 : Inj (λ y → idx 4 (c3 y))
  inj-c3 {zero}           {zero}           e = refl
  inj-c3 {zero}           {suc zero}       ()
  inj-c3 {zero}           {suc (suc zero)} ()
  inj-c3 {suc zero}       {zero}           ()
  inj-c3 {suc zero}       {suc zero}       e = refl
  inj-c3 {suc zero}       {suc (suc zero)} ()
  inj-c3 {suc (suc zero)} {zero}           ()
  inj-c3 {suc (suc zero)} {suc zero}       ()
  inj-c3 {suc (suc zero)} {suc (suc zero)} e = refl

  inj-c4 : Inj (λ y → idx 4 (c4 y))
  inj-c4 {zero}                 {zero}                 e = refl
  inj-c4 {zero}                 {suc zero}             ()
  inj-c4 {zero}                 {suc (suc zero)}       ()
  inj-c4 {zero}                 {suc (suc (suc zero))} ()
  inj-c4 {suc zero}             {zero}                 ()
  inj-c4 {suc zero}             {suc zero}             e = refl
  inj-c4 {suc zero}             {suc (suc zero)}       ()
  inj-c4 {suc zero}             {suc (suc (suc zero))} ()
  inj-c4 {suc (suc zero)}       {zero}                 ()
  inj-c4 {suc (suc zero)}       {suc zero}             ()
  inj-c4 {suc (suc zero)}       {suc (suc zero)}       e = refl
  inj-c4 {suc (suc zero)}       {suc (suc (suc zero))} ()
  inj-c4 {suc (suc (suc zero))} {zero}                 ()
  inj-c4 {suc (suc (suc zero))} {suc zero}             ()
  inj-c4 {suc (suc (suc zero))} {suc (suc zero)}       ()
  inj-c4 {suc (suc (suc zero))} {suc (suc (suc zero))} e = refl

  inj-c4′ : Inj (λ y → idx 4 (c4′ y))
  inj-c4′ {zero}                 {zero}                 e = refl
  inj-c4′ {zero}                 {suc zero}             ()
  inj-c4′ {zero}                 {suc (suc zero)}       ()
  inj-c4′ {zero}                 {suc (suc (suc zero))} ()
  inj-c4′ {suc zero}             {zero}                 ()
  inj-c4′ {suc zero}             {suc zero}             e = refl
  inj-c4′ {suc zero}             {suc (suc zero)}       ()
  inj-c4′ {suc zero}             {suc (suc (suc zero))} ()
  inj-c4′ {suc (suc zero)}       {zero}                 ()
  inj-c4′ {suc (suc zero)}       {suc zero}             ()
  inj-c4′ {suc (suc zero)}       {suc (suc zero)}       e = refl
  inj-c4′ {suc (suc zero)}       {suc (suc (suc zero))} ()
  inj-c4′ {suc (suc (suc zero))} {zero}                 ()
  inj-c4′ {suc (suc (suc zero))} {suc zero}             ()
  inj-c4′ {suc (suc (suc zero))} {suc (suc zero)}       ()
  inj-c4′ {suc (suc (suc zero))} {suc (suc (suc zero))} e = refl

------------------------------------------------------------------------
-- Unit vectors of the bottom four wires

private
  ub0 : unit {W} zero ≈s bot (unit zero) zeros
  ub0 zero                      = refl
  ub0 (suc zero)                = refl
  ub0 (suc (suc zero))          = refl
  ub0 (suc (suc (suc zero)))    = refl
  ub0 (suc (suc (suc (suc j)))) = refl

  ub1 : unit {W} (suc zero) ≈s bot (unit (suc zero)) zeros
  ub1 zero                      = refl
  ub1 (suc zero)                = refl
  ub1 (suc (suc zero))          = refl
  ub1 (suc (suc (suc zero)))    = refl
  ub1 (suc (suc (suc (suc j)))) = refl

  ub2 : unit {W} (suc (suc zero)) ≈s bot (unit (suc (suc zero))) zeros
  ub2 zero                      = refl
  ub2 (suc zero)                = refl
  ub2 (suc (suc zero))          = refl
  ub2 (suc (suc (suc zero)))    = refl
  ub2 (suc (suc (suc (suc j)))) = refl

  ub01 : unit {W} zero ⊕ unit (suc zero) ≈s bot (unit zero ⊕ unit (suc zero)) zeros
  ub01 zero                      = refl
  ub01 (suc zero)                = refl
  ub01 (suc (suc zero))          = refl
  ub01 (suc (suc (suc zero)))    = refl
  ub01 (suc (suc (suc (suc j)))) = refl

------------------------------------------------------------------------
-- Differences of points

private
  P : Fin N → State W
  P = bits W

  -- Four points are coplanar when this vanishes.
  plane : Fin N → Fin N → Fin N → Fin N → State W
  plane a b x y = ((P b ⊕ P a) ⊕ (P x ⊕ P a)) ⊕ (P y ⊕ P a)

  P-ne : {a b : Fin N} → a ≢ b → ¬ (P a ≈s P b)
  P-ne {a} {b} ne e = ne (trans (sym (idx-bits W a)) (trans (idx-cong W e) (idx-bits W b)))

  dd : ∀ x y z → (x xor z) xor (y xor z) ≡ x xor y
  dd false false false = refl
  dd false false true  = refl
  dd false true  false = refl
  dd false true  true  = refl
  dd true  false false = refl
  dd true  false true  = refl
  dd true  true  false = refl
  dd true  true  true  = refl

  cop : ∀ x y w → (x xor y) xor w ≡ false → w ≡ x xor y
  cop false false false e = refl
  cop false true  true  e = refl
  cop true  false true  e = refl
  cop true  true  false e = refl
  cop false false true  ()
  cop false true  false ()
  cop true  false false ()
  cop true  true  true  ()

  -- The difference of two points relative to a third.
  nz₁ : {a b : Fin N} → a ≢ b → NZ (P a ⊕ P b)
  nz₁ ne = diff-nz (P-ne ne)

  nz₂ : {a b r : Fin N} → a ≢ b → NZ ((P a ⊕ P r) ⊕ (P b ⊕ P r))
  nz₂ {a} {b} {r} ne z = diff-nz (P-ne ne) (λ i → trans (sym (dd (P a i) (P b i) (P r i))) (z i))

  ≢-sym : {a b : Fin N} → a ≢ b → b ≢ a
  ≢-sym ne e = ne (sym e)

------------------------------------------------------------------------
-- The frames

private
  -- A list spanning q₀ and D spans the span of q₀, D and unit vectors
  -- of the bottom four wires.
  back-from : ∀ {m d j} (pl : Vec (State W) m) (q₀ : State W) (D : Vec (State W) d) (F : Vec (Fin 4) j) →
    InSpan (pl ++ E4) q₀ → (∀ t → InSpan (pl ++ E4) (lookup D t)) →
    ∀ {y} → InSpan (q₀ ∷ (D ++ map e4 F)) y → InSpan (pl ++ E4) y
  back-from pl q₀ D F s0 sD = span-trans (pl ++ E4) (q₀ ∷ (D ++ map e4 F)) each
    where
    each : ∀ i → InSpan (pl ++ E4) (lookup (q₀ ∷ (D ++ map e4 F)) i)
    each zero    = s0
    each (suc i) = lookup-++-all (InSpan (pl ++ E4)) D (map e4 F) sD
      (λ t → subst (InSpan (pl ++ E4)) (sym (VecP.lookup-map t e4 F)) (e4-span pl (lookup F t))) i

  pt-span : ∀ {m} (pl : Vec (State W) m) (i : Fin m) → InSpan (pl ++ E4) (lookup pl i)
  pt-span pl i = span-++ˡ {xs = pl} E4 (elem-span pl i)

  dif-span : ∀ {m} (pl : Vec (State W) m) (i j : Fin m) → InSpan (pl ++ E4) (lookup pl i ⊕ lookup pl j)
  dif-span pl i j = span-⊕ {xs = pl ++ E4} (pt-span pl i) (pt-span pl j)

------------------------------------------------------------------------
-- Routing two, three and four points

module _ {p : Atom N} where

  routed2 : (a b : Fin N) → a ≢ b → (G : Op 2) → AtI (pt2 a b) G (actVʷ (e p)) →
    (q : Atom 16) → AtI (λ y → idx 4 (c2 y)) G (actVʷ (e q)) → Routed p
  routed2 a b ab G tbl q can = record
    { m = 2 ; pts = pt2 a b ; G = G ; tbl = tbl ; q = q ; cst = c2 ; can = can ; K = Rt.K
    ; lands = lands ; back = λ h → back-from pl (P a) D (Fill.F Rt.fl) (pt-span pl zero) sD (Rt.K-back h) }
    where
    D = (P b ⊕ P a) ∷ []
    module Rt = Route k c (P a) D (indep₁ (nz₁ (≢-sym ab))) (s≤s z≤n)
    pl = tabulate (λ y → P (pt2 a b y))
    sD : ∀ t → InSpan (pl ++ E4) (lookup D t)
    sD zero = dif-span pl (suc zero) zero
    lands : ∀ y → A⟦ Rt.K ⟧ (P (pt2 a b y)) ≈s stack (k + (c + 0)) zeros (c2 y)
    lands zero       = Rt.K-q₀
    lands (suc zero) = Rt.K-at (P b) zero (unit zero) (λ _ → refl) ub0

  routed3 : (a b x : Fin N) → a ≢ b → a ≢ x → b ≢ x → (G : Op 3) → AtI (pt3 a b x) G (actVʷ (e p)) →
    (q : Atom 16) → AtI (λ y → idx 4 (c3 y)) G (actVʷ (e q)) → Routed p
  routed3 a b x ab ax bx G tbl q can = record
    { m = 3 ; pts = pt3 a b x ; G = G ; tbl = tbl ; q = q ; cst = c3 ; can = can ; K = Rt.K
    ; lands = lands ; back = λ h → back-from pl (P a) D (Fill.F Rt.fl) (pt-span pl zero) sD (Rt.K-back h) }
    where
    D = (P b ⊕ P a) ∷ (P x ⊕ P a) ∷ []
    module Rt = Route k c (P a) D
      (indep₂ (nz₁ (≢-sym ab)) (nz₁ (≢-sym ax)) (nz₂ bx)) (s≤s (s≤s z≤n))
    pl = tabulate (λ y → P (pt3 a b x y))
    sD : ∀ t → InSpan (pl ++ E4) (lookup D t)
    sD zero       = dif-span pl (suc zero) zero
    sD (suc zero) = dif-span pl (suc (suc zero)) zero
    lands : ∀ y → A⟦ Rt.K ⟧ (P (pt3 a b x y)) ≈s stack (k + (c + 0)) zeros (c3 y)
    lands zero             = Rt.K-q₀
    lands (suc zero)       = Rt.K-at (P b) zero (unit zero) (λ _ → refl) ub0
    lands (suc (suc zero)) = Rt.K-at (P x) (suc zero) (unit (suc zero)) (λ _ → refl) ub1

  -- Four points: in general position, or coplanar.
  routed4 : (a b x y : Fin N) → a ≢ b → a ≢ x → a ≢ y → b ≢ x → b ≢ y → x ≢ y →
    (G : Op 4) → AtI (pt4 a b x y) G (actVʷ (e p)) →
    (q : Atom 16) → AtI (λ z → idx 4 (c4 z)) G (actVʷ (e q)) →
    (q′ : Atom 16) → AtI (λ z → idx 4 (c4′ z)) G (actVʷ (e q′)) →
    Dec (plane a b x y ≈s zeros) → Routed p
  routed4 a b x y ab ax ay bx by xy G tbl q can q′ can′ = by-plane
    where
    d₁ = P b ⊕ P a
    d₂ = P x ⊕ P a
    d₃ = P y ⊕ P a
    by-plane : Dec (((d₁ ⊕ d₂) ⊕ d₃) ≈s zeros) → Routed p
    pl = tabulate (λ z → P (pt4 a b x y z))
    by-plane (no gen) = record
      { m = 4 ; pts = pt4 a b x y ; G = G ; tbl = tbl ; q = q ; cst = c4 ; can = can ; K = Rt.K
      ; lands = lands ; back = λ h → back-from pl (P a) D (Fill.F Rt.fl) (pt-span pl zero) sD (Rt.K-back h) }
      where
      D = d₁ ∷ d₂ ∷ d₃ ∷ []
      sD : ∀ t → InSpan (pl ++ E4) (lookup D t)
      sD zero             = dif-span pl (suc zero) zero
      sD (suc zero)       = dif-span pl (suc (suc zero)) zero
      sD (suc (suc zero)) = dif-span pl (suc (suc (suc zero))) zero
      module Rt = Route k c (P a) D
        (indep₃ (nz₁ (≢-sym ab)) (nz₁ (≢-sym ax)) (nz₁ (≢-sym ay)) (nz₂ bx) (nz₂ by) (nz₂ xy) gen)
        (s≤s (s≤s (s≤s z≤n)))
      lands : ∀ z → A⟦ Rt.K ⟧ (P (pt4 a b x y z)) ≈s stack (k + (c + 0)) zeros (c4 z)
      lands zero                   = Rt.K-q₀
      lands (suc zero)             = Rt.K-at (P b) zero (unit zero) (λ _ → refl) ub0
      lands (suc (suc zero))       = Rt.K-at (P x) (suc zero) (unit (suc zero)) (λ _ → refl) ub1
      lands (suc (suc (suc zero))) =
        Rt.K-at (P y) (suc (suc zero)) (unit (suc (suc zero))) (λ _ → refl) ub2
    by-plane (yes cpl) = record
      { m = 4 ; pts = pt4 a b x y ; G = G ; tbl = tbl ; q = q′ ; cst = c4′ ; can = can′ ; K = Rt.K
      ; lands = lands ; back = λ h → back-from pl (P a) D (Fill.F Rt.fl) (pt-span pl zero) sD (Rt.K-back h) }
      where
      D = d₁ ∷ d₂ ∷ []
      sD : ∀ t → InSpan (pl ++ E4) (lookup D t)
      sD zero       = dif-span pl (suc zero) zero
      sD (suc zero) = dif-span pl (suc (suc zero)) zero
      module Rt = Route k c (P a) D
        (indep₂ (nz₁ (≢-sym ab)) (nz₁ (≢-sym ax)) (nz₂ bx)) (s≤s (s≤s z≤n))
      lands : ∀ z → A⟦ Rt.K ⟧ (P (pt4 a b x y z)) ≈s stack (k + (c + 0)) zeros (c4′ z)
      lands zero                   = Rt.K-q₀
      lands (suc zero)             = Rt.K-at (P b) zero (unit zero) (λ _ → refl) ub0
      lands (suc (suc zero))       = Rt.K-at (P x) (suc zero) (unit (suc zero)) (λ _ → refl) ub1
      lands (suc (suc (suc zero))) =
        Rt.K-at₂ (P y) zero (suc zero) (unit zero ⊕ unit (suc zero))
          (λ i → cop (d₁ i) (d₂ i) (d₃ i) (cpl i)) ub01

------------------------------------------------------------------------
-- The cases

private
  mm : (a b : Fin N) → Dec (a ≡ b) → Decoded (MM a b)
  mm a .a (yes refl) = trivial (actV-invol (M-gen a))
  mm a b  (no ab)    = routed (routed2 a b ab GMM (atMM (pt2 a b) (inj2 ab))
    (MM (idx 4 (c2 zero)) (idx 4 (c2 (suc zero)))) (atMM (λ z → idx 4 (c2 z)) inj-c2))

  -- Three points in the order of AtomAt's exchanges.
  three : ∀ {p : Atom N} (a b x : Fin N) → a ≢ b → a ≢ x → b ≢ x → (G : Op 3) →
    (Inj (pt3 a b x) → AtI (pt3 a b x) G (actVʷ (e p))) →
    (q : Atom 16) → AtI (λ y → idx 4 (c3 y)) G (actVʷ (e q)) → Decoded p
  three a b x ab ax bx G tbl q can = routed (routed3 a b x ab ax bx G (tbl (inj3 ab ax bx)) q can)

  xx : (a b x y : Fin N) .(ab : a < b) .(xy : x < y) →
    Dec (a ≡ x) → Dec (b ≡ y) → Dec (a ≡ y) → Dec (b ≡ x) → Dec (plane a b x y ≈s zeros) →
    Decoded (XX a b x y ab xy)
  xx a b .a .b ab xy (yes refl) (yes refl) _ _ _ = trivial (actV-invol (X-gen a b ab))
  xx a b .a y ab xy (yes refl) (no b≢y) _ _ _ =
    three a b y (<⇒≢ ab) (<⇒≢ xy) b≢y GXa (λ inj → atXa (pt3 a b y) inj ab xy)
      (XX (idx 4 (c3 zero)) (idx 4 (c3 (suc zero))) (idx 4 (c3 zero)) (idx 4 (c3 (suc (suc zero))))
        (s≤s z≤n) (s≤s z≤n))
      (atXa (λ z → idx 4 (c3 z)) inj-c3 (s≤s z≤n) (s≤s z≤n))
  xx a b x .b ab xy (no a≢x) (yes refl) _ _ _ =
    three a x b a≢x (<⇒≢ ab) (<⇒≢ xy) GXb (λ inj → atXb (pt3 a x b) inj ab xy)
      (XX (idx 4 (c3 zero)) (idx 4 (c3 (suc (suc zero)))) (idx 4 (c3 (suc zero))) (idx 4 (c3 (suc (suc zero))))
        (s≤s z≤n) (s≤s (s≤s z≤n)))
      (atXb (λ z → idx 4 (c3 z)) inj-c3 (s≤s z≤n) (s≤s (s≤s z≤n)))
  xx a b x .a ab xy (no a≢x) (no b≢y) (yes refl) _ _ =
    three x a b (<⇒≢ xy) (<⇒≢ (FP.<-trans xy ab)) (<⇒≢ ab) GXc (λ inj → atXc (pt3 x a b) inj ab xy)
      (XX (idx 4 (c3 (suc zero))) (idx 4 (c3 (suc (suc zero)))) (idx 4 (c3 zero)) (idx 4 (c3 (suc zero)))
        (s≤s (s≤s z≤n)) (s≤s z≤n))
      (atXc (λ z → idx 4 (c3 z)) inj-c3 (s≤s (s≤s z≤n)) (s≤s z≤n))
  xx a b .b y ab xy (no a≢x) (no b≢y) (no a≢y) (yes refl) _ =
    three a b y (<⇒≢ ab) (<⇒≢ (FP.<-trans ab xy)) (<⇒≢ xy) GXd (λ inj → atXd (pt3 a b y) inj ab xy)
      (XX (idx 4 (c3 zero)) (idx 4 (c3 (suc zero))) (idx 4 (c3 (suc zero))) (idx 4 (c3 (suc (suc zero))))
        (s≤s z≤n) (s≤s (s≤s z≤n)))
      (atXd (λ z → idx 4 (c3 z)) inj-c3 (s≤s z≤n) (s≤s (s≤s z≤n)))
  xx a b x y ab xy (no a≢x) (no b≢y) (no a≢y) (no b≢x) pd =
    routed (routed4 a b x y (<⇒≢ ab) a≢x a≢y b≢x b≢y (<⇒≢ xy) GXX
      (atXX (pt4 a b x y) (inj4 (<⇒≢ ab) a≢x a≢y b≢x b≢y (<⇒≢ xy)) ab xy)
      (XX (idx 4 (c4 zero)) (idx 4 (c4 (suc zero))) (idx 4 (c4 (suc (suc zero))))
          (idx 4 (c4 (suc (suc (suc zero))))) (s≤s z≤n) (s≤s (s≤s (s≤s z≤n))))
      (atXX (λ z → idx 4 (c4 z)) inj-c4 (s≤s z≤n) (s≤s (s≤s (s≤s z≤n))))
      (XX (idx 4 (c4′ zero)) (idx 4 (c4′ (suc zero))) (idx 4 (c4′ (suc (suc zero))))
          (idx 4 (c4′ (suc (suc (suc zero))))) (s≤s z≤n) (s≤s (s≤s (s≤s z≤n))))
      (atXX (λ z → idx 4 (c4′ z)) inj-c4′ (s≤s z≤n) (s≤s (s≤s (s≤s z≤n)))) pd)

  jj : (a b x y : Fin N) .(ab : a < b) .(bx : b < x) .(xy : x < y) →
    Dec (plane a b x y ≈s zeros) → Decoded (J a b x y ab bx xy)
  jj a b x y ab bx xy pd =
    routed (routed4 a b x y a≢b a≢x a≢y b≢x b≢y x≢y GJ
      (atJ (pt4 a b x y) (inj4 a≢b a≢x a≢y b≢x b≢y x≢y) ab bx xy)
      (J (idx 4 (c4 zero)) (idx 4 (c4 (suc zero))) (idx 4 (c4 (suc (suc zero))))
         (idx 4 (c4 (suc (suc (suc zero))))) (s≤s z≤n) (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n))))
      (atJ (λ z → idx 4 (c4 z)) inj-c4 (s≤s z≤n) (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n))))
      (J (idx 4 (c4′ zero)) (idx 4 (c4′ (suc zero))) (idx 4 (c4′ (suc (suc zero))))
         (idx 4 (c4′ (suc (suc (suc zero))))) (s≤s z≤n) (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n))))
      (atJ (λ z → idx 4 (c4′ z)) inj-c4′ (s≤s z≤n) (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n)))) pd)
    where
    a≢b = <⇒≢ ab
    a≢x = <⇒≢ (FP.<-trans ab bx)
    a≢y = <⇒≢ (FP.<-trans (FP.<-trans ab bx) xy)
    b≢x = <⇒≢ bx
    b≢y = <⇒≢ (FP.<-trans bx xy)
    x≢y = <⇒≢ xy

classify : (p : Atom N) → Decoded p
classify (MM a b)             = mm a b (a FP.≟ b)
classify (XX a b x y ab xy)   =
  xx a b x y ab xy (a FP.≟ x) (b FP.≟ y) (a FP.≟ y) (b FP.≟ x) (≈s? (plane a b x y) zeros)
classify (J a b x y ab bx xy) = jj a b x y ab bx xy (≈s? (plane a b x y) zeros)

-- The decoder of atoms.
atom : Atom N → P.Circuit W
atom p = decode (classify p)

------------------------------------------------------------------------
-- The points of a decoded atom are among its indices

ArgsIn : ∀ {r} → Vec (State W) r → Atom N → Set
ArgsIn xs (MM a b)             = InSpan xs (P a) × InSpan xs (P b)
ArgsIn xs (XX a b x y _ _)     = InSpan xs (P a) × InSpan xs (P b) × InSpan xs (P x) × InSpan xs (P y)
ArgsIn xs (J a b x y _ _ _)    = InSpan xs (P a) × InSpan xs (P b) × InSpan xs (P x) × InSpan xs (P y)

PtsIn : ∀ {r} → Vec (State W) r → {p : Atom N} → Decoded p → Set
PtsIn xs (trivial _) = ⊤
PtsIn xs (routed r)  = ∀ y → InSpan xs (P (Routed.pts r y))

pts-in : ∀ {r} (xs : Vec (State W) r) p → ArgsIn xs p → PtsIn xs (classify p)
pts-in xs (MM a b) (sa , sb) = mm-in (a FP.≟ b)
  where
  mm-in : (d : Dec (a ≡ b)) → PtsIn xs (mm a b d)
  mm-in (yes refl) = tt
  mm-in (no _)     = λ { zero → sa ; (suc zero) → sb }
pts-in xs (XX a b x y ab xy) (sa , sb , sx , sy) =
  xx-in (a FP.≟ x) (b FP.≟ y) (a FP.≟ y) (b FP.≟ x) (≈s? (plane a b x y) zeros)
  where
  xx-in : (d₁ : Dec (a ≡ x)) (d₂ : Dec (b ≡ y)) (d₃ : Dec (a ≡ y)) (d₄ : Dec (b ≡ x))
    (d₅ : Dec (plane a b x y ≈s zeros)) → PtsIn xs (xx a b x y ab xy d₁ d₂ d₃ d₄ d₅)
  xx-in (yes refl) (yes refl) _          _          _       = tt
  xx-in (yes refl) (no _)     _          _          _       =
    λ { zero → sa ; (suc zero) → sb ; (suc (suc zero)) → sy }
  xx-in (no _)     (yes refl) _          _          _       =
    λ { zero → sa ; (suc zero) → sx ; (suc (suc zero)) → sb }
  xx-in (no _)     (no _)     (yes refl) _          _       =
    λ { zero → sx ; (suc zero) → sa ; (suc (suc zero)) → sb }
  xx-in (no _)     (no _)     (no _)     (yes refl) _       =
    λ { zero → sa ; (suc zero) → sb ; (suc (suc zero)) → sy }
  xx-in (no _)     (no _)     (no _)     (no _)     (yes _) =
    λ { zero → sa ; (suc zero) → sb ; (suc (suc zero)) → sx ; (suc (suc (suc zero))) → sy }
  xx-in (no _)     (no _)     (no _)     (no _)     (no _)  =
    λ { zero → sa ; (suc zero) → sb ; (suc (suc zero)) → sx ; (suc (suc (suc zero))) → sy }
pts-in xs (J a b x y ab bx xy) (sa , sb , sx , sy) = jj-in (≈s? (plane a b x y) zeros)
  where
  jj-in : (d : Dec (plane a b x y ≈s zeros)) → PtsIn xs (jj a b x y ab bx xy d)
  jj-in (yes _) = λ { zero → sa ; (suc zero) → sb ; (suc (suc zero)) → sx ; (suc (suc (suc zero))) → sy }
  jj-in (no _)  = λ { zero → sa ; (suc zero) → sb ; (suc (suc zero)) → sx ; (suc (suc (suc zero))) → sy }
