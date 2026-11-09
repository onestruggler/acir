------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled matchings: involution, conjugation and Klein pairs
--
-- A label is one of the 105 perfect matchings of the Gray positions
-- (CLabels), and Xm x is the frame of G = CX₃₀ that places μ₀ on it:
-- the matching x controlled by wire 3.  Three relations hold among
-- them, each under a side condition that is decided on the labels (by
-- comparing matchings on the eight positions), so that a certificate
-- over labels (LabelEngine) is checked by computation:
--
-- * inv:   Xm x Xm x = ε;
-- * conj:  Xm x Xm y Xm x = Xm (x y x).  G is X on wire 0 times Ḡ, the same
--          controlled by wire 3 = 0 (split), so Xm x is P x Q̄ x with P x a
--          circuit of the lower wires (the matching x, uncontrolled) and
--          Q̄ x the matching x controlled by wire 3 = 0.  Q̄ x commutes with
--          Xm y (block commutation, BC): conjugated by the frame of x it
--          is Ḡ against a frame of G, which the centraliser of μ₀
--          carries to one of five base frames (CLabels' orbit table and
--          the frame lemma W′); the five base commutations are the
--          module parameter.  So Xm x Xm y Xm x = P x Xm y P x, the frame of
--          G by x y x;
-- * klein: Xm x Xm y = Xm (x y) for commuting x ≠ y whose product is a
--          matching: a frame carries the standard Klein pair, μ₀ and its
--          conjugate by CX₀₁, to x and y, and there the relation holds
--          on wires 0, 1, 3.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.CRel where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; if_then_else_)
import Data.Bool.Base
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; reverse)
open import Data.Maybe.Base using (Maybe ; just ; nothing ; fromMaybe)
import Data.Maybe.Base as Maybe
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary.Decidable.Core using (yes ; no)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (⟦_⟧ ; eqF ; eqF-sound)
open import Examples.Groups.XCXCCX-4bit.Placed
  using (PG ; Xᵖ ; CXᵖ ; CCXᵖ ; Wire ; ι ; ι* ; every ; avoids ; ⟦_⟧ᵖ* ; conj-• ; ιX₀)
open import Examples.Groups.XCXCCX-4bit.ToPlaced using (pg ; pg-ok)
open import Examples.Groups.XCXCCX-4bit.Narrow3 using (narrowᵖ)
open import Examples.Groups.XCXCCX-4bit.PFrames
import Examples.Groups.XCXCCX-4bit.Width3 as W3
open import Examples.Groups.XCXCCX-4bit.CBase
open import Examples.Groups.XCXCCX-4bit.CFrame
open import Examples.Groups.XCXCCX-4bit.CLabels
import Examples.Groups.Symmetric.CoxeterFrames as CF

open PB (4 VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)
open PP (4 VRel,_===_) using (by-assoc ; to-list)
open SR (PP.word-setoid (4 VRel,_===_))

private
  ∧ˡ : ∀ {a b} → (a ∧ b) ≡ true → a ≡ true
  ∧ˡ {true} _ = Eq.refl

  ∧ʳ : ∀ {a b} → (a ∧ b) ≡ true → b ≡ true
  ∧ʳ {true} q = q

------------------------------------------------------------------------
-- Frames from lists

private
  avoid? : (t : Fin 8) (xs : List (Fin 8)) → Maybe (CF.Avoid t xs)
  avoid? t []       = just CF.[]
  avoid? t (x ∷ xs) = av (t FinP.≟ x) (avoid? t xs)
    where
    av : _ → Maybe (CF.Avoid t xs) → Maybe (CF.Avoid t (x ∷ xs))
    av (no ne) (just a) = just (ne CF.∷ a)
    av _       _        = nothing

  distinct? : (ts : List (Fin 8)) → Maybe (CF.Distinct ts)
  distinct? []       = just CF.[]
  distinct? (t ∷ ts) = ds (avoid? t ts) (distinct? ts)
    where
    ds : Maybe (CF.Avoid t ts) → Maybe (CF.Distinct ts) → Maybe (CF.Distinct (t ∷ ts))
    ds (just a) (just d) = just (a CF.∷ d)
    ds _        _        = nothing

  frm′ : (ts : List (Fin 8)) → Maybe (CF.Distinct ts) → CW
  frm′ ts (just d) = CF.frame ts d
  frm′ ts nothing  = ε

-- The frame of a list of distinct positions (ε otherwise).
frameD : List (Fin 8) → CW
frameD ts = frm′ ts (distinct? ts)

------------------------------------------------------------------------
-- Labels

L : Set
L = Fin 105

frm : L → CW
frm i = lookup frmT i

-- The controlled matching of a label.
Xm : L → Circuit 4
Xm i = Fr G (frm i)

tbl : L → Fin 8 → Fin 8
tbl i = lookup (lookup tblT i)

private
  findIn : {n : ℕ} → Vec (Vec (Fin 8) 8) n → (Fin 8 → Fin 8) → Maybe (Fin n)
  findIn []       f = nothing
  findIn (t ∷ ts) f = if all8 (λ x → lookup t x ==₈ f x) then just zero else Maybe.map suc (findIn ts f)

-- The label of a matching given as a function.
find : (Fin 8 → Fin 8) → Maybe L
find = findIn tblT

-- x y x and x y.
c3 : L → L → L
c3 x y = fromMaybe x (find (λ p → tbl x (tbl y (tbl x p))))

mul : L → L → L
mul x y = fromMaybe x (find (λ p → tbl x (tbl y p)))

_==ᴸ_ : L → L → Bool
x ==ᴸ y = toℕ x ℕ.≡ᵇ toℕ y

==ᴸ-sound : (x y : L) → (x ==ᴸ y) ≡ true → x ≡ y
==ᴸ-sound x y h = FinP.toℕ-injective (ℕP.≡ᵇ⇒≡ (toℕ x) (toℕ y) (T-true h))
  where
  T-true : ∀ {b} → b ≡ true → Data.Bool.Base.T b
  T-true Eq.refl = _

------------------------------------------------------------------------
-- Frames

Fr-cong : {a b : Circuit 4} (F : CW) → 4 ⊢ a ≈ b → 4 ⊢ Fr a F ≈ Fr b F
Fr-cong F e = cong refl (cong e refl)

Fr-• : (a b : Circuit 4) (F : CW) → 4 ⊢ Fr a F • Fr b F ≈ Fr (a • b) F
Fr-• a b F = conj-• (Pc-inv′ 0 ℕP.≤-refl F) a b

Fr-invol : {b : Circuit 4} (F : CW) → 4 ⊢ b • b ≈ ε → 4 ⊢ Fr b F • Fr b F ≈ ε
Fr-invol {b} F e = trans (Fr-• b b F) (trans (Fr-cong F e) (trans (cong refl left-unit) (Pc-inv 0 ℕP.≤-refl F)))

Fr-comm : {a b : Circuit 4} (F : CW) → Comm a b → Comm (Fr a F) (Fr b F)
Fr-comm {a} {b} F h = trans (Fr-• a b F) (trans (Fr-cong F h) (sym (Fr-• b a F)))

comm-≈ʳ : {a b b′ : Circuit 4} → 4 ⊢ b ≈ b′ → Comm a b′ → Comm a b
comm-≈ʳ e h = comm-sym (comm-≈ e (comm-sym h))

------------------------------------------------------------------------
-- Small identities on few wires

private
  -- An identity of placed words on three wires.
  nar : (m : Wire) (u v : List PG) → every (avoids m) u ≡ true → every (avoids m) v ≡ true →
        eqF 4 ⟦ u ⟧ᵖ* ⟦ v ⟧ᵖ* ≡ true → 4 ⊢ ι* u ≈ ι* v
  nar m u v hu hv hs = narrowᵖ m u v hu hv (eqF-sound 4 _ _ hs)

  -- The same, between circuits with the same letters.
  viaN : {a b : Circuit 4} (m : Wire) (u v : List PG) → every (avoids m) u ≡ true → every (avoids m) v ≡ true →
         eqF 4 ⟦ u ⟧ᵖ* ⟦ v ⟧ᵖ* ≡ true → to-list a ≡ to-list (ι* u) → to-list (ι* v) ≡ to-list b → 4 ⊢ a ≈ b
  viaN m u v hu hv hs p q = trans (by-assoc p) (trans (nar m u v hu hv hs) (by-assoc q))

GG : 4 ⊢ G • G ≈ ε
GG = viaN ₁ (CXᵖ ₃ ₀ ∷ CXᵖ ₃ ₀ ∷ []) [] Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl

ḠḠ : 4 ⊢ Ḡ • Ḡ ≈ ε
ḠḠ = viaN ₁ (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) [] Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl

X₀X₀ : 4 ⊢ ι (Xᵖ ₀) • ι (Xᵖ ₀) ≈ ε
X₀X₀ = viaN ₁ (Xᵖ ₀ ∷ Xᵖ ₀ ∷ []) [] Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl

-- G is X on wire 0 times Ḡ, in either order.
split : 4 ⊢ G ≈ ι (Xᵖ ₀) • Ḡ
split = viaN ₁ (CXᵖ ₃ ₀ ∷ []) (Xᵖ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl

split-comm : Comm (ι (Xᵖ ₀)) Ḡ
split-comm = viaN ₁ (Xᵖ ₀ ∷ Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []) (Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ Xᵖ ₀ ∷ []) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl

-- X on wire 0 is the product of the four flips.
w₀ : CW
w₀ = [ s₀ ]ʷ • [ s₂ ]ʷ • [ s₄ ]ʷ • [ s₆ ]ʷ

X₀-w₀ : 4 ⊢ ι (Xᵖ ₀) ≈ Pc 0 w₀
X₀-w₀ = trans ιX₀ (P-eq {X} {W3.T 0 • W3.T 2 • W3.T 4 • W3.T 6}
                       (eqF-sound 3 ⟦ X ⟧ ⟦ W3.T 0 • W3.T 2 • W3.T 4 • W3.T 6 ⟧ Eq.refl))

-- A three-wire circuit on the lower wires commutes with X on wire 3.
comm-X₃ : (w : Circuit 3) → Comm (w ↓ᵏ 1) (ι (Xᵖ ₃))
comm-X₃ [ gate₀ ⌈ () ⌉ ]ʷ
comm-X₃ [ gate₁ ⌈ X-gate ⌉ ]ʷ       = comm-circ [ gate₁ ⌈ X-gate ⌉ ]ʷ (Xᵖ ₃) Eq.refl
comm-X₃ [ gate₂ ⌈ CX-gate ⌉ ]ʷ      = comm-circ [ gate₂ ⌈ CX-gate ⌉ ]ʷ (Xᵖ ₃) Eq.refl
comm-X₃ [ gate₂ swap ]ʷ             = comm-circ [ gate₂ swap ]ʷ (Xᵖ ₃) Eq.refl
comm-X₃ [ gate₃ ⌈ CCX-gate ⌉ ]ʷ     = comm-circ [ gate₃ ⌈ CCX-gate ⌉ ]ʷ (Xᵖ ₃) Eq.refl
comm-X₃ [ gate₀ ⌈ () ⌉ ↥ ]ʷ
comm-X₃ [ gate₁ ⌈ X-gate ⌉ ↥ ]ʷ     = comm-circ [ gate₁ ⌈ X-gate ⌉ ↥ ]ʷ (Xᵖ ₃) Eq.refl
comm-X₃ [ gate₂ ⌈ CX-gate ⌉ ↥ ]ʷ    = comm-circ [ gate₂ ⌈ CX-gate ⌉ ↥ ]ʷ (Xᵖ ₃) Eq.refl
comm-X₃ [ gate₂ swap ↥ ]ʷ           = comm-circ [ gate₂ swap ↥ ]ʷ (Xᵖ ₃) Eq.refl
comm-X₃ [ gate₀ ⌈ () ⌉ ↥ ↥ ]ʷ
comm-X₃ [ gate₁ ⌈ X-gate ⌉ ↥ ↥ ]ʷ   = comm-circ [ gate₁ ⌈ X-gate ⌉ ↥ ↥ ]ʷ (Xᵖ ₃) Eq.refl
comm-X₃ [ gate₀ ⌈ () ⌉ ↥ ↥ ↥ ]ʷ
comm-X₃ ε                           = comm-ε
comm-X₃ (u • v)                     = comm-• (comm-X₃ u) (comm-X₃ v)

-- So does the circuit of a Coxeter word, and if its permutation
-- commutes with μ₀ it commutes with Ḡ.
comm-Pc-X₃ : (r : CW) → Comm (Pc 0 r) (ι (Xᵖ ₃))
comm-Pc-X₃ r = Eq.subst (λ z → Comm z (ι (Xᵖ ₃))) (Eq.sym (Pc-↓ 0 r)) (comm-X₃ _)

inC? : CW → Bool
inC? r = all8 (λ x → actF r (μ₀ x) ==₈ μ₀ (actF r x))

inC-sound : (r : CW) → inC? r ≡ true → InC r
inC-sound r h x =
  Eq.trans (Eq.sym (actF-ok r (μ₀ x)))
    (Eq.trans (==₈-sound _ _ (all8-sound (λ y → actF r (μ₀ y) ==₈ μ₀ (actF r y)) h x))
              (Eq.cong μ₀ (actF-ok r x)))

comm-Pc-Ḡ : (r : CW) → inC? r ≡ true → Comm (Pc 0 r) Ḡ
comm-Pc-Ḡ r h = commḠ (W-core r (inC-sound r h)) (comm-Pc-X₃ r)

------------------------------------------------------------------------
-- The side conditions, decided on the labels

private
  bc-ok : CW → Maybe L → Bool
  bc-ok F (just m) = eqMatch F (lookup orbCT m • baseW (lookup orbKT m))
                     ∧ (inC? (lookup orbCT m) ∧ inC? (inv (lookup orbCT m)))
  bc-ok F nothing  = false

-- Ḡ against a frame of G, through the orbit table.
BC₀-ok : CW → Bool
BC₀-ok F = bc-ok F (find (matchF F))

-- Q̄ x against Xm y.
BC-ok : L → L → Bool
BC-ok x y = eqMatch (frm x • (inv (frm x) • frm y)) (frm y) ∧ BC₀-ok (inv (frm x) • frm y)

-- The word of the lower part of Xm x, the matching x on both halves.
cP : CW → CW
cP F = F • (w₀ • inv F)

-- The side condition of conjugation.
conj-ok : L → L → Bool
conj-ok x y = eqMatch (cP (frm x) • frm y) (frm (c3 x y)) ∧ BC-ok x y

-- The positions of the Klein four-group of x and y: the orbit of 0
-- and of the first position outside it.
kleinList : L → L → List (Fin 8)
kleinList x y = a ∷ tx a ∷ ty a ∷ tx (ty a) ∷ b ∷ tx b ∷ ty b ∷ tx (ty b) ∷ []
  where
  tx = tbl x
  ty = tbl y
  a : Fin 8
  a = zero
  out : Fin 8 → Bool
  out p = not (p ==₈ a) ∧ (not (p ==₈ tx a) ∧ (not (p ==₈ ty a) ∧ not (p ==₈ tx (ty a))))
  first : List (Fin 8) → Fin 8
  first []       = a
  first (p ∷ ps) = if out p then p else first ps
  b = first (₁ ∷ ₂ ∷ ₃ ∷ ₄ ∷ ₅ ∷ ₆ ∷ ₇ ∷ [])

-- The flip of wire 1, placed by the swap of wires 0, 1.
κw : CW
κw = [ s₁ ]ʷ • [ s₂ ]ʷ • [ s₁ ]ʷ • [ s₄ ]ʷ • [ s₅ ]ʷ • [ s₄ ]ʷ

private
  ko : (x y : L) → Maybe (CF.Distinct (kleinList x y)) → Bool
  ko x y (just d) = eqMatch (frm x) (CF.frame (kleinList x y) d • ε)
                    ∧ (eqMatch (frm y) (CF.frame (kleinList x y) d • baseW ₁)
                    ∧ eqMatch (frm (mul x y)) (CF.frame (kleinList x y) d • κw))
  ko x y nothing  = false

-- The side condition of klein.
klein-ok : L → L → Bool
klein-ok x y = ko x y (distinct? (kleinList x y))

-- Q̄ x and P x: the matching x controlled by wire 3 = 0, and on both
-- halves.
Q̄ : CW → Circuit 4
Q̄ F = Fr Ḡ F

P : CW → Circuit 4
P F = Fr (ι (Xᵖ ₀)) F

------------------------------------------------------------------------
-- The calculus, given the five base commutations

module Calculus (base : (k : Fin 5) → Comm Ḡ (Fr G (baseW k))) where

  ----------------------------------------------------------------------
  -- Involution

  X-inv : (x : L) → 4 ⊢ Xm x • Xm x ≈ ε
  X-inv x = Fr-invol (frm x) GG

  ----------------------------------------------------------------------
  -- Block commutation

  private
    bc : (F : CW) (mm : Maybe L) → bc-ok F mm ≡ true → Comm Ḡ (Fr G F)
    bc F (just m) h =
      comm-≈ʳ (trans (W′ F (c • baseW k) (∧ˡ h)) (sym (Fr-conj G c (baseW k))))
        (comm-sym (comm-• (comm-Pc-Ḡ c (∧ˡ h′)) (comm-• (comm-sym (base k)) (comm-Pc-Ḡ (inv c) (∧ʳ {inC? c} h′)))))
      where
      c = lookup orbCT m
      k = lookup orbKT m
      h′ = ∧ʳ {eqMatch F (c • baseW k)} h
    bc F nothing ()

  BC₀ : (F : CW) → BC₀-ok F ≡ true → Comm Ḡ (Fr G F)
  BC₀ F h = bc F (find (matchF F)) h

  BC : (x y : L) → BC-ok x y ≡ true → Comm (Q̄ (frm x)) (Xm y)
  BC x y h =
    comm-≈ʳ (trans (sym (W′ (frm x • F) (frm y) (∧ˡ h))) (sym (Fr-conj G (frm x) F)))
      (Fr-comm (frm x) (BC₀ F (∧ʳ {eqMatch (frm x • F) (frm y)} h)))
    where
    F = inv (frm x) • frm y

  ----------------------------------------------------------------------
  -- Conjugation

  private
    X-PQ : (F : CW) → 4 ⊢ Fr G F ≈ P F • Q̄ F
    X-PQ F = trans (Fr-cong F split) (sym (Fr-• _ _ F))

    X-QP : (F : CW) → 4 ⊢ Fr G F ≈ Q̄ F • P F
    X-QP F = trans (X-PQ F) (Fr-comm F split-comm)

    Q̄Q̄ : (F : CW) → 4 ⊢ Q̄ F • Q̄ F ≈ ε
    Q̄Q̄ F = Fr-invol F ḠḠ

    PP : (F : CW) → 4 ⊢ P F • P F ≈ ε
    PP F = Fr-invol F X₀X₀

    P-Pc : (F : CW) → 4 ⊢ P F ≈ Pc 0 (cP F)
    P-Pc F = cong refl (cong X₀-w₀ refl)

    -- P F is also the circuit of the inverse word.
    P-Pc⁻ : (F : CW) → 4 ⊢ P F ≈ Pc 0 (inv (cP F))
    P-Pc⁻ F = sym (begin
      Pc 0 (inv c)                            ≈⟨ sym left-unit ⟩
      ε • Pc 0 (inv c)                        ≈⟨ cong (sym (PP F)) refl ⟩
      (P F • P F) • Pc 0 (inv c)              ≈⟨ assoc ⟩
      P F • (P F • Pc 0 (inv c))              ≈⟨ cong refl (cong (P-Pc F) refl) ⟩
      P F • (Pc 0 c • Pc 0 (inv c))           ≈⟨ cong refl (Pc-inv 0 ℕP.≤-refl c) ⟩
      P F • ε                                 ≈⟨ right-unit ⟩
      P F                                     ∎)
      where
      c = cP F

  X-conj : (x y : L) → conj-ok x y ≡ true → 4 ⊢ Xm x • Xm y • Xm x ≈ Xm (c3 x y)
  X-conj x y h = begin
    Xm x • (Xm y • Xm x)                                ≈⟨ cong (X-PQ fx) (cong refl (X-QP fx)) ⟩
    (A • B) • (Y • (B • A))                             ≈⟨ assoc ⟩
    A • (B • (Y • (B • A)))                             ≈⟨ cong refl (sym assoc) ⟩
    A • ((B • Y) • (B • A))                             ≈⟨ cong refl (cong (BC x y (∧ʳ {eqMatch (cP fx • frm y) (frm (c3 x y))} h)) refl) ⟩
    A • ((Y • B) • (B • A))                             ≈⟨ cong refl assoc ⟩
    A • (Y • (B • (B • A)))                             ≈⟨ cong refl (cong refl (sym assoc)) ⟩
    A • (Y • ((B • B) • A))                             ≈⟨ cong refl (cong refl (cong (Q̄Q̄ fx) refl)) ⟩
    A • (Y • (ε • A))                                   ≈⟨ cong refl (cong refl left-unit) ⟩
    A • (Y • A)                                         ≈⟨ cong (P-Pc fx) (cong refl (P-Pc⁻ fx)) ⟩
    Pc 0 (cP fx) • (Y • Pc 0 (inv (cP fx)))             ≈⟨ Fr-conj G (cP fx) (frm y) ⟩
    Fr G (cP fx • frm y)                                ≈⟨ W′ (cP fx • frm y) (frm (c3 x y)) (∧ˡ h) ⟩
    Xm (c3 x y)                                         ∎
    where
    fx = frm x
    A = P fx
    B = Q̄ fx
    Y = Xm y

  ----------------------------------------------------------------------
  -- Klein pairs

  private
    -- The standard Klein pair: μ₀, μ₀ under CX₀₁ and their product, the
    -- flip of wire 1, as frames on wires 0, 1, 3.
    pc-cx : 4 ⊢ Pc 0 (baseW ₁) ≈ ι* (CXᵖ ₀ ₁ ∷ [])
    pc-cx = trans (pg-ok (Pc 0 (baseW ₁))) (nar ₃ (pg (Pc 0 (baseW ₁))) (CXᵖ ₀ ₁ ∷ []) Eq.refl Eq.refl Eq.refl)

    pc-cx⁻ : 4 ⊢ Pc 0 (inv (baseW ₁)) ≈ ι* (CXᵖ ₀ ₁ ∷ [])
    pc-cx⁻ = trans (pg-ok (Pc 0 (inv (baseW ₁)))) (nar ₃ (pg (Pc 0 (inv (baseW ₁)))) (CXᵖ ₀ ₁ ∷ []) Eq.refl Eq.refl Eq.refl)

    pc-sw : 4 ⊢ Pc 0 κw ≈ ι* (CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₀ ∷ [])
    pc-sw = trans (pg-ok (Pc 0 κw)) (nar ₃ (pg (Pc 0 κw)) (CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₀ ∷ []) Eq.refl Eq.refl Eq.refl)

    pc-sw⁻ : 4 ⊢ Pc 0 (inv κw) ≈ ι* (CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₀ ∷ [])
    pc-sw⁻ = trans (pg-ok (Pc 0 (inv κw))) (nar ₃ (pg (Pc 0 (inv κw))) (CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₀ ∷ []) Eq.refl Eq.refl Eq.refl)

    klein-base : 4 ⊢ G • Fr G (baseW ₁) ≈ Fr G κw
    klein-base = begin
      G • (Pc 0 (baseW ₁) • G • Pc 0 (inv (baseW ₁)))
          ≈⟨ cong refl (cong pc-cx (cong refl pc-cx⁻)) ⟩
      G • (ι* (CXᵖ ₀ ₁ ∷ []) • G • ι* (CXᵖ ₀ ₁ ∷ []))
          ≈⟨ viaN ₂ (CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₀ ₁ ∷ [])
                 (CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₀ ∷ [])
                 Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl ⟩
      ι* (CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₀ ∷ []) • G • ι* (CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₀ ∷ [])
          ≈⟨ sym (cong pc-sw (cong refl pc-sw⁻)) ⟩
      Pc 0 κw • G • Pc 0 (inv κw)
          ∎

    kl : (x y : L) (md : Maybe (CF.Distinct (kleinList x y))) → ko x y md ≡ true →
         4 ⊢ Xm x • Xm y ≈ Xm (mul x y)
    kl x y (just d) h = begin
      Fr G (frm x) • Fr G (frm y)                                    ≈⟨ cong (W′ (frm x) (kc • ε) (∧ˡ h)) (W′ (frm y) (kc • baseW ₁) (∧ˡ h′)) ⟩
      Fr G (kc • ε) • Fr G (kc • baseW ₁)                            ≈⟨ cong (sym (Fr-conj G kc ε)) (sym (Fr-conj G kc (baseW ₁))) ⟩
      Fr (Fr G ε) kc • Fr (Fr G (baseW ₁)) kc                        ≈⟨ Fr-• (Fr G ε) (Fr G (baseW ₁)) kc ⟩
      Fr (Fr G ε • Fr G (baseW ₁)) kc                                ≈⟨ Fr-cong kc (cong (trans left-unit right-unit) refl) ⟩
      Fr (G • Fr G (baseW ₁)) kc                                     ≈⟨ Fr-cong kc klein-base ⟩
      Fr (Fr G κw) kc                                                ≈⟨ Fr-conj G kc κw ⟩
      Fr G (kc • κw)                                                 ≈⟨ sym (W′ (frm (mul x y)) (kc • κw) (∧ʳ {eqMatch (frm y) (kc • baseW ₁)} h′)) ⟩
      Fr G (frm (mul x y))                                           ∎
      where
      kc = CF.frame (kleinList x y) d
      h′ = ∧ʳ {eqMatch (frm x) (kc • ε)} h
    kl x y nothing ()

  X-klein : (x y : L) → klein-ok x y ≡ true → 4 ⊢ Xm x • Xm y ≈ Xm (mul x y)
  X-klein x y h = kl x y (distinct? (kleinList x y)) h
