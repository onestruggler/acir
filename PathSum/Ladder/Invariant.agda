------------------------------------------------------------------------
-- Presentations of groups
--
-- What every path-sum reachable from the ladder looks like (for Amy,
-- QPL 2018, proposition 3.2)
--
-- PathSum.Ladder's ξ n is a ladder of n Toffoli gadgets.  Here is the
-- invariant that every path-sum figure 2 reaches from it satisfies
-- (PathSum.Ladder.Steps proves that), stated through values only, so
-- that it survives the renumbering of path variables every step does
-- and the substitution of quotients whose coefficients are never
-- computed.
--
-- A layout (Layout n m) of a path-sum with m path variables gives
--
--  * each gadget a state (st): live, half or dead (PathSum.Ladder.
--    Gadget);
--  * each path variable a role (role): its gadget and its kind, u or v;
--  * each role the path variable that has it, if any (loc), inverse to
--    role (loc-role, role-loc); the roles present are exactly those
--    the state allows (loc-present): u and v of a live gadget, v of a
--    half one, nothing of a dead one.
--
-- At a Boolean point x of the 2n wires and y of the path variables the
-- layout reads each gadget's data (gads): its state, x_g, a_g, and the
-- values of the variables with its two roles (rd).  The invariant
-- (Inv n ψ) is then that the normalisation is the sum of the states'
-- weights, that the phase of ψ is ½ times the gadgets' phase bit
-- modulo 1, and that its outputs, read modulo 2, are x on the x wires
-- and the gadgets' values on the a wires (outF) -- at every point.
--
-- * Inv-ξ: ξ n satisfies it, every gadget live.
-- * Inv-front: renumbering the path variables (PathSum.Reorder.front,
--   which every step at a variable other than the first does) keeps
--   it: the roles are renumbered along (π, unπ), and eval-front reads
--   the renumbered path-sum at the renumbered point.
-- * Tools for the steps: eval-true, eval-false and eval-head read the
--   first path variable (re-proved here from PathSum.Denotation's
--   statements, to keep the semantics out); drop0 is the layout left
--   when the first path variable is removed; half-valued says every
--   value of the phase is a multiple of ½.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Ladder.Invariant (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.Fin.Base using
  (Fin; zero; suc; splitAt; punchIn; punchOut; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using
  (splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ; punchIn-punchOut;
   punchOut-punchIn; punchOut-cong; punchInᵢ≢i)
  renaming (_≟_ to _≟ᶠ_)
open import Data.Fin.Subset using (Subset; inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ; +_)
  renaming (_+_ to _+ℤ_; _-_ to _-ℤ_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; divides; ∣m∣n⇒∣m+n; ∣-trans)
open import Data.Integer.Properties using (+-identityˡ; *-comm; *-identityˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just; _>>=_)
  renaming (map to mapᴹ)
open import Data.Nat.Base using (zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Vec.Base using (_∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; _:+_; _:-_; _:=_)

private
  M : ℕ
  M = ℕ.suc (ℕ.suc (ℕ.suc M₀))

open import PathSum.Base using
  (PathSum; ⟨_,_⟩; phase; out; head-part; tail-part)
open import PathSum.Ladder M₀ using
  (_≡ᴹ_; mk≡ᴹ; ≡ᴹ⇒∣; ≡ᴹ-trans; ≡⇒≡ᴹ; hb; xw; aw; ξ; G₀; eval-ξ-phase;
   outVal; odd-ξ-out)
open import PathSum.Ladder.Gadget using
  (State; live; half; dead; Kind; U; V; Role; present; Gad; gad; step;
   term; prevAt; Vs; Bsum; Bsum-cong; Vs-cong; wsum)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Polynomial using (Poly; Σsub; sat; satᵐ; eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Properties using (Σsub-cong; Σsub-0; Σsub-+; i∣0)
open import PathSum.Reduction M using (½)
open import PathSum.Reorder using
  (front; frontᴾ; unfront; insertᵃ; insertᵃ-here; insertᵃ-punchIn;
   eval-front)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Layouts

record Layout (n m : ℕ) : Set where
  field
    st          : Fin n → State
    role        : Fin m → Role n
    loc         : Fin n → Kind → Maybe (Fin m)
    loc-role    : ∀ c → loc (proj₁ (role c)) (proj₂ (role c)) ≡ just c
    role-loc    : ∀ g b c → loc g b ≡ just c → role c ≡ (g , b)
    loc-present : ∀ g b → is-just (loc g b) ≡ present (st g) b

open Layout public

-- The value of an optional path variable: false when absent.

rd : (Fin m → Bool) → Maybe (Fin m) → Bool
rd y (just c) = y c
rd y nothing  = false

-- The gadgets' data at a point.

gads : Layout n m → (Fin (n + n) → Bool) → (Fin m → Bool) → Fin n → Gad
gads L x y g =
  gad (st L g) (x (xw g)) (x (aw g)) (rd y (loc L g U)) (rd y (loc L g V))

-- The outputs: x_g on wire x_g, gadget g's value on wire a_g.

outF : Layout n m → (Fin (n + n) → Bool) → (Fin m → Bool) →
       Fin (n + n) → Bool
outF {n = n} L x y w =
  [ (λ g → x (xw {n} g)) , Vs true (gads L x y) ]′ (splitAt n w)


------------------------------------------------------------------------
-- The invariant

record Inv (n : ℕ) {k m : ℕ} (ψ : PathSum (n + n) k m) : Set where
  field
    lay      : Layout n m
    k-eq     : k ≡ wsum (st lay)
    phase-ok : ∀ x y → eval (phase ψ) x y ≡ᴹ hb (Bsum true (gads lay x y))
    out-ok   : ∀ w x y → odd (eval (out ψ w) x y) ≡ outF lay x y w

open Inv public


------------------------------------------------------------------------
-- Equal gadget data, equal readings

-- Gadget environments equal pointwise have the same phase bit and
-- values.

module _ {G G′ : Fin n → Gad} (eq : ∀ h → G h ≡ G′ h) where

  Bsum-≗ : ∀ p → Bsum p G ≡ Bsum p G′
  Bsum-≗ = Bsum-cong G G′ (λ h q → cong (λ γ → step γ q) (eq h))
                          (λ h q → cong (λ γ → term γ q) (eq h))

  Vs-≗ : ∀ p g → Vs p G g ≡ Vs p G′ g
  Vs-≗ = Vs-cong G G′ (λ h q → cong (λ γ → step γ q) (eq h))

-- Two readings of the a wires' values that agree give the same
-- outputs.

outF-≗ : (L : Layout n m) (L′ : Layout n k) (x : Fin (n + n) → Bool)
         (y : Fin m → Bool) (y′ : Fin k → Bool) →
         (∀ g → Vs true (gads L x y) g ≡ Vs true (gads L′ x y′) g) →
         ∀ w → outF L x y w ≡ outF L′ x y′ w
outF-≗ {n = n} L L′ x y y′ h w = by (splitAt n w)
  where
  by : (s : Fin n ⊎ Fin n) →
       [ (λ g → x (xw {n} g)) , Vs true (gads L x y) ]′ s ≡
       [ (λ g → x (xw {n} g)) , Vs true (gads L′ x y′) ]′ s
  by (inj₁ g) = refl
  by (inj₂ g) = h g

-- Gadget data built from equal parts.

gad-≡ : ∀ {s x a u v u′ v′} → u ≡ u′ → v ≡ v′ →
        gad s x a u v ≡ gad s x a u′ v′
gad-≡ refl refl = refl


------------------------------------------------------------------------
-- The ladder satisfies it

private
  wsum-live : ∀ n → wsum {n} (λ _ → live) ≡ n + n
  wsum-live zero    = refl
  wsum-live (suc n) =
    cong suc (trans (cong suc (wsum-live n)) (sym (+-suc n n)))

-- Every gadget live; u_g and v_g are path variables g and n + g.

layout₀ : (n : ℕ) → Layout n (n + n)
layout₀ n = record
  { st          = λ _ → live
  ; role        = role₀
  ; loc         = loc₀
  ; loc-role    = loc-role₀
  ; role-loc    = role-loc₀
  ; loc-present = λ { g U → refl ; g V → refl }
  }
  where
  role₀ : Fin (n + n) → Role n
  role₀ c = [ (λ g → g , U) , (λ g → g , V) ]′ (splitAt n c)

  loc₀ : Fin n → Kind → Maybe (Fin (n + n))
  loc₀ g U = just (xw g)
  loc₀ g V = just (aw g)

  loc-role₀ : ∀ c → loc₀ (proj₁ (role₀ c)) (proj₂ (role₀ c)) ≡ just c
  loc-role₀ c with splitAt n c in eq
  ... | inj₁ g = cong just (splitAt⁻¹-↑ˡ eq)
  ... | inj₂ g = cong just (splitAt⁻¹-↑ʳ eq)

  role-loc₀ : ∀ g b c → loc₀ g b ≡ just c → role₀ c ≡ (g , b)
  role-loc₀ g U c refl =
    cong [ (λ g → g , U) , (λ g → g , V) ]′ (splitAt-↑ˡ n g n)
  role-loc₀ g V c refl =
    cong [ (λ g → g , U) , (λ g → g , V) ]′ (splitAt-↑ʳ n n g)

Inv-ξ : (n : ℕ) → Inv n (ξ n)
Inv-ξ n = record
  { lay      = layout₀ n
  ; k-eq     = sym (wsum-live n)
  ; phase-ok = eval-ξ-phase n
  ; out-ok   = odd-ξ-out n
  }


------------------------------------------------------------------------
-- Renumbering keeps it

-- front j lists y_j first: new position 0 is old j, new suc l is old
-- punchIn j l (π); unπ is the inverse.

π : Fin (suc m) → Fin (suc m) → Fin (suc m)
π j zero    = j
π j (suc l) = punchIn j l

private
  unπ′ : (j c : Fin (suc m)) → Dec (j ≡ c) → Fin (suc m)
  unπ′ j c (yes _)   = zero
  unπ′ j c (no j≢c) = suc (punchOut j≢c)

unπ : Fin (suc m) → Fin (suc m) → Fin (suc m)
unπ j c = unπ′ j c (j ≟ᶠ c)

π-unπ : (j c : Fin (suc m)) → π j (unπ j c) ≡ c
π-unπ j c = by (j ≟ᶠ c)
  where
  by : (d : Dec (j ≡ c)) → π j (unπ′ j c d) ≡ c
  by (yes j≡c) = j≡c
  by (no j≢c)  = punchIn-punchOut j≢c

unπ-π : (j c : Fin (suc m)) → unπ j (π j c) ≡ c
unπ-π j zero    = by (j ≟ᶠ j)
  where
  by : (d : Dec (j ≡ j)) → unπ′ j j d ≡ zero
  by (yes _) = refl
  by (no ¬p) = contradiction refl ¬p
unπ-π j (suc l) = by (j ≟ᶠ punchIn j l)
  where
  by : (d : Dec (j ≡ punchIn j l)) → unπ′ j (punchIn j l) d ≡ suc l
  by (yes e)  = contradiction (sym e) (punchInᵢ≢i j l)
  by (no j≢) = cong suc (trans (punchOut-cong j refl) (punchOut-punchIn j))

-- The original point a renumbered point stands for.

unfront-π : (j : Fin (suc m)) (y′ : Fin (suc m) → Bool) (c : Fin (suc m)) →
            unfront j y′ c ≡ y′ (unπ j c)
unfront-π j y′ c = by (j ≟ᶠ c)
  where
  b : Bool
  b = y′ zero

  g : Fin _ → Bool
  g i = y′ (suc i)

  by : (d : Dec (j ≡ c)) → insertᵃ j b g c ≡ y′ (unπ′ j c d)
  by (yes j≡c) = trans (cong (insertᵃ j b g) (sym j≡c)) (insertᵃ-here j b g)
  by (no j≢c)  = trans (cong (insertᵃ j b g) (sym (punchIn-punchOut j≢c)))
                       (insertᵃ-punchIn j b g (punchOut j≢c))

-- The renumbered layout.

frontL : Fin (suc m) → Layout n (suc m) → Layout n (suc m)
frontL {m = m} {n = n} j L = record
  { st          = st L
  ; role        = λ c → role L (π j c)
  ; loc         = loc′
  ; loc-role    = λ c → trans (cong (mapᴹ (unπ j)) (loc-role L (π j c)))
                              (cong just (unπ-π j c))
  ; role-loc    = λ g b c e → by-role g b c (loc L g b) refl e
  ; loc-present = λ g b → trans (is-just-map (loc L g b)) (loc-present L g b)
  }
  where
  loc′ : Fin n → Kind → Maybe (Fin (suc m))
  loc′ g b = mapᴹ (unπ j) (loc L g b)

  by-role : ∀ g b c (mc : Maybe (Fin (suc m))) → loc L g b ≡ mc →
            mapᴹ (unπ j) mc ≡ just c → role L (π j c) ≡ (g , b)
  by-role g b c (just c₀) e refl =
    trans (cong (role L) (π-unπ j c₀)) (role-loc L g b c₀ e)
  by-role g b c nothing   e ()

  is-just-map : (mc : Maybe (Fin (suc m))) →
                is-just (mapᴹ (unπ j) mc) ≡ is-just mc
  is-just-map (just _) = refl
  is-just-map nothing  = refl

-- Its readings are the original ones at the original point.

rd-front : (j : Fin (suc m)) (y′ : Fin (suc m) → Bool)
           (mc : Maybe (Fin (suc m))) →
           rd y′ (mapᴹ (unπ j) mc) ≡ rd (unfront j y′) mc
rd-front j y′ (just c) = sym (unfront-π j y′ c)
rd-front j y′ nothing  = refl

gads-front : (j : Fin (suc m)) (L : Layout n (suc m))
             (x : Fin (n + n) → Bool) (y′ : Fin (suc m) → Bool) →
             ∀ g → gads (frontL j L) x y′ g ≡ gads L x (unfront j y′) g
gads-front j L x y′ g =
  gad-≡ (rd-front j y′ (loc L g U)) (rd-front j y′ (loc L g V))

Inv-front : (j : Fin (suc m)) {ψ : PathSum (n + n) k (suc m)} →
            Inv n ψ → Inv n (front j ψ)
Inv-front {m = m} {n = n} j {ψ} I = record
  { lay      = frontL j L
  ; k-eq     = k-eq I
  ; phase-ok = λ x y′ → ≡ᴹ-trans
      (≡⇒≡ᴹ (eval-front j (phase ψ) x y′))
      (≡ᴹ-trans (phase-ok I x (unfront j y′))
        (≡⇒≡ᴹ (cong hb (sym (Bsum-≗ (gads-front j L x y′) true)))))
  ; out-ok   = λ w x y′ → trans
      (cong odd (eval-front j (out ψ w) x y′))
      (trans (out-ok I w x (unfront j y′))
        (outF-≗ L (frontL j L) x (unfront j y′) y′
          (λ g → sym (Vs-≗ (gads-front j L x y′) true g)) w))
  }
  where
  L : Layout n (suc m)
  L = lay I


------------------------------------------------------------------------
-- Reading the first path variable

-- The assignment with head b and tail y.

infixr 5 _◂_

_◂_ : Bool → (Fin m → Bool) → Fin (suc m) → Bool
(b ◂ y) zero    = b
(b ◂ y) (suc i) = y i

-- With y₀ false, the terms containing it vanish; with y₀ true, they
-- add the quotient.  (PathSum.Denotation.eval-false, eval-true.)

eval-false : (P : Poly n (suc m)) (x : Fin n → Bool) (y : Fin m → Bool) →
             eval P x (false ◂ y) ≡ eval (tail-part P) x y
eval-false {n = n} {m = m} P x y = Σsub-cong (λ α →
  trans (cong (_+ℤ tailSum α) (trans (Σsub-cong (inner α)) (Σsub-0 {m})))
        (+-identityˡ (tailSum α)))
  where
  tailSum : Subset n → ℤ
  tailSum α =
    Σsub (λ β → if satᵐ (α , β) x y then tail-part P (α , β) else 0ℤ)

  inner : ∀ (α : Subset n) (β : Subset m) →
          (if (sat α x ∧ false) then P (α , inside ∷ β) else 0ℤ) ≡ 0ℤ
  inner α β = cong (λ c → if c then P (α , inside ∷ β) else 0ℤ)
                   (∧-zeroʳ (sat α x))

eval-true : (P : Poly n (suc m)) (x : Fin n → Bool) (y : Fin m → Bool) →
            eval P x (true ◂ y) ≡
            eval (head-part P) x y +ℤ eval (tail-part P) x y
eval-true {n = n} {m = m} P x y = Σsub-+ headSum tailSum
  where
  headSum tailSum : Subset n → ℤ
  headSum α =
    Σsub (λ β → if satᵐ (α , β) x y then head-part P (α , β) else 0ℤ)
  tailSum α =
    Σsub (λ β → if satᵐ (α , β) x y then tail-part P (α , β) else 0ℤ)

-- The quotient by y₀ is the difference of the two values.

eval-head : (P : Poly n (suc m)) (x : Fin n → Bool) (y : Fin m → Bool) →
            eval (head-part P) x y ≡
            eval P x (true ◂ y) -ℤ eval P x (false ◂ y)
eval-head P x y = sym (trans
  (cong₂ _-ℤ_ (eval-true P x y) (eval-false P x y))
  (shape (eval (head-part P) x y) (eval (tail-part P) x y)))
  where
  shape : ∀ h t → (h +ℤ t) -ℤ t ≡ h
  shape = solve 2 (λ h t → (h :+ t) :- t := h) refl


------------------------------------------------------------------------
-- Removing the first path variable

pred : Fin (suc m) → Maybe (Fin m)
pred zero    = nothing
pred (suc l) = just l

private
  pred-just : (mc : Maybe (Fin (suc m))) (l : Fin m) →
              (mc >>= pred) ≡ just l → mc ≡ just (suc l)
  pred-just (just (suc l)) l refl = refl
  pred-just (just zero)    l ()
  pred-just nothing        l ()

-- The layout left when the first path variable goes, with new states
-- st′ that differ from the old ones only in that its role is no
-- longer present.

drop0 : (L : Layout n (suc m)) (st′ : Fin n → State) →
        (∀ h b → loc L h b ≢ just zero →
                 present (st′ h) b ≡ present (st L h) b) →
        present (st′ (proj₁ (role L zero))) (proj₂ (role L zero)) ≡ false →
        Layout n m
drop0 {n = n} {m = m} L st′ keep gone = record
  { st          = st′
  ; role        = λ l → role L (suc l)
  ; loc         = λ h b → loc L h b >>= pred
  ; loc-role    = λ l → cong (_>>= pred) (loc-role L (suc l))
  ; role-loc    = λ h b l e → role-loc L h b (suc l) (pred-just (loc L h b) l e)
  ; loc-present = λ h b → by h b (loc L h b) refl
  }
  where
  by : ∀ h b (mc : Maybe (Fin (suc m))) → loc L h b ≡ mc →
       is-just (mc >>= pred) ≡ present (st′ h) b
  by h b (just zero) e = sym (subst (λ r → present (st′ (proj₁ r)) (proj₂ r)
                                            ≡ false)
                                     (role-loc L h b zero e) gone)
  by h b (just (suc l)) e = trans (sym (cong is-just e))
    (trans (loc-present L h b) (sym (keep h b (λ e′ → suc≢zero (trans (sym e) e′)))))
    where
    suc≢zero : ¬ (just (suc l) ≡ just zero)
    suc≢zero ()
  by h b nothing e = trans (sym (cong is-just e))
    (trans (loc-present L h b) (sym (keep h b (λ e′ → nothing≢ (trans (sym e) e′)))))
    where
    nothing≢ : ¬ (nothing ≡ just zero)
    nothing≢ ()

-- Off the first variable's role, reading at c ◂ y is reading the
-- dropped layout at y.

rd-drop : (y : Fin m → Bool) (c : Bool) (mc : Maybe (Fin (suc m))) →
          mc ≢ just zero → rd (c ◂ y) mc ≡ rd y (mc >>= pred)
rd-drop y c (just zero)    ne = contradiction refl ne
rd-drop y c (just (suc l)) ne = refl
rd-drop y c nothing        ne = refl


------------------------------------------------------------------------
-- The phase takes values in ½ℤ

-- ½ divides 2^M.

½∣2^M : ½ ∣ pow M
½∣2^M = divides (+ 2) (trans (pow-suc (ℕ.suc (ℕ.suc M₀))) (*-comm ½ (+ 2)))

-- Every value of the phase is a multiple of ½ (2^(M-1)), modulo 2^M
-- hence exactly.

half-valued : {ψ : PathSum (n + n) k m} → Inv n ψ →
              ∀ x y → ½ ∣ eval (phase ψ) x y
half-valued {ψ = ψ} I x y = subst (½ ∣_) (shape e h)
  (∣m∣n⇒∣m+n (∣-trans ½∣2^M (≡ᴹ⇒∣ (phase-ok I x y))) (½∣hb b))
  where
  b : Bool
  b = Bsum true (gads (lay I) x y)

  e h : ℤ
  e = eval (phase ψ) x y
  h = hb b

  shape : ∀ e h → (e -ℤ h) +ℤ h ≡ e
  shape = solve 2 (λ e h → (e :- h) :+ h := e) refl

  ½∣hb : ∀ c → ½ ∣ hb c
  ½∣hb true  = divides (+ 1) (sym (*-identityˡ ½))
  ½∣hb false = i∣0

