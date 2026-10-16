------------------------------------------------------------------------
-- Presentations of groups
--
-- Affine circuits as words, and the fan-out calculus
--
-- The affine decoding from five wires on (scratchpad/five-qubit-plan.md)
-- conjugates one fixed gate G by affine circuits, words of X on a wire
-- and CX from a wire onto another.  Their combinatorics is done here,
-- once, over an alphabet of its own (`Lt`) and the relations below — each
-- on at most four wires and true of the matrices, so that the
-- interpretation into circuits (Affine.Circuits) is a placed evaluation
-- per relation — and carried to circuits by that interpretation.
--
-- The width is 1 + n; wire 0 is the target of G.  The fan-out `fan w ι`
-- is CX from wire 0 onto every wire 1 + ι k with the bit k of w set:
-- its letters commute (`pass0`), toggling a bit multiplies by one letter
-- (`fan-toggle`), and a CX passes it as the matrices say: unchanged when
-- its control is off the fan and off wire 0 (`fan-com`), picking up
-- CX(0 → v) when its control is on the fan (`fan-in`), and, onto wire
-- 0 from a wire off the fan, picking up CX from its control onto the
-- whole fan (`fan-0`, with `gan`); two CX onto wire 0 from wires on the
-- fan exchange their controls (`pivot`, from the three-wire t-pv).
-- Every CX left behind has its control off wire 0: those commute with
-- G (scratchpad/five/affine.py checks every case numerically).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Affine.Theory (n : ℕ) where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (suc)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Properties using (_≟_) renaming (suc-injective to sF-inj)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford+CS.Tools using (module Tools)

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- Letters

Wire : Set
Wire = Fin (₁₊ n)

data Lt : Set where
  xL : Wire → Lt
  tL : (u v : Wire) → .(u ≢ v) → Lt

X : Wire → Word Lt
X v = [ xL v ]ʷ

-- CX from u onto v.
T : (u v : Wire) → .(u ≢ v) → Word Lt
T u v p = [ tL u v p ]ʷ

-- The exchange of two wires.
SW : (u v : Wire) → .(u ≢ v) → Word Lt
SW u v p = T u v p • T v u (λ e → p (Eq.sym e)) • T u v p

------------------------------------------------------------------------
-- Relations

infix 4 _===_
data _===_ : WRel Lt where
  t-sq  : ∀ {u v} .{p} → T u v p • T u v p === ε
  t-cc  : ∀ {u v w} .{p q} → .(v ≢ w) → T u v p • T u w q === T u w q • T u v p
  t-tt  : ∀ {u v w} .{p q} → .(u ≢ v) → T u w p • T v w q === T v w q • T u w p
  t-dd  : ∀ {a b c d} .{p q} → .(a ≢ c) → .(a ≢ d) → .(b ≢ c) → .(b ≢ d) →
          T a b p • T c d q === T c d q • T a b p
  t-ts  : ∀ {x y z} .{p q r} → T x y p • T y z q • T x y p === T y z q • T x z r
  t-st  : ∀ {x y z} .{p q r} → T y z q • T x y p • T y z q === T x y p • T x z r
  t-sw  : ∀ {u v} .{p q} → T u v p • T v u q • T u v p === T v u q • T u v p • T v u q
  t-pv  : ∀ {o u j} .{a b c d e} →
          T j o a • T u o b • T o u c • T o j d === T o u c • T o j d • SW u j e • T u o b • T j o a
  x-sq  : ∀ {v} → X v • X v === ε
  x-xx  : ∀ {v w} → X v • X w === X w • X v
  x-ctl : ∀ {u v} .{p} → T u v p • X u === X u • X v • T u v p
  x-tgt : ∀ {u v} .{p} → T u v p • X v === X v • T u v p
  x-far : ∀ {u v w} .{p} → .(w ≢ u) → .(w ≢ v) → T u v p • X w === X w • T u v p

open Tools _===_ public

------------------------------------------------------------------------
-- Inverses: the reversed word

rev : Word Lt → Word Lt
rev [ a ]ʷ  = [ a ]ʷ
rev ε       = ε
rev (u • v) = rev v • rev u

letter² : ∀ (a : Lt) → [ a ]ʷ • [ a ]ʷ ≈ ε
letter² (xL v)     = axiom x-sq
letter² (tL u v p) = axiom t-sq

rev-inv : ∀ (w : Word Lt) → w • rev w ≈ ε
rev-inv [ a ]ʷ  = letter² a
rev-inv ε       = left-unit
rev-inv (u • v) = begin
  (u • v) • (rev v • rev u)     ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  u • (v • rev v) • rev u       ≈⟨ back u (front (rev u) (rev-inv v)) ⟩
  u • ε • rev u                 ≈⟨ back u left-unit ⟩
  u • rev u                     ≈⟨ rev-inv u ⟩
  ε ∎

------------------------------------------------------------------------
-- Toggling a bit

toggle : Vec Bool k → Fin k → Vec Bool k
toggle (b ∷ w) 0F     = not b ∷ w
toggle (b ∷ w) (sF i) = b ∷ toggle w i

lookup-toggle : ∀ (w : Vec Bool k) (i : Fin k) → lookup (toggle w i) i ≡ not (lookup w i)
lookup-toggle (b ∷ w) 0F     = Eq.refl
lookup-toggle (b ∷ w) (sF i) = lookup-toggle w i

lookup-toggle′ : ∀ (w : Vec Bool k) (i j : Fin k) → j ≢ i → lookup (toggle w i) j ≡ lookup w j
lookup-toggle′ (b ∷ w) 0F     0F     ne = ⊥-elim (ne Eq.refl)
lookup-toggle′ (b ∷ w) 0F     (sF j) ne = Eq.refl
lookup-toggle′ (b ∷ w) (sF i) 0F     ne = Eq.refl
lookup-toggle′ (b ∷ w) (sF i) (sF j) ne = lookup-toggle′ w i j (λ e → ne (Eq.cong sF e))

------------------------------------------------------------------------
-- The fan-out from wire 0

0≢s : ∀ {i : Fin n} → _≢_ {A = Wire} 0F (sF i)
0≢s ()

s≢0 : ∀ {i : Fin n} → _≢_ {A = Wire} (sF i) 0F
s≢0 ()

s≢s : ∀ {i j : Fin n} → i ≢ j → _≢_ {A = Wire} (sF i) (sF j)
s≢s ne e = ne (sF-inj e)

-- CX from wire 0 onto 1 + x.
T0 : Fin n → Word Lt
T0 x = T 0F (sF x) 0≢s

fan : Vec Bool k → (Fin k → Fin n) → Word Lt
fan []          ι = ε
fan (true  ∷ w) ι = T0 (ι 0F) • fan w (λ i → ι (sF i))
fan (false ∷ w) ι = fan w (λ i → ι (sF i))

comm00 : ∀ (x y : Fin n) → T0 x • T0 y ≈ T0 y • T0 x
comm00 x y with x ≟ y
... | yes Eq.refl = refl
... | no ne       = axiom (t-cc (s≢s ne))

-- The letters of a fan commute.
pass0 : ∀ (x : Fin n) (w : Vec Bool k) (ι : Fin k → Fin n) → T0 x • fan w ι ≈ fan w ι • T0 x
pass0 x []          ι = trans right-unit (sym left-unit)
pass0 x (true  ∷ w) ι = begin
  T0 x • (T0 (ι 0F) • fan w ι′)   ≈⟨ sym assoc ⟩
  (T0 x • T0 (ι 0F)) • fan w ι′   ≈⟨ front _ (comm00 x (ι 0F)) ⟩
  (T0 (ι 0F) • T0 x) • fan w ι′   ≈⟨ assoc ⟩
  T0 (ι 0F) • (T0 x • fan w ι′)   ≈⟨ back _ (pass0 x w ι′) ⟩
  T0 (ι 0F) • (fan w ι′ • T0 x)   ≈⟨ sym assoc ⟩
  (T0 (ι 0F) • fan w ι′) • T0 x ∎
  where ι′ = λ i → ι (sF i)
pass0 x (false ∷ w) ι = pass0 x w (λ i → ι (sF i))

-- Toggling a bit multiplies by its letter.
fan-toggle : ∀ (w : Vec Bool k) (ι : Fin k → Fin n) (j : Fin k) →
             fan (toggle w j) ι ≈ fan w ι • T0 (ι j)
fan-toggle (true ∷ w) ι 0F = sym (begin
  (T0 a • fan w ι′) • T0 a      ≈⟨ assoc ⟩
  T0 a • (fan w ι′ • T0 a)      ≈⟨ back _ (sym (pass0 a w ι′)) ⟩
  T0 a • (T0 a • fan w ι′)      ≈⟨ cancelˡ _ (axiom t-sq) ⟩
  fan w ι′ ∎)
  where
  a = ι 0F
  ι′ = λ i → ι (sF i)
fan-toggle (false ∷ w) ι 0F = pass0 (ι 0F) w (λ i → ι (sF i))
fan-toggle (true ∷ w) ι (sF j) = begin
  T0 (ι 0F) • fan (toggle w j) ι′      ≈⟨ back _ (fan-toggle w ι′ j) ⟩
  T0 (ι 0F) • (fan w ι′ • T0 (ι′ j))   ≈⟨ sym assoc ⟩
  (T0 (ι 0F) • fan w ι′) • T0 (ι′ j) ∎
  where ι′ = λ i → ι (sF i)
fan-toggle (false ∷ w) ι (sF j) = fan-toggle w (λ i → ι (sF i)) j

-- A fan with two bits cleared, the two letters in front.
fan-pull₂ : ∀ (w : Vec Bool k) (ι : Fin k → Fin n) (i j : Fin k) →
            fan w ι ≈ T0 (ι j) • T0 (ι i) • fan (toggle (toggle w i) j) ι
fan-pull₂ w ι i j = begin
  fan w ι
    ≈⟨ sym right-unit ⟩
  fan w ι • ε
    ≈⟨ back _ (sym (axiom t-sq)) ⟩
  fan w ι • (T0 (ι i) • T0 (ι i))
    ≈⟨ back _ (back _ (sym left-unit)) ⟩
  fan w ι • (T0 (ι i) • ε • T0 (ι i))
    ≈⟨ back _ (back _ (front _ (sym (axiom t-sq)))) ⟩
  fan w ι • (T0 (ι i) • (T0 (ι j) • T0 (ι j)) • T0 (ι i))
    ≈⟨ by-passoc (□ • (□ • (□ • □) • □)) (((□ • □) • □) • (□ • □)) Eq.refl ⟩
  ((fan w ι • T0 (ι i)) • T0 (ι j)) • (T0 (ι j) • T0 (ι i))
    ≈⟨ front _ (trans (front _ (sym (fan-toggle w ι i))) (sym (fan-toggle (toggle w i) ι j))) ⟩
  F° • (T0 (ι j) • T0 (ι i))
    ≈⟨ sym assoc ⟩
  (F° • T0 (ι j)) • T0 (ι i)
    ≈⟨ front _ (sym (pass0 (ι j) (toggle (toggle w i) j) ι)) ⟩
  (T0 (ι j) • F°) • T0 (ι i)
    ≈⟨ assoc ⟩
  T0 (ι j) • (F° • T0 (ι i))
    ≈⟨ back _ (sym (pass0 (ι i) (toggle (toggle w i) j) ι)) ⟩
  T0 (ι j) • T0 (ι i) • F° ∎
  where F° = fan (toggle (toggle w i) j) ι

------------------------------------------------------------------------
-- CX passing a fan

private
  -- CX between two wires off wire 0 against a fan letter off its control.
  c0 : ∀ (u v a : Fin n) .(p : _≢_ {A = Wire} (sF u) (sF v)) → a ≢ u →
       T (sF u) (sF v) p • T0 a ≈ T0 a • T (sF u) (sF v) p
  c0 u v a p au with a ≟ v
  ... | yes Eq.refl = axiom (t-tt s≢0)
  ... | no av       = axiom (t-dd s≢0 (s≢s λ e → au (Eq.sym e)) s≢0 (s≢s λ e → av (Eq.sym e)))

-- Control and target off wire 0, control off the fan.
fan-com : ∀ (u v : Fin n) .(p : _≢_ {A = Wire} (sF u) (sF v)) (w : Vec Bool k) (ι : Fin k → Fin n) →
          (∀ i → lookup w i ≡ true → ι i ≢ u) →
          T (sF u) (sF v) p • fan w ι ≈ fan w ι • T (sF u) (sF v) p
fan-com u v p []          ι h = trans right-unit (sym left-unit)
fan-com u v p (true  ∷ w) ι h = begin
  T′ • (T0 (ι 0F) • fan w ι′)   ≈⟨ sym assoc ⟩
  (T′ • T0 (ι 0F)) • fan w ι′   ≈⟨ front _ (c0 u v (ι 0F) p (h 0F Eq.refl)) ⟩
  (T0 (ι 0F) • T′) • fan w ι′   ≈⟨ assoc ⟩
  T0 (ι 0F) • (T′ • fan w ι′)   ≈⟨ back _ (fan-com u v p w ι′ (λ i → h (sF i))) ⟩
  T0 (ι 0F) • (fan w ι′ • T′)   ≈⟨ sym assoc ⟩
  (T0 (ι 0F) • fan w ι′) • T′ ∎
  where
  T′ = T (sF u) (sF v) p
  ι′ = λ i → ι (sF i)
fan-com u v p (false ∷ w) ι h = fan-com u v p w (λ i → ι (sF i)) (λ i → h (sF i))

Injective : (Fin k → Fin n) → Set
Injective ι = ∀ {i j} → ι i ≡ ι j → i ≡ j

private
  inj-sF : ∀ {ι : Fin (suc k) → Fin n} → Injective ι → Injective (λ i → ι (sF i))
  inj-sF inj e = sF-inj (inj e)

-- Control on the fan, target off wire 0 and the control.
fan-in : ∀ (w : Vec Bool k) (ι : Fin k → Fin n) → Injective ι → (i₀ : Fin k) → lookup w i₀ ≡ true →
         ∀ (v : Fin n) .(p : _≢_ {A = Wire} (sF (ι i₀)) (sF v)) →
         T (sF (ι i₀)) (sF v) p • fan w ι ≈ fan w ι • T0 v • T (sF (ι i₀)) (sF v) p
fan-in (true ∷ w) ι inj 0F b v p = begin
  T′ • (T0 u • fan w ι′)
    ≈⟨ sym assoc ⟩
  (T′ • T0 u) • fan w ι′
    ≈⟨ front _ (moveˡ (axiom t-sq) (axiom t-ts)) ⟩
  (T0 u • T′ • T0 v) • fan w ι′
    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
  T0 u • T′ • (T0 v • fan w ι′)
    ≈⟨ back _ (back _ (pass0 v w ι′)) ⟩
  T0 u • T′ • (fan w ι′ • T0 v)
    ≈⟨ back _ (sym assoc) ⟩
  T0 u • (T′ • fan w ι′) • T0 v
    ≈⟨ back _ (front _ (fan-com (ι 0F) v p w ι′ off)) ⟩
  T0 u • (fan w ι′ • T′) • T0 v
    ≈⟨ back _ (trans assoc (back _ (axiom (t-tt s≢0)))) ⟩
  T0 u • fan w ι′ • (T0 v • T′)
    ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • □) • □ • □) Eq.refl ⟩
  (T0 u • fan w ι′) • T0 v • T′ ∎
  where
  u = ι 0F
  ι′ = λ i → ι (sF i)
  T′ = T (sF u) (sF v) p
  off : ∀ i → lookup w i ≡ true → ι′ i ≢ ι 0F
  off i _ e with inj e
  ... | ()
fan-in (false ∷ w) ι inj 0F () v p
fan-in (true ∷ w) ι inj (sF i₀) b v p = begin
  T′ • (T0 a • fan w ι′)
    ≈⟨ sym assoc ⟩
  (T′ • T0 a) • fan w ι′
    ≈⟨ front _ (c0 (ι (sF i₀)) v a p a≢) ⟩
  (T0 a • T′) • fan w ι′
    ≈⟨ assoc ⟩
  T0 a • (T′ • fan w ι′)
    ≈⟨ back _ (fan-in w ι′ (inj-sF {ι = ι} inj) i₀ b v p) ⟩
  T0 a • (fan w ι′ • T0 v • T′)
    ≈⟨ sym assoc ⟩
  (T0 a • fan w ι′) • T0 v • T′ ∎
  where
  a = ι 0F
  ι′ = λ i → ι (sF i)
  T′ = T (sF (ι (sF i₀))) (sF v) p
  a≢ : a ≢ ι (sF i₀)
  a≢ e with inj e
  ... | ()
fan-in (false ∷ w) ι inj (sF i₀) b v p = fan-in w (λ i → ι (sF i)) (inj-sF {ι = ι} inj) i₀ b v p

-- CX from u onto every wire of the fan (u off the fan).
gan : (u : Fin n) (w : Vec Bool k) (ι : Fin k → Fin n) → .(∀ i → lookup w i ≡ true → ι i ≢ u) → Word Lt
gan u []          ι h = ε
gan u (true  ∷ w) ι h = T (sF u) (sF (ι 0F)) (s≢s (λ e → h 0F Eq.refl (Eq.sym e))) • gan u w (λ i → ι (sF i)) (λ i → h (sF i))
gan u (false ∷ w) ι h = gan u w (λ i → ι (sF i)) (λ i → h (sF i))

-- Its letters commute with one more CX from u.
private
  gan-pass : ∀ (u x : Fin n) .(q : _≢_ {A = Wire} (sF u) (sF x)) (w : Vec Bool k) (ι : Fin k → Fin n) →
             .(h : ∀ i → lookup w i ≡ true → ι i ≢ u) →
             T (sF u) (sF x) q • gan u w ι h ≈ gan u w ι h • T (sF u) (sF x) q
  gan-pass u x q []          ι h = trans right-unit (sym left-unit)
  gan-pass u x q (true  ∷ w) ι h = begin
    T′ • (Tg • G)   ≈⟨ sym assoc ⟩
    (T′ • Tg) • G   ≈⟨ front _ (cc x (ι 0F)) ⟩
    (Tg • T′) • G   ≈⟨ assoc ⟩
    Tg • (T′ • G)   ≈⟨ back _ (gan-pass u x q w (λ i → ι (sF i)) (λ i → h (sF i))) ⟩
    Tg • (G • T′)   ≈⟨ sym assoc ⟩
    (Tg • G) • T′ ∎
    where
    G = gan u w (λ i → ι (sF i)) (λ i → h (sF i))
    T′ = T (sF u) (sF x) q
    Tg = T (sF u) (sF (ι 0F)) (s≢s (λ e → h 0F Eq.refl (Eq.sym e)))
    cc : ∀ (a b : Fin n) .{p : _≢_ {A = Wire} (sF u) (sF a)} .{q : _≢_ {A = Wire} (sF u) (sF b)} →
         T (sF u) (sF a) p • T (sF u) (sF b) q ≈ T (sF u) (sF b) q • T (sF u) (sF a) p
    cc a b with a ≟ b
    ... | yes Eq.refl = refl
    ... | no ne       = axiom (t-cc (s≢s ne))
  gan-pass u x q (false ∷ w) ι h = gan-pass u x q w (λ i → ι (sF i)) (λ i → h (sF i))

-- CX onto wire 0 from a wire off the fan.
fan-0 : ∀ (u : Fin n) .(p : _≢_ {A = Wire} (sF u) 0F) (w : Vec Bool k) (ι : Fin k → Fin n) →
        (h : ∀ i → lookup w i ≡ true → ι i ≢ u) →
        T (sF u) 0F p • fan w ι ≈ fan w ι • T (sF u) 0F p • gan u w ι h
fan-0 u p []          ι h = trans right-unit (sym (trans (back _ right-unit) left-unit))
fan-0 u p (true  ∷ w) ι h = begin
  Tu • (T0 a • fan w ι′)
    ≈⟨ sym assoc ⟩
  (Tu • T0 a) • fan w ι′
    ≈⟨ front _ (moveˡ (axiom t-sq) (axiom t-st)) ⟩
  (T0 a • Tu • Tg) • fan w ι′
    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
  T0 a • Tu • (Tg • fan w ι′)
    ≈⟨ back _ (back _ (fan-com u a qa w ι′ h′)) ⟩
  T0 a • Tu • (fan w ι′ • Tg)
    ≈⟨ back _ (sym assoc) ⟩
  T0 a • (Tu • fan w ι′) • Tg
    ≈⟨ back _ (front _ (fan-0 u p w ι′ h′)) ⟩
  T0 a • (fan w ι′ • Tu • gan u w ι′ h′) • Tg
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
  (T0 a • fan w ι′) • Tu • (gan u w ι′ h′ • Tg)
    ≈⟨ back _ (back _ (sym (gan-pass u a qa w ι′ h′))) ⟩
  (T0 a • fan w ι′) • Tu • (Tg • gan u w ι′ h′) ∎
  where
  a = ι 0F
  ι′ = λ i → ι (sF i)
  h′ : ∀ i → lookup w i ≡ true → ι′ i ≢ u
  h′ = λ i → h (sF i)
  Tu = T (sF u) 0F p
  qa : _≢_ {A = Wire} (sF u) (sF a)
  qa = s≢s (λ e → h 0F Eq.refl (Eq.sym e))
  Tg = T (sF u) (sF a) qa
fan-0 u p (false ∷ w) ι h = fan-0 u p w (λ i → ι (sF i)) (λ i → h (sF i))
