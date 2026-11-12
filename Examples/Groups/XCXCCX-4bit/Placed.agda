------------------------------------------------------------------------
-- Presentations of groups
--
-- Placed gates on four wires: X, CX and CCX on any wires
--
-- PG is the alphabet of the theory's gates placed on any wires of a
-- four-wire circuit, with black controls (a white control is X on its
-- wire on either side).  Wire 0 is the bottom wire:
--
--   Xᵖ t          X on wire t;
--   CXᵖ c t       CX with control c and target t (c ≠ t);
--   CCXᵖ a b t    CCX with controls a < b and target t, all distinct.
--
-- Wires are elements of Fin 4, written with the numerals ₀ ₁ ₂ ₃ of
-- Notations, and a side condition is an irrelevant hidden argument
-- T b for a boolean b, which a closed letter fills by eta: a script
-- writes CCXᵖ ₁ ₃ ₀, and a letter with two equal wires or its
-- controls out of order does not typecheck.
--
-- ι places a letter by conjugation with a swap network: its gate on the
-- bottom wires (target on wire 0, controls on wires 1 and 2) between
-- the circuit of a Coxeter word of S₄ that sends 0, 1, 2 to the target
-- and the controls (Coxeter's frame) and its inverse.  The swaps sw d
-- of wires d and d + 1 satisfy the Coxeter relations (σ-inv,
-- Yang–Baxter, comm₂: cox), so by the frame lemma the placement
-- depends only on where the word sends those wires (ι-X, ι-CX, ι-CCX;
-- for CCX also with its controls exchanged, by rule (5): ι-CCX′).  So:
--
-- * a gate shifted k wires up is its placement by the k-th power of
--   the cycle 0 → 1 → 2 → 3 (shift, from naturality), and the letters
--   on consecutive wires are the gates of Syntactics shifted up (ιX₀,
--   …, ιCCX₂₃₁, and ιCCX₂₃₀ for CCX₃₂₀);
-- * a relabelling of the wires (Relabel: a permutation π with a
--   Coxeter word whose network S carries it out; ρ4 a b c d sends the
--   wires 0, 1, 2, 3 to a, b, c, d, fromPerm takes any injective map)
--   is conjugation by its network, ι (relabel R g) ≈ S R • ι g • S⁻ R
--   (relabel-ι, for every letter at once; relabel-ι* on words);
-- * letters on disjoint wires commute (disj-comm): one network places
--   both, the one as a gate on the bottom wires and the other as a
--   gate shifted above it, which the structural comm rules exchange.
--
-- ⟦_⟧ᵖ is the function of a letter on bit vectors; ⟦ ι g ⟧ ≐ ⟦ g ⟧ᵖ is
-- decided by evaluation, once for all 28 letters (sem-ok).  Rule (7)
-- holds for the placed letters under every relabelling (rule7).  Given
-- completeness on three wires (Narrow's parameter; Narrow3 applies it
-- to Width3.complete₃), two words of letters on three of the four
-- wires with the same function are equal (narrow): relabelled by the
-- transposition τ m so that the idle wire m is wire 3, their circuits
-- are three-wire circuits widened (low-ι*), and pad₃ carries the
-- three-wire derivation back.  A triple of wires is given by the wire
-- m it leaves out.
--
-- Words of letters are lists, in diagram order: ι* (g ∷ u) = ι g • ι* u.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.Placed where

open import Data.Bool.Base using (Bool ; true ; false ; T ; not ; _∧_ ; _∨_ ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Empty.Irrelevant as Irr
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _≤_ ; _<_ ; s≤s ; _≡ᵇ_ ; _<ᵇ_ ; _≤ᵇ_)
import Data.Nat.Properties as ℕP
open import Data.Unit.Base using (tt)
import Data.Vec.Base as V
import Data.Vec.Properties as VP
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary.Decidable.Core using (recompute ; T?)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
open import Presentation.Tactics.Words using (module Associative)
open Associative using (word-of-list)

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

import Examples.Groups.Symmetric.Syntactics as Sym
open import Examples.Groups.Symmetric.CoxeterFrames using (Avoid ; Distinct ; [] ; _∷_)
open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics
  using (Bits ; Fun ; _≐_ ; ≐-refl ; ≐-sym ; ≐-trans ; _⨾_ ; ⨾-cong ; ⟦_⟧ᵍ ; ⟦_⟧ ; eqF ; eqF-sound ; sound)
import Examples.Groups.XCXCCX-4bit.Coxeter as Cox
open Cox 4 using (SG ; CW ; act ; inv ; act-inv ; frame ; frame-act ; _‼_)
import Examples.Independence.Reasoning Gate as R
open R.Theory _SRel,_===_ using (ax-at)

open PB (4 VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)
open SR (PP.word-setoid (4 VRel,_===_))

------------------------------------------------------------------------
-- Booleans

private
  ∧ˡ : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧ˡ {true} _ = Eq.refl

  ∧ʳ : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧ʳ {true} h = h

  T-∧₁ : ∀ a {b} → T (a ∧ b) → T a
  T-∧₁ true _ = tt

  T-∧₂ : ∀ a {b} → T (a ∧ b) → T b
  T-∧₂ true p = p

  T-∧ : ∀ a {b} → T a → T b → T (a ∧ b)
  T-∧ true _ q = q

  T-not : ∀ b → T b → T (not b) → ⊥
  T-not true _ ()

  not-T : ∀ b → (T b → ⊥) → T (not b)
  not-T true  f = f tt
  not-T false f = tt

  T→≡ : ∀ {b} → T b → b ≡ true
  T→≡ {true} _ = Eq.refl

  ≡→T : ∀ {b} → b ≡ true → T b
  ≡→T Eq.refl = tt

  imp : ∀ a {b} → not a ∨ b ≡ true → a ≡ true → b ≡ true
  imp true h _ = h

  ∧-swap : ∀ a b c → a ∧ (b ∧ c) ≡ b ∧ (a ∧ c)
  ∧-swap true  b c = Eq.refl
  ∧-swap false true  c = Eq.refl
  ∧-swap false false c = Eq.refl

------------------------------------------------------------------------
-- Wires

Wire : Set
Wire = Fin 4

infix 4 _==_ _<<_
_==_ : Wire → Wire → Bool
a == b = toℕ a ≡ᵇ toℕ b

_<<_ : Wire → Wire → Bool
a << b = toℕ a <ᵇ toℕ b

==-sound : (a b : Wire) → T (a == b) → a ≡ b
==-sound a b h = FinP.toℕ-injective (ℕP.≡ᵇ⇒≡ (toℕ a) (toℕ b) h)

==-refl : (a : Wire) → T (a == a)
==-refl a = ℕP.≡⇒≡ᵇ (toℕ a) (toℕ a) Eq.refl

-- Distinct wires, from an irrelevant boolean test.
neq : (a b : Wire) → .(T (not (a == b))) → a ≢ b
neq a b p e = Irr.⊥-elim (T-not (a == b) (Eq.subst (λ z → T (a == z)) e (==-refl a)) p)

<<-neq : (a b : Wire) → .(T (a << b)) → a ≢ b
<<-neq a b p e = Irr.⊥-elim (ℕP.n≮n (toℕ a)
  (Eq.subst (λ z → toℕ a < toℕ z) (Eq.sym e) (ℕP.<ᵇ⇒< (toℕ a) (toℕ b) p)))

-- Of two distinct wires not in order, the other way round.
<<-flip : (a b : Wire) → a ≢ b → (a << b) ≡ false → T (b << a)
<<-flip a b a≢b e = ℕP.<⇒<ᵇ (ℕP.≤∧≢⇒< (ℕP.≮⇒≥ λ lt → Eq.subst T e (ℕP.<⇒<ᵇ lt))
                                     (λ eq → a≢b (FinP.toℕ-injective (Eq.sym eq))))

------------------------------------------------------------------------
-- Placed gates

okCX : Wire → Wire → Bool
okCX c t = not (c == t)

okCCX : Wire → Wire → Wire → Bool
okCCX a b t = (a << b) ∧ (not (a == t) ∧ not (b == t))

data PG : Set where
  Xᵖ   : (t : Wire) → PG
  CXᵖ  : (c t : Wire) → .{ok : T (okCX c t)} → PG
  CCXᵖ : (a b t : Wire) → .{ok : T (okCCX a b t)} → PG

-- The gate of a letter on the bottom wires, and its wires: the target
-- first, then the controls.
base : PG → Circuit 4
base (Xᵖ _)       = X
base (CXᵖ _ _)    = CX
base (CCXᵖ _ _ _) = CCX

arity : PG → ℕ
arity (Xᵖ _)       = 1
arity (CXᵖ _ _)    = 2
arity (CCXᵖ _ _ _) = 3

wires : PG → List Wire
wires (Xᵖ t)       = t ∷ []
wires (CXᵖ c t)    = t ∷ c ∷ []
wires (CCXᵖ a b t) = t ∷ a ∷ b ∷ []

-- The wires of a letter are distinct.
dX : (t : Wire) → Distinct (t ∷ [])
dX t = [] ∷ []

dCX : (c t : Wire) → .(T (okCX c t)) → Distinct (t ∷ c ∷ [])
dCX c t p = ((λ e → neq c t p (Eq.sym e)) ∷ []) ∷ ([] ∷ [])

-- The three side conditions of CCXᵖ.
ok-ab : (a b t : Wire) → T (okCCX a b t) → T (a << b)
ok-ab a b t p = T-∧₁ (a << b) p

ok-at : (a b t : Wire) → T (okCCX a b t) → T (not (a == t))
ok-at a b t p = T-∧₁ (not (a == t)) (T-∧₂ (a << b) p)

ok-bt : (a b t : Wire) → T (okCCX a b t) → T (not (b == t))
ok-bt a b t p = T-∧₂ (not (a == t)) (T-∧₂ (a << b) p)

dCCX : (a b t : Wire) → .(T (okCCX a b t)) → Distinct (t ∷ a ∷ b ∷ [])
dCCX a b t p =
  ((λ e → neq a t (ok-at a b t p) (Eq.sym e)) ∷ (λ e → neq b t (ok-bt a b t p) (Eq.sym e)) ∷ [])
  ∷ ((<<-neq a b (ok-ab a b t p) ∷ []) ∷ ([] ∷ []))

-- Every element of a list satisfies p.
every : {A : Set} → (A → Bool) → List A → Bool
every p []       = true
every p (x ∷ xs) = p x ∧ every p xs

-- Does the letter leave wire m alone?
avoids : Wire → PG → Bool
avoids m (Xᵖ t)       = not (m == t)
avoids m (CXᵖ c t)    = not (m == c) ∧ not (m == t)
avoids m (CCXᵖ a b t) = not (m == a) ∧ (not (m == b) ∧ not (m == t))

-- Two lists of wires with no wire in common.
apart : List Wire → List Wire → Bool
apart xs ys = every (λ x → every (λ y → not (x == y)) ys) xs

-- Letters on disjoint wires (together on at most four).
disjoint : PG → PG → Bool
disjoint g h = (arity g + arity h ≤ᵇ 4) ∧ apart (wires g) (wires h)

------------------------------------------------------------------------
-- Properties of every letter, decided

private
  all4 : (Wire → Bool) → Bool
  all4 p = p ₀ ∧ (p ₁ ∧ (p ₂ ∧ p ₃))

  all4-sound : (p : Wire → Bool) → all4 p ≡ true → ∀ w → p w ≡ true
  all4-sound p h ₀ = ∧ˡ h
  all4-sound p h ₁ = ∧ˡ (∧ʳ {p ₀} h)
  all4-sound p h ₂ = ∧ˡ (∧ʳ {p ₁} (∧ʳ {p ₀} h))
  all4-sound p h ₃ = ∧ʳ {p ₂} (∧ʳ {p ₁} (∧ʳ {p ₀} h))

  implB : (b : Bool) → (T b → Bool) → Bool
  implB true  f = f tt
  implB false f = true

  implB-sound : (b : Bool) (f : T b → Bool) → implB b f ≡ true → (q : T b) → f q ≡ true
  implB-sound true f h tt = h

  pX : (PG → Bool) → Wire → Bool
  pX p t = p (Xᵖ t)

  pCX : (PG → Bool) → Wire → Wire → Bool
  pCX p c t = implB (okCX c t) (λ ok → p (CXᵖ c t {ok}))

  pCCX : (PG → Bool) → Wire → Wire → Wire → Bool
  pCCX p a b t = implB (okCCX a b t) (λ ok → p (CCXᵖ a b t {ok}))

-- p holds of every letter, checked on all 28.
forallPG : (PG → Bool) → Bool
forallPG p = all4 (pX p) ∧ (all4 (λ c → all4 (pCX p c)) ∧ all4 (λ a → all4 (λ b → all4 (pCCX p a b))))

forallPG-sound : (p : PG → Bool) → forallPG p ≡ true → ∀ g → p g ≡ true
forallPG-sound p h (Xᵖ t) = all4-sound (pX p) (∧ˡ h) t
forallPG-sound p h (CXᵖ c t {ok}) =
  implB-sound (okCX c t) (λ ok′ → p (CXᵖ c t {ok′}))
    (all4-sound (pCX p c) (all4-sound (λ c → all4 (pCX p c)) (∧ˡ (∧ʳ {all4 (pX p)} h)) c) t)
    (recompute (T? (okCX c t)) ok)
forallPG-sound p h (CCXᵖ a b t {ok}) =
  implB-sound (okCCX a b t) (λ ok′ → p (CCXᵖ a b t {ok′}))
    (all4-sound (pCCX p a b)
      (all4-sound (λ b → all4 (pCCX p a b))
        (all4-sound (λ a → all4 (λ b → all4 (pCCX p a b)))
          (∧ʳ {all4 (λ c → all4 (pCX p c))} (∧ʳ {all4 (pX p)} h)) a) b) t)
    (recompute (T? (okCCX a b t)) ok)

------------------------------------------------------------------------
-- Swap networks

-- The swap of wires d and d + 1.
sw : ℕ → Circuit 4
sw 0 = σ
sw 1 = σ ↑
sw 2 = σ ↑ ↑
sw (suc (suc (suc _))) = ε

module Cx = Cox.Circuits 4 sw
open Cx using (Pc)

cox : Cx.Coxeter (4 VRel,_===_)
cox = record { order = order ; braid = braid ; far = far }
  where
  order : ∀ i → 2 + i ≤ 4 → 4 ⊢ sw i • sw i ≈ ε
  order 0 _ = σ-invol
  order 1 _ = lemma-cong↑ (σ • σ) ε σ-invol
  order 2 _ = lemma-cong↑ (σ ↑ • σ ↑) ε (lemma-cong↑ (σ • σ) ε σ-invol)
  order (suc (suc (suc i))) (s≤s (s≤s (s≤s (s≤s ()))))
  braid : ∀ i → 3 + i ≤ 4 → 4 ⊢ sw i • sw (suc i) • sw i ≈ sw (suc i) • sw i • sw (suc i)
  braid 0 _ = yang-baxter
  braid 1 _ = lemma-cong↑ (σ • σ ↑ • σ) (σ ↑ • σ • σ ↑) yang-baxter
  braid (suc (suc i)) (s≤s (s≤s (s≤s (s≤s ()))))
  far : ∀ i j → 2 + i ≤ j → 2 + j ≤ 4 → 4 ⊢ sw i • sw j ≈ sw j • sw i
  far 0 0 () _
  far 0 1 (s≤s ()) _
  far 0 2 _ _ = sym (axiom (comm₂ swap (gate₂ swap)))
  far 0 (suc (suc (suc j))) _ (s≤s (s≤s (s≤s (s≤s ()))))
  far (suc i) 0 () _
  far (suc i) 1 (s≤s ()) _
  far (suc i) 2 (s≤s (s≤s ())) _
  far (suc i) (suc (suc (suc j))) _ (s≤s (s≤s (s≤s (s≤s ()))))

open Cx.Complete cox using (Fr ; Fr-conj ; frame≈ ; Pc-inv ; Pc-inv′ ; Comm≥)

-- The generators of S₄ on the wires 0 1, 1 2 and 2 3.
s₀ s₁ s₂ : SG 4
s₀ = Sym.gate₂ Sym.σ-gate
s₁ = Sym.gate₂ Sym.σ-gate Sym.↥
s₂ = Sym.gate₂ Sym.σ-gate Sym.↥ Sym.↥

-- The cycle 0 → 1 → 2 → 3 → 0 of the wires: its network is σ⁻[ 3 ].
Fc : CW
Fc = [ s₀ ]ʷ • ([ s₁ ]ʷ • [ s₂ ]ʷ)

-- The bottom gates commute with the swaps above them.
private
  cX : Comm≥ 1 X
  cX 0 () _
  cX 1 _ _ = axiom (comm₁ ⌈ X-gate ⌉ (gate₂ swap))
  cX 2 _ _ = axiom (comm₁ ⌈ X-gate ⌉ (gate₂ swap ↥))
  cX (suc (suc (suc i))) _ (s≤s (s≤s (s≤s (s≤s ()))))

  cCX : Comm≥ 2 CX
  cCX 0 () _
  cCX 1 (s≤s ()) _
  cCX 2 _ _ = axiom (comm₂ ⌈ CX-gate ⌉ (gate₂ swap))
  cCX (suc (suc (suc i))) _ (s≤s (s≤s (s≤s (s≤s ()))))

  cCCX : Comm≥ 3 CCX
  cCCX 0 () _
  cCCX 1 (s≤s ()) _
  cCCX 2 (s≤s (s≤s ())) _
  cCCX (suc (suc (suc i))) _ (s≤s (s≤s (s≤s (s≤s ()))))

------------------------------------------------------------------------
-- Placing a letter

ι : PG → Circuit 4
ι (Xᵖ t)            = Fr X (frame (t ∷ []) (dX t))
ι (CXᵖ c t {ok})    = Fr CX (frame (t ∷ c ∷ []) (dCX c t ok))
ι (CCXᵖ a b t {ok}) = Fr CCX (frame (t ∷ a ∷ b ∷ []) (dCCX a b t ok))

ιʷ : Word PG → Circuit 4
ιʷ [ g ]ʷ   = ι g
ιʷ ε       = ε
ιʷ (u • v) = ιʷ u • ιʷ v

-- A list of letters, in diagram order.
ι* : List PG → Circuit 4
ι* u = ιʷ (word-of-list u)

------------------------------------------------------------------------
-- The function of a letter

⟦_⟧ᵖ : PG → Fun 4
⟦ Xᵖ t ⟧ᵖ x       = x V.[ t ]%= not
⟦ CXᵖ c t ⟧ᵖ x    = x V.[ t ]%= (_xor V.lookup x c)
⟦ CCXᵖ a b t ⟧ᵖ x = x V.[ t ]%= (_xor (V.lookup x a ∧ V.lookup x b))

⟦_⟧ᵖ* : List PG → Fun 4
⟦ [] ⟧ᵖ*    = id
⟦ g ∷ u ⟧ᵖ* = ⟦ g ⟧ᵖ ⨾ ⟦ u ⟧ᵖ*

private
  sem-check : forallPG (λ g → eqF 4 ⟦ ι g ⟧ ⟦ g ⟧ᵖ) ≡ true
  sem-check = Eq.refl

-- A placed letter computes its function.
sem-ok : (g : PG) → ⟦ ι g ⟧ ≐ ⟦ g ⟧ᵖ
sem-ok g = eqF-sound 4 ⟦ ι g ⟧ ⟦ g ⟧ᵖ (forallPG-sound (λ g → eqF 4 ⟦ ι g ⟧ ⟦ g ⟧ᵖ) sem-check g)

ι*-sem : (u : List PG) → ⟦ ι* u ⟧ ≐ ⟦ u ⟧ᵖ*
ι*-sem []      = ≐-refl
ι*-sem (g ∷ u) = ⨾-cong (sem-ok g) (ι*-sem u)

------------------------------------------------------------------------
-- Conjugation

Fr-cong : {b b′ : Circuit 4} (F : CW) → 4 ⊢ b ≈ b′ → 4 ⊢ Fr b F ≈ Fr b′ F
Fr-cong F e = cong refl (cong e refl)

module _ {P P⁻ : Circuit 4} (inv-l : 4 ⊢ P⁻ • P ≈ ε) where

  -- Conjugation by P is multiplicative ...
  conj-• : (a b : Circuit 4) → 4 ⊢ (P • a • P⁻) • (P • b • P⁻) ≈ P • (a • b) • P⁻
  conj-• a b = begin
    (P • a • P⁻) • (P • b • P⁻)    ≈⟨ assoc ⟩
    P • (a • P⁻) • (P • b • P⁻)    ≈⟨ cong refl assoc ⟩
    P • a • P⁻ • (P • b • P⁻)      ≈⟨ cong refl (cong refl (sym assoc)) ⟩
    P • a • (P⁻ • P) • b • P⁻      ≈⟨ cong refl (cong refl (cong inv-l refl)) ⟩
    P • a • ε • b • P⁻             ≈⟨ cong refl (cong refl left-unit) ⟩
    P • a • b • P⁻                 ≈⟨ cong refl (sym assoc) ⟩
    P • (a • b) • P⁻               ∎

  -- ... and cancels.
  peel : (a : Circuit 4) → 4 ⊢ P⁻ • (P • a • P⁻) • P ≈ a
  peel a = begin
    P⁻ • (P • a • P⁻) • P          ≈⟨ cong refl assoc ⟩
    P⁻ • P • (a • P⁻) • P          ≈⟨ sym assoc ⟩
    (P⁻ • P) • (a • P⁻) • P        ≈⟨ cong inv-l refl ⟩
    ε • (a • P⁻) • P               ≈⟨ left-unit ⟩
    (a • P⁻) • P                   ≈⟨ assoc ⟩
    a • P⁻ • P                     ≈⟨ cong refl inv-l ⟩
    a • ε                          ≈⟨ right-unit ⟩
    a                              ∎

  unconj : {a b : Circuit 4} → 4 ⊢ P • a • P⁻ ≈ P • b • P⁻ → 4 ⊢ a ≈ b
  unconj {a} {b} e = trans (sym (peel a)) (trans (cong refl (cong e refl)) (peel b))

------------------------------------------------------------------------
-- A placement depends only on where the network sends the gate's wires

ι-X : (t : Wire) (F : CW) → act F ₀ ≡ t → 4 ⊢ ι (Xᵖ t) ≈ Fr X F
ι-X t F h₀ = frame≈ 1 3 ℕP.≤-refl X cX (frame ts (dX t)) F ag
  where
  ts = t ∷ []
  ag : ∀ x → toℕ x < 1 → act (frame ts (dX t)) x ≡ act F x
  ag ₀ _ = Eq.trans (frame-act ts (dX t) ₀ t Eq.refl) (Eq.sym h₀)
  ag (suc x) (s≤s ())

ι-CX : (c t : Wire) .{ok : T (okCX c t)} (F : CW) → act F ₀ ≡ t → act F ₁ ≡ c →
       4 ⊢ ι (CXᵖ c t {ok}) ≈ Fr CX F
ι-CX c t {ok} F h₀ h₁ = frame≈ 2 2 ℕP.≤-refl CX cCX (frame ts d) F ag
  where
  ts = t ∷ c ∷ []
  d = dCX c t ok
  ag : ∀ x → toℕ x < 2 → act (frame ts d) x ≡ act F x
  ag ₀ _ = Eq.trans (frame-act ts d ₀ t Eq.refl) (Eq.sym h₀)
  ag ₁ _ = Eq.trans (frame-act ts d ₁ c Eq.refl) (Eq.sym h₁)
  ag (suc (suc x)) (s≤s (s≤s ()))

ι-CCX : (a b t : Wire) .{ok : T (okCCX a b t)} (F : CW) →
        act F ₀ ≡ t → act F ₁ ≡ a → act F ₂ ≡ b → 4 ⊢ ι (CCXᵖ a b t {ok}) ≈ Fr CCX F
ι-CCX a b t {ok} F h₀ h₁ h₂ = frame≈ 3 1 ℕP.≤-refl CCX cCCX (frame ts d) F ag
  where
  ts = t ∷ a ∷ b ∷ []
  d = dCCX a b t ok
  ag : ∀ x → toℕ x < 3 → act (frame ts d) x ≡ act F x
  ag ₀ _ = Eq.trans (frame-act ts d ₀ t Eq.refl) (Eq.sym h₀)
  ag ₁ _ = Eq.trans (frame-act ts d ₁ a Eq.refl) (Eq.sym h₁)
  ag ₂ _ = Eq.trans (frame-act ts d ₂ b Eq.refl) (Eq.sym h₂)
  ag (suc (suc (suc x))) (s≤s (s≤s (s≤s ())))

-- CCX does not see the order of its controls (rule (5)).
ι-CCX′ : (a b t : Wire) .{ok : T (okCCX a b t)} (F : CW) →
         act F ₀ ≡ t → act F ₁ ≡ b → act F ₂ ≡ a → 4 ⊢ ι (CCXᵖ a b t {ok}) ≈ Fr CCX F
ι-CCX′ a b t {ok} F h₀ h₁ h₂ = begin
  ι (CCXᵖ a b t {ok})                   ≈⟨ ι-CCX a b t {ok} (F • [ s₁ ]ʷ) h₀ h₂ h₁ ⟩
  Fr CCX (F • [ s₁ ]ʷ)                   ≈⟨ sym (Fr-conj CCX F [ s₁ ]ʷ) ⟩
  Pc 0 F • Fr CCX [ s₁ ]ʷ • Pc 0 (inv F)  ≈⟨ cong refl (cong (ax-at r5 1) refl) ⟩
  Pc 0 F • CCX • Pc 0 (inv F)             ∎

------------------------------------------------------------------------
-- A gate shifted up is its placement by the cycle of the wires

-- σ⁻[ 3 ] and σ[ 3 ] are the networks of Fc and its inverse, and a
-- three-wire circuit passes σ[ 3 ] one wire up (naturality, nat₃).
shift : (w : Circuit 3) → 4 ⊢ (w ↓ᵏ 0) ↑ ≈ Fr (w ↓ᵏ 1) Fc
shift w = begin
  (w ↓ᵏ 0) ↑                          ≈⟨ sym left-unit ⟩
  ε • (w ↓ᵏ 0) ↑                      ≈⟨ cong (sym (σ⁻σ 3)) refl ⟩
  (σ⁻[ 3 ] • σ[ 3 ]) • (w ↓ᵏ 0) ↑    ≈⟨ assoc ⟩
  σ⁻[ 3 ] • σ[ 3 ] • (w ↓ᵏ 0) ↑      ≈⟨ cong refl (sym (nat₃ w)) ⟩
  σ⁻[ 3 ] • (w ↓ᵏ 1) • σ[ 3 ]        ∎

X↑₁ : 4 ⊢ X ↑ ≈ Fr X Fc
X↑₁ = shift X

X↑₂ : 4 ⊢ X ↑ ↑ ≈ Fr X (Fc • Fc)
X↑₂ = trans (shift (X ↑)) (trans (Fr-cong Fc X↑₁) (Fr-conj X Fc Fc))

X↑₃ : 4 ⊢ X ↑ ↑ ↑ ≈ Fr X (Fc • (Fc • Fc))
X↑₃ = trans (shift (X ↑ ↑)) (trans (Fr-cong Fc X↑₂) (Fr-conj X Fc (Fc • Fc)))

CX↑₁ : 4 ⊢ CX ↑ ≈ Fr CX Fc
CX↑₁ = shift CX

CX↑₂ : 4 ⊢ CX ↑ ↑ ≈ Fr CX (Fc • Fc)
CX↑₂ = trans (shift (CX ↑)) (trans (Fr-cong Fc CX↑₁) (Fr-conj CX Fc Fc))

CCX↑₁ : 4 ⊢ CCX ↑ ≈ Fr CCX Fc
CCX↑₁ = shift CCX

-- So letters on consecutive wires, in the gate's own order, are the
-- gates shifted up.
ιX₀ : 4 ⊢ ι (Xᵖ ₀) ≈ X
ιX₀ = trans (ι-X ₀ ε Eq.refl) (trans left-unit right-unit)

ιX₁ : 4 ⊢ ι (Xᵖ ₁) ≈ X ↑
ιX₁ = trans (ι-X ₁ Fc Eq.refl) (sym X↑₁)

ιX₂ : 4 ⊢ ι (Xᵖ ₂) ≈ X ↑ ↑
ιX₂ = trans (ι-X ₂ (Fc • Fc) Eq.refl) (sym X↑₂)

ιX₃ : 4 ⊢ ι (Xᵖ ₃) ≈ X ↑ ↑ ↑
ιX₃ = trans (ι-X ₃ (Fc • (Fc • Fc)) Eq.refl) (sym X↑₃)

ιCX₁₀ : 4 ⊢ ι (CXᵖ ₁ ₀) ≈ CX
ιCX₁₀ = trans (ι-CX ₁ ₀ ε Eq.refl Eq.refl) (trans left-unit right-unit)

ιCX₂₁ : 4 ⊢ ι (CXᵖ ₂ ₁) ≈ CX ↑
ιCX₂₁ = trans (ι-CX ₂ ₁ Fc Eq.refl Eq.refl) (sym CX↑₁)

ιCX₃₂ : 4 ⊢ ι (CXᵖ ₃ ₂) ≈ CX ↑ ↑
ιCX₃₂ = trans (ι-CX ₃ ₂ (Fc • Fc) Eq.refl Eq.refl) (sym CX↑₂)

ιCCX₁₂₀ : 4 ⊢ ι (CCXᵖ ₁ ₂ ₀) ≈ CCX
ιCCX₁₂₀ = trans (ι-CCX ₁ ₂ ₀ ε Eq.refl Eq.refl Eq.refl) (trans left-unit right-unit)

ιCCX₂₃₁ : 4 ⊢ ι (CCXᵖ ₂ ₃ ₁) ≈ CCX ↑
ιCCX₂₃₁ = trans (ι-CCX ₂ ₃ ₁ Fc Eq.refl Eq.refl Eq.refl) (sym CCX↑₁)

-- The paper's CCX_{12→4} on four wires.
ιCCX₂₃₀ : 4 ⊢ ι (CCXᵖ ₂ ₃ ₀) ≈ CCX₃₂₀
ιCCX₂₃₀ = trans (ι-CCX ₂ ₃ ₀ ([ s₀ ]ʷ • Fc) Eq.refl Eq.refl Eq.refl)
            (trans (sym (Fr-conj CCX [ s₀ ]ʷ Fc)) (cong refl (cong (sym CCX↑₁) refl)))

------------------------------------------------------------------------
-- Relabelling the wires

-- A permutation of the wires, with a Coxeter word whose network
-- carries it out.
record Relabel : Set where
  field
    π     : Wire → Wire
    net   : CW
    net-π : ∀ w → act net w ≡ π w

  π-inj : ∀ {a b} → π a ≡ π b → a ≡ b
  π-inj {a} {b} e = Eq.trans (Eq.sym (act-inv net a))
    (Eq.trans (Eq.cong (act (inv net)) (Eq.trans (net-π a) (Eq.trans e (Eq.sym (net-π b)))))
              (act-inv net b))

open Relabel using (π ; net ; net-π)

-- The network of a relabelling, and its inverse.
S S⁻ : Relabel → Circuit 4
S R  = Pc 0 (net R)
S⁻ R = Pc 0 (inv (net R))

private
  ≢→T : {a b : Wire} → a ≢ b → T (not (a == b))
  ≢→T {a} {b} a≢b = not-T (a == b) (λ h → a≢b (==-sound a b h))

  false-if : (b : Bool) → (T b → ⊥) → b ≡ false
  false-if true  f = ⊥-elim (f tt)
  false-if false f = Eq.refl

-- CCX with controls x and y in either order, and target z.
ok-tt : (x y z : Wire) → true ≡ (x << y) → x ≢ z → y ≢ z → T (okCCX x y z)
ok-tt x y z e xz yz = T-∧ (x << y) (Eq.subst T e tt) (T-∧ (not (x == z)) (≢→T xz) (≢→T yz))

ok-ff : (x y z : Wire) → false ≡ (x << y) → x ≢ y → x ≢ z → y ≢ z → T (okCCX y x z)
ok-ff x y z e xy xz yz = T-∧ (y << x) (<<-flip x y xy (Eq.sym e)) (T-∧ (not (y == z)) (≢→T yz) (≢→T xz))

ccx-by : (x y z : Wire) (o : Bool) → o ≡ (x << y) → .(x ≢ y) → .(x ≢ z) → .(y ≢ z) → PG
ccx-by x y z true  e xy xz yz = CCXᵖ x y z {ok-tt x y z e xz yz}
ccx-by x y z false e xy xz yz = CCXᵖ y x z {ok-ff x y z e xy xz yz}

ccx : (x y z : Wire) → .(x ≢ y) → .(x ≢ z) → .(y ≢ z) → PG
ccx x y z xy xz yz = ccx-by x y z (x << y) Eq.refl xy xz yz

ι-ccx-by : (x y z : Wire) (o : Bool) (e : o ≡ (x << y)) .(xy : x ≢ y) .(xz : x ≢ z) .(yz : y ≢ z)
           (F : CW) → act F ₀ ≡ z → act F ₁ ≡ x → act F ₂ ≡ y →
           4 ⊢ ι (ccx-by x y z o e xy xz yz) ≈ Fr CCX F
ι-ccx-by x y z true  e xy xz yz F h₀ h₁ h₂ = ι-CCX x y z {ok-tt x y z e xz yz} F h₀ h₁ h₂
ι-ccx-by x y z false e xy xz yz F h₀ h₁ h₂ = ι-CCX′ y x z {ok-ff x y z e xy xz yz} F h₀ h₁ h₂

avoids-ccx-by : (x y z : Wire) (o : Bool) (e : o ≡ (x << y)) .(xy : x ≢ y) .(xz : x ≢ z) .(yz : y ≢ z)
                (m : Wire) → avoids m (ccx-by x y z o e xy xz yz) ≡ not (m == x) ∧ (not (m == y) ∧ not (m == z))
avoids-ccx-by x y z true  e xy xz yz m = Eq.refl
avoids-ccx-by x y z false e xy xz yz m = ∧-swap (not (m == y)) (not (m == x)) (not (m == z))

module _ (R : Relabel) where

  open Relabel R using (π-inj)

  private
    ok-π : (c t : Wire) → .(T (okCX c t)) → T (okCX (π R c) (π R t))
    ok-π c t ok = ≢→T (λ e → neq c t ok (π-inj e))

    π-ab : (a b t : Wire) → .(T (okCCX a b t)) → π R a ≢ π R b
    π-ab a b t ok e = <<-neq a b (ok-ab a b t ok) (π-inj e)

    π-at : (a b t : Wire) → .(T (okCCX a b t)) → π R a ≢ π R t
    π-at a b t ok e = neq a t (ok-at a b t ok) (π-inj e)

    π-bt : (a b t : Wire) → .(T (okCCX a b t)) → π R b ≢ π R t
    π-bt a b t ok e = neq b t (ok-bt a b t ok) (π-inj e)

  -- A letter with its wires relabelled (the controls of CCX re-sorted).
  relabel : PG → PG
  relabel (Xᵖ t)            = Xᵖ (π R t)
  relabel (CXᵖ c t {ok})    = CXᵖ (π R c) (π R t) {ok-π c t ok}
  relabel (CCXᵖ a b t {ok}) = ccx (π R a) (π R b) (π R t) (π-ab a b t ok) (π-at a b t ok) (π-bt a b t ok)

  private
    at : (ts : List Wire) (d : Distinct ts) (i x : Wire) → ts ‼ toℕ i ≡ just x →
         act (net R • frame ts d) i ≡ π R x
    at ts d i x e = Eq.trans (Eq.cong (act (net R)) (frame-act ts d i x e)) (net-π R x)

  -- Relabelling is conjugation by the network.
  relabel-ι : (g : PG) → 4 ⊢ ι (relabel g) ≈ S R • ι g • S⁻ R
  relabel-ι (Xᵖ t) =
    trans (ι-X (π R t) (net R • F) (at ts (dX t) ₀ t Eq.refl)) (sym (Fr-conj X (net R) F))
    where
    ts = t ∷ []
    F = frame ts (dX t)
  relabel-ι (CXᵖ c t {ok}) =
    trans (ι-CX (π R c) (π R t) {ok-π c t ok} (net R • F) (at ts d ₀ t Eq.refl) (at ts d ₁ c Eq.refl))
          (sym (Fr-conj CX (net R) F))
    where
    ts = t ∷ c ∷ []
    d = dCX c t ok
    F = frame ts d
  relabel-ι (CCXᵖ a b t {ok}) =
    trans (ι-ccx-by (π R a) (π R b) (π R t) (π R a << π R b) Eq.refl
                    (π-ab a b t ok) (π-at a b t ok) (π-bt a b t ok)
                    (net R • F) (at ts d ₀ t Eq.refl) (at ts d ₁ a Eq.refl) (at ts d ₂ b Eq.refl))
          (sym (Fr-conj CCX (net R) F))
    where
    ts = t ∷ a ∷ b ∷ []
    d = dCCX a b t ok
    F = frame ts d

  -- ... and so on words.
  relabel-ι* : (u : List PG) → 4 ⊢ ι* (map relabel u) ≈ S R • ι* u • S⁻ R
  relabel-ι* []      = sym (trans (cong refl left-unit) (Pc-inv 0 ℕP.≤-refl (net R)))
  relabel-ι* (g ∷ u) =
    trans (cong (relabel-ι g) (relabel-ι* u)) (conj-• (Pc-inv′ 0 ℕP.≤-refl (net R)) (ι g) (ι* u))

  relabel-≈ : {u v : List PG} → 4 ⊢ ι* u ≈ ι* v → 4 ⊢ ι* (map relabel u) ≈ ι* (map relabel v)
  relabel-≈ {u} {v} e = trans (relabel-ι* u) (trans (cong refl (cong e refl)) (sym (relabel-ι* v)))

  -- Relabelling keeps a letter off the relabelled wire.
  ==-π : (a b : Wire) → (π R a == π R b) ≡ (a == b)
  ==-π a b with a == b in e
  ... | true  = T→≡ (Eq.subst (λ z → T (π R a == π R z)) (==-sound a b (≡→T e)) (==-refl (π R a)))
  ... | false = false-if (π R a == π R b)
                  (λ h → Eq.subst T e (Eq.subst (λ z → T (a == z)) (π-inj (==-sound (π R a) (π R b) h)) (==-refl a)))

  avoids-relabel : (m : Wire) (g : PG) → avoids (π R m) (relabel g) ≡ avoids m g
  avoids-relabel m (Xᵖ t)     = Eq.cong not (==-π m t)
  avoids-relabel m (CXᵖ c t)  = Eq.cong₂ _∧_ (Eq.cong not (==-π m c)) (Eq.cong not (==-π m t))
  avoids-relabel m (CCXᵖ a b t {ok}) =
    Eq.trans (avoids-ccx-by (π R a) (π R b) (π R t) (π R a << π R b) Eq.refl
                            (π-ab a b t ok) (π-at a b t ok) (π-bt a b t ok) (π R m))
             (Eq.cong₂ _∧_ (Eq.cong not (==-π m a))
                           (Eq.cong₂ _∧_ (Eq.cong not (==-π m b)) (Eq.cong not (==-π m t))))

  every-avoids : (m : Wire) (u : List PG) → every (avoids m) u ≡ true →
                 every (avoids (π R m)) (map relabel u) ≡ true
  every-avoids m []      _ = Eq.refl
  every-avoids m (g ∷ u) h =
    Eq.cong₂ _∧_ (Eq.trans (avoids-relabel m g) (∧ˡ h)) (every-avoids m u (∧ʳ {avoids m g} h))

-- The relabelling sending the wires 0, 1, 2, 3 to a, b, c, d.
distinct4 : Wire → Wire → Wire → Wire → Bool
distinct4 a b c d = okCX a b ∧ (okCX a c ∧ (okCX a d ∧ (okCX b c ∧ (okCX b d ∧ okCX c d))))

private
  dist4 : (a b c d : Wire) → .(T (distinct4 a b c d)) → Distinct (a ∷ b ∷ c ∷ d ∷ [])
  dist4 a b c d p =
    (neq a b p₁ ∷ neq a c p₂ ∷ neq a d p₃ ∷ []) ∷ ((neq b c p₄ ∷ neq b d p₅ ∷ []) ∷ ((neq c d p₆ ∷ []) ∷ ([] ∷ [])))
    where
    p′ = recompute (T? (distinct4 a b c d)) p
    q₁ = T-∧₂ (okCX a b) p′
    q₂ = T-∧₂ (okCX a c) q₁
    q₃ = T-∧₂ (okCX a d) q₂
    q₄ = T-∧₂ (okCX b c) q₃
    p₁ = T-∧₁ (okCX a b) p′
    p₂ = T-∧₁ (okCX a c) q₁
    p₃ = T-∧₁ (okCX a d) q₂
    p₄ = T-∧₁ (okCX b c) q₃
    p₅ = T-∧₁ (okCX b d) q₄
    p₆ = T-∧₂ (okCX b d) q₄

sel4 : Wire → Wire → Wire → Wire → Wire → Wire
sel4 a b c d ₀ = a
sel4 a b c d ₁ = b
sel4 a b c d ₂ = c
sel4 a b c d ₃ = d

ρ4 : (a b c d : Wire) → .{_ : T (distinct4 a b c d)} → Relabel
ρ4 a b c d {p} = record { π = sel4 a b c d ; net = frame ts (dist4 a b c d p) ; net-π = np }
  where
  ts = a ∷ b ∷ c ∷ d ∷ []
  np : ∀ w → act (frame ts (dist4 a b c d p)) w ≡ sel4 a b c d w
  np ₀ = frame-act ts (dist4 a b c d p) ₀ a Eq.refl
  np ₁ = frame-act ts (dist4 a b c d p) ₁ b Eq.refl
  np ₂ = frame-act ts (dist4 a b c d p) ₂ c Eq.refl
  np ₃ = frame-act ts (dist4 a b c d p) ₃ d Eq.refl

-- Any permutation of the wires, given as an injective map.
fromPerm : (f : Wire → Wire) → (∀ {a b} → f a ≡ f b → a ≡ b) → Relabel
fromPerm f inj = record { π = f ; net = frame ts d ; net-π = np }
  where
  ts = f ₀ ∷ f ₁ ∷ f ₂ ∷ f ₃ ∷ []
  ne : ∀ {a b} → a ≢ b → f a ≢ f b
  ne a≢b e = a≢b (inj e)
  d : Distinct ts
  d = (ne (λ ()) ∷ ne (λ ()) ∷ ne (λ ()) ∷ []) ∷ ((ne (λ ()) ∷ ne (λ ()) ∷ []) ∷ ((ne (λ ()) ∷ []) ∷ ([] ∷ [])))
  np : ∀ w → act (frame ts d) w ≡ f w
  np ₀ = frame-act ts d ₀ (f ₀) Eq.refl
  np ₁ = frame-act ts d ₁ (f ₁) Eq.refl
  np ₂ = frame-act ts d ₂ (f ₂) Eq.refl
  np ₃ = frame-act ts d ₃ (f ₃) Eq.refl

-- The transposition of wire m and wire 3.
τ : Wire → Relabel
τ ₀ = ρ4 ₃ ₁ ₂ ₀
τ ₁ = ρ4 ₀ ₃ ₂ ₁
τ ₂ = ρ4 ₀ ₁ ₃ ₂
τ ₃ = ρ4 ₀ ₁ ₂ ₃

τ-top : (m : Wire) → π (τ m) m ≡ ₃
τ-top ₀ = Eq.refl
τ-top ₁ = Eq.refl
τ-top ₂ = Eq.refl
τ-top ₃ = Eq.refl

------------------------------------------------------------------------
-- Letters on disjoint wires commute

private
  avoid-sound : (x : Wire) (ys : List Wire) → every (λ y → not (x == y)) ys ≡ true → Avoid x ys
  avoid-sound x []       _ = []
  avoid-sound x (y ∷ ys) h = neq x y (≡→T (∧ˡ h)) ∷ avoid-sound x ys (∧ʳ {not (x == y)} h)

  avoid-++ : {x : Wire} {xs ys : List Wire} → Avoid x xs → Avoid x ys → Avoid x (xs ++ ys)
  avoid-++ []      b = b
  avoid-++ (p ∷ a) b = p ∷ avoid-++ a b

  distinct-++ : (xs ys : List Wire) → Distinct xs → Distinct ys → apart xs ys ≡ true → Distinct (xs ++ ys)
  distinct-++ []       ys []       dy _ = dy
  distinct-++ (x ∷ xs) ys (a ∷ dx) dy h =
    avoid-++ a (avoid-sound x ys (∧ˡ h)) ∷ distinct-++ xs ys dx dy (∧ʳ {every (λ y → not (x == y)) ys} h)

  -- g placed by F, and h by F followed by Fk, which takes h's gate to
  -- bh′ above g's: so they commute when bg and bh′ do.
  comm-via : (g h : PG) (bg bh bh′ : Circuit 4) (F Fk : CW) →
             4 ⊢ ι g ≈ Fr bg F → 4 ⊢ ι h ≈ Fr bh (F • Fk) →
             4 ⊢ bh′ ≈ Fr bh Fk → 4 ⊢ bg • bh′ ≈ bh′ • bg →
             4 ⊢ ι g • ι h ≈ ι h • ι g
  comm-via g h bg bh bh′ F Fk eg eh eb c = begin
    ι g • ι h                          ≈⟨ cong eg eh′ ⟩
    (P • bg • P⁻) • (P • bh′ • P⁻)     ≈⟨ conj-• il bg bh′ ⟩
    P • (bg • bh′) • P⁻                ≈⟨ cong refl (cong c refl) ⟩
    P • (bh′ • bg) • P⁻                ≈⟨ sym (conj-• il bh′ bg) ⟩
    (P • bh′ • P⁻) • (P • bg • P⁻)     ≈⟨ cong (sym eh′) (sym eg) ⟩
    ι h • ι g                          ∎
    where
    P = Pc 0 F
    P⁻ = Pc 0 (inv F)
    il = Pc-inv′ 0 ℕP.≤-refl F
    eh′ : 4 ⊢ ι h ≈ P • bh′ • P⁻
    eh′ = trans eh (trans (sym (Fr-conj bh F Fk)) (cong refl (cong (sym eb) refl)))

disj-comm : (g h : PG) → disjoint g h ≡ true → 4 ⊢ ι g • ι h ≈ ι h • ι g
disj-comm (Xᵖ t) (Xᵖ s) e =
  comm-via (Xᵖ t) (Xᵖ s) X X (X ↑) F Fc
    (ι-X t F (frame-act ts d ₀ t Eq.refl)) (ι-X s (F • Fc) (frame-act ts d ₁ s Eq.refl))
    X↑₁ (sym (comm-gate₁-w↑ ⌈ X-gate ⌉ X))
  where
  ts = t ∷ s ∷ []
  d = distinct-++ (t ∷ []) (s ∷ []) (dX t) (dX s) e
  F = frame ts d
disj-comm (Xᵖ t) (CXᵖ c s {ok}) e =
  comm-via (Xᵖ t) (CXᵖ c s {ok}) X CX (CX ↑) F Fc
    (ι-X t F (frame-act ts d ₀ t Eq.refl))
    (ι-CX c s {ok} (F • Fc) (frame-act ts d ₁ s Eq.refl) (frame-act ts d ₂ c Eq.refl))
    CX↑₁ (sym (comm-gate₁-w↑ ⌈ X-gate ⌉ CX))
  where
  ts = t ∷ s ∷ c ∷ []
  d = distinct-++ (t ∷ []) (s ∷ c ∷ []) (dX t) (dCX c s ok) e
  F = frame ts d
disj-comm (CXᵖ c t {ok}) (Xᵖ s) e =
  comm-via (CXᵖ c t {ok}) (Xᵖ s) CX X (X ↑ ↑) F (Fc • Fc)
    (ι-CX c t {ok} F (frame-act ts d ₀ t Eq.refl) (frame-act ts d ₁ c Eq.refl))
    (ι-X s (F • (Fc • Fc)) (frame-act ts d ₂ s Eq.refl))
    X↑₂ (sym (comm-gate₂-w↑↑ ⌈ CX-gate ⌉ X))
  where
  ts = t ∷ c ∷ s ∷ []
  d = distinct-++ (t ∷ c ∷ []) (s ∷ []) (dCX c t ok) (dX s) e
  F = frame ts d
disj-comm (Xᵖ t) (CCXᵖ a b s {ok}) e =
  comm-via (Xᵖ t) (CCXᵖ a b s {ok}) X CCX (CCX ↑) F Fc
    (ι-X t F (frame-act ts d ₀ t Eq.refl))
    (ι-CCX a b s {ok} (F • Fc) (frame-act ts d ₁ s Eq.refl) (frame-act ts d ₂ a Eq.refl)
                               (frame-act ts d ₃ b Eq.refl))
    CCX↑₁ (sym (comm-gate₁-w↑ ⌈ X-gate ⌉ CCX))
  where
  ts = t ∷ s ∷ a ∷ b ∷ []
  d = distinct-++ (t ∷ []) (s ∷ a ∷ b ∷ []) (dX t) (dCCX a b s ok) e
  F = frame ts d
disj-comm (CCXᵖ a b t {ok}) (Xᵖ s) e =
  comm-via (CCXᵖ a b t {ok}) (Xᵖ s) CCX X (X ↑ ↑ ↑) F (Fc • (Fc • Fc))
    (ι-CCX a b t {ok} F (frame-act ts d ₀ t Eq.refl) (frame-act ts d ₁ a Eq.refl)
                        (frame-act ts d ₂ b Eq.refl))
    (ι-X s (F • (Fc • (Fc • Fc))) (frame-act ts d ₃ s Eq.refl))
    X↑₃ (sym (comm-gate₃-w↑↑↑ ⌈ CCX-gate ⌉ X))
  where
  ts = t ∷ a ∷ b ∷ s ∷ []
  d = distinct-++ (t ∷ a ∷ b ∷ []) (s ∷ []) (dCCX a b t ok) (dX s) e
  F = frame ts d
disj-comm (CXᵖ c t {ok}) (CXᵖ c′ s {ok′}) e =
  comm-via (CXᵖ c t {ok}) (CXᵖ c′ s {ok′}) CX CX (CX ↑ ↑) F (Fc • Fc)
    (ι-CX c t {ok} F (frame-act ts d ₀ t Eq.refl) (frame-act ts d ₁ c Eq.refl))
    (ι-CX c′ s {ok′} (F • (Fc • Fc)) (frame-act ts d ₂ s Eq.refl) (frame-act ts d ₃ c′ Eq.refl))
    CX↑₂ (sym (comm-gate₂-w↑↑ ⌈ CX-gate ⌉ CX))
  where
  ts = t ∷ c ∷ s ∷ c′ ∷ []
  d = distinct-++ (t ∷ c ∷ []) (s ∷ c′ ∷ []) (dCX c t ok) (dCX c′ s ok′) e
  F = frame ts d
disj-comm (CXᵖ _ _)    (CCXᵖ _ _ _) ()
disj-comm (CCXᵖ _ _ _) (CXᵖ _ _)    ()
disj-comm (CCXᵖ _ _ _) (CCXᵖ _ _ _) ()

------------------------------------------------------------------------
-- Rule (7)

-- In our numbering, diagram order: CCX_{3,2→1} CX_{1→0} CCX_{3,2→1} =
-- CCX_{3,2→0} CX_{1→0}.
lhs₇ rhs₇ : List PG
lhs₇ = CCXᵖ ₂ ₃ ₁ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ []
rhs₇ = CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ []

rule7₀ : 4 ⊢ ι* lhs₇ ≈ ι* rhs₇
rule7₀ = begin
  ι (CCXᵖ ₂ ₃ ₁) • ι (CXᵖ ₁ ₀) • ι (CCXᵖ ₂ ₃ ₁) • ε   ≈⟨ cong ιCCX₂₃₁ (cong ιCX₁₀ (cong ιCCX₂₃₁ refl)) ⟩
  CCX ↑ • CX • CCX ↑ • ε                              ≈⟨ cong refl (cong refl right-unit) ⟩
  CCX ↑ • CX • CCX ↑                                  ≈⟨ axiom (srel (srel r7)) ⟩
  CCX₃₂₀ • CX                                         ≈⟨ cong (sym ιCCX₂₃₀) (trans (sym right-unit) (cong (sym ιCX₁₀) refl)) ⟩
  ι (CCXᵖ ₂ ₃ ₀) • ι (CXᵖ ₁ ₀) • ε                   ∎

-- Rule (7) placed on any wires.
rule7 : (R : Relabel) → 4 ⊢ ι* (map (relabel R) lhs₇) ≈ ι* (map (relabel R) rhs₇)
rule7 R = relabel-≈ R {lhs₇} {rhs₇} rule7₀

------------------------------------------------------------------------
-- Three-wire steps

-- Completeness on three wires.
Complete₃ : Set
Complete₃ = ∀ {c c′ : Circuit 3} → ⟦ c ⟧ ≐ ⟦ c′ ⟧ → 3 ⊢ c ≈ c′

private
  -- A circuit that leaves the top wire alone is a narrower one widened.
  low₂ : Gen 2 → Bool
  low₂ (gate₁ _) = true
  low₂ _         = false

  cut₂ : Gen 2 → Gen 1
  cut₂ (gate₁ h) = gate₁ h
  cut₂ _         = gate₁ ⌈ X-gate ⌉

  low₂-ok : (g : Gen 2) → low₂ g ≡ true → g ≡ cut₂ g ↧ᵏ 1
  low₂-ok (gate₀ ⌈ () ⌉) _
  low₂-ok (gate₁ h) _ = Eq.refl
  low₂-ok (gate₂ h) ()
  low₂-ok (g ↥)     ()

  low₃ : Gen 3 → Bool
  low₃ (gate₁ _) = true
  low₃ (gate₂ _) = true
  low₃ (g ↥)     = low₂ g
  low₃ _         = false

  cut₃ : Gen 3 → Gen 2
  cut₃ (gate₁ h) = gate₁ h
  cut₃ (gate₂ h) = gate₂ h
  cut₃ (g ↥)     = cut₂ g ↥
  cut₃ _         = gate₁ ⌈ X-gate ⌉

  low₃-ok : (g : Gen 3) → low₃ g ≡ true → g ≡ cut₃ g ↧ᵏ 1
  low₃-ok (gate₀ ⌈ () ⌉) _
  low₃-ok (gate₁ h) _ = Eq.refl
  low₃-ok (gate₂ h) _ = Eq.refl
  low₃-ok (gate₃ h) ()
  low₃-ok (g ↥)     e = Eq.cong _↥ (low₂-ok g e)

  low₄ : Gen 4 → Bool
  low₄ (g ↥) = low₃ g
  low₄ _     = true

  cut₄ : Gen 4 → Gen 3
  cut₄ (gate₁ h) = gate₁ h
  cut₄ (gate₂ h) = gate₂ h
  cut₄ (gate₃ h) = gate₃ h
  cut₄ (g ↥)     = cut₃ g ↥
  cut₄ _         = gate₁ ⌈ X-gate ⌉

  low₄-ok : (g : Gen 4) → low₄ g ≡ true → g ≡ cut₄ g ↧ᵏ 1
  low₄-ok (gate₀ ⌈ () ⌉) _
  low₄-ok (gate₁ h) _ = Eq.refl
  low₄-ok (gate₂ h) _ = Eq.refl
  low₄-ok (gate₃ h) _ = Eq.refl
  low₄-ok (g ↥)     e = Eq.cong _↥ (low₃-ok g e)

  lowW : Circuit 4 → Bool
  lowW [ g ]ʷ   = low₄ g
  lowW ε       = true
  lowW (u • v) = lowW u ∧ lowW v

  cutW : Circuit 4 → Circuit 3
  cutW [ g ]ʷ   = [ cut₄ g ]ʷ
  cutW ε       = ε
  cutW (u • v) = cutW u • cutW v

  lowW-ok : (w : Circuit 4) → lowW w ≡ true → w ≡ cutW w ↓ᵏ 1
  lowW-ok [ g ]ʷ   e = Eq.cong [_]ʷ (low₄-ok g e)
  lowW-ok ε       _ = Eq.refl
  lowW-ok (u • v) e = Eq.cong₂ _•_ (lowW-ok u (∧ˡ e)) (lowW-ok v (∧ʳ {lowW u} e))

  low-check : forallPG (λ g → not (avoids ₃ g) ∨ lowW (ι g)) ≡ true
  low-check = Eq.refl

  -- A letter off wire 3 is placed on the bottom three wires ...
  low-ι : (g : PG) → avoids ₃ g ≡ true → lowW (ι g) ≡ true
  low-ι g = imp (avoids ₃ g) (forallPG-sound (λ g → not (avoids ₃ g) ∨ lowW (ι g)) low-check g)

  -- ... and so is a word of them.
  low-ι* : (u : List PG) → every (avoids ₃) u ≡ true → lowW (ι* u) ≡ true
  low-ι* []      _ = Eq.refl
  low-ι* (g ∷ u) h = Eq.cong₂ _∧_ (low-ι g (∧ˡ h)) (low-ι* u (∧ʳ {avoids ₃ g} h))

  -- A widened circuit computes on the bottom wires.
  gen↓ : {n : ℕ} (g : Gen n) (x : Bits n) (b : Bool) →
         ⟦ g ↧ᵏ 1 ⟧ᵍ (x V.++ (b V.∷ V.[])) ≡ ⟦ g ⟧ᵍ x V.++ (b V.∷ V.[])
  gen↓ (gate₀ ⌈ () ⌉) x b
  gen↓ (gate₁ ⌈ X-gate ⌉) (a V.∷ x) b = Eq.refl
  gen↓ (gate₂ ⌈ CX-gate ⌉) (a V.∷ c V.∷ x) b = Eq.refl
  gen↓ (gate₂ swap) (a V.∷ c V.∷ x) b = Eq.refl
  gen↓ (gate₃ ⌈ CCX-gate ⌉) (a V.∷ c V.∷ d V.∷ x) b = Eq.refl
  gen↓ (g ↥) (a V.∷ x) b = Eq.cong (a V.∷_) (gen↓ g x b)

  word↓ : {n : ℕ} (w : Circuit n) (x : Bits n) (b : Bool) →
          ⟦ w ↓ᵏ 1 ⟧ (x V.++ (b V.∷ V.[])) ≡ ⟦ w ⟧ x V.++ (b V.∷ V.[])
  word↓ [ g ]ʷ   x b = gen↓ g x b
  word↓ ε       x b = Eq.refl
  word↓ (u • v) x b = Eq.trans (Eq.cong ⟦ v ↓ᵏ 1 ⟧ (word↓ u x b)) (word↓ v (⟦ u ⟧ x) b)

module Narrow (complete₃ : Complete₃) where

  -- Two words on the bottom three wires with the same function are
  -- equal: completeness on three wires, padded.
  narrow-low : (u v : List PG) → every (avoids ₃) u ≡ true → every (avoids ₃) v ≡ true →
               ⟦ ι* u ⟧ ≐ ⟦ ι* v ⟧ → 4 ⊢ ι* u ≈ ι* v
  narrow-low u v hu hv e = Eq.subst₂ (4 ⊢_≈_) (Eq.sym eu) (Eq.sym ev) (pad₃ (complete₃ sem₃) 1)
    where
    cu = cutW (ι* u)
    cv = cutW (ι* v)
    eu : ι* u ≡ cu ↓ᵏ 1
    eu = lowW-ok (ι* u) (low-ι* u hu)
    ev : ι* v ≡ cv ↓ᵏ 1
    ev = lowW-ok (ι* v) (low-ι* v hv)
    e↓ : ⟦ cu ↓ᵏ 1 ⟧ ≐ ⟦ cv ↓ᵏ 1 ⟧
    e↓ = Eq.subst₂ (λ a b → ⟦ a ⟧ ≐ ⟦ b ⟧) eu ev e
    sem₃ : ⟦ cu ⟧ ≐ ⟦ cv ⟧
    sem₃ x = VP.++-injectiveˡ (⟦ cu ⟧ x) (⟦ cv ⟧ x)
      (Eq.trans (Eq.sym (word↓ cu x false)) (Eq.trans (e↓ (x V.++ (false V.∷ V.[]))) (word↓ cv x false)))

  -- Two words on the three wires other than m with the same function
  -- are equal.
  narrow : (m : Wire) (u v : List PG) → every (avoids m) u ≡ true → every (avoids m) v ≡ true →
           ⟦ ι* u ⟧ ≐ ⟦ ι* v ⟧ → 4 ⊢ ι* u ≈ ι* v
  narrow m u v hu hv e = unconj (Pc-inv′ 0 ℕP.≤-refl (net R)) step
    where
    R = τ m
    u′ = map (relabel R) u
    v′ = map (relabel R) v
    hu′ : every (avoids ₃) u′ ≡ true
    hu′ = Eq.subst (λ z → every (avoids z) u′ ≡ true) (τ-top m) (every-avoids R m u hu)
    hv′ : every (avoids ₃) v′ ≡ true
    hv′ = Eq.subst (λ z → every (avoids z) v′ ≡ true) (τ-top m) (every-avoids R m v hv)
    eu : 4 ⊢ ι* u′ ≈ S R • ι* u • S⁻ R
    eu = relabel-ι* R u
    ev : 4 ⊢ ι* v′ ≈ S R • ι* v • S⁻ R
    ev = relabel-ι* R v
    mid : ⟦ S R • ι* u • S⁻ R ⟧ ≐ ⟦ S R • ι* v • S⁻ R ⟧
    mid = ⨾-cong {f = ⟦ S R ⟧} {f′ = ⟦ S R ⟧} ≐-refl (⨾-cong {g = ⟦ S⁻ R ⟧} {g′ = ⟦ S⁻ R ⟧} e ≐-refl)
    sem′ : ⟦ ι* u′ ⟧ ≐ ⟦ ι* v′ ⟧
    sem′ = ≐-trans (sound eu) (≐-trans mid (≐-sym (sound ev)))
    step : 4 ⊢ S R • ι* u • S⁻ R ≈ S R • ι* v • S⁻ R
    step = trans (sym eu) (trans (narrow-low u′ v′ hu′ hv′ sem′) ev)

  -- The same, from the functions of the letters.
  narrowᵖ : (m : Wire) (u v : List PG) → every (avoids m) u ≡ true → every (avoids m) v ≡ true →
            ⟦ u ⟧ᵖ* ≐ ⟦ v ⟧ᵖ* → 4 ⊢ ι* u ≈ ι* v
  narrowᵖ m u v hu hv e = narrow m u v hu hv (≐-trans (ι*-sem u) (≐-trans e (≐-sym (ι*-sem v))))
