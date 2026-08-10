------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger step 1 (§3): the Clifford action on the Pauli group.
--
-- The semantic model of a Clifford word is its conjugation action on the
-- ℤ/4-phased Pauli group P4 (= Selinger's P(n) modulo the global scalar
-- ω), namely `cact` from CliffordAction.  Soundness of the Figure-8
-- relations w.r.t. this action both establishes that Figure 8 presents (a
-- quotient of) the Clifford group and validates the transcription.
--
-- This file proves soundness of the "order" relations C2 (H²=1), C3
-- (S⁴=1) and C5 (CZ²=1); the two-qubit and three-qubit relations follow
-- in later files.  (C1/C4, being purely about the scalar ω, are invisible
-- to the ℤ/4 action and are validated by the ℤ/8 layer.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Selinger.Action where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using (_∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open PrimeModulus p-2 p-prime

import Examples.Groups.Symplectic.Syntactics p-2 p-prime as Syn
open Syn.Symplectic
  using (Gen ; gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate ; S ; H ; CZ ; ⊤⊥ ; ⊥⊤ ; _↑ ; _↓)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (Pauli)
open import Examples.Groups.Pauli.Qubit.SignedPauli using (Φ ; P4Carrier ; ι ; ι-+)
open import Examples.Groups.ProjectiveClifford.Qubit.CliffordAction using (cact ; cact1 ; δ ; incl)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime as Sem using ()
open Sem.Symplectic using (ap)
open Sem.Interpretation using (⟦_⟧)
open import Examples.Groups.ProjectiveClifford.Qubit.CliffordAut using (g4-id ; ι-2 ; neg-id)
-- X, Z and ω as SYMPLECTIC words.  Figure 8 now has its own gate set
-- (ExactGate, in which ω is a 0-ary generator), so ITS X and Z are words
-- over a different alphabet; `cact` is defined on Symplectic circuits,
-- which makes the mod-scalar copy the right source.  ω has no
-- mod-scalar counterpart — modulo scalars there is nothing for it to
-- name — so it is spelled out here as the word Figure 8 used to define
-- it to be.  Nothing below is about Figure 8's rule set: this module
-- only needs the words, to compute their P4-action.
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Figure8-Mod-Scalar
  p-2 p-prime using (X ; Z)

ω : ∀ {n} → Word (Gen (₁₊ n))
ω = (S • H) ^ 3

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- C3:  S⁴ = 1.  Exactly g4-id at the S generator.

c3-sound : (x : P4Carrier (₁₊ n)) → cact (S ^ 4) x ≡ x
c3-sound = g4-id (gate₁ S-gate)

------------------------------------------------------------------------
-- C2:  H² = 1.  H has P4-order 2 (H² = I on P4, phase included).

c2-sound : (x : P4Carrier (₁₊ n)) → cact (H ^ 2) x ≡ x
c2-sound (s , (a , b) ∷ ps) = Eq.cong₂ _,_ phase pauli
  where
  open Eq.≡-Reasoning
  -- phase: s + ι(a·b) + ι((-b)·a) ≡ s, the two ι's cancelling.
  phase : (s + ι (a * b)) + ι ((- b) * a) ≡ s
  phase = begin
    (s + ι (a * b)) + ι ((- b) * a)
      ≡⟨ +-assoc s (ι (a * b)) (ι ((- b) * a)) ⟩
    s + (ι (a * b) + ι ((- b) * a))
      ≡⟨ Eq.cong (λ □ → s + (ι (a * b) + ι □)) lemma ⟩
    s + (ι (a * b) + ι (a * b))
      ≡⟨ Eq.cong (s +_) (ι-2 (a * b)) ⟩
    s + ₀   ≡⟨ +-identityʳ s ⟩   s ∎
    where
    -- (-b)·a = a·b, using -x=x and commutativity at p=2.
    lemma : (- b) * a ≡ a * b
    lemma = begin
      (- b) * a   ≡⟨ Eq.cong (_* a) (neg-id b) ⟩
      b * a       ≡⟨ *-comm b a ⟩
      a * b       ∎
  pauli : ((- a) , (- b)) ∷ ps ≡ (a , b) ∷ ps
  pauli = Eq.cong (_∷ ps) (Eq.cong₂ _,_ (neg-id a) (neg-id b))

------------------------------------------------------------------------
-- C5:  CZ² = 1.  CZ has P4-order 2.

-- v + v = 0 at p = 2.
x+x : (v : ℤ ₚ) → v + v ≡ ₀
x+x ₀ = Eq.refl
x+x ₁ = Eq.refl

c5-sound : (x : P4Carrier (₂₊ n)) → cact (CZ ^ 2) x ≡ x
c5-sound (s , (a , b) ∷ (a' , b') ∷ ps) = Eq.cong₂ _,_ phase pauli
  where
  open Eq.≡-Reasoning
  phase : (s + ι (a * a')) + ι (a * a') ≡ s
  phase = begin
    (s + ι (a * a')) + ι (a * a')
      ≡⟨ +-assoc s (ι (a * a')) (ι (a * a')) ⟩
    s + (ι (a * a') + ι (a * a'))
      ≡⟨ Eq.cong (s +_) (ι-2 (a * a')) ⟩
    s + ₀   ≡⟨ +-identityʳ s ⟩   s ∎
  pauli : (a , b + a' + a') ∷ (a' , b' + a + a) ∷ ps
        ≡ (a , b) ∷ (a' , b') ∷ ps
  pauli = Eq.cong₂ (λ □ ▢ → (a , □) ∷ (a' , ▢) ∷ ps)
            (Eq.trans (+-assoc b a' a') (Eq.trans (Eq.cong (b +_) (x+x a')) (+-identityʳ b)))
            (Eq.trans (+-assoc b' a a) (Eq.trans (Eq.cong (b' +_) (x+x a)) (+-identityʳ b')))

------------------------------------------------------------------------
-- C6/C7:  S commutes with CZ (either wire).

-- Swap the last two summands: (s + x) + y ≡ (s + y) + x.
swap-add : ∀ {m} (s x y : ℤ m) → (s + x) + y ≡ (s + y) + x
swap-add s x y = Eq.trans (+-assoc s x y)
                 (Eq.trans (Eq.cong (s +_) (+-comm x y))
                           (Eq.sym (+-assoc s y x)))

-- C6:  S↓·CZ = CZ·S↓.  S on wire 0 is diagonal, hence commutes with CZ;
-- on the action the two conjugation phases and the two Z-updates just
-- swap order.
c6-sound : (x : P4Carrier (₂₊ n)) → cact (S ↓ • CZ) x ≡ cact (CZ • S ↓) x
c6-sound (s , (a , b) ∷ (a' , b') ∷ ps) = Eq.cong₂ _,_
  (swap-add s (ι (a * a')) (incl a))
  (Eq.cong (λ □ → (a , □) ∷ (a' , b' + a) ∷ ps) (swap-add b a' a))

-- C7:  S↑·CZ = CZ·S↑.  Same, with the roles of the two wires exchanged.
c7-sound : (x : P4Carrier (₂₊ n)) → cact (S ↑ • CZ) x ≡ cact (CZ • S ↑) x
c7-sound (s , (a , b) ∷ (a' , b') ∷ ps) = Eq.cong₂ _,_
  (swap-add s (ι (a * a')) (incl a'))
  (Eq.cong (λ □ → (a , b + a') ∷ (a' , □) ∷ ps) (swap-add b' a a'))

------------------------------------------------------------------------
-- The Pauli action of the derived Pauli words Z = SS and X = HSSH.
--
-- Conjugation by the Pauli Z (resp. X) fixes the symplectic part and
-- multiplies by (-1)^a (resp. (-1)^b), i.e. adds ι of the X- (resp. Z-)
-- exponent to the phase.  These are Selinger's Figure-2 rows for the
-- Pauli operators; they drive C8/C9 below and reappear in Step 2.

private
  open Eq.≡-Reasoning

  -- incl doubled is ι:  incl v + incl v = ι v  (×1 twice = ×2).
  incl-double : (v : ℤ ₚ) → incl v + incl v ≡ ι v
  incl-double ₀ = Eq.refl
  incl-double ₁ = Eq.refl

  -- (-b)·a = a·b  (at p = 2:  -x = x, and · commutes).
  neg-comm-mul : (a b : ℤ ₚ) → (- b) * a ≡ a * b
  neg-comm-mul a b = begin
    (- b) * a   ≡⟨ Eq.cong (_* a) (neg-id b) ⟩
    b * a       ≡⟨ *-comm b a ⟩
    a * b       ∎

  -- Commutative rearrangement of four summands.
  rearrangeQRP : ∀ {m} (s P Q R : ℤ m) → (s + P) + (Q + R) ≡ ((s + Q) + R) + P
  rearrangeQRP s P Q R = begin
    (s + P) + (Q + R)   ≡⟨ Eq.sym (+-assoc (s + P) Q R) ⟩
    ((s + P) + Q) + R   ≡⟨ Eq.cong (_+ R) (swap-add s P Q) ⟩
    ((s + Q) + P) + R   ≡⟨ swap-add (s + Q) P R ⟩
    ((s + Q) + R) + P   ∎

  rearrangeRQP : ∀ {m} (s P Q R : ℤ m) → (s + P) + (Q + R) ≡ ((s + R) + Q) + P
  rearrangeRQP s P Q R =
    Eq.trans (rearrangeQRP s P Q R) (Eq.cong (_+ P) (swap-add s Q R))

-- Z = SS on wire 0:  phase += ι(X-exponent a).
cact-Z↓ : (s : Φ) (a b : ℤ ₚ) (ps : Pauli n)
        → cact (Z ↓) (s , (a , b) ∷ ps) ≡ (s + ι a , (a , b) ∷ ps)
cact-Z↓ s a b ps = Eq.cong₂ _,_
  (Eq.trans (+-assoc s (incl a) (incl a)) (Eq.cong (s +_) (incl-double a)))
  (Eq.cong (λ □ → (a , □) ∷ ps)
   (Eq.trans (+-assoc b a a)
    (Eq.trans (Eq.cong (b +_) (x+x a)) (+-identityʳ b))))

-- Z = SS on wire 1.
cact-Z↑ : (s : Φ) (a b a' b' : ℤ ₚ) (ps : Pauli n)
        → cact (Z ↑) (s , (a , b) ∷ (a' , b') ∷ ps)
        ≡ (s + ι a' , (a , b) ∷ (a' , b') ∷ ps)
cact-Z↑ s a b a' b' ps = Eq.cong₂ _,_
  (Eq.trans (+-assoc s (incl a') (incl a')) (Eq.cong (s +_) (incl-double a')))
  (Eq.cong (λ □ → (a , b) ∷ (a' , □) ∷ ps)
   (Eq.trans (+-assoc b' a' a')
    (Eq.trans (Eq.cong (b' +_) (x+x a')) (+-identityʳ b'))))

-- X = HSSH on wire 0:  phase += ι(Z-exponent b).  (Proved through cact-Z↓,
-- since X = H·Z·H and Z ↓ = SS reduces definitionally.)
cact-X↓ : (s : Φ) (a b : ℤ ₚ) (ps : Pauli n)
        → cact (X ↓) (s , (a , b) ∷ ps) ≡ (s + ι b , (a , b) ∷ ps)
cact-X↓ s a b ps = begin
  cact (X ↓) (s , (a , b) ∷ ps)
    ≡⟨ Eq.cong (cact H) (cact-Z↓ (s + ι (a * b)) (- b) a ps) ⟩
  ((s + ι (a * b)) + ι (- b)) + ι ((- b) * a) , ((- a) , (- b)) ∷ ps
    ≡⟨ Eq.cong₂ _,_ phase pauli ⟩
  s + ι b , (a , b) ∷ ps ∎
  where
  pauli : ((- a) , (- b)) ∷ ps ≡ (a , b) ∷ ps
  pauli = Eq.cong (_∷ ps) (Eq.cong₂ _,_ (neg-id a) (neg-id b))
  cancel : ι (a * b) + ι ((- b) * a) ≡ ₀
  cancel = Eq.trans (Eq.cong (λ □ → ι (a * b) + ι □) (neg-comm-mul a b))
                    (ι-2 (a * b))
  phase : ((s + ι (a * b)) + ι (- b)) + ι ((- b) * a) ≡ s + ι b
  phase = begin
    ((s + ι (a * b)) + ι (- b)) + ι ((- b) * a)
      ≡⟨ Eq.cong (_+ ι ((- b) * a)) (swap-add s (ι (a * b)) (ι (- b))) ⟩
    ((s + ι (- b)) + ι (a * b)) + ι ((- b) * a)
      ≡⟨ +-assoc (s + ι (- b)) (ι (a * b)) (ι ((- b) * a)) ⟩
    (s + ι (- b)) + (ι (a * b) + ι ((- b) * a))
      ≡⟨ Eq.cong ((s + ι (- b)) +_) cancel ⟩
    (s + ι (- b)) + ₀
      ≡⟨ +-identityʳ (s + ι (- b)) ⟩
    s + ι (- b)   ≡⟨ Eq.cong (λ □ → s + ι □) (neg-id b) ⟩   s + ι b ∎

-- X = HSSH on wire 1.
cact-X↑ : (s : Φ) (a b a' b' : ℤ ₚ) (ps : Pauli n)
        → cact (X ↑) (s , (a , b) ∷ (a' , b') ∷ ps)
        ≡ (s + ι b' , (a , b) ∷ (a' , b') ∷ ps)
cact-X↑ s a b a' b' ps = begin
  cact (X ↑) (s , (a , b) ∷ (a' , b') ∷ ps)
    ≡⟨ Eq.cong (cact (H ↑)) (cact-Z↑ (s + ι (a' * b')) a b (- b') a' ps) ⟩
  ((s + ι (a' * b')) + ι (- b')) + ι ((- b') * a')
    , (a , b) ∷ ((- a') , (- b')) ∷ ps
    ≡⟨ Eq.cong₂ _,_ phase pauli ⟩
  s + ι b' , (a , b) ∷ (a' , b') ∷ ps ∎
  where
  pauli : (a , b) ∷ ((- a') , (- b')) ∷ ps ≡ (a , b) ∷ (a' , b') ∷ ps
  pauli = Eq.cong (λ □ → (a , b) ∷ □ ∷ ps) (Eq.cong₂ _,_ (neg-id a') (neg-id b'))
  cancel : ι (a' * b') + ι ((- b') * a') ≡ ₀
  cancel = Eq.trans (Eq.cong (λ □ → ι (a' * b') + ι □) (neg-comm-mul a' b'))
                    (ι-2 (a' * b'))
  phase : ((s + ι (a' * b')) + ι (- b')) + ι ((- b') * a') ≡ s + ι b'
  phase = begin
    ((s + ι (a' * b')) + ι (- b')) + ι ((- b') * a')
      ≡⟨ Eq.cong (_+ ι ((- b') * a')) (swap-add s (ι (a' * b')) (ι (- b'))) ⟩
    ((s + ι (- b')) + ι (a' * b')) + ι ((- b') * a')
      ≡⟨ +-assoc (s + ι (- b')) (ι (a' * b')) (ι ((- b') * a')) ⟩
    (s + ι (- b')) + (ι (a' * b') + ι ((- b') * a'))
      ≡⟨ Eq.cong ((s + ι (- b')) +_) cancel ⟩
    (s + ι (- b')) + ₀
      ≡⟨ +-identityʳ (s + ι (- b')) ⟩
    s + ι (- b')   ≡⟨ Eq.cong (λ □ → s + ι □) (neg-id b') ⟩   s + ι b' ∎

------------------------------------------------------------------------
-- C8/C9:  X through CZ picks up a Z on the other wire.

-- C8:  X↓·CZ = CZ·X↓·Z↑.  Both sides are routed to the common form
-- ((s+ιa')+ιb)+ι(aa') via the closed-form Pauli actions; the phases
-- match by commutative rearrangement (ι(b+a') = ιb + ιa').
c8-sound : (x : P4Carrier (₂₊ n)) → cact (X ↓ • CZ) x ≡ cact (CZ • X ↓ • Z ↑) x
c8-sound {n} (s , (a , b) ∷ (a' , b') ∷ ps) = Eq.trans lhs (Eq.sym rhs)
  where
  P Q R : Φ
  P = ι (a * a')
  Q = ι b
  R = ι a'
  mid : P4Carrier (₂₊ n)
  mid = ((s + R) + Q) + P , (a , b + a') ∷ (a' , b' + a) ∷ ps
  phase : (s + P) + ι (b + a') ≡ ((s + R) + Q) + P
  phase = begin
    (s + P) + ι (b + a')
      ≡⟨ Eq.cong ((s + P) +_) (ι-+ b a') ⟩
    (s + P) + (Q + R)
      ≡⟨ rearrangeRQP s P Q R ⟩
    ((s + R) + Q) + P ∎
  lhs : cact (X ↓ • CZ) (s , (a , b) ∷ (a' , b') ∷ ps) ≡ mid
  lhs = Eq.trans (cact-X↓ (s + P) a (b + a') ((a' , b' + a) ∷ ps))
                 (Eq.cong₂ _,_ phase Eq.refl)
  rhs : cact (CZ • X ↓ • Z ↑) (s , (a , b) ∷ (a' , b') ∷ ps) ≡ mid
  rhs = Eq.trans (Eq.cong (λ y → cact CZ (cact (X ↓) y)) (cact-Z↑ s a b a' b' ps))
                 (Eq.cong (cact CZ) (cact-X↓ (s + R) a b ((a' , b') ∷ ps)))

-- C9:  X↑·CZ = CZ·X↑·Z↓.  Mirror of C8 with the wires exchanged — the
-- right-hand side lists the acted Pauli first, as C8's does, so the two
-- proofs now have the same shape as well as the same content.  (It used
-- to read CZ·Z↓·X↑; the two differ by commuting Paulis on disjoint
-- wires, so only the bookkeeping order of their two phases changes.)
c9-sound : (x : P4Carrier (₂₊ n)) → cact (X ↑ • CZ) x ≡ cact (CZ • X ↑ • Z ↓) x
c9-sound {n} (s , (a , b) ∷ (a' , b') ∷ ps) = Eq.trans lhs (Eq.sym rhs)
  where
  P Q R : Φ
  P = ι (a * a')
  Q = ι b'
  R = ι a
  mid : P4Carrier (₂₊ n)
  mid = ((s + R) + Q) + P , (a , b + a') ∷ (a' , b' + a) ∷ ps
  phase : (s + P) + ι (b' + a) ≡ ((s + R) + Q) + P
  phase = begin
    (s + P) + ι (b' + a)
      ≡⟨ Eq.cong ((s + P) +_) (ι-+ b' a) ⟩
    (s + P) + (Q + R)
      ≡⟨ rearrangeRQP s P Q R ⟩
    ((s + R) + Q) + P ∎
  lhs : cact (X ↑ • CZ) (s , (a , b) ∷ (a' , b') ∷ ps) ≡ mid
  lhs = Eq.trans (cact-X↑ (s + P) a (b + a') a' (b' + a) ps)
                 (Eq.cong₂ _,_ phase Eq.refl)
  rhs : cact (CZ • X ↑ • Z ↓) (s , (a , b) ∷ (a' , b') ∷ ps) ≡ mid
  rhs = Eq.trans (Eq.cong (λ y → cact CZ (cact (X ↑) y))
                          (cact-Z↓ s a b ((a' , b') ∷ ps)))
                 (Eq.cong (cact CZ) (cact-X↑ (s + R) a b a' b' ps))

------------------------------------------------------------------------
-- C12:  CZ↑·CZ = CZ·CZ↑.  Both CZ's are diagonal, hence commute; on the
-- action the two phases and the wire-1 Z-update just swap order.

c12-sound : (x : P4Carrier (₃₊ n)) → cact (CZ ↑ • CZ) x ≡ cact (CZ • CZ ↑) x
c12-sound (s , (a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ ps) = Eq.cong₂ _,_
  (swap-add s (ι (a * a')) (ι (a' * a'')))
  (Eq.cong (λ □ → (a , b + a') ∷ (a' , □) ∷ (a'' , b'' + a') ∷ ps)
           (swap-add b' a a''))

------------------------------------------------------------------------
-- Phase additivity, and the Pauli component of cact.

-- The Pauli component of cact w is the phaseless action of w (so it does
-- not depend on the incoming phase).
cact-proj₂ : (w : Word (Gen n)) (x : P4Carrier n)
           → proj₂ (cact w x) ≡ ap ⟦ w ⟧ (proj₂ x)
cact-proj₂ [ g ]ʷ  (s , P) = Eq.refl
cact-proj₂ ε       (s , P) = Eq.refl
cact-proj₂ (w • v) x =
  Eq.trans (cact-proj₂ w (cact v x)) (Eq.cong (ap ⟦ w ⟧) (cact-proj₂ v x))

pauli-indep : (w : Word (Gen n)) (s : Φ) (P : Pauli n)
            → proj₂ (cact w (s , P)) ≡ proj₂ (cact w (₀ , P))
pauli-indep w s P = Eq.trans (cact-proj₂ w (s , P)) (Eq.sym (cact-proj₂ w (₀ , P)))

-- Running cact w from phase s adds s to the phase obtained from 0.
cact-phase : (w : Word (Gen n)) (s : Φ) (P : Pauli n)
           → proj₁ (cact w (s , P)) ≡ s + proj₁ (cact w (₀ , P))
cact-phase [ g ]ʷ s P = Eq.cong (s +_) (Eq.sym (+-identityˡ (δ g P)))
cact-phase ε       s P = Eq.sym (+-identityʳ s)
cact-phase (w • v) s P = begin
  proj₁ (cact w (cact v (s , P)))
    ≡⟨ cact-phase w (proj₁ (cact v (s , P))) (proj₂ (cact v (s , P))) ⟩
  proj₁ (cact v (s , P)) + proj₁ (cact w (₀ , proj₂ (cact v (s , P))))
    ≡⟨ Eq.cong₂ _+_ (cact-phase v s P)
         (Eq.cong (λ Q → proj₁ (cact w (₀ , Q))) (pauli-indep v s P)) ⟩
  (s + proj₁ (cact v (₀ , P))) + proj₁ (cact w (₀ , proj₂ (cact v (₀ , P))))
    ≡⟨ +-assoc s (proj₁ (cact v (₀ , P))) _ ⟩
  s + (proj₁ (cact v (₀ , P)) + proj₁ (cact w (₀ , proj₂ (cact v (₀ , P)))))
    ≡⟨ Eq.cong (s +_)
         (Eq.sym (cact-phase w (proj₁ (cact v (₀ , P))) (proj₂ (cact v (₀ , P))))) ⟩
  s + proj₁ (cact w (cact v (₀ , P))) ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- C1:  ω⁸ = 1.  ω = (SH)³ is the global scalar e^{iπ/4}; conjugation by a
-- scalar is trivial, so cact ω = id.  From the zero phase (fully concrete
-- in a, b) it reduces to refl; the general phase follows by additivity.

cact-ω₀ : (a b : ℤ ₚ) (ps : Pauli n) → cact ω (₀ , (a , b) ∷ ps) ≡ (₀ , (a , b) ∷ ps)
cact-ω₀ ₀ ₀ ps = Eq.refl
cact-ω₀ ₀ ₁ ps = Eq.refl
cact-ω₀ ₁ ₀ ps = Eq.refl
cact-ω₀ ₁ ₁ ps = Eq.refl

cact-ω : (x : P4Carrier (₁₊ n)) → cact ω x ≡ x
cact-ω (s , (a , b) ∷ ps) = Eq.cong₂ _,_
  (Eq.trans (cact-phase ω s ((a , b) ∷ ps))
   (Eq.trans (Eq.cong (s +_) (Eq.cong proj₁ (cact-ω₀ a b ps))) (+-identityʳ s)))
  (Eq.trans (pauli-indep ω s ((a , b) ∷ ps)) (Eq.cong proj₂ (cact-ω₀ a b ps)))

-- C1:  cact ω⁸ = id, by iterating cact-ω.  (w ^ 1 = w is a special case
-- of the power, so match 0 / 1 / 2+.)
cact-ω^ : (k : ℕ) (x : P4Carrier (₁₊ n)) → cact (ω ^ k) x ≡ x
cact-ω^ zero          x = Eq.refl
cact-ω^ (suc zero)    x = cact-ω x
cact-ω^ (suc (suc k)) x = Eq.trans (Eq.cong (cact ω) (cact-ω^ (suc k) x)) (cact-ω x)

c1-sound : (x : P4Carrier (₁₊ n)) → cact (ω ^ 8) x ≡ x
c1-sound = cact-ω^ 8

-- Phase machinery for lifting phase-0 equalities to all phases.
cact-lift : (w : Word (Gen n)) (s : Φ) (P : Pauli n)
          → cact w (s , P) ≡ (s + proj₁ (cact w (₀ , P)) , proj₂ (cact w (₀ , P)))
cact-lift w s P = Eq.cong₂ _,_ (cact-phase w s P) (pauli-indep w s P)

lift-eq : (u v : Word (Gen n)) (s : Φ) (P : Pauli n)
        → cact u (₀ , P) ≡ cact v (₀ , P)
        → cact u (s , P) ≡ cact v (s , P)
lift-eq u v s P base = begin
  cact u (s , P)                                              ≡⟨ cact-lift u s P ⟩
  s + proj₁ (cact u (₀ , P)) , proj₂ (cact u (₀ , P))
    ≡⟨ Eq.cong₂ (λ q Q → s + q , Q) (Eq.cong proj₁ base) (Eq.cong proj₂ base) ⟩
  s + proj₁ (cact v (₀ , P)) , proj₂ (cact v (₀ , P))        ≡⟨ Eq.sym (cact-lift v s P) ⟩
  cact v (s , P) ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- C13:  ⊤⊥↑·CZ↓·⊥⊤↑ = ⊥⊤↓·CZ↑·⊤⊥↓.  These words contain only H and CZ,
-- so cact-phase is cheap; the phase-0 identity holds on each of the 64
-- Pauli basis elements (all refl), and lift-eq lifts it to every phase.

c13-base : (P : Pauli (₃₊ n))
         → cact (⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑) (₀ , P) ≡ cact (⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓) (₀ , P)
c13-base ((₀ , ₀) ∷ (₀ , ₀) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₀ , ₀) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₀ , ₀) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₀ , ₀) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₀ , ₁) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₀ , ₁) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₀ , ₁) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₀ , ₁) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₁ , ₀) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₁ , ₀) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₁ , ₀) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₁ , ₀) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₁ , ₁) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₁ , ₁) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₁ , ₁) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₀) ∷ (₁ , ₁) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₀ , ₀) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₀ , ₀) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₀ , ₀) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₀ , ₀) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₀ , ₁) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₀ , ₁) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₀ , ₁) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₀ , ₁) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₁ , ₀) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₁ , ₀) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₁ , ₀) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₁ , ₀) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₁ , ₁) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₁ , ₁) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₁ , ₁) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₀ , ₁) ∷ (₁ , ₁) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₀ , ₀) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₀ , ₀) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₀ , ₀) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₀ , ₀) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₀ , ₁) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₀ , ₁) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₀ , ₁) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₀ , ₁) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₁ , ₀) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₁ , ₀) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₁ , ₀) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₁ , ₀) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₁ , ₁) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₁ , ₁) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₁ , ₁) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₀) ∷ (₁ , ₁) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₀ , ₀) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₀ , ₀) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₀ , ₀) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₀ , ₀) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₀ , ₁) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₀ , ₁) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₀ , ₁) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₀ , ₁) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₁ , ₀) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₁ , ₀) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₁ , ₀) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₁ , ₀) ∷ (₁ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₁ , ₁) ∷ (₀ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₁ , ₁) ∷ (₀ , ₁) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₁ , ₁) ∷ (₁ , ₀) ∷ ps) = Eq.refl
c13-base ((₁ , ₁) ∷ (₁ , ₁) ∷ (₁ , ₁) ∷ ps) = Eq.refl

c13-sound : (x : P4Carrier (₃₊ n))
          → cact (⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑) x ≡ cact (⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓) x
c13-sound (s , P) = lift-eq (⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑) (⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓) s P (c13-base P)
