------------------------------------------------------------------------
-- Presentations of groups
--
-- The equations of Item (a) of the Reidemeister–Schreier method
-- (Clément, Appendix A.3.2, the equations (DE-**))
--
-- The method's first family of obligations says that a letter of P is
-- recovered by running its image over the auxiliary generators through
-- the coset action, starting from the identity coset.  Reading the
-- table of Definition A.2 off, the four shapes give
--
--     (−1)_[a](−1)_[b]      ↦  ((−1)_[1](−1)_[a]) ((−1)_[1](−1)_[b])
--     (−1)_[c]X_[a,b]       ↦  ((−1)_[1](−1)_[c]) ((−1)_[1]X_[a,b])
--     X_[a,b]X_[c,d]        ↦  ((−1)_[u]X_[a,b]) ((−1)_[1]X_[c,d])
--     H_[a,b]H_[c,d]        ↦  (H_[a,b]H_[0,1]) (H_[0,1]H_[c,d])
--
-- (u being b, a or 1 according as a, b or neither is the index 1), and
-- each has to be derived from Figure 8.
--
-- The first is immediate: (20)–(22) say the signs are the group of
-- even-weight subsets, (21) being symmetry, (22) composition along a
-- shared index and (20) cancellation of a repeated one.
--
-- The second, `DE-ZX-all`, is nine cases.  (30) reaches the generic
-- one; every other turns on exchanging the two X indices of a mixed
-- letter, `flip′`, which Figure 8 states only for the case where the
-- sign is one of them, (33).  The general form is got by induction on
-- the gap between the indices: (25)–(28) shrink a pair by one index at
-- a time according to the parity of the gap, down to a gap of one,
-- where (23), (29) and (33) settle it.  The induction needs the
-- consecutive letter to be invertible on both sides, which (29) gives
-- on one side only and (23) supplies on the other — that is what lets
-- the twisted commutation (31) be turned round (`zz-past-L`).
--
-- The third, (DE-XX), needs the action of a mixed letter on the signs
-- by conjugation, which is the transposition of its two X indices.
-- For a consecutive letter that action is settled in all four cases —
-- `R-zz` and `R-zz′` for the two indices themselves, `R-zz-fix` for a
-- pair of spectators, `R-zz-own` for its own pair — and `conj-zz`
-- carries it to a general pair by the same Gray-code induction, with
-- `Tr-comp` composing the three transpositions of a step.  (34) then
-- splits the letter in two, `DE-ZX-all` moves the second one's sign
-- onto the index 1, and the action carries that sign across the first:
-- `DE-XX`, with `DE-XX-o₁` and `DE-XX-o₂` for the two cases where the
-- index 1 is itself one of the first X's indices.
--
-- The same induction, run a third time, gives the square of a mixed
-- letter (`zx²`, the general (23)) and hence that a letter and the one
-- with its X indices exchanged are inverse (`zx-inv`, the general
-- (29)).  So the whole mixed-letter fragment of Figure 8 is available
-- at arbitrary index pairs, which is what Item (b) will want for the
-- rules of Figure 7.
--
-- The fourth, (DE-HH), is the one obligation that turns on the
-- Hadamard rules rather than these.  (42) composes a Hadamard pair
-- through `twoSmallest`, two indices *fresh* for the four given ones,
-- whereas the coset action routes through the fixed pair 0 1 — and
-- those agree exactly when neither 0 nor 1 is among the four, which is
-- the case `DE-HH` proves.  There the work is arithmetic rather than
-- equational: make the boolean tests inside `twoSmallest` reduce, and
-- identify (42)'s ℕ-indexed letters with the `Fin`-indexed ones.
--
-- What is left of Item (a) is (DE-HH) when the four indices are all
-- distinct, where (42) does not apply at all, or when 0 or 1 is among
-- them, where the bridge pair is not the coset pair; both need the
-- pattern machinery of (35)–(37).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.DE (m : ℕ) where

open import Data.Bool using (true ; false)
open import Data.Maybe using (just)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax ; _,_ ; proj₁ ; proj₂)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ< ; toℕ<n ; toℕ-injective ; _≟_ ; fromℕ<-toℕ)
open import Data.Nat using (ℕ ; zero ; suc ; pred ; _<_ ; _≤_ ; _∸_ ; _<?_ ; z≤n ; s≤s ; _≡ᵇ_)
  renaming (_^_ to _^ℕ_)
open import Data.Nat.Properties
  using (suc-injective ; <-trans ; <-irrefl ; n<1+n ; ≤-pred ; ≤-antisym
        ; ≮⇒≥ ; ≤-<-trans ; ≤-trans ; ≤-refl ; n≤1+n ; <-cmp)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; subst₂)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

open import Presentation.Base as PB using ()

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8Free
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (parity)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.RS m using (o₁ ; z₀ ; z₀≢o₁ ; toℕ-z₀ ; toℕ-o₁)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; zx ; xx ; hh ; hhℕ ; zxℕ ; zzℕ ; toFin ; twoSmallest ; distinct4)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open Tools (m PF,_===_)
open import Examples.Groups.Real-Clifford+CH.WordAlgebra (m PF,_===_) using (comm-•)

------------------------------------------------------------------------
-- (DE-ZZ)

-- A sign pair is the pair through the index 1: (22) composes along it
-- and (21) puts the shared index first.
DE-ZZ : ∀ (a b : Fin _) → zz a b ≈ zz o₁ a • zz o₁ b
DE-ZZ a b = trans (sym (axiom (r22 a o₁ b))) (cong (axiom (r21 a o₁)) refl)

-- The sign pair on the index 1 twice over is trivial: (21), (22), (20).
private
  zz-o² : ∀ (a : Fin _) → zz o₁ a • zz o₁ a ≈ ε
  zz-o² a = trans (cong (axiom (r21 o₁ a)) refl)
                  (trans (axiom (r22 a o₁ a)) (axiom (r20 a)))

  -- Routing a sign pair through the index 1.
  zz-route : ∀ (c a : Fin _) → zz o₁ c • zz o₁ a ≈ zz c a
  zz-route c a = trans (cong (axiom (r21 o₁ c)) refl) (axiom (r22 c o₁ a))

------------------------------------------------------------------------
-- (DE-ZX), where the indices allow (30)
--
-- (30) peels the sign of a mixed letter onto the first index of its X,
-- so both sides reduce to zx a a b and what is left is a sign identity.
-- It needs all three indices distinct, so this is the case where c is
-- neither a nor b and the index 1 is neither either.

DE-ZX : ∀ (c a b : Fin _) → (a≢b : a ≢ b) → c ≢ a → c ≢ b → o₁ ≢ a → o₁ ≢ b →
        zx c a b ≈ zz o₁ c • zx o₁ a b
DE-ZX c a b a≢b c≢a c≢b o≢a o≢b =
  trans (axiom (r30 c a b a≢b c≢a c≢b))
  (trans (cong (sym (zz-route c a)) refl)
  (trans assoc
         (cong refl (sym (axiom (r30 o₁ a b a≢b o≢a o≢b))))))

-- The case c = a: the two sign pairs cancel outright.
DE-ZX-fix : ∀ (a b : Fin _) → (a≢b : a ≢ b) → o₁ ≢ a → o₁ ≢ b →
            zx a a b ≈ zz o₁ a • zx o₁ a b
DE-ZX-fix a b a≢b o≢a o≢b = sym
  (trans (cong refl (axiom (r30 o₁ a b a≢b o≢a o≢b)))
  (trans (sym assoc)
  (trans (cong (zz-o² a) refl) left-unit)))

------------------------------------------------------------------------
-- Exchanging the two X indices of a mixed letter
--
-- Every case of (DE-ZX) that (30) does not reach — c the second index
-- of the X, or the index 1 one of the two — comes down to moving the
-- sign across an exchange of the X indices:
--
--     zx a a b  ≈  zz a b • zx b b a.
--
-- For consecutive indices Figure 8 gives it outright: (23) says the
-- sign pair is the square of the mixed letter, (29) that the letter
-- and its index-exchanged partner are inverse, and (33) rewrites that
-- partner.  For a general pair it is the Gray-code transport of
-- (24)–(28), (31), (32), which is where the rest of Appendix A.4 goes.

zx-flip : ∀ (a a′ : Fin _) → Succ a a′ → zx a a a′ ≈ zz a a′ • zx a′ a′ a
zx-flip a a′ s = sym
  (trans (cong (axiom (r23 a a′ s)) refl)
  (trans assoc
  (trans (cong refl (cong refl (sym (axiom (r33 a′ a)))))
  (trans (cong refl (axiom (r29 a a′ s))) right-unit))))

-- Consecutive indices are distinct.
succ-≢ : ∀ {a a′ : Fin (2 ^ℕ (₃₊ m))} → Succ a a′ → a ≢ a′
succ-≢ {a} {a′} s e = n≢sn (Eq.trans (Eq.cong toℕ e) s)
  where
  n≢sn : ∀ {k} → k ≢ suc k
  n≢sn {suc k} e′ = n≢sn (suc-injective e′)

-- Hence the two X indices of a mixed letter may be exchanged, when
-- they are consecutive and the sign sits elsewhere: (30) reduces both
-- sides to a sign pair on a common letter, and `zx-flip` is the
-- discrepancy.
zx-sym : ∀ (d a a′ : Fin _) → Succ a a′ → d ≢ a → d ≢ a′ →
         zx d a a′ ≈ zx d a′ a
zx-sym d a a′ s d≢a d≢a′ =
  trans (axiom (r30 d a a′ (succ-≢ s) d≢a d≢a′))
  (trans (cong refl (zx-flip a a′ s))
  (trans (sym assoc)
  (trans (cong (axiom (r22 d a a′)) refl)
         (sym (axiom (r30 d a′ a (λ e → succ-≢ s (Eq.sym e)) d≢a′ d≢a))))))

------------------------------------------------------------------------
-- The consecutive letter is invertible
--
-- (29) says zx a a a′ has zx a′ a a′ as a right inverse; with (23),
-- which makes the sign pair its square, the two are also related by a
-- sign, and that gives the inverse on the left as well.  This is what
-- lets the twisted commutation (31) be turned round — the step the
-- Gray-code induction of (25)–(28) needs at every level.

-- A sign pair is an involution.
zz² : ∀ (a b : Fin _) → zz a b • zz a b ≈ ε
zz² a b = trans (cong refl (axiom (r21 a b)))
                (trans (axiom (r22 a b a)) (axiom (r20 a)))

-- The right inverse is the letter itself with its sign moved.
L-form : ∀ (a a′ : Fin _) → Succ a a′ → zx a′ a a′ ≈ zz a a′ • zx a a a′
L-form a a′ s =
  trans (sym left-unit)
  (trans (cong (sym (zz² a a′)) refl)
  (trans assoc
  (trans (cong refl (cong (axiom (r23 a a′ s)) refl))
  (trans (cong refl assoc)
  (trans (cong refl (cong refl (axiom (r29 a a′ s))))
         (cong refl right-unit))))))

-- So it is an inverse on the left too.
LR : ∀ (a a′ : Fin _) → Succ a a′ → zx a′ a a′ • zx a a a′ ≈ ε
LR a a′ s =
  trans (cong (L-form a a′ s) refl)
  (trans assoc
  (trans (cong refl (sym (axiom (r23 a a′ s)))) (zz² a a′)))

-- Hence (31) read the other way round.
zz-past-L : ∀ (a a′ c : Fin _) → Succ a a′ → c ≢ a → c ≢ a′ →
            zx a′ a a′ • zz a′ c ≈ zz a c • zx a′ a a′
zz-past-L a a′ c s c≢a c≢a′ =
  trans (sym right-unit)
  (trans (cong refl (sym (axiom (r29 a a′ s))))
  (trans assoc
  (trans (cong refl (sym assoc))
  (trans (cong refl (cong (axiom (r31 a a′ c s c≢a c≢a′)) refl))
  (trans (cong refl assoc)
  (trans (sym assoc)
  (trans (cong (LR a a′ s) refl) left-unit)))))))

------------------------------------------------------------------------
-- One step of the Gray-code induction
--
-- The two sign choices on a pair {a , c} are `zx a a c` and
-- `zx c a c`, and the claim relating them is
--
--     zx a a c  ≈  zz a c • zx c a c.
--
-- At even parity (25) and (26) decompose both over the *same* outer
-- letters — the consecutive letter and its inverse — with the claim at
-- {a′ , c} inside.  So the step applies the two decompositions, uses
-- the smaller claim, and carries the sign it produces out past the
-- outer letter, which is `zz-past-L`.

flip-step : ∀ (a a′ c : Fin (2 ^ℕ (₃₊ m))) (s : Succ a a′) →
            toℕ a′ < toℕ c → parity (toℕ c ∸ toℕ a) ≡ true →
            zx a′ a′ c ≈ zz a′ c • zx c a′ c →
            zx a a c ≈ zz a c • zx c a c
flip-step a a′ c s lt p ih =
  trans (axiom (r25 a a′ c s lt p))
  (trans (cong refl (cong ih refl))
  (trans (cong refl assoc)
  (trans (sym assoc)
  (trans (cong (zz-past-L a a′ c s c≢a c≢a′) refl)
  (trans assoc
         (cong refl (sym (axiom (r26 a a′ c s lt p)))))))))
  where
  c≢a′ : c ≢ a′
  c≢a′ e = <-irrefl (Eq.sym (Eq.cong toℕ e)) lt

  c≢a : c ≢ a
  c≢a e = <-irrefl (Eq.sym (Eq.cong toℕ e))
            (<-trans (Eq.subst (toℕ a <_) (Eq.sym s) (n<1+n (toℕ a))) lt)

-- The base of the induction: a gap of one, where `zx-flip` gives the
-- claim and (33) puts the inner letter into the shape the steps use.

flip-base : ∀ (a a′ : Fin (2 ^ℕ (₃₊ m))) → Succ a a′ →
            zx a a a′ ≈ zz a a′ • zx a′ a a′
flip-base a a′ s = trans (zx-flip a a′ s) (cong refl (sym (axiom (r33 a′ a))))

-- At odd parity (27) and (28) decompose over the letter of the pair
-- {c′ , c} at the *top*, which is a consecutive letter in the shape
-- (31) is stated for — so here the sign is carried out by (31) itself,
-- with (21) putting each pair the right way round.

flip-step′ : ∀ (a c′ c : Fin (2 ^ℕ (₃₊ m))) (s : Succ c′ c) →
             suc (toℕ a) < toℕ c → parity (toℕ c ∸ toℕ a) ≡ false →
             zx a a c′ ≈ zz a c′ • zx c′ a c′ →
             zx a a c ≈ zz a c • zx c a c
flip-step′ a c′ c s lt p ih =
  trans (axiom (r27 a c′ c s lt p))
  (trans (cong refl (cong ih refl))
  (trans (cong refl assoc)
  (trans (sym assoc)
  (trans (cong (sym twist) refl)
  (trans assoc
         (cong refl (sym (axiom (r28 a c′ c s lt p)))))))))
  where
  a<c : toℕ a < toℕ c
  a<c = <-trans (n<1+n (toℕ a)) lt

  a≢c : a ≢ c
  a≢c e = <-irrefl (Eq.cong toℕ e) a<c

  a<c′ : toℕ a < toℕ c′
  a<c′ = ≤-pred (Eq.subst (suc (toℕ a) <_) s lt)

  a≢c′ : a ≢ c′
  a≢c′ e = <-irrefl (Eq.cong toℕ e) a<c′

  twist : zz a c • zx c′ c′ c ≈ zx c′ c′ c • zz a c′
  twist = trans (cong (axiom (r21 a c)) refl)
                (trans (axiom (r31 c′ c a s a≢c′ a≢c))
                       (cong refl (axiom (r21 c′ a))))

------------------------------------------------------------------------
-- The general exchange, by induction on the gap
--
-- (25)–(28) shrink the pair {a , c} by one index at a time, according
-- to the parity of the gap: at even parity the lower index moves up,
-- at odd parity the upper index moves down.  Either way a gap of one
-- is reached, which is `flip-base`.  The recursion is on a fuel bound
-- for the gap, the indices being `Fin`s at a width with no literals.

-- The scaffolding is exported: every induction on the distance
-- between two indices needs the same pieces, and `NF` reuses them
-- to write a mixed letter as a product of consecutive ones.

N : ℕ
N = 2 ^ℕ (₃₊ m)

-- Neighbouring indices.
next : (a : Fin N) → suc (toℕ a) < N → Fin N
next a p = fromℕ< p

next-Succ : ∀ (a : Fin N) (p : suc (toℕ a) < N) → Succ a (next a p)
next-Succ a p = toℕ-fromℕ< p

pred≤′ : ∀ k → pred k ≤ k
pred≤′ zero    = z≤n
pred≤′ (suc k) = n≤1+n k

prev : Fin N → Fin N
prev c = fromℕ< (≤-<-trans (pred≤′ (toℕ c)) (toℕ<n c))

prev-toℕ : ∀ (c : Fin N) → toℕ (prev c) ≡ pred (toℕ c)
prev-toℕ c = toℕ-fromℕ< _

suc-pred′ : ∀ {k} → 0 < k → k ≡ suc (pred k)
suc-pred′ {zero}  ()
suc-pred′ {suc k} _ = Eq.refl

prev-Succ : ∀ (c : Fin N) → 0 < toℕ c → Succ (prev c) c
prev-Succ c p = Eq.trans (suc-pred′ p) (Eq.cong suc (Eq.sym (prev-toℕ c)))

-- Arithmetic of the gap.
∸suc : ∀ y x → y ∸ suc x ≡ pred (y ∸ x)
∸suc zero    zero    = Eq.refl
∸suc zero    (suc x) = Eq.refl
∸suc (suc y) zero    = Eq.refl
∸suc (suc y) (suc x) = ∸suc y x

suc∸ : ∀ n → suc n ∸ n ≡ 1
suc∸ zero    = Eq.refl
suc∸ (suc n) = suc∸ n

pred∸ : ∀ y x → pred y ∸ x ≡ pred (y ∸ x)
pred∸ zero    zero    = Eq.refl
pred∸ zero    (suc x) = Eq.refl
pred∸ (suc y) x       = ∸suc (suc y) x

pred≤pred : ∀ {x y} → x ≤ suc y → pred x ≤ y
pred≤pred {zero}  _         = z≤n
pred≤pred {suc x} (s≤s le)  = le

0<∸ : ∀ {x y} → x < y → 0 < y ∸ x
0<∸ {zero}  {suc y} (s≤s _)  = s≤s z≤n
0<∸ {suc x} {suc y} (s≤s lt) = 0<∸ lt

private
  -- The recursion.
  flip-fuel : ∀ (k : ℕ) (a c : Fin N) → toℕ a < toℕ c → toℕ c ∸ toℕ a ≤ k →
              zx a a c ≈ zz a c • zx c a c
  flip-fuel zero a c lt fu = ⊥-elim (<-irrefl Eq.refl (≤-trans (0<∸ lt) fu))
  flip-fuel (suc k) a c lt fu with suc (toℕ a) <? toℕ c
  ... | no ¬p = flip-base a c (≤-antisym (≮⇒≥ ¬p) lt)
  ... | yes p with parity (toℕ c ∸ toℕ a) in eq
  ...         | true  =
    let pa : suc (toℕ a) < N
        pa = <-trans p (toℕ<n c)
        a′ = next a pa
        sa : Succ a a′
        sa = next-Succ a pa
        lt′ : toℕ a′ < toℕ c
        lt′ = Eq.subst (_< toℕ c) (Eq.sym sa) p
        fu′ : toℕ c ∸ toℕ a′ ≤ k
        fu′ = Eq.subst (λ z → toℕ c ∸ z ≤ k) (Eq.sym sa)
                (Eq.subst (_≤ k) (Eq.sym (∸suc (toℕ c) (toℕ a))) (pred≤pred fu))
    in flip-step a a′ c sa lt′ eq (flip-fuel k a′ c lt′ fu′)
  ...         | false =
    let 0<c : 0 < toℕ c
        0<c = ≤-trans (s≤s z≤n) lt
        c′ = prev c
        sc : Succ c′ c
        sc = prev-Succ c 0<c
        lt″ : toℕ a < toℕ c′
        lt″ = ≤-pred (Eq.subst (suc (toℕ a) <_) sc p)
        fu″ : toℕ c′ ∸ toℕ a ≤ k
        fu″ = Eq.subst (λ z → z ∸ toℕ a ≤ k) (Eq.sym (prev-toℕ c))
                (Eq.subst (_≤ k) (Eq.sym (pred∸ (toℕ c) (toℕ a))) (pred≤pred fu))
    in flip-step′ a c′ c sc p eq (flip-fuel k a c′ lt″ fu″)

-- The two sign choices on a pair of indices differ by the sign pair.
flip : ∀ (a c : Fin N) → toℕ a < toℕ c → zx a a c ≈ zz a c • zx c a c
flip a c lt = flip-fuel (toℕ c ∸ toℕ a) a c lt ≤-refl

------------------------------------------------------------------------
-- The exchange, in the forms the case analysis needs

-- The two sign choices on a pair of distinct indices, in either order.
-- One way round is `flip` with (33); the other is that same statement
-- read backwards, the two sign pairs cancelling by (22) and (20).
flip′ : ∀ (a b : Fin N) → a ≢ b → zx a a b ≈ zz a b • zx b b a
flip′ a b a≢b with <-cmp (toℕ a) (toℕ b)
... | tri< lt _ _ = trans (flip a b lt) (cong refl (axiom (r33 b a)))
... | tri≈ _ e _  = ⊥-elim (a≢b (toℕ-injective e))
... | tri> _ _ gt = sym
      (trans (cong refl (trans (flip b a gt) (cong refl (axiom (r33 a b)))))
      (trans (sym assoc)
      (trans (cong (axiom (r22 a b a)) refl)
      (trans (cong (axiom (r20 a)) refl) left-unit))))

-- Hence the X indices may be exchanged whenever the sign sits outside
-- them: (30) on both sides, and `flip′` for the discrepancy.
zx-swap : ∀ (d a b : Fin N) → a ≢ b → d ≢ a → d ≢ b → zx d a b ≈ zx d b a
zx-swap d a b a≢b d≢a d≢b =
  trans (axiom (r30 d a b a≢b d≢a d≢b))
  (trans (cong refl (flip′ a b a≢b))
  (trans (sym assoc)
  (trans (cong (axiom (r22 d a b)) refl)
         (sym (axiom (r30 d b a (λ e → a≢b (Eq.sym e)) d≢b d≢a))))))

------------------------------------------------------------------------
-- (DE-ZX) in full
--
-- Five cases, by whether the sign index coincides with an X index and
-- whether the index 1 does.  The generic one is `DE-ZX`; the others
-- each collapse in two or three rules once `flip′` is available.

-- The sign index is the second X index.
DE-ZX-fix′ : ∀ (a b : Fin N) → (a≢b : a ≢ b) → o₁ ≢ a → o₁ ≢ b →
             zx b a b ≈ zz o₁ b • zx o₁ a b
DE-ZX-fix′ a b a≢b o≢a o≢b =
  trans (axiom (r33 b a))
  (trans (DE-ZX-fix b a (λ e → a≢b (Eq.sym e)) o≢b o≢a)
         (cong refl (sym (zx-swap o₁ a b a≢b o≢a o≢b))))

-- The index 1 is the first X index: (30) already produces the sign
-- pair wanted, up to (21).
DE-ZX-o₁ : ∀ (c b : Fin N) → (o≢b : o₁ ≢ b) → c ≢ o₁ → c ≢ b →
           zx c o₁ b ≈ zz o₁ c • zx o₁ o₁ b
DE-ZX-o₁ c b o≢b c≢o c≢b =
  trans (axiom (r30 c o₁ b o≢b c≢o c≢b))
        (cong (axiom (r21 c o₁)) refl)

-- The index 1 is the second X index.
DE-ZX-o₂ : ∀ (c a : Fin N) → (a≢o : a ≢ o₁) → c ≢ a → c ≢ o₁ →
           zx c a o₁ ≈ zz o₁ c • zx o₁ a o₁
DE-ZX-o₂ c a a≢o c≢a c≢o =
  trans (axiom (r30 c a o₁ a≢o c≢a c≢o))
  (trans (cong refl (flip′ a o₁ a≢o))
  (trans (sym assoc)
  (trans (cong (trans (axiom (r22 c a o₁)) (axiom (r21 c o₁))) refl)
         (cong refl (sym (axiom (r33 o₁ a)))))))

------------------------------------------------------------------------
-- (DE-ZX) assembled
--
-- Nine cases, by whether the index 1 is one of the two X indices and
-- whether the sign index is.  The four substantive ones are the
-- lemmas above; the rest are a sign pair on a repeated index, which
-- (20) kills, or the exchange `flip′`.

private
  -- The sign index is the second X index.
  flip-2 : ∀ (a b : Fin N) → a ≢ b → zx b a b ≈ zz a b • zx a a b
  flip-2 a b a≢b =
    trans (axiom (r33 b a))
    (trans (flip′ b a (λ e → a≢b (Eq.sym e)))
           (cong (axiom (r21 b a)) refl))

  -- A sign pair on a repeated index is the unit.
  drop : ∀ (x : Fin N) (w : Word (GenP (₃₊ m))) → w ≈ zz x x • w
  drop x w = sym (trans (cong (axiom (r20 x)) refl) left-unit)

DE-ZX-all : ∀ (c a b : Fin N) → a ≢ b → zx c a b ≈ zz o₁ c • zx o₁ a b
DE-ZX-all c a b a≢b with o₁ ≟ a | o₁ ≟ b
DE-ZX-all c a b a≢b | yes Eq.refl | _ with c ≟ o₁ | c ≟ b
DE-ZX-all c a b a≢b | yes Eq.refl | _ | yes Eq.refl | _ = drop o₁ (zx o₁ o₁ b)
DE-ZX-all c a b a≢b | yes Eq.refl | _ | no c≢o | yes Eq.refl = flip-2 o₁ c a≢b
DE-ZX-all c a b a≢b | yes Eq.refl | _ | no c≢o | no c≢b =
  DE-ZX-o₁ c b a≢b c≢o c≢b
DE-ZX-all c a b a≢b | no o≢a | yes Eq.refl with c ≟ a | c ≟ o₁
DE-ZX-all c a b a≢b | no o≢a | yes Eq.refl | yes Eq.refl | _ =
  trans (flip′ c o₁ a≢b) (cong (axiom (r21 c o₁)) (sym (axiom (r33 o₁ c))))
DE-ZX-all c a b a≢b | no o≢a | yes Eq.refl | no c≢a | yes Eq.refl =
  drop o₁ (zx o₁ a o₁)
DE-ZX-all c a b a≢b | no o≢a | yes Eq.refl | no c≢a | no c≢o =
  DE-ZX-o₂ c a a≢b c≢a c≢o
DE-ZX-all c a b a≢b | no o≢a | no o≢b with c ≟ a | c ≟ b
DE-ZX-all c a b a≢b | no o≢a | no o≢b | yes Eq.refl | _ =
  DE-ZX-fix a b a≢b o≢a o≢b
DE-ZX-all c a b a≢b | no o≢a | no o≢b | no c≢a | yes Eq.refl =
  DE-ZX-fix′ a b a≢b o≢a o≢b
DE-ZX-all c a b a≢b | no o≢a | no o≢b | no c≢a | no c≢b =
  DE-ZX c a b a≢b c≢a c≢b o≢a o≢b

------------------------------------------------------------------------
-- The signs form an abelian group
--
-- (22) composes two sign pairs along a shared index and has no side
-- condition, so any two sign pairs can be re-cut across each other;
-- with (21) that is commutativity, and (20) kills a repeated index.
-- This is the calculus every later step does its bookkeeping in.

-- Re-cutting a product of two sign pairs.
zz-split : ∀ (a b c d : Fin N) → zz a b • zz c d ≈ zz a c • zz b d
zz-split a b c d =
  trans (cong (sym (axiom (r22 a c b))) refl)
  (trans assoc
         (cong refl (trans (cong (axiom (r21 c b)) refl) (axiom (r22 b c d)))))

zz-comm : ∀ (a b c d : Fin N) → zz a b • zz c d ≈ zz c d • zz a b
zz-comm a b c d =
  trans (zz-split a b c d)
  (trans (cong (axiom (r21 a c)) (axiom (r21 b d)))
         (sym (zz-split c d a b)))

------------------------------------------------------------------------
-- Conjugating a sign by a consecutive mixed letter
--
-- (31) says the letter zx a a a′ carries the sign pair on a′ to the
-- one on a.  Read right to left it carries a to a′, and a sign pair on
-- two spectator indices it leaves alone — for that, cut the pair
-- through a with (22), move each half, and cut it back.  Together
-- these say conjugation by the letter acts on the signs as the
-- transposition of a and a′, which is what the Gray-code induction for
-- (DE-XX) has to propagate.

-- Right to left.
R-zz : ∀ (a a′ e : Fin N) → Succ a a′ → e ≢ a → e ≢ a′ →
       zx a a a′ • zz a e ≈ zz a′ e • zx a a a′
R-zz a a′ e s e≢a e≢a′ = sym (axiom (r31 a a′ e s e≢a e≢a′))

-- A spectator pair passes untouched.
R-zz-fix : ∀ (a a′ x y : Fin N) → Succ a a′ → x ≢ a → x ≢ a′ → y ≢ a → y ≢ a′ →
           zx a a a′ • zz x y ≈ zz x y • zx a a a′
R-zz-fix a a′ x y s x≢a x≢a′ y≢a y≢a′ =
  trans (cong refl (trans (sym (axiom (r22 x a y))) (cong (axiom (r21 x a)) refl)))
  (trans (sym assoc)
  (trans (cong (R-zz a a′ x s x≢a x≢a′) refl)
  (trans assoc
  (trans (cong refl (R-zz a a′ y s y≢a y≢a′))
  (trans (sym assoc)
         (cong (trans (cong (axiom (r21 a′ x)) refl) (axiom (r22 x a′ y))) refl))))))

-- Left to right: the letter carries the sign pair on a to the one on
-- a′.  (31) gives the opposite direction, so this goes through the
-- inverse — `L-form` turns the letter into a sign times its inverse,
-- `zz-past-L` moves the sign across that, and `zz-comm` tidies up.
R-zz′ : ∀ (a a′ y : Fin N) → Succ a a′ → y ≢ a → y ≢ a′ →
        zx a a a′ • zz a′ y ≈ zz a y • zx a a a′
R-zz′ a a′ y s y≢a y≢a′ =
  trans (cong R-form refl)
  (trans assoc
  (trans (cong refl (zz-past-L a a′ y s y≢a y≢a′))
  (trans (sym assoc)
  (trans (cong (zz-comm a a′ a y) refl)
  (trans assoc
         (cong refl (sym R-form)))))))
  where
  R-form : zx a a a′ ≈ zz a a′ • zx a′ a a′
  R-form =
    trans (sym left-unit)
    (trans (cong (sym (zz² a a′)) refl)
    (trans assoc
           (cong refl (sym (L-form a a′ s)))))

-- The letter commutes with its own sign pair, which by (23) is its
-- square.
R-zz-own : ∀ (a a′ : Fin N) → Succ a a′ →
           zx a a a′ • zz a a′ ≈ zz a a′ • zx a a a′
R-zz-own a a′ s =
  trans (cong refl (axiom (r23 a a′ s)))
  (trans (sym assoc)
         (cong (sym (axiom (r23 a a′ s))) refl))

------------------------------------------------------------------------
-- Conjugating a sign by a mixed letter
--
-- A mixed letter acts on the signs by conjugation as the transposition
-- of its two X indices.  That is what (DE-XX) needs, and proving it in
-- general is the Gray-code induction a second time.
--
-- The transposition is carried as a relation, and one that states its
-- equations rather than fixing them as indices: `Fin`'s decidable
-- equality does not reduce at a symbolic width, so a function would be
-- stuck in every goal, and with K disabled an indexed family cannot be
-- matched on where two of its indices coincide.

data Tr (a c x x′ : Fin N) : Set where
  tr-l : x ≡ a → x′ ≡ c → Tr a c x x′
  tr-r : x ≡ c → x′ ≡ a → Tr a c x x′
  tr-o : x ≢ a → x ≢ c → x′ ≡ x → Tr a c x x′

-- Every sign pair factors through a chosen index: (22) and (21), with
-- no side condition.
zz-pivot : ∀ (w x y : Fin N) → zz x y ≈ zz w x • zz w y
zz-pivot w x y =
  trans (sym (axiom (r22 x w y))) (cong (axiom (r21 x w)) refl)

-- The action of a consecutive letter on a pair pivoted at its lower
-- index: its own pair, the pair on the two indices, or a spectator.
R-act : ∀ (a a′ x x′ : Fin N) → Succ a a′ → Tr a a′ x x′ →
        zx a a a′ • zz a x ≈ zz a′ x′ • zx a a a′
R-act a a′ x x′ s (tr-l Eq.refl Eq.refl) =
  trans (cong refl (axiom (r20 a)))
  (trans right-unit (sym (trans (cong (axiom (r20 a′)) refl) left-unit)))
R-act a a′ x x′ s (tr-r Eq.refl Eq.refl) =
  trans (R-zz-own a a′ s) (cong (axiom (r21 a a′)) refl)
R-act a a′ x x′ s (tr-o x≢a x≢a′ Eq.refl) = R-zz a a′ x s x≢a x≢a′

-- Hence on any pair.
R-act₂ : ∀ (a a′ x y x′ y′ : Fin N) → Succ a a′ →
         Tr a a′ x x′ → Tr a a′ y y′ →
         zx a a a′ • zz x y ≈ zz x′ y′ • zx a a a′
R-act₂ a a′ x y x′ y′ s tx ty =
  trans (cong refl (zz-pivot a x y))
  (trans (sym assoc)
  (trans (cong (R-act a a′ x x′ s tx) refl)
  (trans assoc
  (trans (cong refl (R-act a a′ y y′ s ty))
  (trans (sym assoc)
         (cong (sym (zz-pivot a′ x′ y′)) refl))))))

-- The inverse letter acts the same way, being the letter times a sign,
-- and signs commute.
L-act₂ : ∀ (a a′ x y x′ y′ : Fin N) → Succ a a′ →
         Tr a a′ x x′ → Tr a a′ y y′ →
         zx a′ a a′ • zz x y ≈ zz x′ y′ • zx a′ a a′
L-act₂ a a′ x y x′ y′ s tx ty =
  trans (cong (L-form a a′ s) refl)
  (trans assoc
  (trans (cong refl (R-act₂ a a′ x y x′ y′ s tx ty))
  (trans (sym assoc)
  (trans (cong (zz-comm a a′ x′ y′) refl)
  (trans assoc
         (cong refl (sym (L-form a a′ s))))))))

------------------------------------------------------------------------
-- Composing the transpositions of one induction step
--
-- The even step conjugates by the letter's own pair, then the smaller
-- pair, then the letter's own pair again: (a a′)(a′ c)(a a′) = (a c).
-- Every case that does not arise is ruled out by one of the three
-- distinctness hypotheses.

Tr-comp : ∀ {a a′ c x u v w} → a ≢ a′ → a ≢ c → a′ ≢ c →
          Tr a a′ x u → Tr a′ c u v → Tr a a′ v w → Tr a c x w
-- x is the lower index of the letter.
Tr-comp a≢a′ a≢c a′≢c (tr-l x≡a u≡a′) (tr-l _ v≡c) (tr-l v≡a _) =
  ⊥-elim (a≢c (Eq.trans (Eq.sym v≡a) v≡c))
Tr-comp a≢a′ a≢c a′≢c (tr-l x≡a u≡a′) (tr-l _ v≡c) (tr-r v≡a′ _) =
  ⊥-elim (a′≢c (Eq.trans (Eq.sym v≡a′) v≡c))
Tr-comp a≢a′ a≢c a′≢c (tr-l x≡a u≡a′) (tr-l _ v≡c) (tr-o _ _ w≡v) =
  tr-l x≡a (Eq.trans w≡v v≡c)
Tr-comp a≢a′ a≢c a′≢c (tr-l x≡a u≡a′) (tr-r u≡c _) _ =
  ⊥-elim (a′≢c (Eq.trans (Eq.sym u≡a′) u≡c))
Tr-comp a≢a′ a≢c a′≢c (tr-l x≡a u≡a′) (tr-o u≢a′ _ _) _ =
  ⊥-elim (u≢a′ u≡a′)
-- x is the upper index.
Tr-comp a≢a′ a≢c a′≢c (tr-r x≡a′ u≡a) (tr-l u≡a′ _) _ =
  ⊥-elim (a≢a′ (Eq.trans (Eq.sym u≡a) u≡a′))
Tr-comp a≢a′ a≢c a′≢c (tr-r x≡a′ u≡a) (tr-r u≡c _) _ =
  ⊥-elim (a≢c (Eq.trans (Eq.sym u≡a) u≡c))
Tr-comp a≢a′ a≢c a′≢c (tr-r x≡a′ u≡a) (tr-o _ _ v≡u) (tr-l _ w≡a′) =
  tr-o (λ e → a≢a′ (Eq.trans (Eq.sym e) x≡a′))
       (λ e → a′≢c (Eq.trans (Eq.sym x≡a′) e))
       (Eq.trans w≡a′ (Eq.sym x≡a′))
Tr-comp a≢a′ a≢c a′≢c (tr-r x≡a′ u≡a) (tr-o _ _ v≡u) (tr-r v≡a′ _) =
  ⊥-elim (a≢a′ (Eq.trans (Eq.sym (Eq.trans v≡u u≡a)) v≡a′))
Tr-comp a≢a′ a≢c a′≢c (tr-r x≡a′ u≡a) (tr-o _ _ v≡u) (tr-o v≢a _ _) =
  ⊥-elim (v≢a (Eq.trans v≡u u≡a))
-- x is a spectator of the letter's own pair.
Tr-comp a≢a′ a≢c a′≢c (tr-o x≢a x≢a′ u≡x) (tr-l u≡a′ _) _ =
  ⊥-elim (x≢a′ (Eq.trans (Eq.sym u≡x) u≡a′))
Tr-comp a≢a′ a≢c a′≢c (tr-o x≢a x≢a′ u≡x) (tr-r u≡c v≡a′) (tr-l v≡a _) =
  ⊥-elim (a≢a′ (Eq.trans (Eq.sym v≡a) v≡a′))
Tr-comp a≢a′ a≢c a′≢c (tr-o x≢a x≢a′ u≡x) (tr-r u≡c v≡a′) (tr-r _ w≡a) =
  tr-r (Eq.trans (Eq.sym u≡x) u≡c) w≡a
Tr-comp a≢a′ a≢c a′≢c (tr-o x≢a x≢a′ u≡x) (tr-r u≡c v≡a′) (tr-o _ v≢a′ _) =
  ⊥-elim (v≢a′ v≡a′)
Tr-comp a≢a′ a≢c a′≢c (tr-o x≢a x≢a′ u≡x) (tr-o _ u≢c v≡u) (tr-l v≡a _) =
  ⊥-elim (x≢a (Eq.trans (Eq.sym (Eq.trans v≡u u≡x)) v≡a))
Tr-comp a≢a′ a≢c a′≢c (tr-o x≢a x≢a′ u≡x) (tr-o _ u≢c v≡u) (tr-r v≡a′ _) =
  ⊥-elim (x≢a′ (Eq.trans (Eq.sym (Eq.trans v≡u u≡x)) v≡a′))
Tr-comp a≢a′ a≢c a′≢c (tr-o x≢a x≢a′ u≡x) (tr-o _ u≢c v≡u) (tr-o _ _ w≡v) =
  tr-o x≢a (λ e → u≢c (Eq.trans u≡x e))
       (Eq.trans w≡v (Eq.trans v≡u u≡x))

-- The transposition is symmetric in its pair.
Tr-swap : ∀ {a c x x′} → Tr a c x x′ → Tr c a x x′
Tr-swap (tr-l x≡a x′≡c) = tr-r x≡a x′≡c
Tr-swap (tr-r x≡c x′≡a) = tr-l x≡c x′≡a
Tr-swap (tr-o x≢a x≢c e) = tr-o x≢c x≢a e

-- Where an index goes.
tr-dec : ∀ (a c x : Fin N) → Σ[ x′ ∈ Fin N ] Tr a c x x′
tr-dec a c x with x ≟ a
... | yes e = c , tr-l e Eq.refl
... | no x≢a with x ≟ c
...          | yes e = a , tr-r e Eq.refl
...          | no x≢c = x , tr-o x≢a x≢c Eq.refl

-- What conjugating a sign pair by the letter on {a , c} produces.
record Conj (a c x y : Fin N) : Set where
  constructor conj
  field
    fst snd : Fin N
    trx : Tr a c x fst
    try : Tr a c y snd
    law : zx a a c • zz x y ≈ zz fst snd • zx a a c

------------------------------------------------------------------------
-- The induction
--
-- Exactly the shape of `flip-fuel`: the same two decompositions, the
-- same fuel on the gap.  What travels through is a sign pair, and each
-- of the three letters of a decomposition transposes it, the composite
-- being the transposition of the whole pair (`Tr-comp`).

private
  conj-fuel : ∀ (k : ℕ) (a c : Fin N) → toℕ a < toℕ c → toℕ c ∸ toℕ a ≤ k →
              ∀ (x y : Fin N) → Conj a c x y
  conj-fuel zero a c lt fu x y = ⊥-elim (<-irrefl Eq.refl (≤-trans (0<∸ lt) fu))
  conj-fuel (suc k) a c lt fu x y with suc (toℕ a) <? toℕ c
  ... | no ¬p =
    let s : Succ a c
        s = ≤-antisym (≮⇒≥ ¬p) lt
        (x′ , tx) = tr-dec a c x
        (y′ , ty) = tr-dec a c y
    in conj x′ y′ tx ty (R-act₂ a c x y x′ y′ s tx ty)
  ... | yes p with parity (toℕ c ∸ toℕ a) in eq
  ...         | true =
    let pa : suc (toℕ a) < N
        pa = <-trans p (toℕ<n c)
        a′ = next a pa
        s : Succ a a′
        s = next-Succ a pa
        lt′ : toℕ a′ < toℕ c
        lt′ = Eq.subst (_< toℕ c) (Eq.sym s) p
        fu′ : toℕ c ∸ toℕ a′ ≤ k
        fu′ = Eq.subst (λ z → toℕ c ∸ z ≤ k) (Eq.sym s)
                (Eq.subst (_≤ k) (Eq.sym (∸suc (toℕ c) (toℕ a))) (pred≤pred fu))
        a≢a′ = succ-≢ s
        a≢c  = λ e → <-irrefl (Eq.cong toℕ e) (<-trans (n<1+n (toℕ a)) p)
        a′≢c = λ e → <-irrefl (Eq.cong toℕ e) lt′
        (x₁ , t₁) = tr-dec a a′ x
        (y₁ , u₁) = tr-dec a a′ y
        ih = conj-fuel k a′ c lt′ fu′ x₁ y₁
        x₂ = Conj.fst ih ; y₂ = Conj.snd ih
        (x₃ , t₃) = tr-dec a a′ x₂
        (y₃ , u₃) = tr-dec a a′ y₂
    in conj x₃ y₃ (Tr-comp a≢a′ a≢c a′≢c t₁ (Conj.trx ih) t₃)
                  (Tr-comp a≢a′ a≢c a′≢c u₁ (Conj.try ih) u₃)
       (trans (cong (axiom (r25 a a′ c s lt′ eq)) refl)
       (trans assoc
       (trans (cong refl assoc)
       (trans (cong refl (cong refl (R-act₂ a a′ x y x₁ y₁ s t₁ u₁)))
       (trans (cong refl (sym assoc))
       (trans (cong refl (cong (Conj.law ih) refl))
       (trans (cong refl assoc)
       (trans (sym assoc)
       (trans (cong (L-act₂ a a′ x₂ y₂ x₃ y₃ s t₃ u₃) refl)
       (trans assoc
              (cong refl (sym (axiom (r25 a a′ c s lt′ eq))))))))))))))
  ...         | false =
    let 0<c : 0 < toℕ c
        0<c = ≤-trans (s≤s z≤n) lt
        c′ = prev c
        s : Succ c′ c
        s = prev-Succ c 0<c
        lt″ : toℕ a < toℕ c′
        lt″ = ≤-pred (Eq.subst (suc (toℕ a) <_) s p)
        fu″ : toℕ c′ ∸ toℕ a ≤ k
        fu″ = Eq.subst (λ z → z ∸ toℕ a ≤ k) (Eq.sym (prev-toℕ c))
                (Eq.subst (_≤ k) (Eq.sym (pred∸ (toℕ c) (toℕ a))) (pred≤pred fu))
        c≢c′ = λ e → succ-≢ s (Eq.sym e)
        c≢a  = λ e → <-irrefl (Eq.sym (Eq.cong toℕ e)) (<-trans (n<1+n (toℕ a)) p)
        c′≢a = λ e → <-irrefl (Eq.sym (Eq.cong toℕ e)) lt″
        (x₁ , t₁) = tr-dec c′ c x
        (y₁ , u₁) = tr-dec c′ c y
        ih = conj-fuel k a c′ lt″ fu″ x₁ y₁
        x₂ = Conj.fst ih ; y₂ = Conj.snd ih
        (x₃ , t₃) = tr-dec c′ c x₂
        (y₃ , u₃) = tr-dec c′ c y₂
    in conj x₃ y₃
       (Tr-swap (Tr-comp c≢c′ c≢a c′≢a (Tr-swap t₁) (Tr-swap (Conj.trx ih)) (Tr-swap t₃)))
       (Tr-swap (Tr-comp c≢c′ c≢a c′≢a (Tr-swap u₁) (Tr-swap (Conj.try ih)) (Tr-swap u₃)))
       (trans (cong (axiom (r27 a c′ c s p eq)) refl)
       (trans assoc
       (trans (cong refl assoc)
       (trans (cong refl (cong refl (L-act₂ c′ c x y x₁ y₁ s t₁ u₁)))
       (trans (cong refl (sym assoc))
       (trans (cong refl (cong (Conj.law ih) refl))
       (trans (cong refl assoc)
       (trans (sym assoc)
       (trans (cong (R-act₂ c′ c x₂ y₂ x₃ y₃ s t₃ u₃) refl)
       (trans assoc
              (cong refl (sym (axiom (r27 a c′ c s p eq))))))))))))))

-- A mixed letter conjugates a sign pair by transposing its X indices.
conj-zz : ∀ (a c x y : Fin N) → toℕ a < toℕ c → Conj a c x y
conj-zz a c x y lt = conj-fuel (toℕ c ∸ toℕ a) a c lt ≤-refl x y

-- Either order of the pair: for the other one the letter is a sign
-- times the letter on the reversed pair, and signs commute.
conj-any : ∀ (a b x y : Fin N) → a ≢ b → Conj a b x y
conj-any a b x y a≢b with <-cmp (toℕ a) (toℕ b)
... | tri< lt _ _ = conj-zz a b x y lt
... | tri≈ _ e _  = ⊥-elim (a≢b (toℕ-injective e))
... | tri> _ _ gt =
  let cj = conj-zz b a x y gt
      f = Conj.fst cj
      s = Conj.snd cj
  in conj f s (Tr-swap (Conj.trx cj)) (Tr-swap (Conj.try cj))
       (trans (cong (flip′ a b a≢b) refl)
       (trans assoc
       (trans (cong refl (Conj.law cj))
       (trans (sym assoc)
       (trans (cong (zz-comm a b f s) refl)
       (trans assoc
              (cong refl (sym (flip′ a b a≢b)))))))))

------------------------------------------------------------------------
-- (DE-XX), where the index 1 is outside the first X
--
-- (34) splits the letter into two mixed ones, `DE-ZX-all` moves the
-- sign of the second onto the index 1, and the sign so produced is
-- carried across the first by the conjugation action — which, the
-- index 1 being a spectator, exchanges only the two X indices.  (30)
-- then reassembles the first factor.

private
  -- Reading the conjugation action off in the case at hand.
  xx-twist′ : ∀ (a b f s : Fin N) → a ≢ b → o₁ ≢ a → o₁ ≢ b →
              Tr a b o₁ f → Tr a b b s →
              zx a a b • zz o₁ b ≈ zz f s • zx a a b →
              zx a a b • zz o₁ b ≈ zz o₁ a • zx a a b
  xx-twist′ a b f s a≢b o≢a o≢b (tr-l o≡a _) _ law = ⊥-elim (o≢a o≡a)
  xx-twist′ a b f s a≢b o≢a o≢b (tr-r o≡b _) _ law = ⊥-elim (o≢b o≡b)
  xx-twist′ a b .o₁ s a≢b o≢a o≢b (tr-o _ _ Eq.refl) (tr-l b≡a _) law =
    ⊥-elim (a≢b (Eq.sym b≡a))
  xx-twist′ a b .o₁ .a a≢b o≢a o≢b (tr-o _ _ Eq.refl) (tr-r _ Eq.refl) law = law
  xx-twist′ a b .o₁ s a≢b o≢a o≢b (tr-o _ _ Eq.refl) (tr-o _ b≢b _) law =
    ⊥-elim (b≢b Eq.refl)

xx-twist : ∀ (a b : Fin N) → a ≢ b → o₁ ≢ a → o₁ ≢ b →
           zx a a b • zz o₁ b ≈ zz o₁ a • zx a a b
xx-twist a b a≢b o≢a o≢b =
  xx-twist′ a b (Conj.fst cj) (Conj.snd cj) a≢b o≢a o≢b
            (Conj.trx cj) (Conj.try cj) (Conj.law cj)
  where cj = conj-any a b o₁ b a≢b

DE-XX : ∀ (a b c d : Fin N) → (a≢b : a ≢ b) → c ≢ d → o₁ ≢ a → o₁ ≢ b →
        xx a b c d ≈ zx o₁ a b • zx o₁ c d
DE-XX a b c d a≢b c≢d o≢a o≢b =
  trans (axiom (r34 a b c d a≢b c≢d))
  (trans (cong refl (DE-ZX-all b c d c≢d))
  (trans (sym assoc)
  (trans (cong (xx-twist a b a≢b o≢a o≢b) refl)
         (cong (sym (axiom (r30 o₁ a b a≢b o≢a o≢b))) refl))))

------------------------------------------------------------------------
-- (DE-XX), where the index 1 is one of the first X's indices

-- A mixed letter commutes with its own sign pair: the conjugation
-- action exchanges the two indices, and (21) puts them back.
private
  zx-own′ : ∀ (a b f s : Fin N) → a ≢ b → Tr a b a f → Tr a b b s →
            zx a a b • zz a b ≈ zz f s • zx a a b →
            zx a a b • zz a b ≈ zz a b • zx a a b
  zx-own′ a b f s a≢b (tr-r a≡b _) _ law = ⊥-elim (a≢b a≡b)
  zx-own′ a b f s a≢b (tr-o a≢a _ _) _ law = ⊥-elim (a≢a Eq.refl)
  zx-own′ a b .b s a≢b (tr-l _ Eq.refl) (tr-l b≡a _) law =
    ⊥-elim (a≢b (Eq.sym b≡a))
  zx-own′ a b .b .a a≢b (tr-l _ Eq.refl) (tr-r _ Eq.refl) law =
    trans law (cong (axiom (r21 b a)) refl)
  zx-own′ a b .b s a≢b (tr-l _ Eq.refl) (tr-o _ b≢b _) law =
    ⊥-elim (b≢b Eq.refl)

zx-own : ∀ (a b : Fin N) → a ≢ b → zx a a b • zz a b ≈ zz a b • zx a a b
zx-own a b a≢b =
  zx-own′ a b (Conj.fst cj) (Conj.snd cj) a≢b
          (Conj.trx cj) (Conj.try cj) (Conj.law cj)
  where cj = conj-any a b a b a≢b

-- The index 1 is the second index of the first X: (34) is already the
-- statement, the coset action having put the sign there.
DE-XX-o₂ : ∀ (a c d : Fin N) → (a≢o : a ≢ o₁) → c ≢ d →
           xx a o₁ c d ≈ zx a a o₁ • zx o₁ c d
DE-XX-o₂ a c d a≢o c≢d = axiom (r34 a o₁ c d a≢o c≢d)

-- The index 1 is the first: here the sign produced by `DE-ZX-all` is
-- the letter's own pair, so it simply commutes across.
DE-XX-o₁ : ∀ (b c d : Fin N) → (o≢b : o₁ ≢ b) → c ≢ d →
           xx o₁ b c d ≈ zx b o₁ b • zx o₁ c d
DE-XX-o₁ b c d o≢b c≢d =
  trans (axiom (r34 o₁ b c d o≢b c≢d))
  (trans (cong refl (DE-ZX-all b c d c≢d))
  (trans (sym assoc)
         (cong (trans (zx-own o₁ b o≢b) (sym (flip-2 o₁ b o≢b))) refl)))

------------------------------------------------------------------------
-- The square of a mixed letter
--
-- (23) says the square of a consecutive mixed letter is the sign pair
-- on its two indices.  In general it is the same Gray-code induction a
-- third time, and a short one: in a decomposition L M R the inner R L
-- cancels between the two copies, leaving L (M M) R; the induction
-- hypothesis turns the middle into a sign, which the outer letter
-- carries out, and L R then cancels too.

private
  sq-fuel : ∀ (k : ℕ) (a c : Fin N) → toℕ a < toℕ c → toℕ c ∸ toℕ a ≤ k →
            zx a a c • zx a a c ≈ zz a c
  sq-fuel zero a c lt fu = ⊥-elim (<-irrefl Eq.refl (≤-trans (0<∸ lt) fu))
  sq-fuel (suc k) a c lt fu with suc (toℕ a) <? toℕ c
  ... | no ¬p = sym (axiom (r23 a c (≤-antisym (≮⇒≥ ¬p) lt)))
  ... | yes p with parity (toℕ c ∸ toℕ a) in eq
  ...         | true =
    let pa : suc (toℕ a) < N
        pa = <-trans p (toℕ<n c)
        a′ = next a pa
        s : Succ a a′
        s = next-Succ a pa
        lt′ : toℕ a′ < toℕ c
        lt′ = Eq.subst (_< toℕ c) (Eq.sym s) p
        fu′ : toℕ c ∸ toℕ a′ ≤ k
        fu′ = Eq.subst (λ z → toℕ c ∸ z ≤ k) (Eq.sym s)
                (Eq.subst (_≤ k) (Eq.sym (∸suc (toℕ c) (toℕ a))) (pred≤pred fu))
        c≢a  = λ e → <-irrefl (Eq.sym (Eq.cong toℕ e)) (<-trans (n<1+n (toℕ a)) p)
        c≢a′ = λ e → <-irrefl (Eq.sym (Eq.cong toℕ e)) lt′
        dec  = axiom (r25 a a′ c s lt′ eq)
    in trans (cong dec dec)
       (trans assoc
       (trans (cong refl assoc)
       (trans (cong refl (cong refl (sym assoc)))
       (trans (cong refl (cong refl (cong (axiom (r29 a a′ s)) refl)))
       (trans (cong refl (cong refl left-unit))
       (trans (cong refl (sym assoc))
       (trans (cong refl (cong (sq-fuel k a′ c lt′ fu′) refl))
       (trans (sym assoc)
       (trans (cong (zz-past-L a a′ c s c≢a c≢a′) refl)
       (trans assoc
       (trans (cong refl (LR a a′ s)) right-unit)))))))))))
  ...         | false =
    let 0<c : 0 < toℕ c
        0<c = ≤-trans (s≤s z≤n) lt
        c′ = prev c
        s : Succ c′ c
        s = prev-Succ c 0<c
        lt″ : toℕ a < toℕ c′
        lt″ = ≤-pred (Eq.subst (suc (toℕ a) <_) s p)
        fu″ : toℕ c′ ∸ toℕ a ≤ k
        fu″ = Eq.subst (λ z → z ∸ toℕ a ≤ k) (Eq.sym (prev-toℕ c))
                (Eq.subst (_≤ k) (Eq.sym (pred∸ (toℕ c) (toℕ a))) (pred≤pred fu))
        a≢c′ = λ e → <-irrefl (Eq.cong toℕ e) lt″
        a≢c  = λ e → <-irrefl (Eq.cong toℕ e) (<-trans (n<1+n (toℕ a)) p)
        dec  = axiom (r27 a c′ c s p eq)
    in trans (cong dec dec)
       (trans assoc
       (trans (cong refl assoc)
       (trans (cong refl (cong refl (sym assoc)))
       (trans (cong refl (cong refl (cong (LR c′ c s) refl)))
       (trans (cong refl (cong refl left-unit))
       (trans (cong refl (sym assoc))
       (trans (cong refl (cong (sq-fuel k a c′ lt″ fu″) refl))
       (trans (sym assoc)
       (trans (cong (R-act₂ c′ c a c′ a c s (tr-o a≢c′ a≢c Eq.refl)
                                            (tr-l Eq.refl Eq.refl)) refl)
       (trans assoc
       (trans (cong refl (axiom (r29 c′ c s))) right-unit)))))))))))

-- The square of a mixed letter is the sign pair on its X indices.
zx² : ∀ (a c : Fin N) → toℕ a < toℕ c → zx a a c • zx a a c ≈ zz a c
zx² a c lt = sq-fuel (toℕ c ∸ toℕ a) a c lt ≤-refl

-- Reading the conjugation action off for the letter's own pair the
-- other way round.
private
  zx-conj′ : ∀ (a c f s : Fin N) → a ≢ c → Tr a c c f → Tr a c a s →
             zx a a c • zz c a ≈ zz f s • zx a a c →
             zx a a c • zz c a ≈ zz a c • zx a a c
  zx-conj′ a c f s a≢c (tr-l c≡a _) _ law = ⊥-elim (a≢c (Eq.sym c≡a))
  zx-conj′ a c f s a≢c (tr-o _ c≢c _) _ law = ⊥-elim (c≢c Eq.refl)
  zx-conj′ a c .a s a≢c (tr-r _ Eq.refl) (tr-r a≡c _) law = ⊥-elim (a≢c a≡c)
  zx-conj′ a c .a s a≢c (tr-r _ Eq.refl) (tr-o a≢a _ _) law = ⊥-elim (a≢a Eq.refl)
  zx-conj′ a c .a .c a≢c (tr-r _ Eq.refl) (tr-l _ Eq.refl) law = law

zx-conj : ∀ (a c : Fin N) → a ≢ c → zx a a c • zz c a ≈ zz a c • zx a a c
zx-conj a c a≢c =
  zx-conj′ a c (Conj.fst cj) (Conj.snd cj) a≢c
           (Conj.trx cj) (Conj.try cj) (Conj.law cj)
  where cj = conj-any a c c a a≢c

-- The square, in either order of the pair.
zx²′ : ∀ (a c : Fin N) → a ≢ c → zx a a c • zx a a c ≈ zz a c
zx²′ a c a≢c with <-cmp (toℕ a) (toℕ c)
... | tri< lt _ _ = zx² a c lt
... | tri≈ _ e _  = ⊥-elim (a≢c (toℕ-injective e))
... | tri> _ _ gt =
  let c≢a = λ e → a≢c (Eq.sym e) in
  trans (cong (flip′ a c a≢c) (flip′ a c a≢c))
  (trans assoc
  (trans (cong refl (sym assoc))
  (trans (cong refl (cong (zx-conj c a c≢a) refl))
  (trans (cong refl assoc)
  (trans (cong refl (cong refl (zx² c a gt)))
  (trans (cong refl (zz² c a)) right-unit))))))

-- Hence a mixed letter and the one with its X indices exchanged are
-- inverse — the general form of (29).
zx-inv : ∀ (a c : Fin N) → a ≢ c → zx a a c • zx c c a ≈ ε
zx-inv a c a≢c =
  trans (cong refl (flip′ c a (λ e → a≢c (Eq.sym e))))
  (trans (sym assoc)
  (trans (cong (zx-conj a c a≢c) refl)
  (trans assoc
  (trans (cong refl (zx²′ a c a≢c)) (zz² a c)))))

------------------------------------------------------------------------
-- Natural-number indices
--
-- A `Fin` index survives the round trip through ℕ, so a letter written
-- with natural-number indices — which is how `Encoding` writes the ones
-- whose indices are literals — is the one written with `Fin` indices.

-- A Fin index survives the round trip through ℕ, so a letter written
-- with natural-number indices is the one written with Fin indices.
toFin-toℕ : ∀ (a : Fin N) → toFin {₃₊ m} (toℕ a) ≡ just a
toFin-toℕ a with toℕ a <? N
... | yes lt  = Eq.cong just (fromℕ<-toℕ a lt)
... | no ¬lt  = ⊥-elim (¬lt (toℕ<n a))

zxℕ-zx : ∀ (c a b : Fin N) → zxℕ {₃₊ m} (toℕ c) (toℕ a) (toℕ b) ≡ zx c a b
zxℕ-zx c a b rewrite toFin-toℕ c | toFin-toℕ a | toFin-toℕ b = Eq.refl

zzℕ-zz : ∀ (a b : Fin N) → zzℕ {₃₊ m} (toℕ a) (toℕ b) ≡ zz a b
zzℕ-zz a b rewrite toFin-toℕ a | toFin-toℕ b = Eq.refl


------------------------------------------------------------------------
-- Item (b): the rules of Figure 7 run through the coset action
--
-- For each rule of Figure 7 and each of the four cosets, both sides of
-- the rule are run through the action and the resulting words over P
-- have to be identified.  The obligations were computed and checked
-- against the matrices first (`scratchpad/tB.py`, every rule at every
-- coset at every admissible index on eight indices, no failures), so
-- what is written here is known to be what the method asks for.
--
-- The first three rules are the orders.  (a1*) gives the same
-- obligation at all four cosets, since the sign letter only ever moves
-- between a coset and its partner.
--
-- (a3) is worth a note.  At the coset ε it asks for
--
--     hh a b 0 1 • hh 0 1 a b  ≈  ε,
--
-- and (42) at c d := a b says that product is the single letter
-- `hh a b a b`, which denotes H_[a,b] H_[a,b] = I.  So the obligation
-- comes down to `hh a b a b ≈ ε`, and it is not yet clear which rule
-- of Figure 8 supplies that: (35) wants four distinct indices, (36)
-- and (37) want the two pattern positions to differ, and (42) relates
-- the letter to its bridged form rather than to ε.  Worth pinning down
-- before the Hadamard obligations are attempted.

WD-a1 : zz o₁ z₀ • zz o₁ z₀ ≈ ε
WD-a1 = zz² o₁ z₀

-- (a2) at the cosets ε and M: the mixed letter on the index 1 is its
-- own inverse.  (30) peels its sign off, the conjugation action moves
-- that sign across, and the square of what is left is a sign pair
-- which the two peeled ones cancel.
private
  xx-twist₂′ : ∀ (a b f s : Fin N) → a ≢ b → o₁ ≢ a → o₁ ≢ b →
               Tr a b o₁ f → Tr a b a s →
               zx a a b • zz o₁ a ≈ zz f s • zx a a b →
               zx a a b • zz o₁ a ≈ zz o₁ b • zx a a b
  xx-twist₂′ a b f s a≢b o≢a o≢b (tr-l o≡a _) _ law = ⊥-elim (o≢a o≡a)
  xx-twist₂′ a b f s a≢b o≢a o≢b (tr-r o≡b _) _ law = ⊥-elim (o≢b o≡b)
  xx-twist₂′ a b .o₁ s a≢b o≢a o≢b (tr-o _ _ Eq.refl) (tr-r a≡b _) law =
    ⊥-elim (a≢b a≡b)
  xx-twist₂′ a b .o₁ s a≢b o≢a o≢b (tr-o _ _ Eq.refl) (tr-o a≢a _ _) law =
    ⊥-elim (a≢a Eq.refl)
  xx-twist₂′ a b .o₁ .b a≢b o≢a o≢b (tr-o _ _ Eq.refl) (tr-l _ Eq.refl) law = law

xx-twist₂ : ∀ (a b : Fin N) → a ≢ b → o₁ ≢ a → o₁ ≢ b →
            zx a a b • zz o₁ a ≈ zz o₁ b • zx a a b
xx-twist₂ a b a≢b o≢a o≢b =
  xx-twist₂′ a b (Conj.fst cj) (Conj.snd cj) a≢b o≢a o≢b
             (Conj.trx cj) (Conj.try cj) (Conj.law cj)
  where cj = conj-any a b o₁ a a≢b

WD-a2 : ∀ (a b : Fin N) → (a≢b : a ≢ b) → o₁ ≢ a → o₁ ≢ b →
        zx o₁ a b • zx o₁ a b ≈ ε
WD-a2 a b a≢b o≢a o≢b =
  trans (cong r30′ r30′)
  (trans assoc
  (trans (cong refl (sym assoc))
  (trans (cong refl (cong (xx-twist₂ a b a≢b o≢a o≢b) refl))
  (trans (cong refl assoc)
  (trans (sym assoc)
  (trans (cong (zz-route a b) refl)
  (trans (cong refl (zx²′ a b a≢b)) (zz² a b))))))))
  where
  r30′ : zx o₁ a b ≈ zz o₁ a • zx a a b
  r30′ = axiom (r30 o₁ a b a≢b o≢a o≢b)

-- (c1) at the coset ε: both sides come down to the same letter, the
-- sign being carried across by the conjugation action one way and
-- cancelled by (20) the other.
WD-c1 : ∀ (a b : Fin N) → (a≢b : a ≢ b) → o₁ ≢ a → o₁ ≢ b →
        zz o₁ a • zx o₁ a b ≈ zx o₁ a b • zz o₁ b
WD-c1 a b a≢b o≢a o≢b =
  trans (cong refl r30′)
  (trans (sym assoc)
  (trans (cong (zz-o² a) refl)
  (trans left-unit
         (sym (trans (cong r30′ refl)
              (trans assoc
              (trans (cong refl (xx-twist a b a≢b o≢a o≢b))
              (trans (sym assoc)
              (trans (cong (zz-o² a) refl) left-unit)))))))))
  where
  r30′ : zx o₁ a b ≈ zz o₁ a • zx a a b
  r30′ = axiom (r30 o₁ a b a≢b o≢a o≢b)

------------------------------------------------------------------------
-- Figure 9
--
-- The paper's Appendix A.4 derives a figure of auxiliary equations
-- from Figure 8 before attacking Item (a), and the general theory
-- above turns out to be exactly that figure.  Matching them up:
--
--   (47)  is `LR`          -- the consecutive letter's inverse
--   (48)  is `L-cube`      -- that inverse as the letter's cube
--   (51)  is `zx-inv`      -- the general inverse, through (33)
--   (52)  is `zx²′`        -- the general square
--   (53)  is (30) itself
--   (56)  is `zx-own`      -- a letter commutes with its own sign pair
--   (57)  is (56) through (21)
--   (58)–(62) are `conj-any` with one or two spectator indices
--   (63)  is `zz-comm`
--
-- (49), (50), (54) and (55) are the Gray-code transport, which is what
-- `flip-step` and `flip-step′` do, packaged as equations rather than
-- as steps of an induction.  Only (64) — that two mixed letters on
-- disjoint index pairs commute — has no counterpart here yet.
--
-- Figure 9 contains no Hadamard equations at all, so the question
-- raised above, which rule gives `hh a b a b ≈ ε`, is not answered
-- there either; it belongs to the later part of A.4.2.
--
-- And that part is not more equations but a *normal form*.  Lemma A.4
-- gives a unique normal form for words over P containing no Hadamard
-- letter, from which Corollary A.5 reads off that two such words with
-- the same semantics are equal, and Corollaries A.7, A.9 and A.10
-- extend that to words with at most one Hadamard letter.  Appendix
-- A.4 then derives the Reidemeister–Schreier output "with minimum
-- effort" by appealing to those, not by writing derivations out.  Even
-- (64), the one equation of Figure 9 missing here, is proved that way:
-- its argument in the paper runs six hundred lines and cites Lemma A.4
-- itself.
--
-- How much the Hadamard-free fragment would buy was measured
-- (`scratchpad/tC.py`): of the obligations of Item (b), only (a1*) and
-- (b1*) are Hadamard-free at every coset and index, (a2) and (c1) are
-- so except where an index meets 0 or 1, and every rule of Figure 7
-- mentioning H produces Hadamard letters at every coset.  So the four
-- families proved here are essentially what the Hadamard-free fragment
-- reaches; the rest waits on Lemma A.4.
--
-- Lemma A.4's normal form, for the record, is
--
--     ((−1)[a₁](−1)[b₁]) ⋯ ((−1)[a_k](−1)[b_k])
--       ∏_{i=1}^{N−1} ( ∏_{j=d_i}^{N−i−1} ((−1)[j] X[j,j+1]) )
--
-- with k ≥ 0, a₁ < b₁ < ⋯ < a_k < b_k, and d_i ∈ {0,…,N−i}, both
-- products taken in increasing order and an empty one being ε.  So the
-- sign part is an even-sized subset of the indices, written as its
-- elements paired off in increasing order, and the permutation part is
-- a Lehmer code: the vector (d₁,…,d_{N−1}) ranges over ∏(N−i+1) = N!
-- values, one per permutation, each a product of *consecutive* mixed
-- letters.  Uniqueness is read off the semantics — a word of that form
-- denotes a permutation matrix times a diagonal of ±1, the dᵢ being
-- fixed by the permutation and the aᵢ, bᵢ by the diagonal.
--
-- So building it needs: a representation of the two halves (an even
-- `Vec Bool N` and a Lehmer code), the word each denotes, a reduction
-- of any Hadamard-free word to that form, and the uniqueness argument.
-- The general mixed-letter theory above is exactly the rewriting the
-- reduction wants, and `Normalization/NormalForm/*` the frame for the
-- uniqueness half.

-- (48): the inverse of a consecutive letter is its cube, since (23)
-- makes the sign pair its square.
L-cube : ∀ (a a′ : Fin N) → Succ a a′ →
         zx a′ a a′ ≈ (zx a a a′ • zx a a a′) • zx a a a′
L-cube a a′ s = trans (L-form a a′ s) (cong (axiom (r23 a a′ s)) refl)

-- (b1*) at all four cosets: the sign letter on the index 1 is the
-- empty word by (20), so both sides collapse to the same letter.  As
-- with (a1*), the four cosets give the same obligation.
WD-b1 : zz o₁ z₀ • zz o₁ o₁ ≈ zz o₁ o₁ • zz o₁ z₀
WD-b1 = trans (cong refl (axiom (r20 o₁)))
        (trans right-unit
               (sym (trans (cong (axiom (r20 o₁)) refl) left-unit)))

------------------------------------------------------------------------
-- Towards (64): disjoint mixed letters commute
--
-- The paper proves (64) by a double induction on the two gaps, with
-- (54) — which here is (25) together with `L-cube` — shrinking a pair
-- one index at a time, (51) reversing a pair, and a six-way case
-- analysis on how the two pairs interleave on the line.  Its base case
-- is two *consecutive* pairs, which is (32) outright.
--
-- What the induction needs at the base is that case with either pair
-- taken in either order.  One of those is (32); the others follow from
-- it, because reversing a pair costs only a sign pair (`flip′`) and
-- the other letter carries a sign pair on two spectator indices
-- straight through (`R-act₂` with two `tr-o`s).

disj-succ : ∀ (a a′ c c′ : Fin N) → Succ a a′ → Succ c c′ → toℕ a′ < toℕ c →
            zx a a a′ • zx c′ c′ c ≈ zx c′ c′ c • zx a a a′
disj-succ a a′ c c′ s t lt =
  trans (cong refl (flip′ c′ c c′≢c))
  (trans (sym assoc)
  (trans (cong (R-act₂ a a′ c′ c c′ c s
                 (tr-o c′≢a c′≢a′ Eq.refl) (tr-o c≢a c≢a′ Eq.refl)) refl)
  (trans assoc
  (trans (cong refl (axiom (r32 a a′ c c′ s t lt)))
  (trans (sym assoc)
         (cong (sym (flip′ c′ c c′≢c)) refl))))))
  where
  a<a′ : toℕ a < toℕ a′
  a<a′ = Eq.subst (toℕ a <_) (Eq.sym s) (n<1+n (toℕ a))

  c<c′ : toℕ c < toℕ c′
  c<c′ = Eq.subst (toℕ c <_) (Eq.sym t) (n<1+n (toℕ c))

  c′≢c : c′ ≢ c
  c′≢c e = <-irrefl (Eq.sym (Eq.cong toℕ e)) c<c′

  c≢a′ : c ≢ a′
  c≢a′ e = <-irrefl (Eq.sym (Eq.cong toℕ e)) lt

  c≢a : c ≢ a
  c≢a e = <-irrefl (Eq.sym (Eq.cong toℕ e)) (<-trans a<a′ lt)

  c′≢a′ : c′ ≢ a′
  c′≢a′ e = <-irrefl (Eq.sym (Eq.cong toℕ e)) (<-trans lt c<c′)

  c′≢a : c′ ≢ a
  c′≢a e = <-irrefl (Eq.sym (Eq.cong toℕ e)) (<-trans a<a′ (<-trans lt c<c′))

------------------------------------------------------------------------
-- Towards (64), continued: a spectator sign pair
--
-- The double induction for (64) shrinks a pair with (25) or (27) and
-- has to move the other letter past each of the three letters that
-- produces.  Two of them are mixed letters on smaller pairs, which the
-- induction hypothesis covers; the third is the *reversed* consecutive
-- letter, and by `L-form` that is the letter times a sign pair on the
-- two indices being shrunk.  Since those are spectators of the other
-- pair, that sign pair passes straight through — which is this lemma.

private
  conj-spect′ : ∀ (c d x y f s : Fin N) → x ≢ c → x ≢ d → y ≢ c → y ≢ d →
                Tr c d x f → Tr c d y s →
                zx c c d • zz x y ≈ zz f s • zx c c d →
                zx c c d • zz x y ≈ zz x y • zx c c d
  conj-spect′ c d x y .x .y _ _ _ _ (tr-o _ _ Eq.refl) (tr-o _ _ Eq.refl) law = law
  conj-spect′ c d x y f s x≢c _ _ _ (tr-l x≡c _) _ law = ⊥-elim (x≢c x≡c)
  conj-spect′ c d x y f s _ x≢d _ _ (tr-r x≡d _) _ law = ⊥-elim (x≢d x≡d)
  conj-spect′ c d x y f s _ _ y≢c _ _ (tr-l y≡c _) law = ⊥-elim (y≢c y≡c)
  conj-spect′ c d x y f s _ _ _ y≢d _ (tr-r y≡d _) law = ⊥-elim (y≢d y≡d)

conj-spect : ∀ (c d x y : Fin N) → c ≢ d → x ≢ c → x ≢ d → y ≢ c → y ≢ d →
             zx c c d • zz x y ≈ zz x y • zx c c d
conj-spect c d x y c≢d x≢c x≢d y≢c y≢d =
  conj-spect′ c d x y (Conj.fst cj) (Conj.snd cj) x≢c x≢d y≢c y≢d
              (Conj.trx cj) (Conj.try cj) (Conj.law cj)
  where cj = conj-any c d x y c≢d

-- Strict order gives distinctness, in both directions.
<⇒≢ : ∀ {x y : Fin N} → toℕ x < toℕ y → x ≢ y
<⇒≢ lt e = <-irrefl (Eq.cong toℕ e) lt

>⇒≢ : ∀ {x y : Fin N} → toℕ y < toℕ x → x ≢ y
>⇒≢ lt e = <-irrefl (Eq.sym (Eq.cong toℕ e)) lt

-- What remains for (64) is the induction itself.  Note that it needs
-- *both* decompositions, (25) and (27), as the inductions above do:
-- which one applies is fixed by the parity of the gap, not by choice.
-- In the case a < b < c < d that is harmless — (25) shrinks the pair
-- upwards from a and (27) downwards from b, and either way the new
-- index stays strictly below c — but it doubles the branches, and the
-- remaining five interleavings of the two pairs each need their own.

------------------------------------------------------------------------
-- (64) when the two pairs occupy disjoint intervals
--
-- The double induction of the paper's proof, in the case
-- a < b < c < d.  Whichever pair still has a gap is shrunk by (25) or
-- (27) — which of the two is fixed by the parity of that gap, not by
-- choice — and the other letter is moved past each of the three
-- letters the decomposition produces.  Two of them are mixed letters
-- on shorter pairs, covered by the induction hypothesis; the third is
-- the reversed consecutive letter, which by `L-form` is the letter
-- times a sign pair on the two indices being shrunk, and those are
-- spectators of the other pair, so `conj-spect` carries it through.
-- Here the new index always stays inside the interval it came from,
-- so the two pairs remain disjoint at every level.  Both gaps reach
-- one, and (32) finishes.

private
  disj-fuel : ∀ (k₁ k₂ : ℕ) (a b c d : Fin N) →
              toℕ a < toℕ b → toℕ b < toℕ c → toℕ c < toℕ d →
              toℕ b ∸ toℕ a ≤ k₁ → toℕ d ∸ toℕ c ≤ k₂ →
              zx c c d • zx a a b ≈ zx a a b • zx c c d
  disj-fuel zero k₂ a b c d ab bc cd f₁ f₂ =
    ⊥-elim (<-irrefl Eq.refl (≤-trans (0<∸ ab) f₁))
  disj-fuel (suc k₁) zero a b c d ab bc cd f₁ f₂ =
    ⊥-elim (<-irrefl Eq.refl (≤-trans (0<∸ cd) f₂))
  disj-fuel (suc k₁) (suc k₂) a b c d ab bc cd f₁ f₂
    with suc (toℕ a) <? toℕ b
  -- The first pair still has a gap.
  disj-fuel (suc k₁) (suc k₂) a b c d ab bc cd f₁ f₂ | yes p
    with parity (toℕ b ∸ toℕ a) in eq
  disj-fuel (suc k₁) (suc k₂) a b c d ab bc cd f₁ f₂ | yes p | true =
    let pa = <-trans p (toℕ<n b)
        a′ = next a pa
        s  = next-Succ a pa
        a<a′ = Eq.subst (toℕ a <_) (Eq.sym s) (n<1+n (toℕ a))
        a′<b = Eq.subst (_< toℕ b) (Eq.sym s) p
        a′<c = <-trans a′<b bc
        a<c  = <-trans a<a′ a′<c
        1≤k₁ = ≤-trans (Eq.subst (1 ≤_) (∸suc (toℕ b) (toℕ a)) (0<∸ p)) (pred≤pred f₁)
        f₁R  = Eq.subst (λ z → z ∸ toℕ a ≤ k₁) (Eq.sym s)
                 (Eq.subst (_≤ k₁) (Eq.sym (suc∸ (toℕ a))) 1≤k₁)
        f₁M  = Eq.subst (λ z → toℕ b ∸ z ≤ k₁) (Eq.sym s)
                 (Eq.subst (_≤ k₁) (Eq.sym (∸suc (toℕ b) (toℕ a))) (pred≤pred f₁))
        cR = disj-fuel k₁ (suc k₂) a a′ c d a<a′ a′<c cd f₁R f₂
        cM = disj-fuel k₁ (suc k₂) a′ b c d a′<b bc cd f₁M f₂
        cL = trans (cong refl (L-form a a′ s))
             (trans (comm-• (conj-spect c d a a′ (<⇒≢ cd)
                              (<⇒≢ a<c) (<⇒≢ (<-trans a<c cd))
                              (<⇒≢ a′<c) (<⇒≢ (<-trans a′<c cd))) cR)
                    (cong (sym (L-form a a′ s)) refl))
        dec = axiom (r25 a a′ b s a′<b eq)
    in trans (cong refl dec)
       (trans (comm-• cL (comm-• cM cR)) (cong (sym dec) refl))
  disj-fuel (suc k₁) (suc k₂) a b c d ab bc cd f₁ f₂ | yes p | false =
    let 0<b = ≤-trans (s≤s z≤n) ab
        b′ = prev b
        s  = prev-Succ b 0<b
        b′<b = Eq.subst (toℕ b′ <_) (Eq.sym s) (n<1+n (toℕ b′))
        a<b′ = ≤-pred (Eq.subst (suc (toℕ a) <_) s p)
        b′<c = <-trans b′<b bc
        1≤k₁ = ≤-trans (Eq.subst (1 ≤_) (∸suc (toℕ b) (toℕ a)) (0<∸ p)) (pred≤pred f₁)
        s′   = Eq.trans s (Eq.cong suc (prev-toℕ b))
        f₁L  = Eq.subst (λ z → toℕ b ∸ z ≤ k₁) (Eq.sym (prev-toℕ b))
                 (Eq.subst (λ z → z ∸ pred (toℕ b) ≤ k₁) (Eq.sym s′)
                   (Eq.subst (_≤ k₁) (Eq.sym (suc∸ (pred (toℕ b)))) 1≤k₁))
        f₁M  = Eq.subst (λ z → z ∸ toℕ a ≤ k₁) (Eq.sym (prev-toℕ b))
                 (Eq.subst (_≤ k₁) (Eq.sym (pred∸ (toℕ b) (toℕ a))) (pred≤pred f₁))
        cLb = disj-fuel k₁ (suc k₂) b′ b c d b′<b bc cd f₁L f₂
        cM  = disj-fuel k₁ (suc k₂) a b′ c d a<b′ b′<c cd f₁M f₂
        cRb = trans (cong refl (L-form b′ b s))
              (trans (comm-• (conj-spect c d b′ b (<⇒≢ cd)
                               (<⇒≢ b′<c) (<⇒≢ (<-trans b′<c cd))
                               (<⇒≢ bc) (<⇒≢ (<-trans bc cd))) cLb)
                     (cong (sym (L-form b′ b s)) refl))
        dec = axiom (r27 a b′ b s p eq)
    in trans (cong refl dec)
       (trans (comm-• cLb (comm-• cM cRb)) (cong (sym dec) refl))
  -- The first pair is consecutive; shrink the second.
  disj-fuel (suc k₁) (suc k₂) a b c d ab bc cd f₁ f₂ | no ¬p
    with suc (toℕ c) <? toℕ d
  disj-fuel (suc k₁) (suc k₂) a b c d ab bc cd f₁ f₂ | no ¬p | yes q
    with parity (toℕ d ∸ toℕ c) in eq
  disj-fuel (suc k₁) (suc k₂) a b c d ab bc cd f₁ f₂ | no ¬p | yes q | true =
    let pc = <-trans q (toℕ<n d)
        c′ = next c pc
        s  = next-Succ c pc
        c<c′ = Eq.subst (toℕ c <_) (Eq.sym s) (n<1+n (toℕ c))
        c′<d = Eq.subst (_< toℕ d) (Eq.sym s) q
        b<c′ = <-trans bc c<c′
        1≤k₂ = ≤-trans (Eq.subst (1 ≤_) (∸suc (toℕ d) (toℕ c)) (0<∸ q)) (pred≤pred f₂)
        f₂R  = Eq.subst (λ z → z ∸ toℕ c ≤ k₂) (Eq.sym s)
                 (Eq.subst (_≤ k₂) (Eq.sym (suc∸ (toℕ c))) 1≤k₂)
        f₂M  = Eq.subst (λ z → toℕ d ∸ z ≤ k₂) (Eq.sym s)
                 (Eq.subst (_≤ k₂) (Eq.sym (∸suc (toℕ d) (toℕ c))) (pred≤pred f₂))
        cR = disj-fuel (suc k₁) k₂ a b c c′ ab bc c<c′ f₁ f₂R
        cM = disj-fuel (suc k₁) k₂ a b c′ d ab b<c′ c′<d f₁ f₂M
        cL = trans (cong (L-form c c′ s) refl)
             (trans (sym (comm-• (conj-spect a b c c′ (<⇒≢ ab)
                                   (>⇒≢ (<-trans ab bc)) (>⇒≢ bc)
                                   (>⇒≢ (<-trans ab b<c′)) (>⇒≢ b<c′)) (sym cR)))
                    (cong refl (sym (L-form c c′ s))))
        dec = axiom (r25 c c′ d s c′<d eq)
    in trans (cong dec refl)
       (trans (sym (comm-• (sym cL) (comm-• (sym cM) (sym cR))))
              (cong refl (sym dec)))
  disj-fuel (suc k₁) (suc k₂) a b c d ab bc cd f₁ f₂ | no ¬p | yes q | false =
    let 0<d = ≤-trans (s≤s z≤n) cd
        d′ = prev d
        s  = prev-Succ d 0<d
        d′<d = Eq.subst (toℕ d′ <_) (Eq.sym s) (n<1+n (toℕ d′))
        c<d′ = ≤-pred (Eq.subst (suc (toℕ c) <_) s q)
        b<d′ = <-trans bc c<d′
        1≤k₂ = ≤-trans (Eq.subst (1 ≤_) (∸suc (toℕ d) (toℕ c)) (0<∸ q)) (pred≤pred f₂)
        s′   = Eq.trans s (Eq.cong suc (prev-toℕ d))
        f₂L  = Eq.subst (λ z → toℕ d ∸ z ≤ k₂) (Eq.sym (prev-toℕ d))
                 (Eq.subst (λ z → z ∸ pred (toℕ d) ≤ k₂) (Eq.sym s′)
                   (Eq.subst (_≤ k₂) (Eq.sym (suc∸ (pred (toℕ d)))) 1≤k₂))
        f₂M  = Eq.subst (λ z → z ∸ toℕ c ≤ k₂) (Eq.sym (prev-toℕ d))
                 (Eq.subst (_≤ k₂) (Eq.sym (pred∸ (toℕ d) (toℕ c))) (pred≤pred f₂))
        cLd = disj-fuel (suc k₁) k₂ a b d′ d ab b<d′ d′<d f₁ f₂L
        cM  = disj-fuel (suc k₁) k₂ a b c d′ ab bc c<d′ f₁ f₂M
        cRd = trans (cong (L-form d′ d s) refl)
              (trans (sym (comm-• (conj-spect a b d′ d (<⇒≢ ab)
                                    (>⇒≢ (<-trans ab b<d′)) (>⇒≢ b<d′)
                                    (>⇒≢ (<-trans ab (<-trans bc (<-trans c<d′ d′<d))))
                                    (>⇒≢ (<-trans bc (<-trans c<d′ d′<d)))) (sym cLd)))
                     (cong refl (sym (L-form d′ d s))))
        dec = axiom (r27 c d′ d s q eq)
    in trans (cong dec refl)
       (trans (sym (comm-• (sym cLd) (comm-• (sym cM) (sym cRd))))
              (cong refl (sym dec)))
  disj-fuel (suc k₁) (suc k₂) a b c d ab bc cd f₁ f₂ | no ¬p | no ¬q =
    sym (axiom (r32 a b c d (≤-antisym (≮⇒≥ ¬p) ab) (≤-antisym (≮⇒≥ ¬q) cd) bc))

-- (64) for two pairs lying in disjoint intervals.
disj-int : ∀ (a b c d : Fin N) →
           toℕ a < toℕ b → toℕ b < toℕ c → toℕ c < toℕ d →
           zx c c d • zx a a b ≈ zx a a b • zx c c d
disj-int a b c d ab bc cd =
  disj-fuel (toℕ b ∸ toℕ a) (toℕ d ∸ toℕ c) a b c d ab bc cd ≤-refl ≤-refl

------------------------------------------------------------------------
-- Reading the conjugation action off
--
-- `conj-any` produces the transposed indices rather than taking them,
-- which has meant an extraction lemma at each use.  Since the
-- transposition is a function of its input, one uniqueness lemma
-- replaces all of them.

Tr-unique : ∀ {a c x x′ x″ : Fin N} → a ≢ c → Tr a c x x′ → Tr a c x x″ → x′ ≡ x″
Tr-unique a≢c (tr-l _ e₁)    (tr-l _ e₂)    = Eq.trans e₁ (Eq.sym e₂)
Tr-unique a≢c (tr-l x≡a _)   (tr-r x≡c _)   = ⊥-elim (a≢c (Eq.trans (Eq.sym x≡a) x≡c))
Tr-unique a≢c (tr-l x≡a _)   (tr-o x≢a _ _) = ⊥-elim (x≢a x≡a)
Tr-unique a≢c (tr-r x≡c _)   (tr-l x≡a _)   = ⊥-elim (a≢c (Eq.trans (Eq.sym x≡a) x≡c))
Tr-unique a≢c (tr-r _ e₁)    (tr-r _ e₂)    = Eq.trans e₁ (Eq.sym e₂)
Tr-unique a≢c (tr-r x≡c _)   (tr-o _ x≢c _) = ⊥-elim (x≢c x≡c)
Tr-unique a≢c (tr-o x≢a _ _) (tr-l x≡a _)   = ⊥-elim (x≢a x≡a)
Tr-unique a≢c (tr-o _ x≢c _) (tr-r x≡c _)   = ⊥-elim (x≢c x≡c)
Tr-unique a≢c (tr-o _ _ e₁)  (tr-o _ _ e₂)  = Eq.trans e₁ (Eq.sym e₂)

-- The action with both sides named.
conj-at : ∀ (a b x y x′ y′ : Fin N) → (a≢b : a ≢ b) →
          Tr a b x x′ → Tr a b y y′ →
          zx a a b • zz x y ≈ zz x′ y′ • zx a a b
conj-at a b x y x′ y′ a≢b tx ty =
  Eq.subst₂ (λ u v → zx a a b • zz x y ≈ zz u v • zx a a b)
            (Tr-unique a≢b (Conj.trx cj) tx)
            (Tr-unique a≢b (Conj.try cj) ty)
            (Conj.law cj)
  where cj = conj-any a b x y a≢b

------------------------------------------------------------------------
-- (64) for disjoint intervals, the other way round

disj-int′ : ∀ (a b c d : Fin N) →
            toℕ c < toℕ d → toℕ d < toℕ a → toℕ a < toℕ b →
            zx c c d • zx a a b ≈ zx a a b • zx c c d
disj-int′ a b c d cd da ab = sym (disj-int c d a b cd da ab)

------------------------------------------------------------------------
-- An X pair on two disjoint intervals is an involution
--
-- (34) splits the letter into two mixed ones and (30) puts the second
-- one's sign outside its pair; the two letters then commute by (64),
-- each square is a sign pair by the general (23), and what is left is
-- sign algebra.  This is the obligation (a2) gives at the cosets
-- H_[0,1] and H_[0,1](−1)_[1].

xx-invol-gen : ∀ (a b c d : Fin N) → (a≢b : a ≢ b) → (c≢d : c ≢ d) →
               (b≢c : b ≢ c) → (b≢d : b ≢ d) → (c≢a : c ≢ a) → (c≢b : c ≢ b) →
               zx c c d • zx a a b ≈ zx a a b • zx c c d →
               xx a b c d • xx a b c d ≈ ε
xx-invol-gen a b c d a≢b c≢d b≢c b≢d c≢a c≢b comm = begin
  xx a b c d • xx a b c d
    ≈⟨ cong form form ⟩
  (A • (S • C)) • (A • (S • C))
    ≈⟨ by-passoc ((□ • (□ • □)) • (□ • (□ • □)))
                 (□ • ((□ • ((□ • □) • (□ • □))))) Eq.refl ⟩
  A • (S • ((C • A) • (S • C)))
    ≈⟨ back A (back S (front (S • C) comm)) ⟩
  A • (S • ((A • C) • (S • C)))
    ≈⟨ by-passoc (□ • (□ • ((□ • □) • (□ • □))))
                 (□ • ((□ • □) • (□ • (□ • □)))) Eq.refl ⟩
  A • ((S • A) • (C • (S • C)))
    ≈⟨ back A (front (C • (S • C))
         (sym (conj-at a b a c b c a≢b (tr-l Eq.refl Eq.refl)
                       (tr-o c≢a c≢b Eq.refl)))) ⟩
  A • ((A • zz a c) • (C • (S • C)))
    ≈⟨ by-passoc (□ • ((□ • □) • (□ • (□ • □))))
                 ((□ • □) • (□ • (□ • (□ • □)))) Eq.refl ⟩
  (A • A) • (zz a c • (C • (S • C)))
    ≈⟨ front _ (zx²′ a b a≢b) ⟩
  zz a b • (zz a c • (C • (S • C)))
    ≈⟨ back (zz a b) (back (zz a c) tail) ⟩
  zz a b • (zz a c • (zz b d • zz c d))
    ≈⟨ by-passoc (□ • (□ • (□ • □))) ((□ • □) • (□ • □)) Eq.refl ⟩
  (zz a b • zz a c) • (zz b d • zz c d)
    ≈⟨ cong (zz-split a b a c) (zz-split b d c d) ⟩
  (zz a a • zz b c) • (zz b c • zz d d)
    ≈⟨ cong (trans (front _ (axiom (r20 a))) left-unit)
            (trans (back _ (axiom (r20 d))) right-unit) ⟩
  zz b c • zz b c
    ≈⟨ zz² b c ⟩
  ε ∎
  where
  A = zx a a b
  C = zx c c d
  S = zz b c

  form : xx a b c d ≈ A • (S • C)
  form = trans (axiom (r34 a b c d a≢b c≢d))
               (cong refl (axiom (r30 b c d c≢d b≢c b≢d)))

  tail : C • (S • C) ≈ zz b d • zz c d
  tail = begin
    C • (S • C)     ≈⟨ sym assoc ⟩
    (C • S) • C     ≈⟨ front C (conj-at c d b c b d c≢d
                                 (tr-o b≢c b≢d Eq.refl) (tr-l Eq.refl Eq.refl)) ⟩
    (zz b d • C) • C ≈⟨ assoc ⟩
    zz b d • (C • C) ≈⟨ back (zz b d) (zx²′ c d c≢d) ⟩
    zz b d • zz c d ∎

-- The two orderings of the intervals.
xx-invol : ∀ (a b c d : Fin N) →
           toℕ a < toℕ b → toℕ b < toℕ c → toℕ c < toℕ d →
           xx a b c d • xx a b c d ≈ ε
xx-invol a b c d ab bc cd =
  xx-invol-gen a b c d (<⇒≢ ab) (<⇒≢ cd) (<⇒≢ bc) (<⇒≢ (<-trans bc cd))
               (>⇒≢ (<-trans ab bc)) (>⇒≢ bc) (disj-int a b c d ab bc cd)

xx-invol′ : ∀ (a b c d : Fin N) →
            toℕ c < toℕ d → toℕ d < toℕ a → toℕ a < toℕ b →
            xx a b c d • xx a b c d ≈ ε
xx-invol′ a b c d cd da ab =
  xx-invol-gen a b c d (<⇒≢ ab) (<⇒≢ cd)
               (>⇒≢ (<-trans cd (<-trans da ab))) (>⇒≢ (<-trans da ab))
               (<⇒≢ (<-trans cd da)) (<⇒≢ (<-trans cd (<-trans da ab)))
               (disj-int′ a b c d cd da ab)

-- An X pair split into two mixed letters, the second one's sign put
-- outside its own pair: (34) then (30).
xx-form : ∀ (a b c d : Fin N) → (a≢b : a ≢ b) → (c≢d : c ≢ d) →
          b ≢ c → b ≢ d →
          xx a b c d ≈ zx a a b • (zz b c • zx c c d)
xx-form a b c d a≢b c≢d b≢c b≢d =
  trans (axiom (r34 a b c d a≢b c≢d)) (cong refl (axiom (r30 b c d c≢d b≢c b≢d)))

------------------------------------------------------------------------
-- (a2) and (c1) at the cosets H_[0,1] and H_[0,1](−1)_[1]
--
-- There the coset action produces X pairs on {a , b} and {0 , 1}, and
-- since the indices of Figure 7's rule avoid 0 and 1 the two pairs lie
-- in disjoint intervals.  (a2) is then `xx-invol′`.  For (c1) both
-- sides collapse to the same mixed letter: the sign pairs the
-- conjugation action produces cancel by (22) and (20), and the square
-- of the letter on {0 , 1} by the general (23).

private
  -- The indices of the rule sit above 0 and 1.
  module Above (a b : Fin N) (1<a : 1 < toℕ a) (ab : toℕ a < toℕ b) where
    z<o : toℕ z₀ < toℕ o₁
    z<o = Eq.subst₂ _<_ (Eq.sym toℕ-z₀) (Eq.sym toℕ-o₁) (s≤s z≤n)

    o<a : toℕ o₁ < toℕ a
    o<a = Eq.subst (_< toℕ a) (Eq.sym toℕ-o₁) 1<a

    z<a : toℕ z₀ < toℕ a
    z<a = <-trans z<o o<a

    o<b = <-trans o<a ab
    z<b = <-trans z<a ab

    a≢b = <⇒≢ ab
    z≢o = <⇒≢ z<o
    a≢z = >⇒≢ z<a
    a≢o = >⇒≢ o<a
    b≢z = >⇒≢ z<b
    b≢o = >⇒≢ o<b

WD-a2-K : ∀ (a b : Fin N) → 1 < toℕ a → toℕ a < toℕ b →
          xx a b z₀ o₁ • xx a b z₀ o₁ ≈ ε
WD-a2-K a b 1<a ab = xx-invol′ a b z₀ o₁ z<o o<a ab
  where open Above a b 1<a ab

WD-c1-K : ∀ (a b : Fin N) → 1 < toℕ a → toℕ a < toℕ b →
          zx a z₀ o₁ • xx a b z₀ o₁ ≈ xx a b z₀ o₁ • zx b z₀ o₁
WD-c1-K a b 1<a ab = trans left right
  where
  open Above a b 1<a ab

  A = zx a a b
  Z = zx z₀ z₀ o₁

  xf : xx a b z₀ o₁ ≈ A • (zz b z₀ • Z)
  xf = xx-form a b z₀ o₁ a≢b z≢o b≢z b≢o

  -- The letter on {0 , 1} passes A, the two pairs being disjoint.
  ZA : Z • A ≈ A • Z
  ZA = sym (disj-int z₀ o₁ a b z<o o<a ab)

  -- What the conjugation action does to the signs that turn up.
  cb : Z • zz b z₀ ≈ zz b o₁ • Z
  cb = conj-at z₀ o₁ b z₀ b o₁ z≢o (tr-o b≢z b≢o Eq.refl) (tr-l Eq.refl Eq.refl)

  ca : A • zz b o₁ ≈ zz a o₁ • A
  ca = conj-at a b b o₁ a o₁ a≢b (tr-r Eq.refl Eq.refl)
                (tr-o (<⇒≢ o<a) (<⇒≢ o<b) Eq.refl)

  czo : A • zz z₀ o₁ ≈ zz z₀ o₁ • A
  czo = conj-at a b z₀ o₁ z₀ o₁ a≢b (tr-o (<⇒≢ z<a) (<⇒≢ z<b) Eq.refl)
                 (tr-o (<⇒≢ o<a) (<⇒≢ o<b) Eq.refl)

  left : zx a z₀ o₁ • xx a b z₀ o₁ ≈ A
  left = begin
    zx a z₀ o₁ • xx a b z₀ o₁
      ≈⟨ cong (axiom (r30 a z₀ o₁ z≢o a≢z a≢o)) xf ⟩
    (zz a z₀ • Z) • (A • (zz b z₀ • Z))
      ≈⟨ by-passoc ((□ • □) • (□ • (□ • □))) (□ • ((□ • □) • (□ • □))) Eq.refl ⟩
    zz a z₀ • ((Z • A) • (zz b z₀ • Z))
      ≈⟨ back _ (front _ ZA) ⟩
    zz a z₀ • ((A • Z) • (zz b z₀ • Z))
      ≈⟨ by-passoc (□ • ((□ • □) • (□ • □))) (□ • (□ • ((□ • □) • □))) Eq.refl ⟩
    zz a z₀ • (A • ((Z • zz b z₀) • Z))
      ≈⟨ back _ (back _ (front _ cb)) ⟩
    zz a z₀ • (A • ((zz b o₁ • Z) • Z))
      ≈⟨ by-passoc (□ • (□ • ((□ • □) • □))) (□ • ((□ • □) • (□ • □))) Eq.refl ⟩
    zz a z₀ • ((A • zz b o₁) • (Z • Z))
      ≈⟨ back _ (cong ca (zx²′ z₀ o₁ z≢o)) ⟩
    zz a z₀ • ((zz a o₁ • A) • zz z₀ o₁)
      ≈⟨ by-passoc (□ • ((□ • □) • □)) ((□ • □) • (□ • □)) Eq.refl ⟩
    (zz a z₀ • zz a o₁) • (A • zz z₀ o₁)
      ≈⟨ cong (trans (zz-split a z₀ a o₁)
                     (trans (front _ (axiom (r20 a))) left-unit)) czo ⟩
    zz z₀ o₁ • (zz z₀ o₁ • A)
      ≈⟨ cancelˡ A (zz² z₀ o₁) ⟩
    A ∎

  right : A ≈ xx a b z₀ o₁ • zx b z₀ o₁
  right = sym (begin
    xx a b z₀ o₁ • zx b z₀ o₁
      ≈⟨ cong xf (axiom (r30 b z₀ o₁ z≢o b≢z b≢o)) ⟩
    (A • (zz b z₀ • Z)) • (zz b z₀ • Z)
      ≈⟨ by-passoc ((□ • (□ • □)) • (□ • □)) (□ • (□ • ((□ • □) • □))) Eq.refl ⟩
    A • (zz b z₀ • ((Z • zz b z₀) • Z))
      ≈⟨ back _ (back _ (front _ cb)) ⟩
    A • (zz b z₀ • ((zz b o₁ • Z) • Z))
      ≈⟨ by-passoc (□ • (□ • ((□ • □) • □))) (□ • ((□ • □) • (□ • □))) Eq.refl ⟩
    A • ((zz b z₀ • zz b o₁) • (Z • Z))
      ≈⟨ back _ (cong (trans (zz-split b z₀ b o₁)
                             (trans (front _ (axiom (r20 b))) left-unit))
                      (zx²′ z₀ o₁ z≢o)) ⟩
    A • (zz z₀ o₁ • zz z₀ o₁)
      ≈⟨ back _ (zz² z₀ o₁) ⟩
    A • ε
      ≈⟨ right-unit ⟩
    A ∎)
