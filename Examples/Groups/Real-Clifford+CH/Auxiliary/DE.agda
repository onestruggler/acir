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
-- The remaining two, (DE-XX) and (DE-HH), need the action of a mixed
-- letter on the signs by conjugation, which is the transposition of
-- its two X indices.  For a consecutive letter that action is settled
-- here in all four cases — `R-zz` and `R-zz′` for the two indices
-- themselves, `R-zz-fix` for a pair of spectators, `R-zz-own` for its
-- own pair — and the general case is the same Gray-code induction
-- again.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.DE (m : ℕ) where

open import Data.Bool using (true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ< ; toℕ<n ; toℕ-injective ; _≟_)
open import Data.Nat using (ℕ ; zero ; suc ; pred ; _<_ ; _≤_ ; _∸_ ; _<?_ ; z≤n ; s≤s)
  renaming (_^_ to _^ℕ_)
open import Data.Nat.Properties
  using (suc-injective ; <-trans ; <-irrefl ; n<1+n ; ≤-pred ; ≤-antisym
        ; ≮⇒≥ ; ≤-<-trans ; ≤-trans ; ≤-refl ; n≤1+n ; <-cmp)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

open import Presentation.Base as PB using ()

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (parity)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.RS m using (o₁)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; zx)

open PB (m P,_===_)
  using (_≈_ ; refl ; sym ; trans ; cong ; axiom ; assoc ; left-unit ; right-unit)

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

private
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

private
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
