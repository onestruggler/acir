------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma A.1, first part: the generic equations of Figure 6 that
-- Figure 7 derives in a few lines (Clément, Appendix A.2)
--
-- (e1), (e2), (c2), (c3), (c4), the variants (c2†), (c4†), (c5†), and
-- (b2), (b3), (b5), each by the paper's own chain; then the seventeen
-- ways conjugating a letter by X_[x,y] exchanges x and y in it, which
-- is what lets Auxiliary.LemmaA1.Rename move an equation from one tuple
-- of distinct indices to any other.  All indices are distinct and in
-- any order (the paper proves every equation "in full generality").
--
-- Every derivation is a chain of segment replacements (SegChain),
-- generated from the paper's lines and checked numerically first: each
-- replaced segment occurs where the step says and has the matrix of its
-- replacement (LemmaA1/gen: gen_a1.py, spec_base.py).  An equation whose
-- sides the paper writes the other way round carries a prime.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.Base (N : ℕ) where

open import Data.Fin using (Fin)
open import Data.List using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics using (−1 ; X ; H ; _G,_===_)
open _G,_===_
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SegChain (N G,_===_)
  using (at ; _▸_ ; done ; run)

open Tools (N G,_===_)

sy : ∀ {a b : Fin N} → a ≢ b → b ≢ a
sy ne e = ne (Eq.sym e)

------------------------------------------------------------------------
-- The equations

-- (e1): an exchange does not depend on the order of its indices.
e1 : ∀ {b c : Fin N} → b ≢ c → X b c ≈ X c b
e1 {b} {c} bc =
  run {X b c ∷ []}
      {X c b ∷ []}
    ( (at 1 0 (X b c ∷ X b c ∷ []) (sym (axiom (a2 bc)))) ▸
      (at 1 0 (H b c ∷ H b c ∷ []) (sym (axiom (a3 bc)))) ▸
      (at 2 2 (−1 c ∷ H b c ∷ []) (sym (axiom (d2 bc)))) ▸
      (at 0 2 (H c b ∷ X b c ∷ []) (sym (axiom (e2* bc)))) ▸
      (at 1 2 (−1 b ∷ X b c ∷ []) (sym (axiom (c1 bc)))) ▸
      (at 2 2 (H c b ∷ X b c ∷ []) (sym (axiom (e2* bc)))) ▸
      (at 3 2 ([]) (axiom (a2 bc))) ▸
      (at 1 2 (H c b ∷ X c b ∷ []) (axiom (d2 (sy bc)))) ▸
      (at 0 2 ([]) (axiom (a3 (sy bc)))) ▸
      done)

-- (e2): a Hadamard with its indices exchanged.
e2 : ∀ {b c : Fin N} → b ≢ c → H c b ≈ X b c • H b c • X b c
e2 {b} {c} bc =
  run {H c b ∷ []}
      {X b c ∷ H b c ∷ X b c ∷ []}
    ( (at 1 0 (X b c ∷ X b c ∷ []) (sym (axiom (a2 bc)))) ▸
      (at 0 2 (X b c ∷ H b c ∷ []) (axiom (e2* bc))) ▸
      done)

-- (c3), read right to left.
c3′ : ∀ {a b c : Fin N} → a ≢ b → a ≢ c → b ≢ c → X b c • X a b ≈ X a c • X b c
c3′ {a} {b} {c} ab ac bc =
  run {X b c ∷ X a b ∷ []}
      {X a c ∷ X b c ∷ []}
    ( (at 1 0 (H a b ∷ H a b ∷ []) (sym (axiom (a3 ab)))) ▸
      (at 2 2 (−1 b ∷ H a b ∷ []) (sym (axiom (d2 ab)))) ▸
      (at 0 2 (H a c ∷ X b c ∷ []) (sym (axiom (c5 ab ac bc)))) ▸
      (at 3 0 (X b c ∷ X b c ∷ []) (sym (axiom (a2 bc)))) ▸
      (at 2 2 (X b c ∷ −1 c ∷ []) (axiom (c1 bc))) ▸
      (at 1 2 ([]) (axiom (a2 bc))) ▸
      (at 2 2 (H a c ∷ X b c ∷ []) (sym (axiom (c5 ab ac bc)))) ▸
      (at 1 2 (H a c ∷ X a c ∷ []) (axiom (d2 ac))) ▸
      (at 0 2 ([]) (axiom (a3 ac))) ▸
      done)

-- (c2), read right to left.
c2 : ∀ {a b c : Fin N} → a ≢ b → a ≢ c → b ≢ c → X a b • X a c ≈ X b c • X a b
c2 {a} {b} {c} ab ac bc =
  run {X a b ∷ X a c ∷ []}
      {X b c ∷ X a b ∷ []}
    ( (at 1 1 (X c a ∷ []) (e1 ac)) ▸
      (at 0 2 (X c b ∷ X a b ∷ []) (c3′ (sy ac) (sy bc) ab)) ▸
      (at 0 1 (X b c ∷ []) (e1 (sy bc))) ▸
      done)

-- (c4), read right to left.
c4 : ∀ {a b c : Fin N} → a ≢ b → a ≢ c → b ≢ c → X a b • H a c ≈ H b c • X a b
c4 {a} {b} {c} ab ac bc =
  run {X a b ∷ H a c ∷ []}
      {H b c ∷ X a b ∷ []}
    ( (at 2 0 (X c a ∷ X c a ∷ []) (sym (axiom (a2 (sy ac))))) ▸
      (at 1 2 (X c a ∷ H c a ∷ []) (axiom (e2* (sy ac)))) ▸
      (at 0 2 (X c b ∷ X a b ∷ []) (c3′ (sy ac) (sy bc) ab)) ▸
      (at 1 2 (H c b ∷ X a b ∷ []) (sym (axiom (c5 (sy ac) (sy bc) ab)))) ▸
      (at 2 2 (X c b ∷ X a b ∷ []) (c3′ (sy ac) (sy bc) ab)) ▸
      (at 0 2 (H b c ∷ X c b ∷ []) (sym (axiom (e2* (sy bc))))) ▸
      (at 1 2 ([]) (axiom (a2 (sy bc)))) ▸
      done)

-- (c2†), read right to left.
c2†′ : ∀ {a b c : Fin N} → a ≢ b → a ≢ c → b ≢ c → X a c • X a b ≈ X a b • X b c
c2†′ {a} {b} {c} ab ac bc =
  run {X a c ∷ X a b ∷ []}
      {X a b ∷ X b c ∷ []}
    ( (at 0 0 (X a b ∷ X a b ∷ []) (sym (axiom (a2 ab)))) ▸
      (at 1 2 (X b c ∷ X a b ∷ []) (c2 ab ac bc)) ▸
      (at 2 2 ([]) (axiom (a2 ab))) ▸
      done)

-- (c4†), read right to left.
c4†′ : ∀ {a b c : Fin N} → a ≢ b → a ≢ c → b ≢ c → H a c • X a b ≈ X a b • H b c
c4†′ {a} {b} {c} ab ac bc =
  run {H a c ∷ X a b ∷ []}
      {X a b ∷ H b c ∷ []}
    ( (at 0 0 (X a b ∷ X a b ∷ []) (sym (axiom (a2 ab)))) ▸
      (at 1 2 (H b c ∷ X a b ∷ []) (c4 ab ac bc)) ▸
      (at 2 2 ([]) (axiom (a2 ab))) ▸
      done)

-- (c5†), read right to left.
c5†′ : ∀ {a b c : Fin N} → a ≢ b → a ≢ c → b ≢ c → H a b • X b c ≈ X b c • H a c
c5†′ {a} {b} {c} ab ac bc =
  run {H a b ∷ X b c ∷ []}
      {X b c ∷ H a c ∷ []}
    ( (at 0 0 (X b c ∷ X b c ∷ []) (sym (axiom (a2 bc)))) ▸
      (at 1 2 (H a c ∷ X b c ∷ []) (sym (axiom (c5 ab ac bc)))) ▸
      (at 2 2 ([]) (axiom (a2 bc))) ▸
      done)

-- (b2): a sign away from an exchange passes it.
b2 : ∀ {a b c : Fin N} → a ≢ b → a ≢ c → b ≢ c → −1 c • X a b ≈ X a b • −1 c
b2 {a} {b} {c} ab ac bc =
  run {−1 c ∷ X a b ∷ []}
      {X a b ∷ −1 c ∷ []}
    ( (at 0 0 (X a c ∷ X a c ∷ []) (sym (axiom (a2 ac)))) ▸
      (at 1 2 (−1 a ∷ X a c ∷ []) (sym (axiom (c1 ac)))) ▸
      (at 2 2 (X a b ∷ X b c ∷ []) (c2†′ ab ac bc)) ▸
      (at 1 2 (X a b ∷ −1 b ∷ []) (axiom (c1 ab))) ▸
      (at 2 2 (X b c ∷ −1 c ∷ []) (axiom (c1 bc))) ▸
      (at 1 2 (X a c ∷ X a b ∷ []) (sym (c2†′ ab ac bc))) ▸
      (at 0 2 ([]) (axiom (a2 ac))) ▸
      done)

-- (b5): an exchange and a Hadamard on disjoint pairs commute.
b5 : ∀ {a b c d : Fin N} → a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d → H c d • X a b ≈ X a b • H c d
b5 {a} {b} {c} {d} ab ac ad bc bd cd =
  run {H c d ∷ X a b ∷ []}
      {X a b ∷ H c d ∷ []}
    ( (at 0 0 (X a c ∷ X a c ∷ []) (sym (axiom (a2 ac)))) ▸
      (at 1 2 (H a d ∷ X a c ∷ []) (sym (c4†′ ac ad cd))) ▸
      (at 2 2 (X a b ∷ X b c ∷ []) (c2†′ ab ac bc)) ▸
      (at 1 2 (X a b ∷ H b d ∷ []) (c4†′ ab ad bd)) ▸
      (at 2 2 (X b c ∷ H c d ∷ []) (c4†′ bc bd cd)) ▸
      (at 1 2 (X a c ∷ X a b ∷ []) (sym (c2†′ ab ac bc))) ▸
      (at 0 2 ([]) (axiom (a2 ac))) ▸
      done)

-- (b3): exchanges on disjoint pairs commute.
b3 : ∀ {a b c d : Fin N} → a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d → X c d • X a b ≈ X a b • X c d
b3 {a} {b} {c} {d} ab ac ad bc bd cd =
  run {X c d ∷ X a b ∷ []}
      {X a b ∷ X c d ∷ []}
    ( (at 0 0 (X a c ∷ X a c ∷ []) (sym (axiom (a2 ac)))) ▸
      (at 1 2 (X a d ∷ X a c ∷ []) (sym (c2†′ ac ad cd))) ▸
      (at 2 2 (X a b ∷ X b c ∷ []) (c2†′ ab ac bc)) ▸
      (at 1 2 (X a b ∷ X b d ∷ []) (c2†′ ab ad bd)) ▸
      (at 2 2 (X b c ∷ X c d ∷ []) (c2†′ bc bd cd)) ▸
      (at 1 2 (X a c ∷ X a b ∷ []) (sym (c2†′ ab ac bc))) ▸
      (at 0 2 ([]) (axiom (a2 ac))) ▸
      done)

-- Conjugating a letter by X_[x,y] exchanges x and y in it.
rX-xy : ∀ {x y : Fin N} → x ≢ y → X x y • X x y • X x y ≈ X y x
rX-xy {x} {y} xy =
  run {X x y ∷ X x y ∷ X x y ∷ []}
      {X y x ∷ []}
    ( (at 0 2 ([]) (axiom (a2 xy))) ▸
      (at 0 1 (X y x ∷ []) (e1 xy)) ▸
      done)

rX-yx : ∀ {x y : Fin N} → x ≢ y → X x y • X y x • X x y ≈ X x y
rX-yx {x} {y} xy =
  run {X x y ∷ X y x ∷ X x y ∷ []}
      {X x y ∷ []}
    ( (at 1 1 (X x y ∷ []) (e1 (sy xy))) ▸
      (at 0 2 ([]) (axiom (a2 xy))) ▸
      done)

rX-xo : ∀ {x y b : Fin N} → x ≢ y → x ≢ b → y ≢ b → X x y • X x b • X x y ≈ X y b
rX-xo {x} {y} {b} xy xb yb =
  run {X x y ∷ X x b ∷ X x y ∷ []}
      {X y b ∷ []}
    ( (at 0 2 (X y b ∷ X x y ∷ []) (c2 xy xb yb)) ▸
      (at 1 2 ([]) (axiom (a2 xy))) ▸
      done)

rX-yo : ∀ {x y b : Fin N} → x ≢ y → x ≢ b → y ≢ b → X x y • X y b • X x y ≈ X x b
rX-yo {x} {y} {b} xy xb yb =
  run {X x y ∷ X y b ∷ X x y ∷ []}
      {X x b ∷ []}
    ( (at 0 1 (X y x ∷ []) (e1 xy)) ▸
      (at 2 1 (X y x ∷ []) (e1 xy)) ▸
      (at 0 2 (X x b ∷ X y x ∷ []) (c2 (sy xy) yb xb)) ▸
      (at 1 2 ([]) (axiom (a2 (sy xy)))) ▸
      done)

rX-ox : ∀ {x y a : Fin N} → x ≢ y → x ≢ a → y ≢ a → X x y • X a x • X x y ≈ X a y
rX-ox {x} {y} {a} xy xa ya =
  run {X x y ∷ X a x ∷ X x y ∷ []}
      {X a y ∷ []}
    ( (at 1 1 (X x a ∷ []) (e1 (sy xa))) ▸
      (at 0 2 (X y a ∷ X x y ∷ []) (c2 xy xa ya)) ▸
      (at 1 2 ([]) (axiom (a2 xy))) ▸
      (at 0 1 (X a y ∷ []) (e1 ya)) ▸
      done)

rX-oy : ∀ {x y a : Fin N} → x ≢ y → x ≢ a → y ≢ a → X x y • X a y • X x y ≈ X a x
rX-oy {x} {y} {a} xy xa ya =
  run {X x y ∷ X a y ∷ X x y ∷ []}
      {X a x ∷ []}
    ( (at 0 1 (X y x ∷ []) (e1 xy)) ▸
      (at 1 1 (X y a ∷ []) (e1 (sy ya))) ▸
      (at 2 1 (X y x ∷ []) (e1 xy)) ▸
      (at 0 2 (X x a ∷ X y x ∷ []) (c2 (sy xy) ya xa)) ▸
      (at 1 2 ([]) (axiom (a2 (sy xy)))) ▸
      (at 0 1 (X a x ∷ []) (e1 xa)) ▸
      done)

rX-oo : ∀ {x y a b : Fin N} → x ≢ y → x ≢ a → x ≢ b → y ≢ a → y ≢ b → a ≢ b → X x y • X a b • X x y ≈ X a b
rX-oo {x} {y} {a} {b} xy xa xb ya yb ab =
  run {X x y ∷ X a b ∷ X x y ∷ []}
      {X a b ∷ []}
    ( (at 0 2 (X a b ∷ X x y ∷ []) (b3 ab (sy xa) (sy ya) (sy xb) (sy yb) xy)) ▸
      (at 1 2 ([]) (axiom (a2 xy))) ▸
      done)

rH-xy : ∀ {x y : Fin N} → x ≢ y → X x y • H x y • X x y ≈ H y x
rH-xy {x} {y} xy =
  run {X x y ∷ H x y ∷ X x y ∷ []}
      {H y x ∷ []}
    ( (at 0 3 (H y x ∷ []) (sym (e2 xy))) ▸
      done)

rH-yx : ∀ {x y : Fin N} → x ≢ y → X x y • H y x • X x y ≈ H x y
rH-yx {x} {y} xy =
  run {X x y ∷ H y x ∷ X x y ∷ []}
      {H x y ∷ []}
    ( (at 1 1 (X x y ∷ H x y ∷ X x y ∷ []) (e2 xy)) ▸
      (at 0 2 ([]) (axiom (a2 xy))) ▸
      (at 1 2 ([]) (axiom (a2 xy))) ▸
      done)

rH-xo : ∀ {x y b : Fin N} → x ≢ y → x ≢ b → y ≢ b → X x y • H x b • X x y ≈ H y b
rH-xo {x} {y} {b} xy xb yb =
  run {X x y ∷ H x b ∷ X x y ∷ []}
      {H y b ∷ []}
    ( (at 0 2 (H y b ∷ X x y ∷ []) (c4 xy xb yb)) ▸
      (at 1 2 ([]) (axiom (a2 xy))) ▸
      done)

rH-yo : ∀ {x y b : Fin N} → x ≢ y → x ≢ b → y ≢ b → X x y • H y b • X x y ≈ H x b
rH-yo {x} {y} {b} xy xb yb =
  run {X x y ∷ H y b ∷ X x y ∷ []}
      {H x b ∷ []}
    ( (at 0 1 (X y x ∷ []) (e1 xy)) ▸
      (at 2 1 (X y x ∷ []) (e1 xy)) ▸
      (at 0 2 (H x b ∷ X y x ∷ []) (c4 (sy xy) yb xb)) ▸
      (at 1 2 ([]) (axiom (a2 (sy xy)))) ▸
      done)

rH-ox : ∀ {x y a : Fin N} → x ≢ y → x ≢ a → y ≢ a → X x y • H a x • X x y ≈ H a y
rH-ox {x} {y} {a} xy xa ya =
  run {X x y ∷ H a x ∷ X x y ∷ []}
      {H a y ∷ []}
    ( (at 0 1 (X y x ∷ []) (e1 xy)) ▸
      (at 2 1 (X y x ∷ []) (e1 xy)) ▸
      (at 0 2 (H a y ∷ X y x ∷ []) (sym (c5†′ (sy ya) (sy xa) (sy xy)))) ▸
      (at 1 2 ([]) (axiom (a2 (sy xy)))) ▸
      done)

rH-oy : ∀ {x y a : Fin N} → x ≢ y → x ≢ a → y ≢ a → X x y • H a y • X x y ≈ H a x
rH-oy {x} {y} {a} xy xa ya =
  run {X x y ∷ H a y ∷ X x y ∷ []}
      {H a x ∷ []}
    ( (at 0 2 (H a x ∷ X x y ∷ []) (sym (c5†′ (sy xa) (sy ya) xy))) ▸
      (at 1 2 ([]) (axiom (a2 xy))) ▸
      done)

rH-oo : ∀ {x y a b : Fin N} → x ≢ y → x ≢ a → x ≢ b → y ≢ a → y ≢ b → a ≢ b → X x y • H a b • X x y ≈ H a b
rH-oo {x} {y} {a} {b} xy xa xb ya yb ab =
  run {X x y ∷ H a b ∷ X x y ∷ []}
      {H a b ∷ []}
    ( (at 0 2 (H a b ∷ X x y ∷ []) (sym (b5 xy xa xb ya yb ab))) ▸
      (at 1 2 ([]) (axiom (a2 xy))) ▸
      done)

rZ-x : ∀ {x y : Fin N} → x ≢ y → X x y • −1 x • X x y ≈ −1 y
rZ-x {x} {y} xy =
  run {X x y ∷ −1 x ∷ X x y ∷ []}
      {−1 y ∷ []}
    ( (at 1 2 (X x y ∷ −1 y ∷ []) (axiom (c1 xy))) ▸
      (at 0 2 ([]) (axiom (a2 xy))) ▸
      done)

rZ-y : ∀ {x y : Fin N} → x ≢ y → X x y • −1 y • X x y ≈ −1 x
rZ-y {x} {y} xy =
  run {X x y ∷ −1 y ∷ X x y ∷ []}
      {−1 x ∷ []}
    ( (at 0 1 (X y x ∷ []) (e1 xy)) ▸
      (at 2 1 (X y x ∷ []) (e1 xy)) ▸
      (at 1 2 (X y x ∷ −1 x ∷ []) (axiom (c1 (sy xy)))) ▸
      (at 0 2 ([]) (axiom (a2 (sy xy)))) ▸
      done)

rZ-o : ∀ {x y a : Fin N} → x ≢ y → x ≢ a → y ≢ a → X x y • −1 a • X x y ≈ −1 a
rZ-o {x} {y} {a} xy xa ya =
  run {X x y ∷ −1 a ∷ X x y ∷ []}
      {−1 a ∷ []}
    ( (at 0 2 (−1 a ∷ X x y ∷ []) (sym (b2 xy xa ya))) ▸
      (at 1 2 ([]) (axiom (a2 xy))) ▸
      done)
