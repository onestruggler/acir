------------------------------------------------------------------------
-- Presentations of groups
--
-- Independent tensor factors commute in the physical vector semantics.
-- The first-wire rows are computed independently of the circuit theory.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.TensorCommutation where

open import Data.Bool.Base using (Bool ; false ; true ; _xor_ ; _∧_)
open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_^_ to _^ℕ_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; _•_)
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.GeneralN.Semantics as S
import Examples.Groups.CCX+H.GeneralN.ShiftSemantics as Shift
open import Examples.Groups.CCX+H.GeneralN.ActionLinearity using (combine ; combine-! ; action-linear)
import Examples.Groups.CCX+H.GeneralN.HadamardKernel as Kernel
import Examples.Groups.CCX+HH.EncodingSemantics.Structural as Structural
import Examples.Groups.CCX+HH.EncodingSemantics.Blocks as Blocks
import Examples.Groups.CCX+HH.EncodingSemantics.Interchange as Interchange
import Examples.Groups.CCX+HH.EncodingSemantics.Coordinates as Coordinates
import Examples.Groups.CCX+HH-TwoLevel.EmbedAction as EmbedAction
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as A
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι)
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition using (select)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating ; contiguous)
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring as R
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R2
open R2 using (D ; RingD ; AdjointD ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
import Algebra.Properties.Ring as RingProperties

private
  module DQ = Structural R.isCommutativeRing-D R.adj-D R.½
  module K = Kernel R.isCommutativeRing-D R.adj-D R.½ R.√½ R.√½-sq R.√½-half
  module B = Blocks R.isCommutativeRing-D R.adj-D R.½
  module I = Interchange R.isCommutativeRing-D R.adj-D R.½
  module EA = EmbedAction R.isCommutativeRing-D R.adj-D R.½
  module RP = RingProperties R2.DR.ring
  open EA using (restrict ; restrict-!)
  open A using (_!_ ; vec-ext)

row : ∀ n → Bool → S.State (suc n) → S.State n
row n b = restrict (select (alternating (2 ^ℕ n)) b)

private
  restrict-combine : ∀ {m n} (e : Emb m n) a b (u v : Vec D n) →
    restrict e (combine a b u v) ≡ combine a b (restrict e u) (restrict e v)
  restrict-combine e a b u v = vec-ext λ i →
    trans (restrict-! e (combine a b u v) i)
      (trans (combine-! a b u v (ι e i))
        (trans (cong₂ (λ x y → a *ᴰ x +ᴰ b *ᴰ y)
          (sym (restrict-! e u i)) (sym (restrict-! e v i)))
          (sym (combine-! a b (restrict e u) (restrict e v) i))))

  -- A first-wire row rule survives another independent top spectator.
  lift-row : ∀ n (f : S.State (suc n) → S.State (suc n))
    (Φ : ∀ {m} → Vec D m → Vec D m → Vec D m) →
    (∀ {m l} (e : Emb m l) u v → restrict e (Φ u v) ≡ Φ (restrict e u) (restrict e v)) →
    ∀ b → (∀ v → row n b (f v) ≡ Φ (row n false v) (row n true v)) →
    ∀ v → row (suc n) b (DQ.top {suc n} f v) ≡
      Φ (row (suc n) false v) (row (suc n) true v)
  lift-row n f Φ natural b rule v = B.restrict-ext (contiguous (2 ^ℕ n))
    (at false) (at true)
    where
    module Square = I.Square (alternating (2 ^ℕ n)) (contiguous (2 ^ℕ n))
      (contiguous (2 ^ℕ suc n)) (alternating (2 ^ℕ suc n)) (Coordinates.commute (2 ^ℕ n))
    at : ∀ a → restrict (select (contiguous (2 ^ℕ n)) a)
      (row (suc n) b (DQ.top {suc n} f v)) ≡
      restrict (select (contiguous (2 ^ℕ n)) a)
        (Φ (row (suc n) false v) (row (suc n) true v))
    at a = trans (sym (Square.restrict-commute a b (DQ.top {suc n} f v)))
      (trans (cong (row n b) (I.duplicate-restrict (contiguous (2 ^ℕ suc n)) f a v))
        (trans (rule (restrict (select (contiguous (2 ^ℕ suc n)) a) v))
          (trans (cong₂ Φ (Square.restrict-commute a false v) (Square.restrict-commute a true v))
            (sym (natural (select (contiguous (2 ^ℕ n)) a)
              (row (suc n) false v) (row (suc n) true v))))))

  xrow : ∀ {m} → Bool → Vec D m → Vec D m → Vec D m
  xrow false u v = v
  xrow true u v = u

  xrow-natural : ∀ {m n} (e : Emb m n) b u v →
    restrict e (xrow b u v) ≡ xrow b (restrict e u) (restrict e v)
  xrow-natural e false u v = refl
  xrow-natural e true u v = refl

  hrow : ∀ {m} → Bool → Vec D m → Vec D m → Vec D m
  hrow false = combine R.√½ R.√½
  hrow true = combine R.√½ (-ᴰ R.√½)

  hrow-natural : ∀ {m n} (e : Emb m n) b u v →
    restrict e (hrow b u v) ≡ hrow b (restrict e u) (restrict e v)
  hrow-natural e false = restrict-combine e R.√½ R.√½
  hrow-natural e true = restrict-combine e R.√½ (-ᴰ R.√½)

  hminus : ∀ a b → R.√½ *ᴰ (a +ᴰ -ᴰ b) ≡ R.√½ *ᴰ a +ᴰ (-ᴰ R.√½) *ᴰ b
  hminus a b = trans (R2.DR.distribˡ R.√½ a (-ᴰ b))
    (cong (R.√½ *ᴰ a +ᴰ_) (trans (sym (RP.-‿distribʳ-* R.√½ b))
      (RP.-‿distribˡ-* R.√½ b)))

  x-rows : ∀ n b v → row n b (DQ.x n v) ≡ xrow b (row n false v) (row n true v)
  x-rows zero false (a ∷ b ∷ []) = refl
  x-rows zero true (a ∷ b ∷ []) = refl
  x-rows (suc n) b = lift-row n (DQ.x n) (xrow b)
    (λ e → xrow-natural e b) b (x-rows n b)

  h-rows : ∀ n b v → row n b (K.hbase n v) ≡ hrow b (row n false v) (row n true v)
  h-rows zero false (a ∷ b ∷ []) = cong (_∷ []) (R2.DR.distribˡ R.√½ a b)
  h-rows zero true (a ∷ b ∷ []) = cong (_∷ []) (hminus a b)
  h-rows (suc n) b = lift-row n (K.hbase n) (hrow b)
    (λ e → hrow-natural e b) b (h-rows n b)

  rows-commute : ∀ n (f : S.State n → S.State n)
    (local : S.State (suc n) → S.State (suc n))
    (Φ : Bool → S.State n → S.State n → S.State n) →
    (∀ b v → row n b (local v) ≡ Φ b (row n false v) (row n true v)) →
    (∀ b u v → f (Φ b u v) ≡ Φ b (f u) (f v)) →
    ∀ v → DQ.bottom {n} f (local v) ≡ local (DQ.bottom {n} f v)
  rows-commute n f local Φ rule commute v = B.restrict-ext (alternating (2 ^ℕ n))
    (at false) (at true)
    where
    row-bottom : ∀ b z → row n b (DQ.bottom {n} f z) ≡ f (row n b z)
    row-bottom = I.duplicate-restrict (alternating (2 ^ℕ n)) f
    at : ∀ b → row n b (DQ.bottom {n} f (local v)) ≡ row n b (local (DQ.bottom {n} f v))
    at b = trans (row-bottom b (local v))
      (trans (cong f (rule b v))
        (trans (commute b (row n false v) (row n true v))
          (trans (cong₂ (Φ b) (sym (row-bottom false v)) (sym (row-bottom true v)))
            (sym (rule b (DQ.bottom {n} f v))))))

  one-local : ∀ {n} (w : Circuit n) (h : Gate 1) v →
    DQ.bottom {n} (S.action w) (S.gate-action (gate₁ {n} h) v) ≡
    S.gate-action (gate₁ {n} h) (DQ.bottom {n} (S.action w) v)
  one-local {n} w X-gate = rows-commute n (S.action w) (DQ.x n) xrow (x-rows n)
    (λ { false u v → refl ; true u v → refl })
  one-local {n} w H-gate = rows-commute n (S.action w) (K.hbase n) hrow (h-rows n)
    (λ { false → action-linear w R.√½ R.√½ ; true → action-linear w R.√½ (-ᴰ R.√½) })

comm₁ : ∀ {n} (w : Circuit n) (h : Gate 1) v →
  S.action ((w ↑) • [ gate₁ h ]ʷ) v ≡ S.action ([ gate₁ h ]ʷ • (w ↑)) v
comm₁ {n} w h v = trans (Shift.correct w (S.gate-action (gate₁ {n} h) v))
  (trans (one-local w h v) (cong (S.gate-action (gate₁ {n} h)) (sym (Shift.correct w v))))

private
  row₂ : ∀ n → Bool → Bool → S.State (suc (suc n)) → S.State n
  row₂ n a b v = row n b (row (suc n) a v)

  row₃ : ∀ n → Bool → Bool → Bool → S.State (suc (suc (suc n))) → S.State n
  row₃ n a b c v = row n c (row₂ (suc n) a b v)

  row₂-ext : ∀ n {u v : S.State (suc (suc n))} →
    (∀ a b → row₂ n a b u ≡ row₂ n a b v) → u ≡ v
  row₂-ext n eq = B.restrict-ext (alternating (2 ^ℕ suc n))
    (B.restrict-ext (alternating (2 ^ℕ n)) (eq false false) (eq false true))
    (B.restrict-ext (alternating (2 ^ℕ n)) (eq true false) (eq true true))

  row₃-ext : ∀ n {u v : S.State (suc (suc (suc n)))} →
    (∀ a b c → row₃ n a b c u ≡ row₃ n a b c v) → u ≡ v
  row₃-ext n eq = row₂-ext (suc n) λ a b →
    B.restrict-ext (alternating (2 ^ℕ n)) (eq a b false) (eq a b true)

  row-top-swap : ∀ n a b v →
    row n b (restrict (select (contiguous (2 ^ℕ suc n)) a) v) ≡
    restrict (select (contiguous (2 ^ℕ n)) a) (row (suc n) b v)
  row-top-swap n = I.Square.restrict-commute
    (alternating (2 ^ℕ n)) (contiguous (2 ^ℕ n))
    (contiguous (2 ^ℕ suc n)) (alternating (2 ^ℕ suc n)) (Coordinates.commute (2 ^ℕ n))

  row₂-top-swap : ∀ n t a b v →
    row₂ n a b (restrict (select (contiguous (2 ^ℕ suc (suc n))) t) v) ≡
    restrict (select (contiguous (2 ^ℕ n)) t) (row₂ (suc n) a b v)
  row₂-top-swap n t a b v = trans (cong (row n b) (row-top-swap (suc n) t a v))
    (row-top-swap n t b (row (suc (suc n)) a v))

  row₃-top-swap : ∀ n t a b c v →
    row₃ n a b c (restrict (select (contiguous (2 ^ℕ suc (suc (suc n)))) t) v) ≡
    restrict (select (contiguous (2 ^ℕ n)) t) (row₃ (suc n) a b c v)
  row₃-top-swap n t a b c v = trans (cong (row n c) (row₂-top-swap (suc n) t a b v))
    (row-top-swap n t c (row₂ (suc (suc n)) a b v))

  cx-rows : ∀ n a b v → row₂ n a b (DQ.cx n v) ≡ row₂ n (a xor b) b v
  cx-rows zero false false (a ∷ b ∷ c ∷ d ∷ []) = refl
  cx-rows zero false true (a ∷ b ∷ c ∷ d ∷ []) = refl
  cx-rows zero true false (a ∷ b ∷ c ∷ d ∷ []) = refl
  cx-rows zero true true (a ∷ b ∷ c ∷ d ∷ []) = refl
  cx-rows (suc n) a b v = B.restrict-ext (contiguous (2 ^ℕ n)) (at false) (at true)
    where
    at : ∀ t → restrict (select (contiguous (2 ^ℕ n)) t) (row₂ (suc n) a b (DQ.cx (suc n) v)) ≡
      restrict (select (contiguous (2 ^ℕ n)) t) (row₂ (suc n) (a xor b) b v)
    at t = trans (sym (row₂-top-swap n t a b (DQ.cx (suc n) v)))
      (trans (cong (row₂ n a b) (I.duplicate-restrict (contiguous (2 ^ℕ suc (suc n))) (DQ.cx n) t v))
        (trans (cx-rows n a b (restrict (select (contiguous (2 ^ℕ suc (suc n))) t) v))
          (row₂-top-swap n t (a xor b) b v)))

  ccx-rows : ∀ n a b c v → row₃ n a b c (DQ.ccx n v) ≡ row₃ n (a xor (b ∧ c)) b c v
  ccx-rows zero false false false (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
  ccx-rows zero false false true (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
  ccx-rows zero false true false (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
  ccx-rows zero false true true (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
  ccx-rows zero true false false (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
  ccx-rows zero true false true (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
  ccx-rows zero true true false (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
  ccx-rows zero true true true (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
  ccx-rows (suc n) a b c v = B.restrict-ext (contiguous (2 ^ℕ n)) (at false) (at true)
    where
    at : ∀ t → restrict (select (contiguous (2 ^ℕ n)) t) (row₃ (suc n) a b c (DQ.ccx (suc n) v)) ≡
      restrict (select (contiguous (2 ^ℕ n)) t) (row₃ (suc n) (a xor (b ∧ c)) b c v)
    at t = trans (sym (row₃-top-swap n t a b c (DQ.ccx (suc n) v)))
      (trans (cong (row₃ n a b c) (I.duplicate-restrict
        (contiguous (2 ^ℕ suc (suc (suc n)))) (DQ.ccx n) t v))
        (trans (ccx-rows n a b c (restrict (select (contiguous (2 ^ℕ suc (suc (suc n)))) t) v))
          (row₃-top-swap n t (a xor (b ∧ c)) b c v)))

  bottom₂ : ∀ {n} → (S.State n → S.State n) → S.State (suc (suc n)) → S.State (suc (suc n))
  bottom₂ {n} f = DQ.bottom {suc n} (DQ.bottom {n} f)

  bottom₃ : ∀ {n} → (S.State n → S.State n) → S.State (suc (suc (suc n))) → S.State (suc (suc (suc n)))
  bottom₃ {n} f = DQ.bottom {suc (suc n)} (bottom₂ {n} f)

  row₂-bottom : ∀ n f a b v → row₂ n a b (bottom₂ {n} f v) ≡ f (row₂ n a b v)
  row₂-bottom n f a b v = trans (cong (row n b)
    (I.duplicate-restrict (alternating (2 ^ℕ suc n)) (DQ.bottom {n} f) a v))
    (I.duplicate-restrict (alternating (2 ^ℕ n)) f b (row (suc n) a v))

  row₃-bottom : ∀ n f a b c v → row₃ n a b c (bottom₃ {n} f v) ≡ f (row₃ n a b c v)
  row₃-bottom n f a b c v = trans (cong (row₂ n b c)
    (I.duplicate-restrict (alternating (2 ^ℕ suc (suc n))) (bottom₂ {n} f) a v))
    (row₂-bottom n f b c (row (suc (suc n)) a v))

  two-local : ∀ n f v → bottom₂ {n} f (DQ.cx n v) ≡ DQ.cx n (bottom₂ {n} f v)
  two-local n f v = row₂-ext n λ a b → trans (row₂-bottom n f a b (DQ.cx n v))
    (trans (cong f (cx-rows n a b v))
      (sym (trans (cx-rows n a b (bottom₂ {n} f v)) (row₂-bottom n f (a xor b) b v))))

  three-local : ∀ n f v → bottom₃ {n} f (DQ.ccx n v) ≡ DQ.ccx n (bottom₃ {n} f v)
  three-local n f v = row₃-ext n λ a b c → trans (row₃-bottom n f a b c (DQ.ccx n v))
    (trans (cong f (ccx-rows n a b c v))
      (sym (trans (ccx-rows n a b c (bottom₃ {n} f v))
        (row₃-bottom n f (a xor (b ∧ c)) b c v))))

  shift₂ : ∀ {n} (w : Circuit n) v → S.action ((w ↑) ↑) v ≡ bottom₂ {n} (S.action w) v
  shift₂ {n} w v = trans (Shift.correct (w ↑) v)
    (B.parallel-cong (alternating (2 ^ℕ suc n)) (Shift.correct w) (Shift.correct w) v)

  shift₃ : ∀ {n} (w : Circuit n) v → S.action (((w ↑) ↑) ↑) v ≡ bottom₃ {n} (S.action w) v
  shift₃ {n} w v = trans (Shift.correct ((w ↑) ↑) v)
    (B.parallel-cong (alternating (2 ^ℕ suc (suc n))) (shift₂ w) (shift₂ w) v)

comm₂ : ∀ {n} (w : Circuit n) (h : Gate 2) v →
  S.action (((w ↑) ↑) • [ gate₂ h ]ʷ) v ≡ S.action ([ gate₂ h ]ʷ • ((w ↑) ↑)) v
comm₂ {n} w CX-gate v = trans (shift₂ w (DQ.cx n v))
  (trans (two-local n (S.action w) v) (cong (DQ.cx n) (sym (shift₂ w v))))

comm₃ : ∀ {n} (w : Circuit n) (h : Gate 3) v →
  S.action ((((w ↑) ↑) ↑) • [ gate₃ h ]ʷ) v ≡ S.action ([ gate₃ h ]ʷ • (((w ↑) ↑) ↑)) v
comm₃ {n} w CCX-gate v = trans (shift₃ w (DQ.ccx n v))
  (trans (three-local n (S.action w) v) (cong (DQ.ccx n) (sym (shift₃ w v))))
