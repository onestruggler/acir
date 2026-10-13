------------------------------------------------------------------------
-- Presentations of groups
--
-- Tensor kernels for the telescoping HH chain.  The physical Hadamard
-- is specified by its two entries s(a+b), s(a-b).  These definitions
-- do not refer to the auxiliary encoder.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.CCX+H.GeneralN.HadamardKernel
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (h s : A) (s-sq : s * s ≡ h) (s-half : s * s + s * s ≡ 1#)
  where

open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_^_ to _^ℕ_)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NP
import Data.Fin.Base as Fin
import Data.Integer.Base as ℤ
open import Data.Vec.Base using ([] ; _∷_)
import Data.Vec.Base as Vec
import Data.Vec.Properties as VP
import Data.List.Base as List
import Data.List.Properties as LP
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; ε ; _•_)
import Examples.Groups.CCX+HH.Syntactics as C
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.EncodingSemantics.Structural as Structural
import Examples.Groups.CCX+HH.EncodingSemantics.Blocks as Blocks
import Examples.Groups.CCX+HH.EncodingSemantics.Interchange as Interchange
import Examples.Groups.CCX+HH.EncodingSemantics.Append as Append
import Examples.Groups.CCX+H.GeneralN.StructuralEncoding as HE
import Examples.Groups.CCX+H.GeneralN.PairBlocks as PairBlocks
import Examples.Groups.CCX+HH-TwoLevel.EmbedAction as EmbedAction
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition using (left ; right)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary
import Examples.Groups.CCX+HH-TwoLevel.Action as Action
import Quantum.Synthesis.Ring.Properties.Common as Common

open Structural isCR adjI h using (State ; top ; bottom ; gate-action ; hh ; hh₀ ; encoding-correct-action)
open Blocks isCR adjI h using (parallel-id ; parallel-compose ; parallel-cong)
open Action isCR adjI h using (actVʷ ; R ; rowA ; rowB ; rowC ; rowD)

private
  module AR = IsCommutativeRing isCR
  module Solver = Common.ZSolver R
  module I = Interchange isCR adjI h
  module AP = Append isCR adjI h
  module Pairs = PairBlocks (λ a b → s * (a + b)) (λ a b → s * (a + - b))
  open EmbedAction isCR adjI h using (restrict)
  open Solver using (_:+_ ; _:*_ ; :-_ ; _:=_ ; con)

private variable n : ℕ

h₀ : State 1 → State 1
h₀ (a ∷ b ∷ []) = s * (a + b) ∷ s * (a + - b) ∷ []

hbase : (n : ℕ) → State (suc n) → State (suc n)
hbase zero = h₀
hbase (suc n) = top {suc n} (hbase n)

private
  toList-join : ∀ {m} (u v : Vec.Vec A m) →
    Vec.toList (AP.join u v) ≡ Vec.toList u List.++ Vec.toList v
  toList-join u v = trans (VP.toList-++ u (v Vec.++ []))
    (cong (Vec.toList u List.++_)
      (trans (VP.toList-++ v []) (LP.++-identityʳ (Vec.toList v))))

-- Lists erase only the dimension bookkeeping.  The values are still
-- the independently specified tensor kernel on the left and the
-- source's adjacent-pair recursion on the right.
hbase-list : ∀ n v → Vec.toList (hbase n v) ≡ Pairs.flat-list (Vec.toList v)
hbase-list zero (a ∷ b ∷ []) = refl
hbase-list (suc n) v = trans
  (cong (λ w → Vec.toList (hbase (suc n) w)) (sym (AP.join-restrict {m = 2 ^ℕ suc n} v)))
  (trans (at-join lo hi)
    (cong (λ w → Pairs.flat-list (Vec.toList w)) (AP.join-restrict {m = 2 ^ℕ suc n} v)))
  where
  lo = restrict (left (contiguous (2 ^ℕ suc n))) v
  hi = restrict (right (contiguous (2 ^ℕ suc n))) v

  at-join : ∀ u w → Vec.toList (hbase (suc n) (AP.join u w)) ≡
    Pairs.flat-list (Vec.toList (AP.join u w))
  at-join u w = trans
    (cong Vec.toList (AP.parallel-join (hbase n) (hbase n) u w))
    (trans (toList-join (hbase n u) (hbase n w))
      (trans (cong₂ List._++_ (hbase-list n u) (hbase-list n w))
        (sym (trans (cong Pairs.flat-list (toList-join u w))
          (Pairs.flat-list-append-even (2 ^ℕ n) (NP.*-comm 2 (2 ^ℕ n)) u (Vec.toList w))))))

hbase-flat : ∀ n (p : 2 ^ℕ suc n ≡ (2 ^ℕ n) Nat.* 2) v →
  Pairs.cast p (hbase n v) ≡ Pairs.flat (2 ^ℕ n) (Pairs.cast p v)
hbase-flat n p v = trans (sym (VP.cast-is-id refl (Pairs.cast p (hbase n v))))
  (VP.toList-injective refl _ _
  (trans (Pairs.toList-cast p (hbase n v))
    (trans (hbase-list n v)
      (trans (cong Pairs.flat-list (sym (Pairs.toList-cast p v)))
        (sym (Pairs.toList-flat (2 ^ℕ n) (Pairs.cast p v)))))))

private
  half : ∀ a → (s * s + s * s) * a ≡ a
  half a = trans (cong (_* a) s-half) (AR.*-identityˡ a)

  h-inv₁ : ∀ a b → s * (s * (a + b) + s * (a + - b)) ≡ a
  h-inv₁ a b = trans
    (Solver.solve 3 (λ s a b →
      s :* (s :* (a :+ b) :+ s :* (a :+ :- b)) :=
      (s :* s :+ s :* s) :* a) AR.refl s a b) (half a)

  h-inv₂ : ∀ a b → s * (s * (a + b) + - (s * (a + - b))) ≡ b
  h-inv₂ a b = trans
    (Solver.solve 3 (λ s a b →
      s :* (s :* (a :+ b) :+ :- (s :* (a :+ :- b))) :=
      (s :* s :+ s :* s) :* b) AR.refl s a b) (half b)

h₀-invol : ∀ v → h₀ (h₀ v) ≡ v
h₀-invol (a ∷ b ∷ []) = cong₂ _∷_ (h-inv₁ a b)
  (cong₂ _∷_ (h-inv₂ a b) refl)

hbase-invol : ∀ n v → hbase n (hbase n v) ≡ v
hbase-invol zero = h₀-invol
hbase-invol (suc n) v = trans
  (parallel-compose (contiguous (2 ^ℕ suc n))
    (hbase n) (hbase n) (hbase n) (hbase n) v)
  (trans (parallel-cong (contiguous (2 ^ℕ suc n))
    (hbase-invol n) (hbase-invol n) v)
    (parallel-id (contiguous (2 ^ℕ suc n)) v))

private
  tensor-A : ∀ a b c d → rowA a b c d ≡ s * (s * (a + b) + s * (c + d))
  tensor-A a b c d = trans
    (cong (λ z → z * (1# * a + 1# * b + 1# * c + 1# * d)) (sym s-sq))
    (Solver.solve 5 (λ s a b c d →
      (s :* s) :* (con (ℤ.+ 1) :* a :+ con (ℤ.+ 1) :* b :+
                  con (ℤ.+ 1) :* c :+ con (ℤ.+ 1) :* d) :=
      s :* (s :* (a :+ b) :+ s :* (c :+ d))) AR.refl s a b c d)

  tensor-B : ∀ a b c d → rowB a b c d ≡ s * (s * (a + - b) + s * (c + - d))
  tensor-B a b c d = trans
    (cong (λ z → z * (1# * a + (- 1#) * b + 1# * c + (- 1#) * d)) (sym s-sq))
    (Solver.solve 5 (λ s a b c d →
      (s :* s) :* (con (ℤ.+ 1) :* a :+ :- con (ℤ.+ 1) :* b :+
                  con (ℤ.+ 1) :* c :+ :- con (ℤ.+ 1) :* d) :=
      s :* (s :* (a :+ :- b) :+ s :* (c :+ :- d))) AR.refl s a b c d)

  tensor-C : ∀ a b c d → rowC a b c d ≡ s * (s * (a + b) + - (s * (c + d)))
  tensor-C a b c d = trans
    (cong (λ z → z * (1# * a + 1# * b + (- 1#) * c + (- 1#) * d)) (sym s-sq))
    (Solver.solve 5 (λ s a b c d →
      (s :* s) :* (con (ℤ.+ 1) :* a :+ con (ℤ.+ 1) :* b :+
                  :- con (ℤ.+ 1) :* c :+ :- con (ℤ.+ 1) :* d) :=
      s :* (s :* (a :+ b) :+ :- (s :* (c :+ d)))) AR.refl s a b c d)

  tensor-D : ∀ a b c d → rowD a b c d ≡ s * (s * (a + - b) + - (s * (c + - d)))
  tensor-D a b c d = trans
    (cong (λ z → z * (1# * a + (- 1#) * b + (- 1#) * c + 1# * d)) (sym s-sq))
    (Solver.solve 5 (λ s a b c d →
      (s :* s) :* (con (ℤ.+ 1) :* a :+ :- con (ℤ.+ 1) :* b :+
                  :- con (ℤ.+ 1) :* c :+ con (ℤ.+ 1) :* d) :=
      s :* (s :* (a :+ :- b) :+ :- (s :* (c :+ :- d)))) AR.refl s a b c d)

hh₀-tensor : ∀ v → hh₀ v ≡ bottom {1} h₀ (top {1} h₀ v)
hh₀-tensor (a ∷ b ∷ c ∷ d ∷ []) =
  cong₂ _∷_ (tensor-A a b c d) (cong₂ _∷_ (tensor-B a b c d)
    (cong₂ _∷_ (tensor-C a b c d) (cong₂ _∷_ (tensor-D a b c d) refl)))

hh₀-hbase : ∀ v → hh₀ (hbase 1 v) ≡ bottom {1} h₀ v
hh₀-hbase v = trans (hh₀-tensor (hbase 1 v))
  (cong (bottom {1} h₀) (trans
    (parallel-compose (contiguous 2) h₀ h₀ h₀ h₀ v)
    (trans (parallel-cong (contiguous 2) h₀-invol h₀-invol v)
      (parallel-id (contiguous 2) v))))

-- Tensoring the local identity with any number of spectators.
hh-hbase : ∀ n v → hh n (hbase (suc n) v) ≡ bottom {suc n} (hbase n) v
hh-hbase zero = hh₀-hbase
hh-hbase (suc n) v = trans
  (parallel-compose (contiguous (2 ^ℕ suc (suc n)))
    (hh n) (hh n) (hbase (suc n)) (hbase (suc n)) v)
  (trans (parallel-cong (contiguous (2 ^ℕ suc (suc n)))
    (hh-hbase n) (hh-hbase n) v)
    (I.top-bottom (2 ^ℕ suc n) (hbase n) v))

-- Expanding one adjacent HH into H on the upper and then lower wire.
hh-tensor : ∀ n v → hh n v ≡
  bottom {suc n} (hbase n) (hbase (suc n) v)
hh-tensor n v = trans (cong (hh n) (sym (hbase-invol (suc n) v)))
  (hh-hbase n (hbase (suc n) v))

-- Independent physical H on the chosen wire: add low spectators by
-- alternating direct sums, and high spectators through hbase.
hwire : Fin.Fin n → State n → State n
hwire {suc n} Fin.zero = hbase n
hwire {suc zero} (Fin.suc ())
hwire {suc (suc n)} (Fin.suc p) = bottom {suc n} (hwire p)

run : C.Circuit n → State n → State n
run [ g ]ʷ = gate-action g
run ε v = v
run (u • w) v = run u (run w v)

run-correct : ∀ (w : C.Circuit n) v → actVʷ (E.encode w) v ≡ run w v
run-correct [ g ]ʷ = encoding-correct-action g
run-correct ε v = refl
run-correct (u • w) v = trans (cong (actVʷ (E.encode u)) (run-correct w v))
  (run-correct u (run w v))

run-shift : ∀ (w : C.Circuit n) v → run (w C.↑) v ≡ bottom {n} (run w) v
run-shift [ g ]ʷ v = refl
run-shift {n} ε v = sym (parallel-id (alternating (2 ^ℕ n)) v)
run-shift {n} (u • w) v = trans (run-shift u (run (w C.↑) v))
  (trans (cong (bottom {n} (run u)) (run-shift w v))
    (parallel-compose (alternating (2 ^ℕ n)) (run u) (run u) (run w) (run w) v))

-- The HH chain telescopes to a Hadamard on its final wire.
prefix-correct : ∀ {n} (p : Fin.Fin (suc n)) v →
  run (HE.prefix p) (hbase n v) ≡ hwire p v
prefix-correct Fin.zero v = refl
prefix-correct {zero} (Fin.suc ())
prefix-correct {suc n} (Fin.suc p) v = trans
  (run-shift (HE.prefix p) (hh n (hbase (suc n) v)))
  (trans (cong (bottom {suc n} (run (HE.prefix p))) (hh-hbase n v))
    (trans (parallel-compose (alternating (2 ^ℕ suc n))
      (run (HE.prefix p)) (run (HE.prefix p)) (hbase n) (hbase n) v)
      (parallel-cong (alternating (2 ^ℕ suc n)) (prefix-correct p) (prefix-correct p) v)))
