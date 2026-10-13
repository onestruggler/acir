------------------------------------------------------------------------
-- Presentations of groups
--
-- The adjacent classical compiler has its stated action in the actual
-- dyadic vector semantics.  SWAP is expanded into CX HH CX HH CX;
-- every further wire is treated by the tensor semantics, uniformly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics where

open import Data.Bool.Base using (Bool ; false ; true)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _^_ ; z≤n ; s≤s)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁ ; ₂)
open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (D ; isCommutativeRing-D ; adj-D ; ½ᴰ ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis
open import Examples.Groups.CCX+HH.GeneralN.BasisVectors
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (parallel ; parallel-id ; parallel-compose ; parallel-cong)
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition using (Partition ; select)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (ι)

private variable n m : ℕ

-- Word action from the independent physical gate semantics.
quantum : H.Circuit n → Q.State n → Q.State n
quantum [ g ]ʷ = Q.gate-action g
quantum ε v = v
quantum (u • v) x = quantum u (quantum v x)

encoding-action : ∀ (w : H.Circuit n) v → A.actVʷ (E.encode w) v ≡ quantum w v
encoding-action [ g ]ʷ = Q.encoding-correct-action g
encoding-action ε v = refl
encoding-action (u • w) v = trans
  (cong (A.actVʷ (E.encode u)) (encoding-action w v))
  (encoding-action u (quantum w v))

quantum-shift : ∀ (w : H.Circuit n) v → quantum (w H.↑) v ≡ Q.bottom {n} (quantum w) v
quantum-shift [ g ]ʷ v = refl
quantum-shift {n} ε v = sym (parallel-id (alternating (2 ^ n)) v)
quantum-shift {n} (u • w) v = trans
  (cong (quantum (u H.↑)) (quantum-shift w v))
  (trans (quantum-shift u (Q.bottom {n} (quantum w) v))
    (parallel-compose (alternating _) (quantum u) (quantum u) (quantum w) (quantum w) v))

swap₀ : Q.State 2 → Q.State 2
swap₀ (a ∷ b ∷ c ∷ d ∷ []) = a ∷ c ∷ b ∷ d ∷ []

swap : ∀ n → Q.State (suc (suc n)) → Q.State (suc (suc n))
swap zero = swap₀
swap (suc n) = Q.top {suc (suc n)} (swap n)

private
  x12 : T.Gen 4
  x12 = T.X-gen ₁ ₂ (s≤s (s≤s z≤n))

  opaque
    unfolding A.actV A.set₁ A.set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

    swap-matrix : A.⟦ E.encode (H.Ex {0}) ⟧ᵐ ≡ A.⟦ [ x12 ]ʷ ⟧ᵐ
    swap-matrix = refl

    x12-action : ∀ v → A.actV x12 v ≡ swap₀ v
    x12-action (a ∷ b ∷ c ∷ d ∷ []) = refl

  swap-base : ∀ v → quantum (H.Ex {0}) v ≡ swap₀ v
  swap-base v = trans (sym (encoding-action (H.Ex {0}) v))
    (trans (A.same-action (E.encode (H.Ex {0})) [ x12 ]ʷ swap-matrix v) (x12-action v))

  ex-parallel : ∀ (p : Partition m n) (c h : Vec D m → Vec D m) v →
    parallel p c c (parallel p h h (parallel p c c (parallel p h h (parallel p c c v)))) ≡
    parallel p (λ x → c (h (c (h (c x))))) (λ x → c (h (c (h (c x))))) v
  ex-parallel p c h v = trans
    (cong (parallel p c c) (cong (parallel p h h) (cong (parallel p c c)
      (parallel-compose p h h c c v))))
    (trans (cong (parallel p c c) (cong (parallel p h h)
      (parallel-compose p c c (λ x → h (c x)) (λ x → h (c x)) v)))
      (trans (cong (parallel p c c)
        (parallel-compose p h h (λ x → c (h (c x))) (λ x → c (h (c x))) v))
        (parallel-compose p c c (λ x → h (c (h (c x)))) (λ x → h (c (h (c x)))) v)))

swap-correct : ∀ n v → quantum (H.Ex {n}) v ≡ swap n v
swap-correct zero = swap-base
swap-correct (suc n) v = trans (ex-parallel (contiguous _) (Q.cx n) (Q.hh n) v)
  (parallel-cong (contiguous _) (swap-correct n) (swap-correct n) v)

classical₀ : C.Gen n → Q.State n → Q.State n
classical₀ (C.gate₀ ())
classical₀ (C.gate₁ {n} C.X-gate) = Q.x n
classical₀ (C.gate₂ {n} C.CX-gate) = Q.cx n
classical₀ (C.gate₂ {n} C.SWAP-gate) = swap n
classical₀ (C.gate₃ {n} C.CCX-gate) = Q.ccx n
classical₀ (C._↥ {n} g) = Q.bottom {n} (classical₀ g)

classical : C.Circuit n → Q.State n → Q.State n
classical [ g ]ʷ = classical₀ g
classical ε v = v
classical (u • w) v = classical u (classical w v)

physical₀-correct : ∀ (g : C.Gen n) v → quantum (C.physical₀ g) v ≡ classical₀ g v
physical₀-correct (C.gate₀ ()) v
physical₀-correct (C.gate₁ C.X-gate) v = refl
physical₀-correct (C.gate₂ C.CX-gate) v = refl
physical₀-correct (C.gate₂ {n} C.SWAP-gate) v = swap-correct n v
physical₀-correct (C.gate₃ C.CCX-gate) v = refl
physical₀-correct (g C.↥) v = trans (quantum-shift (C.physical₀ g) v)
  (parallel-cong (alternating _) (physical₀-correct g) (physical₀-correct g) v)

physical-correct : ∀ (w : C.Circuit n) v → quantum (C.physical w) v ≡ classical w v
physical-correct [ g ]ʷ = physical₀-correct g
physical-correct ε v = refl
physical-correct (u • w) v = trans (cong (quantum (C.physical u)) (physical-correct w v))
  (physical-correct u (classical w v))

ket : ∀ n → C.State n → Q.State n
ket n s = basis (idx n s)

ket-cong : ∀ n {s t} → s C.≈s t → ket n s ≡ ket n t
ket-cong n eq = cong basis (idx-cong n eq)

private
  top-ket : ∀ n (f : Q.State n → Q.State n) (F : C.State n → C.State n) →
    f (zeroV (2 ^ n)) ≡ zeroV (2 ^ n) → (∀ s → f (ket n s) ≡ ket n (F s)) →
    ∀ s → Q.top {n} f (ket (suc n) s) ≡
      ket (suc n) (append n (F (prefix n s)) (last n s))
  top-ket n f F f0 fs s = trans
    (cong (Q.top {n} f) (trans (sym (ket-cong (suc n) (append-view n s)))
      (cong basis (idx-append n (prefix n s) (last n s)))))
    (trans (parallel-basis (contiguous _) f (last n s)
      (idx n (prefix n s)) (idx n (F (prefix n s))) f0 (fs (prefix n s)))
      (cong basis (sym (idx-append n (F (prefix n s)) (last n s)))))

  bottom-ket : ∀ n (f : Q.State n → Q.State n) (F : C.State n → C.State n) →
    f (zeroV (2 ^ n)) ≡ zeroV (2 ^ n) → (∀ s → f (ket n s) ≡ ket n (F s)) →
    ∀ s → Q.bottom {n} f (ket (suc n) s) ≡ ket (suc n) (cons (s zero) (F (C.lower s)))
  bottom-ket n f F f0 fs s = parallel-basis (alternating _) f (s zero)
    (idx n (C.lower s)) (idx n (F (C.lower s))) f0 (fs (C.lower s))

  x-zero : ∀ n → Q.x n (zeroV (2 ^ suc n)) ≡ zeroV (2 ^ suc n)
  x-zero zero = refl
  x-zero (suc n) = parallel-zero (contiguous _) (Q.x n) (Q.x n) (x-zero n) (x-zero n)

  cx-zero : ∀ n → Q.cx n (zeroV (2 ^ suc (suc n))) ≡ zeroV (2 ^ suc (suc n))
  cx-zero zero = refl
  cx-zero (suc n) = parallel-zero (contiguous _) (Q.cx n) (Q.cx n) (cx-zero n) (cx-zero n)

  ccx-zero : ∀ n → Q.ccx n (zeroV (2 ^ suc (suc (suc n)))) ≡ zeroV (2 ^ suc (suc (suc n)))
  ccx-zero zero = refl
  ccx-zero (suc n) = parallel-zero (contiguous _) (Q.ccx n) (Q.ccx n) (ccx-zero n) (ccx-zero n)

  swap-zero : ∀ n → swap n (zeroV (2 ^ suc (suc n))) ≡ zeroV (2 ^ suc (suc n))
  swap-zero zero = refl
  swap-zero (suc n) = parallel-zero (contiguous _) (swap n) (swap n) (swap-zero n) (swap-zero n)

  x-top : ∀ n s → append (suc n) (C.x (prefix (suc n) s)) (last (suc n) s) C.≈s C.x s
  x-top n s zero = refl
  x-top n s (suc i) = append-view n (C.lower s) i

  cx-top : ∀ n s → append (suc (suc n)) (C.cx (prefix (suc (suc n)) s))
    (last (suc (suc n)) s) C.≈s C.cx s
  cx-top n s zero = refl
  cx-top n s (suc i) = append-view (suc n) (C.lower s) i

  ccx-top : ∀ n s → append (suc (suc (suc n))) (C.ccx (prefix (suc (suc (suc n))) s))
    (last (suc (suc (suc n))) s) C.≈s C.ccx s
  ccx-top n s zero = refl
  ccx-top n s (suc i) = append-view (suc (suc n)) (C.lower s) i

  swap-top : ∀ n s → append (suc (suc n)) (C.swap (prefix (suc (suc n)) s))
    (last (suc (suc n)) s) C.≈s C.swap s
  swap-top n s zero = refl
  swap-top n s (suc zero) = refl
  swap-top n s (suc (suc i)) = append-view n (C.lower (C.lower s)) i

  x-base-ket : ∀ s → Q.x₀ (ket 1 s) ≡ ket 1 (C.x s)
  x-base-ket s with s zero
  ... | false = refl
  ... | true = refl

  cx-base-ket : ∀ s → Q.cx₀ (ket 2 s) ≡ ket 2 (C.cx s)
  cx-base-ket s with s zero | s (suc zero)
  ... | false | false = refl
  ... | false | true = refl
  ... | true | false = refl
  ... | true | true = refl

  swap-base-ket : ∀ s → swap₀ (ket 2 s) ≡ ket 2 (C.swap s)
  swap-base-ket s with s zero | s (suc zero)
  ... | false | false = refl
  ... | false | true = refl
  ... | true | false = refl
  ... | true | true = refl

  ccx-base-ket : ∀ s → Q.ccx₀ (ket 3 s) ≡ ket 3 (C.ccx s)
  ccx-base-ket s with s zero | s (suc zero) | s (suc (suc zero))
  ... | false | false | false = refl
  ... | false | false | true = refl
  ... | false | true | false = refl
  ... | false | true | true = refl
  ... | true | false | false = refl
  ... | true | false | true = refl
  ... | true | true | false = refl
  ... | true | true | true = refl

  x-ket : ∀ n s → Q.x n (ket (suc n) s) ≡ ket (suc n) (C.x s)
  x-ket zero = x-base-ket
  x-ket (suc n) s = trans (top-ket (suc n) (Q.x n) C.x (x-zero n) (x-ket n) s)
    (ket-cong (suc (suc n)) (x-top n s))

  cx-ket : ∀ n s → Q.cx n (ket (suc (suc n)) s) ≡ ket (suc (suc n)) (C.cx s)
  cx-ket zero = cx-base-ket
  cx-ket (suc n) s = trans (top-ket (suc (suc n)) (Q.cx n) C.cx (cx-zero n) (cx-ket n) s)
    (ket-cong (suc (suc (suc n))) (cx-top n s))

  ccx-ket : ∀ n s → Q.ccx n (ket (suc (suc (suc n))) s) ≡ ket (suc (suc (suc n))) (C.ccx s)
  ccx-ket zero = ccx-base-ket
  ccx-ket (suc n) s = trans
    (top-ket (suc (suc (suc n))) (Q.ccx n) C.ccx (ccx-zero n) (ccx-ket n) s)
    (ket-cong (suc (suc (suc (suc n)))) (ccx-top n s))

  swap-ket : ∀ n s → swap n (ket (suc (suc n)) s) ≡ ket (suc (suc n)) (C.swap s)
  swap-ket zero = swap-base-ket
  swap-ket (suc n) s = trans (top-ket (suc (suc n)) (swap n) C.swap (swap-zero n) (swap-ket n) s)
    (ket-cong (suc (suc (suc n))) (swap-top n s))

classical₀-zero : ∀ (g : C.Gen n) → classical₀ g (zeroV (2 ^ n)) ≡ zeroV (2 ^ n)
classical₀-zero (C.gate₀ ())
classical₀-zero (C.gate₁ {n} C.X-gate) = x-zero n
classical₀-zero (C.gate₂ {n} C.CX-gate) = cx-zero n
classical₀-zero (C.gate₂ {n} C.SWAP-gate) = swap-zero n
classical₀-zero (C.gate₃ {n} C.CCX-gate) = ccx-zero n
classical₀-zero (g C.↥) = parallel-zero (alternating _) (classical₀ g) (classical₀ g)
  (classical₀-zero g) (classical₀-zero g)

classical₀-ket : ∀ (g : C.Gen n) s → classical₀ g (ket n s) ≡ ket n (C.act₀ g s)
classical₀-ket (C.gate₀ ()) s
classical₀-ket (C.gate₁ {n} C.X-gate) = x-ket n
classical₀-ket (C.gate₂ {n} C.CX-gate) = cx-ket n
classical₀-ket (C.gate₂ {n} C.SWAP-gate) = swap-ket n
classical₀-ket (C.gate₃ {n} C.CCX-gate) = ccx-ket n
classical₀-ket (C._↥ {n} g) s = trans
  (bottom-ket n (classical₀ g) (C.act₀ g) (classical₀-zero g) (classical₀-ket g) s)
  (ket-cong (suc n) {cons (s zero) (C.act₀ g (C.lower s))} {C.shift (C.act₀ g) s} λ { zero → refl ; (suc i) → refl })

classical-ket : ∀ (w : C.Circuit n) s → classical w (ket n s) ≡ ket n (C.act w s)
classical-ket [ g ]ʷ = classical₀-ket g
classical-ket ε s = refl
classical-ket (u • w) s = trans (cong (classical u) (classical-ket w s))
  (classical-ket u (C.act w s))

-- Actual physical-circuit action, for every computational-basis input.
physical-ket : ∀ (w : C.Circuit n) s → quantum (C.physical w) (ket n s) ≡ ket n (C.act w s)
physical-ket w s = trans (physical-correct w (ket _ s)) (classical-ket w s)

quantum-column : ∀ (w : H.Circuit n) i → A.col (Q.interpret w) i ≡ quantum w (basis i)
quantum-column w i = trans (cong (λ M → A.col M i) (sym (Q.encoding-correct w)))
  (trans (A.col-actMʷ (E.encode w) A.𝕀 i)
    (trans (encoding-action w (A.col A.𝕀 i)) (cong (quantum w) (sym (basis-col i)))))

-- Thus the Boolean action determines every column of the ordinary
-- physical matrix, not just its behavior on a selected input state.
physical-column : ∀ (w : C.Circuit n) i →
  A.col (Q.interpret (C.physical w)) i ≡ ket n (C.act w (bits n i))
physical-column {n} w i = trans (quantum-column (C.physical w) i)
  (trans (cong (quantum (C.physical w)) (cong basis (sym (idx-bits n i))))
    (physical-ket w (bits n i)))
