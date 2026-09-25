------------------------------------------------------------------------
-- Presentations of groups
--
-- Four odd entries, for the hard subcase of Case 3 (case 3.2.2.2).
--
-- The generators on numerators at a fixed scale: X, i, K (when γ
-- divides the new entries) and K† written as K i i.  Then, for
-- j < ℓ < j′ < ℓ′ and numerators that differ from a fixed W only at
-- these four indices, the states of the path of (case 3.2.2.2.1) from
-- (1 + a γ³ , 1 + b γ³ , 1 + c γ³ , 1 + d γ³), as in the table of the
-- paper: in each of them the entry j is even.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.Clifford+CS-TwoLevel.FourOdd {n : ℕ} where

open import Data.Bool.Base using (true)
open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_ ; ≢-sym)
open import Relation.Nullary using (Dec ; yes ; no)

open import Algebra.Solver.Ring.AlmostCommutativeRing using (fromCommutativeRing)
import Algebra.Solver.Ring.Simple
open import Instances using (_≟_ ; DEℤ)
open import Quantum.Synthesis.Ring using (DecEqCplx)
open import Quantum.Synthesis.Ring.Properties using (commutativeRing-ZComplex)

open import Word.Base
open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count-lt)
open import Examples.Groups.Clifford+CS-TwoLevel.Column using (nodd)
open import Examples.Groups.Clifford+CS-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics hiding (_!_ ; U)
open import Examples.Groups.Clifford+CS-TwoLevel.Syllable using (i^-action)
open import Examples.Groups.Clifford+CS-TwoLevel.Step using (scV-γmap)

private
  module ZG = Algebra.Solver.Ring.Simple (fromCommutativeRing commutativeRing-ZComplex) (λ x y → x ≟ y)
  open ZG using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

------------------------------------------------------------------------
-- The generators on numerators

K-step : (a b : Fin n) (ab : a < b) (k : ℕ) (V V′ : Vec Z n) →
         V ! a ZR.+ V ! b ≡ γᶻ ZR.* (V′ ! a) → V ! a ZR.- V ! b ≡ γᶻ ZR.* (V′ ! b) →
         (∀ x → x ≢ a → x ≢ b → V′ ! x ≡ V ! x) → actV (K-gen a b ab) (scV k V) ≡ scV k V′
K-step a b ab k V V′ ea eb eo =
  ≡.trans (actV-K a b ab k V) (≡.trans (≡.cong (scV (suc k)) K≡) (scV-γmap k V′))
  where
  a≢b = FinP.<⇒≢ ab
  γV = Vec.map (γᶻ ZR.*_) V
  K≡ : Kᶻ a b V ≡ Vec.map (γᶻ ZR.*_) V′
  K≡ = vec-ext λ x → at x (x FinP.≟ a) (x FinP.≟ b)
    where
    at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Kᶻ a b V ! x ≡ Vec.map (γᶻ ZR.*_) V′ ! x
    at x (yes ≡.refl) _ =
      ≡.trans (set₂-a a b (V ! a ZR.+ V ! b) (V ! a ZR.- V ! b) γV)
              (≡.trans ea (≡.sym (VecP.lookup-map a (γᶻ ZR.*_) V′)))
    at x (no _) (yes ≡.refl) =
      ≡.trans (set₂-b a b (V ! a ZR.+ V ! b) (V ! a ZR.- V ! b) γV a≢b)
              (≡.trans eb (≡.sym (VecP.lookup-map b (γᶻ ZR.*_) V′)))
    at x (no x≢a) (no x≢b) =
      ≡.trans (set₂-≢ a b (V ! a ZR.+ V ! b) (V ! a ZR.- V ! b) γV x≢a x≢b)
        (≡.trans (VecP.lookup-map x (γᶻ ZR.*_) V)
          (≡.trans (≡.cong (γᶻ ZR.*_) (≡.sym (eo x x≢a x≢b))) (≡.sym (VecP.lookup-map x (γᶻ ZR.*_) V′))))

i-step : (a : Fin n) (k : ℕ) (V V′ : Vec Z n) → V′ ! a ≡ ⅈᶻ ZR.* (V ! a) →
         (∀ x → x ≢ a → V′ ! x ≡ V ! x) → actV (i-gen a) (scV k V) ≡ scV k V′
i-step a k V V′ ea eo = ≡.trans (actV-i a k V) (≡.cong (scV k) (vec-ext λ x → at x (x FinP.≟ a)))
  where
  at : ∀ x → Dec (x ≡ a) → iᶻ a V ! x ≡ V′ ! x
  at x (yes ≡.refl) = ≡.trans (set₁-a a (ⅈᶻ ZR.* (V ! a)) V) (≡.sym ea)
  at x (no x≢a) = ≡.trans (set₁-≢ a (ⅈᶻ ZR.* (V ! a)) V x≢a) (≡.sym (eo x x≢a))

X-step : (a b : Fin n) (ab : a < b) (k : ℕ) (V V′ : Vec Z n) → V′ ! a ≡ V ! b → V′ ! b ≡ V ! a →
         (∀ x → x ≢ a → x ≢ b → V′ ! x ≡ V ! x) → actV (X-gen a b ab) (scV k V) ≡ scV k V′
X-step a b ab k V V′ ea eb eo =
  ≡.trans (actV-X a b ab k V) (≡.cong (scV k) (vec-ext λ x → at x (x FinP.≟ a) (x FinP.≟ b)))
  where
  a≢b = FinP.<⇒≢ ab
  at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Xᶻ a b V ! x ≡ V′ ! x
  at x (yes ≡.refl) _ = ≡.trans (set₂-a a b (V ! b) (V ! a) V) (≡.sym ea)
  at x (no _) (yes ≡.refl) = ≡.trans (set₂-b a b (V ! b) (V ! a) V a≢b) (≡.sym eb)
  at x (no x≢a) (no x≢b) = ≡.trans (set₂-≢ a b (V ! b) (V ! a) V x≢a x≢b) (≡.sym (eo x x≢a x≢b))

-- K† = K i i.
K†-step : (a b : Fin n) (ab : a < b) (k : ℕ) (V V′ : Vec Z n) →
          ⅈᶻ ZR.* (V ! a ZR.+ V ! b) ≡ γᶻ ZR.* (V′ ! a) → ⅈᶻ ZR.* (V ! a ZR.- V ! b) ≡ γᶻ ZR.* (V′ ! b) →
          (∀ x → x ≢ a → x ≢ b → V′ ! x ≡ V ! x) → actVʷ (K a b ab • i a • i b) (scV k V) ≡ scV k V′
K†-step a b ab k V V′ ea eb eo =
  ≡.trans (≡.cong (actV (K-gen a b ab)) (≡.trans (≡.cong (actV (i-gen a)) (actV-i b k V)) (actV-i a k V₁)))
          (K-step a b ab k V₂ V′ ea′ eb′ eo′)
  where
  a≢b = FinP.<⇒≢ ab
  V₁ = iᶻ b V
  V₂ = iᶻ a V₁
  V₂a : V₂ ! a ≡ ⅈᶻ ZR.* (V ! a)
  V₂a = ≡.trans (set₁-a a (ⅈᶻ ZR.* (V₁ ! a)) V₁) (≡.cong (ⅈᶻ ZR.*_) (set₁-≢ b (ⅈᶻ ZR.* (V ! b)) V a≢b))
  V₂b : V₂ ! b ≡ ⅈᶻ ZR.* (V ! b)
  V₂b = ≡.trans (set₁-≢ a (ⅈᶻ ZR.* (V₁ ! a)) V₁ (≢-sym a≢b)) (set₁-a b (ⅈᶻ ZR.* (V ! b)) V)
  ea′ : V₂ ! a ZR.+ V₂ ! b ≡ γᶻ ZR.* (V′ ! a)
  ea′ = ≡.trans (≡.cong₂ ZR._+_ V₂a V₂b) (≡.trans (≡.sym (ZR.distribˡ ⅈᶻ (V ! a) (V ! b))) ea)
  eb′ : V₂ ! a ZR.- V₂ ! b ≡ γᶻ ZR.* (V′ ! b)
  eb′ = ≡.trans (≡.cong₂ ZR._-_ V₂a V₂b)
          (≡.trans (ZG.solve 2 (λ x y → con ⅈᶻ :* x :- con ⅈᶻ :* y := con ⅈᶻ :* (x :- y)) ≡.refl (V ! a) (V ! b)) eb)
  eo′ : ∀ x → x ≢ a → x ≢ b → V′ ! x ≡ V₂ ! x
  eo′ x x≢a x≢b = ≡.trans (eo x x≢a x≢b)
                    (≡.sym (≡.trans (set₁-≢ a (ⅈᶻ ZR.* (V₁ ! a)) V₁ x≢a) (set₁-≢ b (ⅈᶻ ZR.* (V ! b)) V x≢b)))

------------------------------------------------------------------------
-- The entries of the table

γ² γ³ : Z
γ² = γᶻ ZR.* γᶻ
γ³ = γᶻ ZR.* γ²

-- 1 + a γ³, and the entries (1 + i) + i (a + b) γ² and i (a - b) γ²
-- that K† makes of two of them.
z : Z → Z
z a = ZR.1# ZR.+ γ³ ZR.* a

y₁ y₂ : Z → Z → Z
y₁ a b = γᶻ ZR.+ ⅈᶻ ZR.* ((a ZR.+ b) ZR.* γ²)
y₂ a b = ⅈᶻ ZR.* ((a ZR.- b) ZR.* γ²)

-- 2i - (a + b + c + d) γ, and the entries -(a ∓ b ± c ∓ d) γ.
u₁ u₂ u₃ u₄ : Z → Z → Z → Z → Z
u₁ a b c d = γ² ZR.- ((a ZR.+ b) ZR.+ (c ZR.+ d)) ZR.* γᶻ
u₂ a b c d = ZR.- (((a ZR.- b) ZR.+ (c ZR.- d)) ZR.* γᶻ)
u₃ a b c d = ZR.- (((a ZR.+ b) ZR.- (c ZR.+ d)) ZR.* γᶻ)
u₄ a b c d = ZR.- (((a ZR.- b) ZR.- (c ZR.- d)) ZR.* γᶻ)

private
  id-y₁ : ∀ a b → ⅈᶻ ZR.* (z a ZR.+ z b) ≡ γᶻ ZR.* y₁ a b
  id-y₁ = ZG.solve 2 (λ a b → con ⅈᶻ :* ((con ZR.1# :+ con γ³ :* a) :+ (con ZR.1# :+ con γ³ :* b))
                           := con γᶻ :* (con γᶻ :+ con ⅈᶻ :* ((a :+ b) :* con γ²))) ≡.refl

  id-y₂ : ∀ a b → ⅈᶻ ZR.* (z a ZR.- z b) ≡ γᶻ ZR.* y₂ a b
  id-y₂ = ZG.solve 2 (λ a b → con ⅈᶻ :* ((con ZR.1# :+ con γ³ :* a) :- (con ZR.1# :+ con γ³ :* b))
                           := con γᶻ :* (con ⅈᶻ :* ((a :- b) :* con γ²))) ≡.refl

  id-u₁ : ∀ a b c d → ⅈᶻ ZR.* (y₁ a b ZR.+ y₁ c d) ≡ γᶻ ZR.* u₁ a b c d
  id-u₁ = ZG.solve 4 (λ a b c d →
            con ⅈᶻ :* ((con γᶻ :+ con ⅈᶻ :* ((a :+ b) :* con γ²)) :+ (con γᶻ :+ con ⅈᶻ :* ((c :+ d) :* con γ²)))
            := con γᶻ :* (con γ² :- ((a :+ b) :+ (c :+ d)) :* con γᶻ)) ≡.refl

  id-u₃ : ∀ a b c d → ⅈᶻ ZR.* (y₁ a b ZR.- y₁ c d) ≡ γᶻ ZR.* u₃ a b c d
  id-u₃ = ZG.solve 4 (λ a b c d →
            con ⅈᶻ :* ((con γᶻ :+ con ⅈᶻ :* ((a :+ b) :* con γ²)) :- (con γᶻ :+ con ⅈᶻ :* ((c :+ d) :* con γ²)))
            := con γᶻ :* (:- (((a :+ b) :- (c :+ d)) :* con γᶻ))) ≡.refl

  id-u₂ : ∀ a b c d → ⅈᶻ ZR.* (y₂ a b ZR.+ y₂ c d) ≡ γᶻ ZR.* u₂ a b c d
  id-u₂ = ZG.solve 4 (λ a b c d →
            con ⅈᶻ :* ((con ⅈᶻ :* ((a :- b) :* con γ²)) :+ (con ⅈᶻ :* ((c :- d) :* con γ²)))
            := con γᶻ :* (:- (((a :- b) :+ (c :- d)) :* con γᶻ))) ≡.refl

  id-u₄ : ∀ a b c d → ⅈᶻ ZR.* (y₂ a b ZR.- y₂ c d) ≡ γᶻ ZR.* u₄ a b c d
  id-u₄ = ZG.solve 4 (λ a b c d →
            con ⅈᶻ :* ((con ⅈᶻ :* ((a :- b) :* con γ²)) :- (con ⅈᶻ :* ((c :- d) :* con γ²)))
            := con γᶻ :* (:- (((a :- b) :- (c :- d)) :* con γᶻ))) ≡.refl

  id-v₂ : ∀ a b c d → u₃ a b c d ZR.+ u₄ a b c d ≡ γᶻ ZR.* y₂ a c
  id-v₂ = ZG.solve 4 (λ a b c d →
            (:- (((a :+ b) :- (c :+ d)) :* con γᶻ)) :+ (:- (((a :- b) :- (c :- d)) :* con γᶻ))
            := con γᶻ :* (con ⅈᶻ :* ((a :- c) :* con γ²))) ≡.refl

  id-v₄ : ∀ a b c d → u₃ a b c d ZR.- u₄ a b c d ≡ γᶻ ZR.* y₂ b d
  id-v₄ = ZG.solve 4 (λ a b c d →
            (:- (((a :+ b) :- (c :+ d)) :* con γᶻ)) :- (:- (((a :- b) :- (c :- d)) :* con γᶻ))
            := con γᶻ :* (con ⅈᶻ :* ((b :- d) :* con γ²))) ≡.refl

  id-w₁ : ∀ a b c d → u₁ a b c d ZR.+ u₂ a b c d ≡ γᶻ ZR.* y₁ a c
  id-w₁ = ZG.solve 4 (λ a b c d →
            (con γ² :- ((a :+ b) :+ (c :+ d)) :* con γᶻ) :+ (:- (((a :- b) :+ (c :- d)) :* con γᶻ))
            := con γᶻ :* (con γᶻ :+ con ⅈᶻ :* ((a :+ c) :* con γ²))) ≡.refl

  id-w₃ : ∀ a b c d → u₁ a b c d ZR.- u₂ a b c d ≡ γᶻ ZR.* y₁ b d
  id-w₃ = ZG.solve 4 (λ a b c d →
            (con γ² :- ((a :+ b) :+ (c :+ d)) :* con γᶻ) :- (:- (((a :- b) :+ (c :- d)) :* con γᶻ))
            := con γᶻ :* (con γᶻ :+ con ⅈᶻ :* ((b :+ d) :* con γ²))) ≡.refl

  id-zb : ∀ b d → y₁ b d ZR.+ y₂ b d ≡ γᶻ ZR.* z b
  id-zb = ZG.solve 2 (λ b d →
            (con γᶻ :+ con ⅈᶻ :* ((b :+ d) :* con γ²)) :+ (con ⅈᶻ :* ((b :- d) :* con γ²))
            := con γᶻ :* (con ZR.1# :+ con γ³ :* b)) ≡.refl

  id-zd : ∀ b d → y₁ b d ZR.- y₂ b d ≡ γᶻ ZR.* z d
  id-zd = ZG.solve 2 (λ b d →
            (con γᶻ :+ con ⅈᶻ :* ((b :+ d) :* con γ²)) :- (con ⅈᶻ :* ((b :- d) :* con γ²))
            := con γᶻ :* (con ZR.1# :+ con γ³ :* d)) ≡.refl

-- The entries y₁ and u₁ are even.
even-y₁ : ∀ a b → Even (y₁ a b)
even-y₁ a b = γ∣⇒even (ZR.1# ZR.+ ⅈᶻ ZR.* ((a ZR.+ b) ZR.* γᶻ) ,
  ZG.solve 2 (λ a b → con γᶻ :+ con ⅈᶻ :* ((a :+ b) :* con γ²)
                   := con γᶻ :* (con ZR.1# :+ con ⅈᶻ :* ((a :+ b) :* con γᶻ))) ≡.refl a b)

even-u₁ : ∀ a b c d → Even (u₁ a b c d)
even-u₁ a b c d = γ∣⇒even (γᶻ ZR.- ((a ZR.+ b) ZR.+ (c ZR.+ d)) ,
  ZG.solve 4 (λ a b c d → con γ² :- ((a :+ b) :+ (c :+ d)) :* con γᶻ
                       := con γᶻ :* (con γᶻ :- ((a :+ b) :+ (c :+ d)))) ≡.refl a b c d)

------------------------------------------------------------------------
-- Numerators differing from W at j < ℓ < j′ < ℓ′

module Four {j ℓ j′ ℓ′ : Fin n} (jℓ : j < ℓ) (ℓj′ : ℓ < j′) (j′ℓ′ : j′ < ℓ′) (W : Vec Z n) where

  jj′ : j < j′
  jj′ = ℕP.<-trans jℓ ℓj′
  ℓℓ′ : ℓ < ℓ′
  ℓℓ′ = ℕP.<-trans ℓj′ j′ℓ′
  jℓ′ : j < ℓ′
  jℓ′ = ℕP.<-trans jj′ j′ℓ′

  private
    j≢ℓ = FinP.<⇒≢ jℓ
    j≢j′ = FinP.<⇒≢ jj′
    j≢ℓ′ = FinP.<⇒≢ jℓ′
    ℓ≢j′ = FinP.<⇒≢ ℓj′
    ℓ≢ℓ′ = FinP.<⇒≢ ℓℓ′
    j′≢ℓ′ = FinP.<⇒≢ j′ℓ′

  Nv : Z → Z → Z → Z → Vec Z n
  Nv x₁ x₂ x₃ x₄ = set₂ j ℓ x₁ x₂ (set₂ j′ ℓ′ x₃ x₄ W)

  Nv-j : ∀ x₁ x₂ x₃ x₄ → Nv x₁ x₂ x₃ x₄ ! j ≡ x₁
  Nv-j x₁ x₂ x₃ x₄ = set₂-a j ℓ x₁ x₂ (set₂ j′ ℓ′ x₃ x₄ W)

  Nv-ℓ : ∀ x₁ x₂ x₃ x₄ → Nv x₁ x₂ x₃ x₄ ! ℓ ≡ x₂
  Nv-ℓ x₁ x₂ x₃ x₄ = set₂-b j ℓ x₁ x₂ (set₂ j′ ℓ′ x₃ x₄ W) j≢ℓ

  Nv-j′ : ∀ x₁ x₂ x₃ x₄ → Nv x₁ x₂ x₃ x₄ ! j′ ≡ x₃
  Nv-j′ x₁ x₂ x₃ x₄ = ≡.trans (set₂-≢ j ℓ x₁ x₂ (set₂ j′ ℓ′ x₃ x₄ W) (≢-sym j≢j′) (≢-sym ℓ≢j′))
                             (set₂-a j′ ℓ′ x₃ x₄ W)

  Nv-ℓ′ : ∀ x₁ x₂ x₃ x₄ → Nv x₁ x₂ x₃ x₄ ! ℓ′ ≡ x₄
  Nv-ℓ′ x₁ x₂ x₃ x₄ = ≡.trans (set₂-≢ j ℓ x₁ x₂ (set₂ j′ ℓ′ x₃ x₄ W) (≢-sym j≢ℓ′) (≢-sym ℓ≢ℓ′))
                             (set₂-b j′ ℓ′ x₃ x₄ W j′≢ℓ′)

  Nv-o : ∀ x₁ x₂ x₃ x₄ {x} → x ≢ j → x ≢ ℓ → x ≢ j′ → x ≢ ℓ′ → Nv x₁ x₂ x₃ x₄ ! x ≡ W ! x
  Nv-o x₁ x₂ x₃ x₄ a b c d = ≡.trans (set₂-≢ j ℓ x₁ x₂ (set₂ j′ ℓ′ x₃ x₄ W) a b) (set₂-≢ j′ ℓ′ x₃ x₄ W c d)

  -- Two such numerators agree at x if their entries at x agree.
  Nv-same : ∀ {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄} x → (x ≡ j → y₁ ≡ x₁) → (x ≡ ℓ → y₂ ≡ x₂) →
            (x ≡ j′ → y₃ ≡ x₃) → (x ≡ ℓ′ → y₄ ≡ x₄) → Nv y₁ y₂ y₃ y₄ ! x ≡ Nv x₁ x₂ x₃ x₄ ! x
  Nv-same {x₁} {x₂} {x₃} {x₄} {y₁} {y₂} {y₃} {y₄} x h₁ h₂ h₃ h₄ =
    at (x FinP.≟ j) (x FinP.≟ ℓ) (x FinP.≟ j′) (x FinP.≟ ℓ′)
    where
    P : Fin n → Set
    P w = Nv y₁ y₂ y₃ y₄ ! w ≡ Nv x₁ x₂ x₃ x₄ ! w
    at : Dec (x ≡ j) → Dec (x ≡ ℓ) → Dec (x ≡ j′) → Dec (x ≡ ℓ′) → P x
    at (yes e) _ _ _ =
      ≡.subst P (≡.sym e) (≡.trans (Nv-j y₁ y₂ y₃ y₄) (≡.trans (h₁ e) (≡.sym (Nv-j x₁ x₂ x₃ x₄))))
    at (no _) (yes e) _ _ =
      ≡.subst P (≡.sym e) (≡.trans (Nv-ℓ y₁ y₂ y₃ y₄) (≡.trans (h₂ e) (≡.sym (Nv-ℓ x₁ x₂ x₃ x₄))))
    at (no _) (no _) (yes e) _ =
      ≡.subst P (≡.sym e) (≡.trans (Nv-j′ y₁ y₂ y₃ y₄) (≡.trans (h₃ e) (≡.sym (Nv-j′ x₁ x₂ x₃ x₄))))
    at (no _) (no _) (no _) (yes e) =
      ≡.subst P (≡.sym e) (≡.trans (Nv-ℓ′ y₁ y₂ y₃ y₄) (≡.trans (h₄ e) (≡.sym (Nv-ℓ′ x₁ x₂ x₃ x₄))))
    at (no a) (no b) (no c) (no d) = ≡.trans (Nv-o y₁ y₂ y₃ y₄ a b c d) (≡.sym (Nv-o x₁ x₂ x₃ x₄ a b c d))

  -- A numerator with these entries at the four indices, and W's
  -- elsewhere, is Nv.
  Nv-ext : ∀ {x₁ x₂ x₃ x₄} (U : Vec Z n) → U ! j ≡ x₁ → U ! ℓ ≡ x₂ → U ! j′ ≡ x₃ → U ! ℓ′ ≡ x₄ →
           (∀ x → x ≢ j → x ≢ ℓ → x ≢ j′ → x ≢ ℓ′ → U ! x ≡ W ! x) → U ≡ Nv x₁ x₂ x₃ x₄
  Nv-ext {x₁} {x₂} {x₃} {x₄} U e₁ e₂ e₃ e₄ eo =
    vec-ext λ x → at x (x FinP.≟ j) (x FinP.≟ ℓ) (x FinP.≟ j′) (x FinP.≟ ℓ′)
    where
    P : Fin n → Set
    P w = U ! w ≡ Nv x₁ x₂ x₃ x₄ ! w
    at : ∀ x → Dec (x ≡ j) → Dec (x ≡ ℓ) → Dec (x ≡ j′) → Dec (x ≡ ℓ′) → P x
    at x (yes e) _ _ _ = ≡.subst P (≡.sym e) (≡.trans e₁ (≡.sym (Nv-j x₁ x₂ x₃ x₄)))
    at x (no _) (yes e) _ _ = ≡.subst P (≡.sym e) (≡.trans e₂ (≡.sym (Nv-ℓ x₁ x₂ x₃ x₄)))
    at x (no _) (no _) (yes e) _ = ≡.subst P (≡.sym e) (≡.trans e₃ (≡.sym (Nv-j′ x₁ x₂ x₃ x₄)))
    at x (no _) (no _) (no _) (yes e) = ≡.subst P (≡.sym e) (≡.trans e₄ (≡.sym (Nv-ℓ′ x₁ x₂ x₃ x₄)))
    at x (no a) (no b) (no c) (no d) = ≡.trans (eo x a b c d) (≡.sym (Nv-o x₁ x₂ x₃ x₄ a b c d))

  -- With an even entry at j, fewer odd entries than W, where the four
  -- entries of W are odd.
  nodd-N : ∀ x₁ x₂ x₃ x₄ → Even x₁ → Odd (W ! j) → Odd (W ! ℓ) → Odd (W ! j′) → Odd (W ! ℓ′) →
           nodd (Nv x₁ x₂ x₃ x₄) ℕ.< nodd W
  nodd-N x₁ x₂ x₃ x₄ e₁ oj oℓ oj′ oℓ′ =
    count-lt (λ x → oddᶻ (W ! x)) (λ x → oddᶻ (Nv x₁ x₂ x₃ x₄ ! x)) j imp oj
             (≡.trans (≡.cong oddᶻ (Nv-j x₁ x₂ x₃ x₄)) e₁)
    where
    imp : ∀ x → oddᶻ (Nv x₁ x₂ x₃ x₄ ! x) ≡ true → oddᶻ (W ! x) ≡ true
    imp x h = at (x FinP.≟ j) (x FinP.≟ ℓ) (x FinP.≟ j′) (x FinP.≟ ℓ′)
      where
      P : Fin n → Set
      P w = oddᶻ (W ! w) ≡ true
      at : Dec (x ≡ j) → Dec (x ≡ ℓ) → Dec (x ≡ j′) → Dec (x ≡ ℓ′) → P x
      at (yes e) _ _ _ = ≡.subst P (≡.sym e) oj
      at (no _) (yes e) _ _ = ≡.subst P (≡.sym e) oℓ
      at (no _) (no _) (yes e) _ = ≡.subst P (≡.sym e) oj′
      at (no _) (no _) (no _) (yes e) = ≡.subst P (≡.sym e) oℓ′
      at (no a) (no b) (no c) (no d) = ≡.trans (≡.cong oddᶻ (≡.sym (Nv-o x₁ x₂ x₃ x₄ a b c d))) h

  ----------------------------------------------------------------------
  -- The states

  -- The powers of i at the four indices.
  diag : ∀ k e₁ e₂ e₃ e₄ →
         actVʷ (i j ^ e₁ • i ℓ ^ e₂ • i j′ ^ e₃ • i ℓ′ ^ e₄) (scV k W) ≡
         scV k (Nv ((ⅈᶻ ^ᶻ e₁) ZR.* (W ! j)) ((ⅈᶻ ^ᶻ e₂) ZR.* (W ! ℓ)) ((ⅈᶻ ^ᶻ e₃) ZR.* (W ! j′)) ((ⅈᶻ ^ᶻ e₄) ZR.* (W ! ℓ′)))
  diag k e₁ e₂ e₃ e₄ =
    ≡.trans (cong-act (i j ^ e₁ • i ℓ ^ e₂ • i j′ ^ e₃)
              (≡.trans (i^-action ℓ′ e₄ k W) (≡.refl {x = scV k V₄})))
      (≡.trans (cong-act (i j ^ e₁ • i ℓ ^ e₂) (i^-action j′ e₃ k V₄))
        (≡.trans (cong-act (i j ^ e₁) (i^-action ℓ e₂ k V₃))
          (≡.trans (i^-action j e₁ k V₂) (≡.cong (scV k) V₁≡))))
    where
    cong-act : (u : Word (Gen n)) {x y : Vec D n} → x ≡ y → actVʷ u x ≡ actVʷ u y
    cong-act u ≡.refl = ≡.refl
    V₄ = set₁ ℓ′ ((ⅈᶻ ^ᶻ e₄) ZR.* (W ! ℓ′)) W
    V₃ = set₁ j′ ((ⅈᶻ ^ᶻ e₃) ZR.* (V₄ ! j′)) V₄
    V₂ = set₁ ℓ ((ⅈᶻ ^ᶻ e₂) ZR.* (V₃ ! ℓ)) V₃
    V₁ = set₁ j ((ⅈᶻ ^ᶻ e₁) ZR.* (V₂ ! j)) V₂
    V₄j′ : V₄ ! j′ ≡ W ! j′
    V₄j′ = set₁-≢ ℓ′ _ W j′≢ℓ′
    V₃ℓ : V₃ ! ℓ ≡ W ! ℓ
    V₃ℓ = ≡.trans (set₁-≢ j′ _ V₄ ℓ≢j′) (set₁-≢ ℓ′ _ W ℓ≢ℓ′)
    V₂j : V₂ ! j ≡ W ! j
    V₂j = ≡.trans (set₁-≢ ℓ _ V₃ j≢ℓ) (≡.trans (set₁-≢ j′ _ V₄ j≢j′) (set₁-≢ ℓ′ _ W j≢ℓ′))
    V₁≡ : V₁ ≡ Nv ((ⅈᶻ ^ᶻ e₁) ZR.* (W ! j)) ((ⅈᶻ ^ᶻ e₂) ZR.* (W ! ℓ)) ((ⅈᶻ ^ᶻ e₃) ZR.* (W ! j′)) ((ⅈᶻ ^ᶻ e₄) ZR.* (W ! ℓ′))
    V₁≡ = Nv-ext V₁
      (≡.trans (set₁-a j _ V₂) (≡.cong ((ⅈᶻ ^ᶻ e₁) ZR.*_) V₂j))
      (≡.trans (set₁-≢ j _ V₂ (≢-sym j≢ℓ)) (≡.trans (set₁-a ℓ _ V₃) (≡.cong ((ⅈᶻ ^ᶻ e₂) ZR.*_) V₃ℓ)))
      (≡.trans (set₁-≢ j _ V₂ (≢-sym j≢j′)) (≡.trans (set₁-≢ ℓ _ V₃ (≢-sym ℓ≢j′))
        (≡.trans (set₁-a j′ _ V₄) (≡.cong ((ⅈᶻ ^ᶻ e₃) ZR.*_) V₄j′))))
      (≡.trans (set₁-≢ j _ V₂ (≢-sym j≢ℓ′)) (≡.trans (set₁-≢ ℓ _ V₃ (≢-sym ℓ≢ℓ′))
        (≡.trans (set₁-≢ j′ _ V₄ (≢-sym j′≢ℓ′)) (set₁-a ℓ′ _ W))))
      (λ x a b c d → ≡.trans (set₁-≢ j _ V₂ a) (≡.trans (set₁-≢ ℓ _ V₃ b)
                       (≡.trans (set₁-≢ j′ _ V₄ c) (set₁-≢ ℓ′ _ W d))))

  module _ (k : ℕ) (a b c d : Z) where

    -- K†_[j,ℓ] = K i i on (1 + a γ³ , 1 + b γ³ , 1 + c γ³ , 1 + d γ³).
    step₀ : actVʷ (K j ℓ jℓ • i j • i ℓ) (scV k (Nv (z a) (z b) (z c) (z d))) ≡
            scV k (Nv (y₁ a b) (y₂ a b) (z c) (z d))
    step₀ = K†-step j ℓ jℓ k _ _
      (≡.trans (≡.cong₂ (λ s t → ⅈᶻ ZR.* (s ZR.+ t)) (Nv-j _ _ _ _) (Nv-ℓ _ _ _ _))
               (≡.trans (id-y₁ a b) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-j _ _ _ _)))))
      (≡.trans (≡.cong₂ (λ s t → ⅈᶻ ZR.* (s ZR.- t)) (Nv-j _ _ _ _) (Nv-ℓ _ _ _ _))
               (≡.trans (id-y₂ a b) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-ℓ _ _ _ _)))))
      (λ x x≢j x≢ℓ → Nv-same x (λ e → ⊥ (x≢j e)) (λ e → ⊥ (x≢ℓ e)) (λ _ → ≡.refl) (λ _ → ≡.refl))
      where
      open import Data.Empty using () renaming (⊥-elim to ⊥)

    private
      U₁ = u₁ a b c d
      U₂ = u₂ a b c d
      U₃ = u₃ a b c d
      U₄ = u₄ a b c d
      ⊥e : ∀ {A : Set} {x y : Fin n} → x ≢ y → x ≡ y → A
      ⊥e ne e = ⊥ (ne e)
        where open import Data.Empty using () renaming (⊥-elim to ⊥)
      rfl : ∀ {A : Set} {x : A} {B : Set} → B → x ≡ x
      rfl _ = ≡.refl

    -- K†_[j′,ℓ′] = K i i.
    step₁ : actVʷ (K j′ ℓ′ j′ℓ′ • i j′ • i ℓ′) (scV k (Nv (y₁ a b) (y₂ a b) (z c) (z d))) ≡
            scV k (Nv (y₁ a b) (y₂ a b) (y₁ c d) (y₂ c d))
    step₁ = K†-step j′ ℓ′ j′ℓ′ k _ _
      (≡.trans (≡.cong₂ (λ s t → ⅈᶻ ZR.* (s ZR.+ t)) (Nv-j′ _ _ _ _) (Nv-ℓ′ _ _ _ _))
               (≡.trans (id-y₁ c d) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-j′ _ _ _ _)))))
      (≡.trans (≡.cong₂ (λ s t → ⅈᶻ ZR.* (s ZR.- t)) (Nv-j′ _ _ _ _) (Nv-ℓ′ _ _ _ _))
               (≡.trans (id-y₂ c d) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-ℓ′ _ _ _ _)))))
      (λ x a′ b′ → Nv-same x rfl rfl (⊥e a′) (⊥e b′))

    -- K†_[j,j′] = K i i.
    step₂ : actVʷ (K j j′ jj′ • i j • i j′) (scV k (Nv (y₁ a b) (y₂ a b) (y₁ c d) (y₂ c d))) ≡
            scV k (Nv U₁ (y₂ a b) U₃ (y₂ c d))
    step₂ = K†-step j j′ jj′ k _ _
      (≡.trans (≡.cong₂ (λ s t → ⅈᶻ ZR.* (s ZR.+ t)) (Nv-j _ _ _ _) (Nv-j′ _ _ _ _))
               (≡.trans (id-u₁ a b c d) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-j _ _ _ _)))))
      (≡.trans (≡.cong₂ (λ s t → ⅈᶻ ZR.* (s ZR.- t)) (Nv-j _ _ _ _) (Nv-j′ _ _ _ _))
               (≡.trans (id-u₃ a b c d) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-j′ _ _ _ _)))))
      (λ x a′ b′ → Nv-same x (⊥e a′) rfl (⊥e b′) rfl)

    -- K†_[ℓ,ℓ′] = K i i.
    step₃ : actVʷ (K ℓ ℓ′ ℓℓ′ • i ℓ • i ℓ′) (scV k (Nv U₁ (y₂ a b) U₃ (y₂ c d))) ≡ scV k (Nv U₁ U₂ U₃ U₄)
    step₃ = K†-step ℓ ℓ′ ℓℓ′ k _ _
      (≡.trans (≡.cong₂ (λ s t → ⅈᶻ ZR.* (s ZR.+ t)) (Nv-ℓ _ _ _ _) (Nv-ℓ′ _ _ _ _))
               (≡.trans (id-u₂ a b c d) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-ℓ _ _ _ _)))))
      (≡.trans (≡.cong₂ (λ s t → ⅈᶻ ZR.* (s ZR.- t)) (Nv-ℓ _ _ _ _) (Nv-ℓ′ _ _ _ _))
               (≡.trans (id-u₄ a b c d) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-ℓ′ _ _ _ _)))))
      (λ x a′ b′ → Nv-same x rfl (⊥e a′) rfl (⊥e b′))

    -- X_[ℓ,j′].
    step₄ : actV (X-gen ℓ j′ ℓj′) (scV k (Nv U₁ U₂ U₃ U₄)) ≡ scV k (Nv U₁ U₃ U₂ U₄)
    step₄ = X-step ℓ j′ ℓj′ k _ _
      (≡.trans (Nv-ℓ _ _ _ _) (≡.sym (Nv-j′ _ _ _ _)))
      (≡.trans (Nv-j′ _ _ _ _) (≡.sym (Nv-ℓ _ _ _ _)))
      (λ x a′ b′ → Nv-same x rfl (⊥e a′) (⊥e b′) rfl)

    -- K_[ℓ,ℓ′].
    step₅ : actV (K-gen ℓ ℓ′ ℓℓ′) (scV k (Nv U₁ U₃ U₂ U₄)) ≡ scV k (Nv U₁ (y₂ a c) U₂ (y₂ b d))
    step₅ = K-step ℓ ℓ′ ℓℓ′ k _ _
      (≡.trans (≡.cong₂ ZR._+_ (Nv-ℓ _ _ _ _) (Nv-ℓ′ _ _ _ _))
               (≡.trans (id-v₂ a b c d) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-ℓ _ _ _ _)))))
      (≡.trans (≡.cong₂ ZR._-_ (Nv-ℓ _ _ _ _) (Nv-ℓ′ _ _ _ _))
               (≡.trans (id-v₄ a b c d) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-ℓ′ _ _ _ _)))))
      (λ x a′ b′ → Nv-same x rfl (⊥e a′) rfl (⊥e b′))

    -- K_[j,j′].
    step₆ : actV (K-gen j j′ jj′) (scV k (Nv U₁ (y₂ a c) U₂ (y₂ b d))) ≡
            scV k (Nv (y₁ a c) (y₂ a c) (y₁ b d) (y₂ b d))
    step₆ = K-step j j′ jj′ k _ _
      (≡.trans (≡.cong₂ ZR._+_ (Nv-j _ _ _ _) (Nv-j′ _ _ _ _))
               (≡.trans (id-w₁ a b c d) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-j _ _ _ _)))))
      (≡.trans (≡.cong₂ ZR._-_ (Nv-j _ _ _ _) (Nv-j′ _ _ _ _))
               (≡.trans (id-w₃ a b c d) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-j′ _ _ _ _)))))
      (λ x a′ b′ → Nv-same x (⊥e a′) rfl (⊥e b′) rfl)

    -- K_[j′,ℓ′].
    step₇ : actV (K-gen j′ ℓ′ j′ℓ′) (scV k (Nv (y₁ a c) (y₂ a c) (y₁ b d) (y₂ b d))) ≡
            scV k (Nv (y₁ a c) (y₂ a c) (z b) (z d))
    step₇ = K-step j′ ℓ′ j′ℓ′ k _ _
      (≡.trans (≡.cong₂ ZR._+_ (Nv-j′ _ _ _ _) (Nv-ℓ′ _ _ _ _))
               (≡.trans (id-zb b d) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-j′ _ _ _ _)))))
      (≡.trans (≡.cong₂ ZR._-_ (Nv-j′ _ _ _ _) (Nv-ℓ′ _ _ _ _))
               (≡.trans (id-zd b d) (≡.cong (γᶻ ZR.*_) (≡.sym (Nv-ℓ′ _ _ _ _)))))
      (λ x a′ b′ → Nv-same x rfl rfl (⊥e a′) (⊥e b′))
