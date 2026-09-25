------------------------------------------------------------------------
-- Presentations of groups
--
-- Four odd entries, for the hard subcase of Cases 3–5.
--
-- The generators on numerators at a fixed scale: X, powers of ω, and H
-- when δ² divides the new entries.  Then, for j < α < β < ℓ′ and
-- numerators that differ from a fixed W only at these four indices,
-- the states along the two paths of the thesis from
-- (1 + a δ³ , 1 + b δ³ , 1 + c δ³ , 1 + d δ³): the first when
-- a + b + c + d = δ² A, the second when a + b + c + d = δ + δ² A.  In
-- each of them the entry j is even.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.FourOdd {n : ℕ} where

open import Data.Bool.Base using (true)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Integer.Base using (+_ ; -[1+_])
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_ ; ≢-sym)
open import Relation.Nullary using (Dec ; yes ; no)

open import Quantum.Synthesis.Ring using (Omega)

open import Word.Base
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Scale using (λωᶻ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Residue using (δ²ᶻ ; δ³ᶻ ; g1 ; g2 ; g3)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count-lt)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Column using (nodd)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics hiding (_!_ ; U)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syllable using (ω^-action)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Step using (scV-δ²map)

private
  open ZG using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

------------------------------------------------------------------------
-- The generators on numerators

H-step : (a b : Fin n) (ab : a < b) (k : ℕ) (V V′ : Vec Z n) →
         λωᶻ ZR.* (V ! a ZR.+ V ! b) ≡ δ²ᶻ ZR.* (V′ ! a) → λωᶻ ZR.* (V ! a ZR.- V ! b) ≡ δ²ᶻ ZR.* (V′ ! b) →
         (∀ x → x ≢ a → x ≢ b → V′ ! x ≡ V ! x) → actV (H-gen a b ab) (scV k V) ≡ scV k V′
H-step a b ab k V V′ ea eb eo =
  ≡.trans (actV-H a b ab k V) (≡.trans (≡.cong (scV (suc (suc k))) H≡) (scV-δ²map k V′))
  where
  a≢b = FinP.<⇒≢ ab
  u₊ = λωᶻ ZR.* (V ! a ZR.+ V ! b)
  u₋ = λωᶻ ZR.* (V ! a ZR.- V ! b)
  δV = Vec.map (δ²ᶻ ZR.*_) V
  H≡ : Hᶻ a b V ≡ Vec.map (δ²ᶻ ZR.*_) V′
  H≡ = vec-ext λ x → at x (x FinP.≟ a) (x FinP.≟ b)
    where
    at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Hᶻ a b V ! x ≡ Vec.map (δ²ᶻ ZR.*_) V′ ! x
    at x (yes ≡.refl) _ =
      ≡.trans (set₂-a a b u₊ u₋ δV) (≡.trans ea (≡.sym (VecP.lookup-map a (δ²ᶻ ZR.*_) V′)))
    at x (no _) (yes ≡.refl) =
      ≡.trans (set₂-b a b u₊ u₋ δV a≢b) (≡.trans eb (≡.sym (VecP.lookup-map b (δ²ᶻ ZR.*_) V′)))
    at x (no x≢a) (no x≢b) =
      ≡.trans (set₂-≢ a b u₊ u₋ δV x≢a x≢b)
        (≡.trans (VecP.lookup-map x (δ²ᶻ ZR.*_) V)
          (≡.trans (≡.cong (δ²ᶻ ZR.*_) (≡.sym (eo x x≢a x≢b))) (≡.sym (VecP.lookup-map x (δ²ᶻ ZR.*_) V′))))

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

-- H through given entries.
H-pair : ∀ {a b : Fin n} (ab : a < b) (k : ℕ) {V V′ : Vec Z n} {va vb va′ vb′ : Z} →
         V ! a ≡ va → V ! b ≡ vb → V′ ! a ≡ va′ → V′ ! b ≡ vb′ →
         λωᶻ ZR.* (va ZR.+ vb) ≡ δ²ᶻ ZR.* va′ → λωᶻ ZR.* (va ZR.- vb) ≡ δ²ᶻ ZR.* vb′ →
         (∀ x → x ≢ a → x ≢ b → V′ ! x ≡ V ! x) → actV (H-gen a b ab) (scV k V) ≡ scV k V′
H-pair {a} {b} ab k {V} {V′} ea eb ea′ eb′ e₊ e₋ eo = H-step a b ab k V V′
  (≡.trans (≡.cong₂ (λ s t → λωᶻ ZR.* (s ZR.+ t)) ea eb) (≡.trans e₊ (≡.cong (δ²ᶻ ZR.*_) (≡.sym ea′))))
  (≡.trans (≡.cong₂ (λ s t → λωᶻ ZR.* (s ZR.- t)) ea eb) (≡.trans e₋ (≡.cong (δ²ᶻ ZR.*_) (≡.sym eb′))))
  eo

------------------------------------------------------------------------
-- The entries of the states

-- (λω)², and κ = (1 - (λω)²) / δ.
L2 κ : Z
L2 = λωᶻ ZR.* λωᶻ
κ = Omega -[1+ 0 ] -[1+ 0 ] -[1+ 1 ] (+ 0)

-- 1 + a δ³, and the entries δ λω (g₃ + a + b) and δ λω (a - b) that H
-- makes of two of them.
zz : Z → Z
zz a = ZR.1# ZR.+ δ³ᶻ ZR.* a

y₁ y₂ : Z → Z → Z
y₁ a b = δᶻ ZR.* (λωᶻ ZR.* (g3 ZR.+ (a ZR.+ b)))
y₂ a b = δᶻ ZR.* (λωᶻ ZR.* (a ZR.- b))

-- The fourth exponent: a + b + c + d = δ² A, or δ + δ² A.
dd₀ dd₁ : Z → Z → Z → Z → Z
dd₀ a b c A = δ²ᶻ ZR.* A ZR.- (a ZR.+ b ZR.+ c)
dd₁ a b c A = δᶻ ZR.+ δ²ᶻ ZR.* A ZR.- (a ZR.+ b ZR.+ c)

-- The inner entries of the first path.
s₂j : Z → Z
s₂j A = δᶻ ZR.* (g1 ZR.+ L2 ZR.* A)

sβ sℓ : Z → Z → Z → Z
sβ a b A = L2 ZR.* (g1 ZR.* (a ZR.+ b) ZR.- δᶻ ZR.* A)
sℓ b c A = L2 ZR.* (δᶻ ZR.* A ZR.- g1 ZR.* (b ZR.+ c))

-- The inner entries of the second path.
tα t₂β : Z → Z → Z
tα b A = ZR.1# ZR.+ L2 ZR.* (ZR.1# ZR.+ δᶻ ZR.* A ZR.- g1 ZR.* b)
t₂β a A = L2 ZR.* (g1 ZR.* a ZR.- ZR.1# ZR.- δᶻ ZR.* A) ZR.- ZR.1#

t₃j : Z → Z → Z → Z → Z
t₃j a b c A = δᶻ ZR.* (κ ZR.+ L2 ZR.* (g2 ZR.* (a ZR.+ b ZR.+ c) ZR.- A))

-- Multiples of δ are even.
even-δ : ∀ x → Even (δᶻ ZR.* x)
even-δ x = oddᶻ-* δᶻ x

------------------------------------------------------------------------
-- The identities of the steps: λω (x ± y) = δ² z

private
  L = λωᶻ

-- The first and last steps.
h0₊ : ∀ a b → L ZR.* (zz a ZR.+ zz b) ≡ δ²ᶻ ZR.* y₁ a b
h0₊ = ZG.solve 2 (λ a b → con L :* ((con ZR.1# :+ con δ³ᶻ :* a) :+ (con ZR.1# :+ con δ³ᶻ :* b))
                        := con δ²ᶻ :* (con δᶻ :* (con L :* (con g3 :+ (a :+ b))))) ≡.refl

h0₋ : ∀ a b → L ZR.* (zz a ZR.- zz b) ≡ δ²ᶻ ZR.* y₂ a b
h0₋ = ZG.solve 2 (λ a b → con L :* ((con ZR.1# :+ con δ³ᶻ :* a) :- (con ZR.1# :+ con δ³ᶻ :* b))
                        := con δ²ᶻ :* (con δᶻ :* (con L :* (a :- b)))) ≡.refl

h7₊ : ∀ a b → L ZR.* (y₁ a b ZR.+ y₂ a b) ≡ δ²ᶻ ZR.* zz a
h7₊ = ZG.solve 2 (λ a b → con L :* (con δᶻ :* (con L :* (con g3 :+ (a :+ b))) :+ con δᶻ :* (con L :* (a :- b)))
                        := con δ²ᶻ :* (con ZR.1# :+ con δ³ᶻ :* a)) ≡.refl

h7₋ : ∀ a b → L ZR.* (y₁ a b ZR.- y₂ a b) ≡ δ²ᶻ ZR.* zz b
h7₋ = ZG.solve 2 (λ a b → con L :* (con δᶻ :* (con L :* (con g3 :+ (a :+ b))) :- con δᶻ :* (con L :* (a :- b)))
                        := con δ²ᶻ :* (con ZR.1# :+ con δ³ᶻ :* b)) ≡.refl

-- The first path, with d = δ² A - (a + b + c).
h2₊ : ∀ a b c A → L ZR.* (y₁ a b ZR.+ y₁ c (dd₀ a b c A)) ≡ δ²ᶻ ZR.* s₂j A
h2₊ = ZG.solve 4 (λ a b c A →
        con L :* (con δᶻ :* (con L :* (con g3 :+ (a :+ b)))
                  :+ con δᶻ :* (con L :* (con g3 :+ (c :+ (con δ²ᶻ :* A :- (a :+ b :+ c))))))
        := con δ²ᶻ :* (con δᶻ :* (con g1 :+ con L2 :* A))) ≡.refl

h2₋ : ∀ a b c A → L ZR.* (y₁ a b ZR.- y₁ c (dd₀ a b c A)) ≡ δ²ᶻ ZR.* sβ a b A
h2₋ = ZG.solve 4 (λ a b c A →
        con L :* (con δᶻ :* (con L :* (con g3 :+ (a :+ b)))
                  :- con δᶻ :* (con L :* (con g3 :+ (c :+ (con δ²ᶻ :* A :- (a :+ b :+ c))))))
        := con δ²ᶻ :* (con L2 :* (con g1 :* (a :+ b) :- con δᶻ :* A))) ≡.refl

h3₊ : ∀ a b c A → L ZR.* (y₂ a b ZR.+ y₂ c (dd₀ a b c A)) ≡ δ²ᶻ ZR.* sβ a c A
h3₊ = ZG.solve 4 (λ a b c A →
        con L :* (con δᶻ :* (con L :* (a :- b)) :+ con δᶻ :* (con L :* (c :- (con δ²ᶻ :* A :- (a :+ b :+ c)))))
        := con δ²ᶻ :* (con L2 :* (con g1 :* (a :+ c) :- con δᶻ :* A))) ≡.refl

h3₋ : ∀ a b c A → L ZR.* (y₂ a b ZR.- y₂ c (dd₀ a b c A)) ≡ δ²ᶻ ZR.* sℓ b c A
h3₋ = ZG.solve 4 (λ a b c A →
        con L :* (con δᶻ :* (con L :* (a :- b)) :- con δᶻ :* (con L :* (c :- (con δ²ᶻ :* A :- (a :+ b :+ c)))))
        := con δ²ᶻ :* (con L2 :* (con δᶻ :* A :- con g1 :* (b :+ c)))) ≡.refl

h5₊ : ∀ a b c A → L ZR.* (sβ a b A ZR.+ sℓ b c A) ≡ δ²ᶻ ZR.* y₂ a c
h5₊ = ZG.solve 4 (λ a b c A →
        con L :* (con L2 :* (con g1 :* (a :+ b) :- con δᶻ :* A) :+ con L2 :* (con δᶻ :* A :- con g1 :* (b :+ c)))
        := con δ²ᶻ :* (con δᶻ :* (con L :* (a :- c)))) ≡.refl

h5₋ : ∀ a b c A → L ZR.* (sβ a b A ZR.- sℓ b c A) ≡ δ²ᶻ ZR.* y₂ b (dd₀ a b c A)
h5₋ = ZG.solve 4 (λ a b c A →
        con L :* (con L2 :* (con g1 :* (a :+ b) :- con δᶻ :* A) :- con L2 :* (con δᶻ :* A :- con g1 :* (b :+ c)))
        := con δ²ᶻ :* (con δᶻ :* (con L :* (b :- (con δ²ᶻ :* A :- (a :+ b :+ c)))))) ≡.refl

h6₊ : ∀ a c A → L ZR.* (s₂j A ZR.+ sβ a c A) ≡ δ²ᶻ ZR.* y₁ a c
h6₊ = ZG.solve 3 (λ a c A →
        con L :* (con δᶻ :* (con g1 :+ con L2 :* A) :+ con L2 :* (con g1 :* (a :+ c) :- con δᶻ :* A))
        := con δ²ᶻ :* (con δᶻ :* (con L :* (con g3 :+ (a :+ c))))) ≡.refl

h6₋ : ∀ a b c A → L ZR.* (s₂j A ZR.- sβ a c A) ≡ δ²ᶻ ZR.* y₁ b (dd₀ a b c A)
h6₋ = ZG.solve 4 (λ a b c A →
        con L :* (con δᶻ :* (con g1 :+ con L2 :* A) :- con L2 :* (con g1 :* (a :+ c) :- con δᶻ :* A))
        := con δ²ᶻ :* (con δᶻ :* (con L :* (con g3 :+ (b :+ (con δ²ᶻ :* A :- (a :+ b :+ c))))))) ≡.refl

-- The second path, with d = δ + δ² A - (a + b + c).
k2₊ : ∀ a b c A → L ZR.* (y₂ a b ZR.+ y₁ c (dd₁ a b c A)) ≡ δ²ᶻ ZR.* tα b A
k2₊ = ZG.solve 4 (λ a b c A →
        con L :* (con δᶻ :* (con L :* (a :- b))
                  :+ con δᶻ :* (con L :* (con g3 :+ (c :+ (con δᶻ :+ con δ²ᶻ :* A :- (a :+ b :+ c))))))
        := con δ²ᶻ :* (con ZR.1# :+ con L2 :* (con ZR.1# :+ con δᶻ :* A :- con g1 :* b))) ≡.refl

k2₋ : ∀ a b c A → L ZR.* (y₂ a b ZR.- y₁ c (dd₁ a b c A)) ≡ δ²ᶻ ZR.* t₂β a A
k2₋ = ZG.solve 4 (λ a b c A →
        con L :* (con δᶻ :* (con L :* (a :- b))
                  :- con δᶻ :* (con L :* (con g3 :+ (c :+ (con δᶻ :+ con δ²ᶻ :* A :- (a :+ b :+ c))))))
        := con δ²ᶻ :* (con L2 :* (con g1 :* a :- con ZR.1# :- con δᶻ :* A) :- con ZR.1#)) ≡.refl

k3₊ : ∀ a b c A → L ZR.* (y₁ a b ZR.+ y₂ c (dd₁ a b c A)) ≡ δ²ᶻ ZR.* t₃j a b c A
k3₊ = ZG.solve 4 (λ a b c A →
        con L :* (con δᶻ :* (con L :* (con g3 :+ (a :+ b)))
                  :+ con δᶻ :* (con L :* (c :- (con δᶻ :+ con δ²ᶻ :* A :- (a :+ b :+ c)))))
        := con δ²ᶻ :* (con δᶻ :* (con κ :+ con L2 :* (con g2 :* (a :+ b :+ c) :- A)))) ≡.refl

k3₋ : ∀ a b c A → L ZR.* (y₁ a b ZR.- y₂ c (dd₁ a b c A)) ≡ δ²ᶻ ZR.* tα c A
k3₋ = ZG.solve 4 (λ a b c A →
        con L :* (con δᶻ :* (con L :* (con g3 :+ (a :+ b)))
                  :- con δᶻ :* (con L :* (c :- (con δᶻ :+ con δ²ᶻ :* A :- (a :+ b :+ c)))))
        := con δ²ᶻ :* (con ZR.1# :+ con L2 :* (con ZR.1# :+ con δᶻ :* A :- con g1 :* c))) ≡.refl

k5₊ : ∀ a b c A → L ZR.* (t₃j a b c A ZR.+ tα b A) ≡ δ²ᶻ ZR.* y₁ a c
k5₊ = ZG.solve 4 (λ a b c A →
        con L :* (con δᶻ :* (con κ :+ con L2 :* (con g2 :* (a :+ b :+ c) :- A))
                  :+ (con ZR.1# :+ con L2 :* (con ZR.1# :+ con δᶻ :* A :- con g1 :* b)))
        := con δ²ᶻ :* (con δᶻ :* (con L :* (con g3 :+ (a :+ c))))) ≡.refl

k5₋ : ∀ a b c A → L ZR.* (t₃j a b c A ZR.- tα b A) ≡ δ²ᶻ ZR.* y₂ b (dd₁ a b c A)
k5₋ = ZG.solve 4 (λ a b c A →
        con L :* (con δᶻ :* (con κ :+ con L2 :* (con g2 :* (a :+ b :+ c) :- A))
                  :- (con ZR.1# :+ con L2 :* (con ZR.1# :+ con δᶻ :* A :- con g1 :* b)))
        := con δ²ᶻ :* (con δᶻ :* (con L :* (b :- (con δᶻ :+ con δ²ᶻ :* A :- (a :+ b :+ c)))))) ≡.refl

k6₊ : ∀ a c A → L ZR.* (tα c A ZR.+ t₂β a A) ≡ δ²ᶻ ZR.* y₂ a c
k6₊ = ZG.solve 3 (λ a c A →
        con L :* ((con ZR.1# :+ con L2 :* (con ZR.1# :+ con δᶻ :* A :- con g1 :* c))
                  :+ (con L2 :* (con g1 :* a :- con ZR.1# :- con δᶻ :* A) :- con ZR.1#))
        := con δ²ᶻ :* (con δᶻ :* (con L :* (a :- c)))) ≡.refl

k6₋ : ∀ a b c A → L ZR.* (tα c A ZR.- t₂β a A) ≡ δ²ᶻ ZR.* y₁ b (dd₁ a b c A)
k6₋ = ZG.solve 4 (λ a b c A →
        con L :* ((con ZR.1# :+ con L2 :* (con ZR.1# :+ con δᶻ :* A :- con g1 :* c))
                  :- (con L2 :* (con g1 :* a :- con ZR.1# :- con δᶻ :* A) :- con ZR.1#))
        := con δ²ᶻ :* (con δᶻ :* (con L :* (con g3 :+ (b :+ (con δᶻ :+ con δ²ᶻ :* A :- (a :+ b :+ c))))))) ≡.refl

------------------------------------------------------------------------
-- Numerators differing from W at j < α < β < ℓ′

module Four {j α β ℓ′ : Fin n} (jα : j < α) (αβ : α < β) (βℓ′ : β < ℓ′) (W : Vec Z n) where

  jβ : j < β
  jβ = FinP.<-trans jα αβ
  αℓ′ : α < ℓ′
  αℓ′ = FinP.<-trans αβ βℓ′
  jℓ′ : j < ℓ′
  jℓ′ = FinP.<-trans jβ βℓ′

  private
    j≢α = FinP.<⇒≢ jα
    j≢β = FinP.<⇒≢ jβ
    j≢ℓ′ = FinP.<⇒≢ jℓ′
    α≢β = FinP.<⇒≢ αβ
    α≢ℓ′ = FinP.<⇒≢ αℓ′
    β≢ℓ′ = FinP.<⇒≢ βℓ′

  Nv : Z → Z → Z → Z → Vec Z n
  Nv x₁ x₂ x₃ x₄ = set₂ j α x₁ x₂ (set₂ β ℓ′ x₃ x₄ W)

  Nv-j : ∀ x₁ x₂ x₃ x₄ → Nv x₁ x₂ x₃ x₄ ! j ≡ x₁
  Nv-j x₁ x₂ x₃ x₄ = set₂-a j α x₁ x₂ (set₂ β ℓ′ x₃ x₄ W)

  Nv-α : ∀ x₁ x₂ x₃ x₄ → Nv x₁ x₂ x₃ x₄ ! α ≡ x₂
  Nv-α x₁ x₂ x₃ x₄ = set₂-b j α x₁ x₂ (set₂ β ℓ′ x₃ x₄ W) j≢α

  Nv-β : ∀ x₁ x₂ x₃ x₄ → Nv x₁ x₂ x₃ x₄ ! β ≡ x₃
  Nv-β x₁ x₂ x₃ x₄ = ≡.trans (set₂-≢ j α x₁ x₂ (set₂ β ℓ′ x₃ x₄ W) (≢-sym j≢β) (≢-sym α≢β))
                            (set₂-a β ℓ′ x₃ x₄ W)

  Nv-ℓ′ : ∀ x₁ x₂ x₃ x₄ → Nv x₁ x₂ x₃ x₄ ! ℓ′ ≡ x₄
  Nv-ℓ′ x₁ x₂ x₃ x₄ = ≡.trans (set₂-≢ j α x₁ x₂ (set₂ β ℓ′ x₃ x₄ W) (≢-sym j≢ℓ′) (≢-sym α≢ℓ′))
                             (set₂-b β ℓ′ x₃ x₄ W β≢ℓ′)

  Nv-o : ∀ x₁ x₂ x₃ x₄ {x} → x ≢ j → x ≢ α → x ≢ β → x ≢ ℓ′ → Nv x₁ x₂ x₃ x₄ ! x ≡ W ! x
  Nv-o x₁ x₂ x₃ x₄ a b c d = ≡.trans (set₂-≢ j α x₁ x₂ (set₂ β ℓ′ x₃ x₄ W) a b) (set₂-≢ β ℓ′ x₃ x₄ W c d)

  -- Two such numerators agree at x if their entries at x agree.
  Nv-same : ∀ {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄} x → (x ≡ j → y₁ ≡ x₁) → (x ≡ α → y₂ ≡ x₂) →
            (x ≡ β → y₃ ≡ x₃) → (x ≡ ℓ′ → y₄ ≡ x₄) → Nv y₁ y₂ y₃ y₄ ! x ≡ Nv x₁ x₂ x₃ x₄ ! x
  Nv-same {x₁} {x₂} {x₃} {x₄} {y₁} {y₂} {y₃} {y₄} x h₁ h₂ h₃ h₄ =
    at (x FinP.≟ j) (x FinP.≟ α) (x FinP.≟ β) (x FinP.≟ ℓ′)
    where
    P : Fin n → Set
    P w = Nv y₁ y₂ y₃ y₄ ! w ≡ Nv x₁ x₂ x₃ x₄ ! w
    at : Dec (x ≡ j) → Dec (x ≡ α) → Dec (x ≡ β) → Dec (x ≡ ℓ′) → P x
    at (yes e) _ _ _ =
      ≡.subst P (≡.sym e) (≡.trans (Nv-j y₁ y₂ y₃ y₄) (≡.trans (h₁ e) (≡.sym (Nv-j x₁ x₂ x₃ x₄))))
    at (no _) (yes e) _ _ =
      ≡.subst P (≡.sym e) (≡.trans (Nv-α y₁ y₂ y₃ y₄) (≡.trans (h₂ e) (≡.sym (Nv-α x₁ x₂ x₃ x₄))))
    at (no _) (no _) (yes e) _ =
      ≡.subst P (≡.sym e) (≡.trans (Nv-β y₁ y₂ y₃ y₄) (≡.trans (h₃ e) (≡.sym (Nv-β x₁ x₂ x₃ x₄))))
    at (no _) (no _) (no _) (yes e) =
      ≡.subst P (≡.sym e) (≡.trans (Nv-ℓ′ y₁ y₂ y₃ y₄) (≡.trans (h₄ e) (≡.sym (Nv-ℓ′ x₁ x₂ x₃ x₄))))
    at (no a) (no b) (no c) (no d) = ≡.trans (Nv-o y₁ y₂ y₃ y₄ a b c d) (≡.sym (Nv-o x₁ x₂ x₃ x₄ a b c d))

  -- A numerator with these entries at the four indices, and those of
  -- W elsewhere, is Nv.
  Nv-ext : ∀ {x₁ x₂ x₃ x₄} (U : Vec Z n) → U ! j ≡ x₁ → U ! α ≡ x₂ → U ! β ≡ x₃ → U ! ℓ′ ≡ x₄ →
           (∀ x → x ≢ j → x ≢ α → x ≢ β → x ≢ ℓ′ → U ! x ≡ W ! x) → U ≡ Nv x₁ x₂ x₃ x₄
  Nv-ext {x₁} {x₂} {x₃} {x₄} U e₁ e₂ e₃ e₄ eo =
    vec-ext λ x → at x (x FinP.≟ j) (x FinP.≟ α) (x FinP.≟ β) (x FinP.≟ ℓ′)
    where
    P : Fin n → Set
    P w = U ! w ≡ Nv x₁ x₂ x₃ x₄ ! w
    at : ∀ x → Dec (x ≡ j) → Dec (x ≡ α) → Dec (x ≡ β) → Dec (x ≡ ℓ′) → P x
    at x (yes e) _ _ _ = ≡.subst P (≡.sym e) (≡.trans e₁ (≡.sym (Nv-j x₁ x₂ x₃ x₄)))
    at x (no _) (yes e) _ _ = ≡.subst P (≡.sym e) (≡.trans e₂ (≡.sym (Nv-α x₁ x₂ x₃ x₄)))
    at x (no _) (no _) (yes e) _ = ≡.subst P (≡.sym e) (≡.trans e₃ (≡.sym (Nv-β x₁ x₂ x₃ x₄)))
    at x (no _) (no _) (no _) (yes e) = ≡.subst P (≡.sym e) (≡.trans e₄ (≡.sym (Nv-ℓ′ x₁ x₂ x₃ x₄)))
    at x (no a) (no b) (no c) (no d) = ≡.trans (eo x a b c d) (≡.sym (Nv-o x₁ x₂ x₃ x₄ a b c d))

  -- With an even entry at j, fewer odd entries than W, where the four
  -- entries of W are odd.
  nodd-N : ∀ x₁ x₂ x₃ x₄ → Even x₁ → Odd (W ! j) → Odd (W ! α) → Odd (W ! β) → Odd (W ! ℓ′) →
           nodd (Nv x₁ x₂ x₃ x₄) ℕ.< nodd W
  nodd-N x₁ x₂ x₃ x₄ e₁ oj oα oβ oℓ′ =
    count-lt (λ x → oddᶻ (W ! x)) (λ x → oddᶻ (Nv x₁ x₂ x₃ x₄ ! x)) j imp oj
             (≡.trans (≡.cong oddᶻ (Nv-j x₁ x₂ x₃ x₄)) e₁)
    where
    imp : ∀ x → oddᶻ (Nv x₁ x₂ x₃ x₄ ! x) ≡ true → oddᶻ (W ! x) ≡ true
    imp x h = at (x FinP.≟ j) (x FinP.≟ α) (x FinP.≟ β) (x FinP.≟ ℓ′)
      where
      P : Fin n → Set
      P w = oddᶻ (W ! w) ≡ true
      at : Dec (x ≡ j) → Dec (x ≡ α) → Dec (x ≡ β) → Dec (x ≡ ℓ′) → P x
      at (yes e) _ _ _ = ≡.subst P (≡.sym e) oj
      at (no _) (yes e) _ _ = ≡.subst P (≡.sym e) oα
      at (no _) (no _) (yes e) _ = ≡.subst P (≡.sym e) oβ
      at (no _) (no _) (no _) (yes e) = ≡.subst P (≡.sym e) oℓ′
      at (no a) (no b) (no c) (no d) = ≡.trans (≡.cong oddᶻ (≡.sym (Nv-o x₁ x₂ x₃ x₄ a b c d))) h

  ----------------------------------------------------------------------
  -- The states

  -- The powers of ω at the four indices.
  diag : ∀ k e₁ e₂ e₃ e₄ →
         actVʷ (ω j ^ e₁ • ω α ^ e₂ • ω β ^ e₃ • ω ℓ′ ^ e₄) (scV k W) ≡
         scV k (Nv ((ωᶻ ^ᶻ e₁) ZR.* (W ! j)) ((ωᶻ ^ᶻ e₂) ZR.* (W ! α)) ((ωᶻ ^ᶻ e₃) ZR.* (W ! β)) ((ωᶻ ^ᶻ e₄) ZR.* (W ! ℓ′)))
  diag k e₁ e₂ e₃ e₄ =
    ≡.trans (cong-act (ω j ^ e₁ • ω α ^ e₂ • ω β ^ e₃)
              (≡.trans (ω^-action ℓ′ e₄ k W) (≡.refl {x = scV k V₄})))
      (≡.trans (cong-act (ω j ^ e₁ • ω α ^ e₂) (ω^-action β e₃ k V₄))
        (≡.trans (cong-act (ω j ^ e₁) (ω^-action α e₂ k V₃))
          (≡.trans (ω^-action j e₁ k V₂) (≡.cong (scV k) V₁≡))))
    where
    cong-act : (u : Word (Gen n)) {x y : Vec D n} → x ≡ y → actVʷ u x ≡ actVʷ u y
    cong-act u ≡.refl = ≡.refl
    V₄ = set₁ ℓ′ ((ωᶻ ^ᶻ e₄) ZR.* (W ! ℓ′)) W
    V₃ = set₁ β ((ωᶻ ^ᶻ e₃) ZR.* (V₄ ! β)) V₄
    V₂ = set₁ α ((ωᶻ ^ᶻ e₂) ZR.* (V₃ ! α)) V₃
    V₁ = set₁ j ((ωᶻ ^ᶻ e₁) ZR.* (V₂ ! j)) V₂
    V₄β : V₄ ! β ≡ W ! β
    V₄β = set₁-≢ ℓ′ _ W β≢ℓ′
    V₃α : V₃ ! α ≡ W ! α
    V₃α = ≡.trans (set₁-≢ β _ V₄ α≢β) (set₁-≢ ℓ′ _ W α≢ℓ′)
    V₂j : V₂ ! j ≡ W ! j
    V₂j = ≡.trans (set₁-≢ α _ V₃ j≢α) (≡.trans (set₁-≢ β _ V₄ j≢β) (set₁-≢ ℓ′ _ W j≢ℓ′))
    V₁≡ : V₁ ≡ Nv ((ωᶻ ^ᶻ e₁) ZR.* (W ! j)) ((ωᶻ ^ᶻ e₂) ZR.* (W ! α)) ((ωᶻ ^ᶻ e₃) ZR.* (W ! β)) ((ωᶻ ^ᶻ e₄) ZR.* (W ! ℓ′))
    V₁≡ = Nv-ext V₁
      (≡.trans (set₁-a j _ V₂) (≡.cong ((ωᶻ ^ᶻ e₁) ZR.*_) V₂j))
      (≡.trans (set₁-≢ j _ V₂ (≢-sym j≢α)) (≡.trans (set₁-a α _ V₃) (≡.cong ((ωᶻ ^ᶻ e₂) ZR.*_) V₃α)))
      (≡.trans (set₁-≢ j _ V₂ (≢-sym j≢β)) (≡.trans (set₁-≢ α _ V₃ (≢-sym α≢β))
        (≡.trans (set₁-a β _ V₄) (≡.cong ((ωᶻ ^ᶻ e₃) ZR.*_) V₄β))))
      (≡.trans (set₁-≢ j _ V₂ (≢-sym j≢ℓ′)) (≡.trans (set₁-≢ α _ V₃ (≢-sym α≢ℓ′))
        (≡.trans (set₁-≢ β _ V₄ (≢-sym β≢ℓ′)) (set₁-a ℓ′ _ W))))
      (λ x a b c d → ≡.trans (set₁-≢ j _ V₂ a) (≡.trans (set₁-≢ α _ V₃ b)
                       (≡.trans (set₁-≢ β _ V₄ c) (set₁-≢ ℓ′ _ W d))))

  private
    ⊥e : ∀ {A : Set} {x y : Fin n} → x ≢ y → x ≡ y → A
    ⊥e ne e = ⊥-elim (ne e)
    rfl : ∀ {A : Set} {x : A} {B : Set} → B → x ≡ x
    rfl _ = ≡.refl

  module _ (k : ℕ) where

    -- H_[j,α] on (1 + a δ³ , 1 + b δ³ , 1 + c δ³ , 1 + d δ³).
    step₀ : ∀ a b c d → actV (H-gen j α jα) (scV k (Nv (zz a) (zz b) (zz c) (zz d))) ≡
                        scV k (Nv (y₁ a b) (y₂ a b) (zz c) (zz d))
    step₀ a b c d = H-pair jα k (Nv-j _ _ _ _) (Nv-α _ _ _ _) (Nv-j _ _ _ _) (Nv-α _ _ _ _) (h0₊ a b) (h0₋ a b)
      (λ x a′ b′ → Nv-same x (⊥e a′) (⊥e b′) rfl rfl)

    -- H_[β,ℓ′], first and last.
    step₁ : ∀ a b c d → actV (H-gen β ℓ′ βℓ′) (scV k (Nv (y₁ a b) (y₂ a b) (zz c) (zz d))) ≡
                        scV k (Nv (y₁ a b) (y₂ a b) (y₁ c d) (y₂ c d))
    step₁ a b c d = H-pair βℓ′ k (Nv-β _ _ _ _) (Nv-ℓ′ _ _ _ _) (Nv-β _ _ _ _) (Nv-ℓ′ _ _ _ _) (h0₊ c d) (h0₋ c d)
      (λ x a′ b′ → Nv-same x rfl rfl (⊥e a′) (⊥e b′))

    step₇ : ∀ a b c d → actV (H-gen β ℓ′ βℓ′) (scV k (Nv (y₁ a c) (y₂ a c) (y₁ b d) (y₂ b d))) ≡
                        scV k (Nv (y₁ a c) (y₂ a c) (zz b) (zz d))
    step₇ a b c d = H-pair βℓ′ k (Nv-β _ _ _ _) (Nv-ℓ′ _ _ _ _) (Nv-β _ _ _ _) (Nv-ℓ′ _ _ _ _) (h7₊ b d) (h7₋ b d)
      (λ x a′ b′ → Nv-same x rfl rfl (⊥e a′) (⊥e b′))

    -- The first path: H_[j,β], H_[α,ℓ′], X_[α,β], H_[α,ℓ′], H_[j,β].
    module Path₀ (a b c A : Z) where

      d = dd₀ a b c A

      step₂ : actV (H-gen j β jβ) (scV k (Nv (y₁ a b) (y₂ a b) (y₁ c d) (y₂ c d))) ≡
              scV k (Nv (s₂j A) (y₂ a b) (sβ a b A) (y₂ c d))
      step₂ = H-pair jβ k (Nv-j _ _ _ _) (Nv-β _ _ _ _) (Nv-j _ _ _ _) (Nv-β _ _ _ _) (h2₊ a b c A) (h2₋ a b c A)
        (λ x a′ b′ → Nv-same x (⊥e a′) rfl (⊥e b′) rfl)

      step₃ : actV (H-gen α ℓ′ αℓ′) (scV k (Nv (s₂j A) (y₂ a b) (sβ a b A) (y₂ c d))) ≡
              scV k (Nv (s₂j A) (sβ a c A) (sβ a b A) (sℓ b c A))
      step₃ = H-pair αℓ′ k (Nv-α _ _ _ _) (Nv-ℓ′ _ _ _ _) (Nv-α _ _ _ _) (Nv-ℓ′ _ _ _ _) (h3₊ a b c A) (h3₋ a b c A)
        (λ x a′ b′ → Nv-same x rfl (⊥e a′) rfl (⊥e b′))

      step₄ : actV (X-gen α β αβ) (scV k (Nv (s₂j A) (sβ a c A) (sβ a b A) (sℓ b c A))) ≡
              scV k (Nv (s₂j A) (sβ a b A) (sβ a c A) (sℓ b c A))
      step₄ = X-step α β αβ k _ _
        (≡.trans (Nv-α _ _ _ _) (≡.sym (Nv-β _ _ _ _)))
        (≡.trans (Nv-β _ _ _ _) (≡.sym (Nv-α _ _ _ _)))
        (λ x a′ b′ → Nv-same x rfl (⊥e a′) (⊥e b′) rfl)

      step₅ : actV (H-gen α ℓ′ αℓ′) (scV k (Nv (s₂j A) (sβ a b A) (sβ a c A) (sℓ b c A))) ≡
              scV k (Nv (s₂j A) (y₂ a c) (sβ a c A) (y₂ b d))
      step₅ = H-pair αℓ′ k (Nv-α _ _ _ _) (Nv-ℓ′ _ _ _ _) (Nv-α _ _ _ _) (Nv-ℓ′ _ _ _ _) (h5₊ a b c A) (h5₋ a b c A)
        (λ x a′ b′ → Nv-same x rfl (⊥e a′) rfl (⊥e b′))

      step₆ : actV (H-gen j β jβ) (scV k (Nv (s₂j A) (y₂ a c) (sβ a c A) (y₂ b d))) ≡
              scV k (Nv (y₁ a c) (y₂ a c) (y₁ b d) (y₂ b d))
      step₆ = H-pair jβ k (Nv-j _ _ _ _) (Nv-β _ _ _ _) (Nv-j _ _ _ _) (Nv-β _ _ _ _) (h6₊ a c A) (h6₋ a b c A)
        (λ x a′ b′ → Nv-same x (⊥e a′) rfl (⊥e b′) rfl)

    -- The second path: H_[α,β], H_[j,ℓ′], X_[α,ℓ′], H_[j,ℓ′], H_[α,β].
    module Path₁ (a b c A : Z) where

      d = dd₁ a b c A

      step₂ : actV (H-gen α β αβ) (scV k (Nv (y₁ a b) (y₂ a b) (y₁ c d) (y₂ c d))) ≡
              scV k (Nv (y₁ a b) (tα b A) (t₂β a A) (y₂ c d))
      step₂ = H-pair αβ k (Nv-α _ _ _ _) (Nv-β _ _ _ _) (Nv-α _ _ _ _) (Nv-β _ _ _ _) (k2₊ a b c A) (k2₋ a b c A)
        (λ x a′ b′ → Nv-same x rfl (⊥e a′) (⊥e b′) rfl)

      step₃ : actV (H-gen j ℓ′ jℓ′) (scV k (Nv (y₁ a b) (tα b A) (t₂β a A) (y₂ c d))) ≡
              scV k (Nv (t₃j a b c A) (tα b A) (t₂β a A) (tα c A))
      step₃ = H-pair jℓ′ k (Nv-j _ _ _ _) (Nv-ℓ′ _ _ _ _) (Nv-j _ _ _ _) (Nv-ℓ′ _ _ _ _) (k3₊ a b c A) (k3₋ a b c A)
        (λ x a′ b′ → Nv-same x (⊥e a′) rfl rfl (⊥e b′))

      step₄ : actV (X-gen α ℓ′ αℓ′) (scV k (Nv (t₃j a b c A) (tα b A) (t₂β a A) (tα c A))) ≡
              scV k (Nv (t₃j a b c A) (tα c A) (t₂β a A) (tα b A))
      step₄ = X-step α ℓ′ αℓ′ k _ _
        (≡.trans (Nv-α _ _ _ _) (≡.sym (Nv-ℓ′ _ _ _ _)))
        (≡.trans (Nv-ℓ′ _ _ _ _) (≡.sym (Nv-α _ _ _ _)))
        (λ x a′ b′ → Nv-same x rfl (⊥e a′) rfl (⊥e b′))

      step₅ : actV (H-gen j ℓ′ jℓ′) (scV k (Nv (t₃j a b c A) (tα c A) (t₂β a A) (tα b A))) ≡
              scV k (Nv (y₁ a c) (tα c A) (t₂β a A) (y₂ b d))
      step₅ = H-pair jℓ′ k (Nv-j _ _ _ _) (Nv-ℓ′ _ _ _ _) (Nv-j _ _ _ _) (Nv-ℓ′ _ _ _ _) (k5₊ a b c A) (k5₋ a b c A)
        (λ x a′ b′ → Nv-same x (⊥e a′) rfl rfl (⊥e b′))

      step₆ : actV (H-gen α β αβ) (scV k (Nv (y₁ a c) (tα c A) (t₂β a A) (y₂ b d))) ≡
              scV k (Nv (y₁ a c) (y₂ a c) (y₁ b d) (y₂ b d))
      step₆ = H-pair αβ k (Nv-α _ _ _ _) (Nv-β _ _ _ _) (Nv-α _ _ _ _) (Nv-β _ _ _ _) (k6₊ a c A) (k6₋ a b c A)
        (λ x a′ b′ → Nv-same x rfl (⊥e a′) (⊥e b′) rfl)
