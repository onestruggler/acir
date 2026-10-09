------------------------------------------------------------------------
-- Presentations of groups
--
-- The syllable of a matrix (one output of Algorithm 1), and the facts
-- about the action of words that the analysis of the algorithm uses:
-- words acting on indices ≤ p leave the columns beyond p alone, and
-- the action of (-1)_[a]^τ on columns.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Syllable where

open import Data.Empty using (⊥-elim)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base as Vec using (Vec ; tabulate)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Ring
open import Examples.Groups.CCX+HH-TwoLevel.Scale
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (scV ; scV-! ; lde ; num)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.ColumnAction
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
open import Examples.Groups.CCX+HH-TwoLevel.Pivot

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The syllable, and one step of the algorithm

sylAt : Maybe (Fin n) → Matrix n n D → Word (Gen n)
sylAt nothing  M = ε
sylAt (just p) M = sylData p (lde (col M p)) (num (col M p))

syl : Matrix n n D → Word (Gen n)
syl M = sylAt (pivot M) M

syl-just : (M : Matrix n n D) {p : Fin n} → pivot M ≡ just p →
           syl M ≡ sylData p (lde (col M p)) (num (col M p))
syl-just M eq = cong (λ x → sylAt x M) eq

syl-nothing : (M : Matrix n n D) → pivot M ≡ nothing → syl M ≡ ε
syl-nothing M eq = cong (λ x → sylAt x M) eq

-- Step 18: apply the syllable.
step : Matrix n n D → Matrix n n D
step M = actMʷ (syl M) M

------------------------------------------------------------------------
-- Words acting on indices ≤ p

-- The largest index a generator acts on (its extent, Definition A.18).
top : Gen n → Fin n
top (M-gen a)             = a
top (X-gen a b _)         = b
top (K-gen a b c d _ _ _) = d

Within : Fin n → Word (Gen n) → Set
Within p [ g ]ʷ   = top g ≤ p
Within p ε        = ⊤
Within p (u • v)  = Within p u × Within p v

private
  rc : ∀ {a b : Fin n} → .(a < b) → a < b
  rc {a = a} {b} lt = recompute (a FinP.<? b) lt

∈ₛ-top : ∀ {x : Fin n} {g} → x ∈ₛ g → x ≤ top g
∈ₛ-top M-a = FinP.≤-refl
∈ₛ-top (X-a {p = p}) = ℕP.<⇒≤ (rc p)
∈ₛ-top X-b = FinP.≤-refl
∈ₛ-top (K-a {p = p} {q} {r}) = ℕP.<⇒≤ (FinP.<-trans (rc p) (FinP.<-trans (rc q) (rc r)))
∈ₛ-top (K-b {q = q} {r}) = ℕP.<⇒≤ (FinP.<-trans (rc q) (rc r))
∈ₛ-top (K-c {r = r}) = ℕP.<⇒≤ (rc r)
∈ₛ-top K-d = FinP.≤-refl

-- The zero vector is fixed by every generator.
zeroV : Vec D n
zeroV = Vec.replicate _ DR.0#

private
  0! : (x : Fin n) → zeroV ! x ≡ DR.0#
  0! x = VecP.lookup-replicate x DR.0#

  neg0 : DR.- DR.0# ≡ DR.0#
  neg0 = DS.solve 0 (DS.:- DS.con (+ 0) DS.:= DS.con (+ 0)) refl

  lin0 : ∀ s₁ s₂ s₃ s₄ → lin s₁ s₂ s₃ s₄ DR.0# DR.0# DR.0# DR.0# ≡ DR.0#
  lin0 s₁ s₂ s₃ s₄ =
    DS.solve 5 (λ h s₁ s₂ s₃ s₄ → h DS.:* (s₁ DS.:* DS.con (+ 0) DS.:+ s₂ DS.:* DS.con (+ 0)
                                           DS.:+ s₃ DS.:* DS.con (+ 0) DS.:+ s₄ DS.:* DS.con (+ 0))
                                   DS.:= DS.con (+ 0))
      refl ½ᴰ s₁ s₂ s₃ s₄

-- (The case analyses are helpers with their types written out, not
-- dec-elim: its result type, inferred from the branches, makes this
-- intractable.)
actV-0 : (g : Gen n) → actV g zeroV ≡ zeroV
actV-0 (M-gen a) = vec-ext λ x → aux x (x FinP.≟ a)
  where
  aux : ∀ x → Dec (x ≡ a) → actV (M-gen a) zeroV ! x ≡ zeroV ! x
  aux x (yes refl) = trans (actV-Ma x zeroV) (trans (cong DR.-_ (0! x)) (trans neg0 (sym (0! x))))
  aux x (no x≢a) = actV-M≢ a zeroV x≢a
actV-0 (X-gen a b p) = vec-ext λ x → aux x (x FinP.≟ a) (x FinP.≟ b)
  where
  aux : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → actV (X-gen a b p) zeroV ! x ≡ zeroV ! x
  aux x (yes refl) _ = trans (actV-Xa p zeroV) (trans (0! b) (sym (0! x)))
  aux x (no x≢a) (yes refl) = trans (actV-Xb p zeroV) (trans (0! a) (sym (0! x)))
  aux x (no x≢a) (no x≢b) = actV-X≢ p zeroV x≢a x≢b
actV-0 (K-gen a b c d p q r) = vec-ext λ x → aux x (x FinP.≟ a) (x FinP.≟ b) (x FinP.≟ c) (x FinP.≟ d)
  where
  g = K-gen a b c d p q r
  z4 : ∀ (f : D → D → D → D → D) → f (zeroV ! a) (zeroV ! b) (zeroV ! c) (zeroV ! d) ≡ f DR.0# DR.0# DR.0# DR.0#
  z4 f = trans (cong (λ t → f t (zeroV ! b) (zeroV ! c) (zeroV ! d)) (0! a))
           (trans (cong (λ t → f DR.0# t (zeroV ! c) (zeroV ! d)) (0! b))
             (trans (cong (λ t → f DR.0# DR.0# t (zeroV ! d)) (0! c)) (cong (λ t → f DR.0# DR.0# DR.0# t) (0! d))))
  aux : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Dec (x ≡ c) → Dec (x ≡ d) → actV g zeroV ! x ≡ zeroV ! x
  aux x (yes refl) _ _ _ = trans (actV-Ka p q r zeroV) (trans (z4 rowA) (trans (lin0 DR.1# DR.1# DR.1# DR.1#) (sym (0! x))))
  aux x (no _) (yes refl) _ _ = trans (actV-Kb p q r zeroV) (trans (z4 rowB) (trans (lin0 DR.1# m1 DR.1# m1) (sym (0! x))))
  aux x (no _) (no _) (yes refl) _ = trans (actV-Kc p q r zeroV) (trans (z4 rowC) (trans (lin0 DR.1# DR.1# m1 m1) (sym (0! x))))
  aux x (no _) (no _) (no _) (yes refl) = trans (actV-Kd p q r zeroV) (trans (z4 rowD) (trans (lin0 DR.1# m1 m1 DR.1#) (sym (0! x))))
  aux x (no xa) (no xb) (no xc) (no xd) = actV-K≢ p q r zeroV xa xb xc xd

-- A generator acting on indices ≤ p fixes the standard basis vectors
-- beyond p.
actV-e-beyond : (g : Gen n) {p c : Fin n} → top g ≤ p → p < c → actV g (col 𝕀 c) ≡ col 𝕀 c
actV-e-beyond g {p} {c} tp pc = vec-ext λ x →
  dec-elim (∈ₛ? x g)
    (λ x∈g → begin
      actV g e ! x          ≡⟨ actV-local g e zeroV agree x x∈g ⟩
      actV g zeroV ! x      ≡⟨ cong (_! x) (actV-0 g) ⟩
      zeroV ! x             ≡⟨ sym (agree x x∈g) ⟩
      e ! x                 ∎)
    (λ x∉g → actV-off g e x x∉g)
  where
  open ≡-Reasoning
  e = col 𝕀 c
  agree : ∀ y → y ∈ₛ g → e ! y ≡ zeroV ! y
  agree y y∈g = trans (ent-𝕀 y c) (trans (δ-≢ y≢c) (sym (0! y)))
    where
    y≢c : y ≢ c
    y≢c refl = FinP.<-irrefl refl (ℕP.≤-<-trans (ℕP.≤-trans (∈ₛ-top y∈g) tp) pc)

Beyond-actM : (g : Gen n) {p : Fin n} {M : Matrix n n D} → top g ≤ p → Beyond p M → Beyond p (actM g M)
Beyond-actM g {M = M} tp be c pc =
  trans (col-actM g M c) (trans (cong (actV g) (be c pc)) (actV-e-beyond g tp pc))

Beyond-actMʷ : (w : Word (Gen n)) {p : Fin n} {M : Matrix n n D} → Within p w → Beyond p M → Beyond p (actMʷ w M)
Beyond-actMʷ [ g ]ʷ {p} {M} h be = Beyond-actM g {p} {M} h be
Beyond-actMʷ ε h be = be
Beyond-actMʷ (u • v) {p} {M} (hu , hv) be = Beyond-actMʷ u {p} {actMʷ v M} hu (Beyond-actMʷ v {p} {M} hv be)

------------------------------------------------------------------------
-- Standard basis vectors as scaled vectors

eδ : Fin n → Fin n → ℤ
eδ x c with x FinP.≟ c
... | yes _ = + 1
... | no  _ = + 0

eᶻ : Fin n → Vec ℤ n
eᶻ c = tabulate (λ x → eδ x c)

eδ-refl : (x : Fin n) → eδ x x ≡ + 1
eδ-refl x with x FinP.≟ x
... | yes _ = refl
... | no x≢x = ⊥-elim (x≢x refl)

eδ-≢ : {x c : Fin n} → x ≢ c → eδ x c ≡ + 0
eδ-≢ {x = x} {c} x≢c with x FinP.≟ c
... | yes x≡c = ⊥-elim (x≢c x≡c)
... | no _ = refl

eᶻ-! : (c x : Fin n) → eᶻ c ! x ≡ eδ x c
eᶻ-! c x = VecP.lookup∘tabulate (λ x → eδ x c) x

private
  sc0-1 : sc 0 (+ 1) ≡ DR.1#
  sc0-1 = trans (sc-def 0 (+ 1)) (DR.*-identityʳ DR.1#)

  δ≡ : (x c : Fin n) → δ x c ≡ sc 0 (eδ x c)
  δ≡ x c = dec-elim (x FinP.≟ c)
    (λ { refl → trans (δ-refl x) (sym (trans (cong (sc 0) (eδ-refl x)) sc0-1)) })
    (λ x≢c → trans (δ-≢ x≢c) (sym (trans (cong (sc 0) (eδ-≢ x≢c)) (sc-0 0))))

col𝕀≡ : (c : Fin n) → col 𝕀 c ≡ scV 0 (eᶻ c)
col𝕀≡ c = vec-ext λ x → begin
  col 𝕀 c ! x               ≡⟨ ent-𝕀 x c ⟩
  δ x c                     ≡⟨ δ≡ x c ⟩
  sc 0 (eδ x c)             ≡⟨ cong (sc 0) (sym (VecP.lookup∘tabulate (λ x → eδ x c) x)) ⟩
  sc 0 (eᶻ c ! x)           ≡⟨ sym (scV-! 0 (eᶻ c) x) ⟩
  scV 0 (eᶻ c) ! x          ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Updating one entry twice, or by its own value

set₁-set₁ : {B : Set} (a : Fin n) (α β : B) (v : Vec B n) → set₁ a α (set₁ a β v) ≡ set₁ a α v
set₁-set₁ a α β v = vec-ext λ x →
  dec-elim (x FinP.≟ a)
    (λ { refl → trans (set₁-a x α (set₁ x β v)) (sym (set₁-a x α v)) })
    (λ x≢a → trans (set₁-≢ a α (set₁ a β v) x≢a) (trans (set₁-≢ a β v x≢a) (sym (set₁-≢ a α v x≢a))))

set₁-self : {B : Set} (a : Fin n) (v : Vec B n) → set₁ a (v ! a) v ≡ v
set₁-self a v = vec-ext λ x →
  dec-elim (x FinP.≟ a)
    (λ { refl → set₁-a x (v ! x) v })
    (λ x≢a → set₁-≢ a (v ! a) v x≢a)

------------------------------------------------------------------------
-- The action of (-1)_[a]^τ on columns

-- (-1)_[a]^τ negates entry a if τ.
Mτ-action : (a : Fin n) (t : Bool) (k : ℕ) (w : Vec ℤ n) →
            actVʷ (Mτ a t) (scV k w) ≡ scV k (if t then Mᶻ a w else w)
Mτ-action a true  k w = actV-M a k w
Mτ-action a false k w = refl
