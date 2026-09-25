------------------------------------------------------------------------
-- Presentations of groups
--
-- Least denominator exponents (§2.1): every vector v over 𝔻[i] is
-- w / γᵏ for a unique k and w ∈ ℤ[i]ⁿ such that k = 0 or some entry of
-- w is odd.  This k is the least denominator exponent lde v, and w is
-- num v = γ^(lde v) v.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Lde where

open import Data.Bool.Base using (Bool ; true ; false)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
import Data.Fin.Properties as FinP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; _⊔_ ; _∸_ ; _≤_ ; _<_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; ∃₂ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_ ; lookup ; tabulate)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)

open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Scale
open import Examples.Groups.Clifford+CS-TwoLevel.Vector public using (_!_)
open import Examples.Groups.Clifford+CS-TwoLevel.Vector using (vec-ext)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Scaled vectors

-- scV k w = w / γᵏ, entrywise.
scV : ℕ → Vec Z n → Vec D n
scV k w = Vec.map (sc k) w

scV-! : ∀ k (w : Vec Z n) x → scV k w ! x ≡ sc k (w ! x)
scV-! k w x = VecP.lookup-map x (sc k) w

-- Odd and even Gaussian integers.
Odd Even : Z → Set
Odd w = oddᶻ w ≡ true
Even w = oddᶻ w ≡ false

odd? : (w : Z) → Dec (Odd w)
odd? w with oddᶻ w
... | true  = yes refl
... | false = no λ ()

¬Even⇒Odd : ∀ {w} → ¬ Even w → Odd w
¬Even⇒Odd {w} ¬e with oddᶻ w
... | true  = refl
... | false = ⊥-elim (¬e refl)

¬Odd⇒Even : ∀ {w} → ¬ Odd w → Even w
¬Odd⇒Even {w} ¬o with oddᶻ w
... | true  = ⊥-elim (¬o refl)
... | false = refl

Odd⇒¬Even : ∀ {w} → Odd w → ¬ Even w
Odd⇒¬Even o e = contradiction (trans (sym o) e) λ ()

-- A representation w / γᵏ is minimal if k = 0 or some entry is odd.
Minimal : ℕ → Vec Z n → Set
Minimal k w = k ≡ 0 ⊎ ∃ λ x → Odd (w ! x)

------------------------------------------------------------------------
-- Existence

-- Some exponent works for every vector.
repV : (v : Vec D n) → ∃₂ λ K w → v ≡ scV K w
repV [] = 0 , [] , refl
repV (x ∷ xs) with rep x | repV xs
... | K₁ , z , x≡ | K₂ , ws , xs≡ =
  K , (γᶻ ^ᶻ (K ∸ K₁)) ZR.* z ∷ Vec.map ((γᶻ ^ᶻ (K ∸ K₂)) ZR.*_) ws ,
  cong₂ _∷_ (trans x≡ (raise K₁ (ℕP.m≤m⊔n K₁ K₂) z))
            (trans xs≡ (vec-ext λ y → begin
               scV K₂ ws ! y                                   ≡⟨ scV-! K₂ ws y ⟩
               sc K₂ (ws ! y)                                  ≡⟨ raise K₂ (ℕP.m≤n⊔m K₁ K₂) (ws ! y) ⟩
               sc K ((γᶻ ^ᶻ (K ∸ K₂)) ZR.* (ws ! y))           ≡⟨ cong (sc K) (sym (VecP.lookup-map y ((γᶻ ^ᶻ (K ∸ K₂)) ZR.*_) ws)) ⟩
               sc K (Vec.map ((γᶻ ^ᶻ (K ∸ K₂)) ZR.*_) ws ! y)  ≡⟨ sym (scV-! K (Vec.map ((γᶻ ^ᶻ (K ∸ K₂)) ZR.*_) ws) y) ⟩
               scV K (Vec.map ((γᶻ ^ᶻ (K ∸ K₂)) ZR.*_) ws) ! y ∎))
  where
  open ≡-Reasoning
  K = K₁ ⊔ K₂
  raise : ∀ k → k ≤ K → ∀ z → sc k z ≡ sc K ((γᶻ ^ᶻ (K ∸ k)) ZR.* z)
  raise k k≤K z = trans (sc-raise (K ∸ k) k z) (cong (λ e → sc e ((γᶻ ^ᶻ (K ∸ k)) ZR.* z)) (ℕP.m∸n+n≡m k≤K))

-- Dividing a vector of even entries by γ.
halveV : (w : Vec Z n) → (∀ x → Even (w ! x)) → Vec Z n
halveV w ev = tabulate (λ x → proj₁ (even⇒γ∣ (w ! x) (ev x)))

halveV-! : (w : Vec Z n) (ev : ∀ x → Even (w ! x)) (x : Fin n) → w ! x ≡ γᶻ ZR.* (halveV w ev ! x)
halveV-! w ev x = trans (proj₂ (even⇒γ∣ (w ! x) (ev x)))
                        (cong (γᶻ ZR.*_) (sym (VecP.lookup∘tabulate (λ x → proj₁ (even⇒γ∣ (w ! x) (ev x))) x)))

scV-halve : ∀ k (w : Vec Z n) (ev : ∀ x → Even (w ! x)) → scV (suc k) w ≡ scV k (halveV w ev)
scV-halve k w ev = vec-ext λ x → begin
  scV (suc k) w ! x                        ≡⟨ scV-! (suc k) w x ⟩
  sc (suc k) (w ! x)                       ≡⟨ cong (sc (suc k)) (halveV-! w ev x) ⟩
  sc (suc k) (γᶻ ZR.* (halveV w ev ! x))   ≡⟨ sc-γ k (halveV w ev ! x) ⟩
  sc k (halveV w ev ! x)                   ≡⟨ sym (scV-! k (halveV w ev) x) ⟩
  scV k (halveV w ev) ! x                  ∎
  where open ≡-Reasoning

all-even? : (w : Vec Z n) → Dec (∀ x → Even (w ! x))
all-even? w = FinP.all? (λ x → oddᶻ (w ! x) BoolP.≟ false)

-- A minimal representation.
record Rep (v : Vec D n) : Set where
  constructor rep⟨_,_,_,_⟩
  field
    k   : ℕ
    w   : Vec Z n
    eq  : v ≡ scV k w
    min : Minimal k w

-- Lower the exponent while every entry is even.
lower : ∀ {v : Vec D n} K w → v ≡ scV K w → Rep v
lower zero w eq = rep⟨ 0 , w , eq , inj₁ refl ⟩
lower (suc K) w eq with all-even? w
... | yes ev = lower K (halveV w ev) (trans eq (scV-halve K w ev))
... | no ¬ev with FinP.¬∀⇒∃¬ _ (λ x → Even (w ! x)) (λ x → oddᶻ (w ! x) BoolP.≟ false) ¬ev
...   | x , ¬e = rep⟨ suc K , w , eq , inj₂ (x , ¬Even⇒Odd {w ! x} ¬e) ⟩

rep-exists : (v : Vec D n) → Rep v
rep-exists v with repV v
... | K , w , eq = lower K w eq

------------------------------------------------------------------------
-- Uniqueness

private
  -- A multiple of γ is even.
  γ*-even : ∀ y → Even (γᶻ ZR.* y)
  γ*-even y = γ∣⇒even (y , refl)

  -- A representation with a larger exponent than another is not minimal.
  dominated : ∀ {k k'} {w w' : Vec Z n} → k ℕ.< k' → scV k w ≡ scV k' w' → ¬ Minimal k' w'
  dominated k<k' eq (inj₁ refl) = ⊥-elim (ℕP.n≮0 k<k')
  dominated {k = k} {k'} {w} {w'} k<k' eq (inj₂ (x , odd)) = Odd⇒¬Even {w' ! x} odd w'x-even
    where
    open ≡-Reasoning
    d = k' ∸ k
    d≡ : d ℕ.+ k ≡ k'
    d≡ = ℕP.m∸n+n≡m (ℕP.<⇒≤ k<k')
    w'x≡ : w' ! x ≡ (γᶻ ^ᶻ d) ZR.* (w ! x)
    w'x≡ = sc-injective k' (begin
      sc k' (w' ! x)                          ≡⟨ sym (scV-! k' w' x) ⟩
      scV k' w' ! x                           ≡⟨ cong (_! x) (sym eq) ⟩
      scV k w ! x                             ≡⟨ scV-! k w x ⟩
      sc k (w ! x)                            ≡⟨ sc-raise d k (w ! x) ⟩
      sc (d ℕ.+ k) ((γᶻ ^ᶻ d) ZR.* (w ! x))   ≡⟨ cong (λ e → sc e ((γᶻ ^ᶻ d) ZR.* (w ! x))) d≡ ⟩
      sc k' ((γᶻ ^ᶻ d) ZR.* (w ! x))          ∎)
    d≢0 : d ≢ 0
    d≢0 d≡0 = ℕP.<⇒≢ k<k' (trans (sym (cong (ℕ._+ k) d≡0)) d≡)
    w'x-even : Even (w' ! x)
    w'x-even with d | d≢0 | w'x≡
    ... | zero  | d≢0′ | _ = ⊥-elim (d≢0′ refl)
    ... | suc e | _    | eq′ = trans (cong oddᶻ eq′)
                                     (trans (cong oddᶻ (ZR.*-assoc γᶻ (γᶻ ^ᶻ e) (w ! x))) (γ*-even ((γᶻ ^ᶻ e) ZR.* (w ! x))))

rep-unique : ∀ {v : Vec D n} (r r' : Rep v) → Rep.k r ≡ Rep.k r' × Rep.w r ≡ Rep.w r'
rep-unique rep⟨ k , w , eq , min ⟩ rep⟨ k' , w' , eq' , min' ⟩ with ℕP.<-cmp k k'
... | tri< k<k' _ _ = ⊥-elim (dominated k<k' (trans (sym eq) eq') min')
... | tri> _ _ k'<k = ⊥-elim (dominated k'<k (trans (sym eq') eq) min)
... | tri≈ _ refl _ = refl , vec-ext λ x → sc-injective k (begin
    sc k (w ! x)      ≡⟨ sym (scV-! k w x) ⟩
    scV k w ! x       ≡⟨ cong (_! x) (trans (sym eq) eq') ⟩
    scV k w' ! x      ≡⟨ scV-! k w' x ⟩
    sc k (w' ! x)     ∎)
  where
  open ≡-Reasoning

------------------------------------------------------------------------
-- The least denominator exponent and the numerator

lde : Vec D n → ℕ
lde v = Rep.k (rep-exists v)

num : Vec D n → Vec Z n
num v = Rep.w (rep-exists v)

lde-eq : (v : Vec D n) → v ≡ scV (lde v) (num v)
lde-eq v = Rep.eq (rep-exists v)

lde-min : (v : Vec D n) → Minimal (lde v) (num v)
lde-min v = Rep.min (rep-exists v)

-- Any minimal representation is the one computed.
lde-char : ∀ {v : Vec D n} k w → v ≡ scV k w → Minimal k w → lde v ≡ k × num v ≡ w
lde-char {v = v} k w eq min = rep-unique (rep-exists v) rep⟨ k , w , eq , min ⟩

-- Lowering never raises the exponent.
lower-≤ : ∀ {v : Vec D n} K w (eq : v ≡ scV K w) → Rep.k (lower K w eq) ℕ.≤ K
lower-≤ zero w eq = ℕ.z≤n
lower-≤ (suc K) w eq with all-even? w
... | yes ev = ℕP.m≤n⇒m≤1+n (lower-≤ K (halveV w ev) (trans eq (scV-halve K w ev)))
... | no ¬ev with FinP.¬∀⇒∃¬ _ (λ x → Even (w ! x)) (λ x → oddᶻ (w ! x) BoolP.≟ false) ¬ev
...   | x , ¬e = ℕP.≤-refl

-- The least denominator exponent is at most any denominator exponent.
lde-≤ : ∀ {v : Vec D n} K w → v ≡ scV K w → lde v ℕ.≤ K
lde-≤ {v = v} K w eq =
  subst (ℕ._≤ K) (sym (proj₁ (rep-unique (rep-exists v) (lower K w eq)))) (lower-≤ K w eq)
