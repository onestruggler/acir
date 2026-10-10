------------------------------------------------------------------------
-- Presentations of groups
--
-- Counting odd entries of a state's column at a deeper scale.
--
-- Let N be a state whose column p is the numerator V at scale k, and
-- let every entry of V be √2^δ times an entry of U.  Then the column is
-- U at scale k - δ (scale-down; at scale 0 the column would have no odd
-- entry, which a unit vector must have), so an even number of entries
-- of U are odd of class 1 (Norm.evenclass), and an even number are odd
-- unless only one is (Norm.evenodd, Norm.lde0).
--
-- When V is an embedding of a local vector e, the entries of U count
-- as those of the local quotient plus those outside (count-embP); an
-- odd count inside then gives an entry of that kind outside (extra).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Count {n : ℕ} (p : Fin n) where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; not ; if_then_else_ ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (zero ; suc)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; ∃₂ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_ ; tabulate)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (oddℕ ; oddℕ-+)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count ; count-cong ; count-drop ; count-false ; count-one ; first ; first-just ; first-nothing)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; module DR ; √2ᶻ ; _^ᶻ_ ; oddᶻ ; rbit ; oddᶻ-*)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (scV)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm using (NA ; NB ; Σℕ ; Σℤ ; parity-count ; unit-norm ; unit-normB ; evenodd ; evenclass ; lde0)
open import Data.Integer.Base using (+_)
import Data.Integer.Properties as ℤP
open import Relation.Nullary.Decidable using (recompute)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Counting using (count-split)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step using (scV-δmap)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Local {n} using (module Emb)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check using (countV)

private
  t≢f : true ≢ false
  t≢f ()

------------------------------------------------------------------------
-- Counting over vectors

-- A positive count has a witness.
count-exists : ∀ {k} (P : Fin k → Bool) → 0 ℕ.< count P → ∃ λ x → P x ≡ true
count-exists P pos with first P in f
... | just x = x , proj₁ (first-just P f)
... | nothing = ⊥-elim (ℕP.<-irrefl (≡.sym (count-false P (first-nothing P f))) pos)

ind : Bool → ℕ
ind b = if b then 1 else 0

-- Changing one index of a predicate.
count-replace : ∀ {k} (P Q : Fin k → Bool) (a : Fin k) → (∀ x → x ≢ a → P x ≡ Q x) →
                count P ℕ.+ ind (Q a) ≡ count Q ℕ.+ ind (P a)
count-replace P Q a agree with P a in pa | Q a in qa
... | true | true = ≡.cong (ℕ._+ 1) (count-cong P Q at)
  where
  at : ∀ x → P x ≡ Q x
  at x with x FinP.≟ a
  ... | yes ≡.refl = ≡.trans pa (≡.sym qa)
  ... | no x≢a = agree x x≢a
... | false | false = ≡.cong (ℕ._+ 0) (count-cong P Q at)
  where
  at : ∀ x → P x ≡ Q x
  at x with x FinP.≟ a
  ... | yes ≡.refl = ≡.trans pa (≡.sym qa)
  ... | no x≢a = agree x x≢a
... | true | false = ≡.trans (ℕP.+-identityʳ (count P)) (≡.trans (count-drop P Q a pa qa agree) (ℕP.+-comm 1 (count Q)))
... | false | true = ≡.trans (ℕP.+-comm (count P) 1) (≡.trans (≡.sym (count-drop Q P a qa pa (λ x x≢a → ≡.sym (agree x x≢a))))
                                                               (≡.sym (ℕP.+-identityʳ (count Q))))

-- The count over an embedding: inside, then outside.
count-embP : ∀ {m} (ι : Fin m → Fin n) (inj : ∀ {i j} → ι i ≡ ι j → i ≡ j) (P : Z → Bool) → P ZR.0# ≡ false →
             (e : Vec Z m) (V : Vec Z n) →
             count (λ x → P (Emb.emb ι inj e V ! x)) ≡ countV P e ℕ.+ count (λ x → P (Emb.emb ι inj (Vec.replicate m ZR.0#) V ! x))
count-embP {zero} ι inj P P0 [] V = ≡.refl
count-embP {suc m} ι inj P P0 (x₀ ∷ e) V =
  ℕP.+-cancelʳ-≡ (ind (P (V ! a))) (count PE) (ind (P x₀) ℕ.+ countV P e ℕ.+ count PE₀) (begin
    count PE ℕ.+ ind (P (V ! a))                         ≡⟨ ≡.cong (λ y → count PE ℕ.+ ind (P y)) (≡.sym Ua) ⟩
    count PE ℕ.+ ind (PU a)                              ≡⟨ count-replace PE PU a agreeE ⟩
    count PU ℕ.+ ind (PE a)                              ≡⟨ ≡.cong₂ ℕ._+_ ih (≡.cong (ind ∘ P) Ea) ⟩
    countV P e ℕ.+ count PU₀ ℕ.+ ind (P x₀)              ≡⟨ ≡.cong (λ c → countV P e ℕ.+ c ℕ.+ ind (P x₀)) U₀≡ ⟩
    countV P e ℕ.+ (count PE₀ ℕ.+ ind (P (V ! a))) ℕ.+ ind (P x₀)
      ≡⟨ arith (countV P e) (count PE₀) (ind (P (V ! a))) (ind (P x₀)) ⟩
    ind (P x₀) ℕ.+ countV P e ℕ.+ count PE₀ ℕ.+ ind (P (V ! a)) ∎)
  where
  open ≡.≡-Reasoning
  ι′ : Fin m → Fin n
  ι′ = ι ∘ suc
  inj′ : ∀ {i j} → ι′ i ≡ ι′ j → i ≡ j
  inj′ eq = FinP.suc-injective (inj eq)
  a = ι zero
  out′ : ∀ i → ι′ i ≢ a
  out′ i eq with inj eq
  ... | ()
  U = Emb.emb ι′ inj′ e V
  U₀ = Emb.emb ι′ inj′ (Vec.replicate m ZR.0#) V
  E = Emb.emb ι inj (x₀ ∷ e) V
  E₀ = Emb.emb ι inj (ZR.0# ∷ Vec.replicate m ZR.0#) V
  PE PU PE₀ PU₀ : Fin n → Bool
  PE x = P (E ! x)
  PU x = P (U ! x)
  PE₀ x = P (E₀ ! x)
  PU₀ x = P (U₀ ! x)
  ih : count PU ≡ countV P e ℕ.+ count PU₀
  ih = count-embP ι′ inj′ P P0 e V
  Ua : U ! a ≡ V ! a
  Ua = Emb.emb-o ι′ inj′ e V out′
  U₀a : U₀ ! a ≡ V ! a
  U₀a = Emb.emb-o ι′ inj′ (Vec.replicate m ZR.0#) V out′
  Ea : E ! a ≡ x₀
  Ea = Emb.emb-ι ι inj (x₀ ∷ e) V zero
  E₀a : E₀ ! a ≡ ZR.0#
  E₀a = Emb.emb-ι ι inj (ZR.0# ∷ Vec.replicate m ZR.0#) V zero
  -- Away from a, the embedding is that of the rest.
  away : ∀ (f : Vec Z m) y₀ → ∀ y → y ≢ a → Emb.emb ι inj (y₀ ∷ f) V ! y ≡ Emb.emb ι′ inj′ f V ! y
  away f y₀ y y≢a = at (Emb.where? ι inj y)
    where
    at : _ → Emb.emb ι inj (y₀ ∷ f) V ! y ≡ Emb.emb ι′ inj′ f V ! y
    at (inj₁ (zero , eq)) = ⊥-elim (y≢a (≡.sym eq))
    at (inj₁ (suc i , ≡.refl)) = ≡.trans (Emb.emb-ι ι inj (y₀ ∷ f) V (suc i)) (≡.sym (Emb.emb-ι ι′ inj′ f V i))
    at (inj₂ out) = ≡.trans (Emb.emb-o ι inj (y₀ ∷ f) V out) (≡.sym (Emb.emb-o ι′ inj′ f V (out ∘ suc)))
  agreeE : ∀ y → y ≢ a → PE y ≡ PU y
  agreeE y y≢a = ≡.cong P (away e x₀ y y≢a)
  agreeE₀ : ∀ y → y ≢ a → PE₀ y ≡ PU₀ y
  agreeE₀ y y≢a = ≡.cong P (away (Vec.replicate m ZR.0#) ZR.0# y y≢a)
  U₀≡ : count PU₀ ≡ count PE₀ ℕ.+ ind (P (V ! a))
  U₀≡ = ≡.trans (≡.sym (ℕP.+-identityʳ (count PU₀)))
          (≡.trans (≡.cong (λ b → count PU₀ ℕ.+ ind b) (≡.sym P0))
            (≡.trans (≡.cong (λ y → count PU₀ ℕ.+ ind (P y)) (≡.sym E₀a))
              (≡.trans (≡.sym (count-replace PE₀ PU₀ a agreeE₀))
                (≡.cong (λ y → count PE₀ ℕ.+ ind (P y)) U₀a))))
  arith : ∀ a b c d → a ℕ.+ (b ℕ.+ c) ℕ.+ d ≡ d ℕ.+ a ℕ.+ b ℕ.+ c
  arith a b c d = ≡.trans (ℕP.+-comm (a ℕ.+ (b ℕ.+ c)) d)
                    (≡.trans (≡.sym (ℕP.+-assoc d a (b ℕ.+ c))) (≡.sym (ℕP.+-assoc (d ℕ.+ a) b c)))

------------------------------------------------------------------------
-- Scaling down

private
  -- √2 times anything is even.
  √2-even : ∀ y → oddᶻ (√2ᶻ ZR.* y) ≡ false
  √2-even y = oddᶻ-* √2ᶻ y

  -- Multiplication by √2^(suc δ) is multiplication by √2^δ, then by √2.
  map-pow : ∀ δ (u : Vec Z n) → Vec.map ((√2ᶻ ^ᶻ suc δ) ZR.*_) u ≡ Vec.map (√2ᶻ ZR.*_) (Vec.map ((√2ᶻ ^ᶻ δ) ZR.*_) u)
  map-pow δ u = ≡.trans (VecP.map-cong (λ y → ZR.*-assoc √2ᶻ (√2ᶻ ^ᶻ δ) y) u) (VecP.map-∘ (√2ᶻ ZR.*_) ((√2ᶻ ^ᶻ δ) ZR.*_) u)

-- A unit column at scale 0 is not √2 times a vector.
scale-pos : ∀ {N : Matrix n n D} → .(ColOrth N) → ∀ k (u : Vec Z n) → col N p ≡ scV k (Vec.map (√2ᶻ ZR.*_) u) →
            ∃ λ k′ → k ≡ suc k′
scale-pos o zero u eq = ⊥-elim (t≢f (≡.trans (≡.sym odd1) (≡.trans (≡.cong oddℕ (≡.sym norm)) even0)))
  where
  w = Vec.map (√2ᶻ ZR.*_) u
  norm : Σℕ (λ x → NA (w ! x)) ≡ 1
  norm = recompute (Σℕ (λ x → NA (w ! x)) ℕP.≟ 1) (unit-norm 0 w (≡.subst (λ v → ⟨ v , v ⟩ ≡ DR.1#) eq (col-unit o p)))
  odd1 : oddℕ 1 ≡ true
  odd1 = ≡.refl
  even0 : oddℕ (Σℕ (λ x → NA (w ! x))) ≡ false
  even0 = ≡.trans (parity-count w)
            (≡.cong oddℕ (count-false (λ x → oddᶻ (w ! x))
              (λ x → ≡.trans (≡.cong oddᶻ (VecP.lookup-map x (√2ᶻ ZR.*_) u)) (√2-even (u ! x)))))
scale-pos o (suc k′) u eq = k′ , ≡.refl

-- The column at the lower scale.
scale-down : ∀ {N : Matrix n n D} → .(ColOrth N) → ∀ δ k (u : Vec Z n) → col N p ≡ scV k (Vec.map ((√2ᶻ ^ᶻ δ) ZR.*_) u) →
             ∃ λ K → col N p ≡ scV K u
scale-down o zero k u eq = k , ≡.trans eq (≡.cong (scV k) (≡.trans (VecP.map-cong (λ y → ZR.*-identityˡ y) u) (VecP.map-id u)))
scale-down {N} o (suc δ) k u eq = go (scale-pos o k (Vec.map ((√2ᶻ ^ᶻ δ) ZR.*_) u) eq′)
  where
  eq′ : col N p ≡ scV k (Vec.map (√2ᶻ ZR.*_) (Vec.map ((√2ᶻ ^ᶻ δ) ZR.*_) u))
  eq′ = ≡.trans eq (≡.cong (scV k) (map-pow δ u))
  go : (∃ λ k′ → k ≡ suc k′) → ∃ λ K → col N p ≡ scV K u
  go (k′ , e) = scale-down o δ k′ u
    (≡.trans eq′ (≡.trans (≡.cong (λ K → scV K (Vec.map (√2ᶻ ZR.*_) (Vec.map ((√2ᶻ ^ᶻ δ) ZR.*_) u))) e)
                          (scV-δmap k′ (Vec.map ((√2ᶻ ^ᶻ δ) ZR.*_) u))))

------------------------------------------------------------------------
-- The two parities

-- Odd entries of class 1: evenly many.
even-cls : ∀ {N : Matrix n n D} → .(ColOrth N) → ∀ K (u : Vec Z n) → col N p ≡ scV K u →
           oddℕ (count (λ x → oddᶻ (u ! x) ∧ rbit (u ! x))) ≡ false
even-cls o K u eq = evenclass u (recompute (Σℤ (λ x → NB (u ! x)) ℤP.≟ + 0) (unit-normB K u (≡.subst (λ v → ⟨ v , v ⟩ ≡ DR.1#) eq (col-unit o p))))

-- Odd entries: evenly many, or exactly one.
even-odd : ∀ {N : Matrix n n D} → .(ColOrth N) → ∀ K (u : Vec Z n) → col N p ≡ scV K u →
           oddℕ (count (λ x → oddᶻ (u ! x))) ≡ false ⊎ count (λ x → oddᶻ (u ! x)) ≡ 1
even-odd o zero u eq = from (lde0 u (recompute (Σℕ (λ x → NA (u ! x)) ℕP.≟ 1) (unit-norm 0 u (≡.subst (λ v → ⟨ v , v ⟩ ≡ DR.1#) eq (col-unit o p)))))
  where
  one : ∀ {z} → z ≡ ZR.1# ⊎ z ≡ ZR.- ZR.1# → oddᶻ z ≡ true
  one (inj₁ ≡.refl) = ≡.refl
  one (inj₂ ≡.refl) = ≡.refl
  from : (∃ λ m → (u ! m ≡ ZR.1# ⊎ u ! m ≡ ZR.- ZR.1#) × (∀ y → y ≢ m → u ! y ≡ ZR.0#)) →
         oddℕ (count (λ x → oddᶻ (u ! x))) ≡ false ⊎ count (λ x → oddᶻ (u ! x)) ≡ 1
  from (m , pm , rest) = inj₂ (count-one (λ x → oddᶻ (u ! x)) m (one pm) (λ y y≢m → ≡.cong oddᶻ (rest y y≢m)))
even-odd o (suc K) u eq = inj₁ (evenodd K u (recompute (Σℕ (λ x → NA (u ! x)) ℕP.≟ 2 ℕ.^ suc K) (unit-norm (suc K) u (≡.subst (λ v → ⟨ v , v ⟩ ≡ DR.1#) eq (col-unit o p)))))

------------------------------------------------------------------------
-- An entry outside the window

-- The kinds of odd entries counted: all, of class 1, of class 0.
Pκ : Maybe Bool → Z → Bool
Pκ nothing z = oddᶻ z
Pκ (just true) z = oddᶻ z ∧ rbit z
Pκ (just false) z = oddᶻ z ∧ not (rbit z)

private
  Pκ-0 : ∀ κ → Pκ κ ZR.0# ≡ false
  Pκ-0 nothing = ≡.refl
  Pκ-0 (just true) = ≡.refl
  Pκ-0 (just false) = ≡.refl

  ≤-count : ∀ a b → 2 ℕ.≤ a → a ℕ.+ b ≡ 1 → ⊥
  ≤-count (suc zero) b (ℕ.s≤s ()) _
  ≤-count (suc (suc a)) b _ ()

  xor-l : ∀ a b → a xor b ≡ false → a ≡ false → b ≡ false
  xor-l false b e _ = e

  xor-ff : ∀ {a b} → a ≡ false → b ≡ false → a Data.Bool.Base.xor b ≡ false
  xor-ff ≡.refl ≡.refl = ≡.refl

  parity-rest : ∀ a b → oddℕ (a ℕ.+ b) ≡ false → oddℕ a ≡ true → oddℕ b ≡ true
  parity-rest a b e o with oddℕ b in ob
  ... | true = ≡.refl
  ... | false = ⊥-elim (t≢f (≡.trans (≡.sym (≡.trans (oddℕ-+ a b) (≡.cong₂ _xor_ o ob))) e))

  odd-pos : ∀ c → oddℕ c ≡ true → 0 ℕ.< c
  odd-pos (suc c) _ = ℕ.s≤s ℕ.z≤n

module Extra {m : ℕ} (ι : Fin m → Fin n) (inj : ∀ {i j} → ι i ≡ ι j → i ≡ j) where

  open Emb ι inj using (emb ; emb-ι ; emb-o ; where?)

  -- Quotients outside the window.
  private
    quot : ∀ δ (W₀ : Vec Z n) → (∀ x → (∀ i → ι i ≢ x) → ∃ λ y → W₀ ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y) →
           ∀ x → (∃ λ i → ι i ≡ x) ⊎ (∀ i → ι i ≢ x) → Z
    quot δ W₀ div x (inj₁ _) = ZR.0#
    quot δ W₀ div x (inj₂ o) = proj₁ (div x o)

    quot-eq : ∀ δ W₀ div x (o : ∀ i → ι i ≢ x) (w : (∃ λ i → ι i ≡ x) ⊎ (∀ i → ι i ≢ x)) →
              W₀ ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* quot δ W₀ div x w
    quot-eq δ W₀ div x o (inj₁ (i , e)) = ⊥-elim (o i e)
    quot-eq δ W₀ div x o (inj₂ o′) = proj₂ (div x o′)

  -- If the local quotients count an odd number of the kind, and at
  -- least two odd ones, an entry of that kind lies outside the window.
  extra : ∀ {N : Matrix n n D} → .(ColOrth N) → ∀ k (e : Vec Z m) (W₀ : Vec Z n) → col N p ≡ scV k (emb e W₀) →
          ∀ δ (g : Vec Z m) → (∀ i → e ! i ≡ (√2ᶻ ^ᶻ δ) ZR.* (g ! i)) →
          (∀ x → (∀ i → ι i ≢ x) → ∃ λ y → W₀ ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y) →
          2 ℕ.≤ countV oddᶻ g → ∀ κ → oddℕ (countV (Pκ κ) g) ≡ true →
          ∃ λ x → (∀ i → ι i ≢ x) × ∃ λ y → W₀ ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y × Pκ κ y ≡ true
  extra {N} o k e W₀ col≡ δ g eg div two κ oddκ = found (count-exists Pout (odd-pos _ outside-odd))
    where
    Ŵ : Vec Z n
    Ŵ = tabulate (λ x → quot δ W₀ div x (where? x))
    w̃ : Vec Z n
    w̃ = emb g Ŵ
    zeros : Vec Z m
    zeros = Vec.replicate m ZR.0#
    Pout : Fin n → Bool
    Pout x = Pκ κ (emb zeros Ŵ ! x)
    -- The column is w̃ at a lower scale.
    scaled : emb e W₀ ≡ Vec.map ((√2ᶻ ^ᶻ δ) ZR.*_) w̃
    scaled = vec-ext λ x → at x (where? x)
      where
      at : ∀ x → (∃ λ i → ι i ≡ x) ⊎ (∀ i → ι i ≢ x) → emb e W₀ ! x ≡ Vec.map ((√2ᶻ ^ᶻ δ) ZR.*_) w̃ ! x
      at x (inj₁ (i , ≡.refl)) =
        ≡.trans (emb-ι e W₀ i) (≡.trans (eg i) (≡.sym (≡.trans (VecP.lookup-map (ι i) _ w̃) (≡.cong ((√2ᶻ ^ᶻ δ) ZR.*_) (emb-ι g Ŵ i)))))
      at x (inj₂ out) =
        ≡.trans (emb-o e W₀ out)
          (≡.trans (quot-eq δ W₀ div x out (where? x))
            (≡.sym (≡.trans (VecP.lookup-map x _ w̃)
                     (≡.cong ((√2ᶻ ^ᶻ δ) ZR.*_) (≡.trans (emb-o g Ŵ out) (VecP.lookup∘tabulate (λ x → quot δ W₀ div x (where? x)) x))))))
    low : ∃ λ K → col N p ≡ scV K w̃
    low = scale-down o δ k w̃ (≡.trans col≡ (≡.cong (scV k) scaled))
    K = proj₁ low
    colK = proj₂ low
    -- Counts over w̃: the window's, then the outside's.
    splitP : ∀ P → P ZR.0# ≡ false → count (λ x → P (w̃ ! x)) ≡ countV P g ℕ.+ count (λ x → P (emb zeros Ŵ ! x))
    splitP P P0 = count-embP ι inj P P0 g Ŵ
    two-total : 2 ℕ.≤ count (λ x → oddᶻ (w̃ ! x))
    two-total = ℕP.≤-trans two (≡.subst (countV oddᶻ g ℕ.≤_) (≡.sym (splitP oddᶻ ≡.refl)) (ℕP.m≤m+n _ _))
    odd-even : oddℕ (count (λ x → oddᶻ (w̃ ! x))) ≡ false
    odd-even with even-odd o K w̃ colK
    ... | inj₁ ev = ev
    ... | inj₂ one = ⊥-elim (≤-count _ 0 two-total (≡.trans (ℕP.+-identityʳ _) one))
    total-even : oddℕ (count (λ x → Pκ κ (w̃ ! x))) ≡ false
    total-even = at κ
      where
      at : ∀ κ → oddℕ (count (λ x → Pκ κ (w̃ ! x))) ≡ false
      at nothing = odd-even
      at (just true) = even-cls o K w̃ colK
      at (just false) =
        xor-l (oddℕ c₁) (oddℕ c₀)
          (≡.trans (≡.sym (oddℕ-+ c₁ c₀)) (≡.trans (≡.cong oddℕ (≡.sym (count-split (λ x → oddᶻ (w̃ ! x)) (λ x → rbit (w̃ ! x))))) odd-even))
          (even-cls o K w̃ colK)
        where
        c₁ = count (λ x → oddᶻ (w̃ ! x) ∧ rbit (w̃ ! x))
        c₀ = count (λ x → oddᶻ (w̃ ! x) ∧ not (rbit (w̃ ! x)))
    outside-odd : oddℕ (count Pout) ≡ true
    outside-odd = parity-rest (countV (Pκ κ) g) (count Pout) (≡.trans (≡.cong oddℕ (≡.sym (splitP (Pκ κ) (Pκ-0 κ)))) total-even) oddκ
    found : (∃ λ x → Pout x ≡ true) → ∃ λ x → (∀ i → ι i ≢ x) × ∃ λ y → W₀ ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y × Pκ κ y ≡ true
    found (x , px) = at (where? x)
      where
      at : (∃ λ i → ι i ≡ x) ⊎ (∀ i → ι i ≢ x) → ∃ λ x → (∀ i → ι i ≢ x) × ∃ λ y → W₀ ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y × Pκ κ y ≡ true
      at (inj₁ (i , ≡.refl)) =
        ⊥-elim (t≢f (≡.trans (≡.sym px) (≡.trans (≡.cong (Pκ κ) (≡.trans (emb-ι zeros Ŵ i) (VecP.lookup-replicate i ZR.0#))) (Pκ-0 κ))))
      at (inj₂ out) =
        x , out , Ŵ ! x , ≡.trans (quot-eq δ W₀ div x out (where? x)) (≡.cong ((√2ᶻ ^ᶻ δ) ZR.*_) (≡.sym (VecP.lookup∘tabulate _ x))) ,
        ≡.trans (≡.cong (Pκ κ) (≡.sym (emb-o zeros Ŵ out))) px
