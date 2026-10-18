------------------------------------------------------------------------
-- Presentations of groups
--
-- Spans of bit vectors.
--
-- `comb vs as` is the sum of the vectors vs that the coefficients as
-- select.  A list is independent when only the zero coefficients give 0
-- (`Indep`).  Membership in a span is decided by trying every
-- coefficient vector (`span?`), so a list can be extended greedily by
-- the candidates outside its span, staying independent (`greedy`), and
-- four independent vectors never lie in the span of three
-- (`four-in-three`, from the same fact about coefficient vectors in
-- 𝔽₂³, decided).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Span where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_ ; _∧_ ; T ; not)
open import Data.Bool.Properties as BoolP using (xor-identityʳ ; xor-same ; xor-assoc ; xor-comm)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Properties using (all?)
open import Data.List.Base as List using (List ; [] ; _∷_ ; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any as Any using (Any ; here ; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ ; ++⁺ʳ ; map⁺)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; z≤n ; s≤s)
import Data.Nat.Base
import Data.Nat.Properties
open import Data.Product.Base using (Σ ; ∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; replicate ; _++_)
import Data.Vec.Base
import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (map′ ; from-yes)

import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute using (_⊕_ ; unit)
open import Notations using (₄₊)

private
  variable
    n k : ℕ

------------------------------------------------------------------------
-- Linear combinations

-- b times a vector.
scale : Bool → State n → State n
scale b x i = b ∧ x i

comb : Vec (State n) k → Vec Bool k → State n
comb []       []       = zeros
comb (v ∷ vs) (a ∷ as) = scale a v ⊕ comb vs as

Indep : Vec (State n) k → Set
Indep {k = k} vs = ∀ as → comb vs as ≈s zeros → as ≡ replicate k false

InSpan : Vec (State n) k → State n → Set
InSpan {k = k} vs x = Σ (Vec Bool k) λ as → comb vs as ≈s x

------------------------------------------------------------------------
-- Deciding

-- Every coefficient vector.
allVecs : ∀ k → List (Vec Bool k)
allVecs zero    = [] ∷ []
allVecs (suc k) = map (false ∷_) (allVecs k) List.++ map (true ∷_) (allVecs k)

allVecs-complete : (as : Vec Bool k) → as ∈ allVecs k
allVecs-complete []           = here refl
allVecs-complete (false ∷ as) = ++⁺ˡ (map⁺ (Any.map (cong (false ∷_)) (allVecs-complete as)))
allVecs-complete {suc k} (true ∷ as) =
  ++⁺ʳ (map (false ∷_) (allVecs k)) (map⁺ (Any.map (cong (true ∷_)) (allVecs-complete as)))

private
  bool? : (a b : Bool) → Dec (a ≡ b)
  bool? = BoolP._≟_

≈s? : (x y : State n) → Dec (x ≈s y)
≈s? x y = all? (λ i → bool? (x i) (y i))

span? : (vs : Vec (State n) k) (x : State n) → Dec (InSpan vs x)
span? {k = k} vs x = from (Any.any? (λ as → ≈s? (comb vs as) x) (allVecs k))
  where
  from : Dec (Any (λ as → comb vs as ≈s x) (allVecs k)) → Dec (InSpan vs x)
  from (yes a) = yes (wit a)
    where
    wit : ∀ {l} → Any (λ as → comb vs as ≈s x) l → InSpan vs x
    wit (here p)  = _ , p
    wit (there a) = wit a
  from (no ¬a) = no λ { (as , p) → ¬a (Any.map (λ { refl → p }) (allVecs-complete as)) }

------------------------------------------------------------------------
-- Linearity in the coefficients

infixl 6 _⊕ᵥ_
_⊕ᵥ_ : Vec Bool k → Vec Bool k → Vec Bool k
[]       ⊕ᵥ []       = []
(a ∷ as) ⊕ᵥ (b ∷ bs) = (a xor b) ∷ (as ⊕ᵥ bs)

scaleᵥ : Bool → Vec Bool k → Vec Bool k
scaleᵥ {k} false c = replicate k false
scaleᵥ     true  c = c

private
  ∧-xor : ∀ a b c → (a xor b) ∧ c ≡ (a ∧ c) xor (b ∧ c)
  ∧-xor false b c = refl
  ∧-xor true false c = sym (xor-identityʳ c)
  ∧-xor true true c = sym (xor-same c)

  ichg : ∀ a b c d → (a xor b) xor (c xor d) ≡ (a xor c) xor (b xor d)
  ichg a b c d =
    trans (xor-assoc a b (c xor d))
    (trans (cong (a xor_) (trans (sym (xor-assoc b c d))
              (trans (cong (_xor d) (xor-comm b c)) (xor-assoc c b d))))
      (sym (xor-assoc a c (b xor d))))

comb-⊕ : (vs : Vec (State n) k) (as bs : Vec Bool k) →
  comb vs (as ⊕ᵥ bs) ≈s comb vs as ⊕ comb vs bs
comb-⊕ []       []       []       i = refl
comb-⊕ (v ∷ vs) (a ∷ as) (b ∷ bs) i =
  trans (cong₂ _xor_ (∧-xor a b (v i)) (comb-⊕ vs as bs i))
    (ichg (a ∧ v i) (b ∧ v i) (comb vs as i) (comb vs bs i))

comb-zero : (vs : Vec (State n) k) → comb vs (replicate k false) ≈s zeros
comb-zero []       i = refl
comb-zero (v ∷ vs) i = comb-zero vs i

comb-scale : (vs : Vec (State n) k) (a : Bool) (c : Vec Bool k) →
  comb vs (scaleᵥ a c) ≈s scale a (comb vs c)
comb-scale vs false c = comb-zero vs
comb-scale vs true  c i = refl

------------------------------------------------------------------------
-- Extending an independent list

private
  xor-false : ∀ {a b} → a xor b ≡ false → a ≡ b
  xor-false {false} {false} e = refl
  xor-false {true}  {true}  e = refl
  xor-false {false} {true}  ()
  xor-false {true}  {false} ()

indep-extend : {vs : Vec (State n) k} {x : State n} → Indep vs → ¬ InSpan vs x → Indep (x ∷ vs)
indep-extend ind out (false ∷ as) z = cong (false ∷_) (ind as z)
indep-extend ind out (true ∷ as) z = ⊥-elim (out (as , λ i → sym (xor-false (z i))))

-- A vector in the span stays there when the list grows in front.
span-grow : ∀ {j k} (us : Vec (State n) j) {vs : Vec (State n) k} {x : State n} →
  InSpan vs x → InSpan (us ++ vs) x
span-grow []       p = p
span-grow (u ∷ us) p = (false ∷ proj₁ (span-grow us p)) , proj₂ (span-grow us p)

------------------------------------------------------------------------
-- Four vectors are never in the span of three

-- A combination of coefficient vectors.
cmix : ∀ {m} → Vec (Vec Bool k) m → Vec Bool m → Vec Bool k
cmix {k} []       []       = replicate k false
cmix     (c ∷ cs) (a ∷ as) = scaleᵥ a c ⊕ᵥ cmix cs as

comb-mix : ∀ {m} (S : Vec (State n) k) (us : Vec (State n) m) (cs : Vec (Vec Bool k) m) →
  (∀ i → comb S (Data.Vec.Base.lookup cs i) ≈s Data.Vec.Base.lookup us i) →
  ∀ as → comb us as ≈s comb S (cmix cs as)
comb-mix S []       []       e []       i = sym (comb-zero S i)
comb-mix S (u ∷ us) (c ∷ cs) e (a ∷ as) i =
  trans (cong₂ _xor_ (cong (a ∧_) (sym (e zero i))) (comb-mix S us cs (λ j → e (suc j)) as i))
    (trans (cong (_xor comb S (cmix cs as) i) (sym (comb-scale S a c i)))
      (sym (comb-⊕ S (scaleᵥ a c) (cmix cs as) i)))

private
  -- Boolean tests, so that the check below is a closed Boolean.
  isZeroV : Vec Bool k → Bool
  isZeroV []       = true
  isZeroV (a ∷ as) = not a ∧ isZeroV as

  isZeroV-sound : (as : Vec Bool k) → isZeroV as ≡ true → as ≡ replicate k false
  isZeroV-sound []           e = refl
  isZeroV-sound (false ∷ as) e = cong (false ∷_) (isZeroV-sound as e)
  isZeroV-sound (true ∷ as)  ()

  isZeroV-complete : (as : Vec Bool k) → as ≡ replicate k false → isZeroV as ≡ true
  isZeroV-complete [] e = refl
  isZeroV-complete (false ∷ as) refl = isZeroV-complete as refl

  good : Vec (Vec Bool 3) 4 → Vec Bool 4 → Bool
  good cs as = not (isZeroV as) ∧ isZeroV (cmix cs as)

  first : Vec (Vec Bool 3) 4 → List (Vec Bool 4) → Bool
  first cs []        = false
  first cs (as ∷ l)  = good cs as Data.Bool.Base.∨ first cs l

  -- Every four coefficient vectors, as twelve bits.
  split12 : Vec Bool 12 → Vec (Vec Bool 3) 4
  split12 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ []) =
    (a ∷ b ∷ c ∷ []) ∷ (d ∷ e ∷ f ∷ []) ∷ (g ∷ h ∷ i ∷ []) ∷ (j ∷ k ∷ l ∷ []) ∷ []

  join12 : Vec (Vec Bool 3) 4 → Vec Bool 12
  join12 ((a ∷ b ∷ c ∷ []) ∷ (d ∷ e ∷ f ∷ []) ∷ (g ∷ h ∷ i ∷ []) ∷ (j ∷ k ∷ l ∷ []) ∷ []) =
    a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷ k ∷ l ∷ []

  split-join : (cs : Vec (Vec Bool 3) 4) → split12 (join12 cs) ≡ cs
  split-join ((a ∷ b ∷ c ∷ []) ∷ (d ∷ e ∷ f ∷ []) ∷ (g ∷ h ∷ i ∷ []) ∷ (j ∷ k ∷ l ∷ []) ∷ []) = refl

  checkAll : List (Vec Bool 12) → Bool
  checkAll []      = true
  checkAll (b ∷ l) = first (split12 b) (allVecs 4) ∧ checkAll l

  checked : checkAll (allVecs 12) ≡ true
  checked = refl

  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true} e = refl

  ∧-r : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧-r {true} e = e

  ∨-split : ∀ {a b} → a Data.Bool.Base.∨ b ≡ true → (a ≡ true) ⊎ (b ≡ true)
  ∨-split {true}  e = inj₁ refl
  ∨-split {false} e = inj₂ e

  check-∈ : ∀ {b l} → b ∈ l → checkAll l ≡ true → first (split12 b) (allVecs 4) ≡ true
  check-∈ (here refl) e = ∧-l e
  check-∈ {l = c ∷ l} (there m) e = check-∈ m (∧-r {first (split12 c) (allVecs 4)} e)

  first-sound : ∀ cs l → first cs l ≡ true → Σ (Vec Bool 4) λ as → good cs as ≡ true
  first-sound cs (as ∷ l) e with ∨-split {good cs as} e
  ... | inj₁ g = as , g
  ... | inj₂ r = first-sound cs l r

-- Four coefficient vectors in 𝔽₂³ are dependent.
dep3 : (cs : Vec (Vec Bool 3) 4) → Σ (Vec Bool 4) λ as →
  ¬ (as ≡ replicate 4 false) × cmix cs as ≡ replicate 3 false
dep3 cs = as , nz , isZeroV-sound (cmix cs as) (∧-r {not (isZeroV as)} g)
  where
  w = first-sound (split12 (join12 cs)) (allVecs 4)
        (check-∈ (allVecs-complete (join12 cs)) checked)
  as = proj₁ w
  g : good cs as ≡ true
  g = subst (λ c → good c as ≡ true) (split-join cs) (proj₂ w)
  nz : ¬ (as ≡ replicate 4 false)
  nz z with trans (sym (cong not (isZeroV-complete as z))) (∧-l g)
  ... | ()

------------------------------------------------------------------------
-- Four independent vectors are not in the span of three

four-in-three : (S : Vec (State n) 3) (us : Vec (State n) 4) → Indep us →
  (∀ i → InSpan S (Data.Vec.Base.lookup us i)) → ⊥
four-in-three S us ind sp = nz (ind as zero-comb)
  where
  cs : Vec (Vec Bool 3) 4
  cs = Data.Vec.Base.tabulate (λ i → proj₁ (sp i))
  w = dep3 cs
  as = proj₁ w
  nz = proj₁ (proj₂ w)
  zero-comb : comb us as ≈s zeros
  zero-comb i =
    trans (comb-mix S us cs
             (λ j → subst (λ c → comb S c ≈s Data.Vec.Base.lookup us j)
                      (sym (Data.Vec.Properties.lookup∘tabulate (λ i → proj₁ (sp i)) j))
                      (proj₂ (sp j))) as i)
      (trans (cong (λ c → comb S c i) (proj₂ (proj₂ w))) (comb-zero S i))

private
  -- Padding a list of at most three vectors with zeros in front.
  pad3 : ∀ {k} → k Data.Nat.Base.≤ 3 → Vec (State n) k → Vec (State n) 3
  pad3 z≤n                         []           = zeros ∷ zeros ∷ zeros ∷ []
  pad3 (s≤s z≤n)                   (a ∷ [])     = zeros ∷ zeros ∷ a ∷ []
  pad3 (s≤s (s≤s z≤n))             (a ∷ b ∷ []) = zeros ∷ a ∷ b ∷ []
  pad3 (s≤s (s≤s (s≤s z≤n)))       v            = v

  pad3-span : ∀ {k} (le : k Data.Nat.Base.≤ 3) (v : Vec (State n) k) {x : State n} →
    InSpan v x → InSpan (pad3 le v) x
  pad3-span z≤n                   []           p = span-grow (zeros ∷ zeros ∷ zeros ∷ []) p
  pad3-span (s≤s z≤n)             (a ∷ [])     p = span-grow (zeros ∷ zeros ∷ []) p
  pad3-span (s≤s (s≤s z≤n))       (a ∷ b ∷ []) p = span-grow (zeros ∷ []) p
  pad3-span (s≤s (s≤s (s≤s z≤n))) v            p = p

------------------------------------------------------------------------
-- Completing a list by unit vectors on the bottom four wires

e4 : ∀ {m} → Fin 4 → State (₄₊ m)
e4 zero                      = unit zero
e4 (suc zero)                = unit (suc zero)
e4 (suc (suc zero))          = unit (suc (suc zero))
e4 (suc (suc (suc zero)))    = unit (suc (suc (suc zero)))

E4 : ∀ {m} → Vec (State (₄₊ m)) 4
E4 = e4 zero ∷ e4 (suc zero) ∷ e4 (suc (suc zero)) ∷ e4 (suc (suc (suc zero))) ∷ []

E4-indep : ∀ {m} → Indep (E4 {m})
E4-indep (false ∷ false ∷ false ∷ false ∷ []) z = refl
E4-indep (false ∷ false ∷ false ∷ true ∷ []) z with z (suc (suc (suc zero)))
... | ()
E4-indep (false ∷ false ∷ true ∷ false ∷ []) z with z (suc (suc zero))
... | ()
E4-indep (false ∷ false ∷ true ∷ true ∷ []) z with z (suc (suc zero))
... | ()
E4-indep (false ∷ true ∷ false ∷ false ∷ []) z with z (suc zero)
... | ()
E4-indep (false ∷ true ∷ false ∷ true ∷ []) z with z (suc zero)
... | ()
E4-indep (false ∷ true ∷ true ∷ false ∷ []) z with z (suc zero)
... | ()
E4-indep (false ∷ true ∷ true ∷ true ∷ []) z with z (suc zero)
... | ()
E4-indep (true ∷ false ∷ false ∷ false ∷ []) z with z zero
... | ()
E4-indep (true ∷ false ∷ false ∷ true ∷ []) z with z zero
... | ()
E4-indep (true ∷ false ∷ true ∷ false ∷ []) z with z zero
... | ()
E4-indep (true ∷ false ∷ true ∷ true ∷ []) z with z zero
... | ()
E4-indep (true ∷ true ∷ false ∷ false ∷ []) z with z zero
... | ()
E4-indep (true ∷ true ∷ false ∷ true ∷ []) z with z zero
... | ()
E4-indep (true ∷ true ∷ true ∷ false ∷ []) z with z zero
... | ()
E4-indep (true ∷ true ∷ true ∷ true ∷ []) z with z zero
... | ()

-- The completion: unit vectors F in front of D.
record Fill {m d : ℕ} (D : Vec (State (₄₊ m)) d) : Set where
  constructor fill
  field
    j     : ℕ
    F     : Vec (Fin 4) j
    indep : Indep (Data.Vec.Base.map e4 F ++ D)
    bound : j + d Data.Nat.Base.≤ 4

Full : ∀ {m d} {D : Vec (State (₄₊ m)) d} → Fill D → Set
Full {d = d} s = Fill.j s + d ≡ 4

Covers : ∀ {m d} {D : Vec (State (₄₊ m)) d} → Fill D → State (₄₊ m) → Set
Covers {D = D} s x = Full s ⊎ InSpan (Data.Vec.Base.map e4 (Fill.F s) ++ D) x

private
  self-span : (x : State n) (vs : Vec (State n) k) → InSpan (x ∷ vs) x
  self-span {k = k} x vs = (true ∷ replicate k false) ,
    λ i → trans (cong ((true ∧ x i) xor_) (comb-zero vs i)) (xor-identityʳ (x i))

  step : ∀ {m d} {D : Vec (State (₄₊ m)) d} → Fin 4 → Fill D → Fill D
  step {d = d} {D} p (fill j F ind bd) with j + d Data.Nat.Properties.≟ 4
  ... | yes _ = fill j F ind bd
  ... | no ne with span? (Data.Vec.Base.map e4 F ++ D) (e4 p)
  ...   | yes _   = fill j F ind bd
  ...   | no  out = fill (suc j) (p ∷ F) (indep-extend ind out)
                      (Data.Nat.Properties.≤∧≢⇒< bd ne)

  step-p : ∀ {m d} {D : Vec (State (₄₊ m)) d} (p : Fin 4) (s : Fill D) → Covers (step p s) (e4 p)
  step-p {d = d} {D} p (fill j F ind bd) with j + d Data.Nat.Properties.≟ 4
  ... | yes f = inj₁ f
  ... | no ne with span? (Data.Vec.Base.map e4 F ++ D) (e4 p)
  ...   | yes sp  = inj₂ sp
  ...   | no  out = inj₂ (self-span (e4 p) (Data.Vec.Base.map e4 F ++ D))

  step-mono : ∀ {m d} {D : Vec (State (₄₊ m)) d} (p : Fin 4) (s : Fill D) {x : State (₄₊ m)} →
    Covers s x → Covers (step p s) x
  step-mono {d = d} {D} p (fill j F ind bd) c with j + d Data.Nat.Properties.≟ 4
  ... | yes f = c
  ... | no ne with span? (Data.Vec.Base.map e4 F ++ D) (e4 p)
  ...   | yes sp  = c
  ...   | no  out with c
  ...     | inj₁ f  = ⊥-elim (ne f)
  ...     | inj₂ sp = inj₂ (span-grow (e4 p ∷ []) sp)

  lookup-E4 : ∀ {m} (i : Fin 4) → Data.Vec.Base.lookup (E4 {m}) i ≡ e4 i
  lookup-E4 zero                   = refl
  lookup-E4 (suc zero)             = refl
  lookup-E4 (suc (suc zero))       = refl
  lookup-E4 (suc (suc (suc zero))) = refl

-- An independent list of at most four vectors, completed to four by
-- unit vectors on the bottom four wires.
complete4 : ∀ {m d} (D : Vec (State (₄₊ m)) d) → Indep D → d Data.Nat.Base.≤ 4 →
  Σ (Fill D) Full
complete4 {m} {d} D ind le = s₄ , full₄
  where
  s₀ = fill 0 [] ind le
  s₁ = step zero s₀
  s₂ = step (suc zero) s₁
  s₃ = step (suc (suc zero)) s₂
  s₄ = step (suc (suc (suc zero))) s₃
  cov : ∀ p → Covers s₄ (e4 p)
  cov zero = step-mono _ s₃ (step-mono _ s₂ (step-mono _ s₁ (step-p zero s₀)))
  cov (suc zero) = step-mono _ s₃ (step-mono _ s₂ (step-p (suc zero) s₁))
  cov (suc (suc zero)) = step-mono _ s₃ (step-p (suc (suc zero)) s₂)
  cov (suc (suc (suc zero))) = step-p (suc (suc (suc zero))) s₃
  L = Data.Vec.Base.map e4 (Fill.F s₄) ++ D
  full₄ : Full s₄
  full₄ with Fill.j s₄ + d Data.Nat.Properties.≟ 4
  ... | yes f = f
  ... | no ne = ⊥-elim (four-in-three (pad3 le3 L) E4 E4-indep
                   (λ i → pad3-span le3 L (span-of i)))
    where
    le3 : Fill.j s₄ + d Data.Nat.Base.≤ 3
    le3 = Data.Nat.Properties.≤-pred (Data.Nat.Properties.≤∧≢⇒< (Fill.bound s₄) ne)
    span-of : ∀ i → InSpan L (Data.Vec.Base.lookup E4 i)
    span-of i with cov i
    ... | inj₁ f  = ⊥-elim (ne f)
    ... | inj₂ sp = subst (InSpan L) (sym (lookup-E4 i)) sp
