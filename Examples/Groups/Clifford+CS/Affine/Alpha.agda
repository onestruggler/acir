------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding's affine circuits, and their equivariance
--
-- α p q = xs p • L (p ⊕ q) sends the basis state 0 to p and e₀ to q:
-- `xs p` is X on the bits of p.  A letter a — X on a wire, or CX —
-- passes α as its bit map â says: a • α p q ≈ α (â p) (â q) • h with h
-- a word of CX whose controls are off wire 0 (`eqv-α`).  For X, h is ε
-- (the X's commute and p ⊕ q is unchanged); for CX, the X's pass it
-- with the X on its control leaving an X on its target, and Equivariance
-- does the linear part.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Affine.Alpha (n : ℕ) where

open import Data.Bool using (Bool ; true ; false ; not ; if_then_else_ ; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Properties using (_≟_)
open import Data.Product using (Σ ; _×_ ; _,_)
open import Data.Unit using (tt)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford+CS.Affine.Theory n
open import Examples.Groups.Clifford+CS.Affine.Equivariance n

private
  variable
    k : ℕ

  t≢f : true ≢ false
  t≢f ()

------------------------------------------------------------------------
-- Bit vectors

_⊕_ : Vec Bool k → Vec Bool k → Vec Bool k
_⊕_ = zipWith _xor_

toggle-invol : ∀ (p : Vec Bool k) i → toggle (toggle p i) i ≡ p
toggle-invol (true  ∷ p) 0F     = Eq.refl
toggle-invol (false ∷ p) 0F     = Eq.refl
toggle-invol (b ∷ p)     (sF i) = Eq.cong (b ∷_) (toggle-invol p i)

toggle-comm : ∀ (p : Vec Bool k) i j → toggle (toggle p i) j ≡ toggle (toggle p j) i
toggle-comm (b ∷ p) 0F     0F     = Eq.refl
toggle-comm (b ∷ p) 0F     (sF j) = Eq.refl
toggle-comm (b ∷ p) (sF i) 0F     = Eq.refl
toggle-comm (b ∷ p) (sF i) (sF j) = Eq.cong (b ∷_) (toggle-comm p i j)

private
  not-xorˡ : ∀ a b → (not a xor b) ≡ not (a xor b)
  not-xorˡ true  true  = Eq.refl
  not-xorˡ true  false = Eq.refl
  not-xorˡ false true  = Eq.refl
  not-xorˡ false false = Eq.refl

  not-xorʳ : ∀ a b → (a xor not b) ≡ not (a xor b)
  not-xorʳ true  true  = Eq.refl
  not-xorʳ true  false = Eq.refl
  not-xorʳ false true  = Eq.refl
  not-xorʳ false false = Eq.refl

  not-not-xor : ∀ a b → (not a xor not b) ≡ (a xor b)
  not-not-xor true  true  = Eq.refl
  not-not-xor true  false = Eq.refl
  not-not-xor false true  = Eq.refl
  not-not-xor false false = Eq.refl

toggle-⊕ˡ : ∀ (p q : Vec Bool k) i → (toggle p i ⊕ q) ≡ toggle (p ⊕ q) i
toggle-⊕ˡ (a ∷ p) (b ∷ q) 0F     = Eq.cong (_∷ (p ⊕ q)) (not-xorˡ a b)
toggle-⊕ˡ (a ∷ p) (b ∷ q) (sF i) = Eq.cong ((a xor b) ∷_) (toggle-⊕ˡ p q i)

toggle-⊕ʳ : ∀ (p q : Vec Bool k) i → (p ⊕ toggle q i) ≡ toggle (p ⊕ q) i
toggle-⊕ʳ (a ∷ p) (b ∷ q) 0F     = Eq.cong (_∷ (p ⊕ q)) (not-xorʳ a b)
toggle-⊕ʳ (a ∷ p) (b ∷ q) (sF i) = Eq.cong ((a xor b) ∷_) (toggle-⊕ʳ p q i)

toggle-⊕ : ∀ (p q : Vec Bool k) i → (toggle p i ⊕ toggle q i) ≡ (p ⊕ q)
toggle-⊕ (a ∷ p) (b ∷ q) 0F     = Eq.cong (_∷ (p ⊕ q)) (not-not-xor a b)
toggle-⊕ (a ∷ p) (b ∷ q) (sF i) = Eq.cong ((a xor b) ∷_) (toggle-⊕ p q i)

lookup-⊕ : ∀ (p q : Vec Bool k) i → lookup (p ⊕ q) i ≡ (lookup p i xor lookup q i)
lookup-⊕ (a ∷ p) (b ∷ q) 0F     = Eq.refl
lookup-⊕ (a ∷ p) (b ∷ q) (sF i) = lookup-⊕ p q i

-- The bit map of CX is linear.
tmap-⊕ : ∀ (u v : Wire) (p q : Vec Bool (₁₊ n)) → (tmap u v p ⊕ tmap u v q) ≡ tmap u v (p ⊕ q)
tmap-⊕ u v p q =
  Eq.trans (fin (lookup p u) (lookup q u))
           (Eq.cong (λ c → if c then toggle (p ⊕ q) v else (p ⊕ q)) (Eq.sym (lookup-⊕ p q u)))
  where
  fin : ∀ a b → ((if a then toggle p v else p) ⊕ (if b then toggle q v else q))
              ≡ (if a xor b then toggle (p ⊕ q) v else (p ⊕ q))
  fin true  true  = toggle-⊕ p q v
  fin true  false = toggle-⊕ˡ p q v
  fin false true  = toggle-⊕ʳ p q v
  fin false false = Eq.refl

-- Distinct states differ somewhere.
nz-⊕ : ∀ (p q : Vec Bool k) → p ≢ q → NZ (p ⊕ q)
nz-⊕ []      []      ne = ⊥-elim (ne Eq.refl)
nz-⊕ (true  ∷ p) (false ∷ q) ne = 0F , Eq.refl
nz-⊕ (false ∷ p) (true  ∷ q) ne = 0F , Eq.refl
nz-⊕ (true  ∷ p) (true  ∷ q) ne with nz-⊕ p q (λ e → ne (Eq.cong (true ∷_) e))
... | i , e = sF i , e
nz-⊕ (false ∷ p) (false ∷ q) ne with nz-⊕ p q (λ e → ne (Eq.cong (false ∷_) e))
... | i , e = sF i , e

------------------------------------------------------------------------
-- Translations

xs : Vec Bool k → (Fin k → Wire) → Word Lt
xs []          ι = ε
xs (true  ∷ p) ι = X (ι 0F) • xs p (λ i → ι (sF i))
xs (false ∷ p) ι = xs p (λ i → ι (sF i))

-- X's commute.
x-pass : ∀ (a : Wire) (p : Vec Bool k) (ι : Fin k → Wire) → X a • xs p ι ≈ xs p ι • X a
x-pass a []          ι = trans right-unit (sym left-unit)
x-pass a (true  ∷ p) ι = begin
  X a • (X (ι 0F) • xs p ι′)   ≈⟨ trans (sym assoc) (trans (front _ (axiom x-xx)) assoc) ⟩
  X (ι 0F) • (X a • xs p ι′)   ≈⟨ back _ (x-pass a p ι′) ⟩
  X (ι 0F) • (xs p ι′ • X a)   ≈⟨ sym assoc ⟩
  (X (ι 0F) • xs p ι′) • X a ∎
  where ι′ = λ i → ι (sF i)
x-pass a (false ∷ p) ι = x-pass a p (λ i → ι (sF i))

-- X on a wire of the frame toggles its bit.
x-toggle : ∀ (p : Vec Bool k) (ι : Fin k → Wire) (j : Fin k) → X (ι j) • xs p ι ≈ xs (toggle p j) ι
x-toggle (true  ∷ p) ι 0F     = cancelˡ _ (axiom x-sq)
x-toggle (false ∷ p) ι 0F     = refl
x-toggle (true  ∷ p) ι (sF j) = begin
  X (ι (sF j)) • (X (ι 0F) • xs p ι′)   ≈⟨ trans (sym assoc) (trans (front _ (axiom x-xx)) assoc) ⟩
  X (ι 0F) • (X (ι′ j) • xs p ι′)       ≈⟨ back _ (x-toggle p ι′ j) ⟩
  X (ι 0F) • xs (toggle p j) ι′ ∎
  where ι′ = λ i → ι (sF i)
x-toggle (false ∷ p) ι (sF j) = x-toggle p (λ i → ι (sF i)) j

-- CX passes the X's off its control.
t-pass-x : ∀ (u v : Wire) .(r : u ≢ v) (p : Vec Bool k) (ι : Fin k → Wire) →
           (∀ i → lookup p i ≡ true → ι i ≢ u) → T u v r • xs p ι ≈ xs p ι • T u v r
t-pass-x u v r []          ι h = trans right-unit (sym left-unit)
t-pass-x u v r (true  ∷ p) ι h = begin
  T u v r • (X (ι 0F) • xs p ι′)   ≈⟨ trans (sym assoc) (trans (front _ (tx (ι 0F) (h 0F Eq.refl))) assoc) ⟩
  X (ι 0F) • (T u v r • xs p ι′)   ≈⟨ back _ (t-pass-x u v r p ι′ (λ i → h (sF i))) ⟩
  X (ι 0F) • (xs p ι′ • T u v r)   ≈⟨ sym assoc ⟩
  (X (ι 0F) • xs p ι′) • T u v r ∎
  where
  ι′ = λ i → ι (sF i)
  tx : ∀ (a : Wire) → a ≢ u → T u v r • X a ≈ X a • T u v r
  tx a au with a ≟ v
  ... | yes Eq.refl = axiom x-tgt
  ... | no av       = axiom (x-far au av)
t-pass-x u v r (false ∷ p) ι h = t-pass-x u v r p (λ i → ι (sF i)) (λ i → h (sF i))

private
  idʷ : Wire → Wire
  idʷ i = i

-- CX across the X's of p: the X on its control leaves an X on its target.
t-xs : ∀ (u v : Wire) .(r : u ≢ v) (p : Vec Bool (₁₊ n)) → T u v r • xs p idʷ ≈ xs (tmap u v p) idʷ • T u v r
t-xs u v r p = go (lookup p u) Eq.refl
  where
  go : ∀ b → lookup p u ≡ b → T u v r • xs p idʷ ≈ xs (if b then toggle p v else p) idʷ • T u v r
  go false e = t-pass-x u v r p idʷ off
    where
    off : ∀ i → lookup p i ≡ true → idʷ i ≢ u
    off i b Eq.refl = t≢f (Eq.trans (Eq.sym b) e)
  go true e = begin
    T u v r • xs p idʷ
      ≈⟨ back _ (≡≈ (Eq.cong (λ x → xs x idʷ) (Eq.sym (toggle-invol p u)))) ⟩
    T u v r • xs (toggle (toggle p u) u) idʷ
      ≈⟨ back _ (sym (x-toggle (toggle p u) idʷ u)) ⟩
    T u v r • X u • xs p° idʷ
      ≈⟨ trans (sym assoc) (trans (front _ (axiom x-ctl)) assoc) ⟩
    X u • (X v • T u v r) • xs p° idʷ
      ≈⟨ back _ (trans assoc (back _ (t-pass-x u v r p° idʷ off))) ⟩
    X u • X v • xs p° idʷ • T u v r
      ≈⟨ back _ (trans (sym assoc) (front _ (x-toggle p° idʷ v))) ⟩
    X u • xs (toggle p° v) idʷ • T u v r
      ≈⟨ trans (sym assoc) (front _ (x-toggle (toggle p° v) idʷ u)) ⟩
    xs (toggle (toggle p° v) u) idʷ • T u v r
      ≈⟨ front _ (≡≈ (Eq.cong (λ x → xs x idʷ) back-to)) ⟩
    xs (toggle p v) idʷ • T u v r ∎
    where
    p° = toggle p u
    off : ∀ i → lookup p° i ≡ true → idʷ i ≢ u
    off i b Eq.refl = t≢f (Eq.trans (Eq.sym b) (Eq.trans (lookup-toggle p u) (Eq.cong not e)))
    back-to : toggle (toggle p° v) u ≡ toggle p v
    back-to = Eq.trans (toggle-comm p° v u) (Eq.cong (λ x → toggle x v) (toggle-invol p u))

------------------------------------------------------------------------
-- The affine circuits, and how a letter passes them

α : Vec Bool (₁₊ n) → Vec Bool (₁₊ n) → Word Lt
α p q = xs p idʷ • L (p ⊕ q)

-- The bit map of a letter.
amap : Lt → Vec Bool (₁₊ n) → Vec Bool (₁₊ n)
amap (xL v)     p = toggle p v
amap (tL u v _) p = tmap u v p

eqv-α : ∀ (a : Lt) (p q : Vec Bool (₁₊ n)) → p ≢ q →
        Σ (Word Lt) λ h → Ctl h × ([ a ]ʷ • α p q ≈ α (amap a p) (amap a q) • h)
eqv-α (xL v) p q ne = ε , tt , (begin
  X v • xs p idʷ • L (p ⊕ q)
    ≈⟨ trans (sym assoc) (front _ (x-toggle p idʷ v)) ⟩
  xs (toggle p v) idʷ • L (p ⊕ q)
    ≈⟨ back _ (≡≈ (Eq.cong L (Eq.sym (toggle-⊕ p q v)))) ⟩
  xs (toggle p v) idʷ • L (toggle p v ⊕ toggle q v)
    ≈⟨ sym right-unit ⟩
  (xs (toggle p v) idʷ • L (toggle p v ⊕ toggle q v)) • ε ∎)
eqv-α (tL u v r) p q ne with eqvL u v r (p ⊕ q) (nz-⊕ p q ne)
... | pass h c e = h , c , (begin
  T u v r • xs p idʷ • L (p ⊕ q)
    ≈⟨ trans (sym assoc) (trans (front _ (t-xs u v r p)) assoc) ⟩
  xs (tmap u v p) idʷ • T u v r • L (p ⊕ q)
    ≈⟨ back _ e ⟩
  xs (tmap u v p) idʷ • L (tmap u v (p ⊕ q)) • h
    ≈⟨ back _ (front _ (≡≈ (Eq.cong L (Eq.sym (tmap-⊕ u v p q))))) ⟩
  xs (tmap u v p) idʷ • L (tmap u v p ⊕ tmap u v q) • h
    ≈⟨ sym assoc ⟩
  (xs (tmap u v p) idʷ • L (tmap u v p ⊕ tmap u v q)) • h ∎)
