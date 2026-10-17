------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical position of up to five basis states
--
-- Gaussian elimination as an affine word: the first state is translated
-- to 0, and each further state either lies in the span of the images so
-- far (it keeps its image, `old c` with c its coordinates) or gets the
-- next basis vector (`new`): its pivot — its first set bit at or above
-- the rank — is cleared from its other set bits by CX from the pivot
-- (`clr`), and exchanged with the rank's wire.  Neither moves a state
-- whose bits from the rank on are 0 (`Low`), so earlier images stay.
-- With at most five states the rank stays at most 4, so every image is
-- four bits followed by zeros, a function of the pattern alone (`imgs`).
-- scratchpad/five/patterns.py checks the elimination (elim_word).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Affine.Canon (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; not ; if_then_else_ ; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ ; fromℕ<) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Properties using (_≟_ ; toℕ-fromℕ< ; toℕ-injective)
open import Data.Nat using (zero ; suc ; _+_ ; _≤_ ; _<_ ; z≤n ; s≤s)
open import Data.Nat.Properties using (≤-trans ; ≤-refl ; n≤1+n ; +-suc ; <-irrefl ; +-monoʳ-≤ ; m≤m+n ; ≤-reflexive)
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
import Data.List as List
open List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup ; replicate ; _++_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Affine.Theory (₃₊ m)
open import Examples.Groups.Clifford+CS.Affine.Equivariance (₃₊ m) using (tmap)
open import Examples.Groups.Clifford+CS.Affine.Alpha (₃₊ m)
  using (amap ; amapʷ ; _⊕_ ; toggle-invol ; toggle-comm ; toggle-⊕ʳ ; lookup-⊕)

private
  variable
    k : ℕ

St : Set
St = Vec Bool (₄₊ m)

------------------------------------------------------------------------
-- Patterns and their images

data Pat : ℕ → ℕ → Set where
  done : ∀ {r} → Pat r 0
  new  : ∀ {r k} → Pat (suc r) k → Pat r (suc k)
  old  : ∀ {r k} → Vec Bool r → Pat r k → Pat r (suc k)

-- r bits, padded (or cut) to four.
ext : ∀ {r} → Vec Bool r → Vec Bool 4
ext c = go 4 c
  where
  go : ∀ {r} (j : ℕ) → Vec Bool r → Vec Bool j
  go zero    _       = []
  go (suc j) []      = false ∷ go j []
  go (suc j) (b ∷ c) = b ∷ go j c

-- The unit vector at rank r, r bits then a 1.
unitR : (r : ℕ) → Vec Bool (suc r)
unitR zero    = true ∷ []
unitR (suc r) = false ∷ unitR r

pad : Vec Bool 4 → St
pad c = c ++ replicate _ false

imgs : ∀ {r k} → Pat r k → Vec St k
imgs done        = []
imgs {r} (new p) = pad (ext (unitR r)) ∷ imgs p
imgs (old c p)   = pad (ext c) ∷ imgs p

------------------------------------------------------------------------
-- Low vectors: zero from the rank on

Low : ℕ → St → Set
Low r x = ∀ (i : Wire) → r ≤ toℕ i → lookup x i ≡ false

-- The first r bits.
firstR : (r : ℕ) → ∀ {j} → Vec Bool j → Vec Bool r
firstR zero    _       = []
firstR (suc r) []      = false ∷ firstR r []
firstR (suc r) (b ∷ x) = b ∷ firstR r x

------------------------------------------------------------------------
-- Vectors from their bits

zeros : ∀ {j} → Vec Bool j
zeros = replicate _ false

all-false : ∀ {j} (v : Vec Bool j) → (∀ i → lookup v i ≡ false) → v ≡ zeros
all-false []      h = Eq.refl
all-false (b ∷ v) h = Eq.cong₂ _∷_ (h 0F) (all-false v (λ i → h (sF i)))

⊕-self : ∀ {j} (v : Vec Bool j) → v ⊕ v ≡ zeros
⊕-self []          = Eq.refl
⊕-self (true  ∷ v) = Eq.cong (false ∷_) (⊕-self v)
⊕-self (false ∷ v) = Eq.cong (false ∷_) (⊕-self v)

⊕-zeros : ∀ {j} (v : Vec Bool j) → v ⊕ zeros ≡ v
⊕-zeros []          = Eq.refl
⊕-zeros (true  ∷ v) = Eq.cong (true ∷_) (⊕-zeros v)
⊕-zeros (false ∷ v) = Eq.cong (false ∷_) (⊕-zeros v)

xor-true : ∀ a → (a xor true) ≡ not a
xor-true true  = Eq.refl
xor-true false = Eq.refl

xor-false : ∀ a → (a xor false) ≡ a
xor-false true  = Eq.refl
xor-false false = Eq.refl

private
  four≤ : ∀ {r} → r ≤ 4 → (i : Fin m) → r ≤ toℕ {₄₊ m} (sF (sF (sF (sF i))))
  four≤ r≤ i = ≤-trans r≤ (s≤s (s≤s (s≤s (s≤s z≤n))))

  rest-zero : ∀ {r a b c d} → r ≤ 4 → (rest : Vec Bool m) → Low r (a ∷ b ∷ c ∷ d ∷ rest) → rest ≡ zeros
  rest-zero r≤ rest L = all-false rest (λ i → L (sF (sF (sF (sF i)))) (four≤ r≤ i))

-- A low vector is its first r bits, padded.
low-pad : ∀ (r : ℕ) → r ≤ 4 → (x : St) → Low r x → x ≡ pad (ext (firstR r x))
low-pad zero r≤ (a ∷ b ∷ c ∷ d ∷ rest) L =
  Eq.cong₂ _∷_ (L 0F z≤n) (Eq.cong₂ _∷_ (L (sF 0F) z≤n)
    (Eq.cong₂ _∷_ (L (sF (sF 0F)) z≤n) (Eq.cong₂ _∷_ (L (sF (sF (sF 0F))) z≤n) (rest-zero r≤ rest L))))
low-pad (suc zero) r≤ (a ∷ b ∷ c ∷ d ∷ rest) L =
  Eq.cong (a ∷_) (Eq.cong₂ _∷_ (L (sF 0F) (s≤s z≤n))
    (Eq.cong₂ _∷_ (L (sF (sF 0F)) (s≤s z≤n)) (Eq.cong₂ _∷_ (L (sF (sF (sF 0F))) (s≤s z≤n)) (rest-zero r≤ rest L))))
low-pad (suc (suc zero)) r≤ (a ∷ b ∷ c ∷ d ∷ rest) L =
  Eq.cong (a ∷_) (Eq.cong (b ∷_) (Eq.cong₂ _∷_ (L (sF (sF 0F)) (s≤s (s≤s z≤n)))
    (Eq.cong₂ _∷_ (L (sF (sF (sF 0F))) (s≤s (s≤s z≤n))) (rest-zero r≤ rest L))))
low-pad (suc (suc (suc zero))) r≤ (a ∷ b ∷ c ∷ d ∷ rest) L =
  Eq.cong (a ∷_) (Eq.cong (b ∷_) (Eq.cong (c ∷_)
    (Eq.cong₂ _∷_ (L (sF (sF (sF 0F))) (s≤s (s≤s (s≤s z≤n)))) (rest-zero r≤ rest L))))
low-pad (suc (suc (suc (suc zero)))) r≤ (a ∷ b ∷ c ∷ d ∷ rest) L =
  Eq.cong (a ∷_) (Eq.cong (b ∷_) (Eq.cong (c ∷_) (Eq.cong (d ∷_) (rest-zero r≤ rest L))))
low-pad (suc (suc (suc (suc (suc r))))) (s≤s (s≤s (s≤s (s≤s ())))) _ _

------------------------------------------------------------------------
-- The pivot search

find : ∀ {j} (x : Vec Bool j) (r : ℕ) →
       (∀ i → r ≤ toℕ i → lookup x i ≡ false) ⊎ Σ (Fin j) (λ i → (r ≤ toℕ i) × (lookup x i ≡ true))
find []          r       = inj₁ (λ ())
find (true  ∷ x) zero    = inj₂ (0F , z≤n , Eq.refl)
find (false ∷ x) zero    with find x zero
... | inj₁ h           = inj₁ (λ { 0F _ → Eq.refl ; (sF i) _ → h i z≤n })
... | inj₂ (i , _ , e) = inj₂ (sF i , z≤n , e)
find (b ∷ x)     (suc r) with find x r
... | inj₁ h           = inj₁ (λ { 0F () ; (sF i) (s≤s p) → h i p })
... | inj₂ (i , p , e) = inj₂ (sF i , s≤s p , e)

------------------------------------------------------------------------
-- Supports, and toggling a list of bits

supp : ∀ {j} → Vec Bool j → List (Fin j)
supp []          = List.[]
supp (true  ∷ v) = 0F List.∷ List.map sF (supp v)
supp (false ∷ v) = List.map sF (supp v)

toggles : ∀ {j} → Vec Bool j → List (Fin j) → Vec Bool j
toggles x List.[]       = x
toggles x (w List.∷ L)  = toggle (toggles x L) w

private
  toggles-map : ∀ {j} (a : Bool) (x : Vec Bool j) (L : List (Fin j)) →
                toggles (a ∷ x) (List.map sF L) ≡ a ∷ toggles x L
  toggles-map a x List.[]      = Eq.refl
  toggles-map a x (w List.∷ L) = Eq.cong (λ y → toggle y (sF w)) (toggles-map a x L)

toggles-supp : ∀ {j} (x y : Vec Bool j) → toggles x (supp y) ≡ x ⊕ y
toggles-supp []      []          = Eq.refl
toggles-supp (a ∷ x) (true  ∷ y) =
  Eq.trans (Eq.cong (λ v → toggle v 0F) (toggles-map a x (supp y)))
           (Eq.cong₂ _∷_ (Eq.sym (xor-true a)) (toggles-supp x y))
toggles-supp (a ∷ x) (false ∷ y) =
  Eq.trans (toggles-map a x (supp y)) (Eq.cong₂ _∷_ (Eq.sym (xor-false a)) (toggles-supp x y))

supp-mem : ∀ {j} (y : Vec Bool j) {w} → w ∈ supp y → lookup y w ≡ true
supp-mem (true ∷ y) (here Eq.refl) = Eq.refl
supp-mem (true ∷ y) (there mem) with ∈-map⁻ sF mem
... | w′ , mem′ , Eq.refl = supp-mem y mem′
supp-mem (false ∷ y) mem with ∈-map⁻ sF mem
... | w′ , mem′ , Eq.refl = supp-mem y mem′

------------------------------------------------------------------------
-- X on a list of wires, and CX from one wire onto a list

xsL : List Wire → Word Lt
xsL List.[]      = ε
xsL (w List.∷ L) = X w • xsL L

amap-xsL : ∀ (L : List Wire) (x : St) → amapʷ (xsL L) x ≡ toggles x L
amap-xsL List.[]      x = Eq.refl
amap-xsL (w List.∷ L) x = Eq.cong (λ y → toggle y w) (amap-xsL L x)

clr : (j : Wire) (L : List Wire) → .(∀ {w} → w ∈ L → w ≢ j) → Word Lt
clr j List.[]      h = ε
clr j (w List.∷ L) h = T j w (λ e → h (here Eq.refl) (Eq.sym e)) • clr j L (λ mem → h (there mem))

lookup-toggles : ∀ (x : St) (L : List Wire) (j : Wire) → (∀ {w} → w ∈ L → w ≢ j) →
                 lookup (toggles x L) j ≡ lookup x j
lookup-toggles x List.[]      j h = Eq.refl
lookup-toggles x (w List.∷ L) j h =
  Eq.trans (lookup-toggle′ (toggles x L) w j (λ e → h (here Eq.refl) (Eq.sym e)))
           (lookup-toggles x L j (λ mem → h (there mem)))

if-same : ∀ {A : Set} b (y : A) → (if b then y else y) ≡ y
if-same true  y = Eq.refl
if-same false y = Eq.refl

amap-clr : ∀ (j : Wire) (L : List Wire) (h : ∀ {w} → w ∈ L → w ≢ j) (x : St) →
           amapʷ (clr j L h) x ≡ (if lookup x j then toggles x L else x)
amap-clr j List.[]      h x = Eq.sym (if-same (lookup x j) x)
amap-clr j (w List.∷ L) h x =
  Eq.trans (Eq.cong (tmap j w) (amap-clr j L (λ mem → h (there mem)) x)) (step (lookup x j) Eq.refl)
  where
  step : ∀ b → lookup x j ≡ b → tmap j w (if b then toggles x L else x) ≡ (if b then toggle (toggles x L) w else x)
  step true  e = Eq.cong (λ c → if c then toggle (toggles x L) w else toggles x L)
                         (Eq.trans (lookup-toggles x L j (λ mem → h (there mem))) e)
  step false e = Eq.cong (λ c → if c then toggle x w else x) e

------------------------------------------------------------------------
-- Unit vectors, the swap, and the clearing of a pivot

e : Wire → St
e i = toggle zeros i

private
  lookup-zeros : ∀ {j} (i : Fin j) → lookup (zeros {j}) i ≡ false
  lookup-zeros 0F     = Eq.refl
  lookup-zeros (sF i) = lookup-zeros i

lookup-e : ∀ (i j : Wire) → j ≢ i → lookup (e i) j ≡ false
lookup-e i j ji = Eq.trans (lookup-toggle′ zeros i j ji) (lookup-zeros j)

lookup-e-self : ∀ (i : Wire) → lookup (e i) i ≡ true
lookup-e-self i = Eq.trans (lookup-toggle zeros i) (Eq.cong not (lookup-zeros i))

amap-SW-fix : ∀ (j r : Wire) .(p : j ≢ r) (x : St) → lookup x j ≡ false → lookup x r ≡ false →
              amapʷ (SW j r p) x ≡ x
amap-SW-fix j r p x xj xr =
  Eq.trans (Eq.cong (tmap j r) (Eq.trans (Eq.cong (tmap r j) t1) t2)) t1
  where
  t1 : tmap j r x ≡ x
  t1 = Eq.cong (λ c → if c then toggle x r else x) xj
  t2 : tmap r j x ≡ x
  t2 = Eq.cong (λ c → if c then toggle x j else x) xr

amap-SW-e : ∀ (j r : Wire) .(p : j ≢ r) → j ≢ r → amapʷ (SW j r p) (e j) ≡ e r
amap-SW-e j r p jr =
  Eq.trans (Eq.cong (tmap j r) (Eq.trans (Eq.cong (tmap r j) s1) s2)) s3
  where
  rj : r ≢ j
  rj e′ = jr (Eq.sym e′)
  s1 : tmap j r (e j) ≡ toggle (e j) r
  s1 = Eq.cong (λ c → if c then toggle (e j) r else e j) (lookup-e-self j)
  s2 : tmap r j (toggle (e j) r) ≡ e r
  s2 = Eq.trans (Eq.cong (λ c → if c then toggle (toggle (e j) r) j else toggle (e j) r)
                         (Eq.trans (lookup-toggle (e j) r) (Eq.cong not (lookup-e j r rj))))
                (Eq.trans (toggle-comm (e j) r j) (Eq.cong (λ v → toggle v r) (toggle-invol zeros j)))
  s3 : tmap j r (e r) ≡ e r
  s3 = Eq.cong (λ c → if c then toggle (e r) r else e r) (lookup-e r j jr)

-- The wires of the vector with the pivot cleared are not the pivot.
private
  off-pivot : ∀ (b : St) (j : Wire) → lookup b j ≡ true → ∀ {w} → w ∈ supp (toggle b j) → w ≢ j
  off-pivot b j bj mem Eq.refl =
    t≢f (Eq.trans (Eq.sym (supp-mem (toggle b j) mem)) (Eq.trans (lookup-toggle b j) (Eq.cong not bj)))
    where
    t≢f : true ≢ false
    t≢f ()

clear : (b : St) (j : Wire) → lookup b j ≡ true → Word Lt
clear b j bj = clr j (supp (toggle b j)) (off-pivot b j bj)

clear-pivot : ∀ (b : St) (j : Wire) (bj : lookup b j ≡ true) → amapʷ (clear b j bj) b ≡ e j
clear-pivot b j bj =
  Eq.trans (amap-clr j (supp (toggle b j)) (off-pivot b j bj) b)
    (Eq.trans (Eq.cong (λ c → if c then toggles b (supp (toggle b j)) else b) bj)
      (Eq.trans (toggles-supp b (toggle b j))
        (Eq.trans (toggle-⊕ʳ b b j) (Eq.cong (λ v → toggle v j) (⊕-self b)))))

clear-fix : ∀ (b : St) (j : Wire) (bj : lookup b j ≡ true) (x : St) → lookup x j ≡ false → amapʷ (clear b j bj) x ≡ x
clear-fix b j bj x xj =
  Eq.trans (amap-clr j (supp (toggle b j)) (off-pivot b j bj) x)
           (Eq.cong (λ c → if c then toggles x (supp (toggle b j)) else x) xj)

------------------------------------------------------------------------
-- The ranks below four as wires

finR : (r : ℕ) → r < 4 → Wire
finR zero                   _ = 0F
finR (suc zero)             _ = sF 0F
finR (suc (suc zero))       _ = sF (sF 0F)
finR (suc (suc (suc zero))) _ = sF (sF (sF 0F))
finR (suc (suc (suc (suc r)))) (s≤s (s≤s (s≤s (s≤s ()))))

toℕ-finR : ∀ r (p : r < 4) → toℕ (finR r p) ≡ r
toℕ-finR zero                   _ = Eq.refl
toℕ-finR (suc zero)             _ = Eq.refl
toℕ-finR (suc (suc zero))       _ = Eq.refl
toℕ-finR (suc (suc (suc zero))) _ = Eq.refl
toℕ-finR (suc (suc (suc (suc r)))) (s≤s (s≤s (s≤s (s≤s ()))))

img-new : ∀ r (p : r < 4) → e (finR r p) ≡ pad (ext (unitR r))
img-new zero                   _ = Eq.refl
img-new (suc zero)             _ = Eq.refl
img-new (suc (suc zero))       _ = Eq.refl
img-new (suc (suc (suc zero))) _ = Eq.refl
img-new (suc (suc (suc (suc r)))) (s≤s (s≤s (s≤s (s≤s ()))))

-- Low vectors.
low-mono : ∀ {r x} → Low r x → Low (suc r) x
low-mono L i p = L i (≤-trans (n≤1+n _) p)

e-low : ∀ r (p : r < 4) → Low (suc r) (e (finR r p))
e-low r p i ri = lookup-e (finR r p) i ne
  where
  ne : i ≢ finR r p
  ne eq = <-irrefl Eq.refl (Eq.subst (λ x → suc r ≤ x) (toℕ-finR r p) (Eq.subst (λ y → suc r ≤ toℕ y) eq ri))

------------------------------------------------------------------------
-- The elimination

record Res {j} (r : ℕ) (τ : Word Lt) (ps : Vec St j) : Set where
  field
    δ   : Word Lt
    pat : Pat r j
    fix : ∀ x → Low r x → amapʷ δ x ≡ x
    img : ∀ i → amapʷ δ (amapʷ τ (lookup ps i)) ≡ lookup (imgs pat) i

private
  bnd-tail : ∀ r j → r + suc j ≤ 4 → r + j ≤ 4
  bnd-tail r j b = ≤-trans (+-monoʳ-≤ r (n≤1+n j)) b

  bnd-r : ∀ r j → r + j ≤ 4 → r ≤ 4
  bnd-r r j b = ≤-trans (m≤m+n r j) b

  bnd-lt : ∀ r j → r + suc j ≤ 4 → r < 4
  bnd-lt r j b = ≤-trans (s≤s (m≤m+n r j)) (≤-trans (≤-reflexive (Eq.sym (+-suc r j))) b)

  bnd-new : ∀ r j → r + suc j ≤ 4 → suc r + j ≤ 4
  bnd-new r j b = ≤-trans (≤-reflexive (Eq.sym (+-suc r j))) b

  -- The exchange of the pivot with the rank's wire, if they differ.
  swapTo : (j r : Wire) → Dec (j ≡ r) → Word Lt
  swapTo j r (yes _) = ε
  swapTo j r (no ne) = SW j r ne

  swapTo-fix : ∀ j r (d : Dec (j ≡ r)) (x : St) → lookup x j ≡ false → lookup x r ≡ false → amapʷ (swapTo j r d) x ≡ x
  swapTo-fix j r (yes _) x xj xr = Eq.refl
  swapTo-fix j r (no ne) x xj xr = amap-SW-fix j r ne x xj xr

  swapTo-e : ∀ j r (d : Dec (j ≡ r)) → amapʷ (swapTo j r d) (e j) ≡ e r
  swapTo-e j r (yes Eq.refl) = Eq.refl
  swapTo-e j r (no ne)       = amap-SW-e j r ne ne

loop : ∀ {j} (r : ℕ) → r + j ≤ 4 → (τ : Word Lt) (ps : Vec St j) → Res r τ ps
loop r bnd τ [] = record { δ = ε ; pat = done ; fix = λ x _ → Eq.refl ; img = λ () }
loop {suc j} r bnd τ (p ∷ ps) with find (amapʷ τ p) r
... | inj₁ low = record { δ = Res.δ R ; pat = old (firstR r (amapʷ τ p)) (Res.pat R) ; fix = Res.fix R ; img = img′ }
  where
  R = loop r (bnd-tail r j bnd) τ ps
  img′ : ∀ i → amapʷ (Res.δ R) (amapʷ τ (lookup (p ∷ ps) i)) ≡ lookup (imgs (old (firstR r (amapʷ τ p)) (Res.pat R))) i
  img′ 0F     = Eq.trans (Res.fix R (amapʷ τ p) low) (low-pad r (bnd-r r (suc j) bnd) (amapʷ τ p) low)
  img′ (sF i) = Res.img R i
... | inj₂ (jv , rj , bj) = record { δ = Res.δ R • ε₁ ; pat = new (Res.pat R) ; fix = fix′ ; img = img′ }
  where
  b  = amapʷ τ p
  r< = bnd-lt r j bnd
  rF = finR r r<
  d  = jv ≟ rF
  cl = clear b jv bj
  ε₁ = swapTo jv rF d • cl
  R  = loop (suc r) (bnd-new r j bnd) (ε₁ • τ) ps
  ε₁-fix : ∀ x → Low r x → amapʷ ε₁ x ≡ x
  ε₁-fix x L =
    Eq.trans (Eq.cong (amapʷ (swapTo jv rF d)) (clear-fix b jv bj x (L jv rj)))
             (swapTo-fix jv rF d x (L jv rj) (L rF (≤-reflexive (Eq.sym (toℕ-finR r r<)))))
  fix′ : ∀ x → Low r x → amapʷ (Res.δ R • ε₁) x ≡ x
  fix′ x L = Eq.trans (Eq.cong (amapʷ (Res.δ R)) (ε₁-fix x L)) (Res.fix R x (low-mono {r} {x} L))
  img′ : ∀ i → amapʷ (Res.δ R • ε₁) (amapʷ τ (lookup (p ∷ ps) i)) ≡ lookup (imgs (new {r} (Res.pat R))) i
  img′ 0F =
    Eq.trans (Eq.cong (amapʷ (Res.δ R))
               (Eq.trans (Eq.cong (amapʷ (swapTo jv rF d)) (clear-pivot b jv bj)) (swapTo-e jv rF d)))
      (Eq.trans (Res.fix R (e rF) (e-low r r<)) (img-new r r<))
  img′ (sF i) = Res.img R i

-- The canonical position of a first state and up to four more.
record Canon {k} (ps : Vec St k) : Set where
  field
    τ   : Word Lt
    pat : Pat 0 k
    img : ∀ i → amapʷ τ (lookup ps i) ≡ lookup (imgs pat) i

canon : ∀ {j} (p₀ : St) (ps : Vec St j) → j ≤ 4 → Canon (p₀ ∷ ps)
canon p₀ ps j≤ = record { τ = Res.δ R • τ₀ ; pat = old [] (Res.pat R) ; img = img′ }
  where
  τ₀ = xsL (supp p₀)
  R  = loop 0 j≤ τ₀ ps
  z₀ : amapʷ τ₀ p₀ ≡ zeros
  z₀ = Eq.trans (amap-xsL (supp p₀) p₀) (Eq.trans (toggles-supp p₀ p₀) (⊕-self p₀))
  img′ : ∀ i → amapʷ (Res.δ R • τ₀) (lookup (p₀ ∷ ps) i) ≡ lookup (imgs (old [] (Res.pat R))) i
  img′ 0F     = Eq.trans (Eq.cong (amapʷ (Res.δ R)) z₀) (Res.fix R zeros (λ i _ → lookup-zeros i))
  img′ (sF i) = Res.img R i
