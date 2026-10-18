------------------------------------------------------------------------
-- Presentations of groups
--
-- Routing by affine words: Gaussian elimination as a circuit.
--
-- An affine word acts on bit vectors (`A⟦_⟧`, its classical action),
-- and that action is affine (`aff`): it preserves sums of three
-- vectors.  For an injective linear map f : 𝔽₂ᵏ → 𝔽₂ᵐ, `route` is a
-- word in CX and the swap that sends f(eᵢ) to eᵢ for every i < k.  It
-- reduces f(e₀) to e₀ (GeneralN/AffineRouting's `reduce`), routes the
-- rest of f one wire up, and clears what the images keep on wire 0 by
-- CXs into it (`clear`).  For k = m the reverse word realises f
-- (`realise`): two linear maps that agree on the unit vectors agree
-- (`lin-ext`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.AffineRoute where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_ ; _∧_)
open import Data.Bool.Properties
  using (xor-identityʳ ; xor-same ; xor-assoc ; xor-comm ; ∧-zeroʳ ; ∧-identityʳ)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product.Base using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)
open import Relation.Nullary.Negation using (¬_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

open import Examples.Groups.CCX+HH.NaturalP.AffineWords
  using (AGen ; ax ; acx ; asw ; _↥ₐ ; ιC ; inv)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_ ; lower)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties
  using (zeros ; e₀ ; inverse ; inverse-correct ; act-injective ; act-up-cons ; cons-view)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (cons)
open import Examples.Groups.CCX+HH.GeneralN.AffineRouting
  using (NZ ; one ; both ; next ; vec ; reduce ; reduce-zero ; reduce-vec ; nonzero)

private
  variable
    n k m p : ℕ

------------------------------------------------------------------------
-- Affine words as maps of bit vectors

A⟦_⟧ : Word (AGen n) → State n → State n
A⟦ w ⟧ = C.act (wmap ιC w)

A-cong : (w : Word (AGen n)) {s t : State n} → s ≈s t → A⟦ w ⟧ s ≈s A⟦ w ⟧ t
A-cong w = C.act-cong (wmap ιC w)

infixl 9 _↑ₐ
_↑ₐ : Word (AGen n) → Word (AGen (suc n))
_↑ₐ = wmap _↥ₐ

ιC-↑ : (w : Word (AGen n)) → wmap ιC (w ↑ₐ) ≡ wmap ιC w C.↑
ιC-↑ [ g ]ʷ  = refl
ιC-↑ ε       = refl
ιC-↑ (u • v) = cong₂ _•_ (ιC-↑ u) (ιC-↑ v)

A-↑ : (w : Word (AGen n)) (b : Bool) (s : State n) →
  A⟦ w ↑ₐ ⟧ (cons b s) ≈s cons b (A⟦ w ⟧ s)
A-↑ w b s i =
  trans (cong (λ v → C.act v (cons b s) i) (ιC-↑ w)) (act-up-cons (wmap ιC w) b s i)

ιC-inv : (w : Word (AGen n)) → wmap ιC (inv w) ≡ inverse (wmap ιC w)
ιC-inv [ g ]ʷ  = refl
ιC-inv ε       = refl
ιC-inv (u • v) = cong₂ _•_ (ιC-inv v) (ιC-inv u)

A-inv : (w : Word (AGen n)) (s : State n) → A⟦ inv w ⟧ (A⟦ w ⟧ s) ≈s s
A-inv w s i =
  trans (cong (λ v → C.act v (A⟦ w ⟧ s) i) (ιC-inv w)) (inverse-correct (wmap ιC w) s i)

A-injective : (w : Word (AGen n)) {s t : State n} → A⟦ w ⟧ s ≈s A⟦ w ⟧ t → s ≈s t
A-injective w = act-injective (wmap ιC w)

------------------------------------------------------------------------
-- Sums of bit vectors

infixl 6 _⊕_
_⊕_ : State n → State n → State n
(s ⊕ t) i = s i xor t i

unit : Fin n → State n
unit zero    zero    = true
unit zero    (suc j) = false
unit (suc i) zero    = false
unit (suc i) (suc j) = unit i j

private
  ichg : ∀ a b c d → (a xor b) xor (c xor d) ≡ (a xor c) xor (b xor d)
  ichg false false false false = refl
  ichg false false false true  = refl
  ichg false false true  false = refl
  ichg false false true  true  = refl
  ichg false true  false false = refl
  ichg false true  false true  = refl
  ichg false true  true  false = refl
  ichg false true  true  true  = refl
  ichg true  false false false = refl
  ichg true  false false true  = refl
  ichg true  false true  false = refl
  ichg true  false true  true  = refl
  ichg true  true  false false = refl
  ichg true  true  false true  = refl
  ichg true  true  true  false = refl
  ichg true  true  true  true  = refl

  id-x : ∀ a b c → ((a xor b) xor c) xor true ≡ ((a xor true) xor (b xor true)) xor (c xor true)
  id-x false false false = refl
  id-x false false true  = refl
  id-x false true  false = refl
  id-x false true  true  = refl
  id-x true  false false = refl
  id-x true  false true  = refl
  id-x true  true  false = refl
  id-x true  true  true  = refl

  id-cx : ∀ a b c d e f →
    ((a xor b) xor c) xor ((d xor e) xor f) ≡ ((a xor d) xor (b xor e)) xor (c xor f)
  id-cx a b c d e f =
    trans (ichg (a xor b) c (d xor e) f) (cong (_xor (c xor f)) (ichg a b d e))

-- Affine maps preserve sums of three vectors.
Aff : (State n → State m) → Set
Aff F = ∀ s t r → F ((s ⊕ t) ⊕ r) ≈s (F s ⊕ F t) ⊕ F r

private
  aff₀ : (g : AGen n) → Aff (C.act₀ (ιC g))
  aff₀ ax s t r zero    = id-x (s zero) (t zero) (r zero)
  aff₀ ax s t r (suc i) = refl
  aff₀ acx s t r zero   =
    id-cx (s zero) (t zero) (r zero) (s (suc zero)) (t (suc zero)) (r (suc zero))
  aff₀ acx s t r (suc i)             = refl
  aff₀ asw s t r zero                = refl
  aff₀ asw s t r (suc zero)          = refl
  aff₀ asw s t r (suc (suc i))       = refl
  aff₀ (g ↥ₐ) s t r zero    = refl
  aff₀ (g ↥ₐ) s t r (suc i) = aff₀ g (lower s) (lower t) (lower r) i

aff : (w : Word (AGen n)) → Aff A⟦ w ⟧
aff [ g ]ʷ  = aff₀ g
aff ε s t r i = refl
aff (u • v) s t r i =
  trans (A-cong u (aff v s t r) i) (aff u (A⟦ v ⟧ s) (A⟦ v ⟧ t) (A⟦ v ⟧ r) i)

-- A linear map: additive and respecting pointwise equality.
record Lin (F : State n → State m) : Set where
  field
    add  : ∀ s t → F (s ⊕ t) ≈s F s ⊕ F t
    resp : ∀ {s t} → s ≈s t → F s ≈s F t

lin-zero : {F : State n → State m} → Lin F → F zeros ≈s zeros
lin-zero {F = F} L i =
  trans (sym (xor-identityʳ (F zeros i)))
  (trans (cong (F zeros i xor_) (sym (xor-same (F zeros i))))
  (trans (sym (assoc3 (F zeros i)))
  (trans (cong (_xor F zeros i) (sym (Lin.add L zeros zeros i))) (xor-same (F zeros i)))))
  where
  assoc3 : ∀ a → (a xor a) xor a ≡ a xor (a xor a)
  assoc3 false = refl
  assoc3 true  = refl

-- An affine word that fixes 0 is linear.
word-lin : (w : Word (AGen n)) → A⟦ w ⟧ zeros ≈s zeros → Lin A⟦ w ⟧
word-lin w z = record { add = add ; resp = A-cong w }
  where
  add : ∀ s t → A⟦ w ⟧ (s ⊕ t) ≈s A⟦ w ⟧ s ⊕ A⟦ w ⟧ t
  add s t i =
    trans (A-cong w (λ j → sym (xor-identityʳ (s j xor t j))) i)
    (trans (aff w s t zeros i)
    (trans (cong ((A⟦ w ⟧ s i xor A⟦ w ⟧ t i) xor_) (z i))
      (xor-identityʳ _)))

------------------------------------------------------------------------
-- Two linear maps that agree on the unit vectors agree

private
  bit : Bool → State (suc n)
  bit true  = e₀
  bit false = zeros

  split : (s : State (suc n)) → s ≈s bit (s zero) ⊕ cons false (lower s)
  split s = go (s zero) refl
    where
    go : ∀ b → s zero ≡ b → s ≈s bit b ⊕ cons false (lower s)
    go true  e zero    = e
    go true  e (suc i) = refl
    go false e zero    = e
    go false e (suc i) = refl

lin-ext : (F G : State n → State m) → Lin F → Lin G →
  (∀ i → F (unit i) ≈s G (unit i)) → ∀ s → F s ≈s G s
lin-ext {zero} F G LF LG e s i =
  trans (Lin.resp LF (λ ()) i) (trans (lin-zero LF i)
    (trans (sym (lin-zero LG i)) (Lin.resp LG (λ ()) i)))
lin-ext {suc n} {m} F G LF LG e s i =
  trans (Lin.resp LF (split s) i)
  (trans (Lin.add LF (bit (s zero)) (cons false (lower s)) i)
  (trans (cong₂ _xor_ (on-bit (s zero) i)
                     (lin-ext F′ G′ LF′ LG′ e′ (lower s) i))
  (trans (sym (Lin.add LG (bit (s zero)) (cons false (lower s)) i))
    (Lin.resp LG (λ j → sym (split s j)) i))))
  where
  on-bit : ∀ b → F (bit b) ≈s G (bit b)
  on-bit true  j = trans (Lin.resp LF (λ { zero → refl ; (suc _) → refl }) j)
                     (trans (e zero j) (Lin.resp LG (λ { zero → refl ; (suc _) → refl }) j))
  on-bit false j = trans (lin-zero LF j) (sym (lin-zero LG j))

  cons-add : ∀ (s t : State n) → cons false (s ⊕ t) ≈s cons false s ⊕ cons false t
  cons-add s t zero    = refl
  cons-add s t (suc j) = refl

  F′ G′ : State n → State m
  F′ t = F (cons false t)
  G′ t = G (cons false t)

  LF′ : Lin F′
  LF′ = record
    { add  = λ s t j → trans (Lin.resp LF (cons-add s t) j) (Lin.add LF _ _ j)
    ; resp = λ e j → Lin.resp LF (λ { zero → refl ; (suc l) → e l }) j }

  LG′ : Lin G′
  LG′ = record
    { add  = λ s t j → trans (Lin.resp LG (cons-add s t) j) (Lin.add LG _ _ j)
    ; resp = λ e j → Lin.resp LG (λ { zero → refl ; (suc l) → e l }) j }

  e′ : ∀ l → F′ (unit l) ≈s G′ (unit l)
  e′ l j = trans (Lin.resp LF (unit-suc l) j)
             (trans (e (suc l) j) (Lin.resp LG (λ x → sym (unit-suc l x)) j))
    where
    unit-suc : ∀ l → cons false (unit l) ≈s unit (suc l)
    unit-suc l zero    = refl
    unit-suc l (suc x) = refl

------------------------------------------------------------------------
-- The letters of the routing

-- The CX from wire 0 into wire 1.
cx01 : Word (AGen (suc (suc n)))
cx01 = [ asw ]ʷ • [ acx ]ʷ • [ asw ]ʷ

reduceA : NZ n → Word (AGen n)
reduceA one      = ε
reduceA (both v) = cx01 • (reduceA v ↑ₐ)
reduceA (next v) = [ asw ]ʷ • (reduceA v ↑ₐ)

reduceA-≡ : (v : NZ n) → wmap ιC (reduceA v) ≡ reduce v
reduceA-≡ one      = refl
reduceA-≡ (both v) = cong (_ •_) (trans (ιC-↑ (reduceA v)) (cong C._↑ (reduceA-≡ v)))
reduceA-≡ (next v) = cong (_ •_) (trans (ιC-↑ (reduceA v)) (cong C._↑ (reduceA-≡ v)))

reduceA-zero : (v : NZ n) → A⟦ reduceA v ⟧ zeros ≈s zeros
reduceA-zero v i = trans (cong (λ w → C.act w zeros i) (reduceA-≡ v)) (reduce-zero v i)

reduceA-vec : (v : NZ (suc n)) → A⟦ reduceA v ⟧ (vec v) ≈s e₀
reduceA-vec v i = trans (cong (λ w → C.act w (vec v) i) (reduceA-≡ v)) (reduce-vec v i)

-- Adding b to wire 0.
flip0 : Bool → State (suc n) → State (suc n)
flip0 b s zero    = s zero xor b
flip0 b s (suc i) = s (suc i)

-- The CX from wire j + 1 into wire 0.
cx0 : Fin m → Word (AGen (suc m))
cx0 zero            = [ acx ]ʷ
cx0 {suc m} (suc j) = [ asw ]ʷ • (cx0 j ↑ₐ) • [ asw ]ʷ

cx0-act : (j : Fin m) (s : State (suc m)) → A⟦ cx0 j ⟧ s ≈s flip0 (s (suc j)) s
cx0-act zero s zero    = refl
cx0-act zero s (suc i) = refl
cx0-act {suc m} (suc j) s i = trans (C.act-cong [ C.gate₂ C.SWAP-gate ]ʷ inner i) (back i)
  where
  sw = C.act [ C.gate₂ {m} C.SWAP-gate ]ʷ s
  inner : A⟦ cx0 j ↑ₐ ⟧ sw ≈s cons (s (suc zero)) (flip0 (s (suc (suc j))) (lower sw))
  inner l = trans (A-cong (cx0 j ↑ₐ) (λ x → sym (cons-view sw x)) l)
              (trans (A-↑ (cx0 j) (sw zero) (lower sw) l)
                (cong-cons l))
    where
    cong-cons : ∀ l → cons (sw zero) (A⟦ cx0 j ⟧ (lower sw)) l ≡
                      cons (s (suc zero)) (flip0 (s (suc (suc j))) (lower sw)) l
    cong-cons zero    = refl
    cong-cons (suc x) = cx0-act j (lower sw) x
  back : C.act [ C.gate₂ C.SWAP-gate ]ʷ (cons (s (suc zero)) (flip0 (s (suc (suc j))) (lower sw)))
           ≈s flip0 (s (suc (suc j))) s
  back zero          = refl
  back (suc zero)    = refl
  back (suc (suc x)) = refl

-- Dot product of a mask with the bits of a vector, along k ≤ m.
dot : k ≤ m → (Fin k → Bool) → State m → Bool
dot z≤n       bs t = false
dot (s≤s le) bs t = (bs zero ∧ t zero) xor dot le (λ i → bs (suc i)) (lower t)

dot-zeros : (le : k ≤ m) (bs : Fin k → Bool) → dot le bs zeros ≡ false
dot-zeros z≤n      bs = refl
dot-zeros (s≤s le) bs =
  cong₂ _xor_ (∧-zeroʳ (bs zero)) (dot-zeros le (λ i → bs (suc i)))

-- The unit vectors of the target, along k ≤ m.
u′ : k ≤ m → Fin k → State m
u′ (s≤s le) zero    = e₀
u′ (s≤s le) (suc i) = cons false (u′ le i)

dot-u′ : (le : k ≤ m) (bs : Fin k → Bool) (i : Fin k) → dot le bs (u′ le i) ≡ bs i
dot-u′ (s≤s le) bs zero =
  trans (cong₂ _xor_ (∧-identityʳ (bs zero)) (dot-zeros le (λ i → bs (suc i))))
    (xor-identityʳ (bs zero))
dot-u′ (s≤s le) bs (suc i) =
  trans (cong (_xor dot le (λ i → bs (suc i)) (u′ le i)) (∧-zeroʳ (bs zero)))
    (dot-u′ le (λ i → bs (suc i)) i)

private
  bit-cx : Bool → Word (AGen (suc (suc n)))
  bit-cx true  = [ acx ]ʷ
  bit-cx false = ε

  bit-cx-act : (b : Bool) (s : State (suc (suc n))) →
    A⟦ bit-cx b ⟧ s ≈s flip0 (b ∧ s (suc zero)) s
  bit-cx-act true  s zero    = refl
  bit-cx-act true  s (suc i) = refl
  bit-cx-act false s zero    = sym (xor-identityʳ (s zero))
  bit-cx-act false s (suc i) = refl

-- Clearing wire 0: add the masked bits of wires 1 … k into it.
clear : k ≤ m → (Fin k → Bool) → Word (AGen (suc m))
clear z≤n       bs = ε
clear (s≤s le) bs =
  bit-cx (bs zero) • ([ asw ]ʷ • (clear le (λ i → bs (suc i)) ↑ₐ) • [ asw ]ʷ)

clear-act : (le : k ≤ m) (bs : Fin k → Bool) (s : State (suc m)) →
  A⟦ clear le bs ⟧ s ≈s flip0 (dot le bs (lower s)) s
clear-act z≤n bs s zero    = sym (xor-identityʳ (s zero))
clear-act z≤n bs s (suc i) = refl
clear-act {suc k} {suc m} (s≤s le) bs s =
  λ i → trans (A-cong (bit-cx (bs zero)) rest i)
          (trans (bit-cx-act (bs zero) (flip0 d′ s) i) (fin i))
  where
  bs′ : Fin k → Bool
  bs′ i = bs (suc i)
  d′ = dot le bs′ (lower (lower s))
  sw = C.act [ C.gate₂ {m} C.SWAP-gate ]ʷ s
  inner : A⟦ clear le bs′ ↑ₐ ⟧ sw ≈s cons (s (suc zero)) (flip0 d′ (lower sw))
  inner l = trans (A-cong (clear le bs′ ↑ₐ) (λ x → sym (cons-view sw x)) l)
              (trans (A-↑ (clear le bs′) (sw zero) (lower sw) l) (cc l))
    where
    cc : ∀ l → cons (sw zero) (A⟦ clear le bs′ ⟧ (lower sw)) l ≡
               cons (s (suc zero)) (flip0 d′ (lower sw)) l
    cc zero    = refl
    cc (suc x) = clear-act le bs′ (lower sw) x
  back : C.act [ C.gate₂ C.SWAP-gate ]ʷ (cons (s (suc zero)) (flip0 d′ (lower sw)))
           ≈s flip0 d′ s
  back zero          = refl
  back (suc zero)    = refl
  back (suc (suc x)) = refl
  rest : A⟦ [ asw ]ʷ • (clear le bs′ ↑ₐ) • [ asw ]ʷ ⟧ s ≈s flip0 d′ s
  rest l = trans (C.act-cong [ C.gate₂ C.SWAP-gate ]ʷ inner l) (back l)
  fin : flip0 (bs zero ∧ s (suc zero)) (flip0 d′ s) ≈s
        flip0 ((bs zero ∧ s (suc zero)) xor d′) s
  fin zero    = trans (xor-assoc (s zero) d′ _) (cong (s zero xor_) (xor-comm d′ _))
  fin (suc i) = refl

clear-zero : (le : k ≤ m) (bs : Fin k → Bool) → A⟦ clear le bs ⟧ zeros ≈s zeros
clear-zero le bs zero    = trans (clear-act le bs zeros zero) (dot-zeros le bs)
clear-zero le bs (suc i) = clear-act le bs zeros (suc i)

------------------------------------------------------------------------
-- Routing an injective linear map

record Emb (k m : ℕ) : Set where
  field
    f   : State k → State m
    lin : Lin f
    inj : ∀ s → f s ≈s zeros → s ≈s zeros

lin-∘ : {F : State m → State p} {G : State k → State m} → Lin F → Lin G → Lin (λ s → F (G s))
lin-∘ LF LG = record
  { add  = λ s t i → trans (Lin.resp LF (Lin.add LG s t) i) (Lin.add LF _ _ i)
  ; resp = λ e → Lin.resp LF (Lin.resp LG e) }

private
  xor-false : ∀ {a b} → a xor b ≡ false → a ≡ b
  xor-false {false} {false} e = refl
  xor-false {true}  {true}  e = refl
  xor-false {false} {true}  ()
  xor-false {true}  {false} ()

lin-injective : {F : State k → State m} → Lin F → (∀ s → F s ≈s zeros → s ≈s zeros) →
  ∀ {s t} → F s ≈s F t → s ≈s t
lin-injective {F = F} LF z {s} {t} e i =
  xor-false (z (s ⊕ t) (λ j → trans (Lin.add LF s t j)
    (trans (cong (_xor F t j) (e j)) (xor-same (F t j)))) i)

module Step {k m : ℕ} (E : Emb (suc k) (suc m)) where
  open Emb E

  v₀ : State (suc m)
  v₀ = f e₀

  nz : ¬ (v₀ ≈s zeros)
  nz z with inj e₀ z zero
  ... | ()

  v : NZ (suc m)
  v = proj₁ (nonzero (suc m) v₀ nz)

  R : Word (AGen (suc m))
  R = reduceA v

  g : State (suc k) → State (suc m)
  g s = A⟦ R ⟧ (f s)

  gL : Lin g
  gL = lin-∘ (word-lin R (reduceA-zero v)) lin

  g-inj : ∀ {s t} → g s ≈s g t → s ≈s t
  g-inj e = lin-injective lin inj (A-injective R e)

  g-e₀ : g e₀ ≈s e₀
  g-e₀ i = trans (A-cong R (λ j → sym (proj₂ (nonzero (suc m) v₀ nz) j)) i) (reduceA-vec v i)

  bs : Fin k → Bool
  bs i = g (cons false (unit i)) zero

  f′ : State k → State m
  f′ t = lower (g (cons false t))

  private
    cons-add : ∀ (s t : State k) → cons false (s ⊕ t) ≈s cons false s ⊕ cons false t
    cons-add s t zero    = refl
    cons-add s t (suc j) = refl

    absurd-e₀ : ∀ {t : State k} → cons false t ≈s e₀ → ⊥
    absurd-e₀ e with e zero
    ... | ()

    inj-at : ∀ t → f′ t ≈s zeros → ∀ b → g (cons false t) zero ≡ b → t ≈s zeros
    inj-at t z false e i = g-inj {s = cons false t} {t = zeros} at (suc i)
      where
      at : g (cons false t) ≈s g zeros
      at zero    = trans e (sym (lin-zero gL zero))
      at (suc j) = trans (z j) (sym (lin-zero gL (suc j)))
    inj-at t z true e i = ⊥-elim (absurd-e₀ (λ x → g-inj {s = cons false t} {t = e₀} at x))
      where
      at : g (cons false t) ≈s g e₀
      at zero    = trans e (sym (g-e₀ zero))
      at (suc j) = trans (z j) (sym (g-e₀ (suc j)))

  E′ : Emb k m
  E′ = record
    { f   = f′
    ; lin = record
      { add  = λ s t i → trans (Lin.resp gL (cons-add s t) (suc i)) (Lin.add gL _ _ (suc i))
      ; resp = λ e i → Lin.resp gL (λ { zero → refl ; (suc j) → e j }) (suc i) }
    ; inj = λ t z → inj-at t z (g (cons false t) zero) refl
    }

  -- What is left after reducing f(e₀) and routing the rest.
  g-unit : ∀ i → g (unit (suc i)) ≈s cons (bs i) (f′ (unit i))
  g-unit i j = trans (Lin.resp gL (λ { zero → refl ; (suc x) → refl }) j)
                 (sym (cons-view (g (cons false (unit i))) j))

route : k ≤ m → Emb k m → Word (AGen m)
route z≤n      E = ε
route (s≤s le) E = clear le (Step.bs E) • ((route le (Step.E′ E) ↑ₐ) • Step.R E)

route-zero : (le : k ≤ m) (E : Emb k m) → A⟦ route le E ⟧ zeros ≈s zeros
route-zero z≤n E i = refl
route-zero (s≤s le) E i =
  trans (A-cong (clear le (Step.bs E)) up i) (clear-zero le (Step.bs E) i)
  where
  cz : ∀ {n} → cons false (zeros {n}) ≈s zeros
  cz zero    = refl
  cz (suc _) = refl
  cr : cons false (A⟦ route le (Step.E′ E) ⟧ zeros) ≈s zeros
  cr zero    = refl
  cr (suc x) = route-zero le (Step.E′ E) x
  up : A⟦ route le (Step.E′ E) ↑ₐ ⟧ (A⟦ Step.R E ⟧ zeros) ≈s zeros
  up j = trans (A-cong (route le (Step.E′ E) ↑ₐ)
                 (λ x → trans (reduceA-zero (Step.v E) x) (sym (cz x))) j)
           (trans (A-↑ (route le (Step.E′ E)) false zeros j) (cr j))

route-ok : (le : k ≤ m) (E : Emb k m) (i : Fin k) →
  A⟦ route le E ⟧ (Emb.f E (unit i)) ≈s u′ le i
route-ok (s≤s le) E zero j =
  trans (A-cong (clear le bs) up j)
    (trans (clear-act le bs (cons true zeros) j) (fin j))
  where
  open Step E using (bs ; R ; g-e₀ ; E′)
  e₀-cons : ∀ {n} → e₀ {n} ≈s cons true zeros
  e₀-cons zero    = refl
  e₀-cons (suc _) = refl
  cr : cons true (A⟦ route le E′ ⟧ zeros) ≈s cons true zeros
  cr zero    = refl
  cr (suc y) = route-zero le E′ y
  up : A⟦ route le E′ ↑ₐ ⟧ (A⟦ R ⟧ (Emb.f E (unit zero))) ≈s cons true zeros
  up x = trans (A-cong (route le E′ ↑ₐ)
                 (λ y → trans (A-cong R (Lin.resp (Emb.lin E)
                                 (λ { zero → refl ; (suc _) → refl })) y)
                          (trans (g-e₀ y) (e₀-cons y))) x)
           (trans (A-↑ (route le E′) true zeros x) (cr x))
  fin : flip0 (dot le bs zeros) (cons true zeros) ≈s e₀
  fin zero    = cong (true xor_) (dot-zeros le bs)
  fin (suc _) = refl
route-ok (s≤s le) E (suc i) j =
  trans (A-cong (clear le bs) up j)
    (trans (clear-act le bs (cons (bs i) (u′ le i)) j) (fin j))
  where
  open Step E using (bs ; R ; g-unit ; E′ ; f′)
  cr : cons (bs i) (A⟦ route le E′ ⟧ (f′ (unit i))) ≈s cons (bs i) (u′ le i)
  cr zero    = refl
  cr (suc y) = route-ok le E′ i y
  up : A⟦ route le E′ ↑ₐ ⟧ (A⟦ R ⟧ (Emb.f E (unit (suc i)))) ≈s cons (bs i) (u′ le i)
  up x = trans (A-cong (route le E′ ↑ₐ) (g-unit i) x)
           (trans (A-↑ (route le E′) (bs i) (f′ (unit i)) x) (cr x))
  fin : flip0 (dot le bs (u′ le i)) (cons (bs i) (u′ le i)) ≈s u′ (s≤s le) (suc i)
  fin zero    = trans (cong (bs i xor_) (dot-u′ le bs i)) (xor-same (bs i))
  fin (suc _) = refl

------------------------------------------------------------------------
-- Realising an invertible linear map

private
  u′-refl : ∀ m (i : Fin m) → u′ (≤-refl {m}) i ≈s unit i
  u′-refl (suc m) zero    zero    = refl
  u′-refl (suc m) zero    (suc j) = refl
  u′-refl (suc m) (suc i) zero    = refl
  u′-refl (suc m) (suc i) (suc j) = u′-refl m i j

  id-lin : Lin (λ (s : State n) → s)
  id-lin = record { add = λ s t i → refl ; resp = λ e → e }

-- The routing of f inverts f.
route-inv : (E : Emb m m) → ∀ s → A⟦ route ≤-refl E ⟧ (Emb.f E s) ≈s s
route-inv {m} E = lin-ext (λ s → A⟦ route ≤-refl E ⟧ (Emb.f E s)) (λ s → s)
  (lin-∘ (word-lin (route ≤-refl E) (route-zero ≤-refl E)) (Emb.lin E)) id-lin
  (λ i j → trans (route-ok ≤-refl E i j) (u′-refl m i j))

-- A word for f.
realise : Emb m m → Word (AGen m)
realise E = inv (route ≤-refl E)

realise-ok : (E : Emb m m) → ∀ s → A⟦ realise E ⟧ s ≈s Emb.f E s
realise-ok E s i =
  trans (A-cong (inv (route ≤-refl E)) (λ j → sym (route-inv E s j)) i)
    (A-inv (route ≤-refl E) (Emb.f E s) i)

------------------------------------------------------------------------
-- Words without X

data LinG : AGen n → Set where
  lg-cx : LinG (acx {n})
  lg-sw : LinG (asw {n})
  lg-up : {g : AGen n} → LinG g → LinG (g ↥ₐ)

data LinW : Word (AGen n) → Set where
  lw-g : {g : AGen n} → LinG g → LinW [ g ]ʷ
  lw-ε : LinW {n} ε
  lw-• : {u v : Word (AGen n)} → LinW u → LinW v → LinW (u • v)

LinW-↑ : {w : Word (AGen n)} → LinW w → LinW (w ↑ₐ)
LinW-↑ (lw-g p)   = lw-g (lg-up p)
LinW-↑ lw-ε       = lw-ε
LinW-↑ (lw-• p q) = lw-• (LinW-↑ p) (LinW-↑ q)

LinW-inv : {w : Word (AGen n)} → LinW w → LinW (inv w)
LinW-inv (lw-g p)   = lw-g p
LinW-inv lw-ε       = lw-ε
LinW-inv (lw-• p q) = lw-• (LinW-inv q) (LinW-inv p)

private
  sw-lin : LinW ([ asw {n} ]ʷ)
  sw-lin = lw-g lg-sw

  cx01-lin : LinW (cx01 {n})
  cx01-lin = lw-• sw-lin (lw-• (lw-g lg-cx) sw-lin)

  reduceA-lin : (v : NZ n) → LinW (reduceA v)
  reduceA-lin one      = lw-ε
  reduceA-lin (both v) = lw-• cx01-lin (LinW-↑ (reduceA-lin v))
  reduceA-lin (next v) = lw-• sw-lin (LinW-↑ (reduceA-lin v))

  bit-cx-lin : (b : Bool) → LinW (bit-cx {n} b)
  bit-cx-lin true  = lw-g lg-cx
  bit-cx-lin false = lw-ε

  clear-lin : (le : k ≤ m) (bs : Fin k → Bool) → LinW (clear le bs)
  clear-lin z≤n      bs = lw-ε
  clear-lin (s≤s le) bs =
    lw-• (bit-cx-lin (bs zero)) (lw-• sw-lin (lw-• (LinW-↑ (clear-lin le (λ i → bs (suc i)))) sw-lin))

route-lin : (le : k ≤ m) (E : Emb k m) → LinW (route le E)
route-lin z≤n      E = lw-ε
route-lin (s≤s le) E =
  lw-• (clear-lin le (Step.bs E)) (lw-• (LinW-↑ (route-lin le (Step.E′ E))) (reduceA-lin (Step.v E)))

realise-lin : (E : Emb m m) → LinW (realise E)
realise-lin E = LinW-inv (route-lin ≤-refl E)
