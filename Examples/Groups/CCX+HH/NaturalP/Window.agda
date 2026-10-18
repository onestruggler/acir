------------------------------------------------------------------------
-- Presentations of groups
--
-- An affine word that fixes the window, as a word that visibly does.
--
-- On 4 + k + c wires, the bottom k are the controls and the 4 + c
-- above them the block; the window is the set of states whose controls
-- are all 0.  A state is a pair of a control part and a block part
-- (`low`, `high`, `join`).  An affine word on the controls alone acts
-- on the whole width through `wₐ`.  The fan `fan01 m` adds wire 0 into
-- the wires that the mask m marks, and `Lfan k L` adds into the block
-- the image of the controls under a linear map L.
--
-- An affine word S that fixes every state of the window is linear and
-- sends (a , h) to (N a , h ⊕ L a) (`decomp`), so it acts as the word
-- `S′ = wₐ c (realise N) • Lfan k L` (`S′-act`).  Every letter of S′
-- commutes with gates controlled by the controls in white: the first
-- part lives on the controls and has no X (`realise-lin`), the second
-- is controlled by them in black (NaturalP/Stab).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Window where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_ ; _∧_)
open import Data.Bool.Properties
  using (xor-identityʳ ; xor-assoc ; xor-comm ; ∧-identityʳ ; ∧-zeroʳ)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)
open import Notations using (₄₊)

open import Examples.Groups.CCX+HH.NaturalP.AffineWords using (AGen ; ax ; acx ; asw ; _↥ₐ ; ιC)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_ ; lower)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros ; e₀)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (cons)

private
  variable
    k c n m : ℕ

------------------------------------------------------------------------
-- Controls and block

low : ∀ k → State (₄₊ (k + c)) → State k
low zero    x ()
low (suc k) x = cons (x zero) (low k (lower x))

high : ∀ k → State (₄₊ (k + c)) → State (₄₊ c)
high zero    x = x
high (suc k) x = high k (lower x)

join : ∀ k → State k → State (₄₊ c) → State (₄₊ (k + c))
join zero    a h = h
join (suc k) a h = cons (a zero) (join k (lower a) h)

low-join : ∀ k (a : State k) (h : State (₄₊ c)) → low k (join k a h) ≈s a
low-join zero    a h ()
low-join (suc k) a h zero    = refl
low-join (suc k) a h (suc i) = low-join k (lower a) h i

high-join : ∀ k (a : State k) (h : State (₄₊ c)) → high k (join k a h) ≈s h
high-join zero    a h i = refl
high-join (suc k) a h i = high-join k (lower a) h i

join-lh : ∀ k (x : State (₄₊ (k + c))) → join k (low k x) (high k x) ≈s x
join-lh zero    x i       = refl
join-lh (suc k) x zero    = refl
join-lh (suc k) x (suc i) = join-lh k (lower x) i

join-resp : ∀ k {a a′ : State k} {h h′ : State (₄₊ c)} → a ≈s a′ → h ≈s h′ →
  join k a h ≈s join k a′ h′
join-resp zero    ea eh i       = eh i
join-resp (suc k) ea eh zero    = ea zero
join-resp (suc k) ea eh (suc i) = join-resp k (λ j → ea (suc j)) eh i

join-⊕ : ∀ k (a a′ : State k) (h h′ : State (₄₊ c)) →
  join k (a ⊕ a′) (h ⊕ h′) ≈s join k a h ⊕ join k a′ h′
join-⊕ zero    a a′ h h′ i       = refl
join-⊕ (suc k) a a′ h h′ zero    = refl
join-⊕ (suc k) a a′ h h′ (suc i) = join-⊕ k (lower a) (lower a′) h h′ i

low-resp : ∀ k {x y : State (₄₊ (k + c))} → x ≈s y → low k x ≈s low k y
low-resp zero    e ()
low-resp (suc k) e zero    = e zero
low-resp (suc k) e (suc i) = low-resp k (λ j → e (suc j)) i

high-resp : ∀ k {x y : State (₄₊ (k + c))} → x ≈s y → high k x ≈s high k y
high-resp zero    e i = e i
high-resp (suc k) e i = high-resp k (λ j → e (suc j)) i

low-⊕ : ∀ k (x y : State (₄₊ (k + c))) → low k (x ⊕ y) ≈s low k x ⊕ low k y
low-⊕ zero    x y ()
low-⊕ (suc k) x y zero    = refl
low-⊕ (suc k) x y (suc i) = low-⊕ k (lower x) (lower y) i

high-⊕ : ∀ k (x y : State (₄₊ (k + c))) → high k (x ⊕ y) ≈s high k x ⊕ high k y
high-⊕ zero    x y i = refl
high-⊕ (suc k) x y i = high-⊕ k (lower x) (lower y) i

low-zeros : ∀ k → low {c} k zeros ≈s zeros
low-zeros zero    ()
low-zeros (suc k) zero    = refl
low-zeros (suc k) (suc i) = low-zeros k i

------------------------------------------------------------------------
-- Words on the controls

wg : (c : ℕ) → AGen k → AGen (₄₊ (k + c))
wg c ax     = ax
wg c acx    = acx
wg c asw    = asw
wg c (g ↥ₐ) = wg c g ↥ₐ

wₐ : (c : ℕ) → Word (AGen k) → Word (AGen (₄₊ (k + c)))
wₐ c = wmap (wg c)

private
  A-wg : (g : AGen k) (a : State k) (h : State (₄₊ c)) →
    C.act₀ (ιC (wg c g)) (join k a h) ≈s join k (C.act₀ (ιC g) a) h
  A-wg ax a h zero          = refl
  A-wg ax a h (suc i)       = refl
  A-wg acx a h zero         = refl
  A-wg acx a h (suc i)      = refl
  A-wg asw a h zero         = refl
  A-wg asw a h (suc zero)   = refl
  A-wg asw a h (suc (suc i)) = refl
  A-wg (g ↥ₐ) a h zero      = refl
  A-wg (g ↥ₐ) a h (suc i)   = A-wg g (lower a) h i

A-w : (w : Word (AGen k)) (a : State k) (h : State (₄₊ c)) →
  A⟦ wₐ c w ⟧ (join k a h) ≈s join k (A⟦ w ⟧ a) h
A-w [ g ]ʷ  a h = A-wg g a h
A-w ε       a h i = refl
A-w {k} {c} (u • v) a h i =
  trans (A-cong (wₐ c u) (A-w v a h) i) (A-w u (A⟦ v ⟧ a) h i)

------------------------------------------------------------------------
-- Fans

-- b times a vector.
scale : Bool → State n → State n
scale b x i = x i ∧ b

-- The CX from wire 0 into wire 1, when b.
bit01 : Bool → Word (AGen (suc (suc n)))
bit01 true  = cx01
bit01 false = ε

-- Wire 0 added into the wires 1 + j for the j that the mask marks.
fan01 : State m → Word (AGen (suc m))
fan01 {zero}  mask = ε
fan01 {suc m} mask = bit01 (mask zero) • ([ asw ]ʷ • (fan01 (lower mask) ↑ₐ) • [ asw ]ʷ)

private
  bit01-act : (b : Bool) (z : State (suc (suc n))) (i : Fin (suc (suc n))) →
    A⟦ bit01 b ⟧ z i ≡ cons (z zero) (lower z ⊕ scale (z zero) (cons b zeros)) i
  bit01-act true  z zero          = refl
  bit01-act true  z (suc zero)    = refl
  bit01-act true  z (suc (suc i)) = sym (xor-identityʳ (z (suc (suc i))))
  bit01-act false z zero          = refl
  bit01-act false z (suc zero)    = sym (xor-identityʳ _)
  bit01-act false z (suc (suc i)) = sym (xor-identityʳ (z (suc (suc i))))

fan01-act : (mask : State m) (x : State (suc m)) →
  A⟦ fan01 mask ⟧ x ≈s cons (x zero) (lower x ⊕ scale (x zero) mask)
fan01-act {zero}  mask x zero = refl
fan01-act {zero}  mask x (suc ())
fan01-act {suc m} mask x i =
  trans (A-cong (bit01 (mask zero)) rest i)
    (trans (bit01-act (mask zero) z i) (fin i))
  where
  sw = C.act [ C.gate₂ {m} C.SWAP-gate ]ʷ x
  inner′ : State m
  inner′ = lower (lower x) ⊕ scale (x zero) (lower mask)
  z : State (suc (suc m))
  z = cons (x zero) (cons (x (suc zero)) inner′)
  up : A⟦ fan01 (lower mask) ↑ₐ ⟧ sw ≈s cons (x (suc zero)) (cons (x zero) inner′)
  up j = trans (A-cong (fan01 (lower mask) ↑ₐ) (λ y → sym (cv y)) j)
           (trans (A-↑ (fan01 (lower mask)) (x (suc zero)) (lower sw) j) (cc j))
    where
    cv : ∀ y → cons (sw zero) (lower sw) y ≡ sw y
    cv zero    = refl
    cv (suc y) = refl
    cc : ∀ j → cons (x (suc zero)) (A⟦ fan01 (lower mask) ⟧ (lower sw)) j ≡
               cons (x (suc zero)) (cons (x zero) inner′) j
    cc zero    = refl
    cc (suc y) = fan01-act (lower mask) (lower sw) y
  rest : A⟦ [ asw ]ʷ • (fan01 (lower mask) ↑ₐ) • [ asw ]ʷ ⟧ x ≈s z
  rest j = trans (C.act-cong [ C.gate₂ C.SWAP-gate ]ʷ up j) (bk j)
    where
    bk : ∀ j → C.act [ C.gate₂ C.SWAP-gate ]ʷ (cons (x (suc zero)) (cons (x zero) inner′)) j ≡ z j
    bk zero          = refl
    bk (suc zero)    = refl
    bk (suc (suc y)) = refl
  fin : cons (z zero) (lower z ⊕ scale (z zero) (cons (mask zero) zeros)) ≈s
        cons (x zero) (lower x ⊕ scale (x zero) mask)
  fin zero          = refl
  fin (suc zero)    = refl
  fin (suc (suc y)) = xor-identityʳ _

------------------------------------------------------------------------
-- The fan of a linear map from the controls into the block

Lfan : ∀ k → (State k → State (₄₊ c)) → Word (AGen (₄₊ (k + c)))
Lfan zero    L = ε
Lfan (suc k) L = (Lfan k (λ a → L (cons false a)) ↑ₐ) • fan01 (join k zeros (L e₀))

private
  infixr 4 _∙_
  _∙_ : {s t u : State n} → s ≈s t → t ≈s u → s ≈s u
  (e ∙ f) i = trans (e i) (f i)

  ⊕-resp : {s s′ t t′ : State n} → s ≈s s′ → t ≈s t′ → s ⊕ t ≈s s′ ⊕ t′
  ⊕-resp e f i = cong₂ _xor_ (e i) (f i)

  cons-add : (s t : State n) → cons false (s ⊕ t) ≈s cons false s ⊕ cons false t
  cons-add s t zero    = refl
  cons-add s t (suc j) = refl

  split₀ : (b : Bool) (a : State n) → cons b a ≈s scale b e₀ ⊕ cons false a
  split₀ true  a zero    = refl
  split₀ false a zero    = refl
  split₀ b     a (suc i) = refl

  scale-lin : {L : State (suc n) → State m} → Lin L → ∀ b → L (scale b e₀) ≈s scale b (L e₀)
  scale-lin {L = L} LL true i =
    trans (Lin.resp LL (λ j → ∧-identityʳ (e₀ j)) i) (sym (∧-identityʳ (L e₀ i)))
  scale-lin {L = L} LL false i =
    trans (Lin.resp LL (λ j → ∧-zeroʳ (e₀ j)) i)
      (trans (lin-zero LL i) (sym (∧-zeroʳ (L e₀ i))))

  scale-join : ∀ k b (h : State (₄₊ c)) → scale b (join k zeros h) ≈s join k zeros (scale b h)
  scale-join zero    b h i       = refl
  scale-join (suc k) b h zero    = refl
  scale-join (suc k) b h (suc i) = scale-join k b h i

Lfan-act : ∀ k (L : State k → State (₄₊ c)) → Lin L → ∀ x →
  A⟦ Lfan k L ⟧ x ≈s join k (low k x) (high k x ⊕ L (low k x))
Lfan-act zero L LL x i =
  sym (trans (cong (x i xor_) (trans (Lin.resp LL (λ ()) i) (lin-zero LL i))) (xor-identityʳ (x i)))
Lfan-act {c} (suc k) L LL x =
  A-cong (Lfan k L′ ↑ₐ) (fan01-act m₀ x) ∙ A-↑ (Lfan k L′) x₀ (x′ ⊕ scale x₀ m₀) ∙ step
  where
  x₀ = x zero
  x′ = lower x
  L′ : State k → State (₄₊ c)
  L′ a = L (cons false a)
  LL′ : Lin L′
  LL′ = record
    { add  = λ s t i → trans (Lin.resp LL (cons-add s t) i) (Lin.add LL _ _ i)
    ; resp = λ e i → Lin.resp LL (λ { zero → refl ; (suc j) → e j }) i }
  m₀ = join k zeros (L e₀)
  a′ = low k x′
  h′ = high k x′ ⊕ scale x₀ (L e₀)
  y≈ : x′ ⊕ scale x₀ m₀ ≈s join k a′ h′
  y≈ = ⊕-resp (λ i → sym (join-lh k x′ i)) (scale-join k x₀ (L e₀))
     ∙ (λ i → sym (join-⊕ k a′ zeros (high k x′) (scale x₀ (L e₀)) i))
     ∙ join-resp k (λ i → xor-identityʳ (a′ i)) (λ i → refl)
  inner : A⟦ Lfan k L′ ⟧ (x′ ⊕ scale x₀ m₀) ≈s join k a′ (h′ ⊕ L′ a′)
  inner = A-cong (Lfan k L′) y≈ ∙ Lfan-act k L′ LL′ (join k a′ h′)
        ∙ join-resp k (low-join k a′ h′)
            (⊕-resp (high-join k a′ h′) (Lin.resp LL′ (low-join k a′ h′)))
  last : h′ ⊕ L′ a′ ≈s high k x′ ⊕ L (cons x₀ a′)
  last l = trans (xor-assoc (high k x′ l) (scale x₀ (L e₀) l) (L′ a′ l))
    (cong (high k x′ l xor_)
      (sym (trans (Lin.resp LL (split₀ x₀ a′) l)
        (trans (Lin.add LL (scale x₀ e₀) (cons false a′) l)
          (cong (_xor L′ a′ l) (scale-lin LL x₀ l))))))
  step : cons x₀ (A⟦ Lfan k L′ ⟧ (x′ ⊕ scale x₀ m₀)) ≈s
         join (suc k) (low (suc k) x) (high (suc k) x ⊕ L (low (suc k) x))
  step zero    = refl
  step (suc j) = trans (inner j) (join-resp k (λ _ → refl) last j)

------------------------------------------------------------------------
-- A word that fixes the window

module Fix {k c : ℕ} (S : Word (AGen (₄₊ (k + c))))
  (fixW : ∀ x → low k x ≈s zeros → A⟦ S ⟧ x ≈s x) where

  S-zero : A⟦ S ⟧ zeros ≈s zeros
  S-zero = fixW zeros (low-zeros k)

  SL : Lin A⟦ S ⟧
  SL = word-lin S S-zero

  N : State k → State k
  N a = low k (A⟦ S ⟧ (join k a zeros))

  L : State k → State (₄₊ c)
  L a = high k (A⟦ S ⟧ (join k a zeros))

  private
    join0-lin : Lin (λ (a : State k) → join {c} k a zeros)
    join0-lin = record
      { add  = λ a a′ → join-⊕ k a a′ zeros zeros
      ; resp = λ e → join-resp k e (λ _ → refl) }

    low-lin : Lin (low {c} k)
    low-lin = record { add = low-⊕ k ; resp = low-resp k }

    high-lin : Lin (high {c} k)
    high-lin = record { add = high-⊕ k ; resp = high-resp k }

  NL : Lin N
  NL = lin-∘ low-lin (lin-∘ SL join0-lin)

  LL : Lin L
  LL = lin-∘ high-lin (lin-∘ SL join0-lin)

  N-emb : Emb k k
  N-emb = record
    { f   = N
    ; lin = NL
    ; inj = λ a z i →
        trans (sym (low-join k a zeros i))
          (trans (low-resp k (λ j → sym (A-injective S (fixW _ z) j)) i) (z i))
    }

  decomp : ∀ x → A⟦ S ⟧ x ≈s join k (N (low k x)) (high k x ⊕ L (low k x))
  decomp x =
      A-cong S (λ i → sym (parts i))
    ∙ Lin.add SL (join k a zeros) (join k zeros h)
    ∙ ⊕-resp (λ i → sym (join-lh k (A⟦ S ⟧ (join k a zeros)) i))
             (fixW (join k zeros h) (low-join k zeros h))
    ∙ (λ i → sym (join-⊕ k (N a) zeros (L a) h i))
    ∙ join-resp k (λ i → xor-identityʳ (N a i)) (λ i → xor-comm (L a i) (h i))
    where
    a = low k x
    h = high k x
    parts : join k a zeros ⊕ join k zeros h ≈s x
    parts = (λ i → sym (join-⊕ k a zeros zeros h i))
          ∙ join-resp k (λ i → xor-identityʳ (a i)) (λ i → refl)
          ∙ join-lh k x

  -- The same map, as a word on the controls and a fan into the block.
  S′ : Word (AGen (₄₊ (k + c)))
  S′ = wₐ c (realise N-emb) • Lfan k L

  S′-act : ∀ x → A⟦ S′ ⟧ x ≈s A⟦ S ⟧ x
  S′-act x =
      A-cong (wₐ c (realise N-emb)) (Lfan-act k L LL x)
    ∙ A-w (realise N-emb) (low k x) (high k x ⊕ L (low k x))
    ∙ join-resp k (realise-ok N-emb (low k x)) (λ _ → refl)
    ∙ (λ i → sym (decomp x i))
