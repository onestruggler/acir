------------------------------------------------------------------------
-- Presentations of groups
--
-- A row-operation reading that applies the shortcuts whole
--
-- FastEval's reading applies a circuit gate by gate, and the shortcuts
-- of Syntactics are long words: a Swap is fifteen gates, a CCZ
-- forty-five, each a pass over every entry of the trie of rows.  But a
-- Swap, a CNOT, a Toffoli or an X only permutes the rows, a CZ or a CCZ
-- negates some, and a controlled K adds and subtracts half of them.
-- `view` reads a word as FastEval does except that it recognises those
-- shortcuts, lifted any number of wires, by comparing a subword with the
-- shortcut's own spelling — the candidates chosen by the subword's first
-- gate (`match`) — and `runV` applies each as one operation on the rows
-- (`fastL`).  A word is viewed once, and its view shared between the
-- reading and its count of K's (`sameB`).  About ten times faster than
-- FastEval's on the windows of Four/ and Five/.
--
-- A shortcut's operation is given row by row by a recipe (a row,
-- scaled, or the sum or difference of two), applied by one generic
-- operation (`permK`); that the recipe is the shortcut's matrix, up to
-- a power of γ, is one evaluation at the shortcut's own width
-- (`by-rows`), carried to every placement by Interpretation.localise
-- (`mac-gen`).  `runV-ok` relates the reading to Evaluation's; `SameF`
-- compares two readings, each scaled by the other's count of K's, and
-- `sameF-sem` gives the same semantics; `F-sem`, `F-≡` and `F-op`
-- decide a circuit against an operator or a stored matrix.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.MacroEval where

open import Algebra.Bundles using (CommutativeRing)
import Algebra.Properties.Ring as RingProps
open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Maybe using (Maybe ; just ; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using ([] ; _∷_ ; _++_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Interpretation
  using (⟦_⟧ ; ⟦_⟧ₒ ; ⟦_⟧M ; ⟦⟧-ix ; len ; len-↑ ; localise)
open import Examples.Groups.Clifford+CS.Evaluation
  using (Rows ; rix ; add ; sub ; sc ; rix-add ; rix-sub ; rix-sc ; run ; run-ok ; ⟦⟧R-ix ; by-rows)
open import Examples.Groups.Clifford+CS.FastEval
  using (applyQ ; runQ ; applyQ-ok ; run-Q ; nN ; nK ; ngen ; len-split)
open import Examples.Groups.Clifford+CS.Semantics.Decide using (eqM ; eqM-sound)

open RingProps (CommutativeRing.ring +-*-commutativeRing) using (-‿distribˡ-*)

private
  variable
    k c : ℕ

------------------------------------------------------------------------
-- Recognising a spelling

eqG : (g h : Gen k) → Maybe (g ≡ h)
eqG (gate₀ I-gate)  (gate₀ I-gate)  = just Eq.refl
eqG (gate₁ S-gate)  (gate₁ S-gate)  = just Eq.refl
eqG (gate₁ K-gate)  (gate₁ K-gate)  = just Eq.refl
eqG (gate₂ CS-gate) (gate₂ CS-gate) = just Eq.refl
eqG (g ↥)           (h ↥)           = Maybe.map (Eq.cong _↥) (eqG g h)
eqG _               _               = nothing

private
  both : {A B : Set} {a a′ : A} {b b′ : B} {C : Set} (f : A → B → C) →
         Maybe (a ≡ a′) → Maybe (b ≡ b′) → Maybe (f a b ≡ f a′ b′)
  both f (just p) (just q) = just (Eq.cong₂ f p q)
  both f (just p) nothing  = nothing
  both f nothing  _        = nothing

eqW : (w v : Circuit k) → Maybe (w ≡ v)
eqW [ g ]ʷ    [ h ]ʷ    = Maybe.map (Eq.cong [_]ʷ) (eqG g h)
eqW ε         ε         = just Eq.refl
eqW (w • w′)  (v • v′)  = both _•_ (eqW w v) (eqW w′ v′)
eqW _         _         = nothing

------------------------------------------------------------------------
-- The shortcuts

-- The Toffoli with its target on wire 1, as Five.Resps spells it.
Toff₁ : Circuit (₃₊ k)
Toff₁ = K ↑ • CCZ • K ↑ • iI

data Mac : ∀ {k} → Circuit k → Set where
  mX     : Mac (X {k})
  mCX₀₁  : Mac (CX₀₁ {k})
  mCX₁₀  : Mac (CX₁₀ {k})
  mSwap  : Mac (Swap {k})
  mCZ    : Mac (CZ {k})
  mCK₀₁  : Mac (CK {k})
  mCK₁₀  : Mac (CK₁₀ {k})
  mCCZ   : Mac (CCZ {k})
  mToff₀ : Mac (Toff {k})
  mToff₁ : Mac (Toff₁ {k})
  mToff₂ : Mac (Toffᵗ {k})

private
  try : {w v : Circuit k} → Mac v → Maybe (w ≡ v) → Maybe (Mac w)
  try m (just Eq.refl) = just m
  try m nothing        = nothing

  _<|>_ : {A : Set} → Maybe A → Maybe A → Maybe A
  just a  <|> _ = just a
  nothing <|> m = m
  infixr 4 _<|>_

-- A shortcut, or one lifted.
data MacL : ∀ {n} → Circuit n → Set where
  atM : ∀ {n} {w : Circuit n} → Mac w → MacL w
  upM : ∀ {n} {w : Circuit n} → MacL w → MacL (w ↑)

data Kind : Set where
  kX kCX₀₁ kCX₁₀ kSwap kCZ kCK₀₁ kCK₁₀ kCCZ kToff₀ kToff₁ kToff₂ : Kind

-- The shortcut of a kind at width n, if n is wide enough.
at₀ : Kind → ∀ {n} → Maybe (Σ (Circuit n) MacL)
at₀ kX     {₁₊ k} = just (X , atM mX)
at₀ kCX₀₁  {₂₊ k} = just (CX₀₁ , atM mCX₀₁)
at₀ kCX₁₀  {₂₊ k} = just (CX₁₀ , atM mCX₁₀)
at₀ kSwap  {₂₊ k} = just (Swap , atM mSwap)
at₀ kCZ    {₂₊ k} = just (CZ , atM mCZ)
at₀ kCK₀₁  {₂₊ k} = just (CK , atM mCK₀₁)
at₀ kCK₁₀  {₂₊ k} = just (CK₁₀ , atM mCK₁₀)
at₀ kCCZ   {₃₊ k} = just (CCZ , atM mCCZ)
at₀ kToff₀ {₃₊ k} = just (Toff , atM mToff₀)
at₀ kToff₁ {₃₊ k} = just (Toff₁ , atM mToff₁)
at₀ kToff₂ {₃₊ k} = just (Toffᵗ , atM mToff₂)
at₀ _             = nothing

-- Lifted j wires.
atL : Kind → ℕ → ∀ {n} → Maybe (Σ (Circuit n) MacL)
atL κ zero         = at₀ κ
atL κ (suc j) {₀}    = nothing
atL κ (suc j) {₁₊ n} = lift (atL κ j {n})
  where
  lift : Maybe (Σ (Circuit n) MacL) → Maybe (Σ (Circuit (₁₊ n)) MacL)
  lift nothing        = nothing
  lift (just (e , m)) = just (e ↑ , upM m)

private
  tryL : ∀ {n} {w e : Circuit n} → MacL e → Maybe (w ≡ e) → Maybe (MacL w)
  tryL m (just Eq.refl) = just m
  tryL m nothing        = nothing

  check : ∀ {n} (w : Circuit n) → Maybe (Σ (Circuit n) MacL) → Maybe (MacL w)
  check w nothing        = nothing
  check w (just (e , m)) = tryL m (eqW w e)

tryK : ∀ {n} → Kind → ℕ → (w : Circuit n) → Maybe (MacL w)
tryK κ j w = check w (atL κ j)

-- The first gate, its depth and the gate it lifts.
first : ∀ {n} → Circuit n → Maybe (Gen n)
first [ g ]ʷ  = just g
first ε       = nothing
first (w • v) = first w

depth : Gen k → ℕ
depth (g ↥) = suc (depth g)
depth _     = 0

data Base : Set where
  bK bCS bO : Base

baseOf : Gen k → Base
baseOf (gate₁ K-gate)  = bK
baseOf (gate₂ CS-gate) = bCS
baseOf (g ↥)           = baseOf g
baseOf _               = bO

-- The shortcuts that start with K or CS d wires up: a K is the first
-- gate of an X, CX₁₀ or Toffoli on its wire, of a CX₀₁, Swap or Toff₁
-- one wire down, and of a Toffᵗ two down; a CS of a CZ or controlled K
-- on its wires and of a CCZ one wire down.
private
  candsK₂ candsK₁ candsCS₁ : ∀ {n} (w : Circuit n) → ℕ → Maybe (MacL w)
  candsK₂ w zero    = nothing
  candsK₂ w (suc d) = tryK kToff₂ d w
  candsK₁ w zero    = nothing
  candsK₁ w (suc d) = tryK kCX₀₁ d w <|> tryK kSwap d w <|> tryK kToff₁ d w <|> candsK₂ w d
  candsCS₁ w zero    = nothing
  candsCS₁ w (suc d) = tryK kCCZ d w

  cands : ∀ {n} (w : Circuit n) → Base → ℕ → Maybe (MacL w)
  cands w bK  d = tryK kX d w <|> tryK kCX₁₀ d w <|> tryK kToff₀ d w <|> candsK₁ w d
  cands w bCS d = tryK kCZ d w <|> tryK kCK₀₁ d w <|> tryK kCK₁₀ d w <|> candsCS₁ w d
  cands w bO  d = nothing

  disp : ∀ {n} (w : Circuit n) → Maybe (Gen n) → Maybe (MacL w)
  disp w nothing  = nothing
  disp w (just g) = cands w (baseOf g) (depth g)

match : ∀ {n} (w : Circuit n) → Maybe (MacL w)
match w = disp w (first w)

------------------------------------------------------------------------
-- Recipes: a row of a shortcut's operator

data Recipe (m : ℕ) : Set where
  same  : Bits m → Recipe m              -- row z
  scl   : 𝔽 → Bits m → Recipe m          -- s times row z
  plus  : Bits m → Bits m → Recipe m     -- row z plus row z′
  minus : Bits m → Bits m → Recipe m     -- row z minus row z′

-- As a row of an operator.
rowv : ∀ {m} → Recipe m → Bits m → 𝔽
rowv (same z)     u = δb z u
rowv (scl s z)    u = s * δb z u
rowv (plus z z′)  u = δb z u + δb z′ u
rowv (minus z z′) u = δb z u - δb z′ u

Pmat : ∀ {m} → (Bits m → Recipe m) → Mat m
Pmat ρ = matOf (λ x z → rowv (ρ x) z)

-- As an operation on a function of the rows.
evR : ∀ {m} → Recipe m → (Bits m → 𝔽) → 𝔽
evR (same z)     f = f z
evR (scl s z)    f = s * f z
evR (plus z z′)  f = f z + f z′
evR (minus z z′) f = f z - f z′

-- As an operation on a trie of rows.
applyR : ∀ {m} {k} c → Recipe m → (Bits m → Rows k c) → Rows k c
applyR         c (same z)     G = G z
applyR {k = k} c (scl s z)    G = sc {k} c s (G z)
applyR {k = k} c (plus z z′)  G = add {k} c (G z) (G z′)
applyR {k = k} c (minus z z′) G = sub {k} c (G z) (G z′)

-- The trie of rows at depth m, and back.
getK : ∀ m {k} → Rows (m +ℕ k) c → Bits m → Rows k c
getK ₀      R       []          = R
getK (₁₊ m) (l , r) (false ∷ u) = getK m l u
getK (₁₊ m) (l , r) (true  ∷ u) = getK m r u

tabK : ∀ m {k} → (Bits m → Rows k c) → Rows (m +ℕ k) c
tabK ₀      F = F []
tabK (₁₊ m) F = tabK m (λ u → F (false ∷ u)) , tabK m (λ u → F (true ∷ u))

permK : ∀ m {k} c → (Bits m → Recipe m) → Rows (m +ℕ k) c → Rows (m +ℕ k) c
permK m {k} c ρ R = tabK m {k} (λ u → applyR {k = k} c (ρ u) (getK m {k} R))

------------------------------------------------------------------------
-- Their row operations

private
  T F : Bool
  T = true
  F = false

ρX : Bits 1 → Recipe 1
ρX (b ∷ []) = same (not b ∷ [])

ρCX₀₁ ρCX₁₀ ρSwap ρCZ ρCK₀₁ ρCK₁₀ : Bits 2 → Recipe 2
ρCX₀₁ (true ∷ b ∷ [])     = same (T ∷ not b ∷ [])
ρCX₀₁ u                   = same u
ρCX₁₀ (a ∷ true ∷ [])     = same (not a ∷ T ∷ [])
ρCX₁₀ u                   = same u
ρSwap (a ∷ b ∷ [])        = same (b ∷ a ∷ [])
ρCZ (true ∷ true ∷ [])    = scl -1# (T ∷ T ∷ [])
ρCZ u                     = same u
ρCK₀₁ (false ∷ b ∷ [])    = scl γ (F ∷ b ∷ [])
ρCK₀₁ (true ∷ false ∷ []) = plus (T ∷ F ∷ []) (T ∷ T ∷ [])
ρCK₀₁ (true ∷ true ∷ [])  = minus (T ∷ F ∷ []) (T ∷ T ∷ [])
ρCK₁₀ (a ∷ false ∷ [])    = scl γ (a ∷ F ∷ [])
ρCK₁₀ (false ∷ true ∷ []) = plus (F ∷ T ∷ []) (T ∷ T ∷ [])
ρCK₁₀ (true ∷ true ∷ [])  = minus (F ∷ T ∷ []) (T ∷ T ∷ [])

ρCCZ ρToff₀ ρToff₁ ρToff₂ : Bits 3 → Recipe 3
ρCCZ (true ∷ true ∷ true ∷ []) = scl -1# (T ∷ T ∷ T ∷ [])
ρCCZ u                         = same u
ρToff₀ (a ∷ true ∷ true ∷ [])  = same (not a ∷ T ∷ T ∷ [])
ρToff₀ u                       = same u
ρToff₁ (true ∷ b ∷ true ∷ [])  = same (T ∷ not b ∷ T ∷ [])
ρToff₁ u                       = same u
ρToff₂ (true ∷ true ∷ b ∷ [])  = same (T ∷ T ∷ not b ∷ [])
ρToff₂ u                       = same u

fastOp : ∀ {n} c {w : Circuit n} → Mac w → Rows n c → Rows n c
fastOp c (mX {k})     = permK 1 {k} c ρX
fastOp c (mCX₀₁ {k})  = permK 2 {k} c ρCX₀₁
fastOp c (mCX₁₀ {k})  = permK 2 {k} c ρCX₁₀
fastOp c (mSwap {k})  = permK 2 {k} c ρSwap
fastOp c (mCZ {k})    = permK 2 {k} c ρCZ
fastOp c (mCK₀₁ {k})  = permK 2 {k} c ρCK₀₁
fastOp c (mCK₁₀ {k})  = permK 2 {k} c ρCK₁₀
fastOp c (mCCZ {k})   = permK 3 {k} c ρCCZ
fastOp c (mToff₀ {k}) = permK 3 {k} c ρToff₀
fastOp c (mToff₁ {k}) = permK 3 {k} c ρToff₁
fastOp c (mToff₂ {k}) = permK 3 {k} c ρToff₂

-- The power of γ between a shortcut's reading in Evaluation and its
-- recipe (its length, but for a controlled K, whose recipe is γ times
-- its operator), and the K's the recipe leaves.
gMac kMac : ∀ {n} {w : Circuit n} → Mac w → ℕ
gMac mX     = 5
gMac mCX₀₁  = 5
gMac mCX₁₀  = 5
gMac mSwap  = 15
gMac mCZ    = 2
gMac mCK₀₁  = 8
gMac mCK₁₀  = 8
gMac mCCZ   = 45
gMac mToff₀ = 48
gMac mToff₁ = 48
gMac mToff₂ = 48
kMac mCK₀₁ = 1
kMac mCK₁₀ = 1
kMac _     = 0

------------------------------------------------------------------------
-- The reading

fastL : ∀ {n} c {w : Circuit n} → MacL w → Rows n c → Rows n c
fastL c (atM m) R = fastOp c m R
fastL c (upM m)   R = fastL c m (proj₁ R) , fastL c m (proj₂ R)

gL kL : ∀ {n} {w : Circuit n} → MacL w → ℕ
gL (atM m) = gMac m
gL (upM m)   = gL m
kL (atM m) = kMac m
kL (upM m)   = kL m

-- A word as shortcuts, gates and products.
data View : ∀ {n} → Circuit n → Set where
  vmac  : ∀ {n} {w : Circuit n} → MacL w → View w
  vseq  : ∀ {n} {w v : Circuit n} → View w → View v → View (w • v)
  vgate : ∀ {n} (g : Gen n) → View [ g ]ʷ
  veps  : ∀ {n} → View (ε {X = Gen n})

mutual
  view : ∀ {n} (w : Circuit n) → View w
  view w = viewM w (match w)

  viewM : ∀ {n} (w : Circuit n) → Maybe (MacL w) → View w
  viewM w       (just m) = vmac m
  viewM [ g ]ʷ  nothing  = vgate g
  viewM ε       nothing  = veps
  viewM (w • v) nothing  = vseq (view w) (view v)

runV : ∀ {n} c {w : Circuit n} → View w → Rows n c → Rows n c
runV c (vmac m)   R = fastL c m R
runV c (vseq a b) R = runV c a (runV c b R)
runV c (vgate g)  R = applyQ c g R
runV c veps       R = R

matV : ∀ {n} {w : Circuit n} → View w → Mat n
matV {n} vw = mat (runV n vw (entries (idM {n})))

-- The K gates the reading applies as K.
kgenF : Gen k → ℕ
kgenF (gate₁ K-gate) = 1
kgenF (g ↥)          = kgenF g
kgenF _              = 0

-- The K's the reading leaves, and the power of γ between Evaluation's
-- reading and this one.
kV gV : ∀ {n} {w : Circuit n} → View w → ℕ
kV (vmac m)   = kL m
kV (vseq a b) = kV a +ℕ kV b
kV (vgate g)  = kgenF g
kV veps       = 0
gV (vmac m)   = gL m
gV (vseq a b) = gV a +ℕ gV b
gV (vgate g)  = ngen g
gV veps       = 0

⟦_⟧F : Circuit k → Mat k
⟦ w ⟧F = matV (view w)

nKF gF : Circuit k → ℕ
nKF w = kV (view w)
gF w = gV (view w)

-- Two circuits with the same matrix, decided on these readings: each
-- word viewed once, its view shared by its reading and its count.
sameV : ∀ {n} {u v : Circuit n} → View u → View v → Bool
sameV vu vv = eqM (scaleM (γ^ kV vv) (matV vu)) (scaleM (γ^ kV vu) (matV vv))

sameB : Circuit k → Circuit k → Bool
sameB u v = sameV (view u) (view v)

SameF : Circuit k → Circuit k → Set
SameF u v = sameB u v ≡ true

-- A circuit against a stored matrix, and against an operator.
chkV : ∀ {n} {w : Circuit n} → View w → ℕ → Mat n → Bool
chkV vw l M = eqM (scaleM (γ^ l) (matV vw)) (scaleM (γ^ kV vw) M)

ChkF : Circuit k → ℕ → Mat k → Set
ChkF w l M = chkV (view w) l M ≡ true

chkOpV : ∀ {n} {w : Circuit n} → View w → ℕ → Op n → Bool
chkOpV vw l T = eqM (scaleM (γ^ l) (matV vw)) (matOf (γ^ kV vw · T))

ChkOp : Circuit k → ℕ → Op k → Set
ChkOp w l T = chkOpV (view w) l T ≡ true

------------------------------------------------------------------------
-- Recipes are right

private
  Σ-cδ : ∀ {n} (a : 𝔽) (x : Bits n) (f : Bits n → 𝔽) → Σb (λ z → (a * δb x z) * f z) ≡ a * f x
  Σ-cδ a x f =
    Eq.trans (Σ-cong {f = λ z → (a * δb x z) * f z} {g = λ z → a * (δb x z * f z)}
                     (λ z → *-assoc a (δb x z) (f z)))
      (Eq.trans (Σ-scaleˡ a (λ z → δb x z * f z)) (Eq.cong (a *_) (Σ-δˡ x f)))

  m1 : ∀ a → -1# * a ≡ - a
  m1 a = Eq.trans (Eq.sym (-‿distribˡ-* 1# a)) (-‿cong (*-identityˡ a))

  Σ-neg : ∀ {n} (g : Bits n → 𝔽) → Σb (λ z → - g z) ≡ - Σb g
  Σ-neg g = Eq.trans (Σ-cong {f = λ z → - g z} {g = λ z → -1# * g z} (λ z → Eq.sym (m1 (g z))))
              (Eq.trans (Σ-scaleˡ -1# g) (m1 (Σb g)))

Σ-rowv : ∀ {m} (r : Recipe m) (f : Bits m → 𝔽) → Σb (λ u → rowv r u * f u) ≡ evR r f
Σ-rowv (same z)     f = Σ-δˡ z f
Σ-rowv (scl s z)    f = Σ-cδ s z f
Σ-rowv (plus z z′)  f =
  Eq.trans (Σ-cong {f = λ u → (δb z u + δb z′ u) * f u} {g = λ u → δb z u * f u + δb z′ u * f u}
                   (λ u → *-distribʳ-+ (f u) (δb z u) (δb z′ u)))
    (Eq.trans (Σ-add (λ u → δb z u * f u) (λ u → δb z′ u * f u))
              (Eq.cong₂ _+_ (Σ-δˡ z f) (Σ-δˡ z′ f)))
Σ-rowv (minus z z′) f =
  Eq.trans (Σ-cong {f = λ u → (δb z u - δb z′ u) * f u} {g = λ u → δb z u * f u + - (δb z′ u * f u)}
                   (λ u → Eq.trans (*-distribʳ-+ (f u) (δb z u) (- δb z′ u))
                                   (Eq.cong (δb z u * f u +_) (Eq.sym (-‿distribˡ-* (δb z′ u) (f u))))))
    (Eq.trans (Σ-add (λ u → δb z u * f u) (λ u → - (δb z′ u * f u)))
              (Eq.cong₂ _+_ (Σ-δˡ z f) (Eq.trans (Σ-neg (λ u → δb z′ u * f u)) (-‿cong (Σ-δˡ z′ f)))))

private
  evR-cong : ∀ {m} (r : Recipe m) {f g : Bits m → 𝔽} → (∀ u → f u ≡ g u) → evR r f ≡ evR r g
  evR-cong (same z)     e = e z
  evR-cong (scl s z)    e = Eq.cong (s *_) (e z)
  evR-cong (plus z z′)  e = Eq.cong₂ _+_ (e z) (e z′)
  evR-cong (minus z z′) e = Eq.cong₂ _-_ (e z) (e z′)

  rix-applyR : ∀ {m} {k} c (r : Recipe m) (G : Bits m → Rows k c) x y →
               rix {k} {c} (applyR {k = k} c r G) x y ≡ evR r (λ u → rix {k} {c} (G u) x y)
  rix-applyR         c (same z)     G x y = Eq.refl
  rix-applyR {k = k} c (scl s z)    G x y = rix-sc {k} c s (G z) x y
  rix-applyR {k = k} c (plus z z′)  G x y = rix-add {k} c (G z) (G z′) x y
  rix-applyR {k = k} c (minus z z′) G x y = rix-sub {k} c (G z) (G z′) x y

  rix-getK : ∀ m {k} (R : Rows (m +ℕ k) c) (u : Bits m) (x : Bits k) y →
             rix {m +ℕ k} {c} R (u ++ x) y ≡ rix {k} {c} (getK m {k} R u) x y
  rix-getK ₀      R       []          x y = Eq.refl
  rix-getK (₁₊ m) (l , r) (false ∷ u) x y = rix-getK m l u x y
  rix-getK (₁₊ m) (l , r) (true  ∷ u) x y = rix-getK m r u x y

  rix-tabK : ∀ m {k} (G : Bits m → Rows k c) (u : Bits m) (x : Bits k) y →
             rix {m +ℕ k} {c} (tabK m {k} G) (u ++ x) y ≡ rix {k} {c} (G u) x y
  rix-tabK ₀      G []          x y = Eq.refl
  rix-tabK (₁₊ m) G (false ∷ u) x y = rix-tabK m (λ v → G (false ∷ v)) u x y
  rix-tabK (₁₊ m) G (true  ∷ u) x y = rix-tabK m (λ v → G (true ∷ v)) u x y

permK-ok : ∀ m {k} c ρ (R : Rows (m +ℕ k) c) (u : Bits m) (x : Bits k) y →
           rix {m +ℕ k} {c} (permK m {k} c ρ R) (u ++ x) y ≡ evR (ρ u) (λ z → rix {m +ℕ k} {c} R (z ++ x) y)
permK-ok m {k} c ρ R u x y =
  Eq.trans (rix-tabK m {k} (λ v → applyR {k = k} c (ρ v) (getK m {k} R)) u x y)
    (Eq.trans (rix-applyR {k = k} c (ρ u) (getK m {k} R) x y)
              (evR-cong (ρ u) (λ z → Eq.sym (rix-getK {c = c} m {k} R z x y))))

-- A sum over the bottom m wires and the rest, against an embedded operator.
Σ-emb : ∀ m {k} (A : Op m) (u : Bits m) (x : Bits k) (G : Bits (m +ℕ k) → 𝔽) →
        Σb (λ z → tensor A Idₒ (u ++ x) z * G z) ≡ Σb (λ z → A u z * G (z ++ x))
Σ-emb ₀      A []      x G = Σ-cδ (A [] []) x G
Σ-emb (₁₊ m) A (a ∷ u) x G =
  Eq.cong₂ _+_ (Σ-emb m (λ s z → A (a ∷ s) (false ∷ z)) u x (λ z → G (false ∷ z)))
               (Σ-emb m (λ s z → A (a ∷ s) (true ∷ z)) u x (λ z → G (true ∷ z)))

-- A shortcut whose matrix at its own width is γ^ g times its recipe's:
-- so at every width.
mac-gen : ∀ {m} (M₀ : Circuit m) (ρ : Bits m → Recipe m) (g : ℕ) →
          ⟦ M₀ ⟧M ≡ scaleM (γ^ g) (Pmat ρ) →
          ∀ {k} (M : Circuit (m +ℕ k)) → M₀ ↓ᵏ k ≡ M →
          ∀ c (R : Rows (m +ℕ k) c) (u : Bits m) (x : Bits k) y →
          rix {m +ℕ k} {c} (run c M R) (u ++ x) y ≡ γ^ g * rix {m +ℕ k} {c} (permK m {k} c ρ R) (u ++ x) y
mac-gen {m} M₀ ρ g e {k} _ Eq.refl c R u x y = begin
  rix {m +ℕ k} {c} (run c (M₀ ↓ᵏ k) R) (u ++ x) y
    ≡⟨ run-ok c (M₀ ↓ᵏ k) R (u ++ x) y ⟩
  Σb (λ z → ⟦ M₀ ↓ᵏ k ⟧ₒ (u ++ x) z * rix {m +ℕ k} {c} R z y)
    ≡⟨ Σ-cong {f = λ z → ⟦ M₀ ↓ᵏ k ⟧ₒ (u ++ x) z * rix {m +ℕ k} {c} R z y}
              {g = λ z → tensor (ix ⟦ M₀ ⟧M) Idₒ (u ++ x) z * rix {m +ℕ k} {c} R z y}
              (λ z → Eq.cong (_* rix {m +ℕ k} {c} R z y) (localise {n = k} M₀ (u ++ x) z)) ⟩
  Σb (λ z → tensor (ix ⟦ M₀ ⟧M) Idₒ (u ++ x) z * rix {m +ℕ k} {c} R z y)
    ≡⟨ Σ-emb m (ix ⟦ M₀ ⟧M) u x (λ z → rix {m +ℕ k} {c} R z y) ⟩
  Σb (λ z → ix ⟦ M₀ ⟧M u z * rix {m +ℕ k} {c} R (z ++ x) y)
    ≡⟨ Σ-cong {f = λ z → ix ⟦ M₀ ⟧M u z * rix {m +ℕ k} {c} R (z ++ x) y}
              {g = λ z → γ^ g * (rowv (ρ u) z * rix {m +ℕ k} {c} R (z ++ x) y)}
              (λ z → Eq.trans (Eq.cong (_* rix {m +ℕ k} {c} R (z ++ x) y) (entry z))
                              (*-assoc (γ^ g) (rowv (ρ u) z) (rix {m +ℕ k} {c} R (z ++ x) y))) ⟩
  Σb (λ z → γ^ g * (rowv (ρ u) z * rix {m +ℕ k} {c} R (z ++ x) y))
    ≡⟨ Σ-scaleˡ (γ^ g) (λ z → rowv (ρ u) z * rix {m +ℕ k} {c} R (z ++ x) y) ⟩
  γ^ g * Σb (λ z → rowv (ρ u) z * rix {m +ℕ k} {c} R (z ++ x) y)
    ≡⟨ Eq.cong (γ^ g *_) (Σ-rowv (ρ u) (λ z → rix {m +ℕ k} {c} R (z ++ x) y)) ⟩
  γ^ g * evR (ρ u) (λ z → rix {m +ℕ k} {c} R (z ++ x) y)
    ≡⟨ Eq.cong (γ^ g *_) (Eq.sym (permK-ok m {k} c ρ R u x y)) ⟩
  γ^ g * rix {m +ℕ k} {c} (permK m {k} c ρ R) (u ++ x) y ∎
  where
  open Eq.≡-Reasoning
  entry : ∀ z → ix ⟦ M₀ ⟧M u z ≡ γ^ g * rowv (ρ u) z
  entry z = Eq.trans (Eq.cong (λ M → ix M u z) e)
              (Eq.trans (ix-scaleM (γ^ g) (Pmat ρ) u z)
                        (Eq.cong (γ^ g *_) (ix-matOf (λ s v → rowv (ρ s) v) u z)))

-- The recipes, each one evaluation at the shortcut's width.
private
  eX     = by-rows (X {₀})      {scaleM (γ^ 5)  (Pmat ρX)}     Eq.refl
  eCX₀₁  = by-rows (CX₀₁ {₀})   {scaleM (γ^ 5)  (Pmat ρCX₀₁)}  Eq.refl
  eCX₁₀  = by-rows (CX₁₀ {₀})   {scaleM (γ^ 5)  (Pmat ρCX₁₀)}  Eq.refl
  eSwap  = by-rows (Swap {₀})   {scaleM (γ^ 15) (Pmat ρSwap)}  Eq.refl
  eCZ    = by-rows (CZ {₀})     {scaleM (γ^ 2)  (Pmat ρCZ)}    Eq.refl
  eCK₀₁  = by-rows (CK {₀})     {scaleM (γ^ 8)  (Pmat ρCK₀₁)}  Eq.refl
  eCK₁₀  = by-rows (CK₁₀ {₀})   {scaleM (γ^ 8)  (Pmat ρCK₁₀)}  Eq.refl
  eCCZ   = by-rows (CCZ {₀})    {scaleM (γ^ 45) (Pmat ρCCZ)}   Eq.refl
  eToff₀ = by-rows (Toff {₀})   {scaleM (γ^ 48) (Pmat ρToff₀)} Eq.refl
  eToff₁ = by-rows (Toff₁ {₀})  {scaleM (γ^ 48) (Pmat ρToff₁)} Eq.refl
  eToff₂ = by-rows (Toffᵗ {₀})  {scaleM (γ^ 48) (Pmat ρToff₂)} Eq.refl

mac-ok : ∀ {n} c {w : Circuit n} (m : Mac w) (R : Rows n c) x y →
         rix {n} {c} (run c w R) x y ≡ γ^ (gMac m) * rix {n} {c} (fastOp c m R) x y
mac-ok c (mX {k}) R (a ∷ x)         y = mac-gen (X {₀}) ρX 5 eX (X {k}) Eq.refl c R (a ∷ []) x y
mac-ok c (mCX₀₁ {k}) R (a ∷ b ∷ x)     y = mac-gen (CX₀₁ {₀}) ρCX₀₁ 5 eCX₀₁ (CX₀₁ {k}) Eq.refl c R (a ∷ b ∷ []) x y
mac-ok c (mCX₁₀ {k}) R (a ∷ b ∷ x)     y = mac-gen (CX₁₀ {₀}) ρCX₁₀ 5 eCX₁₀ (CX₁₀ {k}) Eq.refl c R (a ∷ b ∷ []) x y
mac-ok c (mSwap {k}) R (a ∷ b ∷ x)     y = mac-gen (Swap {₀}) ρSwap 15 eSwap (Swap {k}) Eq.refl c R (a ∷ b ∷ []) x y
mac-ok c (mCZ {k}) R (a ∷ b ∷ x)     y = mac-gen (CZ {₀}) ρCZ 2 eCZ (CZ {k}) Eq.refl c R (a ∷ b ∷ []) x y
mac-ok c (mCK₀₁ {k}) R (a ∷ b ∷ x)     y = mac-gen (CK {₀}) ρCK₀₁ 8 eCK₀₁ (CK {k}) Eq.refl c R (a ∷ b ∷ []) x y
mac-ok c (mCK₁₀ {k}) R (a ∷ b ∷ x)     y = mac-gen (CK₁₀ {₀}) ρCK₁₀ 8 eCK₁₀ (CK₁₀ {k}) Eq.refl c R (a ∷ b ∷ []) x y
mac-ok c (mCCZ {k}) R (a ∷ b ∷ d ∷ x) y = mac-gen (CCZ {₀}) ρCCZ 45 eCCZ (CCZ {k}) Eq.refl c R (a ∷ b ∷ d ∷ []) x y
mac-ok c (mToff₀ {k}) R (a ∷ b ∷ d ∷ x) y = mac-gen (Toff {₀}) ρToff₀ 48 eToff₀ (Toff {k}) Eq.refl c R (a ∷ b ∷ d ∷ []) x y
mac-ok c (mToff₁ {k}) R (a ∷ b ∷ d ∷ x) y = mac-gen (Toff₁ {₀}) ρToff₁ 48 eToff₁ (Toff₁ {k}) Eq.refl c R (a ∷ b ∷ d ∷ []) x y
mac-ok c (mToff₂ {k}) R (a ∷ b ∷ d ∷ x) y = mac-gen (Toffᵗ {₀}) ρToff₂ 48 eToff₂ (Toffᵗ {k}) Eq.refl c R (a ∷ b ∷ d ∷ []) x y

------------------------------------------------------------------------
-- The reading is Evaluation's, up to a power of γ

private
  -- A word one wire up acts on the two halves of the rows.
  run-↑ : ∀ {k} c (v : Circuit k) (l r : Rows k c) → run c (v ↑) (l , r) ≡ (run c v l , run c v r)
  run-↑ c [ g ]ʷ  l r = Eq.refl
  run-↑ c ε       l r = Eq.refl
  run-↑ c (w • v) l r =
    Eq.trans (Eq.cong (run c (w ↑)) (run-↑ c v l r)) (run-↑ c w (run c v l) (run c v r))

  -- Evaluation's reading is linear.
  run-lin : ∀ {n} c (w : Circuit n) s (R R′ : Rows n c) →
            (∀ x y → rix {n} {c} R x y ≡ s * rix {n} {c} R′ x y) →
            ∀ x y → rix {n} {c} (run c w R) x y ≡ s * rix {n} {c} (run c w R′) x y
  run-lin {n} c w s R R′ h x y =
    Eq.trans (run-ok c w R x y)
      (Eq.trans (Σ-cong {f = λ z → ⟦ w ⟧ₒ x z * rix {n} {c} R z y} {g = λ z → s * (⟦ w ⟧ₒ x z * rix {n} {c} R′ z y)}
                        (λ z → Eq.trans (Eq.cong (⟦ w ⟧ₒ x z *_) (h z y))
                                 (Eq.trans (Eq.sym (*-assoc (⟦ w ⟧ₒ x z) s (rix {n} {c} R′ z y)))
                                   (Eq.trans (Eq.cong (_* rix {n} {c} R′ z y) (*-comm (⟦ w ⟧ₒ x z) s))
                                             (*-assoc s (⟦ w ⟧ₒ x z) (rix {n} {c} R′ z y))))))
        (Eq.trans (Σ-scaleˡ s (λ z → ⟦ w ⟧ₒ x z * rix {n} {c} R′ z y))
                  (Eq.cong (s *_) (Eq.sym (run-ok c w R′ x y)))))

  g0 : ∀ a → a ≡ γ^ 0 * a
  g0 a = Eq.sym (*-identityˡ a)

  gg : ∀ m n a → γ^ n * (γ^ m * a) ≡ γ^ (m +ℕ n) * a
  gg m n a = Eq.trans (Eq.sym (*-assoc (γ^ n) (γ^ m) a))
               (Eq.cong (_* a) (Eq.trans (*-comm (γ^ n) (γ^ m)) (Eq.sym (γ^-+ m n))))

macL-ok : ∀ {n} c {w : Circuit n} (m : MacL w) (R : Rows n c) x y →
          rix {n} {c} (run c w R) x y ≡ γ^ (gL m) * rix {n} {c} (fastL c m R) x y
macL-ok c (atM m) R x y = mac-ok c m R x y
macL-ok c (upM {n} {w} m) (l , r) (false ∷ x) y =
  Eq.trans (Eq.cong (λ T → rix {₁₊ n} {c} T (false ∷ x) y) (run-↑ c w l r)) (macL-ok c m l x y)
macL-ok c (upM {n} {w} m) (l , r) (true ∷ x) y =
  Eq.trans (Eq.cong (λ T → rix {₁₊ n} {c} T (true ∷ x) y) (run-↑ c w l r)) (macL-ok c m r x y)

runV-ok : ∀ {n} c {w : Circuit n} (vw : View w) (R : Rows n c) x y →
          rix {n} {c} (run c w R) x y ≡ γ^ (gV vw) * rix {n} {c} (runV c vw R) x y
runV-ok c (vmac m) R x y = macL-ok c m R x y
runV-ok {n} c (vseq {w = w} {v} a b) R x y =
  Eq.trans (run-lin c w (γ^ gV b) (run c v R) (runV c b R) (runV-ok c b R) x y)
    (Eq.trans (Eq.cong (γ^ gV b *_) (runV-ok c a (runV c b R) x y))
              (gg (gV a) (gV b) (rix {n} {c} (runV c a (runV c b R)) x y)))
runV-ok c (vgate g) R x y = applyQ-ok c g R x y
runV-ok {n} c veps R x y = g0 (rix {n} {c} R x y)

------------------------------------------------------------------------
-- The same semantics

private
  shuffle : ∀ a b d e → (a +ℕ b) +ℕ (d +ℕ e) ≡ (a +ℕ d) +ℕ (b +ℕ e)
  shuffle a b d e =
    Eq.trans (ℕP.+-assoc a b (d +ℕ e))
      (Eq.trans (Eq.cong (a +ℕ_) (Eq.trans (Eq.sym (ℕP.+-assoc b d e))
                                   (Eq.trans (Eq.cong (_+ℕ e) (ℕP.+-comm b d)) (ℕP.+-assoc d b e))))
                (Eq.sym (ℕP.+-assoc a d (b +ℕ e))))

  len-gen : (g : Gen k) → 1 ≡ kgenF g +ℕ ngen g
  len-gen (gate₀ I-gate)  = Eq.refl
  len-gen (gate₁ S-gate)  = Eq.refl
  len-gen (gate₁ K-gate)  = Eq.refl
  len-gen (gate₂ CS-gate) = Eq.refl
  len-gen (g ↥)           = len-gen g

  len-mac : ∀ {n} {w : Circuit n} (m : Mac w) → len w ≡ kMac m +ℕ gMac m
  len-mac mX     = Eq.refl
  len-mac mCX₀₁  = Eq.refl
  len-mac mCX₁₀  = Eq.refl
  len-mac mSwap  = Eq.refl
  len-mac mCZ    = Eq.refl
  len-mac mCK₀₁  = Eq.refl
  len-mac mCK₁₀  = Eq.refl
  len-mac mCCZ   = Eq.refl
  len-mac mToff₀ = Eq.refl
  len-mac mToff₁ = Eq.refl
  len-mac mToff₂ = Eq.refl

len-L : ∀ {n} {w : Circuit n} (m : MacL w) → len w ≡ kL m +ℕ gL m
len-L (atM m)       = len-mac m
len-L (upM {w = w} m) = Eq.trans (len-↑ w) (len-L m)

len-V : ∀ {n} {w : Circuit n} (vw : View w) → len w ≡ kV vw +ℕ gV vw
len-V (vmac m)   = len-L m
len-V (vseq a b) = Eq.trans (Eq.cong₂ _+ℕ_ (len-V a) (len-V b)) (shuffle (kV a) (gV a) (kV b) (gV b))
len-V (vgate g)  = len-gen g
len-V veps       = Eq.refl

len-F : (w : Circuit k) → len w ≡ nKF w +ℕ gF w
len-F w = len-V (view w)

-- At its own width.
V-ix : ∀ {k} {w : Circuit k} (vw : View w) → ∀ (x y : Bits k) → ⟦ w ⟧ₒ x y ≡ γ^ gV vw * ix (matV vw) x y
V-ix {k} {w} vw x y = Eq.trans (⟦⟧R-ix w x y) (runV-ok k vw (entries (idM {k})) x y)

F-ix : (w : Circuit k) → ∀ (x y : Bits k) → ⟦ w ⟧ₒ x y ≡ γ^ gF w * ix ⟦ w ⟧F x y
F-ix w = V-ix (view w)

private
  -- (a b) (c q) = (b c) (a q)
  sw : ∀ a b d q → (a * b) * (d * q) ≡ (b * d) * (a * q)
  sw a b d q = Eq.trans (Eq.cong (_* (d * q)) (*-comm a b)) (*-cross b a d q)

-- Two views with the same reading, up to their K's: the same semantics.
sameV-sem : ∀ {k} {u v : Circuit k} (vu : View u) (vv : View v) → sameV vu vv ≡ true → ⟦ u ⟧ ~ ⟦ v ⟧
sameV-sem {u = u} {v} vu vv e x y = begin
  γ^ len v * ⟦ u ⟧ₒ x y
    ≡⟨ Eq.cong₂ _*_ (Eq.trans (Eq.cong γ^_ (len-V vv)) (γ^-+ (kV vv) (gV vv))) (V-ix vu x y) ⟩
  (A * B) * (C * Fu)
    ≡⟨ sw A B C Fu ⟩
  (B * C) * (A * Fu)
    ≡⟨ Eq.cong ((B * C) *_) E ⟩
  (B * C) * (D * Fv)
    ≡⟨ Eq.cong (_* (D * Fv)) (*-comm B C) ⟩
  (C * B) * (D * Fv)
    ≡⟨ Eq.sym (sw D C B Fv) ⟩
  (D * C) * (B * Fv)
    ≡⟨ Eq.sym (Eq.cong₂ _*_ (Eq.trans (Eq.cong γ^_ (len-V vu)) (γ^-+ (kV vu) (gV vu))) (V-ix vv x y)) ⟩
  γ^ len u * ⟦ v ⟧ₒ x y ∎
  where
  open Eq.≡-Reasoning
  A = γ^ kV vv
  B = γ^ gV vv
  C = γ^ gV vu
  D = γ^ kV vu
  Fu = ix (matV vu) x y
  Fv = ix (matV vv) x y
  e′ : eqM (scaleM A (matV vu)) (scaleM D (matV vv)) ≡ true
  e′ = e
  E : A * Fu ≡ D * Fv
  E = Eq.trans (Eq.sym (ix-scaleM A (matV vu) x y))
        (Eq.trans (ix-≡ (eqM-sound (scaleM A (matV vu)) (scaleM D (matV vv)) e′) x y) (ix-scaleM D (matV vv) x y))

sameF-sem : (u v : Circuit k) → SameF u v → ⟦ u ⟧ ~ ⟦ v ⟧
sameF-sem u v = sameV-sem (view u) (view v)

private
  lcomm : ∀ a b d → a * (b * d) ≡ b * (a * d)
  lcomm a b d = Eq.trans (Eq.sym (*-assoc a b d)) (Eq.trans (Eq.cong (_* d) (*-comm a b)) (*-assoc b a d))

-- A circuit against any operator: γ^ l ⟦ w ⟧F is γ^ (nKF w) T.
F-sem : (w : Circuit k) (l : ℕ) (T : Op k) →
        (∀ (x y : Bits k) → γ^ l * ix ⟦ w ⟧F x y ≡ γ^ nKF w * T x y) → ⟦ w ⟧ ~ (l , T)
F-sem w l T h x y = begin
  γ^ l * ⟦ w ⟧ₒ x y            ≡⟨ Eq.cong (γ^ l *_) (F-ix w x y) ⟩
  γ^ l * (γ^ gF w * Fw)         ≡⟨ lcomm (γ^ l) (γ^ gF w) Fw ⟩
  γ^ gF w * (γ^ l * Fw)         ≡⟨ Eq.cong (γ^ gF w *_) (h x y) ⟩
  γ^ gF w * (γ^ nKF w * T x y)  ≡⟨ lcomm (γ^ gF w) (γ^ nKF w) (T x y) ⟩
  γ^ nKF w * (γ^ gF w * T x y)  ≡⟨ Eq.sym (*-assoc (γ^ nKF w) (γ^ gF w) (T x y)) ⟩
  (γ^ nKF w * γ^ gF w) * T x y  ≡⟨ Eq.cong (_* T x y) (Eq.sym (Eq.trans (Eq.cong γ^_ (len-F w))
                                                                  (γ^-+ (nKF w) (gF w)))) ⟩
  γ^ len w * T x y ∎
  where
  open Eq.≡-Reasoning
  Fw = ix ⟦ w ⟧F x y

-- The same against a stored matrix, as the stored reading's equation.
F-≡ : (w : Circuit k) (l : ℕ) (M : Mat k) → ChkF w l M →
      scaleM (γ^ l) ⟦ w ⟧M ≡ scaleM (γ^ len w) M
F-≡ w l M e = mat-ext (λ x y →
  Eq.trans (ix-scaleM (γ^ l) ⟦ w ⟧M x y)
    (Eq.trans (Eq.cong (γ^ l *_) (Eq.sym (⟦⟧-ix w x y)))
      (Eq.trans (F-sem w l (ix M) h x y) (Eq.sym (ix-scaleM (γ^ len w) M x y)))))
  where
  h : ∀ x y → γ^ l * ix ⟦ w ⟧F x y ≡ γ^ nKF w * ix M x y
  e′ : eqM (scaleM (γ^ l) ⟦ w ⟧F) (scaleM (γ^ nKF w) M) ≡ true
  e′ = e
  h x y = Eq.trans (Eq.sym (ix-scaleM (γ^ l) ⟦ w ⟧F x y))
            (Eq.trans (ix-≡ (eqM-sound (scaleM (γ^ l) ⟦ w ⟧F) (scaleM (γ^ nKF w) M) e′) x y)
                      (ix-scaleM (γ^ nKF w) M x y))

-- Against an operator.
F-op : (w : Circuit k) (l : ℕ) (T : Op k) → ChkOp w l T → ⟦ w ⟧ ~ (l , T)
F-op w l T e = F-sem w l T (λ x y →
  Eq.trans (Eq.sym (ix-scaleM (γ^ l) ⟦ w ⟧F x y))
    (Eq.trans (Eq.cong (λ A → ix A x y) (eqM-sound (scaleM (γ^ l) ⟦ w ⟧F) (matOf (γ^ nKF w · T)) e′))
              (ix-matOf (γ^ nKF w · T) x y)))
  where
  e′ : eqM (scaleM (γ^ l) ⟦ w ⟧F) (matOf (γ^ nKF w · T)) ≡ true
  e′ = e
