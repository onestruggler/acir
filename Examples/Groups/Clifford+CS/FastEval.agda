------------------------------------------------------------------------
-- Presentations of groups
--
-- A faster row-operation reading, charging γ to K alone
--
-- Every gate is γ⁻¹ times a matrix over ℤ[i], and `Evaluation.⟦_⟧R`
-- applies each as that matrix: S, CS and the scalar scale every row by
-- γ or γ i, so a word of n gates multiplies every entry by γ n times and
-- its entries grow to about n/2 bits.  But only K needs γ: the scalar is
-- i, S is diag(1, i) and CS diag(1, 1, 1, i), exactly.  `⟦_⟧Q` applies
-- them so — a diagonal gate multiplies a half or a quarter of the rows
-- by i and leaves the rest alone, K adds and subtracts — and is γ^(nk w)
-- times smaller than `⟦_⟧R`, nk w the number of gates other than K
-- (`run-Q`).  `SameQ` compares two readings scaled by the other's number
-- of K gates, and `sameQ-sem` gives the same semantics; `Q-sem` and
-- `Q-≡` decide a circuit against any operator or stored matrix.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.FastEval where

open import Data.Bool using (true ; false)
open import Data.Integer as ℤ using ()
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
import Data.Nat.Properties as ℕP
import Data.Integer.Properties as ℤP
open import Data.Vec using (_∷_)
import Algebra.Properties.Ring as RingProps
open import Algebra.Bundles using (CommutativeRing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁₊ ; ₂₊)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ₒ ; ⟦_⟧M ; ⟦⟧-ix ; len)
open import Examples.Groups.Clifford+CS.Evaluation
  using (Rows ; rix ; mapT ; get-map ; add ; sub ; sc ; rix-add ; rix-sub ; rix-sc ; applyL ; run ; ⟦⟧R-ix)
open import Examples.Groups.Clifford+CS.Semantics.Decide using (eqM ; eqM-sound)

open RingProps (CommutativeRing.ring +-*-commutativeRing) using (-‿distribʳ-*)

private
  variable
    k c : ℕ

------------------------------------------------------------------------
-- The reading

-- Multiplication by i, forced.
mulI : 𝔽 → 𝔽
mulI (a +i b) = strict ((ℤ.- b) +i a)

scI : ∀ {k} c → Rows k c → Rows k c
scI {k} c = mapT k (mapT c mulI)

-- A generator's ℤ[i] part on the left.
applyQ : ∀ {k} c → Gen k → Rows k c → Rows k c
applyQ {k}    c I-gen  R                       = scI {k} c R
applyQ {₁₊ k} c K-gen  (l , r)                 = add {k} c l r , sub {k} c l r
applyQ {₁₊ k} c S-gen  (l , r)                 = l , scI {k} c r
applyQ {₂₊ k} c CS-gen ((ll , lr) , (rl , rr)) = (ll , lr) , (rl , scI {k} c rr)
applyQ {₁₊ k} c (g ↥)  (l , r)                 = applyQ {k} c g l , applyQ {k} c g r

runQ : ∀ {k} c → Circuit k → Rows k c → Rows k c
runQ c [ g ]ʷ  R = applyQ c g R
runQ c ε       R = R
runQ c (w • v) R = runQ c w (runQ c v R)

⟦_⟧Q : Circuit k → Mat k
⟦_⟧Q {k} w = mat (runQ k w (entries (idM {k})))

-- The number of K gates.
kgen : Gen k → ℕ
kgen K-gen  = 1
kgen (g ↥)  = kgen g
kgen _      = 0

nK : Circuit k → ℕ
nK [ g ]ʷ  = kgen g
nK ε       = 0
nK (w • v) = nK w +ℕ nK v

-- The number of the others.
ngen : Gen k → ℕ
ngen K-gen  = 0
ngen (g ↥)  = ngen g
ngen _      = 1

nN : Circuit k → ℕ
nN [ g ]ʷ  = ngen g
nN ε       = 0
nN (w • v) = nN w +ℕ nN v

-- Two circuits with the same matrix, decided on the fast readings.
SameQ : Circuit k → Circuit k → Set
SameQ u v = eqM (scaleM (γ^ nK v) ⟦ u ⟧Q) (scaleM (γ^ nK u) ⟦ v ⟧Q) ≡ true

------------------------------------------------------------------------
-- Arithmetic

private
  mulI-ok : ∀ a → mulI a ≡ ⅈ * a
  mulI-ok (a +i b) =
    Eq.trans (strict-id ((ℤ.- b) +i a))
      (Eq.cong₂ _+i_
        (Eq.sym (Eq.trans (Eq.cong₂ ℤ._+_ (ℤP.*-zeroˡ a) (Eq.cong ℤ.-_ (ℤP.*-identityˡ b)))
                          (ℤP.+-identityˡ (ℤ.- b))))
        (Eq.sym (Eq.trans (Eq.cong₂ ℤ._+_ (ℤP.*-zeroˡ b) (ℤP.*-identityˡ a)) (ℤP.+-identityˡ a))))

  γ¹ : γ^ 1 ≡ γ
  γ¹ = Eq.trans (strict-id (γ * 1#)) (*-identityʳ γ)

  γⅈ≡ : γⅈ ≡ γ * ⅈ
  γⅈ≡ = Eq.refl

  g0 : ∀ a → a ≡ γ^ 0 * a
  g0 a = Eq.sym (*-identityˡ a)

  g1 : ∀ a → γ * a ≡ γ^ 1 * a
  g1 a = Eq.cong (_* a) (Eq.sym γ¹)

  gi : ∀ a → γⅈ * a ≡ γ^ 1 * (ⅈ * a)
  gi a = Eq.trans (Eq.cong (_* a) γⅈ≡)
           (Eq.trans (*-assoc γ ⅈ a) (Eq.cong (_* (ⅈ * a)) (Eq.sym γ¹)))

  -- s (i a) = i (s a)
  si : ∀ s a → ⅈ * (s * a) ≡ s * (ⅈ * a)
  si s a = Eq.trans (Eq.sym (*-assoc ⅈ s a))
             (Eq.trans (Eq.cong (_* a) (*-comm ⅈ s)) (*-assoc s ⅈ a))

  s-sub : ∀ s a b → s * a - s * b ≡ s * (a - b)
  s-sub s a b = Eq.trans (Eq.cong (s * a +_) (-‿distribʳ-* s b)) (Eq.sym (*-distribˡ-+ s a (- b)))

------------------------------------------------------------------------
-- Rows

rix-scI : ∀ {k} c (R : Rows k c) (x : Bits k) (y : Bits c) → rix {k} {c} (scI {k} c R) x y ≡ ⅈ * rix {k} {c} R x y
rix-scI {k} c R x y =
  Eq.trans (Eq.cong (λ t → get t y) (get-map k (mapT c mulI) R x))
    (Eq.trans (get-map c mulI (get R x) y) (mulI-ok (rix R x y)))

-- A generator: the old row operation is γ^(ngen g) times the new one.
applyQ-ok : ∀ {k} c (g : Gen k) (R : Rows k c) (x : Bits k) (y : Bits c) →
            rix {k} {c} (applyL c g R) x y ≡ γ^ (ngen g) * rix {k} {c} (applyQ c g R) x y
applyQ-ok {k} c I-gen R x y =
  Eq.trans (rix-sc {k} c γⅈ R x y)
    (Eq.trans (gi (rix R x y)) (Eq.cong (γ^ 1 *_) (Eq.sym (rix-scI {k} c R x y))))
applyQ-ok {₁₊ k} c K-gen (l , r) (false ∷ x) y = g0 _
applyQ-ok {₁₊ k} c K-gen (l , r) (true ∷ x) y  = g0 _
applyQ-ok {₁₊ k} c S-gen (l , r) (false ∷ x) y = Eq.trans (rix-sc c γ l x y) (g1 _)
applyQ-ok {₁₊ k} c S-gen (l , r) (true ∷ x) y =
  Eq.trans (rix-sc c γⅈ r x y) (Eq.trans (gi _) (Eq.cong (γ^ 1 *_) (Eq.sym (rix-scI c r x y))))
applyQ-ok {₂₊ k} c CS-gen ((ll , lr) , (rl , rr)) (false ∷ false ∷ x) y =
  Eq.trans (rix-sc c γ ll x y) (g1 _)
applyQ-ok {₂₊ k} c CS-gen ((ll , lr) , (rl , rr)) (false ∷ true ∷ x) y =
  Eq.trans (rix-sc c γ lr x y) (g1 _)
applyQ-ok {₂₊ k} c CS-gen ((ll , lr) , (rl , rr)) (true ∷ false ∷ x) y =
  Eq.trans (rix-sc c γ rl x y) (g1 _)
applyQ-ok {₂₊ k} c CS-gen ((ll , lr) , (rl , rr)) (true ∷ true ∷ x) y =
  Eq.trans (rix-sc c γⅈ rr x y) (Eq.trans (gi _) (Eq.cong (γ^ 1 *_) (Eq.sym (rix-scI c rr x y))))
applyQ-ok {₁₊ k} c (g ↥) (l , r) (false ∷ x) y = applyQ-ok c g l x y
applyQ-ok {₁₊ k} c (g ↥) (l , r) (true ∷ x) y  = applyQ-ok c g r x y

-- The new row operations are linear.
Prop : ∀ k c → 𝔽 → Rows k c → Rows k c → Set
Prop k c s R R′ = ∀ (x : Bits k) (y : Bits c) → rix {k} {c} R x y ≡ s * rix {k} {c} R′ x y

applyQ-lin : ∀ {k} c (g : Gen k) s (R R′ : Rows k c) → Prop k c s R R′ →
             Prop k c s (applyQ c g R) (applyQ c g R′)
applyQ-lin {k} c I-gen s R R′ h x y =
  Eq.trans (rix-scI {k} c R x y)
    (Eq.trans (Eq.cong (ⅈ *_) (h x y))
      (Eq.trans (si s (rix R′ x y)) (Eq.cong (s *_) (Eq.sym (rix-scI {k} c R′ x y)))))
applyQ-lin {₁₊ k} c K-gen s (l , r) (l′ , r′) h (false ∷ x) y =
  Eq.trans (rix-add c l r x y)
    (Eq.trans (Eq.cong₂ _+_ (h (false ∷ x) y) (h (true ∷ x) y))
      (Eq.trans (Eq.sym (*-distribˡ-+ s (rix l′ x y) (rix r′ x y)))
                (Eq.cong (s *_) (Eq.sym (rix-add c l′ r′ x y)))))
applyQ-lin {₁₊ k} c K-gen s (l , r) (l′ , r′) h (true ∷ x) y =
  Eq.trans (rix-sub c l r x y)
    (Eq.trans (Eq.cong₂ _-_ (h (false ∷ x) y) (h (true ∷ x) y))
      (Eq.trans (s-sub s (rix l′ x y) (rix r′ x y))
                (Eq.cong (s *_) (Eq.sym (rix-sub c l′ r′ x y)))))
applyQ-lin {₁₊ k} c S-gen s (l , r) (l′ , r′) h (false ∷ x) y = h (false ∷ x) y
applyQ-lin {₁₊ k} c S-gen s (l , r) (l′ , r′) h (true ∷ x) y =
  applyQ-lin {k} c I-gen s r r′ (λ x′ y′ → h (true ∷ x′) y′) x y
applyQ-lin {₂₊ k} c CS-gen s ((ll , lr) , (rl , rr)) ((ll′ , lr′) , (rl′ , rr′)) h (false ∷ b ∷ x) y =
  h (false ∷ b ∷ x) y
applyQ-lin {₂₊ k} c CS-gen s ((ll , lr) , (rl , rr)) ((ll′ , lr′) , (rl′ , rr′)) h (true ∷ false ∷ x) y =
  h (true ∷ false ∷ x) y
applyQ-lin {₂₊ k} c CS-gen s ((ll , lr) , (rl , rr)) ((ll′ , lr′) , (rl′ , rr′)) h (true ∷ true ∷ x) y =
  applyQ-lin {k} c I-gen s rr rr′ (λ x′ y′ → h (true ∷ true ∷ x′) y′) x y
applyQ-lin {₁₊ k} c (g ↥) s (l , r) (l′ , r′) h (false ∷ x) y =
  applyQ-lin {k} c g s l l′ (λ x′ y′ → h (false ∷ x′) y′) x y
applyQ-lin {₁₊ k} c (g ↥) s (l , r) (l′ , r′) h (true ∷ x) y =
  applyQ-lin {k} c g s r r′ (λ x′ y′ → h (true ∷ x′) y′) x y

runQ-lin : ∀ {k} c (w : Circuit k) s (R R′ : Rows k c) → Prop k c s R R′ →
           Prop k c s (runQ c w R) (runQ c w R′)
runQ-lin c [ g ]ʷ  s R R′ h = applyQ-lin c g s R R′ h
runQ-lin c ε       s R R′ h = h
runQ-lin c (w • v) s R R′ h = runQ-lin c w s (runQ c v R) (runQ c v R′) (runQ-lin c v s R R′ h)

-- A word: the old reading is γ^(nN w) times the new one.
run-Q : ∀ {k} c (w : Circuit k) (R : Rows k c) → Prop k c (γ^ nN w) (run c w R) (runQ c w R)
run-Q c [ g ]ʷ  R x y = applyQ-ok c g R x y
run-Q c ε       R x y = g0 (rix R x y)
run-Q c (w • v) R x y =
  Eq.trans (run-Q c w (run c v R) x y)
    (Eq.trans (Eq.cong (γ^ nN w *_)
                 (runQ-lin c w (γ^ nN v) (run c v R) (runQ c v R) (run-Q c v R) x y))
      (Eq.trans (Eq.sym (*-assoc (γ^ nN w) (γ^ nN v) _))
                (Eq.cong (_* rix (runQ c w (runQ c v R)) x y) (Eq.sym (γ^-+ (nN w) (nN v))))))

------------------------------------------------------------------------
-- The same semantics

len-split : (w : Circuit k) → len w ≡ nK w +ℕ nN w
len-split [ I-gen ]ʷ  = Eq.refl
len-split [ K-gen ]ʷ  = Eq.refl
len-split [ S-gen ]ʷ  = Eq.refl
len-split [ CS-gen ]ʷ = Eq.refl
len-split [ g ↥ ]ʷ    = len-split [ g ]ʷ
len-split ε           = Eq.refl
len-split (w • v)     =
  Eq.trans (Eq.cong₂ _+ℕ_ (len-split w) (len-split v)) (shuffle (nK w) (nN w) (nK v) (nN v))
  where
  shuffle : ∀ a b c d → (a +ℕ b) +ℕ (c +ℕ d) ≡ (a +ℕ c) +ℕ (b +ℕ d)
  shuffle a b c d =
    Eq.trans (ℕP.+-assoc a b (c +ℕ d))
      (Eq.trans (Eq.cong (a +ℕ_) (Eq.trans (Eq.sym (ℕP.+-assoc b c d))
                                   (Eq.trans (Eq.cong (_+ℕ d) (ℕP.+-comm b c)) (ℕP.+-assoc c b d))))
                (Eq.sym (ℕP.+-assoc a c (b +ℕ d))))

private
  -- (a b) (c q) = (b c) (a q)
  sw : ∀ a b c q → (a * b) * (c * q) ≡ (b * c) * (a * q)
  sw a b c q = Eq.trans (Eq.cong (_* (c * q)) (*-comm a b)) (*-cross b a c q)

  lcomm : ∀ a b c → a * (b * c) ≡ b * (a * c)
  lcomm a b c = Eq.trans (Eq.sym (*-assoc a b c)) (Eq.trans (Eq.cong (_* c) (*-comm a b)) (*-assoc b a c))

-- The fast reading at its own width.
Q-ix : (w : Circuit k) → ∀ (x y : Bits k) → ⟦ w ⟧ₒ x y ≡ γ^ nN w * ix ⟦ w ⟧Q x y
Q-ix {k} w x y = Eq.trans (⟦⟧R-ix w x y) (run-Q {k} k w (entries (idM {k})) x y)

-- A circuit against any operator: γ^ l ⟦ w ⟧Q is γ^ (nK w) T.
Q-sem : (w : Circuit k) (l : ℕ) (T : Op k) →
        (∀ (x y : Bits k) → γ^ l * ix ⟦ w ⟧Q x y ≡ γ^ nK w * T x y) → ⟦ w ⟧ ~ (l , T)
Q-sem w l T h x y = begin
  γ^ l * ⟦ w ⟧ₒ x y            ≡⟨ Eq.cong (γ^ l *_) (Q-ix w x y) ⟩
  γ^ l * (γ^ nN w * Qw)         ≡⟨ lcomm (γ^ l) (γ^ nN w) Qw ⟩
  γ^ nN w * (γ^ l * Qw)         ≡⟨ Eq.cong (γ^ nN w *_) (h x y) ⟩
  γ^ nN w * (γ^ nK w * T x y)   ≡⟨ lcomm (γ^ nN w) (γ^ nK w) (T x y) ⟩
  γ^ nK w * (γ^ nN w * T x y)   ≡⟨ Eq.sym (*-assoc (γ^ nK w) (γ^ nN w) (T x y)) ⟩
  (γ^ nK w * γ^ nN w) * T x y   ≡⟨ Eq.cong (_* T x y) (Eq.sym (Eq.trans (Eq.cong γ^_ (len-split w))
                                                                  (γ^-+ (nK w) (nN w)))) ⟩
  γ^ len w * T x y ∎
  where
  open Eq.≡-Reasoning
  Qw = ix ⟦ w ⟧Q x y

-- The same against a stored matrix, as the stored reading's equation.
Q-≡ : (w : Circuit k) (l : ℕ) (M : Mat k) →
      eqM (scaleM (γ^ l) ⟦ w ⟧Q) (scaleM (γ^ nK w) M) ≡ true →
      scaleM (γ^ l) ⟦ w ⟧M ≡ scaleM (γ^ len w) M
Q-≡ w l M e = mat-ext (λ x y →
  Eq.trans (ix-scaleM (γ^ l) ⟦ w ⟧M x y)
    (Eq.trans (Eq.cong (γ^ l *_) (Eq.sym (⟦⟧-ix w x y)))
      (Eq.trans (Q-sem w l (ix M) h x y) (Eq.sym (ix-scaleM (γ^ len w) M x y)))))
  where
  h : ∀ x y → γ^ l * ix ⟦ w ⟧Q x y ≡ γ^ nK w * ix M x y
  h x y = Eq.trans (Eq.sym (ix-scaleM (γ^ l) ⟦ w ⟧Q x y))
            (Eq.trans (ix-≡ (eqM-sound _ _ e) x y) (ix-scaleM (γ^ nK w) M x y))

sameQ-sem : (u v : Circuit k) → SameQ u v → ⟦ u ⟧ ~ ⟦ v ⟧
sameQ-sem u v e x y = begin
  γ^ len v * ⟦ u ⟧ₒ x y
    ≡⟨ Eq.cong₂ _*_ (Eq.trans (Eq.cong γ^_ (len-split v)) (γ^-+ (nK v) (nN v))) (Q-ix u x y) ⟩
  (A * B) * (C * Qu)
    ≡⟨ sw A B C Qu ⟩
  (B * C) * (A * Qu)
    ≡⟨ Eq.cong ((B * C) *_) E ⟩
  (B * C) * (D * Qv)
    ≡⟨ Eq.cong (_* (D * Qv)) (*-comm B C) ⟩
  (C * B) * (D * Qv)
    ≡⟨ Eq.sym (sw D C B Qv) ⟩
  (D * C) * (B * Qv)
    ≡⟨ Eq.sym (Eq.cong₂ _*_ (Eq.trans (Eq.cong γ^_ (len-split u)) (γ^-+ (nK u) (nN u))) (Q-ix v x y)) ⟩
  γ^ len u * ⟦ v ⟧ₒ x y ∎
  where
  open Eq.≡-Reasoning
  A = γ^ nK v
  B = γ^ nN v
  C = γ^ nN u
  D = γ^ nK u
  Qu = ix ⟦ u ⟧Q x y
  Qv = ix ⟦ v ⟧Q x y
  E : A * Qu ≡ D * Qv
  E = Eq.trans (Eq.sym (ix-scaleM A ⟦ u ⟧Q x y))
        (Eq.trans (ix-≡ (eqM-sound _ _ e) x y) (ix-scaleM D ⟦ v ⟧Q x y))
