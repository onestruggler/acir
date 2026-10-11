------------------------------------------------------------------------
-- Presentations of groups
--
-- Words through a Hadamard frame, normalised
--
-- Fix two indices e and f.  A Hadamard pair `H_[x,y] H_[e,f]` is then
-- a single two-level Hadamard on x and y with the frame's Hadamard
-- riding along, and since the frame commutes with everything that
-- avoids e and f, a word of such *half-letters* and Hadamard-free
-- letters behaves like a word in single Hadamards: the Hadamard-free
-- letters can be pushed to the right (`Twist.hh-twist`), a
-- half-letter turned round at the cost of a mixed letter (67), and two
-- equal half-letters in a row cancel (`hh-invol`).  Doing all three
-- gives a normal form — a list of ordered index pairs and a
-- Hadamard-free tail — computed on a template (`Template`) where the
-- indices are literals, and proved sound once (`norm-sound`).  Two
-- words with the same list and tails of the same table are then
-- equivalent (`by-norm`), and both conditions are `refl`.
--
-- Whole pairs `H_[x,y] H_[z,w]` over the template split through the
-- frame by (71), and `H_[e,f] H_[x,y]` turns round by (66), so both
-- are letters of the frame words too.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.FrameNorm (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_ ; _<?_)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Encoding using (hh ; zx ; xx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (sp ; sgn ; prm ; idSP ; SWP ; SWP-invol ; sp-inj ; ⊙-inverse ; eqv
       ; xor-self ; δ)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_ ; ≐-trans to ≐-trans′ ; ≐-sym to ≐-sym′
          ; ≐-refl to ≐-refl′ ; ⊙-cong to ⊙-cong′ ; ⊙-assoc to ⊙-assoc′
          ; ⊙-idˡ to ⊙-idˡ′ ; prm≡ to prm≡′)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm m using (zx-pair)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Template m
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m using (Eq65 ; eq66)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Fuse m using (fuse ; hh-invol)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq67 m using (eq67)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Twist m using (κ ; hh-twist)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools (m P,_===_)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

  refl≡ : ∀ {u v : W} → u ≡ v → u ≈ v
  refl≡ Eq.refl = refl

  -- A letter whose pair repeats an index is the empty word.
  hh-same₁ : ∀ (a c d : Fin N) → hh {₃₊ m} a a c d ≡ ε
  hh-same₁ a c d with a ≟ a
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

  hh-same₂ : ∀ (a b c : Fin N) → hh {₃₊ m} a b c c ≡ ε
  hh-same₂ a b c with a ≟ b | c ≟ c
  ... | yes _ | _     = Eq.refl
  ... | no  _ | yes _ = Eq.refl
  ... | no  _ | no ne = ⊥-elim (ne Eq.refl)

  -- Two exchanges and their reverse.
  xx-inv : ∀ (a b c d : Fin N) → sp (xx {₃₊ m} a b c d) ⊛ sp (xx {₃₊ m} c d a b) ≗ idSP
  xx-inv a b c d with a ≟ b | c ≟ d
  ... | yes _ | yes _ = ≐-refl′
  ... | yes _ | no  _ = ≐-refl′
  ... | no  _ | yes _ = ≐-refl′
  ... | no  _ | no  _ =
    ≐-trans′ (⊙-assoc′ (SWP a b) (SWP c d) (SWP c d ⊛ SWP a b))
    (≐-trans′ (⊙-cong′ (≐-refl′ {SWP a b})
                (≐-trans′ (≐-sym′ (⊙-assoc′ (SWP c d) (SWP c d) (SWP a b)))
                (≐-trans′ (⊙-cong′ (SWP-invol c d) (≐-refl′ {SWP a b}))
                          (⊙-idˡ′ (SWP a b)))))
              (SWP-invol a b))

------------------------------------------------------------------------
-- The normaliser, at a template and a frame

module Norm (e65 : Eq65) {k : ℕ} (ι : Fin k → Fin N)
            (inj : ∀ {x y : Fin k} → ι x ≡ ι y → x ≡ y)
            (e f : Fin N) (ef : e ≢ f)
            (offe : ∀ (x : Fin k) → ι x ≢ e) (offf : ∀ (x : Fin k) → ι x ≢ f) where

  open At ι inj public

  ----------------------------------------------------------------------
  -- The inverse of a template word

  linv : TL k → TL k
  linv (tz i j)       = tz i j
  linv (ty c i j)     = ty (swk i j c) i j
  linv (tx i j i′ j′) = tx i′ j′ i j

  tinv : TW k → TW k
  tinv emp       = emp
  tinv ⌜ l ⌝     = ⌜ linv l ⌝
  tinv (w •ᵗ w′) = tinv w′ •ᵗ tinv w

  private
    linv-sp : ∀ (l : TL k) → sp (instL l) ⊛ sp (instL (linv l)) ≗ idSP
    linv-sp (tz i j) = eqv (λ x → xor-self (δ (ι i) x xor δ (ι j) x)) (λ _ → Eq.refl)
    linv-sp (ty c i j) =
      zx-pair (ι c) (ι (swk i j c)) (ι i) (ι j)
              (Eq.sym (Eq.trans (swap-ι i j (swk i j c)) (Eq.cong ι (swk-invol i j c))))
    linv-sp (tx i j i′ j′) = xx-inv (ι i) (ι j) (ι i′) (ι j′)

  tinv-sp : ∀ (t : TW k) → sp (inst t) ⊛ sp (inst (tinv t)) ≗ idSP
  tinv-sp emp       = ≐-refl′
  tinv-sp ⌜ l ⌝     = linv-sp l
  tinv-sp (w •ᵗ w′) =
    ≐-trans′ (⊙-assoc′ A B (B′ ⊛ A′))
    (≐-trans′ (⊙-cong′ (≐-refl′ {A})
                (≐-trans′ (≐-sym′ (⊙-assoc′ B B′ A′))
                (≐-trans′ (⊙-cong′ (tinv-sp w′) (≐-refl′ {A′})) (⊙-idˡ′ A′))))
              (tinv-sp w))
    where
    A B B′ A′ : _
    A  = sp (inst w)
    B  = sp (inst w′)
    B′ = sp (inst (tinv w′))
    A′ = sp (inst (tinv w))

  ----------------------------------------------------------------------
  -- Pre-images

  pre : TW k → Fin k → Fin k
  pre t x = tpm (tW (tinv t)) x

  pre-ok : ∀ (t : TW k) (x : Fin k) → prm (sp (inst t)) (ι (pre t x)) ≡ ι x
  pre-ok t x =
    Eq.trans (Eq.cong (prm (sp (inst t))) (Eq.sym (prm-at (tinv t) x)))
             (prm≡′ (⊙-inverse (sp (inst t)) (sp (inst (tinv t)))
                               (sp-inj (inst (tinv t))) (tinv-sp t)) (ι x))

  pre-inj : ∀ (t : TW k) {x y : Fin k} → pre t x ≡ pre t y → x ≡ y
  pre-inj t {x} {y} h =
    inj (Eq.trans (Eq.sym (pre-ok t x))
                  (Eq.trans (Eq.cong (λ z → prm (sp (inst t)) (ι z)) h) (pre-ok t y)))

  ----------------------------------------------------------------------
  -- Half-letters

  P : Set
  P = Fin k × Fin k

  half : P → W
  half (x , y) = hh {₃₊ m} (ι x) (ι y) e f

  halves : List P → W
  halves []       = ε
  halves (h ∷ hs) = half h • halves hs

  -- No pair repeats an index.
  ND : List P → Set
  ND []             = ⊤
  ND ((x , y) ∷ hs) = (x ≢ y) × ND hs

  private
    ιne : ∀ {x y : Fin k} → x ≢ y → ι x ≢ ι y
    ιne ne h = ne (inj h)

    halves-++ : ∀ (xs ys : List P) → halves (xs ++ ys) ≈ halves xs • halves ys
    halves-++ []       ys = sym left-unit
    halves-++ (h ∷ xs) ys = trans (back (half h) (halves-++ xs ys)) (sym assoc)

    ND-++ : ∀ (xs ys : List P) → ND xs → ND ys → ND (xs ++ ys)
    ND-++ []             ys _          nys = nys
    ND-++ ((x , y) ∷ xs) ys (ne , nxs) nys = ne , ND-++ xs ys nxs nys

  ----------------------------------------------------------------------
  -- Turning a half-letter round

  orient : Fin k → Fin k → TW k → P × TW k
  orient x y c with x <? y
  ... | yes _ = (x , y) , c
  ... | no  _ = (y , x) , (⌜ ty x y x ⌝ •ᵗ c)

  orient-sound : ∀ (x y : Fin k) (c : TW k) → x ≢ y →
                 half (x , y) • inst c
                 ≈ half (proj₁ (orient x y c)) • inst (proj₂ (orient x y c))
  orient-sound x y c xy with x <? y
  ... | yes _ = refl
  ... | no  _ = begin
    hh {₃₊ m} (ι x) (ι y) e f • inst c
      ≈⟨ front (inst c) (eq67 e65 (ι y) (ι x) e f (ιne (λ h → xy (Eq.sym h)))
                              (offe y) (offf y) (offe x) (offf x) ef) ⟩
    (hh {₃₊ m} (ι y) (ι x) e f • zx {₃₊ m} (ι x) (ι y) (ι x)) • inst c
      ≈⟨ assoc ⟩
    hh {₃₊ m} (ι y) (ι x) e f • (zx {₃₊ m} (ι x) (ι y) (ι x) • inst c) ∎

  orient-nd : ∀ (x y : Fin k) (c : TW k) → x ≢ y →
              proj₁ (proj₁ (orient x y c)) ≢ proj₂ (proj₁ (orient x y c))
  orient-nd x y c xy with x <? y
  ... | yes _ = xy
  ... | no  _ = λ h → xy (Eq.sym h)

  ----------------------------------------------------------------------
  -- Pushing a Hadamard-free tail through a half-letter

  κᵗ : Bool → Fin k → Fin k → TW k → TW k
  κᵗ false x y t = t
  κᵗ true  x y t = ⌜ ty x x y ⌝ •ᵗ t

  private
    κ-inst : ∀ (b : Bool) (x y : Fin k) (t : TW k) →
             κ b (ι x) (ι y) (inst t) ≡ inst (κᵗ b x y t)
    κ-inst false x y t = Eq.refl
    κ-inst true  x y t = Eq.refl

  flag : TW k → Fin k → Fin k → Bool
  flag t x y = tsg (tW t) x xor tsg (tW t) y

  pushH : TW k → P → P × TW k
  pushH t (x , y) =
    orient (pre t x) (pre t y) (κᵗ (flag t (pre t x) (pre t y)) (pre t x) (pre t y) t)

  pushH-sound : ∀ (t : TW k) (x y : Fin k) → x ≢ y →
                inst t • half (x , y)
                ≈ half (proj₁ (pushH t (x , y))) • inst (proj₂ (pushH t (x , y)))
  pushH-sound t x y xy =
    trans twist
      (trans (back (half (x′ , y′)) (refl≡ (κ-inst b x′ y′ t)))
             (orient-sound x′ y′ (κᵗ b x′ y′ t) x′y′))
    where
    x′ y′ : Fin k
    x′ = pre t x
    y′ = pre t y

    b : Bool
    b = flag t x′ y′

    x′y′ : x′ ≢ y′
    x′y′ h = xy (pre-inj t h)

    twist : inst t • hh {₃₊ m} (ι x) (ι y) e f
            ≈ hh {₃₊ m} (ι x′) (ι y′) e f • κ b (ι x′) (ι y′) (κ false e f (inst t))
    twist = hh-twist e65 (inst t) (inst (tinv t)) (hf-inst t) (hf-inst (tinv t)) (tinv-sp t)
              (ι x′) (ι y′) e f (ι x) (ι y) e f
              (pre-ok t x) (pre-ok t y) (W-prm-off t e offe) (W-prm-off t f offf)
              b false
              (Eq.cong₂ _xor_ (sgn-at t x′) (sgn-at t y′))
              (Eq.cong₂ _xor_ (W-sgn-off t e offe) (W-sgn-off t f offf))
              (ιne x′y′) (offe x′) (offf x′) (offe y′) (offf y′) ef

  pushH-nd : ∀ (t : TW k) (x y : Fin k) → x ≢ y →
             proj₁ (proj₁ (pushH t (x , y))) ≢ proj₂ (proj₁ (pushH t (x , y)))
  pushH-nd t x y xy =
    orient-nd (pre t x) (pre t y) (κᵗ (flag t (pre t x) (pre t y)) (pre t x) (pre t y) t)
              (λ h → xy (pre-inj t h))

  -- … and through a list of them.
  pushL : TW k → List P → List P × TW k
  pushL t []       = [] , t
  pushL t (h ∷ hs) =
    (proj₁ (pushH t h) ∷ proj₁ (pushL (proj₂ (pushH t h)) hs)) ,
    proj₂ (pushL (proj₂ (pushH t h)) hs)

  pushL-sound : ∀ (t : TW k) (hs : List P) → ND hs →
                inst t • halves hs ≈ halves (proj₁ (pushL t hs)) • inst (proj₂ (pushL t hs))
  pushL-sound t []             _          = trans right-unit (sym left-unit)
  pushL-sound t ((x , y) ∷ hs) (xy , nhs) = begin
    inst t • (half (x , y) • halves hs)                          ≈⟨ sym assoc ⟩
    (inst t • half (x , y)) • halves hs                          ≈⟨ front (halves hs) (pushH-sound t x y xy) ⟩
    (half h′ • inst t′) • halves hs                              ≈⟨ assoc ⟩
    half h′ • (inst t′ • halves hs)                              ≈⟨ back (half h′) (pushL-sound t′ hs nhs) ⟩
    half h′ • (halves (proj₁ (pushL t′ hs)) • inst (proj₂ (pushL t′ hs)))
                                                                 ≈⟨ sym assoc ⟩
    (half h′ • halves (proj₁ (pushL t′ hs))) • inst (proj₂ (pushL t′ hs)) ∎
    where
    h′ : P
    h′ = proj₁ (pushH t (x , y))

    t′ : TW k
    t′ = proj₂ (pushH t (x , y))

  pushL-nd : ∀ (t : TW k) (hs : List P) → ND hs → ND (proj₁ (pushL t hs))
  pushL-nd t []             _          = tt
  pushL-nd t ((x , y) ∷ hs) (xy , nhs) =
    pushH-nd t x y xy , pushL-nd (proj₂ (pushH t (x , y))) hs nhs

  ----------------------------------------------------------------------
  -- Cancelling equal neighbours

  private
    _≟ᴾ_ : (h h′ : P) → Dec (h ≡ h′)
    (x , y) ≟ᴾ (x′ , y′) with x ≟ x′ | y ≟ y′
    ... | yes Eq.refl | yes Eq.refl = yes Eq.refl
    ... | no  ne      | _           = no (λ { Eq.refl → ne Eq.refl })
    ... | yes _       | no  ne      = no (λ { Eq.refl → ne Eq.refl })

  cons-red : P → List P → List P
  cons-red h []        = h ∷ []
  cons-red h (h′ ∷ hs) with h ≟ᴾ h′
  ... | yes _ = hs
  ... | no  _ = h ∷ h′ ∷ hs

  red : List P → List P
  red []       = []
  red (h ∷ hs) = cons-red h (red hs)

  private
    cons-red-sound : ∀ (x y : Fin k) (hs : List P) → x ≢ y →
                     half (x , y) • halves hs ≈ halves (cons-red (x , y) hs)
    cons-red-sound x y []        xy = refl
    cons-red-sound x y (h′ ∷ hs) xy with (x , y) ≟ᴾ h′
    ... | yes Eq.refl = begin
      half (x , y) • (half (x , y) • halves hs)     ≈⟨ sym assoc ⟩
      (half (x , y) • half (x , y)) • halves hs     ≈⟨ front (halves hs)
                                                         (hh-invol e65 (ι x) (ι y) e f (ιne xy)
                                                           (offe x) (offf x) (offe y) (offf y) ef) ⟩
      ε • halves hs                                 ≈⟨ left-unit ⟩
      halves hs                                     ∎
    ... | no  _ = refl

    cons-red-nd : ∀ (x y : Fin k) (hs : List P) → x ≢ y → ND hs → ND (cons-red (x , y) hs)
    cons-red-nd x y []        xy _   = xy , tt
    cons-red-nd x y (h′ ∷ hs) xy nhs with (x , y) ≟ᴾ h′
    cons-red-nd x y ((x′ , y′) ∷ hs) xy (_ , nhs) | yes _ = nhs
    cons-red-nd x y ((x′ , y′) ∷ hs) xy nhs       | no  _ = xy , nhs

  red-sound : ∀ (hs : List P) → ND hs → halves hs ≈ halves (red hs)
  red-sound []             _          = refl
  red-sound ((x , y) ∷ hs) (xy , nhs) =
    trans (back (half (x , y)) (red-sound hs nhs)) (cons-red-sound x y (red hs) xy)

  red-nd : ∀ (hs : List P) → ND hs → ND (red hs)
  red-nd []             _          = tt
  red-nd ((x , y) ∷ hs) (xy , nhs) = cons-red-nd x y (red hs) xy (red-nd hs nhs)

  ----------------------------------------------------------------------
  -- Frame words

  data FL : Set where
    hf : TL k → FL                             -- a Hadamard-free letter
    hl : Fin k → Fin k → FL                    -- H_[x,y] H_[e,f]
    hr : Fin k → Fin k → FL                    -- H_[e,f] H_[x,y]
    hp : Fin k → Fin k → Fin k → Fin k → FL    -- H_[x,y] H_[z,w]

  infixr 7 _•ᶠ_
  data FW : Set where
    femp : FW
    ⌞_⌟  : FL → FW
    _•ᶠ_ : FW → FW → FW

  instFL : FL → W
  instFL (hf l)       = instL l
  instFL (hl x y)     = hh {₃₊ m} (ι x) (ι y) e f
  instFL (hr x y)     = hh {₃₊ m} e f (ι x) (ι y)
  instFL (hp x y z w) = hh {₃₊ m} (ι x) (ι y) (ι z) (ι w)

  instF : FW → W
  instF femp      = ε
  instF ⌞ l ⌟     = instFL l
  instF (w •ᶠ w′) = instF w • instF w′

  NF : Set
  NF = List P × TW k

  instN : NF → W
  instN n = halves (proj₁ n) • inst (proj₂ n)

  single : Fin k → Fin k → NF
  single x y with x ≟ y
  ... | yes _ = [] , emp
  ... | no  _ = (proj₁ (orient x y emp) ∷ []) , proj₂ (orient x y emp)

  merge : NF → NF → NF
  merge n₁ n₂ =
    red (proj₁ n₁ ++ proj₁ (pushL (proj₂ n₁) (proj₁ n₂))) ,
    (proj₂ (pushL (proj₂ n₁) (proj₁ n₂)) •ᵗ proj₂ n₂)

  pairN : Fin k → Fin k → Fin k → Fin k → NF
  pairN x y z w with x ≟ y | z ≟ w
  ... | no _ | no _ = merge (single x y) (single z w)
  ... | _    | _    = [] , emp

  norm : FW → NF
  norm femp            = [] , emp
  norm ⌞ hf l ⌟        = [] , ⌜ l ⌝
  norm ⌞ hl x y ⌟      = single x y
  norm ⌞ hr x y ⌟      = single x y
  norm ⌞ hp x y z w ⌟  = pairN x y z w
  norm (w •ᶠ w′)       = merge (norm w) (norm w′)

  ----------------------------------------------------------------------
  -- Soundness

  private
    single-nd : ∀ (x y : Fin k) → ND (proj₁ (single x y))
    single-nd x y with x ≟ y
    ... | yes _ = tt
    ... | no xy = orient-nd x y emp xy , tt

    merge-nd : ∀ (n₁ n₂ : NF) → ND (proj₁ n₁) → ND (proj₁ n₂) → ND (proj₁ (merge n₁ n₂))
    merge-nd n₁ n₂ nd₁ nd₂ =
      red-nd _ (ND-++ (proj₁ n₁) _ nd₁ (pushL-nd (proj₂ n₁) (proj₁ n₂) nd₂))

    pairN-nd : ∀ (x y z w : Fin k) → ND (proj₁ (pairN x y z w))
    pairN-nd x y z w with x ≟ y | z ≟ w
    ... | no _  | no _  = merge-nd (single x y) (single z w) (single-nd x y) (single-nd z w)
    ... | yes _ | _     = tt
    ... | no _  | yes _ = tt

  norm-nd : ∀ (w : FW) → ND (proj₁ (norm w))
  norm-nd femp           = tt
  norm-nd ⌞ hf l ⌟       = tt
  norm-nd ⌞ hl x y ⌟     = single-nd x y
  norm-nd ⌞ hr x y ⌟     = single-nd x y
  norm-nd ⌞ hp x y z w ⌟ = pairN-nd x y z w
  norm-nd (w •ᶠ w′)      = merge-nd (norm w) (norm w′) (norm-nd w) (norm-nd w′)

  private
    single-sound : ∀ (x y : Fin k) → hh {₃₊ m} (ι x) (ι y) e f ≈ instN (single x y)
    single-sound x y with x ≟ y
    ... | yes Eq.refl = trans (refl≡ (hh-same₁ (ι x) e f)) (sym left-unit)
    ... | no  xy = begin
      hh {₃₊ m} (ι x) (ι y) e f                       ≈⟨ sym right-unit ⟩
      half (x , y) • inst emp                         ≈⟨ orient-sound x y emp xy ⟩
      half (proj₁ (orient x y emp)) • inst (proj₂ (orient x y emp))
                                                      ≈⟨ front (inst (proj₂ (orient x y emp))) (sym right-unit) ⟩
      (half (proj₁ (orient x y emp)) • ε) • inst (proj₂ (orient x y emp)) ∎

    hr-sound : ∀ (x y : Fin k) → hh {₃₊ m} e f (ι x) (ι y) ≈ hh {₃₊ m} (ι x) (ι y) e f
    hr-sound x y with x ≟ y
    ... | yes Eq.refl = refl≡ (Eq.trans (hh-same₂ e f (ι x)) (Eq.sym (hh-same₁ (ι x) e f)))
    ... | no  xy =
      eq66 e65 e f (ι x) (ι y) ef (λ h → offe x (Eq.sym h)) (λ h → offe y (Eq.sym h))
           (λ h → offf x (Eq.sym h)) (λ h → offf y (Eq.sym h)) (ιne xy)

    merge-sound : ∀ (n₁ n₂ : NF) → ND (proj₁ n₁) → ND (proj₁ n₂) →
                  instN n₁ • instN n₂ ≈ instN (merge n₁ n₂)
    merge-sound (hs₁ , t₁) (hs₂ , t₂) nd₁ nd₂ = begin
      (halves hs₁ • inst t₁) • (halves hs₂ • inst t₂)
        ≈⟨ assoc ⟩
      halves hs₁ • (inst t₁ • (halves hs₂ • inst t₂))
        ≈⟨ back (halves hs₁) (sym assoc) ⟩
      halves hs₁ • ((inst t₁ • halves hs₂) • inst t₂)
        ≈⟨ back (halves hs₁) (front (inst t₂) (pushL-sound t₁ hs₂ nd₂)) ⟩
      halves hs₁ • ((halves hs₂′ • inst t₁′) • inst t₂)
        ≈⟨ back (halves hs₁) assoc ⟩
      halves hs₁ • (halves hs₂′ • (inst t₁′ • inst t₂))
        ≈⟨ sym assoc ⟩
      (halves hs₁ • halves hs₂′) • (inst t₁′ • inst t₂)
        ≈⟨ front (inst t₁′ • inst t₂) (sym (halves-++ hs₁ hs₂′)) ⟩
      halves (hs₁ ++ hs₂′) • (inst t₁′ • inst t₂)
        ≈⟨ front (inst t₁′ • inst t₂)
                 (red-sound (hs₁ ++ hs₂′) (ND-++ hs₁ hs₂′ nd₁ (pushL-nd t₁ hs₂ nd₂))) ⟩
      halves (red (hs₁ ++ hs₂′)) • (inst t₁′ • inst t₂) ∎
      where
      hs₂′ : List P
      hs₂′ = proj₁ (pushL t₁ hs₂)

      t₁′ : TW k
      t₁′ = proj₂ (pushL t₁ hs₂)

    pairN-sound : ∀ (x y z w : Fin k) →
                  hh {₃₊ m} (ι x) (ι y) (ι z) (ι w) ≈ instN (pairN x y z w)
    pairN-sound x y z w with x ≟ y | z ≟ w
    ... | no xy | no zw = begin
      hh {₃₊ m} (ι x) (ι y) (ι z) (ι w)
        ≈⟨ sym (fuse e65 (ι x) (ι y) e f (ι z) (ι w) (ιne xy) ef (ιne zw)) ⟩
      hh {₃₊ m} (ι x) (ι y) e f • hh {₃₊ m} e f (ι z) (ι w)
        ≈⟨ cong (single-sound x y) (trans (hr-sound z w) (single-sound z w)) ⟩
      instN (single x y) • instN (single z w)
        ≈⟨ merge-sound (single x y) (single z w) (single-nd x y) (single-nd z w) ⟩
      instN (merge (single x y) (single z w)) ∎
    ... | yes Eq.refl | _ = trans (refl≡ (hh-same₁ (ι x) (ι z) (ι w))) (sym left-unit)
    ... | no _ | yes Eq.refl = trans (refl≡ (hh-same₂ (ι x) (ι y) (ι z))) (sym left-unit)

  norm-sound : ∀ (w : FW) → instF w ≈ instN (norm w)
  norm-sound femp           = sym left-unit
  norm-sound ⌞ hf l ⌟       = sym left-unit
  norm-sound ⌞ hl x y ⌟     = single-sound x y
  norm-sound ⌞ hr x y ⌟     = trans (hr-sound x y) (single-sound x y)
  norm-sound ⌞ hp x y z w ⌟ = pairN-sound x y z w
  norm-sound (w •ᶠ w′)      =
    trans (cong (norm-sound w) (norm-sound w′))
          (merge-sound (norm w) (norm w′) (norm-nd w) (norm-nd w′))

  ----------------------------------------------------------------------
  -- Deciding an equation

  by-norm : ∀ (w w′ : FW) → proj₁ (norm w) ≡ proj₁ (norm w′) →
            tab (tW (proj₂ (norm w))) ≡ tab (tW (proj₂ (norm w′))) →
            instF w ≈ instF w′
  by-norm w w′ eh et = begin
    instF w                                               ≈⟨ norm-sound w ⟩
    halves (proj₁ (norm w)) • inst (proj₂ (norm w))       ≈⟨ refl≡ (Eq.cong (λ hs → halves hs • inst (proj₂ (norm w))) eh) ⟩
    halves (proj₁ (norm w′)) • inst (proj₂ (norm w))      ≈⟨ back (halves (proj₁ (norm w′)))
                                                               (A5-tmpl (proj₂ (norm w)) (proj₂ (norm w′)) et) ⟩
    halves (proj₁ (norm w′)) • inst (proj₂ (norm w′))     ≈⟨ sym (norm-sound w′) ⟩
    instF w′                                              ∎
