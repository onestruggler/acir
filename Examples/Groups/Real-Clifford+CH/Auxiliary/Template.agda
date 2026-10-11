------------------------------------------------------------------------
-- Presentations of groups
--
-- Hadamard-free words on a template of indices
--
-- Corollary A.5 turns an equation between Hadamard-free words into an
-- equation between their signed permutations, and at symbolic indices
-- that equation is a case analysis on which index meets which.  When
-- the words mention only k indices, known to be distinct, the analysis
-- is the one on k *literal* indices, where it computes.  So a word is
-- written over `Fin k` and read at `Fin N` through an injection ι: at
-- an index ι x its signed permutation is ι of the template's own, and
-- away from the image of ι it is the identity (`W-prm`, `W-sgn`,
-- `W-prm-off`, `W-sgn-off`).  Two template words with the same table
-- are then equivalent at every injection (`A5-tmpl`), and the tables
-- are compared by `refl`.  `prm-at`, `sgn-at` and `inv-tmpl` read off
-- the side conditions `Move.hh-pass` asks for the same way.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Template (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Properties using (_≟_ ; any?)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; tabulate ; lookup)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Data.Vec.Relation.Unary.All as All using (All)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP ; XX)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; zx ; xx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (SP ; sp ; sgn ; prm ; δ ; δ-≢ ; swapF ; swapF-o ; _⊙_ ; _≐_ ; eqv ; idSP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (HFreeʷ ; gen ; nil ; cat ; hf-zz ; hf-xx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm m using (hfree-zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m using (A5-full)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

------------------------------------------------------------------------
-- Template words

-- The three Hadamard-free letter shapes, over k indices: a sign pair,
-- a sign with an exchange, and two exchanges.
data TL (k : ℕ) : Set where
  tz : Fin k → Fin k → TL k
  ty : Fin k → Fin k → Fin k → TL k
  tx : Fin k → Fin k → Fin k → Fin k → TL k

-- Words, bracketed as words are, so that a template reads back as the
-- word of the goal it is used on whatever its bracketing.
infixr 7 _•ᵗ_
data TW (k : ℕ) : Set where
  emp   : TW k
  ⌜_⌝   : TL k → TW k
  _•ᵗ_  : TW k → TW k → TW k

------------------------------------------------------------------------
-- Their signed permutations, on the template's own indices

record TS (k : ℕ) : Set where
  constructor ts
  field
    tsg : Fin k → Bool
    tpm : Fin k → Fin k

open TS public

module _ {k : ℕ} where

  δk : Fin k → Fin k → Bool
  δk c i with i ≟ c
  ... | yes _ = true
  ... | no  _ = false

  swk : Fin k → Fin k → Fin k → Fin k
  swk a b i with i ≟ a
  ... | yes _ = b
  ... | no  _ with i ≟ b
  ...         | yes _ = a
  ...         | no  _ = i

  swk-invol : ∀ (a b i : Fin k) → swk a b (swk a b i) ≡ i
  swk-invol a b i with i ≟ a
  swk-invol a b i | yes Eq.refl with b ≟ a
  ...                           | yes Eq.refl = Eq.refl
  ...                           | no  _ with b ≟ b
  ...                                   | yes _  = Eq.refl
  ...                                   | no  ne = ⊥-elim (ne Eq.refl)
  swk-invol a b i | no ia with i ≟ b
  swk-invol a b i | no ia | yes Eq.refl with a ≟ a
  ...                                   | yes _  = Eq.refl
  ...                                   | no  ne = ⊥-elim (ne Eq.refl)
  swk-invol a b i | no ia | no ib with i ≟ a
  ...                             | yes e = ⊥-elim (ia e)
  ...                             | no  _ with i ≟ b
  ...                                     | yes e = ⊥-elim (ib e)
  ...                                     | no  _ = Eq.refl

  idk : TS k
  idk = ts (λ _ → false) (λ i → i)

  infixr 7 _⊙ₖ_
  _⊙ₖ_ : TS k → TS k → TS k
  f ⊙ₖ g = ts (λ i → tsg f i xor tsg g (tpm f i)) (λ i → tpm g (tpm f i))

  negk : Fin k → TS k
  negk c = ts (δk c) (λ i → i)

  swpk : Fin k → Fin k → TS k
  swpk a b = ts (λ _ → false) (swk a b)

  -- The same decisions as the wrappers `zx` and `xx`: a letter whose
  -- indices coincide is the empty word.
  tL : TL k → TS k
  tL (tz i j) = negk i ⊙ₖ negk j
  tL (ty c i j) with i ≟ j
  ... | yes _ = idk
  ... | no  _ = negk c ⊙ₖ swpk i j
  tL (tx i j i′ j′) with i ≟ j
  ... | yes _ = idk
  ... | no  _ with i′ ≟ j′
  ...         | yes _ = idk
  ...         | no  _ = swpk i j ⊙ₖ swpk i′ j′

  tW : TW k → TS k
  tW emp       = idk
  tW ⌜ l ⌝     = tL l
  tW (w •ᵗ w′) = tW w ⊙ₖ tW w′

  -- The table of a template signed permutation, which `refl` compares.
  tab : TS k → Vec Bool k × Vec (Fin k) k
  tab f = tabulate (tsg f) , tabulate (tpm f)

------------------------------------------------------------------------
-- Pairwise distinct indices, and the injection they are

infixr 5 _∷ᵈ_
data Distinct : ∀ {k : ℕ} → Vec (Fin N) k → Set where
  []ᵈ  : Distinct []
  _∷ᵈ_ : ∀ {k : ℕ} {x : Fin N} {xs : Vec (Fin N) k} →
         All (λ y → y ≢ x) xs → Distinct xs → Distinct (x ∷ xs)

allAt : ∀ {k : ℕ} {P : Fin N → Set} {xs : Vec (Fin N) k} → All P xs →
        ∀ (i : Fin k) → P (lookup xs i)
allAt (p All.∷ _)  zero    = p
allAt (_ All.∷ ps) (suc i) = allAt ps i

lookup-inj : ∀ {k : ℕ} {v : Vec (Fin N) k} → Distinct v →
             ∀ {i j : Fin k} → lookup v i ≡ lookup v j → i ≡ j
lookup-inj (_  ∷ᵈ d) {zero}  {zero}  e = Eq.refl
lookup-inj (nx ∷ᵈ d) {zero}  {suc j} e = ⊥-elim (allAt nx j (Eq.sym e))
lookup-inj (nx ∷ᵈ d) {suc i} {zero}  e = ⊥-elim (allAt nx i e)
lookup-inj (_  ∷ᵈ d) {suc i} {suc j} e = Eq.cong suc (lookup-inj d e)

------------------------------------------------------------------------
-- Reading a template at an injection

module At {k : ℕ} (ι : Fin k → Fin N)
          (inj : ∀ {x y : Fin k} → ι x ≡ ι y → x ≡ y) where

  instL : TL k → W
  instL (tz i j)       = zz (ι i) (ι j)
  instL (ty c i j)     = zx (ι c) (ι i) (ι j)
  instL (tx i j i′ j′) = xx (ι i) (ι j) (ι i′) (ι j′)

  inst : TW k → W
  inst emp       = ε
  inst ⌜ l ⌝     = instL l
  inst (w •ᵗ w′) = inst w • inst w′

  private
    hfree-xx : ∀ (a b c d : Fin N) → HFreeʷ (xx {₃₊ m} a b c d)
    hfree-xx a b c d with a ≟ b
    ... | yes _ = nil
    ... | no ab with c ≟ d
    ...         | yes _ = nil
    ...         | no cd = gen (hf-xx a b c d ab cd)

  hf-instL : ∀ (l : TL k) → HFreeʷ (instL l)
  hf-instL (tz i j)       = gen (hf-zz (ι i) (ι j))
  hf-instL (ty c i j)     = hfree-zx (ι c) (ι i) (ι j)
  hf-instL (tx i j i′ j′) = hfree-xx (ι i) (ι j) (ι i′) (ι j′)

  hf-inst : ∀ (w : TW k) → HFreeʷ (inst w)
  hf-inst emp       = nil
  hf-inst ⌜ l ⌝     = hf-instL l
  hf-inst (w •ᵗ w′) = cat (hf-inst w) (hf-inst w′)

  -- An index off the image of ι.
  Off : Fin N → Set
  Off y = ∀ (x : Fin k) → ι x ≢ y

  ----------------------------------------------------------------------
  -- The atoms commute with ι

  private
    δ-ι : ∀ (c x : Fin k) → δ (ι c) (ι x) ≡ δk c x
    δ-ι c x with ι x ≟ ι c | x ≟ c
    ... | yes _ | yes _  = Eq.refl
    ... | yes e | no  ne = ⊥-elim (ne (inj e))
    ... | no ne | yes e  = ⊥-elim (ne (Eq.cong ι e))
    ... | no _  | no  _  = Eq.refl

    δ-off : ∀ (c : Fin k) (y : Fin N) → Off y → δ (ι c) y ≡ false
    δ-off c y off = δ-≢ (ι c) y (λ e → off c (Eq.sym e))

    sw-ι : ∀ (a b x : Fin k) → swapF (ι a) (ι b) (ι x) ≡ ι (swk a b x)
    sw-ι a b x with ι x ≟ ι a | x ≟ a
    ... | yes _ | yes _  = Eq.refl
    ... | yes e | no  ne = ⊥-elim (ne (inj e))
    ... | no ne | yes e  = ⊥-elim (ne (Eq.cong ι e))
    ... | no _  | no  _  with ι x ≟ ι b | x ≟ b
    ...                  | yes _ | yes _  = Eq.refl
    ...                  | yes e | no  ne = ⊥-elim (ne (inj e))
    ...                  | no ne | yes e  = ⊥-elim (ne (Eq.cong ι e))
    ...                  | no _  | no  _  = Eq.refl

    sw-off : ∀ (a b : Fin k) (y : Fin N) → Off y → swapF (ι a) (ι b) y ≡ y
    sw-off a b y off =
      swapF-o (ι a) (ι b) y (λ e → off a (Eq.sym e)) (λ e → off b (Eq.sym e))

    xor-f : ∀ (x : Bool) → x xor false ≡ x
    xor-f true  = Eq.refl
    xor-f false = Eq.refl

  -- Exported for the inverse of a template letter.
  swap-ι : ∀ (a b x : Fin k) → swapF (ι a) (ι b) (ι x) ≡ ι (swk a b x)
  swap-ι = sw-ι

  ----------------------------------------------------------------------
  -- Letters

  L-prm : ∀ (l : TL k) (x : Fin k) → prm (sp (instL l)) (ι x) ≡ ι (tpm (tL l) x)
  L-prm (tz i j) x = Eq.refl
  L-prm (ty c i j) x with ι i ≟ ι j | i ≟ j
  ... | yes _ | yes _  = Eq.refl
  ... | yes e | no  ne = ⊥-elim (ne (inj e))
  ... | no ne | yes e  = ⊥-elim (ne (Eq.cong ι e))
  ... | no _  | no  _  = sw-ι i j x
  L-prm (tx i j i′ j′) x with ι i ≟ ι j | i ≟ j
  ... | yes _ | yes _  = Eq.refl
  ... | yes e | no  ne = ⊥-elim (ne (inj e))
  ... | no ne | yes e  = ⊥-elim (ne (Eq.cong ι e))
  ... | no _  | no  _  with ι i′ ≟ ι j′ | i′ ≟ j′
  ...                  | yes _ | yes _  = Eq.refl
  ...                  | yes e | no  ne = ⊥-elim (ne (inj e))
  ...                  | no ne | yes e  = ⊥-elim (ne (Eq.cong ι e))
  ...                  | no _  | no  _  =
    Eq.trans (Eq.cong (swapF (ι i′) (ι j′)) (sw-ι i j x)) (sw-ι i′ j′ (swk i j x))

  L-sgn : ∀ (l : TL k) (x : Fin k) → sgn (sp (instL l)) (ι x) ≡ tsg (tL l) x
  L-sgn (tz i j) x = Eq.cong₂ _xor_ (δ-ι i x) (δ-ι j x)
  L-sgn (ty c i j) x with ι i ≟ ι j | i ≟ j
  ... | yes _ | yes _  = Eq.refl
  ... | yes e | no  ne = ⊥-elim (ne (inj e))
  ... | no ne | yes e  = ⊥-elim (ne (Eq.cong ι e))
  ... | no _  | no  _  = Eq.cong (_xor false) (δ-ι c x)
  L-sgn (tx i j i′ j′) x with ι i ≟ ι j | i ≟ j
  ... | yes _ | yes _  = Eq.refl
  ... | yes e | no  ne = ⊥-elim (ne (inj e))
  ... | no ne | yes e  = ⊥-elim (ne (Eq.cong ι e))
  ... | no _  | no  _  with ι i′ ≟ ι j′ | i′ ≟ j′
  ...                  | yes _ | yes _  = Eq.refl
  ...                  | yes e | no  ne = ⊥-elim (ne (inj e))
  ...                  | no ne | yes e  = ⊥-elim (ne (Eq.cong ι e))
  ...                  | no _  | no  _  = Eq.refl

  L-prm-off : ∀ (l : TL k) (y : Fin N) → Off y → prm (sp (instL l)) y ≡ y
  L-prm-off (tz i j) y off = Eq.refl
  L-prm-off (ty c i j) y off with ι i ≟ ι j
  ... | yes _ = Eq.refl
  ... | no  _ = sw-off i j y off
  L-prm-off (tx i j i′ j′) y off with ι i ≟ ι j
  ... | yes _ = Eq.refl
  ... | no  _ with ι i′ ≟ ι j′
  ...         | yes _ = Eq.refl
  ...         | no  _ =
    Eq.trans (Eq.cong (swapF (ι i′) (ι j′)) (sw-off i j y off)) (sw-off i′ j′ y off)

  L-sgn-off : ∀ (l : TL k) (y : Fin N) → Off y → sgn (sp (instL l)) y ≡ false
  L-sgn-off (tz i j) y off = Eq.cong₂ _xor_ (δ-off i y off) (δ-off j y off)
  L-sgn-off (ty c i j) y off with ι i ≟ ι j
  ... | yes _ = Eq.refl
  ... | no  _ = Eq.trans (xor-f (δ (ι c) y)) (δ-off c y off)
  L-sgn-off (tx i j i′ j′) y off with ι i ≟ ι j
  ... | yes _ = Eq.refl
  ... | no  _ with ι i′ ≟ ι j′
  ...         | yes _ = Eq.refl
  ...         | no  _ = Eq.refl

  ----------------------------------------------------------------------
  -- Words

  W-prm : ∀ (w : TW k) (x : Fin k) → prm (sp (inst w)) (ι x) ≡ ι (tpm (tW w) x)
  W-prm emp       x = Eq.refl
  W-prm ⌜ l ⌝     x = L-prm l x
  W-prm (w •ᵗ w′) x =
    Eq.trans (Eq.cong (prm (sp (inst w′))) (W-prm w x)) (W-prm w′ (tpm (tW w) x))

  W-sgn : ∀ (w : TW k) (x : Fin k) → sgn (sp (inst w)) (ι x) ≡ tsg (tW w) x
  W-sgn emp       x = Eq.refl
  W-sgn ⌜ l ⌝     x = L-sgn l x
  W-sgn (w •ᵗ w′) x =
    Eq.cong₂ _xor_ (W-sgn w x)
      (Eq.trans (Eq.cong (sgn (sp (inst w′))) (W-prm w x)) (W-sgn w′ (tpm (tW w) x)))

  W-prm-off : ∀ (w : TW k) (y : Fin N) → Off y → prm (sp (inst w)) y ≡ y
  W-prm-off emp       y off = Eq.refl
  W-prm-off ⌜ l ⌝     y off = L-prm-off l y off
  W-prm-off (w •ᵗ w′) y off =
    Eq.trans (Eq.cong (prm (sp (inst w′))) (W-prm-off w y off)) (W-prm-off w′ y off)

  W-sgn-off : ∀ (w : TW k) (y : Fin N) → Off y → sgn (sp (inst w)) y ≡ false
  W-sgn-off emp       y off = Eq.refl
  W-sgn-off ⌜ l ⌝     y off = L-sgn-off l y off
  W-sgn-off (w •ᵗ w′) y off =
    Eq.cong₂ _xor_ (W-sgn-off w y off)
      (Eq.trans (Eq.cong (sgn (sp (inst w′))) (W-prm-off w y off)) (W-sgn-off w′ y off))

  ----------------------------------------------------------------------
  -- Tables decide equations

  private
    tab-prm : ∀ {f g : TS k} → tab f ≡ tab g → ∀ (x : Fin k) → tpm f x ≡ tpm g x
    tab-prm {f} {g} e x =
      Eq.trans (Eq.sym (lookup∘tabulate (tpm f) x))
        (Eq.trans (Eq.cong (λ t → lookup (proj₂ t) x) e) (lookup∘tabulate (tpm g) x))

    tab-sgn : ∀ {f g : TS k} → tab f ≡ tab g → ∀ (x : Fin k) → tsg f x ≡ tsg g x
    tab-sgn {f} {g} e x =
      Eq.trans (Eq.sym (lookup∘tabulate (tsg f) x))
        (Eq.trans (Eq.cong (λ t → lookup (proj₁ t) x) e) (lookup∘tabulate (tsg g) x))

  -- Two template words with the same table have the same signed
  -- permutation at ι: on the image by the tables, off it both are the
  -- identity.
  same-sp : ∀ (w w′ : TW k) → tab (tW w) ≡ tab (tW w′) → sp (inst w) ≐ sp (inst w′)
  same-sp w w′ e = eqv sg pm
    where
    sg : ∀ (y : Fin N) → sgn (sp (inst w)) y ≡ sgn (sp (inst w′)) y
    sg y with any? (λ x → ι x ≟ y)
    ... | yes (x , Eq.refl) =
      Eq.trans (W-sgn w x) (Eq.trans (tab-sgn e x) (Eq.sym (W-sgn w′ x)))
    ... | no ¬∃ = Eq.trans (W-sgn-off w y off) (Eq.sym (W-sgn-off w′ y off))
      where
      off : Off y
      off x h = ¬∃ (x , h)

    pm : ∀ (y : Fin N) → prm (sp (inst w)) y ≡ prm (sp (inst w′)) y
    pm y with any? (λ x → ι x ≟ y)
    ... | yes (x , Eq.refl) =
      Eq.trans (W-prm w x) (Eq.trans (Eq.cong ι (tab-prm e x)) (Eq.sym (W-prm w′ x)))
    ... | no ¬∃ = Eq.trans (W-prm-off w y off) (Eq.sym (W-prm-off w′ y off))
      where
      off : Off y
      off x h = ¬∃ (x , h)

  -- Corollary A.5, decided on the template.
  A5-tmpl : ∀ (w w′ : TW k) → tab (tW w) ≡ tab (tW w′) →
            PB._≈_ (m P,_===_) (inst w) (inst w′)
  A5-tmpl w w′ e = A5-full (hf-inst w) (hf-inst w′) (same-sp w w′ e)

  -- The side conditions of `Move.hh-pass`, read off the template.
  prm-at : ∀ (w : TW k) (x : Fin k) → prm (sp (inst w)) (ι x) ≡ ι (tpm (tW w) x)
  prm-at = W-prm

  sgn-at : ∀ (w : TW k) (x : Fin k) → sgn (sp (inst w)) (ι x) ≡ tsg (tW w) x
  sgn-at = W-sgn

  inv-tmpl : ∀ (w w′ : TW k) → tab (tW w ⊙ₖ tW w′) ≡ tab idk →
             sp (inst w) ⊙ sp (inst w′) ≐ idSP
  inv-tmpl w w′ e = eqv sg pm
    where
    sg : ∀ (y : Fin N) → sgn (sp (inst w) ⊙ sp (inst w′)) y ≡ false
    sg y with any? (λ x → ι x ≟ y)
    ... | yes (x , Eq.refl) =
      Eq.trans (Eq.cong₂ _xor_ (W-sgn w x)
                  (Eq.trans (Eq.cong (sgn (sp (inst w′))) (W-prm w x))
                            (W-sgn w′ (tpm (tW w) x))))
               (tab-sgn e x)
    ... | no ¬∃ =
      Eq.cong₂ _xor_ (W-sgn-off w y off)
        (Eq.trans (Eq.cong (sgn (sp (inst w′))) (W-prm-off w y off)) (W-sgn-off w′ y off))
      where
      off : Off y
      off x h = ¬∃ (x , h)

    pm : ∀ (y : Fin N) → prm (sp (inst w) ⊙ sp (inst w′)) y ≡ y
    pm y with any? (λ x → ι x ≟ y)
    ... | yes (x , Eq.refl) =
      Eq.trans (Eq.cong (prm (sp (inst w′))) (W-prm w x))
        (Eq.trans (W-prm w′ (tpm (tW w) x)) (Eq.cong ι (tab-prm e x)))
    ... | no ¬∃ =
      Eq.trans (Eq.cong (prm (sp (inst w′))) (W-prm-off w y off)) (W-prm-off w′ y off)
      where
      off : Off y
      off x h = ¬∃ (x , h)
