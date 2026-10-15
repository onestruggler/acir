------------------------------------------------------------------------
-- Presentations of groups
--
-- K-free words on a template of indices
--
-- Corollary A.5 (Unique.A5) turns an equation between K-free words into
-- an equation between their phased permutations, and at symbolic
-- indices that equation is a case analysis on which index meets which.
-- When the words mention only k indices, known to be distinct, the
-- analysis is the one on k *literal* indices, where it computes.  So a
-- word is written over `Fin k` and read at `Fin N` through an injection
-- ι: at an index ι x its phased permutation is ι of the template's own,
-- and away from the image of ι it is the identity (`W-prm`, `W-ph`,
-- `W-prm-off`, `W-ph-off`).  Two template words with the same table are
-- then equivalent at every injection (`A5-tmpl`), the tables compared
-- by `refl`.  Real-Clifford+CH's Auxiliary.Template, for phases in ℤ/4.
--
-- The letters of P′ carry their orderings, so a template letter is read
-- through deciding wrappers: `xd c a b` is (−1)_[c] X_[a,b] in whichever
-- order the indices come, and the empty word when they coincide; `dd`
-- likewise for the double exchange.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)

module Examples.Groups.Clifford+CS.Auxiliary.Template (N′ : ℕ) where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; zero ; suc ; _<_)
open import Data.Fin.Properties using (_≟_ ; any? ; <-cmp ; <-irrefl)
open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; tabulate ; lookup)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Data.Vec.Relation.Unary.All as All using (All)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (_F,_===_)
open import Examples.Groups.Clifford+CS.Auxiliary.NF N′
  using (KFreeʷ ; gen ; nil ; cat ; kf-pp ; kf-px ; kf-dx)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm (suc N′)
  using (Ph ; p0 ; p1 ; p2 ; p3 ; _+ᵖ_ ; +ᵖ-idʳ ; PP ; sp ; ph ; prm ; δ ; δ-≢ ; phif
       ; swapF ; swapF-o ; swapF-sym ; swapF-same ; _⊙_ ; _≐_ ; eqv ; ph≡ ; prm≡ ; idPP
       ; PH ; SWP ; L)
open import Examples.Groups.Clifford+CS.Auxiliary.Unique N′ using (A5)

private
  N : ℕ
  N = suc N′

  W : Set
  W = Word (GenP N)

------------------------------------------------------------------------
-- The deciding wrappers

-- (−1)_[c] X_[a,b], the indices in either order; ε when they coincide.
xd : Fin N → Fin N → Fin N → W
xd c a b with <-cmp a b
... | tri< lt _ _ = [ px c a b lt ]ʷ
... | tri≈ _ _ _  = ε
... | tri> _ _ gt = [ px c b a gt ]ʷ

-- X_[a,b] X_[c,d], each pair in either order; ε when a pair coincides.
dd : Fin N → Fin N → Fin N → Fin N → W
dd a b c d with <-cmp a b | <-cmp c d
... | tri< ab _ _ | tri< cd _ _ = [ dx a b c d ab cd ]ʷ
... | tri< ab _ _ | tri> _ _ dc = [ dx a b d c ab dc ]ʷ
... | tri> _ _ ba | tri< cd _ _ = [ dx b a c d ba cd ]ʷ
... | tri> _ _ ba | tri> _ _ dc = [ dx b a d c ba dc ]ʷ
... | _           | _           = ε

kf-xd : ∀ c a b → KFreeʷ (xd c a b)
kf-xd c a b with <-cmp a b
... | tri< lt _ _ = gen (kf-px c a b lt)
... | tri≈ _ _ _  = nil
... | tri> _ _ gt = gen (kf-px c b a gt)

kf-dd : ∀ a b c d → KFreeʷ (dd a b c d)
kf-dd a b c d with <-cmp a b | <-cmp c d
... | tri< ab _ _ | tri< cd _ _ = gen (kf-dx a b c d ab cd)
... | tri< ab _ _ | tri> _ _ dc = gen (kf-dx a b d c ab dc)
... | tri> _ _ ba | tri< cd _ _ = gen (kf-dx b a c d ba cd)
... | tri> _ _ ba | tri> _ _ dc = gen (kf-dx b a d c ba dc)
... | tri< _ _ _  | tri≈ _ _ _  = nil
... | tri≈ _ _ _  | _           = nil
... | tri> _ _ _  | tri≈ _ _ _  = nil

-- Their phased permutations, pointwise.
private
  irr : ∀ {a b : Fin N} → a ≡ b → a < b → ∀ {A : Set} → A
  irr e lt = ⊥-elim (<-irrefl e lt)

xd-prm : ∀ c a b i → a ≢ b → prm (sp (xd c a b)) i ≡ swapF a b i
xd-prm c a b i ne with <-cmp a b
... | tri< _ _ _  = Eq.refl
... | tri≈ _ e _  = ⊥-elim (ne e)
... | tri> _ _ _  = swapF-sym b a i

xd-ph : ∀ c a b i → a ≢ b → ph (sp (xd c a b)) i ≡ phif (δ c i) p2
xd-ph c a b i ne with <-cmp a b
... | tri< _ _ _  = +ᵖ-idʳ _
... | tri≈ _ e _  = ⊥-elim (ne e)
... | tri> _ _ _  = +ᵖ-idʳ _

xd-same : ∀ c a b → a ≡ b → sp (xd c a b) ≐ idPP
xd-same c a b e with <-cmp a b
... | tri< lt _ _ = irr e lt
... | tri≈ _ _ _  = eqv (λ _ → Eq.refl) (λ _ → Eq.refl)
... | tri> _ _ gt = irr (Eq.sym e) gt

dd-prm : ∀ a b c d i → a ≢ b → c ≢ d → prm (sp (dd a b c d)) i ≡ swapF c d (swapF a b i)
dd-prm a b c d i ne ne′ with <-cmp a b | <-cmp c d
... | tri< _ _ _ | tri< _ _ _ = Eq.refl
... | tri< _ _ _ | tri> _ _ _ = swapF-sym d c (swapF a b i)
... | tri> _ _ _ | tri< _ _ _ = Eq.cong (swapF c d) (swapF-sym b a i)
... | tri> _ _ _ | tri> _ _ _ =
  Eq.trans (swapF-sym d c (swapF b a i)) (Eq.cong (swapF c d) (swapF-sym b a i))
... | tri≈ _ e _ | _          = ⊥-elim (ne e)
... | tri< _ _ _ | tri≈ _ e _ = ⊥-elim (ne′ e)
... | tri> _ _ _ | tri≈ _ e _ = ⊥-elim (ne′ e)

dd-ph : ∀ a b c d i → ph (sp (dd a b c d)) i ≡ p0
dd-ph a b c d i with <-cmp a b | <-cmp c d
... | tri< _ _ _ | tri< _ _ _ = Eq.refl
... | tri< _ _ _ | tri> _ _ _ = Eq.refl
... | tri> _ _ _ | tri< _ _ _ = Eq.refl
... | tri> _ _ _ | tri> _ _ _ = Eq.refl
... | tri< _ _ _ | tri≈ _ _ _ = Eq.refl
... | tri≈ _ _ _ | _          = Eq.refl
... | tri> _ _ _ | tri≈ _ _ _ = Eq.refl

dd-same : ∀ a b c d → (a ≡ b) → sp (dd a b c d) ≐ idPP
dd-same a b c d e with <-cmp a b | <-cmp c d
... | tri< lt _ _ | _          = irr e lt
... | tri> _ _ gt | _          = irr (Eq.sym e) gt
... | tri≈ _ _ _  | _          = eqv (λ _ → Eq.refl) (λ _ → Eq.refl)

dd-same′ : ∀ a b c d → (c ≡ d) → sp (dd a b c d) ≐ idPP
dd-same′ a b c d e with <-cmp a b | <-cmp c d
... | _           | tri< lt _ _ = irr e lt
... | _           | tri> _ _ gt = irr (Eq.sym e) gt
... | tri< _ _ _  | tri≈ _ _ _  = eqv (λ _ → Eq.refl) (λ _ → Eq.refl)
... | tri≈ _ _ _  | tri≈ _ _ _  = eqv (λ _ → Eq.refl) (λ _ → Eq.refl)
... | tri> _ _ _  | tri≈ _ _ _  = eqv (λ _ → Eq.refl) (λ _ → Eq.refl)

------------------------------------------------------------------------
-- Template words

-- The three K-free letter shapes, over k indices: a phase pair, a sign
-- with an exchange, and two exchanges.
data TL (k : ℕ) : Set where
  tp : Fin k → Fin k → TL k
  tx : Fin k → Fin k → Fin k → TL k
  td : Fin k → Fin k → Fin k → Fin k → TL k

-- Words, bracketed as words are, so that a template reads back as the
-- word of the goal it is used on whatever its bracketing.
infixr 7 _•ᵗ_
data TW (k : ℕ) : Set where
  emp   : TW k
  ⌜_⌝   : TL k → TW k
  _•ᵗ_  : TW k → TW k → TW k

------------------------------------------------------------------------
-- Their phased permutations, on the template's own indices

record TS (k : ℕ) : Set where
  constructor ts
  field
    tph : Fin k → Ph
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

  idk : TS k
  idk = ts (λ _ → p0) (λ i → i)

  infixr 7 _⊙ₖ_
  _⊙ₖ_ : TS k → TS k → TS k
  f ⊙ₖ g = ts (λ i → tph f i +ᵖ tph g (tpm f i)) (λ i → tpm g (tpm f i))

  PHk : Fin k → Ph → TS k
  PHk c q = ts (λ i → phif (δk c i) q) (λ i → i)

  SWk : Fin k → Fin k → TS k
  SWk a b = ts (λ _ → p0) (swk a b)

  tL : TL k → TS k
  tL (tp i j) = PHk i p1 ⊙ₖ PHk j p3
  tL (tx c i j) with i ≟ j
  ... | yes _ = idk
  ... | no  _ = PHk c p2 ⊙ₖ SWk i j
  tL (td i j i′ j′) with i ≟ j
  ... | yes _ = idk
  ... | no  _ with i′ ≟ j′
  ...         | yes _ = idk
  ...         | no  _ = SWk i j ⊙ₖ SWk i′ j′

  tW : TW k → TS k
  tW emp       = idk
  tW ⌜ l ⌝     = tL l
  tW (w •ᵗ w′) = tW w ⊙ₖ tW w′

  -- The table of a template phased permutation, which `refl` compares.
  tab : TS k → Vec Ph k × Vec (Fin k) k
  tab f = tabulate (tph f) , tabulate (tpm f)

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
  instL (tp i j)       = [ pp (ι i) (ι j) ]ʷ
  instL (tx c i j)     = xd (ι c) (ι i) (ι j)
  instL (td i j i′ j′) = dd (ι i) (ι j) (ι i′) (ι j′)

  inst : TW k → W
  inst emp       = ε
  inst ⌜ l ⌝     = instL l
  inst (w •ᵗ w′) = inst w • inst w′

  kf-instL : ∀ (l : TL k) → KFreeʷ (instL l)
  kf-instL (tp i j)       = gen (kf-pp (ι i) (ι j))
  kf-instL (tx c i j)     = kf-xd (ι c) (ι i) (ι j)
  kf-instL (td i j i′ j′) = kf-dd (ι i) (ι j) (ι i′) (ι j′)

  kf-inst : ∀ (w : TW k) → KFreeʷ (inst w)
  kf-inst emp       = nil
  kf-inst ⌜ l ⌝     = kf-instL l
  kf-inst (w •ᵗ w′) = cat (kf-inst w) (kf-inst w′)

  -- An index off the image of ι.
  Off : Fin N → Set
  Off y = ∀ (x : Fin k) → ι x ≢ y

  ----------------------------------------------------------------------
  -- The atoms commute with ι

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

  private
    ι≢ : ∀ {i j : Fin k} → i ≢ j → ι i ≢ ι j
    ι≢ ne e = ne (inj e)

  ----------------------------------------------------------------------
  -- Letters

  L-prm : ∀ (l : TL k) (x : Fin k) → prm (sp (instL l)) (ι x) ≡ ι (tpm (tL l) x)
  L-prm (tp i j) x = Eq.refl
  L-prm (tx c i j) x with i ≟ j
  ... | yes e  = prm≡ (xd-same (ι c) (ι i) (ι j) (Eq.cong ι e)) (ι x)
  ... | no  ne = Eq.trans (xd-prm (ι c) (ι i) (ι j) (ι x) (ι≢ ne)) (sw-ι i j x)
  L-prm (td i j i′ j′) x with i ≟ j
  ... | yes e  = prm≡ (dd-same (ι i) (ι j) (ι i′) (ι j′) (Eq.cong ι e)) (ι x)
  ... | no  ne with i′ ≟ j′
  ...          | yes e′ = prm≡ (dd-same′ (ι i) (ι j) (ι i′) (ι j′) (Eq.cong ι e′)) (ι x)
  ...          | no ne′ =
    Eq.trans (dd-prm (ι i) (ι j) (ι i′) (ι j′) (ι x) (ι≢ ne) (ι≢ ne′))
      (Eq.trans (Eq.cong (swapF (ι i′) (ι j′)) (sw-ι i j x)) (sw-ι i′ j′ (swk i j x)))

  L-ph : ∀ (l : TL k) (x : Fin k) → ph (sp (instL l)) (ι x) ≡ tph (tL l) x
  L-ph (tp i j) x =
    Eq.cong₂ _+ᵖ_ (Eq.cong (λ b → phif b p1) (δ-ι i x)) (Eq.cong (λ b → phif b p3) (δ-ι j x))
  L-ph (tx c i j) x with i ≟ j
  ... | yes e  = ph≡ (xd-same (ι c) (ι i) (ι j) (Eq.cong ι e)) (ι x)
  ... | no  ne =
    Eq.trans (xd-ph (ι c) (ι i) (ι j) (ι x) (ι≢ ne))
      (Eq.trans (Eq.cong (λ b → phif b p2) (δ-ι c x)) (Eq.sym (+ᵖ-idʳ _)))
  L-ph (td i j i′ j′) x with i ≟ j
  ... | yes e  = ph≡ (dd-same (ι i) (ι j) (ι i′) (ι j′) (Eq.cong ι e)) (ι x)
  ... | no  ne with i′ ≟ j′
  ...          | yes e′ = ph≡ (dd-same′ (ι i) (ι j) (ι i′) (ι j′) (Eq.cong ι e′)) (ι x)
  ...          | no ne′ = dd-ph (ι i) (ι j) (ι i′) (ι j′) (ι x)

  L-prm-off : ∀ (l : TL k) (y : Fin N) → Off y → prm (sp (instL l)) y ≡ y
  L-prm-off (tp i j) y off = Eq.refl
  L-prm-off (tx c i j) y off with ι i ≟ ι j
  ... | yes e  = prm≡ (xd-same (ι c) (ι i) (ι j) e) y
  ... | no  ne = Eq.trans (xd-prm (ι c) (ι i) (ι j) y ne) (sw-off i j y off)
  L-prm-off (td i j i′ j′) y off with ι i ≟ ι j
  ... | yes e  = prm≡ (dd-same (ι i) (ι j) (ι i′) (ι j′) e) y
  ... | no  ne with ι i′ ≟ ι j′
  ...          | yes e′ = prm≡ (dd-same′ (ι i) (ι j) (ι i′) (ι j′) e′) y
  ...          | no ne′ =
    Eq.trans (dd-prm (ι i) (ι j) (ι i′) (ι j′) y ne ne′)
      (Eq.trans (Eq.cong (swapF (ι i′) (ι j′)) (sw-off i j y off)) (sw-off i′ j′ y off))

  L-ph-off : ∀ (l : TL k) (y : Fin N) → Off y → ph (sp (instL l)) y ≡ p0
  L-ph-off (tp i j) y off =
    Eq.cong₂ _+ᵖ_ (Eq.cong (λ b → phif b p1) (δ-off i y off))
                  (Eq.cong (λ b → phif b p3) (δ-off j y off))
  L-ph-off (tx c i j) y off with ι i ≟ ι j
  ... | yes e  = ph≡ (xd-same (ι c) (ι i) (ι j) e) y
  ... | no  ne = Eq.trans (xd-ph (ι c) (ι i) (ι j) y ne) (Eq.cong (λ b → phif b p2) (δ-off c y off))
  L-ph-off (td i j i′ j′) y off = dd-ph (ι i) (ι j) (ι i′) (ι j′) y

  ----------------------------------------------------------------------
  -- Words

  W-prm : ∀ (w : TW k) (x : Fin k) → prm (sp (inst w)) (ι x) ≡ ι (tpm (tW w) x)
  W-prm emp       x = Eq.refl
  W-prm ⌜ l ⌝     x = L-prm l x
  W-prm (w •ᵗ w′) x =
    Eq.trans (Eq.cong (prm (sp (inst w′))) (W-prm w x)) (W-prm w′ (tpm (tW w) x))

  W-ph : ∀ (w : TW k) (x : Fin k) → ph (sp (inst w)) (ι x) ≡ tph (tW w) x
  W-ph emp       x = Eq.refl
  W-ph ⌜ l ⌝     x = L-ph l x
  W-ph (w •ᵗ w′) x =
    Eq.cong₂ _+ᵖ_ (W-ph w x)
      (Eq.trans (Eq.cong (ph (sp (inst w′))) (W-prm w x)) (W-ph w′ (tpm (tW w) x)))

  W-prm-off : ∀ (w : TW k) (y : Fin N) → Off y → prm (sp (inst w)) y ≡ y
  W-prm-off emp       y off = Eq.refl
  W-prm-off ⌜ l ⌝     y off = L-prm-off l y off
  W-prm-off (w •ᵗ w′) y off =
    Eq.trans (Eq.cong (prm (sp (inst w′))) (W-prm-off w y off)) (W-prm-off w′ y off)

  W-ph-off : ∀ (w : TW k) (y : Fin N) → Off y → ph (sp (inst w)) y ≡ p0
  W-ph-off emp       y off = Eq.refl
  W-ph-off ⌜ l ⌝     y off = L-ph-off l y off
  W-ph-off (w •ᵗ w′) y off =
    Eq.cong₂ _+ᵖ_ (W-ph-off w y off)
      (Eq.trans (Eq.cong (ph (sp (inst w′))) (W-prm-off w y off)) (W-ph-off w′ y off))

  ----------------------------------------------------------------------
  -- Tables decide equations

  private
    tab-prm : ∀ {f g : TS k} → tab f ≡ tab g → ∀ (x : Fin k) → tpm f x ≡ tpm g x
    tab-prm {f} {g} e x =
      Eq.trans (Eq.sym (lookup∘tabulate (tpm f) x))
        (Eq.trans (Eq.cong (λ t → lookup (proj₂ t) x) e) (lookup∘tabulate (tpm g) x))

    tab-ph : ∀ {f g : TS k} → tab f ≡ tab g → ∀ (x : Fin k) → tph f x ≡ tph g x
    tab-ph {f} {g} e x =
      Eq.trans (Eq.sym (lookup∘tabulate (tph f) x))
        (Eq.trans (Eq.cong (λ t → lookup (proj₁ t) x) e) (lookup∘tabulate (tph g) x))

  -- Two template words with the same table have the same phased
  -- permutation at ι: on the image by the tables, off it both are the
  -- identity.
  same-sp : ∀ (w w′ : TW k) → tab (tW w) ≡ tab (tW w′) → sp (inst w) ≐ sp (inst w′)
  same-sp w w′ e = eqv phs pm
    where
    phs : ∀ (y : Fin N) → ph (sp (inst w)) y ≡ ph (sp (inst w′)) y
    phs y with any? (λ x → ι x ≟ y)
    ... | yes (x , Eq.refl) =
      Eq.trans (W-ph w x) (Eq.trans (tab-ph e x) (Eq.sym (W-ph w′ x)))
    ... | no ¬∃ = Eq.trans (W-ph-off w y off) (Eq.sym (W-ph-off w′ y off))
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
            PB._≈_ (N F,_===_) (inst w) (inst w′)
  A5-tmpl w w′ e = A5 (kf-inst w) (kf-inst w′) (same-sp w w′ e)
