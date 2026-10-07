------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma A.1: an equation of Figure 7 holds at every tuple of distinct
-- indices once it holds at one (Clément, Appendix A.2, "we can rename
-- the indices arbitrarily")
--
-- Conjugating a letter by X_[x,y] exchanges x and y in it
-- (LemmaA1.Base, seventeen cases), so conjugating a proper word by a
-- product of exchanges renames its indices by the composite of the
-- transpositions (`conj*`), and an equation between proper words is
-- carried to its renamed instance (`move`).  `build` makes the product
-- for a given assignment of distinct targets to distinct indices: each
-- index in turn is sent where it should go by one more transposition,
-- which leaves the earlier ones alone because their images are already
-- distinct targets (`build-ok`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.Rename (N : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; zero ; suc ; _≟_)
open import Data.List using (List ; [] ; _∷_)
open import Data.Product using (_,_)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup)
open import Data.Vec.Relation.Unary.All using (All ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics
  using (Gen ; −1[_] ; X[_,_] ; H[_,_] ; −1 ; X ; H ; _G,_===_ ;
         ProperG ; −1ᵖ ; Xᵖ ; Hᵖ ; Proper)
open _G,_===_
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.Base N

open Tools (N G,_===_)

private
  variable
    k : ℕ
    x y : Fin N

------------------------------------------------------------------------
-- The transposition of two indices

pick : ∀ {z x y : Fin N} → Dec (z ≡ x) → Dec (z ≡ y) → Fin N
pick {z} {x} {y} (yes _) _       = y
pick {z} {x} {y} (no _)  (yes _) = x
pick {z} {x} {y} (no _)  (no _)  = z

τ : Fin N → Fin N → Fin N → Fin N
τ x y z = pick {z} {x} {y} (z ≟ x) (z ≟ y)

τ-x : ∀ (x y : Fin N) → τ x y x ≡ y
τ-x x y with x ≟ x
... | yes _ = Eq.refl
... | no ne = ⊥-elim (ne Eq.refl)

τ-y : ∀ (x y : Fin N) → x ≢ y → τ x y y ≡ x
τ-y x y xy with y ≟ x
... | yes e = ⊥-elim (xy (Eq.sym e))
... | no _ with y ≟ y
...   | yes _ = Eq.refl
...   | no ne = ⊥-elim (ne Eq.refl)

τ-o : ∀ (x y z : Fin N) → z ≢ x → z ≢ y → τ x y z ≡ z
τ-o x y z zx zy with z ≟ x
... | yes e = ⊥-elim (zx e)
... | no _ with z ≟ y
...   | yes e = ⊥-elim (zy e)
...   | no _  = Eq.refl

-- A transposition is an involution, hence injective.
τ-τ : ∀ (x y z : Fin N) → x ≢ y → τ x y (τ x y z) ≡ z
τ-τ x y z xy with z ≟ x
... | yes Eq.refl = τ-y x y xy
... | no zx with z ≟ y
...   | yes Eq.refl = τ-x x y
...   | no zy = τ-o x y z zx zy

τ-inj : ∀ (x y : Fin N) → x ≢ y → ∀ {u v} → τ x y u ≡ τ x y v → u ≡ v
τ-inj x y xy {u} {v} e =
  Eq.trans (Eq.sym (τ-τ x y u xy)) (Eq.trans (Eq.cong (τ x y) e) (τ-τ x y v xy))

------------------------------------------------------------------------
-- Renaming the indices of a word

ren : (Fin N → Fin N) → Gen N → Gen N
ren σ −1[ a ]    = −1[ σ a ]
ren σ X[ a , b ] = X[ σ a , σ b ]
ren σ H[ a , b ] = H[ σ a , σ b ]

renʷ : (Fin N → Fin N) → Word (Gen N) → Word (Gen N)
renʷ σ [ g ]ʷ  = [ ren σ g ]ʷ
renʷ σ ε       = ε
renʷ σ (u • v) = renʷ σ u • renʷ σ v

renʷ-id : ∀ (w : Word (Gen N)) → renʷ (λ z → z) w ≡ w
renʷ-id [ −1[ a ] ]ʷ    = Eq.refl
renʷ-id [ X[ a , b ] ]ʷ = Eq.refl
renʷ-id [ H[ a , b ] ]ʷ = Eq.refl
renʷ-id ε               = Eq.refl
renʷ-id (u • v)         = Eq.cong₂ _•_ (renʷ-id u) (renʷ-id v)

renʷ-∘ : ∀ (σ ρ : Fin N → Fin N) (w : Word (Gen N)) →
         renʷ σ (renʷ ρ w) ≡ renʷ (λ z → σ (ρ z)) w
renʷ-∘ σ ρ [ −1[ a ] ]ʷ    = Eq.refl
renʷ-∘ σ ρ [ X[ a , b ] ]ʷ = Eq.refl
renʷ-∘ σ ρ [ H[ a , b ] ]ʷ = Eq.refl
renʷ-∘ σ ρ ε               = Eq.refl
renʷ-∘ σ ρ (u • v)         = Eq.cong₂ _•_ (renʷ-∘ σ ρ u) (renʷ-∘ σ ρ v)

-- An injective renaming keeps a word proper.
ren-proper : ∀ (σ : Fin N → Fin N) → (∀ {u v} → σ u ≡ σ v → u ≡ v) →
             ∀ (w : Word (Gen N)) → Proper w → Proper (renʷ σ w)
ren-proper σ inj [ −1[ a ] ]ʷ    −1ᵖ      = −1ᵖ
ren-proper σ inj [ X[ a , b ] ]ʷ (Xᵖ ab)  = Xᵖ (λ e → ab (inj e))
ren-proper σ inj [ H[ a , b ] ]ʷ (Hᵖ ab)  = Hᵖ (λ e → ab (inj e))
ren-proper σ inj ε               _        = _
ren-proper σ inj (u • v)         (p , q)  = ren-proper σ inj u p , ren-proper σ inj v q

------------------------------------------------------------------------
-- Conjugating by one exchange

private
  -- Rewriting the indices of a letter on the right of an equation.
  toZ : ∀ {w : Word (Gen N)} {p p′} → p ≡ p′ → w ≈ −1 p → w ≈ −1 p′
  toZ Eq.refl e = e

  toX : ∀ {w : Word (Gen N)} {p p′ q q′} → p ≡ p′ → q ≡ q′ → w ≈ X p q → w ≈ X p′ q′
  toX Eq.refl Eq.refl e = e

  toH : ∀ {w : Word (Gen N)} {p p′ q q′} → p ≡ p′ → q ≡ q′ → w ≈ H p q → w ≈ H p′ q′
  toH Eq.refl Eq.refl e = e

  sy′ : ∀ {a b : Fin N} → a ≢ b → b ≢ a
  sy′ ne e = ne (Eq.sym e)

  refl≡ : ∀ {u v : Word (Gen N)} → u ≡ v → u ≈ v
  refl≡ Eq.refl = refl

-- The case analysis takes the decisions as arguments, so that matching
-- them does not touch the τ in the goal.
private
  caseZ : ∀ {x y : Fin N} (xy : x ≢ y) (a : Fin N) → Dec (a ≡ x) → Dec (a ≡ y) →
          X x y • −1 a • X x y ≈ −1 (τ x y a)
  caseZ {x} {y} xy a (yes Eq.refl) _           = toZ (Eq.sym (τ-x x y)) (rZ-x xy)
  caseZ {x} {y} xy a (no ax)       (yes Eq.refl) = toZ (Eq.sym (τ-y x y xy)) (rZ-y xy)
  caseZ {x} {y} xy a (no ax)       (no ay)     = toZ (Eq.sym (τ-o x y a ax ay)) (rZ-o xy (sy′ ax) (sy′ ay))

  caseX : ∀ {x y : Fin N} (xy : x ≢ y) (a b : Fin N) → a ≢ b →
          Dec (a ≡ x) → Dec (a ≡ y) → Dec (b ≡ x) → Dec (b ≡ y) →
          X x y • X a b • X x y ≈ X (τ x y a) (τ x y b)
  caseX {x} {y} xy a b ab (yes Eq.refl) _ _ (yes Eq.refl) =
    toX (Eq.sym (τ-x x y)) (Eq.sym (τ-y x y xy)) (rX-xy xy)
  caseX {x} {y} xy a b ab (yes Eq.refl) _ (yes Eq.refl) _ = ⊥-elim (ab Eq.refl)
  caseX {x} {y} xy a b ab (yes Eq.refl) _ (no bx) (no by) =
    toX (Eq.sym (τ-x x y)) (Eq.sym (τ-o x y b bx by)) (rX-xo xy ab (sy′ by))
  caseX {x} {y} xy a b ab (no ax) (yes Eq.refl) (yes Eq.refl) _ =
    toX (Eq.sym (τ-y x y xy)) (Eq.sym (τ-x x y)) (rX-yx xy)
  caseX {x} {y} xy a b ab (no ax) (yes Eq.refl) (no bx) (yes Eq.refl) = ⊥-elim (ab Eq.refl)
  caseX {x} {y} xy a b ab (no ax) (yes Eq.refl) (no bx) (no by) =
    toX (Eq.sym (τ-y x y xy)) (Eq.sym (τ-o x y b bx by)) (rX-yo xy (sy′ bx) ab)
  caseX {x} {y} xy a b ab (no ax) (no ay) (yes Eq.refl) _ =
    toX (Eq.sym (τ-o x y a ax ay)) (Eq.sym (τ-x x y)) (rX-ox xy (sy′ ax) (sy′ ay))
  caseX {x} {y} xy a b ab (no ax) (no ay) (no bx) (yes Eq.refl) =
    toX (Eq.sym (τ-o x y a ax ay)) (Eq.sym (τ-y x y xy)) (rX-oy xy (sy′ ax) (sy′ ay))
  caseX {x} {y} xy a b ab (no ax) (no ay) (no bx) (no by) =
    toX (Eq.sym (τ-o x y a ax ay)) (Eq.sym (τ-o x y b bx by))
        (rX-oo xy (sy′ ax) (sy′ bx) (sy′ ay) (sy′ by) ab)

  caseH : ∀ {x y : Fin N} (xy : x ≢ y) (a b : Fin N) → a ≢ b →
          Dec (a ≡ x) → Dec (a ≡ y) → Dec (b ≡ x) → Dec (b ≡ y) →
          X x y • H a b • X x y ≈ H (τ x y a) (τ x y b)
  caseH {x} {y} xy a b ab (yes Eq.refl) _ _ (yes Eq.refl) =
    toH (Eq.sym (τ-x x y)) (Eq.sym (τ-y x y xy)) (rH-xy xy)
  caseH {x} {y} xy a b ab (yes Eq.refl) _ (yes Eq.refl) _ = ⊥-elim (ab Eq.refl)
  caseH {x} {y} xy a b ab (yes Eq.refl) _ (no bx) (no by) =
    toH (Eq.sym (τ-x x y)) (Eq.sym (τ-o x y b bx by)) (rH-xo xy ab (sy′ by))
  caseH {x} {y} xy a b ab (no ax) (yes Eq.refl) (yes Eq.refl) _ =
    toH (Eq.sym (τ-y x y xy)) (Eq.sym (τ-x x y)) (rH-yx xy)
  caseH {x} {y} xy a b ab (no ax) (yes Eq.refl) (no bx) (yes Eq.refl) = ⊥-elim (ab Eq.refl)
  caseH {x} {y} xy a b ab (no ax) (yes Eq.refl) (no bx) (no by) =
    toH (Eq.sym (τ-y x y xy)) (Eq.sym (τ-o x y b bx by)) (rH-yo xy (sy′ bx) ab)
  caseH {x} {y} xy a b ab (no ax) (no ay) (yes Eq.refl) _ =
    toH (Eq.sym (τ-o x y a ax ay)) (Eq.sym (τ-x x y)) (rH-ox xy (sy′ ax) (sy′ ay))
  caseH {x} {y} xy a b ab (no ax) (no ay) (no bx) (yes Eq.refl) =
    toH (Eq.sym (τ-o x y a ax ay)) (Eq.sym (τ-y x y xy)) (rH-oy xy (sy′ ax) (sy′ ay))
  caseH {x} {y} xy a b ab (no ax) (no ay) (no bx) (no by) =
    toH (Eq.sym (τ-o x y a ax ay)) (Eq.sym (τ-o x y b bx by))
        (rH-oo xy (sy′ ax) (sy′ bx) (sy′ ay) (sy′ by) ab)

conjG : ∀ {x y : Fin N} (xy : x ≢ y) (g : Gen N) → ProperG g →
        X x y • [ g ]ʷ • X x y ≈ [ ren (τ x y) g ]ʷ
conjG {x} {y} xy −1[ a ]    −1ᵖ     = caseZ xy a (a ≟ x) (a ≟ y)
conjG {x} {y} xy X[ a , b ] (Xᵖ ab) = caseX xy a b ab (a ≟ x) (a ≟ y) (b ≟ x) (b ≟ y)
conjG {x} {y} xy H[ a , b ] (Hᵖ ab) = caseH xy a b ab (a ≟ x) (a ≟ y) (b ≟ x) (b ≟ y)

conjʷ : ∀ {x y : Fin N} (xy : x ≢ y) (w : Word (Gen N)) → Proper w →
        X x y • w • X x y ≈ renʷ (τ x y) w
conjʷ xy [ g ]ʷ p = conjG xy g p
conjʷ xy ε _ = trans (back _ left-unit) (axiom (a2 xy))
conjʷ {x} {y} xy (u • v) (pu , pv) =
  trans (back (X x y) assoc)
  (trans (back (X x y) (back u (insertˡ (v • X x y) (axiom (a2 xy)))))
  (trans (back (X x y) (sym assoc))
  (trans (sym assoc)
         (cong (conjʷ xy u pu) (conjʷ xy v pv)))))

------------------------------------------------------------------------
-- Conjugating by a product of exchanges

record Tr : Set where
  constructor tr
  field
    fst snd : Fin N
    ne      : fst ≢ snd

-- The composite permutation, the word and its reverse.
σ : List Tr → Fin N → Fin N
σ []               z = z
σ (tr x y _ ∷ ts) z = τ x y (σ ts z)

Tw Tw⁻ : List Tr → Word (Gen N)
Tw []               = ε
Tw (tr x y _ ∷ ts) = X x y • Tw ts
Tw⁻ []               = ε
Tw⁻ (tr x y _ ∷ ts) = Tw⁻ ts • X x y

σ-inj : ∀ (ts : List Tr) {u v} → σ ts u ≡ σ ts v → u ≡ v
σ-inj []               e = e
σ-inj (tr x y xy ∷ ts) e = σ-inj ts (τ-inj x y xy e)

conj* : ∀ (ts : List Tr) (w : Word (Gen N)) → Proper w →
        Tw ts • w • Tw⁻ ts ≈ renʷ (σ ts) w
conj* [] w _ = trans left-unit (trans right-unit (refl≡ (Eq.sym (renʷ-id w))))
conj* (tr x y xy ∷ ts) w p =
  trans assoc
  (trans (back (X x y) (back (Tw ts) (sym assoc)))
  (trans (back (X x y) (sym assoc))
  (trans (back (X x y) (front (X x y) (conj* ts w p)))
  (trans (conjʷ xy (renʷ (σ ts) w) (ren-proper (σ ts) (σ-inj ts) w p))
         (refl≡ (renʷ-∘ (τ x y) (σ ts) w))))))

-- An equation between proper words holds renamed.
move : ∀ (ts : List Tr) {u v : Word (Gen N)} → Proper u → Proper v →
       u ≈ v → renʷ (σ ts) u ≈ renʷ (σ ts) v
move ts {u} {v} pu pv e =
  trans (sym (conj* ts u pu)) (trans (back (Tw ts) (front (Tw⁻ ts) e)) (conj* ts v pv))

------------------------------------------------------------------------
-- A product of exchanges for a given assignment

-- A member of an All, by position.
allAt : ∀ {k} {P : Fin N → Set} {v : Vec (Fin N) k} → All P v → ∀ j → P (lookup v j)
allAt (p ∷ _)  zero    = p
allAt (_ ∷ ps) (suc j) = allAt ps j

-- Distinct indices.
data Distinct : ∀ {k} → Vec (Fin N) k → Set where
  []ᵈ  : Distinct []
  _∷ᵈ_ : ∀ {k} {a : Fin N} {v : Vec (Fin N) k} → All (a ≢_) v → Distinct v → Distinct (a ∷ v)

lookup-inj : ∀ {k} {v : Vec (Fin N) k} → Distinct v → ∀ {i j} → lookup v i ≡ lookup v j → i ≡ j
lookup-inj (_ ∷ᵈ _)  {zero}  {zero}  _ = Eq.refl
lookup-inj (fa ∷ᵈ _) {zero}  {suc j} e = ⊥-elim (allAt fa j e)
lookup-inj (fa ∷ᵈ _) {suc i} {zero}  e = ⊥-elim (allAt fa i (Eq.sym e))
lookup-inj (_ ∷ᵈ d)  {suc i} {suc j} e = Eq.cong suc (lookup-inj d e)

-- Send l to i on top of ts, unless ts already does.
ext : (l i : Fin N) (ts : List Tr) → Dec (σ ts l ≡ i) → List Tr
ext l i ts (yes _) = ts
ext l i ts (no ne) = tr (σ ts l) i ne ∷ ts

ext-here : ∀ (l i : Fin N) (ts : List Tr) (d : Dec (σ ts l ≡ i)) → σ (ext l i ts d) l ≡ i
ext-here l i ts (yes e)  = e
ext-here l i ts (no ne)  = τ-x (σ ts l) i

ext-there : ∀ (l i : Fin N) (ts : List Tr) (d : Dec (σ ts l ≡ i)) (l′ i′ : Fin N) →
            σ ts l′ ≡ i′ → l ≢ l′ → i ≢ i′ → σ (ext l i ts d) l′ ≡ i′
ext-there l i ts (yes _) l′ i′ e _  _  = e
ext-there l i ts (no ne) l′ i′ e ll ii =
  Eq.trans (Eq.cong (τ (σ ts l) i) e)
           (τ-o (σ ts l) i i′ (λ h → ll (σ-inj ts (Eq.sym (Eq.trans e h)))) (λ h → ii (Eq.sym h)))

build : ∀ {k} → Vec (Fin N) k → Vec (Fin N) k → List Tr
build []       []       = []
build (l ∷ ls) (i ∷ is) = ext l i (build ls is) (σ (build ls is) l ≟ i)

build-ok : ∀ {k} (ls is : Vec (Fin N) k) → Distinct ls → Distinct is →
           ∀ j → σ (build ls is) (lookup ls j) ≡ lookup is j
build-ok (l ∷ ls) (i ∷ is) _ _ zero =
  ext-here l i (build ls is) (σ (build ls is) l ≟ i)
build-ok (l ∷ ls) (i ∷ is) (fl ∷ᵈ dl) (fi ∷ᵈ di) (suc j) =
  ext-there l i (build ls is) (σ (build ls is) l ≟ i) (lookup ls j) (lookup is j)
            (build-ok ls is dl di j) (allAt fl j) (allAt fi j)

------------------------------------------------------------------------
-- An exchange passing one letter, which it renames

passR : ∀ {x y : Fin N} (xy : x ≢ y) (g : Gen N) → ProperG g →
        X x y • [ g ]ʷ ≈ [ ren (τ x y) g ]ʷ • X x y
passR {x} {y} xy g p =
  trans (back (X x y) (insertʳ [ g ]ʷ (axiom (a2 xy))))
  (trans (sym assoc)
         (front (X x y) (conjG xy g p)))

passL : ∀ {x y : Fin N} (xy : x ≢ y) (g : Gen N) → ProperG g →
        [ g ]ʷ • X x y ≈ X x y • [ ren (τ x y) g ]ʷ
passL {x} {y} xy g p =
  trans (insertˡ ([ g ]ʷ • X x y) (axiom (a2 xy)))
        (back (X x y) (conjG xy g p))
