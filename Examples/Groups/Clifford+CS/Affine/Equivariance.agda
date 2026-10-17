------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical affine circuits, and how a letter passes them
--
-- For distinct basis states p, q of 1 + n wires the decoding conjugates
-- its gate by α p q = xs p • L (p ⊕ q): `L w` is a linear circuit
-- sending e₀ to w (the fan-out from wire 0 onto the support of w off
-- wire 0, after CX from the first wire of that support onto wire 0 when
-- w₀ = 0) and `xs p` the X on the bits of p.  The decoding is
-- equivariant because every letter a passes α: a • α p q ≈ α (â p) (â q)
-- • h, with â the letter's bit map and h a word of CX whose controls are
-- off wire 0 (`Ctl h`), which commute with the gate (`eqv-α`).  For the
-- translations this is commuting X's; for a CX it is the case analysis
-- of scratchpad/five/affine.py (`beta_claim`), here one lemma per case
-- (A: w₀ = 1, B: w₀ = 0; 1: control and target off wire 0, 2: control on
-- it, 3: target on it), each a few uses of the fan-out calculus.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Affine.Equivariance (n : ℕ) where

open import Data.Bool using (Bool ; true ; false ; not ; if_then_else_ ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Empty.Irrelevant as Irr
open import Data.Fin using (Fin) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Properties using (_≟_)
import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing)
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford+CS.Affine.Theory n

private
  variable
    k : ℕ

  t≢f : true ≢ false
  t≢f ()

  idᶠ : Fin n → Fin n
  idᶠ i = i

  inj-id : Injective idᶠ
  inj-id e = e

------------------------------------------------------------------------
-- Words of CX with their controls off wire 0

Ctl : Word Lt → Set
Ctl [ xL _ ]ʷ          = ⊥
Ctl [ tL 0F _ _ ]ʷ     = ⊥
Ctl [ tL (sF _) _ _ ]ʷ = ⊤
Ctl ε                  = ⊤
Ctl (a • b)            = Ctl a × Ctl b

Ctl-gan : ∀ (u : Fin n) (w : Vec Bool k) (ι : Fin k → Fin n) .h → Ctl (gan u w ι h)
Ctl-gan u []          ι h = tt
Ctl-gan u (true  ∷ w) ι h = tt , Ctl-gan u w (λ i → ι (sF i)) (λ i → h (sF i))
Ctl-gan u (false ∷ w) ι h = Ctl-gan u w (λ i → ι (sF i)) (λ i → h (sF i))

------------------------------------------------------------------------
-- The fan-out of the whole support

F : Vec Bool n → Word Lt
F w = fan w idᶠ

≡≈ : ∀ {a b : Word Lt} → a ≡ b → a ≈ b
≡≈ Eq.refl = refl

-- Off a cleared bit.
private
  off-cleared : ∀ (w : Vec Bool n) (a b : Fin n) → a ≢ b → lookup w a ≡ true →
                ∀ i → lookup (toggle (toggle w a) b) i ≡ true → idᶠ i ≢ a
  off-cleared w a b ab la i li Eq.refl =
    t≢f (Eq.trans (Eq.sym li)
          (Eq.trans (lookup-toggle′ (toggle w a) b a ab)
            (Eq.trans (lookup-toggle w a) (Eq.cong not la))))

  off-cleared′ : ∀ (w : Vec Bool n) (a b : Fin n) → a ≢ b → lookup w b ≡ true →
                 ∀ i → lookup (toggle (toggle w a) b) i ≡ true → idᶠ i ≢ b
  off-cleared′ w a b ab lb i li Eq.refl =
    t≢f (Eq.trans (Eq.sym li)
          (Eq.trans (lookup-toggle (toggle w a) b)
            (Eq.cong not (Eq.trans (lookup-toggle′ w a b (λ e → ab (Eq.sym e))) lb))))

-- The pivot change: two CX onto wire 0 from wires a, b of the fan.
piv : (w : Vec Bool n) (a b : Fin n) → .(a ≢ b) → .(lookup w a ≡ true) → .(lookup w b ≡ true) → Word Lt
piv w a b ab la lb =
  SW (sF a) (sF b) (s≢s ab) •
  T (sF a) 0F s≢0 • gan a (toggle (toggle w a) b) idᶠ (off-cleared w a b ab la) •
  T (sF b) 0F s≢0 • gan b (toggle (toggle w a) b) idᶠ (off-cleared′ w a b ab lb)

Ctl-piv : ∀ w a b .ab .la .lb → Ctl (piv w a b ab la lb)
Ctl-piv w a b ab la lb =
  (tt , tt , tt) , tt , Ctl-gan a (toggle (toggle w a) b) idᶠ (off-cleared w a b ab la) ,
  tt , Ctl-gan b (toggle (toggle w a) b) idᶠ (off-cleared′ w a b ab lb)

pivot : ∀ (w : Vec Bool n) (a b : Fin n) (ab : a ≢ b) (la : lookup w a ≡ true) (lb : lookup w b ≡ true) →
        T (sF b) 0F s≢0 • T (sF a) 0F s≢0 • F w ≈ F w • piv w a b ab la lb
pivot w a b ab la lb = begin
  Tb • Ta • F w
    ≈⟨ back _ (back _ (fan-pull₂ w idᶠ a b)) ⟩
  Tb • Ta • (T0 b • T0 a • F°)
    ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (comm00 b a)) assoc))) ⟩
  Tb • Ta • (T0 a • T0 b • F°)
    ≈⟨ by-passoc (□ • □ • (□ • □ • □)) ((□ • □ • □ • □) • □) Eq.refl ⟩
  (Tb • Ta • T0 a • T0 b) • F°
    ≈⟨ front _ (axiom (t-pv {e = s≢s ab})) ⟩
  (T0 a • T0 b • S • Ta • Tb) • F°
    ≈⟨ by-passoc ((□ • □ • □ • □ • □) • □) (□ • □ • □ • □ • (□ • □)) Eq.refl ⟩
  T0 a • T0 b • S • Ta • (Tb • F°)
    ≈⟨ back _ (back _ (back _ (back _ (fan-0 b s≢0 w° idᶠ hb)))) ⟩
  T0 a • T0 b • S • Ta • (F° • Tb • Gb)
    ≈⟨ back _ (back _ (back _ (trans (sym assoc) (front _ (fan-0 a s≢0 w° idᶠ ha))))) ⟩
  T0 a • T0 b • S • (F° • Ta • Ga) • Tb • Gb
    ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (trans (sym assoc) (front _ SF))) assoc))) ⟩
  T0 a • T0 b • (F° • S) • (Ta • Ga) • Tb • Gb
    ≈⟨ by-passoc (□ • □ • (□ • □) • (□ • □) • □ • □) ((□ • □ • □) • □ • □ • □ • □ • □) Eq.refl ⟩
  (T0 a • T0 b • F°) • S • Ta • Ga • Tb • Gb
    ≈⟨ front _ (trans (trans (sym assoc) (trans (front _ (comm00 a b)) assoc)) (sym (fan-pull₂ w idᶠ a b))) ⟩
  F w • S • Ta • Ga • Tb • Gb ∎
  where
  w° = toggle (toggle w a) b
  F° = F w°
  Ta = T (sF a) 0F s≢0
  Tb = T (sF b) 0F s≢0
  S = SW (sF a) (sF b) (s≢s ab)
  ha : ∀ i → lookup w° i ≡ true → idᶠ i ≢ a
  ha = off-cleared w a b ab la
  hb : ∀ i → lookup w° i ≡ true → idᶠ i ≢ b
  hb = off-cleared′ w a b ab lb
  Ga = gan a w° idᶠ ha
  Gb = gan b w° idᶠ hb
  ba : b ≢ a
  ba e = ab (Eq.sym e)
  -- The exchange of a and b passes the fan with both bits cleared.
  SF : S • F° ≈ F° • S
  Tab = T (sF a) (sF b) (s≢s ab)
  Tba = T (sF b) (sF a) (s≢s ba)
  SF = begin
    (Tab • Tba • Tab) • F°
      ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
    Tab • Tba • Tab • F°
      ≈⟨ back _ (back _ (fan-com a b (s≢s ab) w° idᶠ ha)) ⟩
    Tab • Tba • (F° • Tab)
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (fan-com b a (s≢s ba) w° idᶠ hb)) assoc)) ⟩
    Tab • F° • Tba • Tab
      ≈⟨ trans (sym assoc) (trans (front _ (fan-com a b (s≢s ab) w° idᶠ ha)) assoc) ⟩
    F° • Tab • Tba • Tab ∎

------------------------------------------------------------------------
-- The first bit set, and the canonical linear circuits

first : Vec Bool k → Maybe (Fin k)
first []          = nothing
first (true  ∷ w) = just 0F
first (false ∷ w) = Maybe.map sF (first w)

first-just : ∀ (w : Vec Bool k) {j} → first w ≡ just j → lookup w j ≡ true
first-just (true ∷ w) Eq.refl = Eq.refl
first-just (false ∷ w) {j} e with first w in e′
first-just (false ∷ w) {j} () | nothing
first-just (false ∷ w) {.(sF i)} Eq.refl | just i = first-just w e′

first-some : ∀ (w : Vec Bool k) (i : Fin k) → lookup w i ≡ true → Σ (Fin k) λ j → first w ≡ just j
first-some (true ∷ w)  i      b = 0F , Eq.refl
first-some (false ∷ w) 0F     ()
first-some (false ∷ w) (sF i) b with first-some w i b
... | j , e = sF j , Eq.cong (Maybe.map sF) e

L₀ : Maybe (Fin n) → Vec Bool n → Word Lt
L₀ nothing  w = ε
L₀ (just j) w = T (sF j) 0F s≢0 • F w

-- A linear circuit sending e₀ to w.
L : Vec Bool (₁₊ n) → Word Lt
L (true  ∷ w) = F w
L (false ∷ w) = L₀ (first w) w

L-false : ∀ (w : Vec Bool n) {j} → first w ≡ just j → L (false ∷ w) ≡ T (sF j) 0F s≢0 • F w
L-false w e = Eq.cong (λ m → L₀ m w) e

------------------------------------------------------------------------
-- A CX passing L

-- The bit map of CX from u onto v.
tmap : (u v : Wire) → Vec Bool (₁₊ n) → Vec Bool (₁₊ n)
tmap u v w = if lookup w u then toggle w v else w

record Pass (a : Word Lt) (w w′ : Vec Bool (₁₊ n)) : Set where
  constructor pass
  field
    h   : Word Lt
    ctl : Ctl h
    eq  : a • L w ≈ L w′ • h

private
  -- Two CX onto wire 0 commute.
  tt00 : ∀ (a b : Fin n) → T (sF a) 0F s≢0 • T (sF b) 0F s≢0 ≈ T (sF b) 0F s≢0 • T (sF a) 0F s≢0
  tt00 a b with a ≟ b
  ... | yes Eq.refl = refl
  ... | no ab       = axiom (t-tt (s≢s ab))

  -- CX between wires off 0, against CX onto 0 from a third wire or the control.
  c-j0 : ∀ (u v j : Fin n) .(p : _≢_ {A = Wire} (sF u) (sF v)) → v ≢ j →
         T (sF u) (sF v) p • T (sF j) 0F s≢0 ≈ T (sF j) 0F s≢0 • T (sF u) (sF v) p
  c-j0 u v j p vj with u ≟ j
  ... | yes Eq.refl = axiom (t-cc (λ ()))
  ... | no uj       = axiom (t-dd (s≢s uj) s≢0 (s≢s vj) s≢0)

  -- Moving a CX onto wire 0 out of the way of another.
  swap0 : ∀ (a b : Fin n) (w : Vec Bool n) → T (sF a) 0F s≢0 • F w ≈ T (sF b) 0F s≢0 • (T (sF b) 0F s≢0 • T (sF a) 0F s≢0 • F w)
  swap0 a b w = sym (cancelˡ _ (axiom t-sq))

-- (A1) w₀ = 1, control and target off wire 0.
A1 : ∀ (u v : Fin n) .(p : _≢_ {A = Wire} (sF u) (sF v)) (w : Vec Bool n) (b : Bool) → lookup w u ≡ b →
     Pass (T (sF u) (sF v) p) (true ∷ w) (if b then true ∷ toggle w v else true ∷ w)
A1 u v p w false e = pass (T (sF u) (sF v) p) tt (fan-com u v p w idᶠ off)
  where
  off : ∀ i → lookup w i ≡ true → idᶠ i ≢ u
  off i b Eq.refl = t≢f (Eq.trans (Eq.sym b) e)
A1 u v p w true e = pass (T (sF u) (sF v) p) tt (begin
  T (sF u) (sF v) p • F w            ≈⟨ fan-in w idᶠ inj-id u e v p ⟩
  F w • T0 v • T (sF u) (sF v) p     ≈⟨ trans (sym assoc) (front _ (sym (fan-toggle w idᶠ v))) ⟩
  F (toggle w v) • T (sF u) (sF v) p ∎)

-- (A2) w₀ = 1, control on wire 0.
A2 : ∀ (v : Fin n) .(p : _≢_ {A = Wire} 0F (sF v)) (w : Vec Bool n) →
     Pass (T 0F (sF v) p) (true ∷ w) (true ∷ toggle w v)
A2 v p w = pass ε tt (begin
  T0 v • F w             ≈⟨ pass0 v w idᶠ ⟩
  F w • T0 v             ≈⟨ sym (fan-toggle w idᶠ v) ⟩
  F (toggle w v)         ≈⟨ sym right-unit ⟩
  F (toggle w v) • ε ∎)

-- (A3) w₀ = 1, target on wire 0.
A3 : ∀ (u : Fin n) .(p : _≢_ {A = Wire} (sF u) 0F) (w : Vec Bool n) (b : Bool) → lookup w u ≡ b →
     Pass (T (sF u) 0F p) (true ∷ w) (if b then false ∷ w else true ∷ w)
A3 u p w false e = pass (T (sF u) 0F p • gan u w idᶠ off) (tt , Ctl-gan u w idᶠ off) (fan-0 u p w idᶠ off)
  where
  off : ∀ i → lookup w i ≡ true → idᶠ i ≢ u
  off i b Eq.refl = t≢f (Eq.trans (Eq.sym b) e)
A3 u p w true e with first-some w u e
... | j , fj with j ≟ u
... | yes Eq.refl = pass ε tt (trans (≡≈ (Eq.sym (L-false w fj))) (sym right-unit))
... | no ju = pass (piv w u j uj e lj) (Ctl-piv w u j uj e lj) (begin
    T (sF u) 0F s≢0 • F w
      ≈⟨ swap0 u j w ⟩
    T (sF j) 0F s≢0 • (T (sF j) 0F s≢0 • T (sF u) 0F s≢0 • F w)
      ≈⟨ back _ (pivot w u j uj e lj) ⟩
    T (sF j) 0F s≢0 • (F w • piv w u j uj e lj)
      ≈⟨ trans (sym assoc) (front _ (≡≈ (Eq.sym (L-false w fj)))) ⟩
    L (false ∷ w) • piv w u j uj e lj ∎)
  where
  uj : u ≢ j
  uj e′ = ju (Eq.sym e′)
  lj : lookup w j ≡ true
  lj = first-just w fj

-- (B) w₀ = 0: L w is CX(j → 0) after the fan, j the first bit of the support.
module B (w : Vec Bool n) (j : Fin n) (fj : first w ≡ just j) where

  private
    lj : lookup w j ≡ true
    lj = first-just w fj

    Tj = T (sF j) 0F s≢0

    Lw : L (false ∷ w) ≈ Tj • F w
    Lw = ≡≈ (L-false w fj)

    -- From the canonical form with some pivot to L of a vector with w₀ = 0.
    settle : ∀ (w′ : Vec Bool n) (a : Fin n) → lookup w′ a ≡ true → (h : Word Lt) → Ctl h →
             ∀ {x} → x ≈ T (sF a) 0F s≢0 • F w′ • h → Σ (Word Lt) λ h′ → Ctl h′ × (x ≈ L (false ∷ w′) • h′)
    settle w′ a la h ch {x} e with first-some w′ a la
    ... | j′ , fj′ with j′ ≟ a
    ... | yes Eq.refl = h , ch , trans e (trans (sym assoc) (front _ (≡≈ (Eq.sym (L-false w′ fj′)))))
    ... | no ja = piv w′ a j′ aj la lj′ • h , (Ctl-piv w′ a j′ aj la lj′ , ch) , (begin
        x
          ≈⟨ e ⟩
        T (sF a) 0F s≢0 • F w′ • h
          ≈⟨ sym assoc ⟩
        (T (sF a) 0F s≢0 • F w′) • h
          ≈⟨ front _ (swap0 a j′ w′) ⟩
        (T (sF j′) 0F s≢0 • (T (sF j′) 0F s≢0 • T (sF a) 0F s≢0 • F w′)) • h
          ≈⟨ front _ (back _ (pivot w′ a j′ aj la lj′)) ⟩
        (T (sF j′) 0F s≢0 • (F w′ • piv w′ a j′ aj la lj′)) • h
          ≈⟨ trans (front _ (sym assoc)) assoc ⟩
        (T (sF j′) 0F s≢0 • F w′) • piv w′ a j′ aj la lj′ • h
          ≈⟨ front _ (≡≈ (Eq.sym (L-false w′ fj′))) ⟩
        L (false ∷ w′) • piv w′ a j′ aj la lj′ • h ∎)
      where
      aj : a ≢ j′
      aj e′ = ja (Eq.sym e′)
      lj′ : lookup w′ j′ ≡ true
      lj′ = first-just w′ fj′

    toPass : ∀ {a w′} → (Σ (Word Lt) λ h → Ctl h × (a • L (false ∷ w) ≈ L w′ • h)) → Pass a (false ∷ w) w′
    toPass (h , c , e) = pass h c e

  -- (B1) control and target off wire 0.
  B1 : ∀ (u v : Fin n) .(p : _≢_ {A = Wire} (sF u) (sF v)) (b : Bool) → lookup w u ≡ b →
       Pass (T (sF u) (sF v) p) (false ∷ w) (if b then false ∷ toggle w v else false ∷ w)
  B1 u v p false e with v ≟ j
  ... | no vj = pass Tuv tt (begin
      Tuv • L (false ∷ w)   ≈⟨ back _ Lw ⟩
      Tuv • Tj • F w        ≈⟨ trans (sym assoc) (trans (front _ (c-j0 u v j p vj)) assoc) ⟩
      Tj • Tuv • F w        ≈⟨ back _ (fan-com u v p w idᶠ off) ⟩
      Tj • F w • Tuv        ≈⟨ trans (sym assoc) (front _ (sym Lw)) ⟩
      L (false ∷ w) • Tuv ∎)
    where
    off : ∀ i → lookup w i ≡ true → idᶠ i ≢ u
    off i b Eq.refl = t≢f (Eq.trans (Eq.sym b) e)
    Tuv = T (sF u) (sF v) p
  ... | yes Eq.refl = pass (Tuv • T (sF u) 0F s≢0 • gan u w idᶠ off) (tt , tt , Ctl-gan u w idᶠ off) (begin
      Tuv • L (false ∷ w)
        ≈⟨ back _ Lw ⟩
      Tuv • Tj • F w
        ≈⟨ trans (sym assoc) (front _ (moveˡ (axiom t-sq) (axiom t-st))) ⟩
      (Tj • Tuv • T (sF u) 0F s≢0) • F w
        ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
      Tj • Tuv • (T (sF u) 0F s≢0 • F w)
        ≈⟨ back _ (back _ (fan-0 u s≢0 w idᶠ off)) ⟩
      Tj • Tuv • (F w • T (sF u) 0F s≢0 • gan u w idᶠ off)
        ≈⟨ back _ (trans (sym assoc) (front _ (fan-com u v p w idᶠ off))) ⟩
      Tj • (F w • Tuv) • T (sF u) 0F s≢0 • gan u w idᶠ off
        ≈⟨ by-passoc (□ • (□ • □) • □ • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
      (Tj • F w) • Tuv • T (sF u) 0F s≢0 • gan u w idᶠ off
        ≈⟨ front _ (sym Lw) ⟩
      L (false ∷ w) • Tuv • T (sF u) 0F s≢0 • gan u w idᶠ off ∎)
    where
    off : ∀ i → lookup w i ≡ true → idᶠ i ≢ u
    off i b Eq.refl = t≢f (Eq.trans (Eq.sym b) e)
    Tuv = T (sF u) (sF j) p
  B1 u v p true e with v ≟ j
  ... | no vj = toPass (settle (toggle w v) j lj′ Tuv tt (begin
      Tuv • L (false ∷ w)
        ≈⟨ back _ Lw ⟩
      Tuv • Tj • F w
        ≈⟨ trans (sym assoc) (trans (front _ (c-j0 u v j p vj)) assoc) ⟩
      Tj • Tuv • F w
        ≈⟨ back _ (fan-in w idᶠ inj-id u e v p) ⟩
      Tj • F w • T0 v • Tuv
        ≈⟨ back _ (trans (sym assoc) (front _ (sym (fan-toggle w idᶠ v)))) ⟩
      Tj • F (toggle w v) • Tuv ∎))
      where
      Tuv = T (sF u) (sF v) p
      lj′ : lookup (toggle w v) j ≡ true
      lj′ = Eq.trans (lookup-toggle′ w v j (λ e′ → vj (Eq.sym e′))) lj
  ... | yes Eq.refl = toPass (settle (toggle w j) u lu′ h′ (tt , Ctl-gan j (toggle w j) idᶠ offj , tt) (begin
      Tuv • L (false ∷ w)
        ≈⟨ back _ Lw ⟩
      Tuv • Tj • F w
        ≈⟨ trans (sym assoc) (front _ (moveʳ (axiom t-sq) (trans assoc (axiom t-ts)))) ⟩
      ((Tj • Tu0) • Tuv) • F w
        ≈⟨ trans assoc (trans assoc (back _ (back _ (fan-in w idᶠ inj-id u e j p)))) ⟩
      Tj • Tu0 • (F w • T0 j • Tuv)
        ≈⟨ back _ (back _ (trans (sym assoc) (front _ (sym (fan-toggle w idᶠ j))))) ⟩
      Tj • Tu0 • (F (toggle w j) • Tuv)
        ≈⟨ trans (sym assoc) (trans (front _ (tt00 j u)) assoc) ⟩
      Tu0 • Tj • (F (toggle w j) • Tuv)
        ≈⟨ back _ (trans (sym assoc) (front _ (fan-0 j s≢0 (toggle w j) idᶠ offj))) ⟩
      Tu0 • (F (toggle w j) • Tj • gan j (toggle w j) idᶠ offj) • Tuv
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) (□ • □ • (□ • □ • □)) Eq.refl ⟩
      Tu0 • F (toggle w j) • h′ ∎))
      where
      Tuv = T (sF u) (sF j) p
      Tu0 = T (sF u) 0F s≢0
      uj : u ≢ j
      uj e′ = Irr.⊥-elim (p (Eq.cong sF e′))
      offj : ∀ i → lookup (toggle w j) i ≡ true → idᶠ i ≢ j
      offj i li Eq.refl = t≢f (Eq.trans (Eq.sym li) (Eq.trans (lookup-toggle w j) (Eq.cong not lj)))
      lu′ : lookup (toggle w j) u ≡ true
      lu′ = Eq.trans (lookup-toggle′ w j u uj) e
      h′ : Word Lt
      h′ = Tj • gan j (toggle w j) idᶠ offj • Tuv

  -- (B2) control on wire 0.
  B2 : ∀ (v : Fin n) .(p : _≢_ {A = Wire} 0F (sF v)) → Pass (T 0F (sF v) p) (false ∷ w) (false ∷ w)
  B2 v p with v ≟ j
  ... | no vj = pass (T (sF j) (sF v) (s≢s jv)) tt (begin
      T0 v • L (false ∷ w)
        ≈⟨ back _ Lw ⟩
      T0 v • Tj • F w
        ≈⟨ trans (sym assoc) (front _ (moveʳ (axiom t-sq) (trans assoc (axiom t-st)))) ⟩
      ((Tj • Tjv) • T0 v) • F w
        ≈⟨ trans assoc (trans assoc (back _ (back _ (pass0 v w idᶠ)))) ⟩
      Tj • Tjv • (F w • T0 v)
        ≈⟨ back _ (trans (sym assoc) (front _ (fan-in w idᶠ inj-id j lj v (s≢s jv)))) ⟩
      Tj • (F w • T0 v • Tjv) • T0 v
        ≈⟨ back _ (trans assoc (back _ (trans assoc (back _ (axiom (t-tt s≢0)))))) ⟩
      Tj • F w • T0 v • (T0 v • Tjv)
        ≈⟨ back _ (back _ (cancelˡ _ (axiom t-sq))) ⟩
      Tj • F w • Tjv
        ≈⟨ trans (sym assoc) (front _ (sym Lw)) ⟩
      L (false ∷ w) • Tjv ∎)
      where
      jv : j ≢ v
      jv e′ = vj (Eq.sym e′)
      Tjv = T (sF j) (sF v) (s≢s jv)
  ... | yes Eq.refl = pass (Tj • gan j w° idᶠ off) (tt , Ctl-gan j w° idᶠ off) (begin
      T0 j • L (false ∷ w)
        ≈⟨ back _ Lw ⟩
      T0 j • Tj • F w
        ≈⟨ back _ (back _ pullj) ⟩
      T0 j • Tj • (T0 j • F w°)
        ≈⟨ trans (back _ (sym assoc)) (sym assoc) ⟩
      (T0 j • Tj • T0 j) • F w°
        ≈⟨ front _ (axiom t-sw) ⟩
      (Tj • T0 j • Tj) • F w°
        ≈⟨ trans assoc (back _ (trans assoc (back _ (fan-0 j s≢0 w° idᶠ off)))) ⟩
      Tj • T0 j • (F w° • Tj • gan j w° idᶠ off)
        ≈⟨ back _ (trans (sym assoc) (front _ (sym pullj))) ⟩
      Tj • F w • Tj • gan j w° idᶠ off
        ≈⟨ trans (sym assoc) (front _ (sym Lw)) ⟩
      L (false ∷ w) • Tj • gan j w° idᶠ off ∎)
      where
      w° = toggle w j
      off : ∀ i → lookup w° i ≡ true → idᶠ i ≢ j
      off i li Eq.refl = t≢f (Eq.trans (Eq.sym li) (Eq.trans (lookup-toggle w j) (Eq.cong not lj)))
      pullj : F w ≈ T0 j • F w°
      pullj = begin
        F w                          ≈⟨ sym right-unit ⟩
        F w • ε                      ≈⟨ back _ (sym (axiom t-sq)) ⟩
        F w • (T0 j • T0 j)          ≈⟨ sym assoc ⟩
        (F w • T0 j) • T0 j          ≈⟨ front _ (sym (fan-toggle w idᶠ j)) ⟩
        F w° • T0 j                  ≈⟨ sym (pass0 j w° idᶠ) ⟩
        T0 j • F w° ∎

  -- (B3) target on wire 0.
  B3 : ∀ (u : Fin n) .(p : _≢_ {A = Wire} (sF u) 0F) (b : Bool) → lookup w u ≡ b →
       Pass (T (sF u) 0F p) (false ∷ w) (if b then true ∷ w else false ∷ w)
  B3 u p false e = pass (Tu0 • gan u w idᶠ off) (tt , Ctl-gan u w idᶠ off) (begin
    Tu0 • L (false ∷ w)
      ≈⟨ back _ Lw ⟩
    Tu0 • Tj • F w
      ≈⟨ trans (sym assoc) (trans (front _ (tt00 u j)) assoc) ⟩
    Tj • Tu0 • F w
      ≈⟨ back _ (fan-0 u s≢0 w idᶠ off) ⟩
    Tj • F w • Tu0 • gan u w idᶠ off
      ≈⟨ trans (sym assoc) (front _ (sym Lw)) ⟩
    L (false ∷ w) • Tu0 • gan u w idᶠ off ∎)
    where
    Tu0 = T (sF u) 0F s≢0
    off : ∀ i → lookup w i ≡ true → idᶠ i ≢ u
    off i b Eq.refl = t≢f (Eq.trans (Eq.sym b) e)
  B3 u p true e with u ≟ j
  ... | yes Eq.refl = pass ε tt (begin
      Tu0 • L (false ∷ w)   ≈⟨ back _ Lw ⟩
      Tu0 • Tu0 • F w       ≈⟨ cancelˡ _ (axiom t-sq) ⟩
      F w                   ≈⟨ sym right-unit ⟩
      F w • ε ∎)
    where Tu0 = T (sF u) 0F s≢0
  ... | no uj = pass (piv w u j uj e lj) (Ctl-piv w u j uj e lj) (begin
      Tu0 • L (false ∷ w)   ≈⟨ back _ Lw ⟩
      Tu0 • Tj • F w        ≈⟨ trans (sym assoc) (trans (front _ (tt00 u j)) assoc) ⟩
      Tj • Tu0 • F w        ≈⟨ pivot w u j uj e lj ⟩
      F w • piv w u j uj e lj ∎)
    where Tu0 = T (sF u) 0F s≢0

------------------------------------------------------------------------
-- Every CX passes L

NZ : Vec Bool k → Set
NZ w = Σ _ λ i → lookup w i ≡ true

private
  nz-tail : ∀ (w : Vec Bool n) → NZ (false ∷ w) → Σ (Fin n) λ j → first w ≡ just j
  nz-tail w (0F , ())
  nz-tail w (sF i , b) = first-some w i b

eqvL : ∀ (u v : Wire) .(p : u ≢ v) (w : Vec Bool (₁₊ n)) → NZ w → Pass (T u v p) w (tmap u v w)
eqvL 0F      0F      p w           nz = Irr.⊥-elim (p Eq.refl)
eqvL 0F      (sF v)  p (true  ∷ w) nz = A2 v p w
eqvL 0F      (sF v)  p (false ∷ w) nz with nz-tail w nz
... | j , fj = B.B2 w j fj v p
eqvL (sF u)  0F      p (true  ∷ w) nz = A3 u p w (lookup w u) Eq.refl
eqvL (sF u)  0F      p (false ∷ w) nz with nz-tail w nz
... | j , fj = B.B3 w j fj u p (lookup w u) Eq.refl
eqvL (sF u)  (sF v)  p (true  ∷ w) nz = A1 u v p w (lookup w u) Eq.refl
eqvL (sF u)  (sF v)  p (false ∷ w) nz with nz-tail w nz
... | j , fj = B.B1 w j fj u v p (lookup w u) Eq.refl
