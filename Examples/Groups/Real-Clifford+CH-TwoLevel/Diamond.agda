------------------------------------------------------------------------
-- Presentations of groups
--
-- The four-entry diamond: the edges H on all valid pairs among four
-- odd entries a < b < c < d of one residue class, given the edge H on
-- the canonical pair (a, b).
--
-- With the numerator entries A, A + 2z_b, A + 2z_c, A + 2z_d and
-- S = z_b + z_c + z_d, each pairing Π_A = {ab, cd}, Π_B = {ac, bd},
-- Π_C = {ad, bc} makes the four entries even, and two pairings in a
-- row give four entries of one parity, that of S or of A + S:
--
-- * S even: Π_B Π_A is even, and (f1) Π_A Π_B = Π_B Π_A closes a
--   square below the level from Π_A to Π_B;
-- * S odd: Π_C Π_B is even, and (f2) Π_B Π_C = X_[a,b] X_[c,d] Π_C Π_B
--   closes one from Π_B to Π_C.
--
-- The other pairing comes from the state Z_[d]·s, where the parity of
-- S flips (the Z_[d] edges commute with H_[a,c] and H_[b,c]).  The
-- column computations are on the four entries only (Local), at the
-- scale of s; the ring identities of the steps were generated.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Product.Base using (_,_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction using (EdgesBelow)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Diamond {n : ℕ} (p : Fin n) (k′ ℓ : ℕ)
  (ih : EdgesBelow {n} (suc (toℕ p) , suc k′ , ℓ)) where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (_<_ ; _≤_)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (∃ ; _×_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec ; _∷_ ; [])
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Notations using (₀ ; ₁ ; ₂ ; ₃)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (D ; Z ; module ZR ; module ZG ; √2ᶻ ; oddᶻ ; rbit ; oddᶻ-+ ; oddᶻ-neg ; oddᶻ-* ; rbit-+ ; rbit-neg)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm using (2ᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (scV ; num ; Odd ; Even)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Zᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (Beyond ; level ; _<ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable using (Beyond-actM)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Levels using (odd-Z ; lde-Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step using (same-class)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (Z-Z ; comm-gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (Path ; Low ; path-• ; path-below ; act-gg)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PathTools {n} using (path-cong ; peel ; module Below)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PairBase p k′ ℓ ih
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Local {n} using (upd₂ ; module Emb)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Pairings {n} as Pairings

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid
open Below {L = L} ih using (bridge)
open ZG using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

------------------------------------------------------------------------
-- Parities

private
  xor-false : ∀ b → b xor false ≡ b
  xor-false true = ≡.refl
  xor-false false = ≡.refl

  xor-self : ∀ b → b xor b ≡ false
  xor-self true = ≡.refl
  xor-self false = ≡.refl

  xor-true : ∀ b → b xor true ≡ not b
  xor-true true = ≡.refl
  xor-true false = ≡.refl

  2z≡ : ∀ z → 2ᶻ ZR.* z ≡ z ZR.+ z
  2z≡ z = ZG.solve 1 (λ z → con 2ᶻ :* z := z :+ z) ≡.refl z

  odd-2 : ∀ z → oddᶻ (2ᶻ ZR.* z) ≡ false
  odd-2 z = ≡.trans (≡.cong oddᶻ (2z≡ z)) (≡.trans (oddᶻ-+ z z) (xor-self (oddᶻ z)))

  rbit-2 : ∀ z → rbit (2ᶻ ZR.* z) ≡ false
  rbit-2 z = ≡.trans (≡.cong rbit (2z≡ z)) (≡.trans (rbit-+ z z) (xor-self (rbit z)))

  -- x = y + 2z: the same parity and residue.
  par : ∀ {x y} z → x ≡ y ZR.+ 2ᶻ ZR.* z → oddᶻ x ≡ oddᶻ y
  par {x} {y} z e =
    ≡.trans (≡.cong oddᶻ e) (≡.trans (oddᶻ-+ y (2ᶻ ZR.* z)) (≡.trans (≡.cong (oddᶻ y xor_) (odd-2 z)) (xor-false (oddᶻ y))))

  rpar : ∀ {x y} z → x ≡ y ZR.+ 2ᶻ ZR.* z → rbit x ≡ rbit y
  rpar {x} {y} z e =
    ≡.trans (≡.cong rbit e) (≡.trans (rbit-+ y (2ᶻ ZR.* z)) (≡.trans (≡.cong (rbit y xor_) (rbit-2 z)) (xor-false (rbit y))))

  even-r : ∀ x → Even (√2ᶻ ZR.* x)
  even-r x = oddᶻ-* √2ᶻ x

  even-nr : ∀ x → Even (ZR.- (√2ᶻ ZR.* x))
  even-nr x = ≡.trans (oddᶻ-neg (√2ᶻ ZR.* x)) (even-r x)

  -- Z_[d] keeps the residue of every entry.
  rbit-Z : (d : Fin n) (w : Vec Z n) (x : Fin n) → rbit (Zᶻ d w ! x) ≡ rbit (w ! x)
  rbit-Z d w x = at (x FinP.≟ d)
    where
    at : Dec (x ≡ d) → rbit (Zᶻ d w ! x) ≡ rbit (w ! x)
    at (yes ≡.refl) = ≡.trans (≡.cong rbit (set₁-a x (ZR.- (w ! x)) w)) (rbit-neg (w ! x))
    at (no x≢d) = ≡.cong rbit (set₁-≢ d (ZR.- (w ! d)) w x≢d)

-- A path at equal matrices.
path-≡ : ∀ {w : Word (Gen n)} {N N′ : Matrix n n D} .{oN : ColOrth N} .{oN′ : ColOrth N′} →
         N ≡ N′ → Path w N oN → Path w N′ oN′
path-≡ ≡.refl x = x

------------------------------------------------------------------------
-- Four sorted indices

module Four {a b c d : Fin n} (ab : a < b) (bc : b < c) (cd : c < d) (d≤p : d ≤ p) where

  open Pairings.Sorted ab bc cd public

  private
    sym≢ : ∀ {x y : Fin n} → x ≢ y → y ≢ x
    sym≢ ne e = ne (≡.sym e)
  a≢b = <⇒≢ ab
  a≢c = <⇒≢ ac
  a≢d = <⇒≢ ad
  b≢c = <⇒≢ bc
  b≢d = <⇒≢ bd
  c≢d = <⇒≢ cd
  b≢a = sym≢ a≢b
  c≢a = sym≢ a≢c
  d≢a = sym≢ a≢d
  c≢b = sym≢ b≢c
  d≢b = sym≢ b≢d
  d≢c = sym≢ c≢d

  c≤p : c ≤ p
  c≤p = ℕP.<⇒≤ (ℕP.<-≤-trans cd d≤p)

  b≤p : b ≤ p
  b≤p = ℕP.<⇒≤ (ℕP.<-≤-trans bd d≤p)

  ι : Fin 4 → Fin n
  ι ₀ = a
  ι ₁ = b
  ι ₂ = c
  ι ₃ = d

  ι-inj : ∀ {i j} → ι i ≡ ι j → i ≡ j
  ι-inj {₀} {₀} _ = ≡.refl
  ι-inj {₀} {₁} e = ⊥-elim (a≢b e)
  ι-inj {₀} {₂} e = ⊥-elim (a≢c e)
  ι-inj {₀} {₃} e = ⊥-elim (a≢d e)
  ι-inj {₁} {₀} e = ⊥-elim (b≢a e)
  ι-inj {₁} {₁} _ = ≡.refl
  ι-inj {₁} {₂} e = ⊥-elim (b≢c e)
  ι-inj {₁} {₃} e = ⊥-elim (b≢d e)
  ι-inj {₂} {₀} e = ⊥-elim (c≢a e)
  ι-inj {₂} {₁} e = ⊥-elim (c≢b e)
  ι-inj {₂} {₂} _ = ≡.refl
  ι-inj {₂} {₃} e = ⊥-elim (c≢d e)
  ι-inj {₃} {₀} e = ⊥-elim (d≢a e)
  ι-inj {₃} {₁} e = ⊥-elim (d≢b e)
  ι-inj {₃} {₂} e = ⊥-elim (d≢c e)
  ι-inj {₃} {₃} _ = ≡.refl

  ι≤p : ∀ m → ι m ≤ p
  ι≤p ₀ = ℕP.<⇒≤ (ℕP.<-≤-trans ad d≤p)
  ι≤p ₁ = b≤p
  ι≤p ₂ = c≤p
  ι≤p ₃ = d≤p

  open Emb ι ι-inj using (emb ; emb-self ; emb-ext ; loc ; H-emb ; nodd-emb)

  -- A state whose column p is known: the embedding of e at scale k.
  record Known (Wn : Vec Z n) (N′ : Matrix n n D) (e : Vec Z 4) : Set where
    constructor known
    field
      colK : col N′ p ≡ scV k (emb e Wn)
      beK  : Beyond p N′

  stepH : ∀ {Wn N′ e} (i j : Fin 4) .(ij : ι i < ι j) (α β : Z) →
          e ! i ZR.+ e ! j ≡ √2ᶻ ZR.* α → e ! i ZR.- e ! j ≡ √2ᶻ ZR.* β →
          Known Wn N′ e → Known Wn (actM (H-gen (ι i) (ι j) ij) N′) (upd₂ i j α β e)
  stepH {Wn} {N′} {e} i j ij α β sm df (known cK bK) =
    known (≡.trans (col-actM (H-gen (ι i) (ι j) ij) N′ p)
            (≡.trans (≡.cong (actV (H-gen (ι i) (ι j) ij)) cK) (H-emb i j ij k e Wn α β sm df)))
          (Beyond-actM (H-gen (ι i) (ι j) ij) {p} {N′} (ι≤p j) bK)

  lowK : ∀ {Wn N′ e} → (∀ m → Odd (Wn ! ι m)) → nodd Wn ≡ ℓ → Known Wn N′ e →
         (m : Fin 4) → Even (e ! m) → level N′ <ₗ L
  lowK {Wn} {N′} {e} odd4 ℓe (known cK bK) m ev =
    low N′ bK (emb e Wn) cK (≡.subst (nodd (emb e Wn) ℕ.<_) ℓe (nodd-emb e Wn odd4 m ev))

  ----------------------------------------------------------------------
  -- The routes from a state with entries A, A + 2z_b, A + 2z_c, A + 2z_d

  module Route (N : Matrix n n D) .(oN : ColOrth N) (eqN : level N ≡ L)
               (A zb zc zd : Z) (oA : Odd A)
               (wa : State.W N oN eqN ! a ≡ A)
               (wb : State.W N oN eqN ! b ≡ A ZR.+ 2ᶻ ZR.* zb)
               (wc : State.W N oN eqN ! c ≡ A ZR.+ 2ᶻ ZR.* zc)
               (wd : State.W N oN eqN ! d ≡ A ZR.+ 2ᶻ ZR.* zd)
               (pAB : Path Hab N oN) where

    open State N oN eqN using (W ; colM ; be ; ℓM ; below ; below₂ ; square)

    S : Z
    S = zb ZR.+ zc ZR.+ zd

    e₀ : Vec Z 4
    e₀ = A ∷ (A ZR.+ (2ᶻ ZR.* zb)) ∷ (A ZR.+ (2ᶻ ZR.* zc)) ∷ (A ZR.+ (2ᶻ ZR.* zd)) ∷ []

    e₁ : Vec Z 4
    e₁ = A ∷ (A ZR.+ (2ᶻ ZR.* zb)) ∷ (√2ᶻ ZR.* ((A ZR.+ zc) ZR.+ zd)) ∷ (√2ᶻ ZR.* (zc ZR.- zd)) ∷ []

    eA : Vec Z 4
    eA = (√2ᶻ ZR.* (A ZR.+ zb)) ∷ (ZR.- (√2ᶻ ZR.* zb)) ∷ (√2ᶻ ZR.* ((A ZR.+ zc) ZR.+ zd)) ∷ (√2ᶻ ZR.* (zc ZR.- zd)) ∷ []

    e₂ : Vec Z 4
    e₂ = (√2ᶻ ZR.* (A ZR.+ zb)) ∷ ((zc ZR.- zd) ZR.- zb) ∷ (√2ᶻ ZR.* ((A ZR.+ zc) ZR.+ zd)) ∷ ((ZR.- zb) ZR.- (zc ZR.- zd)) ∷ []

    eBA : Vec Z 4
    eBA = ((A ZR.+ zb) ZR.+ ((A ZR.+ zc) ZR.+ zd)) ∷ ((zc ZR.- zd) ZR.- zb) ∷ ((A ZR.+ zb) ZR.- ((A ZR.+ zc) ZR.+ zd)) ∷ ((ZR.- zb) ZR.- (zc ZR.- zd)) ∷ []

    e₃ : Vec Z 4
    e₃ = A ∷ (√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zd)) ∷ (A ZR.+ (2ᶻ ZR.* zc)) ∷ (√2ᶻ ZR.* (zb ZR.- zd)) ∷ []

    eB : Vec Z 4
    eB = (√2ᶻ ZR.* (A ZR.+ zc)) ∷ (√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zd)) ∷ (ZR.- (√2ᶻ ZR.* zc)) ∷ (√2ᶻ ZR.* (zb ZR.- zd)) ∷ []

    e₄ : Vec Z 4
    e₄ = (√2ᶻ ZR.* (A ZR.+ zc)) ∷ (√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zd)) ∷ ((zb ZR.- zd) ZR.- zc) ∷ ((ZR.- zc) ZR.- (zb ZR.- zd)) ∷ []

    eAB : Vec Z 4
    eAB = ((A ZR.+ zc) ZR.+ ((A ZR.+ zb) ZR.+ zd)) ∷ ((A ZR.+ zc) ZR.- ((A ZR.+ zb) ZR.+ zd)) ∷ ((zb ZR.- zd) ZR.- zc) ∷ ((ZR.- zc) ZR.- (zb ZR.- zd)) ∷ []

    e₇ : Vec Z 4
    e₇ = A ∷ (√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zc)) ∷ (√2ᶻ ZR.* (zb ZR.- zc)) ∷ (A ZR.+ (2ᶻ ZR.* zd)) ∷ []

    eC : Vec Z 4
    eC = (√2ᶻ ZR.* (A ZR.+ zd)) ∷ (√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zc)) ∷ (√2ᶻ ZR.* (zb ZR.- zc)) ∷ (ZR.- (√2ᶻ ZR.* zd)) ∷ []

    e₅ : Vec Z 4
    e₅ = (√2ᶻ ZR.* (A ZR.+ zc)) ∷ (((A ZR.+ zb) ZR.+ zd) ZR.- zc) ∷ (((A ZR.+ zb) ZR.+ zd) ZR.+ zc) ∷ (√2ᶻ ZR.* (zb ZR.- zd)) ∷ []

    eCB : Vec Z 4
    eCB = ((A ZR.+ zc) ZR.+ (zb ZR.- zd)) ∷ (((A ZR.+ zb) ZR.+ zd) ZR.- zc) ∷ (((A ZR.+ zb) ZR.+ zd) ZR.+ zc) ∷ ((A ZR.+ zc) ZR.- (zb ZR.- zd)) ∷ []

    e₆ : Vec Z 4
    e₆ = (√2ᶻ ZR.* (A ZR.+ zd)) ∷ (((A ZR.+ zb) ZR.+ zc) ZR.- zd) ∷ (√2ᶻ ZR.* (zb ZR.- zc)) ∷ (((A ZR.+ zb) ZR.+ zc) ZR.+ zd) ∷ []

    eBC : Vec Z 4
    eBC = ((A ZR.+ zd) ZR.+ (zb ZR.- zc)) ∷ (((A ZR.+ zb) ZR.+ zc) ZR.- zd) ∷ ((A ZR.+ zd) ZR.- (zb ZR.- zc)) ∷ (((A ZR.+ zb) ZR.+ zc) ZR.+ zd) ∷ []

    S1-α S1-β : Z
    S1-α = (√2ᶻ ZR.* ((A ZR.+ zc) ZR.+ zd))
    S1-β = (√2ᶻ ZR.* (zc ZR.- zd))

    S2-α S2-β : Z
    S2-α = (√2ᶻ ZR.* (A ZR.+ zb))
    S2-β = (ZR.- (√2ᶻ ZR.* zb))

    S3-α S3-β : Z
    S3-α = ((zc ZR.- zd) ZR.- zb)
    S3-β = ((ZR.- zb) ZR.- (zc ZR.- zd))

    S4-α S4-β : Z
    S4-α = ((A ZR.+ zb) ZR.+ ((A ZR.+ zc) ZR.+ zd))
    S4-β = ((A ZR.+ zb) ZR.- ((A ZR.+ zc) ZR.+ zd))

    S5-α S5-β : Z
    S5-α = (√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zd))
    S5-β = (√2ᶻ ZR.* (zb ZR.- zd))

    S6-α S6-β : Z
    S6-α = (√2ᶻ ZR.* (A ZR.+ zc))
    S6-β = (ZR.- (√2ᶻ ZR.* zc))

    S7-α S7-β : Z
    S7-α = ((zb ZR.- zd) ZR.- zc)
    S7-β = ((ZR.- zc) ZR.- (zb ZR.- zd))

    S8-α S8-β : Z
    S8-α = ((A ZR.+ zc) ZR.+ ((A ZR.+ zb) ZR.+ zd))
    S8-β = ((A ZR.+ zc) ZR.- ((A ZR.+ zb) ZR.+ zd))

    S9-α S9-β : Z
    S9-α = (√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zc))
    S9-β = (√2ᶻ ZR.* (zb ZR.- zc))

    S10-α S10-β : Z
    S10-α = (√2ᶻ ZR.* (A ZR.+ zd))
    S10-β = (ZR.- (√2ᶻ ZR.* zd))

    S11-α S11-β : Z
    S11-α = (((A ZR.+ zb) ZR.+ zd) ZR.- zc)
    S11-β = (((A ZR.+ zb) ZR.+ zd) ZR.+ zc)

    S12-α S12-β : Z
    S12-α = ((A ZR.+ zc) ZR.+ (zb ZR.- zd))
    S12-β = ((A ZR.+ zc) ZR.- (zb ZR.- zd))

    S13-α S13-β : Z
    S13-α = (((A ZR.+ zb) ZR.+ zc) ZR.- zd)
    S13-β = (((A ZR.+ zb) ZR.+ zc) ZR.+ zd)

    S14-α S14-β : Z
    S14-α = ((A ZR.+ zd) ZR.+ (zb ZR.- zc))
    S14-β = ((A ZR.+ zd) ZR.- (zb ZR.- zc))

    -- S1: H_[c,d] on e₀
    S1-sum : ((A ZR.+ (2ᶻ ZR.* zc)) ZR.+ (A ZR.+ (2ᶻ ZR.* zd))) ≡ (√2ᶻ ZR.* (√2ᶻ ZR.* ((A ZR.+ zc) ZR.+ zd)))
    S1-sum = ZG.solve 4 (λ A zb zc zd → ((A :+ ((con 2ᶻ) :* zc)) :+ (A :+ ((con 2ᶻ) :* zd))) := ((con √2ᶻ) :* ((con √2ᶻ) :* ((A :+ zc) :+ zd)))) ≡.refl A zb zc zd
    S1-dif : ((A ZR.+ (2ᶻ ZR.* zc)) ZR.- (A ZR.+ (2ᶻ ZR.* zd))) ≡ (√2ᶻ ZR.* (√2ᶻ ZR.* (zc ZR.- zd)))
    S1-dif = ZG.solve 4 (λ A zb zc zd → ((A :+ ((con 2ᶻ) :* zc)) :- (A :+ ((con 2ᶻ) :* zd))) := ((con √2ᶻ) :* ((con √2ᶻ) :* (zc :- zd)))) ≡.refl A zb zc zd

    -- S2: H_[a,b] on e₁
    S2-sum : (A ZR.+ (A ZR.+ (2ᶻ ZR.* zb))) ≡ (√2ᶻ ZR.* (√2ᶻ ZR.* (A ZR.+ zb)))
    S2-sum = ZG.solve 4 (λ A zb zc zd → (A :+ (A :+ ((con 2ᶻ) :* zb))) := ((con √2ᶻ) :* ((con √2ᶻ) :* (A :+ zb)))) ≡.refl A zb zc zd
    S2-dif : (A ZR.- (A ZR.+ (2ᶻ ZR.* zb))) ≡ (√2ᶻ ZR.* (ZR.- (√2ᶻ ZR.* zb)))
    S2-dif = ZG.solve 4 (λ A zb zc zd → (A :- (A :+ ((con 2ᶻ) :* zb))) := ((con √2ᶻ) :* (:- ((con √2ᶻ) :* zb)))) ≡.refl A zb zc zd

    -- S3: H_[b,d] on eA
    S3-sum : ((ZR.- (√2ᶻ ZR.* zb)) ZR.+ (√2ᶻ ZR.* (zc ZR.- zd))) ≡ (√2ᶻ ZR.* ((zc ZR.- zd) ZR.- zb))
    S3-sum = ZG.solve 4 (λ A zb zc zd → ((:- ((con √2ᶻ) :* zb)) :+ ((con √2ᶻ) :* (zc :- zd))) := ((con √2ᶻ) :* ((zc :- zd) :- zb))) ≡.refl A zb zc zd
    S3-dif : ((ZR.- (√2ᶻ ZR.* zb)) ZR.- (√2ᶻ ZR.* (zc ZR.- zd))) ≡ (√2ᶻ ZR.* ((ZR.- zb) ZR.- (zc ZR.- zd)))
    S3-dif = ZG.solve 4 (λ A zb zc zd → ((:- ((con √2ᶻ) :* zb)) :- ((con √2ᶻ) :* (zc :- zd))) := ((con √2ᶻ) :* ((:- zb) :- (zc :- zd)))) ≡.refl A zb zc zd

    -- S4: H_[a,c] on e₂
    S4-sum : ((√2ᶻ ZR.* (A ZR.+ zb)) ZR.+ (√2ᶻ ZR.* ((A ZR.+ zc) ZR.+ zd))) ≡ (√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ ((A ZR.+ zc) ZR.+ zd)))
    S4-sum = ZG.solve 4 (λ A zb zc zd → (((con √2ᶻ) :* (A :+ zb)) :+ ((con √2ᶻ) :* ((A :+ zc) :+ zd))) := ((con √2ᶻ) :* ((A :+ zb) :+ ((A :+ zc) :+ zd)))) ≡.refl A zb zc zd
    S4-dif : ((√2ᶻ ZR.* (A ZR.+ zb)) ZR.- (√2ᶻ ZR.* ((A ZR.+ zc) ZR.+ zd))) ≡ (√2ᶻ ZR.* ((A ZR.+ zb) ZR.- ((A ZR.+ zc) ZR.+ zd)))
    S4-dif = ZG.solve 4 (λ A zb zc zd → (((con √2ᶻ) :* (A :+ zb)) :- ((con √2ᶻ) :* ((A :+ zc) :+ zd))) := ((con √2ᶻ) :* ((A :+ zb) :- ((A :+ zc) :+ zd)))) ≡.refl A zb zc zd

    -- S5: H_[b,d] on e₀
    S5-sum : ((A ZR.+ (2ᶻ ZR.* zb)) ZR.+ (A ZR.+ (2ᶻ ZR.* zd))) ≡ (√2ᶻ ZR.* (√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zd)))
    S5-sum = ZG.solve 4 (λ A zb zc zd → ((A :+ ((con 2ᶻ) :* zb)) :+ (A :+ ((con 2ᶻ) :* zd))) := ((con √2ᶻ) :* ((con √2ᶻ) :* ((A :+ zb) :+ zd)))) ≡.refl A zb zc zd
    S5-dif : ((A ZR.+ (2ᶻ ZR.* zb)) ZR.- (A ZR.+ (2ᶻ ZR.* zd))) ≡ (√2ᶻ ZR.* (√2ᶻ ZR.* (zb ZR.- zd)))
    S5-dif = ZG.solve 4 (λ A zb zc zd → ((A :+ ((con 2ᶻ) :* zb)) :- (A :+ ((con 2ᶻ) :* zd))) := ((con √2ᶻ) :* ((con √2ᶻ) :* (zb :- zd)))) ≡.refl A zb zc zd

    -- S6: H_[a,c] on e₃
    S6-sum : (A ZR.+ (A ZR.+ (2ᶻ ZR.* zc))) ≡ (√2ᶻ ZR.* (√2ᶻ ZR.* (A ZR.+ zc)))
    S6-sum = ZG.solve 4 (λ A zb zc zd → (A :+ (A :+ ((con 2ᶻ) :* zc))) := ((con √2ᶻ) :* ((con √2ᶻ) :* (A :+ zc)))) ≡.refl A zb zc zd
    S6-dif : (A ZR.- (A ZR.+ (2ᶻ ZR.* zc))) ≡ (√2ᶻ ZR.* (ZR.- (√2ᶻ ZR.* zc)))
    S6-dif = ZG.solve 4 (λ A zb zc zd → (A :- (A :+ ((con 2ᶻ) :* zc))) := ((con √2ᶻ) :* (:- ((con √2ᶻ) :* zc)))) ≡.refl A zb zc zd

    -- S7: H_[c,d] on eB
    S7-sum : ((ZR.- (√2ᶻ ZR.* zc)) ZR.+ (√2ᶻ ZR.* (zb ZR.- zd))) ≡ (√2ᶻ ZR.* ((zb ZR.- zd) ZR.- zc))
    S7-sum = ZG.solve 4 (λ A zb zc zd → ((:- ((con √2ᶻ) :* zc)) :+ ((con √2ᶻ) :* (zb :- zd))) := ((con √2ᶻ) :* ((zb :- zd) :- zc))) ≡.refl A zb zc zd
    S7-dif : ((ZR.- (√2ᶻ ZR.* zc)) ZR.- (√2ᶻ ZR.* (zb ZR.- zd))) ≡ (√2ᶻ ZR.* ((ZR.- zc) ZR.- (zb ZR.- zd)))
    S7-dif = ZG.solve 4 (λ A zb zc zd → ((:- ((con √2ᶻ) :* zc)) :- ((con √2ᶻ) :* (zb :- zd))) := ((con √2ᶻ) :* ((:- zc) :- (zb :- zd)))) ≡.refl A zb zc zd

    -- S8: H_[a,b] on e₄
    S8-sum : ((√2ᶻ ZR.* (A ZR.+ zc)) ZR.+ (√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zd))) ≡ (√2ᶻ ZR.* ((A ZR.+ zc) ZR.+ ((A ZR.+ zb) ZR.+ zd)))
    S8-sum = ZG.solve 4 (λ A zb zc zd → (((con √2ᶻ) :* (A :+ zc)) :+ ((con √2ᶻ) :* ((A :+ zb) :+ zd))) := ((con √2ᶻ) :* ((A :+ zc) :+ ((A :+ zb) :+ zd)))) ≡.refl A zb zc zd
    S8-dif : ((√2ᶻ ZR.* (A ZR.+ zc)) ZR.- (√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zd))) ≡ (√2ᶻ ZR.* ((A ZR.+ zc) ZR.- ((A ZR.+ zb) ZR.+ zd)))
    S8-dif = ZG.solve 4 (λ A zb zc zd → (((con √2ᶻ) :* (A :+ zc)) :- ((con √2ᶻ) :* ((A :+ zb) :+ zd))) := ((con √2ᶻ) :* ((A :+ zc) :- ((A :+ zb) :+ zd)))) ≡.refl A zb zc zd

    -- S9: H_[b,c] on e₀
    S9-sum : ((A ZR.+ (2ᶻ ZR.* zb)) ZR.+ (A ZR.+ (2ᶻ ZR.* zc))) ≡ (√2ᶻ ZR.* (√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zc)))
    S9-sum = ZG.solve 4 (λ A zb zc zd → ((A :+ ((con 2ᶻ) :* zb)) :+ (A :+ ((con 2ᶻ) :* zc))) := ((con √2ᶻ) :* ((con √2ᶻ) :* ((A :+ zb) :+ zc)))) ≡.refl A zb zc zd
    S9-dif : ((A ZR.+ (2ᶻ ZR.* zb)) ZR.- (A ZR.+ (2ᶻ ZR.* zc))) ≡ (√2ᶻ ZR.* (√2ᶻ ZR.* (zb ZR.- zc)))
    S9-dif = ZG.solve 4 (λ A zb zc zd → ((A :+ ((con 2ᶻ) :* zb)) :- (A :+ ((con 2ᶻ) :* zc))) := ((con √2ᶻ) :* ((con √2ᶻ) :* (zb :- zc)))) ≡.refl A zb zc zd

    -- S10: H_[a,d] on e₇
    S10-sum : (A ZR.+ (A ZR.+ (2ᶻ ZR.* zd))) ≡ (√2ᶻ ZR.* (√2ᶻ ZR.* (A ZR.+ zd)))
    S10-sum = ZG.solve 4 (λ A zb zc zd → (A :+ (A :+ ((con 2ᶻ) :* zd))) := ((con √2ᶻ) :* ((con √2ᶻ) :* (A :+ zd)))) ≡.refl A zb zc zd
    S10-dif : (A ZR.- (A ZR.+ (2ᶻ ZR.* zd))) ≡ (√2ᶻ ZR.* (ZR.- (√2ᶻ ZR.* zd)))
    S10-dif = ZG.solve 4 (λ A zb zc zd → (A :- (A :+ ((con 2ᶻ) :* zd))) := ((con √2ᶻ) :* (:- ((con √2ᶻ) :* zd)))) ≡.refl A zb zc zd

    -- S11: H_[b,c] on eB
    S11-sum : ((√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zd)) ZR.+ (ZR.- (√2ᶻ ZR.* zc))) ≡ (√2ᶻ ZR.* (((A ZR.+ zb) ZR.+ zd) ZR.- zc))
    S11-sum = ZG.solve 4 (λ A zb zc zd → (((con √2ᶻ) :* ((A :+ zb) :+ zd)) :+ (:- ((con √2ᶻ) :* zc))) := ((con √2ᶻ) :* (((A :+ zb) :+ zd) :- zc))) ≡.refl A zb zc zd
    S11-dif : ((√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zd)) ZR.- (ZR.- (√2ᶻ ZR.* zc))) ≡ (√2ᶻ ZR.* (((A ZR.+ zb) ZR.+ zd) ZR.+ zc))
    S11-dif = ZG.solve 4 (λ A zb zc zd → (((con √2ᶻ) :* ((A :+ zb) :+ zd)) :- (:- ((con √2ᶻ) :* zc))) := ((con √2ᶻ) :* (((A :+ zb) :+ zd) :+ zc))) ≡.refl A zb zc zd

    -- S12: H_[a,d] on e₅
    S12-sum : ((√2ᶻ ZR.* (A ZR.+ zc)) ZR.+ (√2ᶻ ZR.* (zb ZR.- zd))) ≡ (√2ᶻ ZR.* ((A ZR.+ zc) ZR.+ (zb ZR.- zd)))
    S12-sum = ZG.solve 4 (λ A zb zc zd → (((con √2ᶻ) :* (A :+ zc)) :+ ((con √2ᶻ) :* (zb :- zd))) := ((con √2ᶻ) :* ((A :+ zc) :+ (zb :- zd)))) ≡.refl A zb zc zd
    S12-dif : ((√2ᶻ ZR.* (A ZR.+ zc)) ZR.- (√2ᶻ ZR.* (zb ZR.- zd))) ≡ (√2ᶻ ZR.* ((A ZR.+ zc) ZR.- (zb ZR.- zd)))
    S12-dif = ZG.solve 4 (λ A zb zc zd → (((con √2ᶻ) :* (A :+ zc)) :- ((con √2ᶻ) :* (zb :- zd))) := ((con √2ᶻ) :* ((A :+ zc) :- (zb :- zd)))) ≡.refl A zb zc zd

    -- S13: H_[b,d] on eC
    S13-sum : ((√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zc)) ZR.+ (ZR.- (√2ᶻ ZR.* zd))) ≡ (√2ᶻ ZR.* (((A ZR.+ zb) ZR.+ zc) ZR.- zd))
    S13-sum = ZG.solve 4 (λ A zb zc zd → (((con √2ᶻ) :* ((A :+ zb) :+ zc)) :+ (:- ((con √2ᶻ) :* zd))) := ((con √2ᶻ) :* (((A :+ zb) :+ zc) :- zd))) ≡.refl A zb zc zd
    S13-dif : ((√2ᶻ ZR.* ((A ZR.+ zb) ZR.+ zc)) ZR.- (ZR.- (√2ᶻ ZR.* zd))) ≡ (√2ᶻ ZR.* (((A ZR.+ zb) ZR.+ zc) ZR.+ zd))
    S13-dif = ZG.solve 4 (λ A zb zc zd → (((con √2ᶻ) :* ((A :+ zb) :+ zc)) :- (:- ((con √2ᶻ) :* zd))) := ((con √2ᶻ) :* (((A :+ zb) :+ zc) :+ zd))) ≡.refl A zb zc zd

    -- S14: H_[a,c] on e₆
    S14-sum : ((√2ᶻ ZR.* (A ZR.+ zd)) ZR.+ (√2ᶻ ZR.* (zb ZR.- zc))) ≡ (√2ᶻ ZR.* ((A ZR.+ zd) ZR.+ (zb ZR.- zc)))
    S14-sum = ZG.solve 4 (λ A zb zc zd → (((con √2ᶻ) :* (A :+ zd)) :+ ((con √2ᶻ) :* (zb :- zc))) := ((con √2ᶻ) :* ((A :+ zd) :+ (zb :- zc)))) ≡.refl A zb zc zd
    S14-dif : ((√2ᶻ ZR.* (A ZR.+ zd)) ZR.- (√2ᶻ ZR.* (zb ZR.- zc))) ≡ (√2ᶻ ZR.* ((A ZR.+ zd) ZR.- (zb ZR.- zc)))
    S14-dif = ZG.solve 4 (λ A zb zc zd → (((con √2ᶻ) :* (A :+ zd)) :- ((con √2ᶻ) :* (zb :- zc))) := ((con √2ᶻ) :* ((A :+ zd) :- (zb :- zc)))) ≡.refl A zb zc zd


    odd4 : ∀ m → Odd (W ! ι m)
    odd4 ₀ = ≡.trans (≡.cong oddᶻ wa) oA
    odd4 ₁ = ≡.trans (par {W ! b} {A} zb wb) oA
    odd4 ₂ = ≡.trans (par {W ! c} {A} zc wc) oA
    odd4 ₃ = ≡.trans (par {W ! d} {A} zd wd) oA

    cls : ∀ m → rbit (W ! ι m) ≡ rbit A
    cls ₀ = ≡.cong rbit wa
    cls ₁ = rpar {W ! b} {A} zb wb
    cls ₂ = rpar {W ! c} {A} zc wc
    cls ₃ = rpar {W ! d} {A} zd wd

    valid : ∀ i j → Valid W (ι i) (ι j)
    valid i j = odd4 i , odd4 j , ≡.trans (cls i) (≡.sym (cls j))

    K₀ : Known W N e₀
    K₀ = known (≡.trans colM (≡.cong (scV k) (≡.trans (≡.sym (emb-self W)) (emb-ext {loc W} {e₀} {W} {W} loc≡ (λ _ _ → ≡.refl))))) be
      where
      at : ∀ m → W ! ι m ≡ e₀ ! m
      at ₀ = wa
      at ₁ = wb
      at ₂ = wc
      at ₃ = wd
      loc≡ : ∀ m → loc W ! m ≡ e₀ ! m
      loc≡ m = ≡.trans (VecP.lookup∘tabulate (λ m → W ! ι m) m) (at m)

    lw : ∀ {N′ e} → Known W N′ e → (m : Fin 4) → Even (e ! m) → level N′ <ₗ L
    lw = lowK odd4 ℓM

    -- The canonical pairing.
    pA : Path ΠA N oN
    pA = path-cong cd-ab N oN (path-• Hcd Hab N oN pCD pAB)
      where
      pCD : Path Hcd (actM (H-gen a b ab) N) (ColOrth-actMʷ Hab oN)
      pCD = ih (H-gen c d cd) (actM (H-gen a b ab) N) (ColOrth-actMʷ Hab oN) (below a b ab (valid ₀ ₁))
               (below₂ a b ab c d cd (valid ₀ ₁) (valid ₂ ₃) c≢a c≢b d≢a d≢b)

    K₁ = stepH ₂ ₃ cd S1-α S1-β S1-sum S1-dif K₀
    K₃ = stepH ₁ ₃ bd S5-α S5-β S5-sum S5-dif K₀
    KB = stepH ₀ ₂ ac S6-α S6-β S6-sum S6-dif K₃

    --------------------------------------------------------------------
    -- S even: Π_A to Π_B by (f1)

    module CaseI (even : oddᶻ S ≡ false) where

      private
        KA  = stepH ₀ ₁ ab S2-α S2-β S2-sum S2-dif K₁
        K₂  = stepH ₁ ₃ bd S3-α S3-β S3-sum S3-dif KA
        KBA = stepH ₀ ₂ ac S4-α S4-β S4-sum S4-dif K₂
        K₄  = stepH ₂ ₃ cd S7-α S7-β S7-sum S7-dif KB
        KAB = stepH ₀ ₁ ab S8-α S8-β S8-sum S8-dif K₄

        evS : ∀ {x} y → x ≡ S ZR.+ 2ᶻ ZR.* y → Even x
        evS {x} y e = ≡.trans (par {x} {S} y e) even

        evBA : Even (eBA ! ₂)
        evBA = evS (ZR.- (zc ZR.+ zd))
          (ZG.solve 4 (λ A zb zc zd → (A :+ zb) :- ((A :+ zc) :+ zd) := ((zb :+ zc) :+ zd) :+ con 2ᶻ :* (:- (zc :+ zd)))
             ≡.refl A zb zc zd)

        evAB : Even (eAB ! ₂)
        evAB = evS (ZR.- (zc ZR.+ zd))
          (ZG.solve 4 (λ A zb zc zd → (zb :- zd) :- zc := ((zb :+ zc) :+ zd) :+ con 2ᶻ :* (:- (zc :+ zd)))
             ≡.refl A zb zc zd)

        lowBA : Low L ΠB (actMʷ ΠA N)
        lowBA = (lw KA ₀ (even-r (A ZR.+ zb)) , lw K₂ ₀ (even-r (A ZR.+ zb))) , (lw K₂ ₀ (even-r (A ZR.+ zb)) , lw KBA ₂ evBA)

        lowAB : Low L ΠA (actMʷ ΠB N)
        lowAB = (lw KB ₀ (even-r (A ZR.+ zc)) , lw K₄ ₀ (even-r (A ZR.+ zc))) , (lw K₄ ₀ (even-r (A ZR.+ zc)) , lw KAB ₂ evAB)

        pBA : Path (ΠB • ΠA) N oN
        pBA = path-• ΠB ΠA N oN (path-below ih ΠB (actMʷ ΠA N) (ColOrth-actMʷ ΠA oN) lowBA) pA

        pB : Path ΠB N oN
        pB = peel ΠA ΠB N oN (path-cong (sym f1) N oN pBA) (path-below ih ΠA (actMʷ ΠB N) (ColOrth-actMʷ ΠB oN) lowAB)

      pBD : Path Hbd N oN
      pBD = peel Hac Hbd N oN pB
              (ih (H-gen a c ac) (actM (H-gen b d bd) N) (ColOrth-actMʷ Hbd oN) (below b d bd (valid ₁ ₃))
                  (below₂ b d bd a c ac (valid ₁ ₃) (valid ₀ ₂) a≢b a≢d c≢b c≢d))

      pAC : Path Hac N oN
      pAC = square b d bd a c ac (valid ₁ ₃) (valid ₀ ₂) a≢b a≢d c≢b c≢d pBD

    --------------------------------------------------------------------
    -- S odd: Π_B to Π_C by (f2)

    module CaseII (odd : oddᶻ S ≡ true) (pAC : Path Hac N oN) (pBD : Path Hbd N oN) where

      private
        K₇  = stepH ₁ ₂ bc S9-α S9-β S9-sum S9-dif K₀
        KC  = stepH ₀ ₃ ad S10-α S10-β S10-sum S10-dif K₇
        K₅  = stepH ₁ ₂ bc S11-α S11-β S11-sum S11-dif KB
        KCB = stepH ₀ ₃ ad S12-α S12-β S12-sum S12-dif K₅
        K₆  = stepH ₁ ₃ bd S13-α S13-β S13-sum S13-dif KC
        KBC = stepH ₀ ₂ ac S14-α S14-β S14-sum S14-dif K₆

        evAS : ∀ {x} y → x ≡ (A ZR.+ S) ZR.+ 2ᶻ ZR.* y → Even x
        evAS {x} y e = ≡.trans (par {x} {A ZR.+ S} y e) (≡.trans (oddᶻ-+ A S) (≡.cong₂ _xor_ oA odd))

        evCB : Even (eCB ! ₀)
        evCB = evAS (ZR.- zd)
          (ZG.solve 4 (λ A zb zc zd → (A :+ zc) :+ (zb :- zd) := (A :+ ((zb :+ zc) :+ zd)) :+ con 2ᶻ :* (:- zd))
             ≡.refl A zb zc zd)

        evBC : Even (eBC ! ₁)
        evBC = evAS (ZR.- zd)
          (ZG.solve 4 (λ A zb zc zd → ((A :+ zb) :+ zc) :- zd := (A :+ ((zb :+ zc) :+ zd)) :+ con 2ᶻ :* (:- zd))
             ≡.refl A zb zc zd)

        pB : Path ΠB N oN
        pB = path-• Hac Hbd N oN
               (ih (H-gen a c ac) (actM (H-gen b d bd) N) (ColOrth-actMʷ Hbd oN) (below b d bd (valid ₁ ₃))
                   (below₂ b d bd a c ac (valid ₁ ₃) (valid ₀ ₂) a≢b a≢d c≢b c≢d))
               pBD

        lowCB : Low L ΠC (actMʷ ΠB N)
        lowCB = (lw KB ₀ (even-r (A ZR.+ zc)) , lw K₅ ₀ (even-r (A ZR.+ zc))) , (lw K₅ ₀ (even-r (A ZR.+ zc)) , lw KCB ₀ evCB)

        lt₀ : level (actMʷ (ΠC • ΠB) N) <ₗ L
        lt₀ = lw KCB ₀ evCB
        lt₁ : level (actMʷ (Xcd • ΠC • ΠB) N) <ₗ L
        lt₁ = X-low cd d≤p (actMʷ (ΠC • ΠB) N) lt₀
        lt₂ : level (actMʷ (Xab • Xcd • ΠC • ΠB) N) <ₗ L
        lt₂ = X-low ab b≤p (actMʷ (Xcd • ΠC • ΠB) N) lt₁

        lowXX : Low L (Xab • Xcd) (actMʷ (ΠC • ΠB) N)
        lowXX = (lt₀ , lt₁) , (lt₁ , lt₂)

        lowBC : Low L ΠB (actMʷ ΠC N)
        lowBC = (lw KC ₀ (even-r (A ZR.+ zd)) , lw K₆ ₀ (even-r (A ZR.+ zd))) , (lw K₆ ₀ (even-r (A ZR.+ zd)) , lw KBC ₁ evBC)

        pCB : Path (ΠC • ΠB) N oN
        pCB = path-• ΠC ΠB N oN (path-below ih ΠC (actMʷ ΠB N) (ColOrth-actMʷ ΠB oN) lowCB) pB

        pXCB : Path ((Xab • Xcd) • ΠC • ΠB) N oN
        pXCB = path-• (Xab • Xcd) (ΠC • ΠB) N oN
                 (path-below ih (Xab • Xcd) (actMʷ (ΠC • ΠB) N) (ColOrth-actMʷ (ΠC • ΠB) oN) lowXX) pCB

        pC : Path ΠC N oN
        pC = peel ΠB ΠC N oN (path-cong (sym f2′) N oN pXCB)
               (path-below ih ΠB (actMʷ ΠC N) (ColOrth-actMʷ ΠC oN) lowBC)

      pBC : Path Hbc N oN
      pBC = peel Had Hbc N oN pC
              (ih (H-gen a d ad) (actM (H-gen b c bc) N) (ColOrth-actMʷ Hbc oN) (below b c bc (valid ₁ ₂))
                  (below₂ b c bc a d ad (valid ₁ ₂) (valid ₀ ₃) a≢b a≢c d≢b d≢c))

      pAD : Path Had N oN
      pAD = square b c bc a d ad (valid ₁ ₂) (valid ₀ ₃) a≢b a≢c d≢b d≢c pBC

------------------------------------------------------------------------
-- The diamond

module _ (M : Matrix n n D) .(o : ColOrth M) (eq : level M ≡ L) where

  open State M o eq using (W ; odd≤ ; square ; canonical-at)

  diamond : ∀ {a b c d : Fin n} (ab : a < b) (bc : b < c) (cd : c < d) →
            firstOdd W ≡ just a → nextSame a W ≡ just b →
            Odd (W ! c) → Odd (W ! d) → rbit (W ! c) ≡ rbit (W ! a) → rbit (W ! d) ≡ rbit (W ! a) →
            (Path (H a c (FinP.<-trans ab bc)) M o × Path (H b d (FinP.<-trans bc cd)) M o) ×
            (Path (H a d (FinP.<-trans ab (FinP.<-trans bc cd))) M o × Path (H b c bc) M o)
  diamond {a} {b} {c} {d} ab bc cd fa nb oc od rc rd = result
    where
    d≤p : d ≤ p
    d≤p = odd≤ od
    open Four ab bc cd d≤p

    oa : Odd (W ! a)
    oa = proj₁ (firstOdd-spec W fa)

    private
      spec = nextSame-spec W nb
    ob : Odd (W ! b)
    ob = proj₁ (proj₁ (proj₂ spec))
    rb : rbit (W ! b) ≡ rbit (W ! a)
    rb = proj₂ (proj₁ (proj₂ spec))

    A = W ! a
    Cb = same-class (W ! b) A ob oa rb
    Cc = same-class (W ! c) A oc oa rc
    Cd = same-class (W ! d) A od oa rd
    zb = proj₁ Cb
    zc = proj₁ Cc
    zd = proj₁ Cd

    pAB : Path Hab M o
    pAB = canonical-at ab fa nb

    module R = Route M o eq A zb zc zd oa ≡.refl (proj₂ Cb) (proj₂ Cc) (proj₂ Cd) pAB

    -- The state Z_[d]·M.
    MZ = actM (Z-gen d) M
    eqZ : level MZ ≡ L
    eqZ = mono-L (Z-gen d) tt d≤p M eq
    module SZ = State MZ (ColOrth-actMʷ (Zʷ d) o) eqZ

    WZ : SZ.W ≡ Zᶻ d W
    WZ = ≡.trans (≡.cong num (col-actM (Z-gen d) M p)) (proj₂ (lde-Z d (col M p)))

    zdZ = ZR.- A ZR.- zd

    at≢ : ∀ {x} → x ≢ d → SZ.W ! x ≡ W ! x
    at≢ {x} x≢d = ≡.trans (≡.cong (_! x) WZ) (set₁-≢ d (ZR.- (W ! d)) W x≢d)

    wdZ : SZ.W ! d ≡ A ZR.+ 2ᶻ ZR.* zdZ
    wdZ = ≡.trans (≡.cong (_! d) WZ) (≡.trans (set₁-a d (ZR.- (W ! d)) W)
            (≡.trans (≡.cong ZR.-_ (proj₂ Cd))
                     (ZG.solve 2 (λ A zd → :- (A :+ con 2ᶻ :* zd) := A :+ con 2ᶻ :* ((:- A) :- zd)) ≡.refl A zd)))

    faZ : firstOdd SZ.W ≡ just a
    faZ = ≡.trans (firstOdd-cong SZ.W W (λ x → ≡.trans (≡.cong (λ w → oddᶻ (w ! x)) WZ) (odd-Z d W x))) fa

    nbZ : nextSame a SZ.W ≡ just b
    nbZ = ≡.trans (nextSame-cong SZ.W W a (λ x → ≡.trans (≡.cong (λ w → oddᶻ (w ! x)) WZ) (odd-Z d W x))
                                          (λ x → ≡.trans (≡.cong (λ w → rbit (w ! x)) WZ) (rbit-Z d W x))) nb

    pABZ : Path Hab MZ (ColOrth-actMʷ (Zʷ d) o)
    pABZ = SZ.canonical-at ab faZ nbZ

    module RZ = Route MZ (ColOrth-actMʷ (Zʷ d) o) eqZ A zb zc zdZ oa (at≢ a≢d) (≡.trans (at≢ b≢d) (proj₂ Cb))
                      (≡.trans (at≢ c≢d) (proj₂ Cc)) wdZ pABZ

    -- The parity of S flips.
    S-flip : oddᶻ RZ.S ≡ not (oddᶻ R.S)
    S-flip =
      ≡.trans (par {RZ.S} {R.S ZR.+ ZR.- A} (ZR.- zd) (ZG.solve 4 (λ A zb zc zd → (zb :+ zc) :+ ((:- A) :- zd) := (((zb :+ zc) :+ zd) :+ (:- A)) :+ con 2ᶻ :* (:- zd)) ≡.refl A zb zc zd))
        (≡.trans (oddᶻ-+ R.S (ZR.- A)) (≡.trans (≡.cong (oddᶻ R.S xor_) (≡.trans (oddᶻ-neg A) oa)) (xor-true (oddᶻ R.S))))

    -- The edges Z_[d] out of M and Z_[d]·M.
    vab = R.valid ₀ ₁
    vabZ = RZ.valid ₀ ₁

    Zd-ab : Zʷ d • Hab ≈ Hab • Zʷ d
    Zd-ab = comm-gen (Z-gen d) (H-gen a b ab) ((d≢a ∷ d≢b ∷ []) ∷ [])

    pZ : Path (Zʷ d) M o
    pZ = bridge (Z-gen d) M o Hab Hab (Zʷ d) pAB pABZ
           (below-ab , Z-low d≤p _ below-ab) Zd-ab
      where
      below-ab = State.below M o eq a b ab vab

    pZZ : Path (Zʷ d) MZ (ColOrth-actMʷ (Zʷ d) o)
    pZZ = bridge (Z-gen d) MZ (ColOrth-actMʷ (Zʷ d) o) Hab Hab (Zʷ d) pABZ (path-≡ (≡.sym (act-gg (Z-gen d) M)) pAB)
            (below-ab , Z-low d≤p _ below-ab) Zd-ab
      where
      below-ab = SZ.below a b ab vabZ

    -- Z_[d] commutes with H_[x,y] for x, y ≠ d: H is a path at M iff at
    -- Z_[d]·M.
    module Trick {x y : Fin n} .(xy : x < y) (x≢d : x ≢ d) (y≢d : y ≢ d) (i j : Fin 4)
                 (ix : ι i ≡ x) (jy : ι j ≡ y) where

      private
        vM : Valid W x y
        vM = ≡.subst₂ (Valid W) ix jy (R.valid i j)
        vZ : Valid SZ.W x y
        vZ = ≡.subst₂ (Valid SZ.W) ix jy (RZ.valid i j)
        sym≢ : ∀ {u v : Fin n} → u ≢ v → v ≢ u
        sym≢ ne e = ne (≡.sym e)
        comm : Zʷ d • H x y xy ≈ H x y xy • Zʷ d
        comm = comm-gen (Z-gen d) (H-gen x y xy) ((sym≢ x≢d ∷ sym≢ y≢d ∷ []) ∷ [])
        ZHZ : Zʷ d • H x y xy • Zʷ d ≈ H x y xy
        ZHZ = begin
          Zʷ d • H x y xy • Zʷ d      ≈⟨ sym assoc ⟩
          (Zʷ d • H x y xy) • Zʷ d    ≈⟨ cleft comm ⟩
          (H x y xy • Zʷ d) • Zʷ d    ≈⟨ assoc ⟩
          H x y xy • (Zʷ d • Zʷ d)    ≈⟨ cright Z-Z ⟩
          H x y xy • ε                ≈⟨ right-unit ⟩
          H x y xy                    ∎

      from-Z : Path (H x y xy) MZ (ColOrth-actMʷ (Zʷ d) o) → Path (H x y xy) M o
      from-Z pH = path-cong ZHZ M o (path-• (Zʷ d) (H x y xy • Zʷ d) M o pZ′ (path-• (H x y xy) (Zʷ d) M o pH pZ))
        where
        lt = SZ.below x y xy vZ
        pZ′ : Path (Zʷ d) (actM (H-gen x y xy) MZ) (ColOrth-actMʷ (H x y xy • Zʷ d) o)
        pZ′ = ih (Z-gen d) (actM (H-gen x y xy) MZ) (ColOrth-actMʷ (H x y xy • Zʷ d) o) lt (Z-low d≤p _ lt)

      to-Z : Path (H x y xy) M o → Path (H x y xy) MZ (ColOrth-actMʷ (Zʷ d) o)
      to-Z pH = path-cong ZHZ MZ (ColOrth-actMʷ (Zʷ d) o)
                  (path-• (Zʷ d) (H x y xy • Zʷ d) MZ (ColOrth-actMʷ (Zʷ d) o) pZ′ (path-• (H x y xy) (Zʷ d) MZ (ColOrth-actMʷ (Zʷ d) o) pH′ pZZ))
        where
        back≡ : actM (Z-gen d) MZ ≡ M
        back≡ = act-gg (Z-gen d) M
        pH′ : Path (H x y xy) (actM (Z-gen d) MZ) (ColOrth-actMʷ (Zʷ d) (ColOrth-actMʷ (Zʷ d) o))
        pH′ = path-≡ (≡.sym back≡) pH
        lt : level (actM (H-gen x y xy) (actM (Z-gen d) MZ)) <ₗ L
        lt = ≡.subst (λ N → level (actM (H-gen x y xy) N) <ₗ L) (≡.sym back≡) (State.below M o eq x y xy vM)
        pZ′ : Path (Zʷ d) (actM (H-gen x y xy) (actM (Z-gen d) MZ)) (ColOrth-actMʷ (H x y xy • Zʷ d) (ColOrth-actMʷ (Zʷ d) o))
        pZ′ = ih (Z-gen d) (actM (H-gen x y xy) (actM (Z-gen d) MZ)) (ColOrth-actMʷ (H x y xy • Zʷ d) (ColOrth-actMʷ (Zʷ d) o))
                 lt (Z-low d≤p _ lt)

    module Tac = Trick ac a≢d c≢d ₀ ₂ ≡.refl ≡.refl
    module Tbc = Trick bc b≢d c≢d ₁ ₂ ≡.refl ≡.refl

    result : (Path Hac M o × Path Hbd M o) × (Path Had M o × Path Hbc M o)
    result = by (oddᶻ R.S) ≡.refl
      where
      by : (s : Bool) → oddᶻ R.S ≡ s → (Path Hac M o × Path Hbd M o) × (Path Had M o × Path Hbc M o)
      by false e = (CI.pAC , CI.pBD) , (pAD , pBC)
        where
        module CI = R.CaseI e
        pACZ = Tac.to-Z CI.pAC
        pBDZ = SZ.square a c ac b d bd (RZ.valid ₀ ₂) (RZ.valid ₁ ₃) b≢a b≢c d≢a d≢c pACZ
        module CIIZ = RZ.CaseII (≡.trans S-flip (≡.cong not e)) pACZ pBDZ
        pBC = Tbc.from-Z CIIZ.pBC
        pAD = square b c bc a d ad (R.valid ₁ ₂) (R.valid ₀ ₃) a≢b a≢c d≢b d≢c pBC
      by true e = (pAC , pBD) , (CII.pAD , CII.pBC)
        where
        module CIZ = RZ.CaseI (≡.trans S-flip (≡.cong not e))
        pAC = Tac.from-Z CIZ.pAC
        pBD = square a c ac b d bd (R.valid ₀ ₂) (R.valid ₁ ₃) b≢a b≢c d≢a d≢c pAC
        module CII = R.CaseII e pAC pBD
