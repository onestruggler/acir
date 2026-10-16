------------------------------------------------------------------------
-- Presentations of groups
--
-- The letters of P′ as gadgets
--
-- The affine decoding decodes a letter of P′ as a product of at most
-- four gadgets — two-level iZ, XZ or the hybrid's block on two indices
-- (`gl`):
--
--   pp a b       iZ on (a , b), nothing when a = b (the rule pp-id);
--   px c a b     XZ on (a , b) if c = a, on (b , a) if c = b, and
--                otherwise XZ on (c , a) twice, then on (a , b)
--                (Corollary A.5, decided on a template);
--   dx a b c d   XZ on (a , b), then px b c d (the rule dx-split);
--   ki a b s     the hybrid on (b , a), then iZ on (a , s) unless s = a
--                (the rule ki-sink).
--
-- Each gadget is itself a letter of P′ (`gw`), so the decomposition is
-- a derivation (`dec-w`), and with the gadgets' reading on bit vectors
-- (Five.Sem.PGad) the reading of a word over P′ is the product of the
-- two-level operators of its gadgets (`sem-w`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Five.Decode (m : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; zero ; suc ; _<_)
open import Data.Fin.Properties using (_≟_ ; _<?_ ; <-cmp ; <-asym ; <⇒≢)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_ ; lookup)
open import Data.Vec.Relation.Unary.All using () renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_ ; _≟_)
open import Examples.Groups.Clifford+CS.Encoding m using (n ; N ; N′ ; cod ; idx ; idx-cod ; cod-inj)
open import Examples.Groups.Clifford+CS.BridgeGray n using (⟦_⟧Y ; ⟦_⟧ᴾ ; ⟦_⟧PY ; PY-asG ; sound-Y)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; ki ; asG)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules
  using (_R,_===_ ; free⇒full-≈ ; pp-id ; dx-split ; ki-sink)
import Examples.Groups.Clifford+CS.Auxiliary.Sound N as Sound
open import Examples.Groups.Clifford+CS.Auxiliary.Template N′
  using (xd ; module At ; Distinct ; []ᵈ ; _∷ᵈ_ ; lookup-inj ; TW ; emp ; ⌜_⌝ ; _•ᵗ_ ; tx)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind ; kpp ; krot ; kki ; blkOf)
import Examples.Groups.Clifford+CS.Five.Sem.PGad m as PG

private
  _≈ᴾ_ : Word (GenP N) → Word (GenP N) → Set
  _≈ᴾ_ = PB._≈_ (N R,_===_)

  rc : ∀ {a b : Fin N} → .(a < b) → a < b
  rc {a} {b} p = recompute (a <? b) p

------------------------------------------------------------------------
-- Gadgets

record Gd : Set where
  constructor gd
  field
    kind : Kind
    i j  : Fin N

open Gd public

-- The hybrid's block on (p , q) is the letter ki q p q, for q < p.
kd : Fin N → Fin N → Word (GenP N)
kd p q with <-cmp q p
... | tri< lt _ _ = [ ki q p q lt ]ʷ
... | tri≈ _ _ _  = ε
... | tri> _ _ _  = ε

-- The gadget as a word over P′.
gw : Gd → Word (GenP N)
gw (gd kpp a b)  = [ pp a b ]ʷ
gw (gd krot a b) = xd a a b
gw (gd kki a b)  = kd a b

∏ : List Gd → Word (GenP N)
∏ []      = ε
∏ (g ∷ L) = gw g • ∏ L

-- Gadgets on two distinct indices, the hybrid's in decreasing order.
Valid : Gd → Set
Valid (gd kpp a b)  = a ≢ b
Valid (gd krot a b) = a ≢ b
Valid (gd kki a b)  = b < a

------------------------------------------------------------------------
-- The decomposition of a letter

ppL : (a b : Fin N) → Dec (a ≡ b) → List Gd
ppL a b (yes _) = []
ppL a b (no _)  = gd kpp a b ∷ []

pxL : (c a b : Fin N) → Dec (c ≡ a) → Dec (c ≡ b) → List Gd
pxL c a b (yes _) _       = gd krot a b ∷ []
pxL c a b (no _)  (yes _) = gd krot b a ∷ []
pxL c a b (no _)  (no _)  = gd krot c a ∷ gd krot c a ∷ gd krot a b ∷ []

kiL : (a b s : Fin N) → Dec (s ≡ a) → List Gd
kiL a b s (yes _) = gd kki b a ∷ []
kiL a b s (no _)  = gd kki b a ∷ gd kpp a s ∷ []

gl : GenP N → List Gd
gl (pp a b)          = ppL a b (a ≟ b)
gl (px c a b _)      = pxL c a b (c ≟ a) (c ≟ b)
gl (dx a b c d _ _)  = gd krot a b ∷ pxL b c d (b ≟ c) (b ≟ d)
gl (ki a b s _)      = kiL a b s (s ≟ a)

GL : Word (GenP N) → List Gd
GL [ x ]ʷ  = gl x
GL ε       = []
GL (u • v) = GL u ++ GL v

------------------------------------------------------------------------
-- The spellings of the wrappers

xd-lt : ∀ c a b (lt : a < b) → xd c a b ≡ [ px c a b lt ]ʷ
xd-lt c a b lt with <-cmp a b
... | tri< _ _ _  = refl
... | tri≈ _ e _  = ⊥-elim (<⇒≢ lt e)
... | tri> _ _ gt = ⊥-elim (<-asym lt gt)

xd-gt : ∀ c a b (lt : a < b) → xd c b a ≡ [ px c a b lt ]ʷ
xd-gt c a b lt with <-cmp b a
... | tri< gt _ _ = ⊥-elim (<-asym lt gt)
... | tri≈ _ e _  = ⊥-elim (<⇒≢ lt (Eq.sym e))
... | tri> _ _ _  = refl

kd-lt : ∀ p q (lt : q < p) → kd p q ≡ [ ki q p q lt ]ʷ
kd-lt p q lt with <-cmp q p
... | tri< _ _ _  = refl
... | tri≈ _ e _  = ⊥-elim (<⇒≢ lt e)
... | tri> _ _ gt = ⊥-elim (<-asym lt gt)

------------------------------------------------------------------------
-- The decomposition as a derivation

private
  ≡⇒≈ : ∀ {u v : Word (GenP N)} → u ≡ v → u ≈ᴾ v
  ≡⇒≈ refl = PB.refl

  unit : ∀ (w : Word (GenP N)) → w ≈ᴾ (w • ε)
  unit w = PB.sym PB.right-unit

  -- (−1)_[c] X_[a,b] with c off the pair: XZ on (c , a) twice, then on (a , b).
  far : ∀ c a b (ab : a < b) → c ≢ a → c ≢ b →
        [ px c a b ab ]ʷ ≈ᴾ (xd c c a • (xd c c a • (xd a a b • ε)))
  far c a b ab ca cb =
    PB.trans (≡⇒≈ (Eq.sym (xd-lt c a b ab))) (PB.sym (free⇒full-≈ (A.A5-tmpl w w′ refl)))
    where
    dist : Distinct (c ∷ a ∷ b ∷ [])
    dist = ((λ e → ca (Eq.sym e)) ∷ᵛ ((λ e → cb (Eq.sym e)) ∷ᵛ []ᵛ))
           ∷ᵈ (((λ e → <⇒≢ ab (Eq.sym e)) ∷ᵛ []ᵛ) ∷ᵈ ([]ᵛ ∷ᵈ []ᵈ))

    module A = At (lookup (c ∷ a ∷ b ∷ [])) (lookup-inj dist)

    w w′ : TW 3
    w  = ⌜ tx zero zero (suc zero) ⌝ •ᵗ (⌜ tx zero zero (suc zero) ⌝ •ᵗ
           (⌜ tx (suc zero) (suc zero) (suc (suc zero)) ⌝ •ᵗ emp))
    w′ = ⌜ tx zero (suc zero) (suc (suc zero)) ⌝

  decpp : ∀ a b (d : Dec (a ≡ b)) → [ pp a b ]ʷ ≈ᴾ ∏ (ppL a b d)
  decpp a .a (yes refl) = PB.axiom (pp-id a)
  decpp a b  (no _)     = unit _

  decpx : ∀ c a b (ab : a < b) (d₁ : Dec (c ≡ a)) (d₂ : Dec (c ≡ b)) → [ px c a b ab ]ʷ ≈ᴾ ∏ (pxL c a b d₁ d₂)
  decpx c .c b ab (yes refl) _       = PB.trans (≡⇒≈ (Eq.sym (xd-lt c c b ab))) (unit _)
  decpx c a .c ab (no _)     (yes refl) = PB.trans (≡⇒≈ (Eq.sym (xd-gt c a c ab))) (unit _)
  decpx c a b ab  (no ca)    (no cb)    = far c a b ab ca cb

  decki : ∀ a b s (ab : a < b) (d : Dec (s ≡ a)) → [ ki a b s ab ]ʷ ≈ᴾ ∏ (kiL a b s d)
  decki a b .a ab (yes refl) = PB.trans (≡⇒≈ (Eq.sym (kd-lt b a ab))) (unit _)
  decki a b s  ab (no _)     =
    PB.trans (PB.sym (PB.axiom (ki-sink a b a s ab)))
      (PB.cong (≡⇒≈ (Eq.sym (kd-lt b a ab))) (unit _))

dec : ∀ x → [ x ]ʷ ≈ᴾ ∏ (gl x)
dec (pp a b)            = decpp a b (a ≟ b)
dec (px c a b ab)       = decpx c a b (rc ab) (c ≟ a) (c ≟ b)
dec (dx a b c d ab cd)  =
  PB.trans (PB.axiom (dx-split a b c d ab cd))
    (PB.cong (≡⇒≈ (Eq.sym (xd-lt a a b (rc ab)))) (decpx b c d (rc cd) (b ≟ c) (b ≟ d)))
dec (ki a b s ab)       = decki a b s (rc ab) (s ≟ a)

private
  ∏-++ : ∀ L L′ → ∏ (L ++ L′) ≈ᴾ (∏ L • ∏ L′)
  ∏-++ []      L′ = PB.sym PB.left-unit
  ∏-++ (g ∷ L) L′ = PB.trans (PB.cong PB.refl (∏-++ L L′)) (PB.sym PB.assoc)

dec-w : ∀ u → u ≈ᴾ ∏ (GL u)
dec-w [ x ]ʷ  = dec x
dec-w ε       = PB.refl
dec-w (u • v) = PB.trans (PB.cong (dec-w u) (dec-w v)) (PB.sym (∏-++ (GL u) (GL v)))

------------------------------------------------------------------------
-- The gadgets are valid

private
  vpp : ∀ a b (d : Dec (a ≡ b)) → All Valid (ppL a b d)
  vpp a b (yes _) = []
  vpp a b (no ne) = ne ∷ []

  vpx : ∀ c a b (ab : a < b) (d₁ : Dec (c ≡ a)) (d₂ : Dec (c ≡ b)) → All Valid (pxL c a b d₁ d₂)
  vpx c a b ab (yes _)  _        = <⇒≢ ab ∷ []
  vpx c a b ab (no _)   (yes _)  = (λ e → <⇒≢ ab (Eq.sym e)) ∷ []
  vpx c a b ab (no ca)  (no cb)  = ca ∷ ca ∷ <⇒≢ ab ∷ []

  vki : ∀ a b s (ab : a < b) (d : Dec (s ≡ a)) → All Valid (kiL a b s d)
  vki a b s ab (yes _) = ab ∷ []
  vki a b s ab (no ne) = ab ∷ (λ e → ne (Eq.sym e)) ∷ []

valid : ∀ x → All Valid (gl x)
valid (pp a b)           = vpp a b (a ≟ b)
valid (px c a b ab)      = vpx c a b (rc ab) (c ≟ a) (c ≟ b)
valid (dx a b c d ab cd) = <⇒≢ (rc ab) ∷ vpx b c d (rc cd) (b ≟ c) (b ≟ d)
valid (ki a b s ab)      = vki a b s (rc ab) (s ≟ a)

valid-GL : ∀ u → All Valid (GL u)
valid-GL [ x ]ʷ  = valid x
valid-GL ε       = []
valid-GL (u • v) = ++⁺ (valid-GL u) (valid-GL v)

------------------------------------------------------------------------
-- The reading

-- The product of the gadgets' two-level operators.
Π : List Gd → Scaled n
Π []      = ε∙
Π (g ∷ L) = tl (blkOf (kind g)) (cod (i g)) (cod (j g)) ∙ Π L

private
  T : Gd → Scaled n
  T g = tl (blkOf (kind g)) (cod (i g)) (cod (j g))

  rot-sem : ∀ a b → a ≢ b → ⟦ xd a a b ⟧PY ~ T (gd krot a b)
  rot-sem a b ne with <-cmp a b
  ... | tri< lt _ _ =
    Eq.subst₂ (λ x y → .(lt : x < y) → ⟦ px x x y lt ⟧ᴾ ~ T (gd krot a b)) (idx-cod a) (idx-cod b)
      (PG.Rot.rot<-tl (cod a) (cod b) (λ e → ne (cod-inj e))) lt
  ... | tri≈ _ e _  = ⊥-elim (ne e)
  ... | tri> _ _ gt =
    Eq.subst₂ (λ x y → .(gt : y < x) → ⟦ px x y x gt ⟧ᴾ ~ T (gd krot a b)) (idx-cod a) (idx-cod b)
      (PG.Rot.rot>-tl (cod a) (cod b) (λ e → ne (cod-inj e))) gt

  ki-sem : ∀ a b → b < a → ⟦ kd a b ⟧PY ~ T (gd kki a b)
  ki-sem a b lt =
    Eq.subst (λ w → ⟦ w ⟧PY ~ T (gd kki a b)) (Eq.sym (kd-lt a b lt))
      (Eq.subst₂ (λ x y → .(lt : y < x) → ⟦ ki y x y lt ⟧ᴾ ~ T (gd kki a b)) (idx-cod a) (idx-cod b)
        (PG.Ki.ki-tl (cod a) (cod b) (λ e → <⇒≢ lt (cod-inj (Eq.sym e)))) lt)

gw-sem : ∀ g → Valid g → ⟦ gw g ⟧PY ~ T g
gw-sem (gd kpp a b)  ne =
  Eq.subst₂ (λ x y → ⟦ pp x y ⟧ᴾ ~ T (gd kpp a b)) (idx-cod a) (idx-cod b)
    (PG.PP.pp-tl (cod a) (cod b) (λ e → ne (cod-inj e)))
gw-sem (gd krot a b) ne = rot-sem a b ne
gw-sem (gd kki a b)  lt = ki-sem a b lt

sem-∏ : ∀ L → All Valid L → ⟦ ∏ L ⟧PY ~ Π L
sem-∏ []      []       = ~-refl ε∙
sem-∏ (g ∷ L) (v ∷ vs) =
  ∙-cong {s = ⟦ gw g ⟧PY} {s' = T g} {t = ⟦ ∏ L ⟧PY} {t' = Π L} (gw-sem g v) (sem-∏ L vs)

-- The rules of P′ are sound for the reading.
sound : ∀ {u t : Word (GenP N)} → u ≈ᴾ t → ⟦ u ⟧PY ~ ⟦ t ⟧PY
sound {u} {t} e =
  ~-trans {s = ⟦ u ⟧PY} {t = ⟦ (asG ʷ) u ⟧Y} {u = ⟦ t ⟧PY} (PY-asG u)
    (~-trans {s = ⟦ (asG ʷ) u ⟧Y} {t = ⟦ (asG ʷ) t ⟧Y} {u = ⟦ t ⟧PY} (sound-Y (Sound.sound e))
      (~-sym {s = ⟦ t ⟧PY} {t = ⟦ (asG ʷ) t ⟧Y} (PY-asG t)))

sem-w : ∀ u → ⟦ u ⟧PY ~ Π (GL u)
sem-w u = ~-trans {s = ⟦ u ⟧PY} {t = ⟦ ∏ (GL u) ⟧PY} {u = Π (GL u)}
            (sound (dec-w u)) (sem-∏ (GL u) (valid-GL u))
