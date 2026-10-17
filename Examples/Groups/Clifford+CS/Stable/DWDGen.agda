------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 at every width from five wires on
--
-- Five.Decode (generic in the width) decodes a word u of P′ as a list
-- of gadgets `GL u` and reads it as the product `Π` of their two-level
-- operators (`sem-w`).  Read at the Gray codes, that list is a decoded
-- word (`dec`), and when its gadgets' indices lie among at most five
-- indices it is `inst` of an index word over them (`iw`, `inst-iw`).
-- So two words whose products agree — the two sides of a rule of P′, by
-- Five.Decode.sound (`from-rule`) — decode to equal circuits on 5 + m
-- wires given completeness on 4 + m (`engine`): their decoded words
-- denote those products (GadgetFacts.D-sem, `Π-tl`), and HyperCanon.
-- lemma-sem does the rest.  A letter's gadgets are on its own indices
-- (`gl-in`) and every rule of P′ has at most five (`cover`, the
-- memberships found by instance search), so the decoding of letters
-- `dl`, extended to words (`dec-ʷ`), respects every rule of P′: `dwd`,
-- Lemma 8.8 on 5 + m wires from completeness on 4 + m.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)

module Examples.Groups.Clifford+CS.Stable.DWDGen
  (c4 : Complete 4) (c₅ : Completeᵧ 5)
  (f4 : ∀ m → F4ᵗ m) (f5 : ∀ m → F5ᵗ m)
  (tr : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (F : Facts4)
  where

open import Data.Fin using (Fin) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Properties using (<⇒≢ ; _≟_)
open import Data.List using (List ; [] ; _∷_ ; map ; _++_)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat using (_≤_ ; z≤n ; s≤s)
open import Data.Product using (Σ ; _×_ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup) renaming (map to vmap)
open import Data.Vec.Properties using (lookup-map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics using (_~_ ; _∙_ ; ~-trans ; ~-sym)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; ki)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind ; kpp ; krot ; kki ; blkOf)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl)
open import Examples.Groups.Clifford+CS.Stable.GadgetFacts c4 c₅ f4 f5 tr F
  using (IW ; inst ; NeW ; lemma-sem ; Lit ; D ; Ne ; Πtl ; D-sem)
import Examples.Groups.Clifford+CS.Five.Decode as Decode
import Examples.Groups.Clifford+CS.Encoding as Encoding
import Examples.Groups.Clifford+CS.BridgeGray as BridgeGray

module _ (m : ℕ) where
  private
    module Dc = Decode (suc m)
  open Dc using (Gd ; gd ; kind ; i ; j ; gl ; GL ; Π ; Valid ; valid-GL ; sem-w ; ppL ; pxL ; kiL)
  open Encoding (suc m) using (N ; cod ; cod-inj)
  private
    module BG = BridgeGray (₄₊ (suc m))

  -- A gadget at the Gray codes of its indices.
  toLit : Gd → Lit (suc m)
  toLit g = kind g , cod (i g) , cod (j g)

  -- The decoding of a word over P′ on 5 + m wires.
  dec : Word (GenP N) → Circuit (₄₊ (suc m))
  dec u = D (suc m) (map toLit (GL u))

  private
    Π-tl : ∀ (L : List Gd) → Πtl (map toLit L) ≡ Π L
    Π-tl []      = Eq.refl
    Π-tl (g ∷ L) = Eq.cong (tl (blkOf (kind g)) (cod (i g)) (cod (j g)) ∙_) (Π-tl L)

    valid≢ : ∀ (g : Gd) → Valid g → i g ≢ j g
    valid≢ (gd kpp a b)  ne = ne
    valid≢ (gd krot a b) ne = ne
    valid≢ (gd kki a b)  lt = λ e → <⇒≢ lt (Eq.sym e)

    ne-lit : ∀ (L : List Gd) → All Valid L → Ne (map toLit L)
    ne-lit []      []       = []
    ne-lit (g ∷ L) (v ∷ vs) = (λ e → valid≢ g v (cod-inj e)) ∷ ne-lit L vs

  -- An index in a vector of indices, found by instance search.
  record In {k} (ix : Vec (Fin N) k) (a : Fin N) : Set where
    constructor at
    field
      pos    : Fin k
      pos-ok : lookup ix pos ≡ a

  record Both (A B : Set) : Set where
    constructor both
    field
      fst : A
      snd : B

  instance
    in-here : ∀ {k} {ix : Vec (Fin N) k} {a} → In (a ∷ ix) a
    in-here = at 0F Eq.refl

    in-there : ∀ {k} {ix : Vec (Fin N) k} {a b} → {{In ix a}} → In (b ∷ ix) a
    in-there {{at p e}} = at (sF p) e
    {-# OVERLAPPABLE in-there #-}

    both-i : ∀ {A B : Set} → {{A}} → {{B}} → Both A B
    both-i {{a}} {{b}} = both a b

    tt-i : ⊤
    tt-i = tt

  -- The gadgets' indices lie in a vector of indices.
  AllIn : ∀ {k} → Vec (Fin N) k → List Gd → Set
  AllIn ix = All (λ g → In ix (i g) × In ix (j g))

  -- A letter's indices, and a word's, lie in it.
  LIn : ∀ {k} → Vec (Fin N) k → GenP N → Set
  LIn ix (pp a b)         = Both (In ix a) (In ix b)
  LIn ix (px c a b _)     = Both (In ix c) (Both (In ix a) (In ix b))
  LIn ix (dx a b c d _ _) = Both (In ix a) (Both (In ix b) (Both (In ix c) (In ix d)))
  LIn ix (ki a b s _)     = Both (In ix a) (Both (In ix b) (In ix s))

  WIn : ∀ {k} → Vec (Fin N) k → Word (GenP N) → Set
  WIn ix [ x ]ʷ   = LIn ix x
  WIn ix ε       = ⊤
  WIn ix (u • v) = Both (WIn ix u) (WIn ix v)

  -- A letter's gadgets are on its own indices.
  gl-in : ∀ {k} (ix : Vec (Fin N) k) (x : GenP N) → LIn ix x → AllIn ix (gl x)
  gl-in ix (pp a b)         (both ha hb)                       = ppL-in (a ≟ b)
    where
    ppL-in : ∀ d → AllIn ix (ppL a b d)
    ppL-in (yes _) = []
    ppL-in (no _)  = (ha , hb) ∷ []
  gl-in ix (px c a b _)     (both hc (both ha hb))             = pxL-in (c ≟ a) (c ≟ b)
    where
    pxL-in : ∀ d₁ d₂ → AllIn ix (pxL c a b d₁ d₂)
    pxL-in (yes _) _       = (ha , hb) ∷ []
    pxL-in (no _)  (yes _) = (hb , ha) ∷ []
    pxL-in (no _)  (no _)  = (hc , ha) ∷ (hc , ha) ∷ (ha , hb) ∷ []
  gl-in ix (dx a b c d _ _) (both ha (both hb (both hc hd))) = (ha , hb) ∷ pxL-in (b ≟ c) (b ≟ d)
    where
    pxL-in : ∀ d₁ d₂ → AllIn ix (pxL b c d d₁ d₂)
    pxL-in (yes _) _       = (hc , hd) ∷ []
    pxL-in (no _)  (yes _) = (hd , hc) ∷ []
    pxL-in (no _)  (no _)  = (hb , hc) ∷ (hb , hc) ∷ (hc , hd) ∷ []
  gl-in ix (ki a b s _)     (both ha (both hb hs))             = kiL-in (s ≟ a)
    where
    kiL-in : ∀ d → AllIn ix (kiL a b s d)
    kiL-in (yes _) = (hb , ha) ∷ []
    kiL-in (no _)  = (hb , ha) ∷ (ha , hs) ∷ []

  GL-in : ∀ {k} (ix : Vec (Fin N) k) (u : Word (GenP N)) → WIn ix u → AllIn ix (GL u)
  GL-in ix [ x ]ʷ   h            = gl-in ix x h
  GL-in ix ε       h            = []
  GL-in ix (u • v) (both hu hv) = ++⁺ (GL-in ix u hu) (GL-in ix v hv)

  -- The index word of such a list.
  iw : ∀ {k} (ix : Vec (Fin N) k) (L : List Gd) → AllIn ix L → IW k
  iw ix []      []             = []
  iw ix (g ∷ L) ((a , b) ∷ h) = (kind g , In.pos a , In.pos b) ∷ iw ix L h

  private
    at′ : ∀ {k} (ix : Vec (Fin N) k) {a} (h : In ix a) → lookup (vmap cod ix) (In.pos h) ≡ cod a
    at′ ix (at k e) = Eq.trans (lookup-map k cod ix) (Eq.cong cod e)

  inst-iw : ∀ {k} (ix : Vec (Fin N) k) (L : List Gd) (h : AllIn ix L) → inst (vmap cod ix) (iw ix L h) ≡ map toLit L
  inst-iw ix []      []             = Eq.refl
  inst-iw ix (g ∷ L) ((a , b) ∷ h) =
    Eq.cong₂ _∷_ (Eq.cong₂ (λ x y → kind g , x , y) (at′ ix a) (at′ ix b)) (inst-iw ix L h)

  private
    ne-iw : ∀ {k} (ix : Vec (Fin N) k) (L : List Gd) (h : AllIn ix L) → All Valid L → NeW (vmap cod ix) (iw ix L h)
    ne-iw ix []      []             []       = []
    ne-iw ix (g ∷ L) ((a , b) ∷ h) (v ∷ vs) =
      (λ e → valid≢ g v (cod-inj (Eq.trans (Eq.sym (at′ ix a)) (Eq.trans e (at′ ix b))))) ∷ ne-iw ix L h vs

  -- Equal products give equal decodings, given completeness one width
  -- down.
  engine : Completeᵧ (₄₊ m) → ∀ {k} (u t : Word (GenP N)) (ix : Vec (Fin N) (suc k)) → k ≤ 4 →
           AllIn ix (GL u) → AllIn ix (GL t) → Π (GL u) ~ Π (GL t) →
           (₄₊ (suc m)) ⊢ᵧ dec u ≈ dec t
  engine c u t ix k≤ hu ht s =
    Eq.subst₂ (λ a b → (₄₊ (suc m)) ⊢ᵧ D (suc m) a ≈ D (suc m) b) (inst-iw ix (GL u) hu) (inst-iw ix (GL t) ht)
      (lemma-sem m c (iw ix (GL u) hu) (iw ix (GL t) ht) (vmap cod ix) k≤
         (ne-iw ix (GL u) hu (valid-GL u)) (ne-iw ix (GL t) ht (valid-GL t))
         (Eq.subst₂ (λ a b → ⟦ D (suc m) a ⟧ ~ ⟦ D (suc m) b ⟧)
                    (Eq.sym (inst-iw ix (GL u) hu)) (Eq.sym (inst-iw ix (GL t) ht)) sem))
    where
    Lu = map toLit (GL u)
    Lt = map toLit (GL t)
    sem : ⟦ D (suc m) Lu ⟧ ~ ⟦ D (suc m) Lt ⟧
    sem =
      ~-trans {s = ⟦ D (suc m) Lu ⟧} {Π (GL u)} {⟦ D (suc m) Lt ⟧}
        (Eq.subst (λ x → ⟦ D (suc m) Lu ⟧ ~ x) (Π-tl (GL u)) (D-sem (suc m) Lu (ne-lit (GL u) (valid-GL u))))
        (~-trans {s = Π (GL u)} {Π (GL t)} {⟦ D (suc m) Lt ⟧} s
          (~-sym {s = ⟦ D (suc m) Lt ⟧} {Π (GL t)}
            (Eq.subst (λ x → ⟦ D (suc m) Lt ⟧ ~ x) (Π-tl (GL t)) (D-sem (suc m) Lt (ne-lit (GL t) (valid-GL t))))))

  -- The two sides of a derivation in P′ have the same product.
  from-rule : ∀ {u t : Word (GenP N)} → PB._≈_ (N R,_===_) u t → Π (GL u) ~ Π (GL t)
  from-rule {u} {t} e =
    ~-trans {s = Π (GL u)} {BG.⟦ u ⟧PY} {Π (GL t)} (~-sym {s = BG.⟦ u ⟧PY} {Π (GL u)} (sem-w u))
      (~-trans {s = BG.⟦ u ⟧PY} {BG.⟦ t ⟧PY} {Π (GL t)} (Dc.sound e) (sem-w t))

  -- The decoding of a letter, and its extension to words.
  private
    D-++ : ∀ (ℓ₁ ℓ₂ : List (Lit (suc m))) → (₄₊ (suc m)) ⊢ᵧ D (suc m) (ℓ₁ ++ ℓ₂) ≈ D (suc m) ℓ₁ • D (suc m) ℓ₂
    D-++ []                ℓ₂ = PB.sym PB.left-unit
    D-++ ((κ , p , q) ∷ ℓ₁) ℓ₂ = PB.trans (PB.cong PB.refl (D-++ ℓ₁ ℓ₂)) (PB.sym PB.assoc)

  dl : GenP N → Circuit (₄₊ (suc m))
  dl x = dec [ x ]ʷ

  dec-ʷ : ∀ (u : Word (GenP N)) → (₄₊ (suc m)) ⊢ᵧ (dl ʷ) u ≈ dec u
  dec-ʷ [ x ]ʷ   = PB.refl
  dec-ʷ ε       = PB.refl
  dec-ʷ (u • v) =
    PB.trans (PB.cong (dec-ʷ u) (dec-ʷ v))
      (PB.sym (Eq.subst (λ L → (₄₊ (suc m)) ⊢ᵧ D (suc m) L ≈ dec u • dec v)
                        (Eq.sym (map-++ toLit (GL u) (GL v)))
                        (D-++ (map toLit (GL u)) (map toLit (GL v)))))

  -- Every rule of P′ is on at most five indices.
  record Cov (u t : Word (GenP N)) : Set where
    constructor cov
    field
      {k} : ℕ
      ix  : Vec (Fin N) (suc k)
      k≤  : k ≤ 4
      hu  : WIn ix u
      ht  : WIn ix t

  private
    k1 : ∀ {u t} (a : Fin N) → {{WIn (a ∷ []) u}} → {{WIn (a ∷ []) t}} → Cov u t
    k1 a {{hu}} {{ht}} = cov (a ∷ []) z≤n hu ht

    k2 : ∀ {u t} (a b : Fin N) → {{WIn (a ∷ b ∷ []) u}} → {{WIn (a ∷ b ∷ []) t}} → Cov u t
    k2 a b {{hu}} {{ht}} = cov (a ∷ b ∷ []) (s≤s z≤n) hu ht

    k3 : ∀ {u t} (a b c : Fin N) → {{WIn (a ∷ b ∷ c ∷ []) u}} → {{WIn (a ∷ b ∷ c ∷ []) t}} → Cov u t
    k3 a b c {{hu}} {{ht}} = cov (a ∷ b ∷ c ∷ []) (s≤s (s≤s z≤n)) hu ht

    k4 : ∀ {u t} (a b c d : Fin N) → {{WIn (a ∷ b ∷ c ∷ d ∷ []) u}} → {{WIn (a ∷ b ∷ c ∷ d ∷ []) t}} →
         Cov u t
    k4 a b c d {{hu}} {{ht}} = cov (a ∷ b ∷ c ∷ d ∷ []) (s≤s (s≤s (s≤s z≤n))) hu ht

    k5 : ∀ {u t} (a b c d e : Fin N) → {{WIn (a ∷ b ∷ c ∷ d ∷ e ∷ []) u}} →
         {{WIn (a ∷ b ∷ c ∷ d ∷ e ∷ []) t}} → Cov u t
    k5 a b c d e {{hu}} {{ht}} = cov (a ∷ b ∷ c ∷ d ∷ e ∷ []) (s≤s (s≤s (s≤s (s≤s z≤n)))) hu ht

  cover : ∀ {u t : Word (GenP N)} → N R, u === t → Cov u t
  cover (pp-id a)                                 = k1 a
  cover (pp-ord a b)                              = k2 a b
  cover (pp-comm a b c d)                         = k4 a b c d
  cover (pp-tele a b c)                           = k3 a b c
  cover (px-sq a a′ _)                            = k2 a a′
  cover (px-braid a a′ a″ _ _)                    = k3 a a′ a″
  cover (px-shrink₁ a a′ c _ _)                   = k3 a a′ c
  cover (px-shrink₂ a a′ c _ _)                   = k3 a a′ c
  cover (px-shrink₃ a c′ c _ _)                   = k3 a c′ c
  cover (px-shrink₄ a c′ c _ _)                   = k3 a c′ c
  cover (px-inv a a′ _)                           = k2 a a′
  cover (px-sign c a b _)                         = k3 c a b
  cover (px-conj a a′ c _ _ _)                    = k3 a a′ c
  cover (px-conj₂ a a′ _)                         = k2 a a′
  cover (px-comm a a′ b b′ _ _ _)                 = k4 a a′ b b′
  cover (dx-split a b c d _ _)                    = k4 a b c d
  cover (ki-sink a b s t _)                       = k4 a b s t
  cover (ki-pp a b s x _ _ _ _ _)                 = k4 a b s x
  cover (ki-px a b s x y _ _ _ _ _ _ _ _ _ _)     = k5 a b s x y
  cover (ki-ki a b c d s _ _ _ _ _ _ _ _ _ _)     = k5 a b c d s
  cover (ki-swap j k l s _ _ _ _ _)               = k4 j k l s
  cover (ki-swap′ j k l s _ _ _ _ _)              = k4 j k l s
  cover (ki-x a b s _ _ _)                        = k3 a b s
  cover (ki-16 a b s _ _ _)                       = k3 a b s
  cover (ki-ii a b s _ _ _)                       = k3 a b s
  cover (ki-sq a b s _ _ _)                       = k3 a b s
  cover (ki-yb j k l m′ s _ _ _ _ _ _ _ _ _)      = k5 j k l m′ s

  -- Lemma 8.8 on 5 + m wires: the decoding respects every rule of P′,
  -- given completeness on 4 + m.
  dwd : Completeᵧ (₄₊ m) → ∀ {u t : Word (GenP N)} → N R, u === t → (₄₊ (suc m)) ⊢ᵧ (dl ʷ) u ≈ (dl ʷ) t
  dwd c {u} {t} r = go (cover r)
    where
    go : Cov u t → (₄₊ (suc m)) ⊢ᵧ (dl ʷ) u ≈ (dl ʷ) t
    go (cov ix k≤ hu ht) =
      PB.trans (dec-ʷ u)
        (PB.trans (engine c u t ix k≤ (GL-in ix u hu) (GL-in ix t ht) (from-rule (PB.axiom r)))
                  (PB.sym (dec-ʷ t)))
