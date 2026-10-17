------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 for words of P′ whose gadgets lie on few indices
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
-- lemma-sem does the rest.
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
open import Data.Fin.Properties using (<⇒≢)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Nat using (_≤_)
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; lookup) renaming (map to vmap)
open import Data.Vec.Properties using (lookup-map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics using (_~_ ; _∙_ ; ~-trans ; ~-sym)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (_R,_===_)
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
  open Dc using (Gd ; gd ; kind ; i ; j ; GL ; Π ; Valid ; valid-GL ; sem-w)
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

  -- The gadgets' indices lie in a vector of indices.
  In : ∀ {k} → Vec (Fin N) k → Fin N → Set
  In ix a = Σ (Fin _) λ k → lookup ix k ≡ a

  AllIn : ∀ {k} → Vec (Fin N) k → List Gd → Set
  AllIn ix = All (λ g → In ix (i g) × In ix (j g))

  -- The index word of such a list.
  iw : ∀ {k} (ix : Vec (Fin N) k) (L : List Gd) → AllIn ix L → IW k
  iw ix []      []             = []
  iw ix (g ∷ L) ((a , b) ∷ h) = (kind g , proj₁ a , proj₁ b) ∷ iw ix L h

  private
    at : ∀ {k} (ix : Vec (Fin N) k) {a} (h : In ix a) → lookup (vmap cod ix) (proj₁ h) ≡ cod a
    at ix (k , e) = Eq.trans (lookup-map k cod ix) (Eq.cong cod e)

  inst-iw : ∀ {k} (ix : Vec (Fin N) k) (L : List Gd) (h : AllIn ix L) → inst (vmap cod ix) (iw ix L h) ≡ map toLit L
  inst-iw ix []      []             = Eq.refl
  inst-iw ix (g ∷ L) ((a , b) ∷ h) =
    Eq.cong₂ _∷_ (Eq.cong₂ (λ x y → kind g , x , y) (at ix a) (at ix b)) (inst-iw ix L h)

  private
    ne-iw : ∀ {k} (ix : Vec (Fin N) k) (L : List Gd) (h : AllIn ix L) → All Valid L → NeW (vmap cod ix) (iw ix L h)
    ne-iw ix []      []             []       = []
    ne-iw ix (g ∷ L) ((a , b) ∷ h) (v ∷ vs) =
      (λ e → valid≢ g v (cod-inj (Eq.trans (Eq.sym (at ix a)) (Eq.trans e (at ix b))))) ∷ ne-iw ix L h vs

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
