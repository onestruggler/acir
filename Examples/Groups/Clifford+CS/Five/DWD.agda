------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding respects the rules of P′, on five wires
--
-- The analogue of Lemma 8.8 at n = 5, by the hyperplane argument.  A rule
-- u === t of P′ has at most five indices; read as five-bit vectors they
-- lie on an affine hyperplane c · x = κ (Five.Sem.Hyper), and the affine
-- circuit β = βc c κ sends it into the half where wire 4 reads 0.  Then
-- conjugating the decoded sides by β gives λ⁰ of four-wire products W_u,
-- W_t (Five.Dec5.red-D), and those have the same semantics: the rule is
-- sound for P′'s reading, which is the product of the gadgets' two-level
-- operators (Five.Decode.sem-w), and conjugating by β and dropping wire
-- 4 keeps them equal (Five.Sem.Core.core).  Completeness on four wires
-- and the transport of λ⁰ finish (`dwd`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Primality using (prime[2])
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Word.Base using (_•_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Inputs using (Inputs)
open import Examples.Groups.Clifford+CS.Five.Rules using (_⊢ₓ_≈_)
open import Examples.Groups.Clifford+CS.Five.Affine using (τ)
open import Examples.Groups.Clifford+CS.Five.Stab using (e₀)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)
import Examples.Groups.Clifford+CS.Five.Calc as Calc
import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0 as B
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan 0 prime[2] 0 using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Completeness.Aff 0 prime[2] using (adm)
open import Examples.Groups.Qupit-Phase-Affine.Evaluation 0 prime[2] 0 adm using (fn)
open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (_⁻¹)

module Examples.Groups.Clifford+CS.Five.DWD
  (I : Inputs)
  (F : Facts4)
  (c4 : Complete 4)
  (cind : (V : Kind) (α β : B.Circuit 5) → fn α 0ᵛ ≡ fn β 0ᵛ → fn α e₀ ≡ fn β e₀ →
          5 ⊢ₓ τ α • Calc.Λ⁰ (Inputs.F4ᵍ I) (Inputs.F5ᵍ I) (Inputs.x4x4 I) (Facts4.G F V) • τ (α ⁻¹)
             ≈ τ β • Calc.Λ⁰ (Inputs.F4ᵍ I) (Inputs.F5ᵍ I) (Inputs.x4x4 I) (Facts4.G F V) • τ (β ⁻¹))
  where

open import Data.Bool using (Bool ; true ; false ; _xor_)
import Data.Bool.Properties as BoolP
open import Data.Fin using (Fin ; zero ; suc)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (Vec ; lookup) renaming ([] to []ᵥ ; _∷_ to _∷ᵥ_ ; _++_ to _++ᵥ_ ; map to mapᵥ)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_ ; _≟_)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ₒ ; ⟦⟧ₒ-ε)
open import Examples.Groups.Clifford+CS.Five.Rules using (embed)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Affine using (aff⇒)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl) renaming (F to F⁰)
open import Examples.Groups.Clifford+CS.Five.Sem.Aff using (bm ; bm-inv ; bm-inv′)
open import Examples.Groups.Clifford+CS.Five.Sem.Build using (α ; α-o ; α-e ; ze ; dot)
open import Examples.Groups.Clifford+CS.Five.Sem.Hyper using (Plane ; hyper ; βc ; β-top ; last)
open import Examples.Groups.Clifford+CS.Five.Sem.Core using (Pt ; Πp ; low ; top ; lows ; mapf ; OnHalf ; core)
open import Examples.Groups.Clifford+CS.Five.Sem.Gad4 (Facts4.G F) (Facts4.sem F) using (gad₄-sem)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (hom)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (blkOf ; kpp ; krot ; kki)
open import Examples.Groups.Clifford+CS.Encoding 1 using (N ; cod ; cod-inj)
open import Examples.Groups.Clifford+CS.BridgeGray 5 using (⟦_⟧PY)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; ki)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules
  using (_R,_===_ ; pp-id ; pp-ord ; pp-comm ; pp-tele ; px-sq ; px-braid ; px-shrink₁ ; px-shrink₂
       ; px-shrink₃ ; px-shrink₄ ; px-inv ; px-sign ; px-conj ; px-conj₂ ; px-comm ; dx-split ; ki-sink
       ; ki-pp ; ki-px ; ki-ki ; ki-swap ; ki-swap′ ; ki-x ; ki-16 ; ki-ii ; ki-sq ; ki-yb)
open import Examples.Groups.Clifford+CS.Five.Decode 1
  using (Gd ; gd ; kind ; i ; j ; gl ; GL ; Valid ; valid-GL ; Π ; sem-w ; sound)
open import Examples.Groups.Clifford+CS.Five.Dec5 I F cind
  using (d ; Dg ; Dg₄ ; g₄ ; pts ; Good ; lowsβ ; red-D ; dʷ-D)

open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (module Inv)
open import Data.Fin.Properties using (_≟_ ; <⇒≢)
open import Data.Vec.Properties using (lookup-map)
open import Relation.Nullary using (Dec ; yes ; no)
open import Examples.Groups.Clifford+CS.Five.Decode 1 using (ppL ; pxL ; kiL)

open Inputs I
open Facts4 F using (G)
open Calc F4ᵍ F5ᵍ x4x4 using (Λ⁰ ; transport⁰)

------------------------------------------------------------------------
-- The indices of a word

-- P holds of every index of a letter, of every letter of a word.
AllX : (Fin N → Set) → GenP N → Set
AllX P (pp a b)         = P a × P b
AllX P (px c a b _)     = P c × P a × P b
AllX P (dx a b c d _ _) = P a × P b × P c × P d
AllX P (ki a b s _)     = P a × P b × P s

AllI : (Fin N → Set) → Word (GenP N) → Set
AllI P [ x ]ʷ  = AllX P x
AllI P ε       = ⊤
AllI P (u • v) = AllI P u × AllI P v

-- The gadgets of a letter sit on its indices.
private
  Both : (Fin N → Set) → Gd → Set
  Both P g = P (i g) × P (j g)

  bpp : ∀ {P} a b (d : Dec (a ≡ b)) → P a → P b → All (Both P) (ppL a b d)
  bpp a b (yes _) pa pb = []
  bpp a b (no _)  pa pb = (pa , pb) ∷ []

  bpx : ∀ {P} c a b (d₁ : Dec (c ≡ a)) (d₂ : Dec (c ≡ b)) → P c → P a → P b → All (Both P) (pxL c a b d₁ d₂)
  bpx c a b (yes _) _       pc pa pb = (pa , pb) ∷ []
  bpx c a b (no _)  (yes _) pc pa pb = (pb , pa) ∷ []
  bpx c a b (no _)  (no _)  pc pa pb = (pc , pa) ∷ (pc , pa) ∷ (pa , pb) ∷ []

  bki : ∀ {P} a b s (d : Dec (s ≡ a)) → P a → P b → P s → All (Both P) (kiL a b s d)
  bki a b s (yes _) pa pb ps = (pb , pa) ∷ []
  bki a b s (no _)  pa pb ps = (pb , pa) ∷ (pa , ps) ∷ []

  ++⁺ : ∀ {Q : Gd → Set} {L L′} → All Q L → All Q L′ → All Q (Data.List._++_ L L′)
  ++⁺ []       h′ = h′
  ++⁺ (x ∷ h)  h′ = x ∷ ++⁺ h h′

on-gl : ∀ {P} x → AllX P x → All (Both P) (gl x)
on-gl (pp a b)           (pa , pb)            = bpp a b (a ≟ b) pa pb
on-gl (px c a b _)       (pc , pa , pb)       = bpx c a b (c ≟ a) (c ≟ b) pc pa pb
on-gl (dx a b c d _ _)   (pa , pb , pc , pd)  = (pa , pb) ∷ bpx b c d (b ≟ c) (b ≟ d) pb pc pd
on-gl (ki a b s _)       (pa , pb , ps)       = bki a b s (s ≟ a) pa pb ps

on-GL : ∀ {P} u → AllI P u → All (Both P) (GL u)
on-GL [ x ]ʷ  h         = on-gl x h
on-GL ε       h         = []
on-GL (u • v) (hu , hv) = ++⁺ (on-GL u hu) (on-GL v hv)

------------------------------------------------------------------------
-- One rule

module Gen (u t : Word (GenP N)) (ax : N R, u === t) (ix : Vec (Fin N) 5)
           (hu : ∀ (P : Fin N → Set) → (∀ k → P (lookup ix k)) → AllI P u)
           (ht : ∀ (P : Fin N → Set) → (∀ k → P (lookup ix k)) → AllI P t) where

  private
    v : Vec (Bits 5) 5
    v = mapᵥ cod ix

    pl : Plane v
    pl = hyper v

    c : Bits 5
    c = Plane.c pl

    κ : Bool
    κ = dot c (cod (lookup ix zero))

    OnP : Fin N → Set
    OnP a = dot c (cod a) ≡ κ

    onk : ∀ k → OnP (lookup ix k)
    onk k = Eq.trans (Eq.sym (Eq.cong (dot c) (lookup-map k cod ix)))
              (Eq.trans (Plane.on pl k) (Eq.cong (dot c) (lookup-map zero cod ix)))

    β : B.Circuit 5
    β = βc c κ

    f g : Bits 5 → Bits 5
    f = bm β
    g = bm (β ⁻¹)

    fg : ∀ x → f (g x) ≡ x
    fg = bm-inv′ β

    gf : ∀ x → g (f x) ≡ x
    gf = bm-inv β

    last-top : ∀ y → last y ≡ top y
    last-top (_ ∷ᵥ _ ∷ᵥ _ ∷ᵥ _ ∷ᵥ _ ∷ᵥ []ᵥ) = refl

    low-F : ∀ y → top y ≡ false → y ≡ low y ++ᵥ F⁰
    low-F (x₀ ∷ᵥ x₁ ∷ᵥ x₂ ∷ᵥ x₃ ∷ᵥ .false ∷ᵥ []ᵥ) refl = refl

    top-on : ∀ a → OnP a → top (f (cod a)) ≡ false
    top-on a h =
      Eq.trans (Eq.sym (last-top (f (cod a))))
        (Eq.trans (β-top c (Plane.nz pl) κ (cod a))
          (Eq.trans (Eq.cong (_xor κ) h) (BoolP.xor-same κ)))

    low-inj : ∀ p q → top (f p) ≡ false → top (f q) ≡ false → low (f p) ≡ low (f q) → p ≡ q
    low-inj p q tp tq e = Eq.trans (Eq.sym (gf p)) (Eq.trans (Eq.cong g fpq) (gf q))
      where
      fpq : f p ≡ f q
      fpq = Eq.trans (low-F (f p) tp) (Eq.trans (Eq.cong (_++ᵥ F⁰) e) (Eq.sym (low-F (f q) tq)))

    vne : ∀ G → Valid G → i G ≢ j G
    vne (gd kpp a b)  ne = ne
    vne (gd krot a b) ne = ne
    vne (gd kki a b)  lt = λ e → <⇒≢ lt (Eq.sym e)

    good : ∀ G → Valid G → Both OnP G → Good β (kind G , cod (i G) , cod (j G))
    good G vG (hi , hj) = pq , lpq , top-on (i G) hi , top-on (j G) hj
      where
      pq : cod (i G) ≢ cod (j G)
      pq e = vne G vG (cod-inj e)

      lpq : low (bm β (cod (i G))) ≢ low (bm β (cod (j G)))
      lpq e = pq (low-inj (cod (i G)) (cod (j G)) (top-on (i G) hi) (top-on (j G) hj) e)

    goods : ∀ Gs → All Valid Gs → All (Both OnP) Gs → All (Good β) (pts Gs)
    goods []       []       []       = []
    goods (G ∷ Gs) (vG ∷ vs) (h ∷ hs) = good G vG h ∷ goods Gs vs hs

    L L′ : List (Pt 5)
    L  = pts (GL u)
    L′ = pts (GL t)

    gL : All (Good β) L
    gL = goods (GL u) (valid-GL u) (on-GL u (hu OnP onk))

    gL′ : All (Good β) L′
    gL′ = goods (GL t) (valid-GL t) (on-GL t (ht OnP onk))

    ----------------------------------------------------------------------
    -- The semantics

    Π-pts : ∀ Gs → Π Gs ≡ Πp (pts Gs)
    Π-pts []       = refl
    Π-pts (G ∷ Gs) = Eq.cong (tl (blkOf (kind G)) (cod (i G)) (cod (j G)) ∙_) (Π-pts Gs)

    eΠ : Πp L ~ Πp L′
    eΠ = Eq.subst₂ _~_ (Π-pts (GL u)) (Π-pts (GL t))
           (~-trans {s = Π (GL u)} {t = ⟦ u ⟧PY} {u = Π (GL t)}
             (~-sym {s = ⟦ u ⟧PY} {t = Π (GL u)} (sem-w u))
             (~-trans {s = ⟦ u ⟧PY} {t = ⟦ t ⟧PY} {u = Π (GL t)} (sound (PB.axiom ax)) (sem-w t)))

    halfs : ∀ M → All (Good β) M → OnHalf (mapf f g fg gf M)
    halfs []                []                     = []
    halfs ((V , p , q) ∷ M) ((_ , _ , tp , tq) ∷ gs) = (tp , tq) ∷ halfs M gs

    lows-mapf : ∀ M → lows (mapf f g fg gf M) ≡ lowsβ β M
    lows-mapf []                = refl
    lows-mapf ((V , p , q) ∷ M) = Eq.cong ((V , low (f p) , low (f q)) ∷_) (lows-mapf M)

    e4Π : Πp (lowsβ β L) ~ Πp (lowsβ β L′)
    e4Π = Eq.subst₂ _~_ (Eq.cong Πp (lows-mapf L)) (Eq.cong Πp (lows-mapf L′))
            (core f g fg gf L L′ eΠ (halfs L gL) (halfs L′ gL′))

    Dist : Pt 4 → Set
    Dist (V , a , b) = a ≢ b

    dist : ∀ M → All (Good β) M → All Dist (lowsβ β M)
    dist []                []                       = []
    dist ((V , p , q) ∷ M) ((_ , ne , _ , _) ∷ gs)  = ne ∷ dist M gs

    g₄-sem : ∀ V a b → a ≢ b → ⟦ g₄ V a b ⟧ ~ tl (blkOf V) a b
    g₄-sem V a b ne =
      Eq.subst₂ (λ x y → ⟦ g₄ V a b ⟧ ~ tl (blkOf V) x y) (α-o a b) (α-e a b ne) (gad₄-sem V (α a b))

    sem4 : ∀ Q → All Dist Q → ⟦ Dg₄ Q ⟧ ~ Πp Q
    sem4 []                []        = ~-reflexive {l = 0} {0} {M = ⟦_⟧ₒ {4} ε} {Idₒ} refl ⟦⟧ₒ-ε
    sem4 ((V , a , b) ∷ Q) (ne ∷ ds) =
      ~-trans {s = ⟦ g₄ V a b • Dg₄ Q ⟧} {t = ⟦ g₄ V a b ⟧ ∙ ⟦ Dg₄ Q ⟧} {u = Πp ((V , a , b) ∷ Q)}
        (hom (g₄ V a b) (Dg₄ Q))
        (∙-cong {s = ⟦ g₄ V a b ⟧} {s' = tl (blkOf V) a b} {t = ⟦ Dg₄ Q ⟧} {t' = Πp Q}
          (g₄-sem V a b ne) (sem4 Q ds))

    W W′ : Circuit 4
    W  = Dg₄ (lowsβ β L)
    W′ = Dg₄ (lowsβ β L′)

    sem-eq : ⟦ W ⟧ ~ ⟦ W′ ⟧
    sem-eq =
      ~-trans {s = ⟦ W ⟧} {t = Πp (lowsβ β L)} {u = ⟦ W′ ⟧} (sem4 (lowsβ β L) (dist L gL))
        (~-trans {s = Πp (lowsβ β L)} {t = Πp (lowsβ β L′)} {u = ⟦ W′ ⟧} e4Π
          (~-sym {s = ⟦ W′ ⟧} {t = Πp (lowsβ β L′)} (sem4 (lowsβ β L′) (dist L′ gL′))))

    e5 : Λ⁰ W ≈ Λ⁰ W′
    e5 = transport⁰ ok {W} {W′} (c4 {W} {W′} sem-eq)

    ----------------------------------------------------------------------
    -- Conjugating back

    il : τ (β ⁻¹) • τ β ≈ ε
    il = embed (aff⇒ (Inv.inverseˡ 5 {β}))

    uncj : ∀ x → x ≈ τ (β ⁻¹) • (τ β • x • τ (β ⁻¹)) • τ β
    uncj x = begin
      x                                             ≈⟨ sym left-unit ⟩
      ε • x                                         ≈⟨ front x (sym il) ⟩
      (τ (β ⁻¹) • τ β) • x                          ≈⟨ back _ (sym right-unit) ⟩
      (τ (β ⁻¹) • τ β) • (x • ε)                    ≈⟨ back _ (back x (sym il)) ⟩
      (τ (β ⁻¹) • τ β) • (x • (τ (β ⁻¹) • τ β))
        ≈⟨ by-passoc ((□ • □) • (□ • (□ • □))) (□ • (□ • □ • □) • □) Eq.refl ⟩
      τ (β ⁻¹) • (τ β • x • τ (β ⁻¹)) • τ β ∎

  dwd : (d ʷ) u ≈ (d ʷ) t
  dwd = begin
    (d ʷ) u                                       ≈⟨ dʷ-D u ⟩
    Dg L                                          ≈⟨ uncj (Dg L) ⟩
    τ (β ⁻¹) • (τ β • Dg L • τ (β ⁻¹)) • τ β      ≈⟨ back _ (front _ (red-D β L gL)) ⟩
    τ (β ⁻¹) • Λ⁰ W • τ β                         ≈⟨ back _ (front _ e5) ⟩
    τ (β ⁻¹) • Λ⁰ W′ • τ β                        ≈⟨ back _ (front _ (sym (red-D β L′ gL′))) ⟩
    τ (β ⁻¹) • (τ β • Dg L′ • τ (β ⁻¹)) • τ β     ≈⟨ sym (uncj (Dg L′)) ⟩
    Dg L′                                         ≈⟨ sym (dʷ-D t) ⟩
    (d ʷ) t ∎

------------------------------------------------------------------------
-- Every rule
--
-- Each rule's indices (at most five, the vector padded by repeats), and
-- for each side the index of every letter in that vector.

private
  vec : Fin N → Fin N → Fin N → Fin N → Fin N → Vec (Fin N) 5
  vec a b c e f = a ∷ᵥ b ∷ᵥ c ∷ᵥ e ∷ᵥ f ∷ᵥ []ᵥ

  ι₀ ι₁ ι₂ ι₃ ι₄ : Fin 5
  ι₀ = zero
  ι₁ = suc zero
  ι₂ = suc (suc zero)
  ι₃ = suc (suc (suc zero))
  ι₄ = suc (suc (suc (suc zero)))

dwd : ∀ {u t} → N R, u === t → (d ʷ) u ≈ (d ʷ) t
dwd ax@(pp-id a) =
  Gen.dwd _ _ ax (vec a a a a a) (λ P h → h ι₀ , h ι₀) (λ P h → tt)
dwd ax@(pp-ord a b) =
  Gen.dwd _ _ ax (vec a b a a a)
    (λ P h → (h ι₀ , h ι₁) , ((h ι₀ , h ι₁) , ((h ι₀ , h ι₁) , (h ι₀ , h ι₁)))) (λ P h → tt)
dwd ax@(pp-comm a b c e) =
  Gen.dwd _ _ ax (vec a b c e a)
    (λ P h → (h ι₀ , h ι₁) , (h ι₂ , h ι₃)) (λ P h → (h ι₂ , h ι₃) , (h ι₀ , h ι₁))
dwd ax@(pp-tele a b c) =
  Gen.dwd _ _ ax (vec a b c a a)
    (λ P h → (h ι₀ , h ι₁) , (h ι₁ , h ι₂)) (λ P h → h ι₀ , h ι₂)
dwd ax@(px-sq a a′ s) =
  Gen.dwd _ _ ax (vec a a′ a a a)
    (λ P h → (h ι₀ , h ι₁) , (h ι₀ , h ι₁)) (λ P h → (h ι₀ , h ι₀ , h ι₁) , (h ι₀ , h ι₀ , h ι₁))
dwd ax@(px-braid a a′ a″ s s′) =
  Gen.dwd _ _ ax (vec a a′ a″ a a)
    (λ P h → (h ι₀ , h ι₀ , h ι₁) , ((h ι₁ , h ι₁ , h ι₂) , (h ι₀ , h ι₀ , h ι₁)))
    (λ P h → (h ι₁ , h ι₁ , h ι₂) , ((h ι₀ , h ι₀ , h ι₁) , (h ι₁ , h ι₁ , h ι₂)))
dwd ax@(px-shrink₁ a a′ c s lt) =
  Gen.dwd _ _ ax (vec a a′ c a a)
    (λ P h → h ι₀ , h ι₀ , h ι₂)
    (λ P h → (h ι₁ , h ι₀ , h ι₁) , ((h ι₁ , h ι₁ , h ι₂) , (h ι₀ , h ι₀ , h ι₁)))
dwd ax@(px-shrink₂ a a′ c s lt) =
  Gen.dwd _ _ ax (vec a a′ c a a)
    (λ P h → h ι₂ , h ι₀ , h ι₂)
    (λ P h → (h ι₁ , h ι₀ , h ι₁) , ((h ι₂ , h ι₁ , h ι₂) , (h ι₀ , h ι₀ , h ι₁)))
dwd ax@(px-shrink₃ a c′ c s lt) =
  Gen.dwd _ _ ax (vec a c′ c a a)
    (λ P h → h ι₀ , h ι₀ , h ι₂)
    (λ P h → (h ι₁ , h ι₁ , h ι₂) , ((h ι₀ , h ι₀ , h ι₁) , (h ι₂ , h ι₁ , h ι₂)))
dwd ax@(px-shrink₄ a c′ c s lt) =
  Gen.dwd _ _ ax (vec a c′ c a a)
    (λ P h → h ι₂ , h ι₀ , h ι₂)
    (λ P h → (h ι₁ , h ι₁ , h ι₂) , ((h ι₁ , h ι₀ , h ι₁) , (h ι₂ , h ι₁ , h ι₂)))
dwd ax@(px-inv a a′ s) =
  Gen.dwd _ _ ax (vec a a′ a a a)
    (λ P h → (h ι₀ , h ι₀ , h ι₁) , (h ι₁ , h ι₀ , h ι₁)) (λ P h → tt)
dwd ax@(px-sign c a b ab) =
  Gen.dwd _ _ ax (vec c a b c c)
    (λ P h → h ι₀ , h ι₁ , h ι₂)
    (λ P h → (h ι₀ , h ι₁) , ((h ι₀ , h ι₁) , (h ι₁ , h ι₁ , h ι₂)))
dwd ax@(px-conj a a′ c s _ _) =
  Gen.dwd _ _ ax (vec a a′ c a a)
    (λ P h → (h ι₁ , h ι₂) , (h ι₀ , h ι₀ , h ι₁)) (λ P h → (h ι₀ , h ι₀ , h ι₁) , (h ι₀ , h ι₂))
dwd ax@(px-conj₂ a a′ s) =
  Gen.dwd _ _ ax (vec a a′ a a a)
    (λ P h → (h ι₀ , h ι₁) , (h ι₀ , h ι₀ , h ι₁)) (λ P h → (h ι₀ , h ι₀ , h ι₁) , (h ι₁ , h ι₀))
dwd ax@(px-comm a a′ b b′ s s′ lt) =
  Gen.dwd _ _ ax (vec a a′ b b′ a)
    (λ P h → (h ι₀ , h ι₀ , h ι₁) , (h ι₂ , h ι₂ , h ι₃))
    (λ P h → (h ι₂ , h ι₂ , h ι₃) , (h ι₀ , h ι₀ , h ι₁))
dwd ax@(dx-split a b c e ab ce) =
  Gen.dwd _ _ ax (vec a b c e a)
    (λ P h → h ι₀ , h ι₁ , h ι₂ , h ι₃) (λ P h → (h ι₀ , h ι₀ , h ι₁) , (h ι₁ , h ι₂ , h ι₃))
dwd ax@(ki-sink a b s t ab) =
  Gen.dwd _ _ ax (vec a b s t a)
    (λ P h → (h ι₀ , h ι₁ , h ι₂) , (h ι₂ , h ι₃)) (λ P h → h ι₀ , h ι₁ , h ι₃)
dwd ax@(ki-pp a b s x ab _ _ _ _) =
  Gen.dwd _ _ ax (vec a b s x a)
    (λ P h → (h ι₃ , h ι₂) , (h ι₀ , h ι₁ , h ι₂)) (λ P h → (h ι₀ , h ι₁ , h ι₂) , (h ι₃ , h ι₂))
dwd ax@(ki-px a b s x y ab xy _ _ _ _ _ _ _ _) =
  Gen.dwd _ _ ax (vec a b s x y)
    (λ P h → (h ι₂ , h ι₃ , h ι₄) , (h ι₀ , h ι₁ , h ι₂))
    (λ P h → (h ι₀ , h ι₁ , h ι₂) , (h ι₂ , h ι₃ , h ι₄))
dwd ax@(ki-ki a b c e s ab ce _ _ _ _ _ _ _ _) =
  Gen.dwd _ _ ax (vec a b c e s)
    (λ P h → (h ι₀ , h ι₁ , h ι₄) , (h ι₂ , h ι₃ , h ι₄))
    (λ P h → (h ι₂ , h ι₃ , h ι₄) , (h ι₀ , h ι₁ , h ι₄))
dwd ax@(ki-swap j k l s p q _ _ _) =
  Gen.dwd _ _ ax (vec j k l s j)
    (λ P h → (h ι₁ , h ι₂ , h ι₃) , (h ι₃ , h ι₀ , h ι₁))
    (λ P h → (h ι₃ , h ι₀ , h ι₁) , (h ι₀ , h ι₂ , h ι₃))
dwd ax@(ki-swap′ j k l s p q _ _ _) =
  Gen.dwd _ _ ax (vec j k l s j)
    (λ P h → (h ι₀ , h ι₂ , h ι₃) , (h ι₃ , h ι₁ , h ι₂))
    (λ P h → (h ι₃ , h ι₁ , h ι₂) , (h ι₀ , h ι₁ , h ι₃))
dwd ax@(ki-x a b s ab _ _) =
  Gen.dwd _ _ ax (vec a b s a a)
    (λ P h → (h ι₀ , h ι₁ , h ι₂) , ((h ι₁ , h ι₂) , (h ι₁ , h ι₂)))
    (λ P h → (h ι₂ , h ι₀ , h ι₁) , (h ι₀ , h ι₁ , h ι₂))
dwd ax@(ki-16 a b s ab _ _) =
  Gen.dwd _ _ ax (vec a b s a a)
    (λ P h → (h ι₀ , h ι₁ , h ι₂) , ((h ι₁ , h ι₂) , ((h ι₁ , h ι₂) , (h ι₁ , h ι₂))))
    (λ P h → (h ι₁ , h ι₂) , ((h ι₀ , h ι₁ , h ι₂) , ((h ι₁ , h ι₂) , (h ι₀ , h ι₁ , h ι₂))))
dwd ax@(ki-ii a b s ab _ _) =
  Gen.dwd _ _ ax (vec a b s a a)
    (λ P h → (h ι₀ , h ι₁ , h ι₂) , ((h ι₀ , h ι₂) , (h ι₁ , h ι₂)))
    (λ P h → (h ι₀ , h ι₂) , ((h ι₁ , h ι₂) , (h ι₀ , h ι₁ , h ι₂)))
dwd ax@(ki-sq a b s ab _ _) =
  Gen.dwd _ _ ax (vec a b s a a)
    (λ P h → ((h ι₀ , h ι₁ , h ι₂) , (h ι₀ , h ι₁ , h ι₂)) , ((h ι₀ , h ι₂) , (h ι₁ , h ι₂)))
    (λ P h → tt)
dwd ax@(ki-yb j k l m s jk lm jl km _ _ _ _ _) =
  Gen.dwd _ _ ax (vec j k l m s)
    (λ P h → (h ι₀ , h ι₁ , h ι₄) , ((h ι₂ , h ι₃ , h ι₄) , ((h ι₀ , h ι₂ , h ι₄) , (h ι₁ , h ι₃ , h ι₄))))
    (λ P h → (h ι₀ , h ι₂ , h ι₄) , ((h ι₁ , h ι₃ , h ι₄) , ((h ι₀ , h ι₁ , h ι₄) , (h ι₂ , h ι₃ , h ι₄))))
