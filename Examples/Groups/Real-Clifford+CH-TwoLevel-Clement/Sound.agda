------------------------------------------------------------------------
-- Presentations of groups
--
-- A tree that passes the check gives the hard edge.
--
-- The setting of a node is a state s at L = (p + 1, k, 4) with a
-- window ι of local indices ≤ p outside which every entry is even, the
-- local entries the values of the forms at some ρ, the tagged entries
-- at their depths, and, with the flag, minimality of s.  Then
-- Path (Hs (ι ic) (ι id)) s (sound), by induction on the tree:
--
-- * leaf: the route is a path (Route) with the relation of its diagram
--   (Relators);
-- * split: the values are those of one branch (Subst);
-- * extend: at the state after the route the column is a vector at a
--   lower scale whose local quotients the check counts; minimality and
--   the tags put every outside entry at depth δ at least (deep-out), so
--   an outside entry of the kind exists (Count.Extra), and its value is
--   the new form at some value of the new variable;
-- * conj: the letter g is an edge out of s, and out of Hs ic id · s;
--   g' Hs = Hs g with g' = g, or X for Z at id, closes the square
--   (via-w), the path from g · s given by the subtree;
-- * relabel: the window permuted; reversing the pair costs
--   Hs c d = Xs d c • Z c • Hs d c, edges out of Hs d c · s;
-- * useNF: the normal form's theorem at the composed values.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Word.Base using (Word)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (ColOrth)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Framework as F

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Sound {n : ℕ} (p : Fin n) (k′ ℓ : ℕ)
  (nw : (M : Matrix n n D) → .(ColOrth M) → Word (Gen n))
  (ih : F.EdgesBelow p k′ ℓ nw) (plain : F.PlainEdges p k′ ℓ nw) (ℓ4 : ℓ ≡ 4) where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; not ; if_then_else_ ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (zero ; suc ; _<_ ; _≤_)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_ ; length)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; ∃₂ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_ ; tabulate ; _[_]≔_)
import Data.Vec.Properties as VecP
import Function.Bundles as Fun
open import Relation.Binary.PropositionalEquality as ≡ using (_≢_)
open import Relation.Nullary using (yes ; no)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (oddℕ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (D ; Z ; module ZR ; module ZG ; √2ᶻ ; _^ᶻ_ ; oddᶻ ; rbit ; oddᶻ-neg ; rbit-neg ; rbit-+ ; even⇒δ∣)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (num)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Clement using (_===ᶜ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (level)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (Z-Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (sound-act)
open F p k′ ℓ nw using (Path ; path-• ; nw-cong ; path-cong)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Local {n} using (module Emb ; upd₁-i ; upd₁-o ; upd₂-o)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric {n} using (Hs ; Xs ; Hs-comm)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence as EQ
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PairLevels p k′ ℓ using (k ; L ; module State)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Route p k′ ℓ nw ih plain as RT
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Forms
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Subst
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Tree
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.TreeFacts
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Count p using (module Extra ; Pκ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Relators using (module Leaf ; module Deco)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Placed as Placed

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid
open ZG using (_:*_ ; :-_ ; _:-_ ; _:=_ ; con)

private
  fst : ∀ a {b} → a ∧ b ≡ true → a ≡ true
  fst true _ = ≡.refl

  snd : ∀ a {b} → a ∧ b ≡ true → b ≡ true
  snd true e = e

  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

------------------------------------------------------------------------
-- States, windows, depths

Wn : Matrix n n D → Vec Z n
Wn N = num (col N p)

-- z is √2^δ times an odd element.
Deep : Z → ℕ → Set
Deep z δ = ∃ λ y → z ≡ (√2ᶻ ^ᶻ δ) ZR.* y × oddᶻ y ≡ true

-- No two entries of depth 1, or of depth 2, are of one class.
Minimal : Matrix n n D → Set
Minimal N = ∀ δ → 1 ℕ.≤ δ → δ ℕ.≤ 2 → ∀ u v y y′ → u ≢ v →
            Wn N ! u ≡ (√2ᶻ ^ᶻ δ) ZR.* y → Wn N ! v ≡ (√2ᶻ ^ᶻ δ) ZR.* y′ →
            oddᶻ y ≡ true → oddᶻ y′ ≡ true → rbit y ≡ rbit y′ → ⊥

record Win (m : ℕ) (s : Matrix n n D) : Set where
  constructor win
  field
    ι   : Fin m → Fin n
    inj : ∀ {i j} → ι i ≡ ι j → i ≡ j
    ι≤p : ∀ i → ι i ≤ p
    out : ∀ x → (∀ i → ι i ≢ x) → oddᶻ (Wn s ! x) ≡ false

open Win public

locW : ∀ {m} {s : Matrix n n D} → Win m s → Vec Z m
locW {s = s} w = tabulate (λ i → Wn s ! ι w i)

TagsOK : ∀ {m} (s : Matrix n n D) → Win m s → Vec (Maybe ℕ) m → Set
TagsOK s w tags = ∀ i δ → tags ! i ≡ just δ → Deep (Wn s ! ι w i) δ

-- The statement of a normal form's tree.
NFThm : ((nf : NF) → NFData nf) → NF → Set
NFThm nfData nf =
  ∀ (s : Matrix n n D) .(o : ColOrth s) (eq : level s ≡ L) (w : Win (nfRows nf) s) (ρ : Vec Z (nfVars nf)) →
  ⟦ NFData.forms (nfData nf) ⟧ᵛ ρ ≡ locW w → TagsOK s w (NFData.tags (nfData nf)) →
  (NFData.mini (nfData nf) ≡ true → Minimal s) → NFData.ic (nfData nf) ≢ NFData.id (nfData nf) →
  Path (Hs (ι w (NFData.ic (nfData nf))) (ι w (NFData.id (nfData nf)))) s o

------------------------------------------------------------------------
-- Relations and squares

private
  fromᶜ : ∀ {u v : Word (Gen n)} → PB._≈_ (_===ᶜ_ {n}) u v → u ≈ v
  fromᶜ = Fun.Equivalence.from EQ.equivalent

  ZH : ∀ {a b x : Fin n} → a ≢ b → x ≢ a → x ≢ b → Zʷ x • Hs a b ≈ Hs a b • Zʷ x
  ZH {a} {b} {x} ab xa xb = begin
    Zʷ x • Hs a b                        ≈⟨ sym right-unit ⟩
    (Zʷ x • Hs a b) • ε                  ≈⟨ cright sym Z-Z ⟩
    (Zʷ x • Hs a b) • (Zʷ x • Zʷ x)      ≈⟨ sym assoc ⟩
    ((Zʷ x • Hs a b) • Zʷ x) • Zʷ x      ≈⟨ cleft assoc ⟩
    (Zʷ x • (Hs a b • Zʷ x)) • Zʷ x      ≈⟨ cleft fromᶜ (Deco.ZHZ ab xa xb) ⟩
    Hs a b • Zʷ x                        ∎

  XH′ : ∀ {a b : Fin n} → a ≢ b → Xs a b • Hs a b ≈ Hs a b • Zʷ b
  XH′ ab = fromᶜ (Deco.XH ab)

  XZH′ : ∀ {a b : Fin n} → a ≢ b → Xs a b • Zʷ b • Hs a b ≈ Hs b a
  XZH′ ab = fromᶜ (Deco.XZH ab)

-- The edge g out of M from a path N′ out of g·M and a path U out of M
-- with N′ g ≈ U (PathTools.via, for words).
via-w : (g : Word (Gen n)) (M : Matrix n n D) .(o : ColOrth M) (N′ U : Word (Gen n)) →
        Path N′ (actMʷ g M) (ColOrth-actMʷ g o) → N′ • g ≈ U → Path U M o → Path g M o
via-w g M o N′ U pN rel pU = begin
  nw (actMʷ g M) (ColOrth-actMʷ g o) • g
    ≈⟨ cleft sym pN ⟩
  (nw (actMʷ N′ (actMʷ g M)) (ColOrth-actMʷ N′ (ColOrth-actMʷ g o)) • N′) • g
    ≈⟨ assoc ⟩
  nw (actMʷ N′ (actMʷ g M)) (ColOrth-actMʷ N′ (ColOrth-actMʷ g o)) • (N′ • g)
    ≈⟨ cright rel ⟩
  nw (actMʷ N′ (actMʷ g M)) (ColOrth-actMʷ N′ (ColOrth-actMʷ g o)) • U
    ≈⟨ cleft refl′ (nw-cong (sound-act rel M) _ (ColOrth-actMʷ U o)) ⟩
  nw (actMʷ U M) (ColOrth-actMʷ U o) • U
    ≈⟨ pU ⟩
  nw M o ∎

------------------------------------------------------------------------
-- Facts at a window

module At-window {m : ℕ} (s : Matrix n n D) .(o : ColOrth s) (eq : level s ≡ L) (w : Win m s) where

  open RT.Local-at s o eq ℓ4 (ι w) (inj w) (ι≤p w) (out w) public
  open Emb (ι w) (inj w) using (emb ; emb-ι ; emb-o)

  wordRι = Placed.wordR (ι w)

  known-at : ∀ {r} (fs : Vec (Form r) m) ρ → ⟦ fs ⟧ᵛ ρ ≡ locW w → Known s (⟦ fs ⟧ᵛ ρ)
  known-at fs ρ eqv = ≡.subst (Known s) (≡.sym eqv) known-s

  -- A route of the check's runF leads to a known state.
  run-known : ∀ {r} (R : Route m) (fs : Vec (Form r) m) {fs′} → runF R fs ≡ just fs′ → ∀ ρ {N} →
              Known N (⟦ fs ⟧ᵛ ρ) → Known (actMʷ (wordRι R) N) (⟦ fs′ ⟧ᵛ ρ)
  run-known [] fs ≡.refl ρ K = K
  run-known (g ∷ R) fs e ρ K with distinctF g in dg | stepF g fs in st
  ... | true | just fs₁ = run-known R fs₁ e ρ (known-step g (distinctF-sound g dg) (stepF-sound g fs st ρ) K)
  run-known (g ∷ R) fs () ρ K | true | nothing
  run-known (g ∷ R) fs () ρ K | false | _

  -- The local vector of a known state at L is its window's.
  loc-emb : ∀ (e : Vec Z m) (V : Vec Z n) → tabulate (λ i → emb e V ! ι w i) ≡ e
  loc-emb e V = vec-ext λ i → ≡.trans (VecP.lookup∘tabulate (λ i → emb e V ! ι w i) i) (emb-ι e V i)

  -- A known state at L: its window and its local vector.
  module Next {N : Matrix n n D} {e : Vec Z m} (K : Known N e) .(oN : ColOrth N) (eqN : level N ≡ L) where

    WN : Wn N ≡ emb e (Wn s)
    WN = W-at K oN eqN

    win′ : Win m N
    win′ = win (ι w) (inj w) (ι≤p w) λ x o′ → ≡.trans (≡.cong (λ V → oddᶻ (V ! x)) WN) (≡.trans (≡.cong oddᶻ (emb-o e (Wn s) o′)) (out w x o′))

    loc′ : e ≡ locW win′
    loc′ = ≡.sym (≡.trans (≡.cong (λ V → tabulate (λ i → V ! ι w i)) WN) (loc-emb e (Wn s)))

    outside : ∀ x → (∀ i → ι w i ≢ x) → Wn N ! x ≡ Wn s ! x
    outside x o′ = ≡.trans (≡.cong (_! x) WN) (emb-o e (Wn s) o′)

    inside : ∀ i → Wn N ! ι w i ≡ e ! i
    inside i = ≡.trans (≡.cong (_! ι w i) WN) (emb-ι e (Wn s) i)

  -- The path of a one-letter route.
  letter : ∀ {r} (g : Let m) (fs : Vec (Form r) m) ρ {N} .(oN : ColOrth N) → check (g ∷ []) fs ≡ true →
           Known N (⟦ fs ⟧ᵛ ρ) → Path (wordL g) N oN
  letter g fs ρ {N} oN ok K = path-cong left-unit N oN (route-path (g ∷ []) fs ρ oN ok K)

------------------------------------------------------------------------
-- Leaves

private
  check-distinct : ∀ {m r} (g : Let m) gs (fs : Vec (Form r) m) → check (g ∷ gs) fs ≡ true → Distinct g
  check-distinct g gs fs ok with stepF g fs
  ... | just fs′ = distinctF-sound g (fst (distinctF g) ok)

  ends : ∀ {m} (ic id a b : Fin m) fl → endsOK ic id a b fl ≡ true →
         (fl ≡ false × a ≡ ic × b ≡ id) ⊎ (fl ≡ true × a ≡ id × b ≡ ic)
  ends ic id a b false e = inj₁ (≡.refl , ==-sound (fst (a == ic) e) , ==-sound (snd (a == ic) e))
  ends ic id a b true e = inj₂ (≡.refl , ==-sound (fst (a == id) e) , ==-sound (snd (a == id) e))

leaf-path : ∀ {m r} (ld : LeafD m) (ic id : Fin m) (fs : Vec (Form r) m) ρ → leafOK ic id ld ≡ true →
            check (leafRoute ld) fs ≡ true → ∀ s .(o : ColOrth s) (eq : level s ≡ L) (w : Win m s) →
            ⟦ fs ⟧ᵛ ρ ≡ locW w → Path (Hs (ι w ic) (ι w id)) s o
leaf-path {m} (l30 (a ∷ b ∷ lab) Q fl) ic id fs ρ okL okC s o eq w eqv =
  path-cong (rel (ends ic id a b fl (fst (endsOK ic id a b fl) (snd (distinctV (a ∷ b ∷ lab)) okL)))) s o pth
  where
  open At-window s o eq w using (route-path ; known-at)
  labv = a ∷ b ∷ lab
  pth = route-path (leafRoute (l30 labv Q fl)) fs ρ o okC (known-at fs ρ eqv)
  lab-inj = distinctV-sound labv (fst (distinctV labv) okL)
  okQ = avoid-sound a Q (snd (endsOK ic id a b fl) (snd (distinctV labv) okL))
  rel : (fl ≡ false × a ≡ ic × b ≡ id) ⊎ (fl ≡ true × a ≡ id × b ≡ ic) →
        Placed.wordR (ι w) (leafRoute (l30 labv Q fl)) ≈ Hs (ι w ic) (ι w id)
  rel (inj₁ (≡.refl , ≡.refl , ≡.refl)) = Leaf.route30-rel (ι w) (inj w) (Vec.lookup labv) lab-inj Q okQ
  rel (inj₂ (≡.refl , ≡.refl , ≡.refl)) = Leaf.route30-flip (ι w) (inj w) (Vec.lookup labv) lab-inj Q okQ
leaf-path {m} (l20 (a ∷ b ∷ lab) Q fl) ic id fs ρ okL okC s o eq w eqv =
  path-cong (rel (ends ic id a b fl (fst (endsOK ic id a b fl) (snd (distinctV (a ∷ b ∷ lab)) okL)))) s o pth
  where
  open At-window s o eq w using (route-path ; known-at)
  labv = a ∷ b ∷ lab
  pth = route-path (leafRoute (l20 labv Q fl)) fs ρ o okC (known-at fs ρ eqv)
  lab-inj = distinctV-sound labv (fst (distinctV labv) okL)
  okQ = avoid-sound a Q (snd (endsOK ic id a b fl) (snd (distinctV labv) okL))
  rel : (fl ≡ false × a ≡ ic × b ≡ id) ⊎ (fl ≡ true × a ≡ id × b ≡ ic) →
        Placed.wordR (ι w) (leafRoute (l20 labv Q fl)) ≈ Hs (ι w ic) (ι w id)
  rel (inj₁ (≡.refl , ≡.refl , ≡.refl)) = Leaf.route20-rel (ι w) (inj w) (Vec.lookup labv) lab-inj Q okQ
  rel (inj₂ (≡.refl , ≡.refl , ≡.refl)) = Leaf.route20-flip (ι w) (inj w) (Vec.lookup labv) lab-inj Q okQ

------------------------------------------------------------------------
-- Depths and counts

private
  deep-neg : ∀ {z δ} → Deep z δ → Deep (ZR.- z) δ
  deep-neg {z} {δ} (y , e , oy) =
    ZR.- y , ≡.trans (≡.cong ZR.-_ e) (ZG.solve 2 (λ c y → :- (c :* y) := c :* (:- y)) ≡.refl (√2ᶻ ^ᶻ δ) y) ,
    ≡.trans (oddᶻ-neg y) oy

  -- A state whose numerator is that of s up to signs is minimal with s.
  minimal-± : ∀ {N s} → (∀ x → Wn N ! x ≡ Wn s ! x ⊎ Wn N ! x ≡ ZR.- (Wn s ! x)) → Minimal s → Minimal N
  minimal-± {N} {s} pm mn δ lo hi u v y y′ uv eu ev oy oy′ c = at (back u y eu) (back v y′ ev)
    where
    back′ : ∀ (a b : Z) y → (b ≡ a ⊎ b ≡ ZR.- a) → b ≡ (√2ᶻ ^ᶻ δ) ZR.* y →
            ∃ λ y₀ → a ≡ (√2ᶻ ^ᶻ δ) ZR.* y₀ × oddᶻ y₀ ≡ oddᶻ y × rbit y₀ ≡ rbit y
    back′ a b y (inj₁ same) e = y , ≡.trans (≡.sym same) e , ≡.refl , ≡.refl
    back′ a b y (inj₂ neg) e = ZR.- y ,
      ≡.trans (ZG.solve 1 (λ t → t := :- (:- t)) ≡.refl a)
        (≡.trans (≡.cong ZR.-_ (≡.trans (≡.sym neg) e)) (ZG.solve 2 (λ c y → :- (c :* y) := c :* (:- y)) ≡.refl (√2ᶻ ^ᶻ δ) y)) ,
      oddᶻ-neg y , rbit-neg y
    back : ∀ x y → Wn N ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y →
           ∃ λ y₀ → Wn s ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y₀ × oddᶻ y₀ ≡ oddᶻ y × rbit y₀ ≡ rbit y
    back x y e = back′ (Wn s ! x) (Wn N ! x) y (pm x) e
    at : (∃ λ y₀ → Wn s ! u ≡ (√2ᶻ ^ᶻ δ) ZR.* y₀ × oddᶻ y₀ ≡ oddᶻ y × rbit y₀ ≡ rbit y) →
         (∃ λ y₀ → Wn s ! v ≡ (√2ᶻ ^ᶻ δ) ZR.* y₀ × oddᶻ y₀ ≡ oddᶻ y′ × rbit y₀ ≡ rbit y′) → ⊥
    at (a , ea , oa , ra) (b , eb , ob , rb) =
      mn δ lo hi u v a b uv ea eb (≡.trans oa oy) (≡.trans ob oy′) (≡.trans ra (≡.trans c (≡.sym rb)))

  Pκ-odd : ∀ κ y → Pκ κ y ≡ true → oddᶻ y ≡ true
  Pκ-odd nothing y e = e
  Pκ-odd (just true) y e = fst (oddᶻ y) e
  Pκ-odd (just false) y e = fst (oddᶻ y) e

  new-cls : ∀ {r} δ b y → oddᶻ y ≡ true → rbit y ≡ b → ∃ λ v → ∀ (ρ : Vec Z r) → ⟦ newF δ (just b) ⟧ (v ∷ ρ) ≡ (√2ᶻ ^ᶻ δ) ZR.* y
  new-cls δ b y oy cy = at (cls-decomp y b oy cy)
    where
    at : (∃ λ v → y ≡ ZR.1# ZR.+ √2ᶻ ZR.* bitᶻ b ZR.+ (ZR.1# ZR.+ ZR.1#) ZR.* v) →
         ∃ λ v → ∀ ρ → ⟦ newF δ (just b) ⟧ (v ∷ ρ) ≡ (√2ᶻ ^ᶻ δ) ZR.* y
    at (v , ev) = v , λ ρ → ≡.trans (⟦newF⟧ δ b v ρ) (≡.cong ((√2ᶻ ^ᶻ δ) ZR.*_) (≡.sym ev))

  -- The value of the new entry.
  new-val : ∀ {r} δ κ y → Pκ κ y ≡ true → ∃ λ v → ∀ (ρ : Vec Z r) → ⟦ newF δ κ ⟧ (v ∷ ρ) ≡ (√2ᶻ ^ᶻ δ) ZR.* y
  new-val δ nothing y e = at (odd-decomp y e)
    where
    at : (∃ λ v → y ≡ ZR.1# ZR.+ √2ᶻ ZR.* v) → ∃ λ v → ∀ ρ → ⟦ newF δ nothing ⟧ (v ∷ ρ) ≡ (√2ᶻ ^ᶻ δ) ZR.* y
    at (v , ev) = v , λ ρ → ≡.trans (⟦newF₀⟧ δ v ρ) (≡.cong ((√2ᶻ ^ᶻ δ) ZR.*_) (≡.sym ev))
  new-val δ (just true) y e = new-cls δ true y (fst (oddᶻ y) e) (snd (oddᶻ y) e)
  new-val δ (just false) y e = new-cls δ false y (fst (oddᶻ y) e) (not-t (snd (oddᶻ y) e))

  -- What countOK says about the local quotients.
  countOK-sound : ∀ {m r} κ (gs : Vec (Form r) m) → countOK κ gs ≡ true → ∀ ρ → oddℕ (countV (Pκ κ) (⟦ gs ⟧ᵛ ρ)) ≡ true
  countOK-sound nothing gs e ρ =
    ≡.trans (odd-count-sum (⟦ gs ⟧ᵛ ρ)) (≡.trans (≡.cong oddᶻ (≡.sym (⟦sumF⟧ gs ρ))) (oddF-sound (sumF gs) e ρ))
  countOK-sound (just b) gs e ρ with noddF gs in nd | clsF (oddSumF gs) in cl
  ... | just c | just c₁ = at b e
    where
    cnt1 : oddℕ (countV (λ z → oddᶻ z ∧ rbit z) (⟦ gs ⟧ᵛ ρ)) ≡ c₁
    cnt1 = ≡.trans (odd-count-cls gs nd ρ) (clsF-sound (oddSumF gs) cl ρ)
    cnt : countV oddᶻ (⟦ gs ⟧ᵛ ρ) ≡ c
    cnt = ≡.trans (≡.sym (noddV-countV (⟦ gs ⟧ᵛ ρ))) (noddF-sound gs nd ρ)
    at : ∀ b → (if b then c₁ else oddℕ c xor c₁) ≡ true → oddℕ (countV (Pκ (just b)) (⟦ gs ⟧ᵛ ρ)) ≡ true
    at true e′ = ≡.trans cnt1 e′
    at false e′ = ≡.trans (odd-count-cls0 (⟦ gs ⟧ᵛ ρ)) (≡.trans (≡.cong₂ _xor_ (≡.cong oddℕ cnt) cnt1) e′)
  countOK-sound (just b) gs () ρ | just c | nothing
  countOK-sound (just b) gs () ρ | nothing | _

------------------------------------------------------------------------
-- Minimality puts the entries outside the window deep

private
  pairOK-sound : ∀ {m r} δ′ (tags : Vec (Maybe ℕ) m) (fs : Vec (Form r) m) a b → pairOK δ′ tags fs (a , b) ≡ true →
                 tags ! a ≡ just δ′ × tags ! b ≡ just δ′ ×
                 ∃₂ λ qa qb → halfFⁿ δ′ (fs ! a) ≡ just qa × halfFⁿ δ′ (fs ! b) ≡ just qb × clsF (qa ⊕ qb) ≡ just true
  pairOK-sound δ′ tags fs a b e with tags ! a in ta | tags ! b in tb | halfFⁿ δ′ (fs ! a) in ha | halfFⁿ δ′ (fs ! b) in hb
  ... | just δa | just δb | just qa | just qb =
    ≡.cong just (ℕP.≡ᵇ⇒≡ δa δ′ (T′ (fst (δa ℕ.≡ᵇ δ′) e))) ,
    ≡.cong just (ℕP.≡ᵇ⇒≡ δb δ′ (T′ (fst (δb ℕ.≡ᵇ δ′) (snd (δa ℕ.≡ᵇ δ′) e)))) ,
    qa , qb , ≡.refl , ≡.refl , jt (clsF (qa ⊕ qb)) (snd (δb ℕ.≡ᵇ δ′) (snd (δa ℕ.≡ᵇ δ′) e))
    where
    open import Data.Bool.Base using (T)
    T′ : ∀ {x} → x ≡ true → T x
    T′ ≡.refl = _
    jt : ∀ c → isJustTrue c ≡ true → c ≡ just true
    jt (just true) _ = ≡.refl
  pairOK-sound δ′ tags fs a b () | just _ | just _ | just _ | nothing
  pairOK-sound δ′ tags fs a b () | just _ | just _ | nothing | _
  pairOK-sound δ′ tags fs a b () | just _ | nothing | _ | _
  pairOK-sound δ′ tags fs a b () | nothing | _ | _ | _

  pairs-get : ∀ {m r} (k : ℕ) (tags : Vec (Maybe ℕ) m) (fs : Vec (Form r) m) (ps : List (Fin m × Fin m)) →
              pairsOK k tags fs ps ≡ true → ∀ δ′ → k ℕ.≤ δ′ → δ′ ℕ.< k ℕ.+ length ps →
              ∃₂ λ a b → pairOK δ′ tags fs (a , b) ≡ true
  pairs-get k tags fs [] e δ′ kδ lt = ⊥-elim (ℕP.<-irrefl ≡.refl (ℕP.<-≤-trans lt (≡.subst (ℕ._≤ δ′) (≡.sym (ℕP.+-identityʳ k)) kδ)))
  pairs-get k tags fs ((a , b) ∷ ps) e δ′ kδ lt with k ℕP.≟ δ′
  ... | yes ≡.refl = a , b , fst (pairOK k tags fs (a , b)) e
  ... | no k≢δ′ = pairs-get (suc k) tags fs ps (snd (pairOK k tags fs (a , b)) e) δ′ (ℕP.≤∧≢⇒< kδ k≢δ′)
                    (≡.subst (δ′ ℕ.<_) (ℕP.+-suc k (length ps)) lt)

  xor-cases : ∀ c a b → a xor b ≡ true → c ≡ a ⊎ c ≡ b
  xor-cases false false true _ = inj₁ ≡.refl
  xor-cases false true false _ = inj₂ ≡.refl
  xor-cases true false true _ = inj₂ ≡.refl
  xor-cases true true false _ = inj₁ ≡.refl

deep-out : ∀ {m r} s (w : Win m s) (tags : Vec (Maybe ℕ) m) (fs : Vec (Form r) m) ρ → ⟦ fs ⟧ᵛ ρ ≡ locW w →
           TagsOK s w tags → Minimal s → ∀ δ (ps : List (Fin m × Fin m)) → pairsOK 1 tags fs ps ≡ true →
           suc (length ps) ≡ δ → δ ℕ.≤ 3 →
           ∀ e → e ℕ.≤ δ → ∀ x → (∀ i → ι w i ≢ x) → ∃ λ y → Wn s ! x ≡ (√2ᶻ ^ᶻ e) ZR.* y
deep-out s w tags fs ρ eqv tg mn δ ps pok len δ3 zero _ x ox = Wn s ! x , ≡.sym (ZR.*-identityˡ (Wn s ! x))
deep-out s w tags fs ρ eqv tg mn δ ps pok len δ3 (suc e) e<δ x ox = step (deep-out s w tags fs ρ eqv tg mn δ ps pok len δ3 e (ℕP.<⇒≤ e<δ) x ox)
  where
  contra : ∀ e (y′ : Z) → suc e ℕ.≤ δ → Wn s ! x ≡ (√2ᶻ ^ᶻ e) ZR.* y′ → oddᶻ y′ ≡ true → ⊥
  contra zero y′ _ ey′ oy′ =
    t≢f (≡.trans (≡.sym oy′) (≡.trans (≡.cong oddᶻ (≡.trans (≡.sym (ZR.*-identityˡ y′)) (≡.sym ey′))) (out w x ox)))
  contra (suc e₀) y′ lt ey′ oy′ = at (pairs-get 1 tags fs ps pok (suc e₀) (ℕ.s≤s ℕ.z≤n) (≡.subst (suc e₀ ℕ.<_) (≡.sym len) lt))
    where
    e₁ = suc e₀
    e₁≤2 : e₁ ℕ.≤ 2
    e₁≤2 = ℕP.≤-pred (ℕP.≤-trans lt δ3)
    quot : ∀ a qa → halfFⁿ e₁ (fs ! a) ≡ just qa → Deep (Wn s ! ι w a) e₁ → ∃ λ ya → Wn s ! ι w a ≡ (√2ᶻ ^ᶻ e₁) ZR.* ya × oddᶻ ya ≡ true × ya ≡ ⟦ qa ⟧ ρ
    quot a qa ha (ya , eya , oya) = ya , eya , oya ,
      pow-cancel e₁ ya (⟦ qa ⟧ ρ) (≡.trans (≡.sym eya) (≡.trans val (halfFⁿ-sound e₁ (fs ! a) ha ρ)))
      where
      val : Wn s ! ι w a ≡ ⟦ fs ! a ⟧ ρ
      val = ≡.trans (≡.sym (VecP.lookup∘tabulate (λ i → Wn s ! ι w i) a)) (≡.trans (≡.cong (_! a) (≡.sym eqv)) (⟦⟧ᵛ-! fs ρ a))
    differ : ∀ {ya yb qa qb} → ya ≡ ⟦ qa ⟧ ρ → yb ≡ ⟦ qb ⟧ ρ → clsF (qa ⊕ qb) ≡ just true → rbit ya xor rbit yb ≡ true
    differ {ya} {yb} {qa} {qb} qa≡ qb≡ cl = ≡.trans (≡.sym (rbit-+ ya yb))
      (≡.trans (≡.cong rbit (≡.trans (≡.cong₂ ZR._+_ qa≡ qb≡) (≡.sym (⟦⊕⟧ qa qb ρ)))) (clsF-sound (qa ⊕ qb) cl ρ))
    pick : ∀ a b ya yb → rbit y′ ≡ rbit ya ⊎ rbit y′ ≡ rbit yb →
           Wn s ! ι w a ≡ (√2ᶻ ^ᶻ e₁) ZR.* ya → oddᶻ ya ≡ true → Wn s ! ι w b ≡ (√2ᶻ ^ᶻ e₁) ZR.* yb → oddᶻ yb ≡ true → ⊥
    pick a b ya yb (inj₁ ca) eya oya eyb oyb = mn e₁ (ℕ.s≤s ℕ.z≤n) e₁≤2 x (ι w a) y′ ya (λ p → ox a (≡.sym p)) ey′ eya oy′ oya ca
    pick a b ya yb (inj₂ cb) eya oya eyb oyb = mn e₁ (ℕ.s≤s ℕ.z≤n) e₁≤2 x (ι w b) y′ yb (λ p → ox b (≡.sym p)) ey′ eyb oy′ oyb cb
    both : ∀ a b qa qb → clsF (qa ⊕ qb) ≡ just true →
           (∃ λ ya → Wn s ! ι w a ≡ (√2ᶻ ^ᶻ e₁) ZR.* ya × oddᶻ ya ≡ true × ya ≡ ⟦ qa ⟧ ρ) →
           (∃ λ yb → Wn s ! ι w b ≡ (√2ᶻ ^ᶻ e₁) ZR.* yb × oddᶻ yb ≡ true × yb ≡ ⟦ qb ⟧ ρ) → ⊥
    both a b qa qb cl (ya , eya , oya , qa≡) (yb , eyb , oyb , qb≡) =
      pick a b ya yb (xor-cases (rbit y′) (rbit ya) (rbit yb) (differ {ya} {yb} {qa} {qb} qa≡ qb≡ cl)) eya oya eyb oyb
    facts : ∀ a b → (tags ! a ≡ just e₁ × tags ! b ≡ just e₁ ×
                     ∃₂ λ qa qb → halfFⁿ e₁ (fs ! a) ≡ just qa × halfFⁿ e₁ (fs ! b) ≡ just qb × clsF (qa ⊕ qb) ≡ just true) → ⊥
    facts a b (ta , tb , qa , qb , ha , hb , cl) = both a b qa qb cl (quot a qa ha (tg a e₁ ta)) (quot b qb hb (tg b e₁ tb))
    at : (∃₂ λ a b → pairOK e₁ tags fs (a , b) ≡ true) → ⊥
    at (a , b , pab) = facts a b (pairOK-sound e₁ tags fs a b pab)
  step : (∃ λ y → Wn s ! x ≡ (√2ᶻ ^ᶻ e) ZR.* y) → ∃ λ y → Wn s ! x ≡ (√2ᶻ ^ᶻ suc e) ZR.* y
  step (y′ , ey′) = by (oddᶻ y′) ≡.refl
    where
    by : ∀ b → oddᶻ y′ ≡ b → ∃ λ y → Wn s ! x ≡ (√2ᶻ ^ᶻ suc e) ZR.* y
    by true oy = ⊥-elim (contra e y′ e<δ ey′ oy)
    by false oy = from (even⇒δ∣ y′ oy)
      where
      from : (∃ λ y″ → y′ ≡ √2ᶻ ZR.* y″) → ∃ λ y → Wn s ! x ≡ (√2ᶻ ^ᶻ suc e) ZR.* y
      from (y″ , e″) = y″ , ≡.trans ey′ (≡.trans (≡.cong ((√2ᶻ ^ᶻ e) ZR.*_) e″)
                              (ZG.solve 2 (λ c y → c :* (con √2ᶻ :* y) := (con √2ᶻ :* c) :* y) ≡.refl (√2ᶻ ^ᶻ e) y″))

------------------------------------------------------------------------
-- Steps on values

private
  caseM-true : ∀ {A : Set} (m : Maybe A) (k : A → Bool) → caseM m false k ≡ true → ∃ λ a → m ≡ just a × k a ≡ true
  caseM-true (just a) k e = a , ≡.refl , e
  caseM-true nothing k ()

  z-vals : ∀ {m} {j : Fin m} {e e′ : Vec Z m} → Step (Zˡ j) e e′ → ∀ i → e′ ! i ≡ e ! i ⊎ e′ ! i ≡ ZR.- (e ! i)
  z-vals {j = j} {e} stepZ i = at (i FinP.≟ j)
    where
    at : _ → updA₁ j (ZR.- (e ! j)) e ! i ≡ e ! i ⊎ updA₁ j (ZR.- (e ! j)) e ! i ≡ ZR.- (e ! i)
    at (yes ≡.refl) = inj₂ (upd₁-i i (ZR.- (e ! i)) e)
    at (no i≢j) = inj₁ (upd₁-o j (ZR.- (e ! j)) e i≢j)

  h-vals : ∀ {m} {u v : Fin m} {e e′ : Vec Z m} → Step (Hˡ u v) e e′ → ∀ i → i ≢ u → i ≢ v → e′ ! i ≡ e ! i
  h-vals {e = e} (stepH α β _ _) i iu iv = upd₂-o _ _ α β e iu iv

  upd-tags : ∀ {m} (tags : Vec (Maybe ℕ) m) u v i {δ} → ((tags [ u ]≔ nothing) [ v ]≔ nothing) ! i ≡ just δ →
             i ≢ u × i ≢ v × tags ! i ≡ just δ
  upd-tags tags u v i {δ} e = at (i FinP.≟ v) (i FinP.≟ u)
    where
    nj : nothing ≢ just δ
    nj ()
    at : _ → _ → i ≢ u × i ≢ v × tags ! i ≡ just δ
    at (yes ≡.refl) _ = ⊥-elim (nj (≡.trans (≡.sym (VecP.lookup∘update i (tags [ u ]≔ nothing) nothing)) e))
    at (no i≢v) (yes ≡.refl) =
      ⊥-elim (nj (≡.trans (≡.sym (≡.trans (VecP.lookup∘update′ i≢v (tags [ i ]≔ nothing) nothing) (VecP.lookup∘update i tags nothing))) e))
    at (no i≢v) (no i≢u) =
      i≢u , i≢v , ≡.trans (≡.sym (≡.trans (VecP.lookup∘update′ i≢v (tags [ u ]≔ nothing) nothing) (VecP.lookup∘update′ i≢u tags nothing))) e

  atL?-sound : ∀ {m r} (fs : Vec (Form r) m) → atL? (just fs) ≡ true → kindF fs ≡ just atL
  atL?-sound fs e with caseM-true (kindF fs) isAtL e
  ... | atL , k , _ = k
  atL?-sound fs e | low , k , ()

  if-sw : ∀ {A : Set} (sw : Bool) (x y : A) → (if sw then x else y) ≡ x ⊎ (if sw then x else y) ≡ y
  if-sw true x y = inj₁ ≡.refl
  if-sw false x y = inj₂ ≡.refl

------------------------------------------------------------------------
-- The induction

module Main (nfData : (nf : NF) → NFData nf) (allow : NF → Bool) (nfThm : ∀ nf → allow nf ≡ true → NFThm nfData nf) where

  open Checker nfData allow

  -- The goal at a node.
  Goal : ∀ {m} (s : Matrix n n D) .(o : ColOrth s) → Win m s → Fin m → Fin m → Set
  Goal s o w ic id = Path (Hs (ι w ic) (ι w id)) s o


  ----------------------------------------------------------------------
  -- conj: the edge g out of s, and out of Hs ic id · s, and the square

  conj-case : ∀ {m r} (g : Let m) tags mini (ic id : Fin m) (fs fs′ fcd : Vec (Form r) m) ρ → ic ≢ id →
    stepF g fs ≡ just fs′ → stepF (Hˡ ic id) fs ≡ just fcd → apart ic id g ≡ true → check (g ∷ []) fs ≡ true →
    kindF fs′ ≡ just atL → check (conjLetter ic id g ∷ []) fcd ≡ true →
    ∀ s .(o : ColOrth s) (eq : level s ≡ L) (w : Win m s) → ⟦ fs ⟧ᵛ ρ ≡ locW w → TagsOK s w tags → (mini ≡ true → Minimal s) →
    (∀ N .(oN : ColOrth N) (eqN : level N ≡ L) (wN : Win m N) → ι wN ≡ ι w → ⟦ fs′ ⟧ᵛ ρ ≡ locW wN →
       (∀ x → (∀ i → ι w i ≢ x) → Wn N ! x ≡ Wn s ! x) →
       TagsOK N wN (tagsAfter g tags) → (miniAfter g mini ≡ true → Minimal N) → Goal N oN wN ic id) →
    Goal s o w ic id
  conj-case g tags mini ic id fs fs′ fcd ρ icd st sc ap cg ka cl s o eq w eqv tg mn rec =
    via-w (Hs (ι w ic) (ι w id)) s o (wordL g′) (Hs (ι w ic) (ι w id) • wordL g) pG′ (rel g ap dg)
      (path-• (Hs (ι w ic) (ι w id)) (wordL g) s o recN pG)
    where
    open At-window s o eq w
    g′ = conjLetter ic id g
    ι≢ : ∀ {i j} → i ≢ j → ι w i ≢ ι w j
    ι≢ ne e = ne (inj w e)
    K = known-at fs ρ eqv
    dg : Distinct g
    dg = check-distinct g [] fs cg
    stp = stepF-sound g fs st ρ
    K′ = known-step g dg stp K
    N = actMʷ (wordL g) s
    four : noddV (⟦ fs′ ⟧ᵛ ρ) ≡ 4
    four = proj₂ (kindF-sound fs′ ka ρ) ≡.refl
    eqN : level N ≡ L
    eqN = At-L.levelL K′ four
    module NX = Next K′ (ColOrth-actMʷ (wordL g) o) eqN
    s-vals : ∀ i → (⟦ fs ⟧ᵛ ρ) ! i ≡ Wn s ! ι w i
    s-vals i = ≡.trans (≡.cong (_! i) eqv) (VecP.lookup∘tabulate (λ i → Wn s ! ι w i) i)
    -- Tags and minimality after g.
    z-deep : ∀ i δ → (⟦ fs′ ⟧ᵛ ρ) ! i ≡ (⟦ fs ⟧ᵛ ρ) ! i ⊎ (⟦ fs′ ⟧ᵛ ρ) ! i ≡ ZR.- ((⟦ fs ⟧ᵛ ρ) ! i) →
             Deep (Wn s ! ι w i) δ → Deep (Wn N ! ι w i) δ
    z-deep i δ (inj₁ e) d = ≡.subst (λ z → Deep z δ) (≡.sym (≡.trans (NX.inside i) (≡.trans e (s-vals i)))) d
    z-deep i δ (inj₂ e) d = ≡.subst (λ z → Deep z δ) (≡.sym (≡.trans (NX.inside i) (≡.trans e (≡.cong ZR.-_ (s-vals i))))) (deep-neg {Wn s ! ι w i} {δ} d)
    h-deep : ∀ {u v} → Step (Hˡ u v) (⟦ fs ⟧ᵛ ρ) (⟦ fs′ ⟧ᵛ ρ) → ∀ i δ → i ≢ u × i ≢ v × tags ! i ≡ just δ → Deep (Wn N ! ι w i) δ
    h-deep stp′ i δ (iu , iv , ti′) =
      ≡.subst (λ z → Deep z δ) (≡.sym (≡.trans (NX.inside i) (≡.trans (h-vals stp′ i iu iv) (s-vals i)))) (tg i δ ti′)
    tags-after : ∀ g → apart ic id g ≡ true → Step g (⟦ fs ⟧ᵛ ρ) (⟦ fs′ ⟧ᵛ ρ) → TagsOK N NX.win′ (tagsAfter g tags)
    tags-after (Zˡ j) _ stp′ i δ ti = z-deep i δ (z-vals stp′ i) (tg i δ ti)
    tags-after (Hˡ u v) _ stp′ i δ ti = h-deep stp′ i δ (upd-tags tags u v i ti)
    tags-after (Xˡ a b) () stp′
    z-pm : ∀ {j} → Step (Zˡ j) (⟦ fs ⟧ᵛ ρ) (⟦ fs′ ⟧ᵛ ρ) → ∀ x → (∃ λ i → ι w i ≡ x) ⊎ (∀ i → ι w i ≢ x) →
           Wn N ! x ≡ Wn s ! x ⊎ Wn N ! x ≡ ZR.- (Wn s ! x)
    z-pm stp′ x (inj₁ (i , ≡.refl)) = sgn (z-vals stp′ i)
      where
      sgn : (⟦ fs′ ⟧ᵛ ρ) ! i ≡ (⟦ fs ⟧ᵛ ρ) ! i ⊎ (⟦ fs′ ⟧ᵛ ρ) ! i ≡ ZR.- ((⟦ fs ⟧ᵛ ρ) ! i) →
            Wn N ! ι w i ≡ Wn s ! ι w i ⊎ Wn N ! ι w i ≡ ZR.- (Wn s ! ι w i)
      sgn (inj₁ e) = inj₁ (≡.trans (NX.inside i) (≡.trans e (s-vals i)))
      sgn (inj₂ e) = inj₂ (≡.trans (NX.inside i) (≡.trans e (≡.cong ZR.-_ (s-vals i))))
    z-pm stp′ x (inj₂ o′) = inj₁ (NX.outside x o′)
    mini-after : ∀ g → apart ic id g ≡ true → Step g (⟦ fs ⟧ᵛ ρ) (⟦ fs′ ⟧ᵛ ρ) → miniAfter g mini ≡ true → Minimal N
    mini-after (Zˡ j) _ stp′ m≡ = minimal-± {N} {s} (λ x → z-pm stp′ x (Emb.where? (ι w) (inj w) x)) (mn m≡)
    mini-after (Hˡ u v) _ stp′ ()
    mini-after (Xˡ a b) () stp′ m≡
    recN : Path (Hs (ι w ic) (ι w id)) N (ColOrth-actMʷ (wordL g) o)
    recN = rec N (ColOrth-actMʷ (wordL g) o) eqN NX.win′ ≡.refl NX.loc′ NX.outside (tags-after g ap stp) (mini-after g ap stp)
    pG : Path (wordL g) s o
    pG = letter g fs ρ o cg K
    Kcd = known-step (Hˡ ic id) icd (stepF-sound (Hˡ ic id) fs sc ρ) K
    pG′ : Path (wordL g′) (actMʷ (Hs (ι w ic) (ι w id)) s) (ColOrth-actMʷ (Hs (ι w ic) (ι w id)) o)
    pG′ = letter g′ fcd ρ (ColOrth-actMʷ (Hs (ι w ic) (ι w id)) o) cl Kcd
    -- The square: g′ Hs = Hs g.
    zrel : ∀ j (b : Bool) → (j == id) ≡ b → (j == ic) ≡ false →
           wordL (if b then Xˡ ic id else Zˡ j) • Hs (ι w ic) (ι w id) ≈ Hs (ι w ic) (ι w id) • Zʷ (ι w j)
    zrel j true e _ = ≡.subst (λ x → Xs (ι w ic) (ι w id) • Hs (ι w ic) (ι w id) ≈ Hs (ι w ic) (ι w id) • Zʷ (ι w x))
                              (≡.sym (==-sound e)) (XH′ (ι≢ icd))
    zrel j false e jc = ZH (ι≢ icd) (ι≢ (==-false jc)) (ι≢ (==-false e))
    rel : ∀ g → apart ic id g ≡ true → Distinct g → wordL (conjLetter ic id g) • Hs (ι w ic) (ι w id) ≈ Hs (ι w ic) (ι w id) • wordL g
    rel (Zˡ j) a _ = zrel j (j == id) ≡.refl (not-t a)
    rel (Hˡ u v) a uv =
      Hs-comm (ι≢ uv) (ι≢ icd) (ι≢ (==-false (not-t (fst (not (u == ic)) a))))
        (ι≢ (==-false (not-t (fst (not (u == id)) (snd (not (u == ic)) a)))))
        (ι≢ (==-false (not-t (fst (not (v == ic)) (snd (not (u == id)) (snd (not (u == ic)) a))))))
        (ι≢ (==-false (not-t (snd (not (v == ic)) (snd (not (u == id)) (snd (not (u == ic)) a))))))
    rel (Xˡ a b) () _

  ----------------------------------------------------------------------
  -- extend: an entry outside the window, at depth δ

  extend-case : ∀ {m r} δ κ (R : Route m) a b c d (ps : List (Fin m × Fin m)) tags (ic id : Fin m) (fs : Vec (Form r) m) fsR gs ρ →
    runF R fs ≡ just fsR → halfVⁿ δ fsR ≡ just gs → (δ ℕ.≤ᵇ 3) ≡ true → (suc (length ps) ℕ.≡ᵇ δ) ≡ true →
    pairsOK 1 tags fs ps ≡ true → certOK gs a b c d ≡ true → countOK κ gs ≡ true →
    ∀ s .(o : ColOrth s) (eq : level s ≡ L) (w : Win m s) → ⟦ fs ⟧ᵛ ρ ≡ locW w → TagsOK s w tags → Minimal s →
    (∀ (ρ′ : Vec Z (suc r)) (w′ : Win (suc m) s) → ⟦ newF δ κ ∷ Vec.map liftF fs ⟧ᵛ ρ′ ≡ locW w′ →
       TagsOK s w′ (just δ ∷ tags) → Goal s o w′ (suc ic) (suc id)) →
    Goal s o w ic id
  extend-case δ κ R a b c d ps tags ic id fs fsR gs ρ rr hh le3 ln pok cert cnt s o eq w eqv tg mn rec =
    found (Extra.extra (ι w) (inj w) (ColOrth-actMʷ (wordRι R) o) k (⟦ fsR ⟧ᵛ ρ) (Wn s) (colK KR) δ (⟦ gs ⟧ᵛ ρ) eg div
             (certOK-sound gs a b c d cert ρ) κ (countOK-sound κ gs cnt ρ))
    where
    open At-window s o eq w
    open import Data.Bool.Base using (T)
    T′ : ∀ {x} → x ≡ true → T x
    T′ ≡.refl = _
    K = known-at fs ρ eqv
    KR = run-known R fs rr ρ K
    eg : ∀ i → (⟦ fsR ⟧ᵛ ρ) ! i ≡ (√2ᶻ ^ᶻ δ) ZR.* ((⟦ gs ⟧ᵛ ρ) ! i)
    eg i = ≡.trans (⟦⟧ᵛ-! fsR ρ i) (≡.trans (halfVⁿ-sound δ fsR hh ρ i) (≡.cong ((√2ᶻ ^ᶻ δ) ZR.*_) (≡.sym (⟦⟧ᵛ-! gs ρ i))))
    δ3 : δ ℕ.≤ 3
    δ3 = ℕP.≤ᵇ⇒≤ δ 3 (T′ le3)
    len : suc (length ps) ≡ δ
    len = ℕP.≡ᵇ⇒≡ (suc (length ps)) δ (T′ ln)
    div : ∀ x → (∀ i → ι w i ≢ x) → ∃ λ y → Wn s ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y
    div = deep-out s w tags fs ρ eqv tg mn δ ps pok len δ3 δ ℕP.≤-refl
    found : (∃ λ x → (∀ i → ι w i ≢ x) × ∃ λ y → Wn s ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y × Pκ κ y ≡ true) → Goal s o w ic id
    found (x , ox , y , ey , py) = rec (proj₁ nv ∷ ρ) w′ eqv′ tg′
      where
      oy : oddᶻ y ≡ true
      oy = Pκ-odd κ y py
      x≤p : x ≤ p
      x≤p = ℕP.≮⇒≥ λ p<x → pow-odd-≢0 δ y oy (≡.trans (≡.sym ey) (State.zero> s o eq x p<x))
      ι′ : Fin (suc _) → Fin n
      ι′ zero = x
      ι′ (suc i) = ι w i
      inj′ : ∀ {i j} → ι′ i ≡ ι′ j → i ≡ j
      inj′ {zero} {zero} _ = ≡.refl
      inj′ {zero} {suc j} e = ⊥-elim (ox j (≡.sym e))
      inj′ {suc i} {zero} e = ⊥-elim (ox i e)
      inj′ {suc i} {suc j} e = ≡.cong suc (inj w e)
      ι≤p′ : ∀ i → ι′ i ≤ p
      ι≤p′ zero = x≤p
      ι≤p′ (suc i) = ι≤p w i
      w′ : Win (suc _) s
      w′ = win ι′ inj′ ι≤p′ (λ z o′ → out w z (λ i → o′ (suc i)))
      nv = new-val δ κ y py
      lifted : ⟦ Vec.map liftF fs ⟧ᵛ (proj₁ nv ∷ ρ) ≡ ⟦ fs ⟧ᵛ ρ
      lifted = ≡.trans (≡.sym (VecP.map-∘ (λ f → ⟦ f ⟧ (proj₁ nv ∷ ρ)) liftF fs)) (VecP.map-cong (λ f → ⟦liftF⟧ f (proj₁ nv) ρ) fs)
      eqv′ : ⟦ newF δ κ ∷ Vec.map liftF fs ⟧ᵛ (proj₁ nv ∷ ρ) ≡ locW w′
      eqv′ = ≡.cong₂ _∷_ (≡.trans (proj₂ nv ρ) (≡.sym ey)) (≡.trans lifted eqv)
      tg′ : TagsOK s w′ (just δ ∷ tags)
      tg′ zero δ′ ≡.refl = y , ey , oy
      tg′ (suc i) δ′ ti = tg i δ′ ti

  ----------------------------------------------------------------------
  -- relabel: a permutation of the window

  relabel-case : ∀ {m r} (π : Vec (Fin m) m) sw (ic′ id′ : Fin m) tags (ic id : Fin m) (fs : Vec (Form r) m) ρ → ic ≢ id →
    distinctV π ≡ true → ontoV π ≡ true → (π ! ic′ == (if sw then id else ic)) ≡ true → (π ! id′ == (if sw then ic else id)) ≡ true →
    (if sw then flipOK ic id fs else true) ≡ true →
    ∀ s .(o : ColOrth s) (eq : level s ≡ L) (w : Win m s) → ⟦ fs ⟧ᵛ ρ ≡ locW w → TagsOK s w tags →
    (∀ (w′ : Win m s) → ⟦ Vec.map (fs !_) π ⟧ᵛ ρ ≡ locW w′ → TagsOK s w′ (Vec.map (tags !_) π) → ic′ ≢ id′ →
       Goal s o w′ ic′ id′) →
    Goal s o w ic id
  relabel-case π sw ic′ id′ tags ic id fs ρ icd di on e1 e2 fl s o eq w eqv tg rec = finish sw e1 e2 fl
    where
    open At-window s o eq w
    πinj = distinctV-sound π di
    πonto = ontoV-sound π on
    w′ : Win _ s
    w′ = win (λ i → ι w (π ! i)) (λ e → πinj (inj w e)) (λ i → ι≤p w (π ! i))
             (λ x o′ → out w x (λ j e → let (i , pi) = πonto j in o′ i (≡.trans (≡.cong (ι w) pi) e)))
    s-vals : ∀ i → (⟦ fs ⟧ᵛ ρ) ! i ≡ Wn s ! ι w i
    s-vals i = ≡.trans (≡.cong (_! i) eqv) (VecP.lookup∘tabulate (λ i → Wn s ! ι w i) i)
    eqv′ : ⟦ Vec.map (fs !_) π ⟧ᵛ ρ ≡ locW w′
    eqv′ = vec-ext λ i →
      ≡.trans (⟦⟧ᵛ-! (Vec.map (fs !_) π) ρ i)
        (≡.trans (≡.cong (λ f → ⟦ f ⟧ ρ) (VecP.lookup-map i (fs !_) π))
          (≡.trans (≡.sym (⟦⟧ᵛ-! fs ρ (π ! i))) (≡.trans (s-vals (π ! i)) (≡.sym (VecP.lookup∘tabulate (λ i → Wn s ! ι w (π ! i)) i)))))
    tg′ : TagsOK s w′ (Vec.map (tags !_) π)
    tg′ i δ ti = tg (π ! i) δ (≡.trans (≡.sym (VecP.lookup-map i (tags !_) π)) ti)
    icd′ : ∀ {x y} → x ≢ y → π ! ic′ ≡ x → π ! id′ ≡ y → ic′ ≢ id′
    icd′ xy ex ey ≡.refl = xy (≡.trans (≡.sym ex) ey)
    finish : ∀ sw → (π ! ic′ == (if sw then id else ic)) ≡ true → (π ! id′ == (if sw then ic else id)) ≡ true →
             (if sw then flipOK ic id fs else true) ≡ true → Goal s o w ic id
    finish false e1 e2 _ =
      ≡.subst₂ (λ x y → Path (Hs (ι w x) (ι w y)) s o) (==-sound e1) (==-sound e2)
        (rec w′ eqv′ tg′ (icd′ icd (==-sound e1) (==-sound e2)))
    finish true e1 e2 fo = path-cong rel s o (path-• (wordRι (Zˡ ic ∷ Xˡ id ic ∷ [])) (Hs (ι w id) (ι w ic)) s o p2 recr)
      where
      recr : Path (Hs (ι w id) (ι w ic)) s o
      recr = ≡.subst₂ (λ x y → Path (Hs (ι w x) (ι w y)) s o) (==-sound e1) (==-sound e2)
               (rec w′ eqv′ tg′ (icd′ (λ e → icd (≡.sym e)) (==-sound e1) (==-sound e2)))
      fN = caseM-true (stepF (Hˡ id ic) fs) _ fo
      Kdc = known-step (Hˡ id ic) (λ e → icd (≡.sym e)) (stepF-sound (Hˡ id ic) fs (proj₁ (proj₂ fN)) ρ) (known-at fs ρ eqv)
      p2 : Path (wordRι (Zˡ ic ∷ Xˡ id ic ∷ [])) (actMʷ (Hs (ι w id) (ι w ic)) s) (ColOrth-actMʷ (Hs (ι w id) (ι w ic)) o)
      p2 = route-path (Zˡ ic ∷ Xˡ id ic ∷ []) (proj₁ fN) ρ (ColOrth-actMʷ (Hs (ι w id) (ι w ic)) o) (proj₂ (proj₂ fN)) Kdc
      rel : wordRι (Zˡ ic ∷ Xˡ id ic ∷ []) • Hs (ι w id) (ι w ic) ≈ Hs (ι w ic) (ι w id)
      rel = begin
        ((ε • Xs (ι w id) (ι w ic)) • Zʷ (ι w ic)) • Hs (ι w id) (ι w ic)   ≈⟨ cleft cleft left-unit ⟩
        (Xs (ι w id) (ι w ic) • Zʷ (ι w ic)) • Hs (ι w id) (ι w ic)         ≈⟨ assoc ⟩
        Xs (ι w id) (ι w ic) • Zʷ (ι w ic) • Hs (ι w id) (ι w ic)           ≈⟨ XZH′ (λ e → icd (inj w (≡.sym e))) ⟩
        Hs (ι w ic) (ι w id)                                                ∎

  ----------------------------------------------------------------------
  -- useNF: the normal form's theorem

  use-case : ∀ {r} nf (τ : Vec (Form r) (nfVars nf)) tags mini (ic id : Fin (nfRows nf)) (fs : Vec (Form r) (nfRows nf)) ρ → ic ≢ id →
    allow nf ≡ true → (ic == NFData.ic (nfData nf)) ≡ true → (id == NFData.id (nfData nf)) ≡ true →
    eqTags tags (NFData.tags (nfData nf)) ≡ true → (if NFData.mini (nfData nf) then mini else true) ≡ true →
    eqFs (Vec.map (λ f → compF f τ) (NFData.forms (nfData nf))) fs ≡ true →
    ∀ s .(o : ColOrth s) (eq : level s ≡ L) (w : Win (nfRows nf) s) → ⟦ fs ⟧ᵛ ρ ≡ locW w → TagsOK s w tags →
    (mini ≡ true → Minimal s) → Goal s o w ic id
  use-case nf τ tags mini ic id fs ρ icd al eic eid etg emi efs s o eq w eqv tg mn =
    ≡.subst₂ (λ x y → Path (Hs (ι w x) (ι w y)) s o) (≡.sym (==-sound eic)) (≡.sym (==-sound eid))
      (nfThm nf al s o eq w (⟦ τ ⟧ᵛ ρ) eqvNF (≡.subst (TagsOK s w) (eqTags-sound tags _ etg) tg) (mini-of (NFData.mini (nfData nf)) emi)
        (λ e → icd (≡.trans (==-sound eic) (≡.trans e (≡.sym (==-sound eid))))))
    where
    eqvNF : ⟦ NFData.forms (nfData nf) ⟧ᵛ (⟦ τ ⟧ᵛ ρ) ≡ locW w
    eqvNF = ≡.trans (VecP.map-cong (λ f → ≡.sym (⟦compF⟧ f τ ρ)) (NFData.forms (nfData nf)))
              (≡.trans (VecP.map-∘ (λ f → ⟦ f ⟧ ρ) (λ f → compF f τ) (NFData.forms (nfData nf)))
                (≡.trans (≡.cong (λ fs → ⟦ fs ⟧ᵛ ρ) (eqFs-sound _ fs efs)) eqv))
    mini-of : ∀ b → (if b then mini else true) ≡ true → b ≡ true → Minimal s
    mini-of true e _ = mn e

  ----------------------------------------------------------------------
  -- The induction

  sound : ∀ {m r} (t : Tree m r) (tags : Vec (Maybe ℕ) m) (mini : Bool) (ic id : Fin m) (fs : Vec (Form r) m) (ρ : Vec Z r) →
          checkT t tags mini ic id fs ≡ true → ic ≢ id →
          ∀ s .(o : ColOrth s) (eq : level s ≡ L) (w : Win m s) →
          ⟦ fs ⟧ᵛ ρ ≡ locW w → TagsOK s w tags → (mini ≡ true → Minimal s) → Goal s o w ic id
  sound (leaf ld) tags mini ic id fs ρ chk icd s o eq w eqv tg mn =
    leaf-path ld ic id fs ρ (fst (leafOK ic id ld) chk) (snd (leafOK ic id ld) chk) s o eq w eqv
  sound (split v g t₀ t₁) tags mini ic id fs ρ chk icd s o eq w eqv tg mn = branch (split-sound v g one ρ)
    where
    one = fst (isOne (co g ! v)) chk
    c₀ = fst (checkT t₀ tags mini ic id (Vec.map (substF v (splitH v g false)) fs)) (snd (isOne (co g ! v)) chk)
    c₁ = snd (checkT t₀ tags mini ic id (Vec.map (substF v (splitH v g false)) fs)) (snd (isOne (co g ! v)) chk)
    vals : ∀ b ρ′ → (∀ f → ⟦ substF v (splitH v g b) f ⟧ ρ′ ≡ ⟦ f ⟧ ρ) → ⟦ Vec.map (substF v (splitH v g b)) fs ⟧ᵛ ρ′ ≡ locW w
    vals b ρ′ h = ≡.trans (≡.trans (≡.sym (VecP.map-∘ (λ f → ⟦ f ⟧ ρ′) (substF v (splitH v g b)) fs)) (VecP.map-cong h fs)) eqv
    branch : (∃₂ λ b ρ′ → ∀ f → ⟦ substF v (splitH v g b) f ⟧ ρ′ ≡ ⟦ f ⟧ ρ) → Goal s o w ic id
    branch (false , ρ′ , h) = sound t₀ tags mini ic id _ ρ′ c₀ icd s o eq w (vals false ρ′ h) tg mn
    branch (true , ρ′ , h) = sound t₁ tags mini ic id _ ρ′ c₁ icd s o eq w (vals true ρ′ h) tg mn
  sound (extend δ κ R a b c d ps t) tags mini ic id fs ρ chk icd s o eq w eqv tg mn =
    go (caseM-true (runF R fs) _ (fst (extOK δ κ R a b c d ps tags fs) (snd mini chk)))
    where
    m≡ = fst mini chk
    ct = snd (extOK δ κ R a b c d ps tags fs) (snd mini chk)
    go : (∃ λ fsR → runF R fs ≡ just fsR ×
            caseM (halfVⁿ δ fsR) false (λ gs → (δ ℕ.≤ᵇ 3) ∧ (suc (length ps) ℕ.≡ᵇ δ) ∧ pairsOK 1 tags fs ps ∧ certOK gs a b c d ∧ countOK κ gs) ≡ true) →
         Goal s o w ic id
    go (fsR , rr , e1) = go′ (caseM-true (halfVⁿ δ fsR) _ e1)
      where
      go′ : (∃ λ gs → halfVⁿ δ fsR ≡ just gs ×
               ((δ ℕ.≤ᵇ 3) ∧ (suc (length ps) ℕ.≡ᵇ δ) ∧ pairsOK 1 tags fs ps ∧ certOK gs a b c d ∧ countOK κ gs) ≡ true) →
            Goal s o w ic id
      go′ (gs , hh , e2) =
        extend-case δ κ R a b c d ps tags ic id fs fsR gs ρ rr hh ok-d3 ln pok ce cn s o eq w eqv tg (mn m≡)
          (λ ρ′ w′ eqv′ tg′ → sound t (just δ ∷ tags) true (suc ic) (suc id) _ ρ′ ct (λ e → icd (FinP.suc-injective e)) s o eq w′ eqv′ tg′
                                 (λ _ → mn m≡))
        where
        ok-d3 = fst (δ ℕ.≤ᵇ 3) e2
        e3 = snd (δ ℕ.≤ᵇ 3) e2
        ln = fst (suc (length ps) ℕ.≡ᵇ δ) e3
        e4 = snd (suc (length ps) ℕ.≡ᵇ δ) e3
        pok = fst (pairsOK 1 tags fs ps) e4
        e5 = snd (pairsOK 1 tags fs ps) e4
        ce = fst (certOK gs a b c d) e5
        cn = snd (certOK gs a b c d) e5
  sound (conj g t) tags mini ic id fs ρ chk icd s o eq w eqv tg mn = go (caseM-true (stepF g fs) _ chk)
    where
    go : (∃ λ fs′ → stepF g fs ≡ just fs′ × (conjOK ic id g fs ∧ checkT t (tagsAfter g tags) (miniAfter g mini) ic id fs′) ≡ true) →
         Goal s o w ic id
    go (fs′ , st , ok-c1) = go′ (caseM-true (stepF (Hˡ ic id) fs) _ (fst (conjOK ic id g fs) ok-c1))
      where
      go′ : (∃ λ fcd → stepF (Hˡ ic id) fs ≡ just fcd ×
               (apart ic id g ∧ check (g ∷ []) fs ∧ atL? (stepF g fs) ∧ check (conjLetter ic id g ∷ []) fcd) ≡ true) →
            Goal s o w ic id
      go′ (fcd , sc , ok-c2) =
        conj-case g tags mini ic id fs fs′ fcd ρ icd st sc ap cg ka cl s o eq w eqv tg mn
          (λ N oN eqN wN _ eqvN _ tgN mnN → sound t (tagsAfter g tags) (miniAfter g mini) ic id fs′ ρ
                                             (snd (conjOK ic id g fs) ok-c1) icd N oN eqN wN eqvN tgN mnN)
        where
        ap = fst (apart ic id g) ok-c2
        ok-c3 = snd (apart ic id g) ok-c2
        cg = fst (check (g ∷ []) fs) ok-c3
        ok-c4 = snd (check (g ∷ []) fs) ok-c3
        ka = atL?-sound fs′ (≡.subst (λ x → atL? x ≡ true) st (fst (atL? (stepF g fs)) ok-c4))
        cl = snd (atL? (stepF g fs)) ok-c4
  sound (relabel π sw ic′ id′ t) tags mini ic id fs ρ chk icd s o eq w eqv tg mn =
    relabel-case π sw ic′ id′ tags ic id fs ρ icd di on e1 e2 fl s o eq w eqv tg
      (λ w′ eqv′ tg′ icd′ → sound t (Vec.map (tags !_) π) mini ic′ id′ _ ρ ct icd′ s o eq w′ eqv′ tg′ mn)
    where
    A1 = distinctV π
    A2 = ontoV π
    A3 = π ! ic′ == (if sw then id else ic)
    A4 = π ! id′ == (if sw then ic else id)
    A5 = if sw then flipOK ic id fs else true
    di = fst A1 chk
    on = fst A2 (snd A1 chk)
    e1 = fst A3 (snd A2 (snd A1 chk))
    e2 = fst A4 (snd A3 (snd A2 (snd A1 chk)))
    fl = fst A5 (snd A4 (snd A3 (snd A2 (snd A1 chk))))
    ct = snd A5 (snd A4 (snd A3 (snd A2 (snd A1 chk))))
  sound (useNF nf τ) tags mini ic id fs ρ chk icd s o eq w eqv tg mn =
    use-case nf τ tags mini ic id fs ρ icd al eic eid etg emi efs s o eq w eqv tg mn
    where
    B1 = allow nf
    B2 = ic == NFData.ic (nfData nf)
    B3 = id == NFData.id (nfData nf)
    B4 = eqTags tags (NFData.tags (nfData nf))
    B5 = if NFData.mini (nfData nf) then mini else true
    al = fst B1 chk
    eic = fst B2 (snd B1 chk)
    eid = fst B3 (snd B2 (snd B1 chk))
    etg = fst B4 (snd B3 (snd B2 (snd B1 chk)))
    emi = fst B5 (snd B4 (snd B3 (snd B2 (snd B1 chk))))
    efs = snd B5 (snd B4 (snd B3 (snd B2 (snd B1 chk))))
