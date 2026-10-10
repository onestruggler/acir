------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 4.4, Subcase 1.14.2: G = X[j,j+1] at a state s of level L,
-- k > 0, whose syllable is H[i₁,j], with entry j+1 in the class of i₁.
--
-- Write a = i₁, b = j, c = j+1.  The class of a has evenly many odd
-- entries, so it has a fourth, d; it comes after c, since a is the
-- first odd entry, b the next in its class, and no index lies between
-- b and c.  The syllable of r = G·s is again H[a,b] (Swap.ns-j-keep).
-- With entries A, A + 2q, A + 2p, A + 2d at a, b, c, d, Clément's
-- diagrams (27) and (28) complete the square from H[a,b]·r:
--
-- * p + q + d even: H[c,d] PB X[b,c] PB H[c,d], PB = H[a,c] H[b,d];
-- * p + q + d odd:  H[c,d] PC X[b,d] PC H[c,d], PC = H[a,d] H[b,c].
--
-- Every state on the way has an even entry among a, b, c, d
-- (Steps1142), so it lies below L, and the relations are Rel1142's,
-- carried to a < b < c < d.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (Lvl)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction as TR

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case1142 {n : ℕ} {L : Lvl} (ih : TR.EdgesBelow {n} L) where

open import Data.Bool.Base using (Bool ; true ; false ; _∨_ ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (just)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable using (does)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
import Presentation.Tactics.Words as TW
open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (oddℕ)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count ; dec-elim ; tri-elim)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Counting using (count-three ; search)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (D ; Z ; module ZR ; √2ᶻ ; oddᶻ ; rbit ; oddᶻ-+ ; oddᶻ-neg ; oddᶻ-*)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (_!_ ; scV ; Minimal ; Odd ; Even ; Odd⇒¬Even ; lde ; num)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm using (2ᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column using (nodd ; firstOdd ; nextSame ; Same ; firstOdd-spec ; nextSame-spec)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Xᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; _<ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Levels using (Minimal-X)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step using (odd⇒≤ ; same-class)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (sound-act)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (ne-𝕀)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Local {n} using (upd₂ ; module Emb)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Embedding as E
import Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence.Places as Places
import Examples.Groups.Real-Clifford+CH-TwoLevel.LocalRelations as LR
import Examples.Groups.Real-Clifford+CH-TwoLevel.Pairings as Pairings
import Examples.Groups.Real-Clifford+CH-TwoLevel.PairLevels as PairLevels
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Embed {n} using (module Known-at)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Algorithm using (levelᶜ ; sylᶜ ; sylDataᶜ ; sylDataᶜ-pair ; third)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Squares {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.State {n} using (module At ; module Pos ; lowᶜ)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Rel1142 as R
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Steps1142 as Steps1142
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Swap as Swap
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case1 as Case1

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open Close ih

private
  sym≢ : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
  sym≢ ne e = ne (≡.sym e)

  <-≢ : ∀ {x y : Fin n} → x < y → x ≢ y
  <-≢ lt ≡.refl = FinP.<-irrefl ≡.refl lt

  t≢f : true ≢ false
  t≢f ()

  ⟪_⟫ : ∀ {m} → List (Gen m) → Word (Gen m)
  ⟪_⟫ = TW.Associative.word-of-list

  ----------------------------------------------------------------------
  -- Parities

  even-√2 : ∀ x → Even (√2ᶻ ZR.* x)
  even-√2 x = oddᶻ-* √2ᶻ x

  even-−√2 : ∀ x → Even (ZR.- (√2ᶻ ZR.* x))
  even-−√2 x = ≡.trans (oddᶻ-neg (√2ᶻ ZR.* x)) (even-√2 x)

  odd-− : ∀ x y → oddᶻ (x ZR.- y) ≡ oddᶻ x xor oddᶻ y
  odd-− x y = ≡.trans (oddᶻ-+ x (ZR.- y)) (≡.cong (oddᶻ x xor_) (oddᶻ-neg y))

  odd-−− : ∀ x y z → oddᶻ ((x ZR.- y) ZR.- z) ≡ (oddᶻ x xor oddᶻ y) xor oddᶻ z
  odd-−− x y z = ≡.trans (odd-− (x ZR.- y) z) (≡.cong (_xor oddᶻ z) (odd-− x y))

  -- (A + p) + (q − d) is even when A is odd and q − d − p is odd.
  xor-w3 : ∀ a x y z → a ≡ true → (y xor z) xor x ≡ true → (a xor x) xor (y xor z) ≡ false
  xor-w3 true false false false _ ()
  xor-w3 true false false true _ _ = ≡.refl
  xor-w3 true false true false _ _ = ≡.refl
  xor-w3 true false true true _ ()
  xor-w3 true true false false _ _ = ≡.refl
  xor-w3 true true false true _ ()
  xor-w3 true true true false _ ()
  xor-w3 true true true true _ _ = ≡.refl
  xor-w3 false _ _ _ () _

------------------------------------------------------------------------
-- The edge at s

module At1142 (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (pv : pivot s ≡ just p) (eqL : levelᶜ s ≡ L)
              {j j′ : Fin n} (adj : toℕ j′ ≡ suc (toℕ j)) (j′≤p : j′ ≤ p)
              (k′ : ℕ) (eK : lde (col s p) ≡ suc k′) {a : Fin n} (fo : firstOdd (num (col s p)) ≡ just a)
              (nx : nextSame a (num (col s p)) ≡ just j) (sm : Same (num (col s p)) a j′) where

  open At s o pv using (W ; colW ; min ; be ; lvl ; syl ; zero> ; colX ; module Act)
  open Swap adj using (jj′ ; j≢j′ ; none-between ; fo-out ; ns-j-keep)

  G : Gen n
  G = X-gen j j′ jj′

  r : Matrix n n D
  r = actM G s

  b c : Fin n
  b = j
  c = j′

  specb = nextSame-spec W nx

  ab : a < b
  ab = proj₁ specb
  bc : b < c
  bc = jj′

  sb : Same W a b
  sb = proj₁ (proj₂ specb)

  oa : Odd (W ! a)
  oa = proj₁ (firstOdd-spec W fo)
  ob : Odd (W ! b)
  ob = proj₁ sb
  oc : Odd (W ! c)
  oc = proj₁ sm

  a≢b : a ≢ b
  a≢b = <-≢ ab
  a≢c : a ≢ c
  a≢c = <-≢ (FinP.<-trans ab bc)

  -- L, with its exponent.
  L≡ : L ≡ (suc (toℕ p) , suc k′ , nodd W)
  L≡ = ≡.trans (≡.sym eqL) (≡.trans lvl (≡.cong (λ K → suc (toℕ p) , K , third K W) eK))

  colk : col s p ≡ scV (suc k′) W
  colk = ≡.trans colW (≡.cong (λ K → scV K W) eK)

  ----------------------------------------------------------------------
  -- The fourth entry d of the class of a

  β : Bool
  β = rbit (W ! a)

  module PL = PairLevels p k′ (nodd W)
  module SS = PL.State s o (Pos.conv≡ s (≡.trans eqL L≡))

  E? : Fin n → Bool
  E? y = does (y FinP.≟ a) ∨ (does (y FinP.≟ b) ∨ does (y FinP.≟ c))

  in3 : ∀ y → E? y ≡ true → y ≡ a ⊎ y ≡ b ⊎ y ≡ c
  in3 y e with y FinP.≟ a | y FinP.≟ b | y FinP.≟ c
  in3 y e | yes ya | _ | _ = inj₁ ya
  in3 y e | no _ | yes yb | _ = inj₂ (inj₁ yb)
  in3 y e | no _ | no _ | yes yc = inj₂ (inj₂ yc)
  in3 y () | no _ | no _ | no _

  out3 : ∀ y → E? y ≡ false → y ≢ a × y ≢ b × y ≢ c
  out3 y e with y FinP.≟ a | y FinP.≟ b | y FinP.≟ c
  out3 y () | yes _ | _ | _
  out3 y () | no _ | yes _ | _
  out3 y () | no _ | no _ | yes _
  out3 y e | no na | no nb | no nc = na , nb , nc

  cls : ∀ x → Same W a x → SS.Cls β x ≡ true
  cls x (ox , rx) = ≡.subst (λ t → SS.Cls t x ≡ true) rx (SS.cls-true x ox)

  fourth : ∃ λ d → Same W a d × d ≢ a × d ≢ b × d ≢ c
  fourth = from (search (SS.Cls β) E?)
    where
    from : (∃ λ y → SS.Cls β y ≡ true × E? y ≡ false) ⊎ (∀ y → SS.Cls β y ≡ true → E? y ≡ true) →
           ∃ λ d → Same W a d × d ≢ a × d ≢ b × d ≢ c
    from (inj₁ (y , cy , ey)) = y , SS.cls-spec β y cy , out3 y ey
    from (inj₂ all) = ⊥-elim (t≢f (≡.trans (≡.sym (≡.cong oddℕ three)) (SS.cls-even β)))
      where
      three : count (SS.Cls β) ≡ 3
      three = count-three (SS.Cls β) a b c a≢b a≢c j≢j′ (cls a (oa , ≡.refl)) (cls b sb) (cls c sm)
                (λ y cy → in3 y (all y cy))

  d : Fin n
  d = proj₁ fourth

  sd : Same W a d
  sd = proj₁ (proj₂ fourth)

  d≢a : d ≢ a
  d≢a = proj₁ (proj₂ (proj₂ fourth))
  d≢b : d ≢ b
  d≢b = proj₁ (proj₂ (proj₂ (proj₂ fourth)))
  d≢c : d ≢ c
  d≢c = proj₂ (proj₂ (proj₂ (proj₂ fourth)))

  od : Odd (W ! d)
  od = proj₁ sd

  cd : c < d
  cd = tri-elim (FinP.<-cmp d c) (λ d<c → ⊥-elim (below d<c)) (λ d≡c → ⊥-elim (d≢c d≡c)) (λ c<d → c<d)
    where
    below : d < c → ⊥
    below d<c = tri-elim (FinP.<-cmp d b)
      (λ d<b → tri-elim (FinP.<-cmp d a)
        (λ d<a → Odd⇒¬Even {W ! d} od (proj₂ (firstOdd-spec W fo) d d<a))
        (λ d≡a → d≢a d≡a)
        (λ a<d → proj₂ (proj₂ specb) d a<d d<b sd))
      (λ d≡b → d≢b d≡b)
      (λ b<d → none-between b<d d<c)

  d≤p : d ≤ p
  d≤p = odd⇒≤ {p = p} {W} zero> od

  -- The entries A, A + 2q, A + 2p, A + 2d.
  A : Z
  A = W ! a

  cb = same-class (W ! b) A ob oa (proj₂ sb)
  cc = same-class (W ! c) A oc oa (proj₂ sm)
  cd′ = same-class (W ! d) A od oa (proj₂ sd)

  zb zc zd : Z
  zb = proj₁ cb
  zc = proj₁ cc
  zd = proj₁ cd′

  module St = Steps1142 A zc zb zd

  ----------------------------------------------------------------------
  -- The window a < b < c < d

  open Places.Emb4 ab bc cd using (σ ; o02 ; o03 ; o12 ; o13 ; o23) renaming (emb to e4)

  inj : ∀ {x y} → σ x ≡ σ y → x ≡ y
  inj {x} {y} eq = dec-elim (x FinP.≟ y) (λ e → e) (λ ne → ⊥-elim (E.Emb.injective e4 ne eq))

  σ≤p : ∀ x → σ x ≤ p
  σ≤p zero = ℕP.≤-trans (ℕP.<⇒≤ o03) d≤p
  σ≤p (suc zero) = ℕP.≤-trans (ℕP.<⇒≤ o13) d≤p
  σ≤p (suc (suc zero)) = ℕP.≤-trans (ℕP.<⇒≤ o23) d≤p
  σ≤p (suc (suc (suc zero))) = d≤p

  open Emb σ inj using (emb ; emb-ext ; emb-self ; loc ; nodd-emb)
  open Known-at p (suc k′) σ inj σ≤p W

  odd4 : ∀ l → Odd (W ! σ l)
  odd4 zero = oa
  odd4 (suc zero) = ob
  odd4 (suc (suc zero)) = oc
  odd4 (suc (suc (suc zero))) = od

  -- A known state with an even local entry lies below L.
  lowK : ∀ {N e} → Known N e → (l : Fin 4) → Even (e ! l) → levelᶜ N <ₗ L
  lowK {N} {e} K l ev =
    ≡.subst (levelᶜ N <ₗ_) (≡.sym L≡) (lowᶜ N (beK K) k′ (emb e W) (colK K) (nodd-emb e W odd4 l ev))

  stepH : ∀ {N e} (x y : Fin 4) (lt : σ x < σ y) (e′ : Vec Z 4) →
          e ! x ZR.+ e ! y ≡ √2ᶻ ZR.* (e′ ! x) → e ! x ZR.- e ! y ≡ √2ᶻ ZR.* (e′ ! y) →
          upd₂ x y (e′ ! x) (e′ ! y) e ≡ e′ → Known N e → Known (actM (H-gen (σ x) (σ y) lt) N) e′
  stepH {N} x y lt e′ sum dif eq K =
    ≡.subst (Known (actM (H-gen (σ x) (σ y) lt) N)) eq (known-Hgen x y lt (e′ ! x) (e′ ! y) sum dif K)

  stepX : ∀ {N e} (x y : Fin 4) (lt : σ x < σ y) (e′ : Vec Z 4) →
          upd₂ x y (e ! y) (e ! x) e ≡ e′ → Known N e → Known (actM (X-gen (σ x) (σ y) lt) N) e′
  stepX {N} x y lt e′ eq K = ≡.subst (Known (actM (X-gen (σ x) (σ y) lt) N)) eq (known-Xgen x y lt K)

  -- s, r = G·s and H[a,b]·r are known.
  es : Vec Z 4
  es = A ∷ (A ZR.+ 2ᶻ ZR.* zb) ∷ (A ZR.+ 2ᶻ ZR.* zc) ∷ (A ZR.+ 2ᶻ ZR.* zd) ∷ []

  emb-s : emb es W ≡ W
  emb-s = ≡.trans (emb-ext {es} {loc W} {W} {W} at (λ _ _ → ≡.refl)) (emb-self W)
    where
    at : ∀ l → es ! l ≡ loc W ! l
    at zero = ≡.refl
    at (suc zero) = ≡.sym (proj₂ cb)
    at (suc (suc zero)) = ≡.sym (proj₂ cc)
    at (suc (suc (suc zero))) = ≡.sym (proj₂ cd′)

  K-s : Known s es
  K-s = known (≡.trans colk (≡.cong (scV (suc k′)) (≡.sym emb-s))) be

  K-r : Known r St.vr
  K-r = stepX (suc zero) (suc (suc zero)) bc St.vr ≡.refl K-s

  M0 : Matrix n n D
  M0 = actM (H-gen a b ab) r
  K0 : Known M0 St.v0
  K0 = stepH zero (suc zero) ab St.v0 St.h01-sum St.h01-dif ≡.refl K-r

  M1 : Matrix n n D
  M1 = actM (H-gen c d cd) M0
  K1 : Known M1 St.v1
  K1 = stepH (suc (suc zero)) (suc (suc (suc zero))) cd St.v1 St.h23-sum St.h23-dif ≡.refl K0

  ----------------------------------------------------------------------
  -- The syllables of s and r: H[a,b]

  sylN : sylᶜ s ≡ H a b ab
  sylN = ≡.trans syl (≡.trans (≡.cong (λ K → sylDataᶜ p K W) eK) (sylDataᶜ-pair {p = p} k′ W fo nx ab))

  W′ : Vec Z n
  W′ = Xᶻ j j′ W

  colr : col r p ≡ scV (suc k′) W′
  colr = ≡.trans (colX j j′ jj′) (≡.cong (λ K → scV K W′) eK)

  min′ : Minimal (suc k′) W′
  min′ = Minimal-X j j′ j≢j′ W (≡.subst (λ K → Minimal K W) eK min)

  open Act G j′≤p using (module Rep)
  module Rr = Rep (suc k′) W′ colr min′ (ne-𝕀 r p k′ W′ colr min′)

  sylR : sylᶜ r ≡ H a b ab
  sylR = ≡.trans Rr.syl′ (sylDataᶜ-pair {p = p} k′ W′ (fo-out W fo a≢b a≢c) (ns-j-keep W nx sm) ab)

  pN : Path (H a b ab) s o
  pN = prograde (H-gen a b ab) s o pv sylN

  pN′ : Path (H a b ab) r (ColOrth-actMʷ [ G ]ʷ o)
  pN′ = prograde (H-gen a b ab) r (ColOrth-actMʷ [ G ]ʷ o) Rr.pv′ sylR

  -- The end of a square lies below L: it is H[a,b]·s.
  end-below : ∀ {Wd} → Wd • H a b ab • [ G ]ʷ ≈ H a b ab → levelᶜ (actMʷ Wd M0) <ₗ L
  end-below rel = ≡.subst (λ M → levelᶜ M <ₗ L) (≡.sym (sound-act rel s))
                    (≡.subst (λ w → levelᶜ (actMʷ w s) <ₗ L) sylN (normal-below s o pv (inj₂ eqL)))

  ----------------------------------------------------------------------
  -- The relations, on a < b < c < d

  module P = E.Pull e4 (_===_ {n})

  f1w : E.Emb.word e4 ⟪ R.Lf1 ⟫ ≈ E.Emb.word e4 ⟪ R.Rf1 ⟫
  f1w = trans (by-assoc auto) (trans (Pairings.Sorted.f1 {n} ab bc cd) (by-assoc auto))

  Gw : E.Emb.word e4 ⟪ R.LG ⟫ ≈ E.Emb.word e4 ⟪ R.RG ⟫
  Gw = trans (by-assoc auto) (trans (Pairings.Sorted.G≈ {n} ab bc cd) (by-assoc auto))

  open R.From P.pull (P.pull-local (λ x → axiom (LR.local⇒ x))) (P.hyp f1w) (P.hyp Gw) using (r27 ; r28)

  ----------------------------------------------------------------------
  -- The parity of p + q + d chooses the route

  S? : Bool
  S? = (oddᶻ zb xor oddᶻ zd) xor oddᶻ zc

  -- p + q + d even: H[c,d] PB X[b,c] PB H[c,d] (27).
  module Even (eS : S? ≡ false) where

    M2 = actM (H-gen b d o13) M1
    M3 = actM (H-gen a c o02) M2
    M4 = actM (X-gen b c o12) M3
    M5 = actM (H-gen b d o13) M4
    M6 = actM (H-gen a c o02) M5

    K2 : Known M2 St.v2
    K2 = stepH (suc zero) (suc (suc (suc zero))) o13 St.v2 St.e13-sum St.e13-dif ≡.refl K1
    K3 : Known M3 St.v3
    K3 = stepH zero (suc (suc zero)) o02 St.v3 St.e02-sum St.e02-dif ≡.refl K2
    K4 : Known M4 St.v4
    K4 = stepX (suc zero) (suc (suc zero)) o12 St.v4 ≡.refl K3
    K5 : Known M5 St.v5
    K5 = stepH (suc zero) (suc (suc (suc zero))) o13 St.v5 St.e13′-sum St.e13′-dif ≡.refl K4
    K6 : Known M6 St.v6
    K6 = stepH zero (suc (suc zero)) o02 St.v6 St.e02′-sum St.e02′-dif ≡.refl K5

    Wd : Word (Gen n)
    Wd = E.Emb.word e4 ⟪ R.h23 ∷ R.h02 ∷ R.h13 ∷ R.x12 ∷ R.h02 ∷ R.h13 ∷ R.h23 ∷ [] ⟫

    rel : Wd • H a b ab • [ G ]ʷ ≈ H a b ab
    rel = trans (by-assoc auto) (trans (P.push r27) (by-assoc auto))

    ev3 : Even ((zb ZR.- zd) ZR.- zc)
    ev3 = ≡.trans (odd-−− zb zd zc) eS

    low : Low L Wd M0
    low = ((((((tt , (l0 , l1)) , (l1 , l2)) , (l2 , l3)) , (l3 , l4)) , (l4 , l5)) , (l5 , l6)) , (l6 , end-below rel)
      where
      l0 = lowK K0 zero (even-√2 (A ZR.+ zc))
      l1 = lowK K1 zero (even-√2 (A ZR.+ zc))
      l2 = lowK K2 zero (even-√2 (A ZR.+ zc))
      l3 = lowK K3 (suc zero) ev3
      l4 = lowK K4 (suc (suc zero)) ev3
      l5 = lowK K5 (suc zero) (even-−√2 zb)
      l6 = lowK K6 zero (even-√2 (A ZR.+ zb))

    square : Path [ G ]ʷ s o
    square = close G s o (H a b ab) (H a b ab) Wd pN pN′ low rel

  -- p + q + d odd: H[c,d] PC X[b,d] PC H[c,d] (28).
  module Odd (eS : S? ≡ true) where

    M2 = actM (H-gen b c o12) M1
    M3 = actM (H-gen a d o03) M2
    M4 = actM (X-gen b d o13) M3
    M5 = actM (H-gen b c o12) M4
    M6 = actM (H-gen a d o03) M5

    K2 : Known M2 St.w2
    K2 = stepH (suc zero) (suc (suc zero)) o12 St.w2 St.o12-sum St.o12-dif ≡.refl K1
    K3 : Known M3 St.w3
    K3 = stepH zero (suc (suc (suc zero))) o03 St.w3 St.o03-sum St.o03-dif ≡.refl K2
    K4 : Known M4 St.w4
    K4 = stepX (suc zero) (suc (suc (suc zero))) o13 St.w4 ≡.refl K3
    K5 : Known M5 St.w5
    K5 = stepH (suc zero) (suc (suc zero)) o12 St.w5 St.o12′-sum St.o12′-dif ≡.refl K4
    K6 : Known M6 St.w6
    K6 = stepH zero (suc (suc (suc zero))) o03 St.w6 St.o03′-sum St.o03′-dif ≡.refl K5

    Wd : Word (Gen n)
    Wd = E.Emb.word e4 ⟪ R.h23 ∷ R.h03 ∷ R.h12 ∷ R.x13 ∷ R.h03 ∷ R.h12 ∷ R.h23 ∷ [] ⟫

    rel : Wd • H a b ab • [ G ]ʷ ≈ H a b ab
    rel = trans (by-assoc auto) (trans (P.push r28) (by-assoc auto))

    ev3 : Even ((A ZR.+ zc) ZR.+ (zb ZR.- zd))
    ev3 = ≡.trans (oddᶻ-+ (A ZR.+ zc) (zb ZR.- zd))
            (≡.trans (≡.cong₂ _xor_ (oddᶻ-+ A zc) (odd-− zb zd)) (xor-w3 (oddᶻ A) (oddᶻ zc) (oddᶻ zb) (oddᶻ zd) oa eS))

    low : Low L Wd M0
    low = ((((((tt , (l0 , l1)) , (l1 , l2)) , (l2 , l3)) , (l3 , l4)) , (l4 , l5)) , (l5 , l6)) , (l6 , end-below rel)
      where
      l0 = lowK K0 zero (even-√2 (A ZR.+ zc))
      l1 = lowK K1 zero (even-√2 (A ZR.+ zc))
      l2 = lowK K2 zero (even-√2 (A ZR.+ zc))
      l3 = lowK K3 zero ev3
      l4 = lowK K4 zero ev3
      l5 = lowK K5 (suc zero) (even-−√2 zb)
      l6 = lowK K6 zero (even-√2 (A ZR.+ zb))

    square : Path [ G ]ʷ s o
    square = close G s o (H a b ab) (H a b ab) Wd pN pN′ low rel

  case1142 : Path [ G ]ʷ s o
  case1142 = by S? ≡.refl
    where
    by : ∀ t → S? ≡ t → Path [ G ]ʷ s o
    by false e = Even.square e
    by true e = Odd.square e

------------------------------------------------------------------------
-- Subcase 1.14.2 at every state of L

hyp1142 : Case1.Hyp1142 ih
hyp1142 s o pv eqL adj j′≤p le k′ eK fo nx sm = At1142.case1142 s o pv eqL adj j′≤p k′ eK fo nx sm
