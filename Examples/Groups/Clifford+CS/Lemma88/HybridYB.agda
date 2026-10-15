------------------------------------------------------------------------
-- Presentations of groups
--
-- The hybrid rule ki-yb at every instance, from one
--
-- On N = 4 + m ≥ 16 indices.  ki-yb at (j, k, l, m) with sink s is the
-- rule at the canonical instance (N − 4, N − 3, N − 2, N − 1) with sink
-- N − 5 conjugated by a K-free word u sending the canonical indices to
-- (j, k, l, m, s) with phase zero on all of them: then u carries each of
-- the rule's four letters (HybridPair.hyb-conj), and the rule follows
-- from the canonical one.  The word is built from a plan, a list of
-- (target, source) pairs: ρ [] = id and ρ ((x, y) ∷ p) = (x ρp(y)) ∘ ρp,
-- a transposition after the rest, so that ρ sends each source to its
-- target (`ρ-img`, distinct targets and distinct sources); each
-- transposition is the letter (−1)_[g] X_[a,b] with g a spare index off
-- every target and source, which no letter moves, so all the phase is
-- on g (`W-ph`), and each letter is an involution, so the reversed word
-- is an inverse.  After Real-Clifford+CH's Auxiliary.Telescope.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc ; _≤_)
open import Word.Base using (Word ; WRel)

module Examples.Groups.Clifford+CS.Lemma88.HybridYB
  {X : Set} (Γ : WRel X) (m : ℕ) (p p′ l h k : ℕ → Word X)
  (big : 16 ≤ suc (suc (suc (suc m)))) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ) renaming (_<_ to _<ᶠ_)
open import Data.Fin.Properties using (toℕ-injective ; _≟_ ; <-cmp)
open import Data.List using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.All as All using (All ; [] ; _∷_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero ; _+_ ; _∸_ ; _<_ ; z≤n ; s≤s)
open import Data.Nat.Properties as NP using ()
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Nullary.Decidable
open import Word.Base using (ε ; _•_ ; [_]ʷ ; _ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; ki)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (_F,_===_)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (kiw)
open import Examples.Groups.Clifford+CS.Auxiliary.NF (suc (suc (suc m)))
  using (KFreeʷ ; nil ; cat ; fin ; fin-toℕ ; fin≢)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm (suc (suc (suc (suc m))))
  using (p0 ; p2 ; _+ᵖ_ ; sp ; ph ; prm ; prm≡ ; ph≡ ; δ-≢ ; phif
       ; swapF ; swapF-b ; swapF-o ; swapF-inj ; swapF-same)
open import Examples.Groups.Clifford+CS.Auxiliary.Template (suc (suc (suc m)))
  using (xd ; kf-xd ; xd-prm ; xd-ph ; xd-same)
open import Examples.Groups.Clifford+CS.Lemma88.Chains p p′ l h k using (d)
import Examples.Groups.Clifford+CS.Auxiliary.Fresh as Fresh
import Examples.Groups.Clifford+CS.Lemma88.Fragment as Fr
import Examples.Groups.Clifford+CS.Lemma88.HybridTop as HTop
import Examples.Groups.Clifford+CS.Lemma88.HybridCen as HCen
import Examples.Groups.Clifford+CS.Lemma88.HybridPair as HP
import Examples.Groups.Clifford+CS.Lemma88.HybridOne as HO
import Examples.Groups.Clifford+CS.Lemma88.HybridKK as HK
open import Examples.Groups.Clifford+CS.Tools using (module Tools)

private
  N′ N : ℕ
  N′ = suc (suc (suc m))
  N  = suc N′

  W : Set
  W = Word (GenP N)

  module FrN = Fr Γ N p p′ l h k

  infix 4 _≈ᶠ_
  _≈ᶠ_ : W → W → Set
  _≈ᶠ_ = PB._≈_ (N F,_===_)

open PB Γ using (_≈_)
open HTop Γ N p p′ l h k using (top ; TopFar)
open HCen Γ m p p′ l h k using (tT ; tT1 ; tB ; toT ; toT1 ; toB)
open HO Γ m p p′ l h k using (tT<tT1)

------------------------------------------------------------------------
-- Plans

Plan : Set
Plan = List (Fin N × Fin N)

ρ : Plan → Fin N → Fin N
ρ []            v = v
ρ ((x , y) ∷ q) v = swapF x (ρ q y) (ρ q v)

ρ-inj : ∀ q {u v} → ρ q u ≡ ρ q v → u ≡ v
ρ-inj []            e = e
ρ-inj ((x , y) ∷ q) e = ρ-inj q (swapF-inj x (ρ q y) e)

-- Distinct targets and distinct sources.
Ok : Plan → Set
Ok []            = ⊤
Ok ((x , y) ∷ q) = All (λ e → x ≢ proj₁ e × y ≢ proj₂ e) q × Ok q

ρ-img : ∀ q → Ok q → ∀ {x y} → (x , y) ∈ q → ρ q y ≡ x
ρ-img ((x , y) ∷ q) ok (here Eq.refl) = swapF-b x (ρ q y)
ρ-img ((x , y) ∷ q) (all , ok) {x′} {y′} (there mem) =
  Eq.trans (Eq.cong (swapF x (ρ q y)) ih)
           (swapF-o x (ρ q y) x′ (λ e → proj₁ (find mem) (Eq.sym e))
                                 (λ e → proj₂ (find mem) (Eq.sym (ρ-inj q (Eq.trans ih e)))))
  where
  ih = ρ-img q ok mem

  find : ∀ {e} → e ∈ q → x ≢ proj₁ e × y ≢ proj₂ e
  find {e} mem′ = go all mem′
    where
    go : ∀ {r} → All (λ e → x ≢ proj₁ e × y ≢ proj₂ e) r → e ∈ r → x ≢ proj₁ e × y ≢ proj₂ e
    go (a ∷ _)  (here Eq.refl) = a
    go (_ ∷ as) (there mm)     = go as mm

-- A spare index off every target and source.
Spare : Plan → Fin N → Set
Spare q g = All (λ e → g ≢ proj₁ e × g ≢ proj₂ e) q

ρ-g : ∀ q g → Spare q g → ρ q g ≡ g
ρ-g []            g spr = Eq.refl
ρ-g ((x , y) ∷ q) g ((gx , gy) ∷ spr) =
  Eq.trans (Eq.cong (swapF x (ρ q y)) ih)
           (swapF-o x (ρ q y) g gx (λ e → gy (ρ-inj q (Eq.trans ih e))))
  where ih = ρ-g q g spr

ρ-g′ : ∀ q g → Spare q g → ∀ y → y ≢ g → ρ q y ≢ g
ρ-g′ q g spr y yg e = yg (ρ-inj q (Eq.trans e (Eq.sym (ρ-g q g spr))))

------------------------------------------------------------------------
-- The word of a plan

private
  xdprm : ∀ c a b i → prm (sp (xd c a b)) i ≡ swapF a b i
  xdprm c a b i = go (a ≟ b)
    where
    go : Dec (a ≡ b) → prm (sp (xd c a b)) i ≡ swapF a b i
    go (yes e) = Eq.trans (prm≡ (xd-same c a b e) i)
                          (Eq.sym (Eq.subst (λ z → swapF a z i ≡ i) e (swapF-same a i)))
    go (no ne) = xd-prm c a b i ne

  xdph0 : ∀ c a b i → i ≢ c → ph (sp (xd c a b)) i ≡ p0
  xdph0 c a b i ic = go (a ≟ b)
    where
    go : Dec (a ≡ b) → ph (sp (xd c a b)) i ≡ p0
    go (yes e) = ph≡ (xd-same c a b e) i
    go (no ne) = Eq.trans (xd-ph c a b i ne) (Eq.cong (λ β → phif β p2) (δ-≢ c i ic))

module PlanWord (g : Fin N) where

  Wd Wr : Plan → W
  Wd []            = ε
  Wd ((x , y) ∷ q) = Wd q • xd g x (ρ q y)
  Wr []            = ε
  Wr ((x , y) ∷ q) = xd g x (ρ q y) • Wr q

  kf-Wd : ∀ q → KFreeʷ (Wd q)
  kf-Wd []            = nil
  kf-Wd ((x , y) ∷ q) = cat (kf-Wd q) (kf-xd g x (ρ q y))

  W-prm : ∀ q t → prm (sp (Wd q)) t ≡ ρ q t
  W-prm []            t = Eq.refl
  W-prm ((x , y) ∷ q) t =
    Eq.trans (Eq.cong (prm (sp (xd g x (ρ q y)))) (W-prm q t)) (xdprm g x (ρ q y) (ρ q t))

  W-ph : ∀ q → Spare q g → ∀ t → t ≢ g → ph (sp (Wd q)) t ≡ p0
  W-ph []            spr t tg = Eq.refl
  W-ph ((x , y) ∷ q) (_ ∷ spr) t tg =
    Eq.cong₂ _+ᵖ_ (W-ph q spr t tg)
      (Eq.trans (Eq.cong (ph (sp (xd g x (ρ q y)))) (W-prm q t))
                (xdph0 g x (ρ q y) (ρ q t) (ρ-g′ q g spr t tg)))

------------------------------------------------------------------------
-- The canonical instance: N − 4, N − 3, N − 2, N − 1 with sink N − 5

private
  q₀ : m < N
  q₀ = NP.≤-trans (NP.n≤1+n (suc m)) (NP.≤-trans (NP.n≤1+n (suc (suc m))) (NP.n≤1+n (suc (suc (suc m)))))

  qs : m ∸ 1 < N
  qs = NP.≤-<-trans (NP.m∸n≤m m 1) q₀

  m≥1 : 1 ≤ m
  m≥1 = NP.≤-pred (NP.≤-pred (NP.≤-pred (NP.≤-pred (NP.≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) big))))

tJ tS : Fin N
tJ = fin m q₀
tS = fin (m ∸ 1) qs

private
  toJ : toℕ tJ ≡ m
  toJ = fin-toℕ m q₀

  toS : toℕ tS ≡ m ∸ 1
  toS = fin-toℕ (m ∸ 1) qs

  lt : ∀ {a b : Fin N} {x y : ℕ} → toℕ a ≡ x → toℕ b ≡ y → x < y → a <ᶠ b
  lt ea eb xy = Eq.subst₂ _<_ (Eq.sym ea) (Eq.sym eb) xy

  -- the orderings of the four pairs
  qJB : tJ <ᶠ tB
  qJB = lt toJ toB (NP.n<1+n m)
  qJT : tJ <ᶠ tT
  qJT = lt toJ toT (NP.<-trans (NP.n<1+n m) (NP.n<1+n (suc m)))
  qBT1 : tB <ᶠ tT1
  qBT1 = lt toB toT1 (NP.<-trans (NP.n<1+n (suc m)) (NP.n<1+n (suc (suc m))))

  -- the canonical indices are distinct
  ne : ∀ {a b : Fin N} {x y : ℕ} → toℕ a ≡ x → toℕ b ≡ y → x < y → a ≢ b
  ne ea eb xy e = NP.<⇒≢ xy (Eq.trans (Eq.sym ea) (Eq.trans (Eq.cong toℕ e) eb))

  pred< : ∀ n → 1 ≤ n → n ∸ 1 < n
  pred< (suc n) _ = NP.n<1+n n

  sJ : m ∸ 1 < m
  sJ = pred< m m≥1

-- The rule at the canonical instance.
YB₀ : Set
YB₀ = (d ʷ) (kiw tJ tB tS qJB • (kiw tT tT1 tS tT<tT1 • (kiw tJ tT tS qJT • kiw tB tT1 tS qBT1)))
      ≈ (d ʷ) (kiw tJ tT tS qJT • (kiw tB tT1 tS qBT1 • (kiw tJ tB tS qJB • kiw tT tT1 tS tT<tT1)))

------------------------------------------------------------------------
-- The transport

module Proofs (F : FrN.Facts) (T : TopFar)
  (sc : (p′ (suc m) • p′ (suc m) • p′ (suc (suc m))) • k top
        ≈ k top • (p′ (suc m) • p′ (suc m) • p′ (suc (suc m))))
  (shift : ∀ {j} → suc (suc j) < N →
           (l j • l (suc j)) • k j ≈ k (suc j) • (l j • l (suc j)))
  (yb₀ : YB₀) where

  open FrN.Facts F
  open FrN.Proofs F
  open Tools Γ hiding (_≈_)
  open HCen.Proofs Γ m p p′ l h k F T sc using (d-≈)
  open HP.Proofs Γ m p p′ l h k F T sc shift using (hyb-conj)

  private
    xd-sq : ∀ g a b → g ≢ a → g ≢ b → (xd g a b • xd g a b) ≈ᶠ ε
    xd-sq g a b ga gb with <-cmp a b
    ... | tri< ab _ _ = HK.xx-inv Γ m p p′ l h k g a b ab ga gb
    ... | tri≈ _ _ _  = PB.left-unit
    ... | tri> _ _ ba = HK.xx-inv Γ m p p′ l h k g b a ba gb ga

    conj-• : ∀ {U A A′ B B′ : Word X} → U • A ≈ A′ • U → U • B ≈ B′ • U →
             U • (A • B) ≈ (A′ • B′) • U
    conj-• {U} {A} {A′} {B} {B′} cA cB = begin
      U • (A • B)       ≈⟨ sym assoc ⟩
      (U • A) • B       ≈⟨ front B cA ⟩
      (A′ • U) • B      ≈⟨ assoc ⟩
      A′ • (U • B)      ≈⟨ back A′ cB ⟩
      A′ • (B′ • U)     ≈⟨ sym assoc ⟩
      (A′ • B′) • U     ∎

    carry : ∀ {U Ū A B A′ B′ : Word X} → Ū • U ≈ ε →
            U • A ≈ A′ • U → U • B ≈ B′ • U → A′ ≈ B′ → A ≈ B
    carry {U} {Ū} {A} {B} {A′} {B′} inv cA cB e = begin
      A                 ≈⟨ sym left-unit ⟩
      ε • A             ≈⟨ front A (sym inv) ⟩
      (Ū • U) • A       ≈⟨ assoc ⟩
      Ū • (U • A)       ≈⟨ back Ū cA ⟩
      Ū • (A′ • U)      ≈⟨ back Ū (front U e) ⟩
      Ū • (B′ • U)      ≈⟨ back Ū (sym cB) ⟩
      Ū • (U • B)       ≈⟨ sym assoc ⟩
      (Ū • U) • B       ≈⟨ front B inv ⟩
      ε • B             ≈⟨ left-unit ⟩
      B                 ∎

  module _ (g : Fin N) where
    open PlanWord g

    -- The reversed word is a left inverse.
    W-inv : ∀ q → Spare q g → (d ʷ) (Wr q) • (d ʷ) (Wd q) ≈ ε
    W-inv []            spr = left-unit
    W-inv ((x , y) ∷ q) ((gx , gy) ∷ spr) = begin
      (Lx • Rq) • (Dq • Lx)    ≈⟨ assoc ⟩
      Lx • (Rq • (Dq • Lx))    ≈⟨ back Lx (sym assoc) ⟩
      Lx • ((Rq • Dq) • Lx)    ≈⟨ back Lx (front Lx (W-inv q spr)) ⟩
      Lx • (ε • Lx)            ≈⟨ back Lx left-unit ⟩
      Lx • Lx                  ≈⟨ d-≈ (xd-sq g x (ρ q y) gx (λ e → ρ-g′ q g spr y (λ e′ → gy (Eq.sym e′)) (Eq.sym e))) ⟩
      ε                        ∎
      where
      Lx = (d ʷ) (xd g x (ρ q y))
      Rq = (d ʷ) (Wr q)
      Dq = (d ʷ) (Wd q)

  ----------------------------------------------------------------------
  -- ki-yb at every instance

  d-ki-yb : ∀ (jj kk ll mm s : Fin N) .(jk : jj <ᶠ kk) .(lm : ll <ᶠ mm) .(jl : jj <ᶠ ll) .(km : kk <ᶠ mm) →
            kk ≢ ll → s ≢ jj → s ≢ kk → s ≢ ll → s ≢ mm →
            (d ʷ) (kiw jj kk s jk • (kiw ll mm s lm • (kiw jj ll s jl • kiw kk mm s km)))
            ≈ (d ʷ) (kiw jj ll s jl • (kiw kk mm s km • (kiw jj kk s jk • kiw ll mm s lm)))
  d-ki-yb jj kk ll mm s jk lm jl km kl sj sk sl sm =
    G.result (Fresh.Fresh3.f₁ fr) (Fresh.Fresh3.off₁ fr)
    where
    open PlanWord

    rel : ∀ {a b : Fin N} → .(a <ᶠ b) → toℕ a < toℕ b
    rel {a} {b} ab = Relation.Nullary.Decidable.recompute (toℕ a NP.<? toℕ b) ab

    ≢< : ∀ {a b : Fin N} → toℕ a < toℕ b → a ≢ b
    ≢< ab e = NP.<⇒≢ ab (Eq.cong toℕ e)

    sym≢ : ∀ {a b : Fin N} → a ≢ b → b ≢ a
    sym≢ n e = n (Eq.sym e)

    qq : Plan
    qq = (jj , tJ) ∷ (kk , tB) ∷ (ll , tT) ∷ (mm , tT1) ∷ (s , tS) ∷ []

    -- the targets are distinct, and so are the canonical sources
    jm : toℕ jj < toℕ mm
    jm = NP.<-trans (rel jl) (rel lm)

    sB : m ∸ 1 < suc m
    sB = NP.<-trans sJ (NP.n<1+n m)
    sT : m ∸ 1 < suc (suc m)
    sT = NP.<-trans sB (NP.n<1+n (suc m))
    sT1 : m ∸ 1 < suc (suc (suc m))
    sT1 = NP.<-trans sT (NP.n<1+n (suc (suc m)))
    JT1 : m < suc (suc (suc m))
    JT1 = NP.<-trans (NP.<-trans (NP.n<1+n m) (NP.n<1+n (suc m))) (NP.n<1+n (suc (suc m)))
    BT : suc m < suc (suc m)
    BT = NP.n<1+n (suc m)
    BT1 : suc m < suc (suc (suc m))
    BT1 = NP.<-trans BT (NP.n<1+n (suc (suc m)))
    TT1 : suc (suc m) < suc (suc (suc m))
    TT1 = NP.n<1+n (suc (suc m))

    ok : Ok qq
    ok = ((≢< (rel jk) , ne toJ toB (NP.n<1+n m))
          ∷ (≢< (rel jl) , ne toJ toT (NP.<-trans (NP.n<1+n m) BT))
          ∷ (≢< jm , ne toJ toT1 JT1)
          ∷ (sym≢ sj , sym≢ (ne toS toJ sJ)) ∷ [])
       , ((kl , ne toB toT BT) ∷ (≢< (rel km) , ne toB toT1 BT1)
          ∷ (sym≢ sk , sym≢ (ne toS toB sB)) ∷ [])
       , ((≢< (rel lm) , ne toT toT1 TT1) ∷ (sym≢ sl , sym≢ (ne toS toT sT)) ∷ [])
       , ((sym≢ sm , sym≢ (ne toS toT1 sT1)) ∷ [])
       , ([] , tt)

    Blocked : List (Fin N)
    Blocked = jj ∷ kk ∷ ll ∷ mm ∷ s ∷ tJ ∷ tB ∷ tT ∷ tT1 ∷ tS ∷ []

    -- a spare index
    fr = Fresh.fresh3 N big Blocked
                      (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))

    mJ : (jj , tJ) ∈ qq
    mJ = here Eq.refl
    mK : (kk , tB) ∈ qq
    mK = there (here Eq.refl)
    mL : (ll , tT) ∈ qq
    mL = there (there (here Eq.refl))
    mM : (mm , tT1) ∈ qq
    mM = there (there (there (here Eq.refl)))
    mS : (s , tS) ∈ qq
    mS = there (there (there (there (here Eq.refl))))

    module G (g : Fin N) (offg : All (λ y → g ≢ y) Blocked) where

      spare : Spare qq g
      spare = mk offg
        where
        mk : All (λ y → g ≢ y) Blocked → Spare qq g
        mk (gj ∷ gk ∷ gl ∷ gm ∷ gs ∷ gJ ∷ gB ∷ gT ∷ gT1 ∷ gS ∷ []) =
          (gj , gJ) ∷ (gk , gB) ∷ (gl , gT) ∷ (gm , gT1) ∷ (gs , gS) ∷ []

      gsrc : ∀ {x y} → (x , y) ∈ qq → y ≢ g
      gsrc mem e = go spare mem e
        where
        go : ∀ {r x y} → Spare r g → (x , y) ∈ r → y ≢ g
        go ((_ , gy) ∷ _) (here Eq.refl) e′ = gy (Eq.sym e′)
        go (_ ∷ sp′)      (there mm′)    e′ = go sp′ mm′ e′

      u : W
      u = Wd g qq

      img : ∀ {x y} → (x , y) ∈ qq → prm (sp u) y ≡ x
      img mem = Eq.trans (W-prm g qq _) (ρ-img qq ok mem)

      phz : ∀ {x y} → (x , y) ∈ qq → ph (sp u) y ≡ p0
      phz mem = W-ph g qq spare _ (gsrc mem)

      c : ∀ {a b a′ b′} .(ab : a <ᶠ b) .(ab′ : a′ <ᶠ b′) → (a , a′) ∈ qq → (b , b′) ∈ qq →
          (d ʷ) u • d (ki a b s ab) ≈ d (ki a′ b′ tS ab′) • (d ʷ) u
      c {a} {b} {a′} {b′} ab ab′ ma mb =
        hyb-conj a b s a′ b′ tS ab ab′ (kf-Wd g qq) (img ma) (img mb) (img mS)
                 (Eq.trans (phz ma) (Eq.sym (phz mb)))

      inv : (d ʷ) (Wr g qq) • (d ʷ) u ≈ ε
      inv = W-inv g qq spare

      result : (d ʷ) (kiw jj kk s jk • (kiw ll mm s lm • (kiw jj ll s jl • kiw kk mm s km)))
               ≈ (d ʷ) (kiw jj ll s jl • (kiw kk mm s km • (kiw jj kk s jk • kiw ll mm s lm)))
      result =
        carry inv (conj-• (c jk qJB mJ mK) (conj-• (c lm tT<tT1 mL mM)
                    (conj-• (c jl qJT mJ mL) (c km qBT1 mK mM))))
                  (conj-• (c jl qJT mJ mL) (conj-• (c km qBT1 mK mM)
                    (conj-• (c jk qJB mJ mK) (c lm tT<tT1 mL mM))))
                  yb₀
