------------------------------------------------------------------------
-- Presentations of groups
--
-- Routes on local indices, checked on forms, are paths.
--
-- Let s be a state at L = (p + 1, k, 4) whose odd entries lie at the
-- local indices ι 0, …, ι (m - 1) ≤ p.  Away from them the column of a
-- known state (Embed) is that of s, hence even, so its odd entries are
-- its odd local entries (nodd-known): a known state lies below L when
-- at most three local entries are odd, and at L when four are.
--
-- An edge with both ends below L is given (ih).  One out of a state at
-- L is an edge at L (PairEdges.At.edgesWith), which needs, for an H,
-- that it is not hard: its two entries are not odd of different
-- classes (PlainAt).  One into a state at L is that edge backwards.
-- The letters of a route are words of one generator, or X H X; the
-- check (Check) gives the levels and the plainness each edge needs, so
-- a route that passes the check from the forms of s is a path out of s
-- (route-path).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Product.Base using (_,_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction using (EdgesBelow)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Route {n : ℕ} (p : Fin n) (k′ ℓ : ℕ)
  (ih : EdgesBelow {n} (suc (toℕ p) , suc k′ , ℓ)) where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (_<_ ; _≤_)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
import Data.Vec.Properties as VecP
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; oddᶻ ; rbit)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (scV ; lde-char)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column using (nodd)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (level ; _<ₗ_ ; <ₗ-irrefl ; pivot-char)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (level-of ; ne-𝕀)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step using (scV-injective)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (Path ; path-ε ; path-• ; back ; act-gg ; _≤ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Local {n} using (upd₂ ; upd₂-i ; upd₂-j ; module Emb)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric {n} using (HsT ; XsT)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PairBase p k′ ℓ ih
  using (k ; L ; X-low ; mono-L ; module State) renaming (low to below-L)
import Examples.Groups.Real-Clifford+CH-TwoLevel.PairEdges p k′ ℓ ih as PE
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Forms using (Form)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Embed {n} using (count-emb ; module Known-at)

private
  sym≢ : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
  sym≢ ne e = ne (≡.sym e)

  t≢f : true ≢ false
  t≢f ()

------------------------------------------------------------------------
-- Edges of one generator

-- An H that is not hard at a state at L.
PlainAt : (N : Matrix n n D) .(oN : ColOrth N) → level N ≡ L → Gen n → Set
PlainAt N oN eqN (H-gen a b _) =
  oddᶻ (State.W N oN eqN ! a) ≡ true → oddᶻ (State.W N oN eqN ! b) ≡ true →
  rbit (State.W N oN eqN ! a) ≡ rbit (State.W N oN eqN ! b)
PlainAt N oN eqN (X-gen _ _ _) = ⊤
PlainAt N oN eqN (Z-gen _) = ⊤

private
  needs : (N : Matrix n n D) .(oN : ColOrth N) (eqN : level N ≡ L) (g : Gen n) →
          PlainAt N oN eqN g → PE.At.Needs N oN eqN g
  needs N oN eqN (H-gen a b ab) pl oa ob r _ = ⊥-elim (r (pl oa ob))
  needs N oN eqN (X-gen _ _ _) _ = tt
  needs N oN eqN (Z-gen _) _ = tt

  le-of : ∀ {x} → x <ₗ L ⊎ x ≡ L → x ≤ₗ L
  le-of (inj₁ lt) = inj₁ lt
  le-of (inj₂ eq) = inj₂ eq

-- The edge g out of N, from the levels of its ends and plainness at the
-- ends at L that it needs.
gen-edge : (g : Gen n) (N : Matrix n n D) .(oN : ColOrth N) →
           level N <ₗ L ⊎ level N ≡ L → level (actM g N) <ₗ L ⊎ level (actM g N) ≡ L →
           ((eqN : level N ≡ L) → PlainAt N oN eqN g) →
           (level N <ₗ L → (eqG : level (actM g N) ≡ L) → PlainAt (actM g N) (ColOrth-actMʷ [ g ]ʷ oN) eqG g) →
           Path [ g ]ʷ N oN
gen-edge g N oN (inj₁ ltN) (inj₁ ltG) _ _ = ih g N oN ltN ltG
gen-edge g N oN (inj₂ eqN) aG plN _ = PE.At.edgesWith N oN eqN g (le-of aG) (needs N oN eqN g (plN eqN))
gen-edge g N oN (inj₁ ltN) (inj₂ eqG) _ plG =
  back g N oN (PE.At.edgesWith (actM g N) (ColOrth-actMʷ [ g ]ʷ oN) eqG g
                 (inj₁ (≡.subst (_<ₗ L) (≡.sym (≡.cong level (act-gg g N))) ltN))
                 (needs (actM g N) (ColOrth-actMʷ [ g ]ʷ oN) eqG g (plG ltN eqG)))

------------------------------------------------------------------------
-- Routes on local indices of a state at L

module Local-at (s : Matrix n n D) .(o : ColOrth s) (eq : level s ≡ L) (ℓ4 : ℓ ≡ 4)
                {m : ℕ} (ι : Fin m → Fin n) (inj : ∀ {i j} → ι i ≡ ι j → i ≡ j) (ι≤p : ∀ i → ι i ≤ p)
                (out : ∀ x → (∀ i → ι i ≢ x) → oddᶻ (State.W s o eq ! x) ≡ false) where

  W₀ : Vec Z n
  W₀ = State.W s o eq

  open Emb ι inj using (emb ; emb-ι ; emb-o ; emb-ext ; where? ; loc ; emb-self)
  open Known-at p k ι inj ι≤p W₀ public

  private
    ι≢ : ∀ {i j} → i ≢ j → ι i ≢ ι j
    ι≢ i≢j e = i≢j (inj e)

    -- W₀ with the local entries 0: even everywhere.
    zeros : Vec Z m
    zeros = Vec.replicate m ZR.0#

    W̃ : Vec Z n
    W̃ = emb zeros W₀

    W̃-even : ∀ x → oddᶻ (W̃ ! x) ≡ false
    W̃-even x = at (where? x)
      where
      at : (∃ λ i → ι i ≡ x) ⊎ (∀ i → ι i ≢ x) → oddᶻ (W̃ ! x) ≡ false
      at (inj₁ (i , ≡.refl)) = ≡.trans (≡.cong oddᶻ (≡.trans (emb-ι zeros W₀ i) (VecP.lookup-replicate i ZR.0#))) ≡.refl
      at (inj₂ o′) = ≡.trans (≡.cong oddᶻ (emb-o zeros W₀ o′)) (out x o′)

  -- The odd entries of a known state are its odd local entries.
  nodd-known : ∀ e → nodd (emb e W₀) ≡ noddV e
  nodd-known e =
    ≡.trans (≡.cong nodd (emb-ext {e} {e} {W₀} {W̃} (λ _ → ≡.refl) (λ x o′ → ≡.sym (emb-o zeros W₀ o′))))
            (count-emb ι inj e W̃ W̃-even)

  -- s is known, with its local entries.
  known-s : Known s (loc W₀)
  known-s = known (≡.trans (State.colM s o eq) (≡.cong (scV k) (≡.sym (emb-self W₀)))) (State.be s o eq)

  private
    odd-local : ∀ {m′} (e : Vec Z m′) → 0 ℕ.< noddV e → ∃ λ i → oddᶻ (e ! i) ≡ true
    odd-local (x ∷ e) pos with oddᶻ x in o
    ... | true = Fin.zero , o
    ... | false = let (i , oi) = odd-local e pos in Fin.suc i , oi

    four-pos : ∀ {c} → c ≡ 4 → 0 ℕ.< c
    four-pos ≡.refl = ℕ.s≤s ℕ.z≤n

  -- The level of a known state.
  level-low : ∀ {N e} → Known N e → noddV e ℕ.< 4 → level N <ₗ L
  level-low {N} {e} K lt =
    below-L N (beK K) (emb e W₀) (colK K) (≡.subst (nodd (emb e W₀) ℕ.<_) (≡.sym ℓ4) (≡.subst (ℕ._< 4) (≡.sym (nodd-known e)) lt))

  module At-L {N : Matrix n n D} {e : Vec Z m} (K : Known N e) (four : noddV e ≡ 4) where

    private
      oe = odd-local e (four-pos four)
      i₀ = proj₁ oe
      wodd : oddᶻ (emb e W₀ ! ι i₀) ≡ true
      wodd = ≡.trans (≡.cong oddᶻ (emb-ι e W₀ i₀)) (proj₂ oe)
      ne = ne-𝕀 N p k′ (emb e W₀) (colK K) (inj₂ (ι i₀ , wodd))
      pv = pivot-char N ne (beK K)

    levelL : level N ≡ L
    levelL = ≡.trans (level-of N pv k (emb e W₀) (colK K) (inj₂ (ι i₀ , wodd)))
               (≡.cong (λ c → suc (toℕ p) , k , c) (≡.trans (nodd-known e) (≡.trans four (≡.sym ℓ4))))

  ----------------------------------------------------------------------
  -- Letters

  -- The kind of a local vector.
  Kd : Vec Z m → Set
  Kd e = noddV e ℕ.< 4 ⊎ noddV e ≡ 4

  lvl : ∀ {N e} → Known N e → Kd e → level N <ₗ L ⊎ level N ≡ L
  lvl K (inj₁ lt) = inj₁ (level-low K lt)
  lvl K (inj₂ four) = inj₂ (At-L.levelL K four)

  private
    not-both : ∀ {x} → x <ₗ L → x ≡ L → ⊥
    not-both lt ≡.refl = <ₗ-irrefl lt

    -- X keeps the level.
    keepX : ∀ {a b} (lt : a < b) → b ≤ p → (N : Matrix n n D) → level N <ₗ L ⊎ level N ≡ L →
            level (actM (X-gen a b lt) N) <ₗ L ⊎ level (actM (X-gen a b lt) N) ≡ L
    keepX lt b≤p N (inj₁ l) = inj₁ (X-low lt b≤p N l)
    keepX lt b≤p N (inj₂ e) = inj₂ (mono-L (X-gen _ _ lt) tt b≤p N e)

  -- The numerator of a known state at L is its embedding.
  W-at : ∀ {N e} → Known N e → .(oN : ColOrth N) (eqN : level N ≡ L) → State.W N oN eqN ≡ emb e W₀
  W-at {N} {e} K oN eqN = scV-injective k _ _ (≡.trans (≡.sym (State.colM N oN eqN)) (colK K))

  -- Plainness at a known state at L, from plainness of its local entries.
  plain-at : ∀ {N e} → Known N e → .(oN : ColOrth N) (eqN : level N ≡ L) (a b : Fin m) .(lt : ι a < ι b) →
             (oddᶻ (e ! a) ≡ true → oddᶻ (e ! b) ≡ true → rbit (e ! a) ≡ rbit (e ! b)) →
             PlainAt N oN eqN (H-gen (ι a) (ι b) lt)
  plain-at {N} {e} K oN eqN a b lt pl oa ob =
    ≡.trans (≡.cong rbit ea) (≡.trans (pl (≡.trans (≡.sym (≡.cong oddᶻ ea)) oa) (≡.trans (≡.sym (≡.cong oddᶻ eb)) ob))
                                      (≡.sym (≡.cong rbit eb)))
    where
    ea : State.W N oN eqN ! ι a ≡ e ! a
    ea = ≡.trans (≡.cong (_! ι a) (W-at K oN eqN)) (emb-ι e W₀ a)
    eb : State.W N oN eqN ! ι b ≡ e ! b
    eb = ≡.trans (≡.cong (_! ι b) (W-at K oN eqN)) (emb-ι e W₀ b)

  -- A letter is a path, given the kinds of its ends and plainness where
  -- an end at L needs it.
  letter-path : ∀ {N e e′} (g : Let m) → Distinct g → Step g e e′ → Known N e → .(oN : ColOrth N) →
                (κ : Kd e) (κ′ : Kd e′) → (noddV e ≡ 4 → Plain g e) → (noddV e ℕ.< 4 → noddV e′ ≡ 4 → Plain g e′) →
                Path (wordL g) N oN
  letter-path {N} {e} {e′} (Hˡ i j) d (stepH α β sum dif) K oN κ κ′ pl pl′ = pathH (FinP.<-cmp (ι i) (ι j))
    where
    pathH : (t : Tri (ι i < ι j) (ι i ≡ ι j) (ι j < ι i)) → Path (HsT (ι i) (ι j) t) N oN
    pathH (tri< lt _ _) = gen-edge (H-gen (ι i) (ι j) lt) N oN (lvl K κ) (lvl K′ κ′) (plN κ) (plG κ κ′)
      where
      K′ = known-Hgen i j lt α β sum dif K
      plN : Kd e → (eqN : level N ≡ L) → PlainAt N oN eqN (H-gen (ι i) (ι j) lt)
      plN (inj₁ l) eqN = ⊥-elim (not-both (level-low K l) eqN)
      plN (inj₂ four) eqN = plain-at K oN eqN i j lt (pl four)
      plG : Kd e → Kd e′ → level N <ₗ L → (eqG : level (actM (H-gen (ι i) (ι j) lt) N) ≡ L) →
            PlainAt (actM (H-gen (ι i) (ι j) lt) N) (ColOrth-actMʷ [ H-gen (ι i) (ι j) lt ]ʷ oN) eqG (H-gen (ι i) (ι j) lt)
      plG (inj₂ four) _ ltN eqG = ⊥-elim (not-both ltN (At-L.levelL K four))
      plG (inj₁ _) (inj₁ l′) ltN eqG = ⊥-elim (not-both (level-low K′ l′) eqG)
      plG (inj₁ l) (inj₂ four′) ltN eqG = plain-at K′ (ColOrth-actMʷ [ H-gen (ι i) (ι j) lt ]ʷ oN) eqG i j lt (pl′ l four′)
    pathH (tri≈ _ eq _) = ⊥-elim (d (inj eq))
    pathH (tri> _ _ gt) =
      path-• [ X₁ ]ʷ ([ H₁ ]ʷ • [ X₁ ]ʷ) N oN
        (gen-edge X₁ N₂ (ColOrth-actMʷ ([ H₁ ]ʷ • [ X₁ ]ʷ) oN) lv₂ lv₃ (λ _ → tt) (λ _ _ → tt))
        (path-• [ H₁ ]ʷ [ X₁ ]ʷ N oN
          (gen-edge H₁ N₁ (ColOrth-actMʷ [ X₁ ]ʷ oN) lv₁ lv₂ (plN₁ κ) (plG₁ κ κ′))
          (gen-edge X₁ N oN lv₀ lv₁ (λ _ → tt) (λ _ _ → tt)))
      where
      open Rev {i} {j} gt using (X₁ ; H₁ ; swapK)
      j≢i = sym≢ d
      e₁ = upd₂ j i (e ! i) (e ! j) e
      e₂ = upd₂ j i α β e₁
      N₁ = actM X₁ N
      N₂ = actM H₁ N₁
      N₃ = actM X₁ N₂
      i≤p = ι≤p i
      K₁ : Known N₁ e₁
      K₁ = swapK K
      e₁j : e₁ ! j ≡ e ! i
      e₁j = upd₂-i j i (e ! i) (e ! j) e
      e₁i : e₁ ! i ≡ e ! j
      e₁i = upd₂-j j i (e ! i) (e ! j) e j≢i
      K₂ : Known N₂ e₂
      K₂ = known-Hgen j i gt α β (≡.trans (≡.cong₂ ZR._+_ e₁j e₁i) sum) (≡.trans (≡.cong₂ ZR._-_ e₁j e₁i) dif) K₁
      e₂j : e₂ ! j ≡ α
      e₂j = upd₂-i j i α β e₁
      e₂i : e₂ ! i ≡ β
      e₂i = upd₂-j j i α β e₁ j≢i
      K₃ : Known N₃ e′
      K₃ = ≡.subst (Known N₃) (≡.trans (≡.cong₂ (λ s t → upd₂ j i s t e₂) e₂i e₂j) (swap-upd i j α β e d)) (swapK K₂)
      lv₀ = lvl K κ
      lv₁ = keepX gt i≤p N lv₀
      lv₃ = lvl K₃ κ′
      lv₂ : level N₂ <ₗ L ⊎ level N₂ ≡ L
      lv₂ = ≡.subst (λ M → level M <ₗ L ⊎ level M ≡ L) (act-gg X₁ N₂) (keepX gt i≤p N₃ lv₃)
      e′i : e′ ! i ≡ α
      e′i = upd₂-i i j α β e
      e′j : e′ ! j ≡ β
      e′j = upd₂-j i j α β e d
      plN₁ : Kd e → (eq₁ : level N₁ ≡ L) → PlainAt N₁ (ColOrth-actMʷ [ X₁ ]ʷ oN) eq₁ H₁
      plN₁ (inj₁ l) eq₁ = ⊥-elim (not-both (X-low gt i≤p N (level-low K l)) eq₁)
      plN₁ (inj₂ four) eq₁ = plain-at K₁ (ColOrth-actMʷ [ X₁ ]ʷ oN) eq₁ j i gt λ oa ob →
        ≡.trans (≡.cong rbit e₁j) (≡.trans (pl four (≡.trans (≡.sym (≡.cong oddᶻ e₁j)) oa) (≡.trans (≡.sym (≡.cong oddᶻ e₁i)) ob))
                                           (≡.sym (≡.cong rbit e₁i)))
      plG₁ : Kd e → Kd e′ → level N₁ <ₗ L → (eq₂ : level N₂ ≡ L) → PlainAt N₂ (ColOrth-actMʷ ([ H₁ ]ʷ • [ X₁ ]ʷ) oN) eq₂ H₁
      plG₁ (inj₂ four) _ lt₁ eq₂ = ⊥-elim (not-both lt₁ (mono-L X₁ tt i≤p N (At-L.levelL K four)))
      plG₁ (inj₁ _) (inj₁ l′) lt₁ eq₂ =
        ⊥-elim (not-both (≡.subst (_<ₗ L) (≡.cong level (act-gg X₁ N₂)) (X-low gt i≤p N₃ (level-low K₃ l′))) eq₂)
      plG₁ (inj₁ l) (inj₂ four′) lt₁ eq₂ = plain-at K₂ (ColOrth-actMʷ ([ H₁ ]ʷ • [ X₁ ]ʷ) oN) eq₂ j i gt λ oa ob →
        ≡.trans (≡.cong rbit e₂j)
          (≡.trans (≡.trans (≡.sym (≡.cong rbit e′i))
                     (≡.trans (pl′ l four′ (≡.trans (≡.cong oddᶻ e′i) (≡.trans (≡.sym (≡.cong oddᶻ e₂j)) oa))
                                           (≡.trans (≡.cong oddᶻ e′j) (≡.trans (≡.sym (≡.cong oddᶻ e₂i)) ob)))
                              (≡.cong rbit e′j)))
                   (≡.sym (≡.cong rbit e₂i)))
  letter-path {N} {e} (Xˡ i j) d stepX K oN κ κ′ _ _ = pathX (FinP.<-cmp (ι i) (ι j))
    where
    pathX : (t : Tri (ι i < ι j) (ι i ≡ ι j) (ι j < ι i)) → Path (XsT (ι i) (ι j) t) N oN
    pathX (tri< lt _ _) = gen-edge (X-gen (ι i) (ι j) lt) N oN (lvl K κ) (lvl (known-Xgen i j lt K) κ′) (λ _ → tt) (λ _ _ → tt)
    pathX (tri≈ _ eq _) = ⊥-elim (d (inj eq))
    pathX (tri> _ _ gt) =
      gen-edge (X-gen (ι j) (ι i) gt) N oN (lvl K κ)
        (lvl (≡.subst (Known (actM (X-gen (ι j) (ι i) gt) N)) (swap-sym i j e d) (known-Xgen j i gt K)) κ′)
        (λ _ → tt) (λ _ _ → tt)
  letter-path {N} {e} (Zˡ i) d stepZ K oN κ κ′ _ _ =
    gen-edge (Z-gen (ι i)) N oN (lvl K κ) (lvl (known-Z i K) κ′) (λ _ → tt) (λ _ _ → tt)

  ----------------------------------------------------------------------
  -- Routes

  private
    ∧-split : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
    ∧-split {true} {true} _ = ≡.refl , ≡.refl

    lt4≢ : ∀ {c} → c ℕ.< 4 → c ≡ 4 → ⊥
    lt4≢ lt ≡.refl = ℕP.<-irrefl ≡.refl lt

    -- What a successful edge check gives at the values.
    edge-facts : ∀ {r} (g : Let m) (fs fs′ : Vec (Form r) m) → edgeF g (kindF fs) fs (kindF fs′) fs′ ≡ true →
                 ∀ ρ → Kd (⟦ fs ⟧ᵛ ρ) × Kd (⟦ fs′ ⟧ᵛ ρ) ×
                       (noddV (⟦ fs ⟧ᵛ ρ) ≡ 4 → Plain g (⟦ fs ⟧ᵛ ρ)) ×
                       (noddV (⟦ fs ⟧ᵛ ρ) ℕ.< 4 → noddV (⟦ fs′ ⟧ᵛ ρ) ≡ 4 → Plain g (⟦ fs′ ⟧ᵛ ρ))
    edge-facts g fs fs′ ok ρ with kindF fs in k₁ | kindF fs′ in k₂
    ... | just low | just low =
      inj₁ (proj₁ (kindF-sound fs k₁ ρ) ≡.refl) , inj₁ (proj₁ (kindF-sound fs′ k₂ ρ) ≡.refl) ,
      (λ f → ⊥-elim (lt4≢ (proj₁ (kindF-sound fs k₁ ρ) ≡.refl) f)) ,
      (λ _ f → ⊥-elim (lt4≢ (proj₁ (kindF-sound fs′ k₂ ρ) ≡.refl) f))
    ... | just low | just atL =
      inj₁ (proj₁ (kindF-sound fs k₁ ρ) ≡.refl) , inj₂ (proj₂ (kindF-sound fs′ k₂ ρ) ≡.refl) ,
      (λ f → ⊥-elim (lt4≢ (proj₁ (kindF-sound fs k₁ ρ) ≡.refl) f)) ,
      (λ _ _ → plainF-sound g fs′ ok ρ)
    ... | just atL | just low =
      inj₂ (proj₂ (kindF-sound fs k₁ ρ) ≡.refl) , inj₁ (proj₁ (kindF-sound fs′ k₂ ρ) ≡.refl) ,
      (λ _ → plainF-sound g fs ok ρ) ,
      (λ l _ → ⊥-elim (lt4≢ l (proj₂ (kindF-sound fs k₁ ρ) ≡.refl)))
    ... | just atL | just atL =
      inj₂ (proj₂ (kindF-sound fs k₁ ρ) ≡.refl) , inj₂ (proj₂ (kindF-sound fs′ k₂ ρ) ≡.refl) ,
      (λ _ → plainF-sound g fs ok ρ) ,
      (λ l _ → ⊥-elim (lt4≢ l (proj₂ (kindF-sound fs k₁ ρ) ≡.refl)))
    ... | just low | nothing = ⊥-elim (t≢f (≡.sym ok))
    ... | just atL | nothing = ⊥-elim (t≢f (≡.sym ok))
    ... | nothing | _ = ⊥-elim (t≢f (≡.sym ok))

  -- A route that passes the check is a path.
  route-path : ∀ {r} (gs : Route m) (fs : Vec (Form r) m) (ρ : Vec Z r) {N : Matrix n n D} .(oN : ColOrth N) →
               check gs fs ≡ true → Known N (⟦ fs ⟧ᵛ ρ) → Path (wordR gs) N oN
  route-path [] fs ρ {N} oN _ K = path-ε N oN
  route-path (g ∷ gs) fs ρ {N} oN ok K with stepF g fs in st
  ... | nothing = ⊥-elim (t≢f (≡.sym ok))
  ... | just fs′ =
    path-• (wordR gs) (wordL g) N oN
      (route-path gs fs′ ρ (ColOrth-actMʷ (wordL g) oN) rest (known-step g dg (stepF-sound g fs st ρ) K))
      (letter-path g dg (stepF-sound g fs st ρ) K oN κ κ′ pl pl′)
    where
    sp₁ = ∧-split {distinctF g} ok
    sp₂ = ∧-split {edgeF g (kindF fs) fs (kindF fs′) fs′} (proj₂ sp₁)
    dg = distinctF-sound g (proj₁ sp₁)
    rest = proj₂ sp₂
    facts = edge-facts g fs fs′ (proj₁ sp₂) ρ
    κ = proj₁ facts
    κ′ = proj₁ (proj₂ facts)
    pl = proj₁ (proj₂ (proj₂ facts))
    pl′ = proj₂ (proj₂ (proj₂ facts))
