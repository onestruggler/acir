------------------------------------------------------------------------
-- Presentations of groups
--
-- The paper's path out of a state with eight known odd entries, for
-- the edge X_[d,e] when e is odd (Lemma A.20, Subcase 1.2.2.3).
--
-- Let σ be at the level of s, with pivot column U / 2ᴷ whose first odd
-- entries are a < b < c < d < e < f < g < h.  The paper's syllable T₁
-- on a, b, c, d is a path out of σ (it is a word of X's and (-1)'s
-- times the normal syllable), and halves those entries; the syllable
-- T₂ on e, f, g, h halves those.  The halves after T₁ have parities
-- (¬Σ₁, Σ₁, Σ₁, Σ₁), those after T₂ (¬Σ₂, Σ₂, Σ₂, Σ₂) (XEStep).  The
-- signed swap S of a with e (if Σ₁ ≠ Σ₂) or with h (if Σ₁ = Σ₂) leaves
-- an even number of odd halves on each quadruple, so K and K′ keep
-- every entry a..h even (EvenK).  Every state after T₁ thus has fewer
-- odd entries than s at the same exponent, or a smaller exponent, and
-- lies below the level of s (QuadXETail.level-under).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (col ; ColOrth ; actM)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (pivot ; level)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (lde)
import Examples.Groups.CCX+HH-TwoLevel.Reduction as R

module Examples.Groups.CCX+HH-TwoLevel.QuadXEBase {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p)
  {k′ : ℕ} (ks : lde (col s p) ≡ suc k′) (ih : R.EdgesBelow {n} (level s)) where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Nullary using (Dec ; yes ; no)

open import Word.Base
import Presentation.Base as PB
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (oddℤ ; oddℤ-neg)
open import Examples.Groups.CCX+HH-TwoLevel.Lde
  using (scV ; Minimal ; Odd ; Even ; lde-≤ ; lde-char ; all-even? ; halveV ; scV-halve ; ¬Even⇒Odd ; Odd⇒¬Even ; num ; even-2*)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (_!_ ; actMʷ ; actV ; actVʷ ; col-actMʷ ; col-actM ; ColOrth-actMʷ ; 𝕀)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot
  using (_<ₗ_ ; Beyond ; pivot-char ; pivot-just ; level-just ; lvlAt ; Lvl)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable using (syl ; step ; top ; Within ; Beyond-actM ; Beyond-actMʷ)
open import Examples.Groups.CCX+HH-TwoLevel.Levels using (<ₗ-trans ; mono-level ; Mono)
open import Examples.Groups.CCX+HH-TwoLevel.Engine using (⟪_⟫)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; gen ; ι)
import Data.Fin.Base as F
open import Examples.Groups.CCX+HH-TwoLevel.Residue using (τ)
open import Examples.Groups.CCX+HH-TwoLevel.TauSyl using (mτ)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count-lt)
open R {n} using (Path ; Low ; path-• ; path-below)
open import Examples.Groups.CCX+HH-TwoLevel.PathTools {n} using (path-cong ; module Below)
open import Examples.Groups.CCX+HH-TwoLevel.States {n}
  using (MonoWord ; mono-word-below ; mono-word-level ; path-normal ; lt-step ; syl-of ; level-of ; ne-𝕀)
import Examples.Groups.CCX+HH-TwoLevel.XEStep as XS

-- (QuadBase through QuadXETail: one instance of it, so that the indices
-- a, b, c, d here and there are the same names.)
open import Examples.Groups.CCX+HH-TwoLevel.QuadXETail s o ps ks ih public

open PB (_===_ {n}) using (_≈_) renaming (sym to ≈sym)
open Below {L = level s} ih using (bridge)
import Data.Integer.Solver as ℤSolver

private
  module ℤS = ℤSolver.+-*-Solver
  open ℤS using (_:+_ ; _:*_ ; :-_ ; _:=_ ; con)

private
  lvs′ : level s ≡ (suc (toℕ p) , K′ , nodd W)
  lvs′ = ≡.trans lvl (≡.cong (λ k → suc (toℕ p) , k , nodd W) ks)

------------------------------------------------------------------------
-- Words of signs and their indices

private
  within-mτ₁ : ∀ (x : Fin n) τ → x ≤ p → Within p ⟪ mτ x τ ⟫
  within-mτ₁ x true h = h , tt
  within-mτ₁ x false h = tt

  within-mτ : ∀ (x : Fin n) τ (l : List (Gen n)) → x ≤ p → Within p ⟪ l ⟫ → Within p ⟪ mτ x τ ++ l ⟫
  within-mτ x true l h w = h , w
  within-mτ x false l h w = w

  mono-mτ₁ : ∀ (x : Fin n) τ → x ≤ p → MonoWord p ⟪ mτ x τ ⟫
  mono-mτ₁ x true h = h , tt
  mono-mτ₁ x false h = tt

  mono-mτ : ∀ (x : Fin n) τ (l : List (Gen n)) → x ≤ p → MonoWord p ⟪ l ⟫ → MonoWord p ⟪ mτ x τ ++ l ⟫
  mono-mτ x true l h w = h , w
  mono-mτ x false l h w = w

  -- Lists without K, relabelled into indices ≤ p, are words of X's and
  -- (-1)'s.
  mono-map : ∀ (e : Emb 4 n) → (∀ z → ι e z ≤ p) → (xs : List (Gen 4)) → XS.noK xs ≡ true →
             MonoWord p ⟪ map (gen e) xs ⟫
  mono-map e h [] _ = tt
  mono-map e h (M-gen x ∷ xs) k = h x , mono-map e h xs k
  mono-map e h (X-gen x y q ∷ xs) k = h y , mono-map e h xs k
  mono-map e h (K-gen _ _ _ _ _ _ _ ∷ xs) ()

------------------------------------------------------------------------
-- The descent from a state with eight known odd entries

module Descent (σ : Matrix n n D) .(oσ : ColOrth σ) (U : Vec ℤ n) (eqσ : col σ p ≡ scV K′ U)
  (beσ : Beyond p σ) (cnt : nodd U ≡ nodd W)
  {e f g h : Fin n}
  (fo₀ : firstOdd U ≡ just a) (na₀ : nextOdd a U ≡ just b) (nb₀ : nextOdd b U ≡ just c) (nc₀ : nextOdd c U ≡ just d)
  (nd₀ : nextOdd d U ≡ just e) (ne₀ : nextOdd e U ≡ just f) (nf₀ : nextOdd f U ≡ just g) (ng₀ : nextOdd g U ≡ just h)
  (h≤p : h ≤ p) where

  d<e : d < e
  d<e = proj₁ (nextOdd-spec U nd₀)
  e<f : e < f
  e<f = proj₁ (nextOdd-spec U ne₀)
  f<g : f < g
  f<g = proj₁ (nextOdd-spec U nf₀)
  g<h : g < h
  g<h = proj₁ (nextOdd-spec U ng₀)

  private
    ne< : ∀ {u v : Fin n} → u < v → u ≢ v
    ne< lt e = ℕP.<-irrefl (≡.cong toℕ e) lt
    gt : ∀ {u v : Fin n} → u < v → v ≢ u
    gt lt e = ne< lt (≡.sym e)
    _⟨<⟩_ = FinP.<-trans
    infixr 5 _⟨<⟩_
    le : ∀ {u v : Fin n} → u < v → u ≤ v
    le = ℕP.<⇒≤
    -- Bounds.
    g≤p = ℕP.≤-trans (le g<h) h≤p
    f≤p = ℕP.≤-trans (le f<g) g≤p
    e≤p = ℕP.≤-trans (le e<f) f≤p
    d≤p′ = ℕP.≤-trans (le d<e) e≤p
    c≤p = ℕP.≤-trans (le c<d) d≤p′
    b≤p = ℕP.≤-trans (le b<c) c≤p
    a≤p = ℕP.≤-trans (le a<b) b≤p
    -- The odd entries of U.
    oaU : Odd (U ! a)
    oaU = proj₁ (firstOdd-spec U fo₀)
    obU = proj₁ (proj₂ (nextOdd-spec U na₀))
    ocU = proj₁ (proj₂ (nextOdd-spec U nb₀))
    odU = proj₁ (proj₂ (nextOdd-spec U nc₀))
    oeU = proj₁ (proj₂ (nextOdd-spec U nd₀))
    ofU = proj₁ (proj₂ (nextOdd-spec U ne₀))
    ogU = proj₁ (proj₂ (nextOdd-spec U nf₀))
    ohU = proj₁ (proj₂ (nextOdd-spec U ng₀))

  ----------------------------------------------------------------------
  -- The first syllable, a path out of σ

  -- (Named, so that the terms mentioning its fields share it.)
  tr₁ : XS.TauR U a b c d a<b b<c c<d
  tr₁ = XS.tau U a<b b<c c<d oaU obU ocU odU

  module T₁ = XS.TauR tr₁

  T1w : Word (Gen n)
  T1w = XS.τword U a<b b<c c<d

  private
    minU : Minimal K′ U
    minU = inj₂ (a , oaU)
    pivσ : pivot σ ≡ just p
    pivσ = pivot-char σ (ne-𝕀 σ p k′ U eqσ minU) beσ
    lvσ : level σ ≡ level s
    lvσ = ≡.trans (level-of σ pivσ K′ U eqσ minU) (≡.trans (≡.cong (λ m → suc (toℕ p) , K′ , m) cnt) (≡.sym lvs′))
    sylσ : syl σ ≡ [ K-gen a b c d a<b b<c c<d ]ʷ • Mτ a (((τ (U ! a) xor τ (U ! b)) xor τ (U ! c)) xor τ (U ! d))
    sylσ = ≡.trans (syl-of σ pivσ K′ U eqσ minU) (sylData-quad {p = p} k′ U fo₀ na₀ nb₀ nc₀ a<b b<c c<d)

  pT1 : Path T1w σ oσ
  pT1 = path-cong (≈sym T₁.rel) σ oσ (path-• T₁.S′ N σ oσ pS′ pNσ)
    where
    N = [ K-gen a b c d a<b b<c c<d ]ʷ • Mτ a (((τ (U ! a) xor τ (U ! b)) xor τ (U ! c)) xor τ (U ! d))
    pNσ : Path N σ oσ
    pNσ = ≡.subst (λ w → Path w σ oσ) sylσ (path-normal σ oσ pivσ)
    lN : level (actMʷ N σ) <ₗ level s
    lN = ≡.subst₂ _<ₗ_ (≡.cong (λ w → level (actMʷ w σ)) sylσ) lvσ (lt-step σ oσ pivσ)
    pS′ : Path T₁.S′ (actMʷ N σ) (ColOrth-actMʷ N oσ)
    pS′ = path-below ih T₁.S′ (actMʷ N σ) (ColOrth-actMʷ N oσ)
            (mono-word-below T₁.S′ (T₁.S′-mono a≤p b≤p c≤p d≤p′) (actMʷ N σ) lN lB)

  ----------------------------------------------------------------------
  -- The columns along the rest

  σ₁ : Matrix n n D
  σ₁ = actMʷ T1w σ

  col₁ : col σ₁ p ≡ scV K′ T₁.Wh
  col₁ = ≡.trans (col-actMʷ T1w σ p) (≡.trans (≡.cong (actVʷ T1w) eqσ) (T₁.col-T K′))

  private
    -- Beyond d, the first syllable changes nothing.
    hi₁ : ∀ {z} → d < z → T₁.Wh ! z ≡ U ! z
    hi₁ dz = T₁.Wh-o (gt (a<b ⟨<⟩ b<c ⟨<⟩ c<d ⟨<⟩ dz)) (gt (b<c ⟨<⟩ c<d ⟨<⟩ dz)) (gt (c<d ⟨<⟩ dz)) (gt dz)
    odd₁ : ∀ {z} → d < z → Odd (U ! z) → Odd (T₁.Wh ! z)
    odd₁ dz oz = ≡.trans (≡.cong oddℤ (hi₁ dz)) oz

  tr₂ : XS.TauR T₁.Wh e f g h e<f f<g g<h
  tr₂ = XS.tau T₁.Wh e<f f<g g<h (odd₁ d<e oeU) (odd₁ (d<e ⟨<⟩ e<f) ofU)
                     (odd₁ (d<e ⟨<⟩ e<f ⟨<⟩ f<g) ogU) (odd₁ (d<e ⟨<⟩ e<f ⟨<⟩ f<g ⟨<⟩ g<h) ohU)

  module T₂ = XS.TauR tr₂

  T2w : Word (Gen n)
  T2w = XS.τword T₁.Wh e<f f<g g<h

  -- The signs of the second syllable are those of U.
  τ₂≡ : τ (T₁.Wh ! e) ≡ τ (U ! e) × τ (T₁.Wh ! f) ≡ τ (U ! f) × τ (T₁.Wh ! g) ≡ τ (U ! g) × τ (T₁.Wh ! h) ≡ τ (U ! h)
  τ₂≡ = ≡.cong τ (hi₁ d<e) , ≡.cong τ (hi₁ (d<e ⟨<⟩ e<f)) , ≡.cong τ (hi₁ (d<e ⟨<⟩ e<f ⟨<⟩ f<g)) ,
        ≡.cong τ (hi₁ (d<e ⟨<⟩ e<f ⟨<⟩ f<g ⟨<⟩ g<h))

  -- The choice of the swap.
  useE : Bool
  useE = T₁.Σz xor T₂.Σz

  private
    four : ∀ {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : Bool} → x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ → x₄ ≡ y₄ →
           ((x₁ xor x₂) xor x₃) xor x₄ ≡ ((y₁ xor y₂) xor y₃) xor y₄
    four ≡.refl ≡.refl ≡.refl ≡.refl = ≡.refl

  -- It depends on the eight entries alone.
  useE-ζ : (oa : Odd (U ! a)) (ob : Odd (U ! b)) (oc : Odd (U ! c)) (od : Odd (U ! d))
           (oe : Odd (U ! e)) (of : Odd (U ! f)) (og : Odd (U ! g)) (oh : Odd (U ! h)) →
           useE ≡ (((XS.ζ (U ! a) oa xor XS.ζ (U ! b) ob) xor XS.ζ (U ! c) oc) xor XS.ζ (U ! d) od) xor
                  (((XS.ζ (U ! e) oe xor XS.ζ (U ! f) of) xor XS.ζ (U ! g) og) xor XS.ζ (U ! h) oh)
  useE-ζ oa ob oc od oe of og oh = ≡.cong₂ _xor_
    (≡.trans (XS.tau-Σz U a<b b<c c<d oaU obU ocU odU)
      (four (XS.ζ-irr (U ! a) oaU oa) (XS.ζ-irr (U ! b) obU ob) (XS.ζ-irr (U ! c) ocU oc) (XS.ζ-irr (U ! d) odU od)))
    (≡.trans (XS.tau-Σz T₁.Wh e<f f<g g<h (odd₁ d<e oeU) (odd₁ (d<e ⟨<⟩ e<f) ofU)
                (odd₁ (d<e ⟨<⟩ e<f ⟨<⟩ f<g) ogU) (odd₁ (d<e ⟨<⟩ e<f ⟨<⟩ f<g ⟨<⟩ g<h) ohU))
      (four (XS.ζ-cong (hi₁ d<e) _ oe) (XS.ζ-cong (hi₁ (d<e ⟨<⟩ e<f)) _ of)
            (XS.ζ-cong (hi₁ (d<e ⟨<⟩ e<f ⟨<⟩ f<g)) _ og) (XS.ζ-cong (hi₁ (d<e ⟨<⟩ e<f ⟨<⟩ f<g ⟨<⟩ g<h)) _ oh)))

  -- (-1)_[a] (-1)_[x] X_[a,x], with x = e or h.
  xS : Bool → Fin n
  xS true = e
  xS false = h

  a<xS : ∀ u → a < xS u
  a<xS true = a<b ⟨<⟩ b<c ⟨<⟩ c<d ⟨<⟩ d<e
  a<xS false = a<b ⟨<⟩ b<c ⟨<⟩ c<d ⟨<⟩ d<e ⟨<⟩ e<f ⟨<⟩ f<g ⟨<⟩ g<h

  Sw : Bool → Word (Gen n)
  Sw u = [ M-gen a ]ʷ • ([ M-gen (xS u) ]ʷ • [ X-gen a (xS u) (a<xS u) ]ʷ)

  K₁g K₂g : Gen n
  K₁g = K-gen a b c d a<b b<c c<d
  K₂g = K-gen e f g h e<f f<g g<h

  -- After the first syllable: K′ K S T₂.
  Rest : Bool → Word (Gen n)
  Rest u = [ K₂g ]ʷ • ([ K₁g ]ʷ • (Sw u • T2w))

  ----------------------------------------------------------------------
  -- Below the level of s, all the way

  private
    neg2 : ∀ x → ℤ.- (+ 2 ℤ.* x) ≡ + 2 ℤ.* (ℤ.- x)
    neg2 = ℤS.solve 1 (λ x → :- (con (+ 2) :* x) := con (+ 2) :* (:- x)) ≡.refl

    under′ : ∀ (M : Matrix n n D) (V : Vec ℤ n) → Beyond p M → col M p ≡ scV K′ V →
             (∀ x → Odd (V ! x) → Odd (U ! x)) → Even (V ! a) → level M <ₗ level s
    under′ = under U cnt oaU

    -- Signs and their indices.
    within-T : ∀ {i j k l : Fin n} .(ij : i < j) .(jk : j < k) .(kl : k < l) τ₀ τ₁ τ₂ τ₃ →
               i ≤ p → j ≤ p → k ≤ p → l ≤ p →
               Within p ⟪ K-gen i j k l ij jk kl ∷ (mτ i τ₀ ++ (mτ j τ₁ ++ (mτ k τ₂ ++ mτ l τ₃))) ⟫
    within-T {i} {j} {k} {l} ij jk kl τ₀ τ₁ τ₂ τ₃ hi hj hk hl =
      hl , within-mτ i τ₀ _ hi (within-mτ j τ₁ _ hj (within-mτ k τ₂ _ hk (within-mτ₁ l τ₃ hl)))

    mono-signs : ∀ (i j k l : Fin n) τ₀ τ₁ τ₂ τ₃ → i ≤ p → j ≤ p → k ≤ p → l ≤ p →
                 MonoWord p ⟪ mτ i τ₀ ++ (mτ j τ₁ ++ (mτ k τ₂ ++ mτ l τ₃)) ⟫
    mono-signs i j k l τ₀ τ₁ τ₂ τ₃ hi hj hk hl = mono-mτ i τ₀ _ hi (mono-mτ j τ₁ _ hj (mono-mτ k τ₂ _ hk (mono-mτ₁ l τ₃ hl)))

    -- The states.
    be₁ : Beyond p σ₁
    be₁ = Beyond-actMʷ T1w (within-T a<b b<c c<d (τ (U ! a)) (τ (U ! b)) (τ (U ! c)) (τ (U ! d)) a≤p b≤p c≤p d≤p′) beσ

    ev₁a : Even (T₁.Wh ! a)
    ev₁a = ev2 T₁.hA T₁.Wh-i
    sub₁ : ∀ x → Odd (T₁.Wh ! x) → Odd (U ! x)
    sub₁ = sub4 T₁.Wh U T₁.Wh-o ev₁a (ev2 T₁.hB T₁.Wh-j) (ev2 T₁.hC T₁.Wh-k) (ev2 T₁.hD T₁.Wh-l)

  lσ₁ : level σ₁ <ₗ level s
  lσ₁ = under′ σ₁ T₁.Wh be₁ col₁ sub₁ ev₁a

  private
    signs₂ : Word (Gen n)
    signs₂ = ⟪ mτ e (τ (T₁.Wh ! e)) ++ (mτ f (τ (T₁.Wh ! f)) ++ (mτ g (τ (T₁.Wh ! g)) ++ mτ h (τ (T₁.Wh ! h)))) ⟫
    m₂ : MonoWord p signs₂
    m₂ = mono-signs e f g h (τ (T₁.Wh ! e)) (τ (T₁.Wh ! f)) (τ (T₁.Wh ! g)) (τ (T₁.Wh ! h)) e≤p f≤p g≤p h≤p

  σ₂ : Matrix n n D
  σ₂ = actMʷ T2w σ₁

  col₂ : col σ₂ p ≡ scV K′ T₂.Wh
  col₂ = ≡.trans (col-actMʷ T2w σ₁ p) (≡.trans (≡.cong (actVʷ T2w) col₁) (T₂.col-T K′))

  private
    be₂ : Beyond p σ₂
    be₂ = Beyond-actMʷ T2w (within-T e<f f<g g<h (τ (T₁.Wh ! e)) (τ (T₁.Wh ! f)) (τ (T₁.Wh ! g)) (τ (T₁.Wh ! h)) e≤p f≤p g≤p h≤p) be₁
    -- T₂ leaves a, b, c, d.
    lo₂ : ∀ {z} → z < e → T₂.Wh ! z ≡ T₁.Wh ! z
    lo₂ ze = T₂.Wh-o (ne< ze) (ne< (ze ⟨<⟩ e<f)) (ne< (ze ⟨<⟩ e<f ⟨<⟩ f<g)) (ne< (ze ⟨<⟩ e<f ⟨<⟩ f<g ⟨<⟩ g<h))
    ae = a<b ⟨<⟩ b<c ⟨<⟩ c<d ⟨<⟩ d<e
    be′ = b<c ⟨<⟩ c<d ⟨<⟩ d<e
    ce = c<d ⟨<⟩ d<e
    -- U₂ = T₂.Wh: halves on a..h.
    w₂a : T₂.Wh ! a ≡ + 2 ℤ.* T₁.hA
    w₂a = ≡.trans (lo₂ ae) T₁.Wh-i
    w₂b : T₂.Wh ! b ≡ + 2 ℤ.* T₁.hB
    w₂b = ≡.trans (lo₂ be′) T₁.Wh-j
    w₂c : T₂.Wh ! c ≡ + 2 ℤ.* T₁.hC
    w₂c = ≡.trans (lo₂ ce) T₁.Wh-k
    w₂d : T₂.Wh ! d ≡ + 2 ℤ.* T₁.hD
    w₂d = ≡.trans (lo₂ d<e) T₁.Wh-l
    sub₂ : ∀ x → Odd (T₂.Wh ! x) → Odd (U ! x)
    sub₂ x ox = sub₁ x (sub4 T₂.Wh T₁.Wh T₂.Wh-o (ev2 T₂.hA T₂.Wh-i) (ev2 T₂.hB T₂.Wh-j) (ev2 T₂.hC T₂.Wh-k) (ev2 T₂.hD T₂.Wh-l) x ox)

  lσ₂ : level σ₂ <ₗ level s
  lσ₂ = under′ σ₂ T₂.Wh be₂ col₂ sub₂ (ev2 T₁.hA w₂a)

  ----------------------------------------------------------------------
  -- The descent

  -- (A product, not a record: the positivity checker would normalise the
  -- field types, and with them the levels of the states.)
  Result : Bool → Set
  Result u = Low (level s) (Rest u) σ₁ × level (actMʷ (Rest u) σ₁) <ₗ level s

  private
    xor-lemma₁ : ∀ x y → x xor y ≡ true → ((not y xor x) xor x) xor x ≡ false
    xor-lemma₁ true  false _ = ≡.refl
    xor-lemma₁ false true  _ = ≡.refl
    xor-lemma₁ true  true  ()
    xor-lemma₁ false false ()
    xor-lemma₂ : ∀ x y → x xor y ≡ true → ((not x xor y) xor y) xor y ≡ false
    xor-lemma₂ true  false _ = ≡.refl
    xor-lemma₂ false true  _ = ≡.refl
    xor-lemma₂ true  true  ()
    xor-lemma₂ false false ()
    xor-lemma₃ : ∀ x y → x xor y ≡ false → ((y xor x) xor x) xor x ≡ false
    xor-lemma₃ true  true  _ = ≡.refl
    xor-lemma₃ false false _ = ≡.refl
    xor-lemma₃ true  false ()
    xor-lemma₃ false true  ()
    xor-lemma₄ : ∀ x y → x xor y ≡ false → ((not y xor y) xor y) xor not x ≡ false
    xor-lemma₄ true  true  _ = ≡.refl
    xor-lemma₄ false false _ = ≡.refl
    xor-lemma₄ true  false ()
    xor-lemma₄ false true  ()

    oddneg : ∀ x → oddℤ (ℤ.- x) ≡ oddℤ x
    oddneg = oddℤ-neg

    m-Sw : ∀ u → MonoWord p (Sw u)
    m-Sw true = a≤p , e≤p , e≤p
    m-Sw false = a≤p , h≤p , h≤p

    w-Sw : ∀ u → Within p (Sw u)
    w-Sw true = a≤p , e≤p , e≤p
    w-Sw false = a≤p , h≤p , h≤p

    -- Moving a level along an equation of matrices, checked by
    -- conversion of the matrices (comparing the levels instead would
    -- compute them).
    cast : ∀ (M M′ : Matrix n n D) → M ≡ M′ → level M <ₗ level s → level M′ <ₗ level s
    cast M M′ eq l = ≡.subst (λ M → level M <ₗ level s) eq l

    castLow : ∀ (w : Word (Gen n)) (M M′ : Matrix n n D) → M ≡ M′ → Low (level s) w M → Low (level s) w M′
    castLow w M M′ eq l = ≡.subst (Low (level s) w) eq l

    -- After T₂.
    l-T2 : level (actMʷ T2w σ₁) <ₗ level s
    l-T2 = cast σ₂ (actMʷ T2w σ₁) ≡.refl lσ₂

    first : ∀ u → Low (level s) (Sw u • T2w) σ₁
    first u = ((mono-word-below ⟪ mτ e (τ (T₁.Wh ! e)) ++ (mτ f (τ (T₁.Wh ! f)) ++ (mτ g (τ (T₁.Wh ! g)) ++ mτ h (τ (T₁.Wh ! h)))) ⟫ m₂ σ₁ lσ₁ lB ,
                mono-word-level ⟪ mτ e (τ (T₁.Wh ! e)) ++ (mτ f (τ (T₁.Wh ! f)) ++ (mτ g (τ (T₁.Wh ! g)) ++ mτ h (τ (T₁.Wh ! h)))) ⟫ m₂ σ₁ lσ₁ lB ,
                cast σ₂ (actM (K-gen e f g h e<f f<g g<h) (actMʷ ⟪ mτ e (τ (T₁.Wh ! e)) ++ (mτ f (τ (T₁.Wh ! f)) ++ (mτ g (τ (T₁.Wh ! g)) ++ mτ h (τ (T₁.Wh ! h)))) ⟫ σ₁)) ≡.refl lσ₂) ,
               mono-word-below (Sw u) (m-Sw u) (actMʷ T2w σ₁) l-T2 lB)

    l-S : ∀ u → level (actMʷ (Sw u • T2w) σ₁) <ₗ level s
    l-S u = cast (actMʷ (Sw u) (actMʷ T2w σ₁)) (actMʷ (Sw u • T2w) σ₁) ≡.refl (mono-word-level (Sw u) (m-Sw u) (actMʷ T2w σ₁) l-T2 lB)

    be-S : ∀ u → Beyond p (actMʷ (Sw u • T2w) σ₁)
    be-S u = Beyond-actMʷ (Sw u • T2w) (w-Sw u , within-T e<f f<g g<h (τ (T₁.Wh ! e)) (τ (T₁.Wh ! f)) (τ (T₁.Wh ! g)) (τ (T₁.Wh ! h)) e≤p f≤p g≤p h≤p) be₁

    col-S : ∀ u (V : Vec ℤ n) → actVʷ (Sw u) (scV K′ T₂.Wh) ≡ scV K′ V → col (actMʷ (Sw u • T2w) σ₁) p ≡ scV K′ V
    col-S u V h = ≡.trans (col-actMʷ (Sw u • T2w) σ₁ p)
                    (≡.trans (≡.cong (actVʷ (Sw u • T2w)) col₁) (≡.trans (≡.cong (actVʷ (Sw u)) (T₂.col-T K′)) h))

    result : ∀ u → level (actM (K-gen a b c d a<b b<c c<d) (actMʷ (Sw u • T2w) σ₁)) <ₗ level s ×
                   level (actM (K-gen e f g h e<f f<g g<h) (actM (K-gen a b c d a<b b<c c<d) (actMʷ (Sw u • T2w) σ₁))) <ₗ level s →
                   Result u
    result u (l₄ , l₅) = ((first u , l-S u , l₄′) , l₄′ , l₅′) , l₅″
      where
      M₃ = actMʷ (Sw u • T2w) σ₁
      M₄ = actM (K-gen a b c d a<b b<c c<d) M₃
      M₅ = actM (K-gen e f g h e<f f<g g<h) M₄
      l₄′ : level (actMʷ ([ K₁g ]ʷ • (Sw u • T2w)) σ₁) <ₗ level s
      l₄′ = cast M₄ (actMʷ ([ K₁g ]ʷ • (Sw u • T2w)) σ₁) ≡.refl l₄
      l₅′ : level (actM K₂g (actMʷ ([ K₁g ]ʷ • (Sw u • T2w)) σ₁)) <ₗ level s
      l₅′ = cast M₅ (actM K₂g (actMʷ ([ K₁g ]ʷ • (Sw u • T2w)) σ₁)) ≡.refl l₅
      l₅″ : level (actMʷ (Rest u) σ₁) <ₗ level s
      l₅″ = cast M₅ (actMʷ (Rest u) σ₁) ≡.refl l₅

  descent : ∀ u → useE ≡ u → Result u
  descent true hu = result true (tail U cnt oaU d<e e<f f<g g<h h≤p (actMʷ (Sw true • T2w) σ₁) SW.U′ (be-S true) (col-S true SW.U′ (SW.col-S K′)) sub₃
                    (ℤ.- T₂.hA) T₁.hB T₁.hC T₁.hD (ℤ.- T₁.hA) T₂.hB T₂.hC T₂.hD
                    U₃a (≡.trans (o3 (gt a<b) (ne< be′)) w₂b) (≡.trans (o3 (gt (a<b ⟨<⟩ b<c)) (ne< ce)) w₂c)
                    (≡.trans (o3 (gt (a<b ⟨<⟩ b<c ⟨<⟩ c<d)) (ne< d<e)) w₂d)
                    U₃e (≡.trans (o3 (gt (ae ⟨<⟩ e<f)) (gt e<f)) T₂.Wh-j)
                    (≡.trans (o3 (gt (ae ⟨<⟩ e<f ⟨<⟩ f<g)) (gt (e<f ⟨<⟩ f<g))) T₂.Wh-k)
                    (≡.trans (o3 (gt (ae ⟨<⟩ e<f ⟨<⟩ f<g ⟨<⟩ g<h)) (gt (e<f ⟨<⟩ f<g ⟨<⟩ g<h))) T₂.Wh-l)
                    Σ₁≡ Σ₂≡)
    where
    sw : XS.SwapR T₂.Wh a e (a<xS true)
    sw = XS.swap T₂.Wh (a<xS true)
    module SW = XS.SwapR sw
    U₃a : SW.U′ ! a ≡ + 2 ℤ.* (ℤ.- T₂.hA)
    U₃a = ≡.trans SW.U′-a (≡.trans (≡.cong ℤ.-_ T₂.Wh-i) (neg2 T₂.hA))
    U₃e : SW.U′ ! e ≡ + 2 ℤ.* (ℤ.- T₁.hA)
    U₃e = ≡.trans SW.U′-x (≡.trans (≡.cong ℤ.-_ w₂a) (neg2 T₁.hA))
    o3 : ∀ {z} → z ≢ a → z ≢ e → SW.U′ ! z ≡ T₂.Wh ! z
    o3 = SW.U′-o
    sub₃ : ∀ x → Odd (SW.U′ ! x) → Odd (U ! x)
    sub₃ x ox = sub₂ x (sub2 SW.U′ T₂.Wh o3 (ev2 _ U₃a) (ev2 _ U₃e) x ox)
    Σ₁≡ : ((oddℤ (ℤ.- T₂.hA) xor oddℤ T₁.hB) xor oddℤ T₁.hC) xor oddℤ T₁.hD ≡ false
    Σ₁≡ = ≡.trans (≡.cong (λ q → ((q xor oddℤ T₁.hB) xor oddℤ T₁.hC) xor oddℤ T₁.hD) (≡.trans (oddneg T₂.hA) T₂.par-A))
            (≡.trans (≡.cong₂ (λ q r → ((not T₂.Σz xor q) xor r) xor oddℤ T₁.hD) T₁.par-B T₁.par-C)
              (≡.trans (≡.cong (λ q → ((not T₂.Σz xor T₁.Σz) xor T₁.Σz) xor q) T₁.par-D)
                (xor-lemma₁ T₁.Σz T₂.Σz hu)))
    Σ₂≡ : ((oddℤ (ℤ.- T₁.hA) xor oddℤ T₂.hB) xor oddℤ T₂.hC) xor oddℤ T₂.hD ≡ false
    Σ₂≡ = ≡.trans (≡.cong (λ q → ((q xor oddℤ T₂.hB) xor oddℤ T₂.hC) xor oddℤ T₂.hD) (≡.trans (oddneg T₁.hA) T₁.par-A))
            (≡.trans (≡.cong₂ (λ q r → ((not T₁.Σz xor q) xor r) xor oddℤ T₂.hD) T₂.par-B T₂.par-C)
              (≡.trans (≡.cong (λ q → ((not T₁.Σz xor T₂.Σz) xor T₂.Σz) xor q) T₂.par-D)
                (xor-lemma₂ T₁.Σz T₂.Σz hu)))
  descent false hu = result false (tail U cnt oaU d<e e<f f<g g<h h≤p (actMʷ (Sw false • T2w) σ₁) SW.U′ (be-S false) (col-S false SW.U′ (SW.col-S K′)) sub₃
                    (ℤ.- T₂.hD) T₁.hB T₁.hC T₁.hD T₂.hA T₂.hB T₂.hC (ℤ.- T₁.hA)
                    U₃a (≡.trans (o3 (gt a<b) (ne< (be′ ⟨<⟩ e<f ⟨<⟩ f<g ⟨<⟩ g<h))) w₂b)
                    (≡.trans (o3 (gt (a<b ⟨<⟩ b<c)) (ne< (ce ⟨<⟩ e<f ⟨<⟩ f<g ⟨<⟩ g<h))) w₂c)
                    (≡.trans (o3 (gt (a<b ⟨<⟩ b<c ⟨<⟩ c<d)) (ne< (d<e ⟨<⟩ e<f ⟨<⟩ f<g ⟨<⟩ g<h))) w₂d)
                    (≡.trans (o3 (gt ae) (ne< (e<f ⟨<⟩ f<g ⟨<⟩ g<h))) T₂.Wh-i)
                    (≡.trans (o3 (gt (ae ⟨<⟩ e<f)) (ne< (f<g ⟨<⟩ g<h))) T₂.Wh-j)
                    (≡.trans (o3 (gt (ae ⟨<⟩ e<f ⟨<⟩ f<g)) (ne< g<h)) T₂.Wh-k)
                    U₃h Σ₁≡ Σ₂≡)
    where
    sw : XS.SwapR T₂.Wh a h (a<xS false)
    sw = XS.swap T₂.Wh (a<xS false)
    module SW = XS.SwapR sw
    U₃a : SW.U′ ! a ≡ + 2 ℤ.* (ℤ.- T₂.hD)
    U₃a = ≡.trans SW.U′-a (≡.trans (≡.cong ℤ.-_ T₂.Wh-l) (neg2 T₂.hD))
    U₃h : SW.U′ ! h ≡ + 2 ℤ.* (ℤ.- T₁.hA)
    U₃h = ≡.trans SW.U′-x (≡.trans (≡.cong ℤ.-_ w₂a) (neg2 T₁.hA))
    o3 : ∀ {z} → z ≢ a → z ≢ h → SW.U′ ! z ≡ T₂.Wh ! z
    o3 = SW.U′-o
    sub₃ : ∀ x → Odd (SW.U′ ! x) → Odd (U ! x)
    sub₃ x ox = sub₂ x (sub2 SW.U′ T₂.Wh o3 (ev2 _ U₃a) (ev2 _ U₃h) x ox)
    Σ₁≡ : ((oddℤ (ℤ.- T₂.hD) xor oddℤ T₁.hB) xor oddℤ T₁.hC) xor oddℤ T₁.hD ≡ false
    Σ₁≡ = ≡.trans (≡.cong (λ q → ((q xor oddℤ T₁.hB) xor oddℤ T₁.hC) xor oddℤ T₁.hD) (≡.trans (oddneg T₂.hD) T₂.par-D))
            (≡.trans (≡.cong₂ (λ q r → ((T₂.Σz xor q) xor r) xor oddℤ T₁.hD) T₁.par-B T₁.par-C)
              (≡.trans (≡.cong (λ q → ((T₂.Σz xor T₁.Σz) xor T₁.Σz) xor q) T₁.par-D)
                (xor-lemma₃ T₁.Σz T₂.Σz hu)))
    Σ₂≡ : ((oddℤ T₂.hA xor oddℤ T₂.hB) xor oddℤ T₂.hC) xor oddℤ (ℤ.- T₁.hA) ≡ false
    Σ₂≡ = ≡.trans (≡.cong₂ (λ q r → ((q xor r) xor oddℤ T₂.hC) xor oddℤ (ℤ.- T₁.hA)) T₂.par-A T₂.par-B)
            (≡.trans (≡.cong₂ (λ q r → ((not T₂.Σz xor T₂.Σz) xor q) xor r) T₂.par-C (≡.trans (oddneg T₁.hA) T₁.par-A))
              (xor-lemma₄ T₁.Σz T₂.Σz hu))

  ----------------------------------------------------------------------
  -- The path along the descent, and the square that closes it

  -- (Stated here, where the states have their own names: the types of a
  -- module application mention the definitions of this module applied
  -- to its arguments, and restating them otherwise makes Agda compare
  -- levels by computing them.)

  path-desc : ∀ u → useE ≡ u → Path (Rest u • T1w) σ oσ
  path-desc u hu = path-• (Rest u) T1w σ oσ
    (path-below ih (Rest u) (actMʷ T1w σ) (ColOrth-actMʷ T1w oσ)
      (castLow (Rest u) σ₁ (actMʷ T1w σ) ≡.refl (proj₁ (descent u hu)))) pT1

  -- A generator g of X's and (-1)'s, whose image has a path w₂ that
  -- closes the square.
  close : ∀ u → useE ≡ u → (g : Gen n) → Mono g → top g ≤ p → (w₂ : Word (Gen n)) →
          Path w₂ (actM g σ) (ColOrth-actMʷ [ g ]ʷ oσ) → ([ g ]ʷ • Rest u) • T1w ≈ w₂ • [ g ]ʷ → Path [ g ]ʷ σ oσ
  close u hu g mg tg w₂ p₂ rel = bridge g σ oσ T1w w₂ ([ g ]ʷ • Rest u) pT1 p₂ low rel
    where
    res = descent u hu
    l₃ : level (actMʷ (Rest u) (actMʷ T1w σ)) <ₗ level s
    l₃ = cast (actMʷ (Rest u) σ₁) (actMʷ (Rest u) (actMʷ T1w σ)) ≡.refl (proj₂ res)
    low : Low (level s) ([ g ]ʷ • Rest u) (actMʷ T1w σ)
    low = castLow (Rest u) σ₁ (actMʷ T1w σ) ≡.refl (proj₁ res) , l₃ , mono-level g mg tg (actMʷ (Rest u) (actMʷ T1w σ)) l₃ lB

------------------------------------------------------------------------
-- Two descents, from σ and from x·σ, closing a square

-- (The descents are named by the definitions of Descent applied to
-- their arguments, the form in which their types mention them.)

module _ (σ : Matrix n n D) .(oσ : ColOrth σ) (U : Vec ℤ n) (eqσ : col σ p ≡ scV K′ U)
  (beσ : Beyond p σ) (cnt : nodd U ≡ nodd W) {e f g h : Fin n}
  (fo₀ : firstOdd U ≡ just a) (na₀ : nextOdd a U ≡ just b) (nb₀ : nextOdd b U ≡ just c) (nc₀ : nextOdd c U ≡ just d)
  (nd₀ : nextOdd d U ≡ just e) (ne₀ : nextOdd e U ≡ just f) (nf₀ : nextOdd f U ≡ just g) (ng₀ : nextOdd g U ≡ just h)
  (h≤p : h ≤ p) (x : Gen n) (mx : Mono x) (tx : top x ≤ p)
  (U′ : Vec ℤ n) (eq′ : col (actM x σ) p ≡ scV K′ U′) (be′ : Beyond p (actM x σ)) (cnt′ : nodd U′ ≡ nodd W)
  (fo′ : firstOdd U′ ≡ just a) (na′ : nextOdd a U′ ≡ just b) (nb′ : nextOdd b U′ ≡ just c) (nc′ : nextOdd c U′ ≡ just d)
  (nd′ : nextOdd d U′ ≡ just e) (ne′ : nextOdd e U′ ≡ just f) (nf′ : nextOdd f U′ ≡ just g) (ng′ : nextOdd g U′ ≡ just h) where

  pair-close : ∀ u →
    Descent.useE σ oσ U eqσ beσ cnt fo₀ na₀ nb₀ nc₀ nd₀ ne₀ nf₀ ng₀ h≤p ≡ u →
    Descent.useE (actM x σ) (ColOrth-actMʷ [ x ]ʷ oσ) U′ eq′ be′ cnt′ fo′ na′ nb′ nc′ nd′ ne′ nf′ ng′ h≤p ≡ u →
    ([ x ]ʷ • Descent.Rest σ oσ U eqσ beσ cnt fo₀ na₀ nb₀ nc₀ nd₀ ne₀ nf₀ ng₀ h≤p u) •
      Descent.T1w σ oσ U eqσ beσ cnt fo₀ na₀ nb₀ nc₀ nd₀ ne₀ nf₀ ng₀ h≤p ≈
    (Descent.Rest (actM x σ) (ColOrth-actMʷ [ x ]ʷ oσ) U′ eq′ be′ cnt′ fo′ na′ nb′ nc′ nd′ ne′ nf′ ng′ h≤p u •
      Descent.T1w (actM x σ) (ColOrth-actMʷ [ x ]ʷ oσ) U′ eq′ be′ cnt′ fo′ na′ nb′ nc′ nd′ ne′ nf′ ng′ h≤p) • [ x ]ʷ →
    Path [ x ]ʷ σ oσ
  pair-close u hu hu′ rel =
    Descent.close σ oσ U eqσ beσ cnt fo₀ na₀ nb₀ nc₀ nd₀ ne₀ nf₀ ng₀ h≤p u hu x mx tx
      (Descent.Rest (actM x σ) (ColOrth-actMʷ [ x ]ʷ oσ) U′ eq′ be′ cnt′ fo′ na′ nb′ nc′ nd′ ne′ nf′ ng′ h≤p u •
       Descent.T1w (actM x σ) (ColOrth-actMʷ [ x ]ʷ oσ) U′ eq′ be′ cnt′ fo′ na′ nb′ nc′ nd′ ne′ nf′ ng′ h≤p)
      (Descent.path-desc (actM x σ) (ColOrth-actMʷ [ x ]ʷ oσ) U′ eq′ be′ cnt′ fo′ na′ nb′ nc′ nd′ ne′ nf′ ng′ h≤p u hu′) rel
