------------------------------------------------------------------------
-- Presentations of groups
--
-- The edges X_[x,x+1] at a level with a positive exponent (Lemma A.20,
-- Subcase 1.2).
--
-- X = X_[x,y], y = x + 1, swaps two entries of the pivot column W / 2ᴷ
-- and keeps its exponent.  With a < b < c < d the first four odd
-- entries and N = K_[a,b,c,d] (-1)_[a]^t the normal syllable:
--
-- * x, y not among a, b, c, d: the first four odd entries and their
--   values are unchanged, and X commutes with N (V = X);
-- * one of them is, and the other entry is even: the odd entry moves to
--   the neighbouring index, and X renames N by (3d)–(3g) (V = X);
-- * both are: the syllable is unchanged and V comes from RelX4;
-- * x = d and the entry y is odd: the edge eodd, given (QuadXE).
--
-- In all but the last the sign t is unchanged: the same four values
-- are odd, moved at most.
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

module Examples.Groups.CCX+HH-TwoLevel.QuadX {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p)
  {k′ : ℕ} (ks : lde (col s p) ≡ suc k′) (ih : R.EdgesBelow {n} (level s)) where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Fin.Properties as FinP
open import Data.Integer.Base using (ℤ)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (scV ; Minimal ; Odd ; Even ; odd? ; ¬Odd⇒Even)
open import Examples.Groups.CCX+HH-TwoLevel.Residue using (τ)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.ColumnAction using (Xᶻ ; actV-X)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (_!_ ; set₂-a ; set₂-b ; set₂-≢ ; <⇒≢ ; ColOrth-actMʷ)
open import Examples.Groups.CCX+HH-TwoLevel.Signs {n} using (Apart ; Mτ-comm ; Mτ-X ; Mτ-X′)
open import Examples.Groups.CCX+HH-TwoLevel.Derived {n} using (flip)
open import Examples.Groups.CCX+HH-TwoLevel.Engine using (prfᶠ ; emb⁼)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; emb ; [_]ᵢ ; _∷ᵢ_)
open import Examples.Groups.CCX+HH-TwoLevel.States {n} using (MonoWord)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable using (syl)
open R {n} using (Path)
import Examples.Groups.CCX+HH-TwoLevel.RelX4 as RX

open import Examples.Groups.CCX+HH-TwoLevel.QuadBase s o ps ks ih

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  ≡⇒≈ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  ≡⇒≈ ≡.refl = refl

  ne< : ∀ {u v : Fin n} → u < v → u ≢ v
  ne< lt e = ℕP.<-irrefl (≡.cong toℕ e) lt

  -- The square from a square for K and one for the sign.
  sq-N : ∀ {g : Gen n} {V Kw Kw′ Mt Mt′ : Word (Gen n)} → V • Kw ≈ Kw′ • [ g ]ʷ → [ g ]ʷ • Mt ≈ Mt′ • [ g ]ʷ →
         V • (Kw • Mt) ≈ (Kw′ • Mt′) • [ g ]ʷ
  sq-N {g} {V} {Kw} {Kw′} {Mt} {Mt′} hK hM = begin
    V • (Kw • Mt)          ≈⟨ sym assoc ⟩
    (V • Kw) • Mt          ≈⟨ cleft hK ⟩
    (Kw′ • [ g ]ʷ) • Mt    ≈⟨ assoc ⟩
    Kw′ • ([ g ]ʷ • Mt)    ≈⟨ cright hM ⟩
    Kw′ • (Mt′ • [ g ]ʷ)   ≈⟨ sym assoc ⟩
    (Kw′ • Mt′) • [ g ]ʷ   ∎

  -- A renaming in the other direction.
  back-ren : ∀ {g : Gen n} {A B : Word (Gen n)} → [ g ]ʷ • B ≈ A • [ g ]ʷ → [ g ]ʷ • A ≈ B • [ g ]ʷ
  back-ren {g} h = sym (flip g (sym h))

  e4 : Emb 4 n
  e4 = emb (a ∷ᵛ b ∷ᵛ c ∷ᵛ d ∷ᵛ []ᵛ) (a<b ∷ᵢ b<c ∷ᵢ c<d ∷ᵢ [ d ]ᵢ)

  oa : Odd (W ! a)
  oa = proj₁ (firstOdd-spec W fo)
  ob : Odd (W ! b)
  ob = proj₁ (proj₂ (nextOdd-spec W na))
  oc : Odd (W ! c)
  oc = proj₁ (proj₂ (nextOdd-spec W nb))
  od : Odd (W ! d)
  od = proj₁ (proj₂ (nextOdd-spec W nc))

------------------------------------------------------------------------
-- The edge

module EdgeX {x y : Fin n} .(xy : x < y) (adj : toℕ y ≡ suc (toℕ x)) (y≤p : y ≤ p) where

  gX : Gen n
  gX = X-gen x y xy

  Xw : Word (Gen n)
  Xw = [ gX ]ʷ

  W′ : Vec ℤ n
  W′ = Xᶻ x y W

  eqX : col (actM gX s) p ≡ scV K′ W′
  eqX = ≡.trans (colg gX) (actV-X x y xy K′ W)

  private
    x≢y : x ≢ y
    x≢y = <⇒≢ xy

    W′x : W′ ! x ≡ W ! y
    W′x = set₂-a x y (W ! y) (W ! x) W

    W′y : W′ ! y ≡ W ! x
    W′y = set₂-b x y (W ! y) (W ! x) W x≢y

    W′o : ∀ {z} → z ≢ x → z ≢ y → W′ ! z ≡ W ! z
    W′o zx zy = set₂-≢ x y (W ! y) (W ! x) W zx zy

    -- Nothing lies strictly between x and y.
    between : ∀ {z : Fin n} → x < z → z < y → ⊥
    between {z} xz zy = ℕP.<-irrefl ≡.refl (ℕP.<-≤-trans zy (≡.subst (ℕ._≤ toℕ z) (≡.sym adj) xz))

    -- An entry of W′ is that of W, or swapped.
    W′-par : ∀ z {P : ℤ → Set} → (z ≢ x → z ≢ y → P (W ! z)) → (z ≡ x → P (W ! y)) → (z ≡ y → P (W ! x)) →
             P (W′ ! z)
    W′-par z {P} hz hx hy = by (z FinP.≟ x) (z FinP.≟ y)
      where
      by : Dec (z ≡ x) → Dec (z ≡ y) → P (W′ ! z)
      by (yes ≡.refl) _ = ≡.subst P (≡.sym W′x) (hx ≡.refl)
      by (no zx) (yes ≡.refl) = ≡.subst P (≡.sym W′y) (hy ≡.refl)
      by (no zx) (no zy) = ≡.subst P (≡.sym (W′o zx zy)) (hz zx zy)

  ----------------------------------------------------------------------
  -- After X, from the first four odd entries a′ < b′ < c′ < d′ of W′

  module After′ {a′ b′ c′ d′ : Fin n} (ab′ : a′ < b′) (bc′ : b′ < c′) (cd′ : c′ < d′)
    (oa′ : Odd (W′ ! a′)) (ob′ : Odd (W′ ! b′)) (oc′ : Odd (W′ ! c′)) (od′ : Odd (W′ ! d′))
    (ev′ : ∀ z → z < d′ → z ≢ a′ → z ≢ b′ → z ≢ c′ → Even (W′ ! z)) where

    private
      fo′ : firstOdd W′ ≡ just a′
      fo′ = firstOdd-char W′ oa′ (λ z z<a → ev′ z (FinP.<-trans z<a (FinP.<-trans ab′ (FinP.<-trans bc′ cd′)))
              (ne< z<a) (ne< (FinP.<-trans z<a ab′)) (ne< (FinP.<-trans z<a (FinP.<-trans ab′ bc′))))
      na′ : nextOdd a′ W′ ≡ just b′
      na′ = nextOdd-char W′ ab′ ob′ (λ z a<z z<b → ev′ z (FinP.<-trans z<b (FinP.<-trans bc′ cd′))
              (λ e → ne< a<z (≡.sym e)) (ne< z<b) (ne< (FinP.<-trans z<b bc′)))
      nb′ : nextOdd b′ W′ ≡ just c′
      nb′ = nextOdd-char W′ bc′ oc′ (λ z b<z z<c → ev′ z (FinP.<-trans z<c cd′)
              (λ e → ne< (FinP.<-trans ab′ b<z) (≡.sym e)) (λ e → ne< b<z (≡.sym e)) (ne< z<c))
      nc′ : nextOdd c′ W′ ≡ just d′
      nc′ = nextOdd-char W′ cd′ od′ (λ z c<z z<d → ev′ z z<d
              (λ e → ne< (FinP.<-trans (FinP.<-trans ab′ bc′) c<z) (≡.sym e))
              (λ e → ne< (FinP.<-trans bc′ c<z) (≡.sym e)) (λ e → ne< c<z (≡.sym e)))
      mn′ : Minimal K′ W′
      mn′ = inj₂ (a′ , oa′)

    N′≡ : sylData p K′ W′ ≡ K a′ b′ c′ d′ ab′ bc′ cd′ • Mτ a′ (σ₄ W′ a′ b′ c′ d′)
    N′≡ = sylData-quad {p = p} k′ W′ fo′ na′ nb′ nc′ ab′ bc′ cd′

    pN′ : Path (sylData p K′ W′) (actM gX s) (ColOrth-actMʷ Xw o)
    pN′ = path-g gX y≤p W′ eqX mn′

    -- The square, with t unchanged.
    close : (V : Word (Gen n)) → MonoWord p V → σ₄ W′ a′ b′ c′ d′ ≡ t →
            V • (K a b c d a<b b<c c<d • Mτ a t) ≈ (K a′ b′ c′ d′ ab′ bc′ cd′ • Mτ a′ t) • Xw → Path Xw s o
    close V mV t′ rel = square gX (sylData p K′ W′) V pN′ mV (begin
      V • syl s                                                     ≈⟨ cright ≡⇒≈ N≡ ⟩
      V • (K a b c d a<b b<c c<d • Mτ a t)                          ≈⟨ rel ⟩
      (K a′ b′ c′ d′ ab′ bc′ cd′ • Mτ a′ t) • Xw                    ≈⟨ cleft ≡⇒≈ (≡.sym (≡.trans N′≡ (≡.cong (λ q → K a′ b′ c′ d′ ab′ bc′ cd′ • Mτ a′ q) t′))) ⟩
      sylData p K′ W′ • Xw                                          ∎)

  ----------------------------------------------------------------------
  -- x and y apart from a, b, c, d

  disjoint : x ≢ a → x ≢ b → x ≢ c → x ≢ d → y ≢ a → y ≢ b → y ≢ c → y ≢ d → Path Xw s o
  disjoint xa xb xc xd ya yb yc yd = close Xw y≤p t′ rel
    where
    -- x < d iff y < d; then both are even.
    evx : x < d → Even (W ! x)
    evx x<d = ev x x<d xa xb xc
    evy : y < d → Even (W ! y)
    evy y<d = ev y y<d ya yb yc
    ev′ : ∀ z → z < d → z ≢ a → z ≢ b → z ≢ c → Even (W′ ! z)
    ev′ z z<d za zb zc = W′-par z {λ w → Even w} (λ _ _ → ev z z<d za zb zc)
      (λ { ≡.refl → evy (by-y z<d) }) (λ { ≡.refl → evx (FinP.<-trans xy′ z<d) })
      where
      xy′ : x < y
      xy′ = ≡.subst (toℕ x ℕ.<_) (≡.sym adj) (ℕP.n<1+n (toℕ x))
      -- x < d gives y ≤ d, and y ≢ d.
      by-y : x < d → y < d
      by-y x<d = ℕP.≤∧≢⇒< (≡.subst (ℕ._≤ toℕ d) (≡.sym adj) x<d) (λ e → yd (FinP.toℕ-injective e))
    open After′ a<b b<c c<d (≡.trans (≡.cong oddℤ (W′o (λ e → xa (≡.sym e)) (λ e → ya (≡.sym e)))) oa)
                            (≡.trans (≡.cong oddℤ (W′o (λ e → xb (≡.sym e)) (λ e → yb (≡.sym e)))) ob)
                            (≡.trans (≡.cong oddℤ (W′o (λ e → xc (≡.sym e)) (λ e → yc (≡.sym e)))) oc)
                            (≡.trans (≡.cong oddℤ (W′o (λ e → xd (≡.sym e)) (λ e → yd (≡.sym e)))) od) ev′
    t′ : σ₄ W′ a b c d ≡ t
    t′ = ≡.trans (≡.cong₂ (λ u v → ((τ u xor τ v) xor τ (W′ ! c)) xor τ (W′ ! d))
                   (W′o (λ e → xa (≡.sym e)) (λ e → ya (≡.sym e))) (W′o (λ e → xb (≡.sym e)) (λ e → yb (≡.sym e))))
                 (≡.cong₂ (λ u v → ((τ (W ! a) xor τ (W ! b)) xor τ u) xor τ v)
                   (W′o (λ e → xc (≡.sym e)) (λ e → yc (≡.sym e))) (W′o (λ e → xd (≡.sym e)) (λ e → yd (≡.sym e))))
    rel : Xw • (K a b c d a<b b<c c<d • Mτ a t) ≈ (K a b c d a<b b<c c<d • Mτ a t) • Xw
    rel = sq-N (axiom (r2c xy a<b b<c c<d (λ e → xa e) (λ e → xb e) (λ e → xc e) (λ e → xd e)
                                          (λ e → ya e) (λ e → yb e) (λ e → yc e) (λ e → yd e)))
               (sym (Mτ-comm a t gX ((λ e → xa (≡.sym e)) , (λ e → ya (≡.sym e)))))

  ----------------------------------------------------------------------
  -- One of x, y among a, b, c, d, the other entry even: renaming

  private
    xy′ : x < y
    xy′ = ≡.subst (toℕ x ℕ.<_) (≡.sym adj) (ℕP.n<1+n (toℕ x))

    -- y follows x: x < z gives y ≤ z.
    after : ∀ {z : Fin n} → x < z → y ≤ z
    after xz = ≡.subst (ℕ._≤ _) (≡.sym adj) xz

    -- z < y gives z ≤ x.
    before : ∀ {z : Fin n} → z < y → z ≤ x
    before zy = ℕP.≤-pred (≡.subst (_ ℕ.<_) adj zy)

    lt≢ : ∀ {u v : Fin n} → u < v → v ≢ u
    lt≢ lt e = ne< lt (≡.sym e)

    -- The signs and K's of the syllable, entry by entry.
    odd′ : ∀ {z} → z ≢ x → z ≢ y → Odd (W ! z) → Odd (W′ ! z)
    odd′ zx zy o = ≡.trans (≡.cong oddℤ (W′o zx zy)) o

    τ′ : ∀ {z} → z ≢ x → z ≢ y → τ (W′ ! z) ≡ τ (W ! z)
    τ′ zx zy = ≡.cong τ (W′o zx zy)

  -- x = a, y even: the odd entry a moves to y.
  up-a : x ≡ a → Even (W ! y) → y ≢ b → Path Xw s o
  up-a ≡.refl ey yb = close Xw y≤p t′ (sq-N (axiom (r3d xy yb′ b<c c<d a<b)) (Mτ-X′ xy t))
    where
    yb′ : y < b
    yb′ = ℕP.≤∧≢⇒< (after a<b) (λ e → yb (FinP.toℕ-injective e))
    ev′ : ∀ z → z < d → z ≢ y → z ≢ b → z ≢ c → Even (W′ ! z)
    ev′ z z<d zy zb zc = W′-par z {λ w → Even w} (λ zx _ → ev z z<d zx zb zc) (λ _ → ey) (λ e → ⊥-elim (zy e))
    open After′ yb′ b<c c<d (≡.trans (≡.cong oddℤ W′y) oa)
      (odd′ (lt≢ a<b) (lt≢ yb′) ob) (odd′ (lt≢ (FinP.<-trans a<b b<c)) (lt≢ (FinP.<-trans yb′ b<c)) oc)
      (odd′ (lt≢ (FinP.<-trans a<b (FinP.<-trans b<c c<d))) (lt≢ (FinP.<-trans yb′ (FinP.<-trans b<c c<d))) od) ev′
    t′ : σ₄ W′ y b c d ≡ t
    t′ = ≡.trans (≡.cong₂ (λ u v → ((τ u xor v) xor τ (W′ ! c)) xor τ (W′ ! d)) W′y (τ′ (lt≢ a<b) (lt≢ yb′)))
           (≡.cong₂ (λ u v → ((τ (W ! a) xor τ (W ! b)) xor u) xor v)
             (τ′ (lt≢ (FinP.<-trans a<b b<c)) (lt≢ (FinP.<-trans yb′ b<c)))
             (τ′ (lt≢ (FinP.<-trans a<b (FinP.<-trans b<c c<d))) (lt≢ (FinP.<-trans yb′ (FinP.<-trans b<c c<d)))))

  -- x = b, y even.
  up-b : x ≡ b → Even (W ! y) → y ≢ c → Path Xw s o
  up-b ≡.refl ey yc = close Xw y≤p t′
    (sq-N (axiom (r3e a<b xy yc′ c<d b<c (FinP.<-trans a<b xy′))) (sym (Mτ-comm a t gX (ne< a<b , ne< (FinP.<-trans a<b xy′)))))
    where
    yc′ : y < c
    yc′ = ℕP.≤∧≢⇒< (after b<c) (λ e → yc (FinP.toℕ-injective e))
    ay : a < y
    ay = FinP.<-trans a<b xy′
    ev′ : ∀ z → z < d → z ≢ a → z ≢ y → z ≢ c → Even (W′ ! z)
    ev′ z z<d za zy zc = W′-par z {λ w → Even w} (λ zx _ → ev z z<d za zx zc) (λ _ → ey) (λ e → ⊥-elim (zy e))
    open After′ ay yc′ c<d (odd′ (ne< a<b) (ne< ay) oa) (≡.trans (≡.cong oddℤ W′y) ob)
      (odd′ (lt≢ b<c) (lt≢ yc′) oc) (odd′ (lt≢ (FinP.<-trans b<c c<d)) (lt≢ (FinP.<-trans yc′ c<d)) od) ev′
    t′ : σ₄ W′ a y c d ≡ t
    t′ = ≡.trans (≡.cong₂ (λ u v → ((u xor τ v) xor τ (W′ ! c)) xor τ (W′ ! d)) (τ′ (ne< a<b) (ne< ay)) W′y)
           (≡.cong₂ (λ u v → ((τ (W ! a) xor τ (W ! b)) xor u) xor v)
             (τ′ (lt≢ b<c) (lt≢ yc′)) (τ′ (lt≢ (FinP.<-trans b<c c<d)) (lt≢ (FinP.<-trans yc′ c<d))))

  -- x = c, y even.
  up-c : x ≡ c → Even (W ! y) → y ≢ d → Path Xw s o
  up-c ≡.refl ey yd = close Xw y≤p t′
    (sq-N (axiom (r3f a<b b<c xy yd′ c<d (FinP.<-trans b<c xy′)))
          (sym (Mτ-comm a t gX (ne< (FinP.<-trans a<b b<c) , ne< (FinP.<-trans (FinP.<-trans a<b b<c) xy′)))))
    where
    yd′ : y < d
    yd′ = ℕP.≤∧≢⇒< (after c<d) (λ e → yd (FinP.toℕ-injective e))
    by : b < y
    by = FinP.<-trans b<c xy′
    ev′ : ∀ z → z < d → z ≢ a → z ≢ b → z ≢ y → Even (W′ ! z)
    ev′ z z<d za zb zy = W′-par z {λ w → Even w} (λ zx _ → ev z z<d za zb zx) (λ _ → ey) (λ e → ⊥-elim (zy e))
    open After′ a<b by yd′ (odd′ (ne< (FinP.<-trans a<b b<c)) (ne< (FinP.<-trans a<b by)) oa)
      (odd′ (ne< b<c) (ne< by) ob) (≡.trans (≡.cong oddℤ W′y) oc) (odd′ (lt≢ c<d) (lt≢ yd′) od) ev′
    t′ : σ₄ W′ a b y d ≡ t
    t′ = ≡.trans (≡.cong₂ (λ u v → ((u xor v) xor τ (W′ ! y)) xor τ (W′ ! d))
                   (τ′ (ne< (FinP.<-trans a<b b<c)) (ne< (FinP.<-trans a<b by))) (τ′ (ne< b<c) (ne< by)))
           (≡.cong₂ (λ u v → ((τ (W ! a) xor τ (W ! b)) xor τ u) xor v) W′y (τ′ (lt≢ c<d) (lt≢ yd′)))

  -- x = d, y even.
  up-d : x ≡ d → Even (W ! y) → Path Xw s o
  up-d ≡.refl ey = close Xw y≤p t′
    (sq-N (axiom (r3g a<b b<c c<d xy (FinP.<-trans c<d xy′)))
          (sym (Mτ-comm a t gX (ne< (FinP.<-trans a<b (FinP.<-trans b<c c<d)) ,
                                ne< (FinP.<-trans (FinP.<-trans a<b (FinP.<-trans b<c c<d)) xy′)))))
    where
    cy : c < y
    cy = FinP.<-trans c<d xy′
    ev′ : ∀ z → z < y → z ≢ a → z ≢ b → z ≢ c → Even (W′ ! z)
    ev′ z z<y za zb zc = W′-par z {λ w → Even w}
      (λ zx zy → ev z (ℕP.≤∧≢⇒< (before z<y) (λ e → zx (FinP.toℕ-injective e))) za zb zc)
      (λ _ → ey) (λ e → ⊥-elim (ne< z<y e))
    da = FinP.<-trans a<b (FinP.<-trans b<c c<d)
    db = FinP.<-trans b<c c<d
    open After′ a<b b<c cy (odd′ (ne< da) (ne< (FinP.<-trans da xy′)) oa)
      (odd′ (ne< db) (ne< (FinP.<-trans db xy′)) ob) (odd′ (ne< c<d) (ne< cy) oc) (≡.trans (≡.cong oddℤ W′y) od) ev′
    t′ : σ₄ W′ a b c y ≡ t
    t′ = ≡.trans (≡.cong₂ (λ u v → ((u xor v) xor τ (W′ ! c)) xor τ (W′ ! y))
                   (τ′ (ne< da) (ne< (FinP.<-trans da xy′))) (τ′ (ne< db) (ne< (FinP.<-trans db xy′))))
           (≡.cong₂ (λ u v → ((τ (W ! a) xor τ (W ! b)) xor u) xor τ v) (τ′ (ne< c<d) (ne< cy)) W′y)

  -- y = a, x even: the odd entry a moves to x.
  down-a : y ≡ a → Even (W ! x) → Path Xw s o
  down-a ≡.refl ex = close Xw y≤p t′ (sq-N (back-ren (axiom (r3d xy a<b b<c c<d (FinP.<-trans xy a<b)))) (Mτ-X xy t))
    where
    xb = FinP.<-trans xy′ a<b
    ev′ : ∀ z → z < d → z ≢ x → z ≢ b → z ≢ c → Even (W′ ! z)
    ev′ z z<d zx zb zc = W′-par z {λ w → Even w} (λ _ zy → ev z z<d zy zb zc) (λ e → ⊥-elim (zx e)) (λ _ → ex)
    open After′ xb b<c c<d (≡.trans (≡.cong oddℤ W′x) oa)
      (odd′ (lt≢ xb) (lt≢ a<b) ob) (odd′ (lt≢ (FinP.<-trans xb b<c)) (lt≢ (FinP.<-trans a<b b<c)) oc)
      (odd′ (lt≢ (FinP.<-trans xb (FinP.<-trans b<c c<d))) (lt≢ (FinP.<-trans a<b (FinP.<-trans b<c c<d))) od) ev′
    t′ : σ₄ W′ x b c d ≡ t
    t′ = ≡.trans (≡.cong₂ (λ u v → ((τ u xor v) xor τ (W′ ! c)) xor τ (W′ ! d)) W′x (τ′ (lt≢ xb) (lt≢ a<b)))
           (≡.cong₂ (λ u v → ((τ (W ! a) xor τ (W ! b)) xor u) xor v)
             (τ′ (lt≢ (FinP.<-trans xb b<c)) (lt≢ (FinP.<-trans a<b b<c)))
             (τ′ (lt≢ (FinP.<-trans xb (FinP.<-trans b<c c<d))) (lt≢ (FinP.<-trans a<b (FinP.<-trans b<c c<d)))))

  -- y = b, x even (x ≠ a).
  down-b : y ≡ b → Even (W ! x) → x ≢ a → Path Xw s o
  down-b ≡.refl ex xa = close Xw y≤p t′
    (sq-N (back-ren (axiom (r3e ax xy b<c c<d (FinP.<-trans xy b<c) a<b)))
          (sym (Mτ-comm a t gX ((λ e → xa (≡.sym e)) , ne< a<b))))
    where
    ax : a < x
    ax = ℕP.≤∧≢⇒< (before a<b) (λ e → xa (FinP.toℕ-injective (≡.sym e)))
    xc = FinP.<-trans xy′ b<c
    ev′ : ∀ z → z < d → z ≢ a → z ≢ x → z ≢ c → Even (W′ ! z)
    ev′ z z<d za zx zc = W′-par z {λ w → Even w} (λ _ zy → ev z z<d za zy zc) (λ e → ⊥-elim (zx e)) (λ _ → ex)
    open After′ ax xc c<d (odd′ (ne< ax) (ne< a<b) oa) (≡.trans (≡.cong oddℤ W′x) ob)
      (odd′ (lt≢ xc) (lt≢ b<c) oc) (odd′ (lt≢ (FinP.<-trans xc c<d)) (lt≢ (FinP.<-trans b<c c<d)) od) ev′
    t′ : σ₄ W′ a x c d ≡ t
    t′ = ≡.trans (≡.cong₂ (λ u v → ((u xor τ v) xor τ (W′ ! c)) xor τ (W′ ! d)) (τ′ (ne< ax) (ne< a<b)) W′x)
           (≡.cong₂ (λ u v → ((τ (W ! a) xor τ (W ! b)) xor u) xor v)
             (τ′ (lt≢ xc) (lt≢ b<c)) (τ′ (lt≢ (FinP.<-trans xc c<d)) (lt≢ (FinP.<-trans b<c c<d))))

  -- y = c, x even (x ≠ b).
  down-c : y ≡ c → Even (W ! x) → x ≢ b → Path Xw s o
  down-c ≡.refl ex xb = close Xw y≤p t′
    (sq-N (back-ren (axiom (r3f a<b bx xy c<d (FinP.<-trans xy c<d) b<c)))
          (sym (Mτ-comm a t gX (ne< ax , ne< (FinP.<-trans a<b b<c)))))
    where
    bx : b < x
    bx = ℕP.≤∧≢⇒< (before b<c) (λ e → xb (FinP.toℕ-injective (≡.sym e)))
    ax = FinP.<-trans a<b bx
    xd = FinP.<-trans xy′ c<d
    ev′ : ∀ z → z < d → z ≢ a → z ≢ b → z ≢ x → Even (W′ ! z)
    ev′ z z<d za zb zx = W′-par z {λ w → Even w} (λ _ zy → ev z z<d za zb zy) (λ e → ⊥-elim (zx e)) (λ _ → ex)
    open After′ a<b bx xd (odd′ (ne< ax) (ne< (FinP.<-trans a<b b<c)) oa) (odd′ (ne< bx) (ne< b<c) ob)
      (≡.trans (≡.cong oddℤ W′x) oc) (odd′ (lt≢ xd) (lt≢ c<d) od) ev′
    t′ : σ₄ W′ a b x d ≡ t
    t′ = ≡.trans (≡.cong₂ (λ u v → ((u xor v) xor τ (W′ ! x)) xor τ (W′ ! d))
                   (τ′ (ne< ax) (ne< (FinP.<-trans a<b b<c))) (τ′ (ne< bx) (ne< b<c)))
           (≡.cong₂ (λ u v → ((τ (W ! a) xor τ (W ! b)) xor τ u) xor v) W′x (τ′ (lt≢ xd) (lt≢ c<d)))

  -- y = d, x even (x ≠ c).
  down-d : y ≡ d → Even (W ! x) → x ≢ c → Path Xw s o
  down-d ≡.refl ex xc = close Xw y≤p t′
    (sq-N (back-ren (axiom (r3g a<b b<c cx xy c<d)))
          (sym (Mτ-comm a t gX (ne< ax , ne< (FinP.<-trans a<b (FinP.<-trans b<c c<d))))))
    where
    cx : c < x
    cx = ℕP.≤∧≢⇒< (before c<d) (λ e → xc (FinP.toℕ-injective (≡.sym e)))
    bx = FinP.<-trans b<c cx
    ax = FinP.<-trans a<b bx
    ev′ : ∀ z → z < x → z ≢ a → z ≢ b → z ≢ c → Even (W′ ! z)
    ev′ z z<x za zb zc = W′-par z {λ w → Even w} (λ _ zy → ev z (FinP.<-trans z<x xy′) za zb zc)
      (λ e → ⊥-elim (ne< z<x e)) (λ e → ⊥-elim (ne< (FinP.<-trans z<x xy′) e))
    open After′ a<b b<c cx (odd′ (ne< ax) (ne< (FinP.<-trans ax xy′)) oa) (odd′ (ne< bx) (ne< (FinP.<-trans bx xy′)) ob)
      (odd′ (ne< cx) (ne< c<d) oc) (≡.trans (≡.cong oddℤ W′x) od) ev′
    t′ : σ₄ W′ a b c x ≡ t
    t′ = ≡.trans (≡.cong₂ (λ u v → ((u xor v) xor τ (W′ ! c)) xor τ (W′ ! x))
                   (τ′ (ne< ax) (ne< (FinP.<-trans ax xy′))) (τ′ (ne< bx) (ne< (FinP.<-trans bx xy′))))
           (≡.cong₂ (λ u v → ((τ (W ! a) xor τ (W ! b)) xor τ u) xor τ v) (W′o (ne< cx) (ne< c<d)) W′x)

  ----------------------------------------------------------------------
  -- x and y both among a, b, c, d

  private
    swap₁₂ : ∀ p q r v → ((p xor q) xor r) xor v ≡ ((q xor p) xor r) xor v
    swap₁₂ p q r v = ≡.cong (λ u → (u xor r) xor v) (BoolP.xor-comm p q)
    swap₂₃ : ∀ p q r v → ((p xor r) xor q) xor v ≡ ((p xor q) xor r) xor v
    swap₂₃ p q r v = ≡.cong (_xor v) (≡.trans (BoolP.xor-assoc p r q)
                       (≡.trans (≡.cong (p xor_) (BoolP.xor-comm r q)) (≡.sym (BoolP.xor-assoc p q r))))
    swap₃₄ : ∀ p q r v → ((p xor q) xor v) xor r ≡ ((p xor q) xor r) xor v
    swap₃₄ p q r v = ≡.trans (BoolP.xor-assoc (p xor q) v r)
                       (≡.trans (≡.cong ((p xor q) xor_) (BoolP.xor-comm v r)) (≡.sym (BoolP.xor-assoc (p xor q) r v)))

  -- x = a, y = b.
  both-ab : x ≡ a → y ≡ b → Path Xw s o
  both-ab ≡.refl ≡.refl = by t ≡.refl
    where
    ev′ : ∀ z → z < d → z ≢ x → z ≢ y → z ≢ c → Even (W′ ! z)
    ev′ z z<d zx zy zc = W′-par z {λ w → Even w} (λ _ _ → ev z z<d zx zy zc) (λ e → ⊥-elim (zx e)) (λ e → ⊥-elim (zy e))
    open After′ a<b b<c c<d (≡.trans (≡.cong oddℤ W′x) ob) (≡.trans (≡.cong oddℤ W′y) oa)
      (odd′ (lt≢ (FinP.<-trans a<b b<c)) (lt≢ b<c) oc) (odd′ (lt≢ (FinP.<-trans a<b (FinP.<-trans b<c c<d))) (lt≢ (FinP.<-trans b<c c<d)) od) ev′
    t′ : σ₄ W′ a b c d ≡ t
    t′ = ≡.trans (≡.cong₂ (λ u v → ((τ u xor τ v) xor τ (W′ ! c)) xor τ (W′ ! d)) W′x W′y)
           (≡.trans (≡.cong₂ (λ u v → ((τ (W ! y) xor τ (W ! x)) xor τ u) xor τ v)
                       (W′o (lt≢ (FinP.<-trans a<b b<c)) (lt≢ b<c)) (W′o (lt≢ (FinP.<-trans a<b (FinP.<-trans b<c c<d))) (lt≢ (FinP.<-trans b<c c<d))))
             (swap₁₂ (τ (W ! y)) (τ (W ! x)) (τ (W ! c)) (τ (W ! d))))
    Kw = K a b c d a<b b<c c<d
    by : ∀ tv → t ≡ tv → Path Xw s o
    by false ht = close (M d • (M b • X b d (FinP.<-trans b<c c<d))) (d≤p , ℕP.≤-trans (ℕP.<⇒≤ (FinP.<-trans b<c c<d)) d≤p , d≤p) t′
      (begin
        (M d • (M b • X b d _)) • (Kw • Mτ a t)    ≈⟨ cright cright ≡⇒≈ (≡.cong (Mτ a) ht) ⟩
        (M d • (M b • X b d _)) • (Kw • ε)         ≈⟨ cright right-unit ⟩
        (M d • (M b • X b d _)) • Kw               ≈⟨ assoc ⟩
        M d • ((M b • X b d _) • Kw)               ≈⟨ cright assoc ⟩
        M d • (M b • (X b d _ • Kw))               ≈⟨ prfᶠ (emb⁼ e4 RX.sq-01-f) ⟩
        Kw • Xw                                    ≈⟨ cleft sym right-unit ⟩
        (Kw • ε) • Xw                              ≈⟨ cleft cright ≡⇒≈ (≡.cong (Mτ a) (≡.sym ht)) ⟩
        (Kw • Mτ a t) • Xw                         ∎)
    by true ht = close (M a • (M c • X a c (FinP.<-trans a<b b<c)))
      (ℕP.≤-trans (ℕP.<⇒≤ (FinP.<-trans a<b (FinP.<-trans b<c c<d))) d≤p , ℕP.≤-trans (ℕP.<⇒≤ c<d) d≤p , ℕP.≤-trans (ℕP.<⇒≤ c<d) d≤p) t′
      (begin
        (M a • (M c • X a c _)) • (Kw • Mτ a t)    ≈⟨ cright cright ≡⇒≈ (≡.cong (Mτ a) ht) ⟩
        (M a • (M c • X a c _)) • (Kw • M a)       ≈⟨ assoc ⟩
        M a • ((M c • X a c _) • (Kw • M a))       ≈⟨ cright assoc ⟩
        M a • (M c • (X a c _ • (Kw • M a)))       ≈⟨ prfᶠ (emb⁼ e4 RX.sq-01-t) ⟩
        Kw • (M a • Xw)                            ≈⟨ sym assoc ⟩
        (Kw • M a) • Xw                            ≈⟨ cleft cright ≡⇒≈ (≡.cong (Mτ a) (≡.sym ht)) ⟩
        (Kw • Mτ a t) • Xw                         ∎)

  -- x = b, y = c.
  both-bc : x ≡ b → y ≡ c → Path Xw s o
  both-bc ≡.refl ≡.refl = close Xw y≤p t′ (sq-N (prfᶠ (emb⁼ e4 RX.sq-12)) (sym (Mτ-comm a t gX (ne< a<b , ne< (FinP.<-trans a<b b<c)))))
    where
    ev′ : ∀ z → z < d → z ≢ a → z ≢ x → z ≢ y → Even (W′ ! z)
    ev′ z z<d za zx zy = W′-par z {λ w → Even w} (λ _ _ → ev z z<d za zx zy) (λ e → ⊥-elim (zx e)) (λ e → ⊥-elim (zy e))
    open After′ a<b b<c c<d (odd′ (ne< a<b) (ne< (FinP.<-trans a<b b<c)) oa)
      (≡.trans (≡.cong oddℤ W′x) oc) (≡.trans (≡.cong oddℤ W′y) ob) (odd′ (lt≢ (FinP.<-trans b<c c<d)) (lt≢ c<d) od) ev′
    t′ : σ₄ W′ a b c d ≡ t
    t′ = ≡.trans (≡.cong₂ (λ u v → ((u xor τ v) xor τ (W′ ! c)) xor τ (W′ ! d)) (τ′ (ne< a<b) (ne< (FinP.<-trans a<b b<c))) W′x)
           (≡.trans (≡.cong₂ (λ u v → ((τ (W ! a) xor τ (W ! c)) xor τ u) xor v) W′y (τ′ (lt≢ (FinP.<-trans b<c c<d)) (lt≢ c<d)))
             (swap₂₃ (τ (W ! a)) (τ (W ! b)) (τ (W ! c)) (τ (W ! d))))

  -- x = c, y = d.
  both-cd : x ≡ c → y ≡ d → Path Xw s o
  both-cd ≡.refl ≡.refl = close (X b d (FinP.<-trans b<c c<d)) d≤p t′
    (sq-N (prfᶠ (emb⁼ e4 RX.sq-23)) (sym (Mτ-comm a t gX (ne< (FinP.<-trans a<b b<c) , ne< (FinP.<-trans a<b (FinP.<-trans b<c c<d))))))
    where
    ev′ : ∀ z → z < d → z ≢ a → z ≢ b → z ≢ x → Even (W′ ! z)
    ev′ z z<d za zb zx = W′-par z {λ w → Even w} (λ _ _ → ev z z<d za zb zx) (λ e → ⊥-elim (zx e)) (λ e → ⊥-elim (ne< z<d e))
    open After′ a<b b<c c<d (odd′ (ne< (FinP.<-trans a<b b<c)) (ne< (FinP.<-trans a<b (FinP.<-trans b<c c<d))) oa)
      (odd′ (ne< b<c) (ne< (FinP.<-trans b<c c<d)) ob) (≡.trans (≡.cong oddℤ W′x) od) (≡.trans (≡.cong oddℤ W′y) oc) ev′
    t′ : σ₄ W′ a b c d ≡ t
    t′ = ≡.trans (≡.cong₂ (λ u v → ((u xor v) xor τ (W′ ! c)) xor τ (W′ ! d))
                   (τ′ (ne< (FinP.<-trans a<b b<c)) (ne< (FinP.<-trans a<b (FinP.<-trans b<c c<d)))) (τ′ (ne< b<c) (ne< (FinP.<-trans b<c c<d))))
           (≡.trans (≡.cong₂ (λ u v → ((τ (W ! a) xor τ (W ! b)) xor τ u) xor τ v) W′x W′y)
             (swap₃₄ (τ (W ! a)) (τ (W ! b)) (τ (W ! c)) (τ (W ! d))))

  ----------------------------------------------------------------------
  -- All cases, given the edge when x = d and the entry y is odd

  edge : (x ≡ d → Odd (W ! y) → Path Xw s o) → Path Xw s o
  edge eodd = byx (x FinP.≟ a) (x FinP.≟ b) (x FinP.≟ c) (x FinP.≟ d)
    where
    -- y just after an index u, and not the next index v.
    nxt : ∀ {u v : Fin n} → x ≡ u → u < v → y ≢ v → y < v
    nxt ≡.refl uv yv = ℕP.≤∧≢⇒< (after uv) (λ e → yv (FinP.toℕ-injective e))
    -- u < y when x = u.
    lt-y : ∀ {u : Fin n} → x ≡ u → u < y
    lt-y ≡.refl = xy′
    -- x < v when y = v.
    x-lt : ∀ {v : Fin n} → y ≡ v → x < v
    x-lt ≡.refl = xy′
    byx : Dec (x ≡ a) → Dec (x ≡ b) → Dec (x ≡ c) → Dec (x ≡ d) → Path Xw s o
    byx _ _ _ (yes xd) = by (odd? (W ! y))
      where
      by : Dec (Odd (W ! y)) → Path Xw s o
      by (yes oy) = eodd xd oy
      by (no ny) = up-d xd (¬Odd⇒Even {W ! y} ny)
    byx _ _ (yes xc) (no _) = by (y FinP.≟ d)
      where
      by : Dec (y ≡ d) → Path Xw s o
      by (yes yd) = both-cd xc yd
      by (no yd) = up-c xc (ev y y<d (lt≢ (FinP.<-trans (FinP.<-trans a<b b<c) cy)) (lt≢ (FinP.<-trans b<c cy)) (lt≢ cy)) yd
        where
        y<d = nxt xc c<d yd
        cy = lt-y xc
    byx _ (yes xb) (no _) (no _) = by (y FinP.≟ c)
      where
      by : Dec (y ≡ c) → Path Xw s o
      by (yes yc) = both-bc xb yc
      by (no yc) = up-b xb (ev y (FinP.<-trans y<c c<d) (lt≢ (FinP.<-trans a<b by′)) (lt≢ by′) yc) yc
        where
        y<c = nxt xb b<c yc
        by′ = lt-y xb
    byx (yes xa) (no _) (no _) (no _) = by (y FinP.≟ b)
      where
      by : Dec (y ≡ b) → Path Xw s o
      by (yes yb) = both-ab xa yb
      by (no yb) = up-a xa (ev y (FinP.<-trans y<b (FinP.<-trans b<c c<d)) (lt≢ (lt-y xa)) yb (ne< (FinP.<-trans y<b b<c))) yb
        where
        y<b = nxt xa a<b yb
    byx (no xa) (no xb) (no xc) (no xd) = byy (y FinP.≟ a) (y FinP.≟ b) (y FinP.≟ c) (y FinP.≟ d)
      where
      evx : ∀ {v} → y ≡ v → v ≤ d → Even (W ! x)
      evx {v} yv v≤d = ev x (ℕP.<-≤-trans (x-lt yv) v≤d) xa xb xc
      byy : Dec (y ≡ a) → Dec (y ≡ b) → Dec (y ≡ c) → Dec (y ≡ d) → Path Xw s o
      byy (yes ya) _ _ _ = down-a ya (evx ya (ℕP.<⇒≤ (FinP.<-trans a<b (FinP.<-trans b<c c<d))))
      byy (no _) (yes yb) _ _ = down-b yb (evx yb (ℕP.<⇒≤ (FinP.<-trans b<c c<d))) xa
      byy (no _) (no _) (yes yc) _ = down-c yc (evx yc (ℕP.<⇒≤ c<d)) xb
      byy (no _) (no _) (no _) (yes yd) = down-d yd (evx yd ℕP.≤-refl) xc
      byy (no ya) (no yb) (no yc) (no yd) = disjoint xa xb xc xd ya yb yc yd
