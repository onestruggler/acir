------------------------------------------------------------------------
-- Presentations of groups
--
-- The square of the paper's path for the edge X_[d,e] when e is odd
-- (Lemma A.20, Subcase 1.2.2.3).
--
-- For indices a < b < c < d < e < f < g < h, write K = K_[a,b,c,d],
-- K′ = K_[e,f,g,h], and D₁, D₂ for the signs (-1)^τ on a, b, c, d and on
-- e, f, g, h.  From s the path takes K D₁, then K′ D₂, then S, K and
-- K′; from X_[d,e]·s the same with τ_d and τ_e exchanged (the entries d
-- and e are).  Both end at the same state:
--
--   X K′ K S K′ D₂ K D₁ = K′ K S K′ D₂′ K D₁′ X,
--
-- because the signs D₂ commute with K and the rest with X up to the
-- exchange, which leaves X Z = Z X for Z = K′ K S K′ K (Rel8).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH-TwoLevel.QuadXERel {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.CCX+HH-TwoLevel.Column using (Mτ)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (<⇒≢)
open import Examples.Groups.CCX+HH-TwoLevel.Signs {n} using (Apart ; Mτ-comm ; Mτ-X′ ; Mτ-X)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  ne< : ∀ {u v : Fin n} → u < v → u ≢ v
  ne< = λ lt → <⇒≢ lt

  -- Two signs on different indices commute.
  Mτ-Mτ : ∀ x τ y τ′ → x ≢ y → Mτ x τ • Mτ y τ′ ≈ Mτ y τ′ • Mτ x τ
  Mτ-Mτ x τ y true  xy = Mτ-comm x τ (M-gen y) xy
  Mτ-Mτ x τ y false xy = trans right-unit (sym left-unit)

  -- A word commuting with each of four signs commutes with them all.
  through4 : ∀ {G m₁ m₂ m₃ m₄ : Word (Gen n)} → m₁ • G ≈ G • m₁ → m₂ • G ≈ G • m₂ → m₃ • G ≈ G • m₃ → m₄ • G ≈ G • m₄ →
             (m₁ • (m₂ • (m₃ • m₄))) • G ≈ G • (m₁ • (m₂ • (m₃ • m₄)))
  through4 {G} {m₁} {m₂} {m₃} {m₄} h₁ h₂ h₃ h₄ = begin
    (m₁ • (m₂ • (m₃ • m₄))) • G      ≈⟨ assoc ⟩
    m₁ • ((m₂ • (m₃ • m₄)) • G)      ≈⟨ cright assoc ⟩
    m₁ • (m₂ • ((m₃ • m₄) • G))      ≈⟨ cright cright assoc ⟩
    m₁ • (m₂ • (m₃ • (m₄ • G)))      ≈⟨ cright cright cright h₄ ⟩
    m₁ • (m₂ • (m₃ • (G • m₄)))      ≈⟨ cright cright (trans (sym assoc) (cleft h₃)) ⟩
    m₁ • (m₂ • ((G • m₃) • m₄))      ≈⟨ cright cright assoc ⟩
    m₁ • (m₂ • (G • (m₃ • m₄)))      ≈⟨ cright (trans (sym assoc) (cleft h₂)) ⟩
    m₁ • ((G • m₂) • (m₃ • m₄))      ≈⟨ cright assoc ⟩
    m₁ • (G • (m₂ • (m₃ • m₄)))      ≈⟨ trans (sym assoc) (cleft h₁) ⟩
    (G • m₁) • (m₂ • (m₃ • m₄))      ≈⟨ assoc ⟩
    G • (m₁ • (m₂ • (m₃ • m₄)))      ∎

  -- A sign commutes with a generator apart from it, on either side.
  sign-g : ∀ x τ (g : Gen n) → Apart x g → Mτ x τ • [ g ]ʷ ≈ [ g ]ʷ • Mτ x τ
  sign-g = Mτ-comm

module _ {a b c d e f g h : Fin n} (ab : a < b) (bc : b < c) (cd : c < d) (de : d < e) (ef : e < f) (fg : f < g) (gh : g < h)
         (τa τb τc τd τe τf τg τh : Bool) (S : Word (Gen n)) where

  private
    -- Order facts.
    ac = FinP.<-trans ab bc
    ad = FinP.<-trans ac cd
    ae = FinP.<-trans ad de
    af = FinP.<-trans ae ef
    ag = FinP.<-trans af fg
    ah = FinP.<-trans ag gh
    bd = FinP.<-trans bc cd
    be = FinP.<-trans bd de
    bf = FinP.<-trans be ef
    bg = FinP.<-trans bf fg
    bh = FinP.<-trans bg gh
    ce = FinP.<-trans cd de
    cf = FinP.<-trans ce ef
    cg = FinP.<-trans cf fg
    ch = FinP.<-trans cg gh
    df = FinP.<-trans de ef
    dg = FinP.<-trans df fg
    dh = FinP.<-trans dg gh
    eg = FinP.<-trans ef fg
    eh = FinP.<-trans eg gh
    fh = FinP.<-trans fg gh
    gt : ∀ {u v : Fin n} → u < v → v ≢ u
    gt lt e = ne< lt (≡.sym e)

  K₁ K₂ X₀ : Gen n
  K₁ = K-gen a b c d ab bc cd
  K₂ = K-gen e f g h ef fg gh
  X₀ = X-gen d e de

  D₁ D₂ D₁′ D₂′ : Word (Gen n)
  D₁ = Mτ a τa • (Mτ b τb • (Mτ c τc • Mτ d τd))
  D₂ = Mτ e τe • (Mτ f τf • (Mτ g τg • Mτ h τh))
  D₁′ = Mτ a τa • (Mτ b τb • (Mτ c τc • Mτ d τe))
  D₂′ = Mτ e τd • (Mτ f τf • (Mτ g τg • Mτ h τh))

  -- Z = K′ K S K′ K.
  Z : Word (Gen n)
  Z = [ K₂ ]ʷ • ([ K₁ ]ʷ • (S • ([ K₂ ]ʷ • [ K₁ ]ʷ)))

  private
    -- The signs on e, f, g, h commute with K.
    D₂K : ∀ τ → (Mτ e τ • (Mτ f τf • (Mτ g τg • Mτ h τh))) • [ K₁ ]ʷ ≈ [ K₁ ]ʷ • (Mτ e τ • (Mτ f τf • (Mτ g τg • Mτ h τh)))
    D₂K τ = through4 (sign-g e τ K₁ (gt ae , gt be , gt ce , gt de)) (sign-g f τf K₁ (gt af , gt bf , gt cf , gt df))
                     (sign-g g τg K₁ (gt ag , gt bg , gt cg , gt dg)) (sign-g h τh K₁ (gt ah , gt bh , gt ch , gt dh))

    -- The common signs, on a, b, c, f, g, h.
    A F : Word (Gen n)
    A = Mτ a τa • (Mτ b τb • Mτ c τc)
    F = Mτ f τf • (Mτ g τg • Mτ h τh)

    -- D₂ D₁ = F A (signs on d, e).
    regroup : ∀ τ₁ τ₂ → (Mτ e τ₂ • F) • (A • Mτ d τ₁) ≈ (F • A) • (Mτ d τ₁ • Mτ e τ₂)
    regroup τ₁ τ₂ = begin
      (Mτ e τ₂ • F) • (A • Mτ d τ₁)          ≈⟨ cleft eF ⟩
      (F • Mτ e τ₂) • (A • Mτ d τ₁)          ≈⟨ assoc ⟩
      F • (Mτ e τ₂ • (A • Mτ d τ₁))          ≈⟨ cright (trans (sym assoc) (cleft eA)) ⟩
      F • ((A • Mτ e τ₂) • Mτ d τ₁)          ≈⟨ cright assoc ⟩
      F • (A • (Mτ e τ₂ • Mτ d τ₁))          ≈⟨ cright cright Mτ-Mτ e τ₂ d τ₁ (gt de) ⟩
      F • (A • (Mτ d τ₁ • Mτ e τ₂))          ≈⟨ sym assoc ⟩
      (F • A) • (Mτ d τ₁ • Mτ e τ₂)          ∎
      where
      eF : Mτ e τ₂ • F ≈ F • Mτ e τ₂
      eF = begin
        Mτ e τ₂ • (Mτ f τf • (Mτ g τg • Mτ h τh))   ≈⟨ trans (sym assoc) (cleft Mτ-Mτ e τ₂ f τf (ne< ef)) ⟩
        (Mτ f τf • Mτ e τ₂) • (Mτ g τg • Mτ h τh)   ≈⟨ assoc ⟩
        Mτ f τf • (Mτ e τ₂ • (Mτ g τg • Mτ h τh))   ≈⟨ cright (trans (sym assoc) (cleft Mτ-Mτ e τ₂ g τg (ne< eg))) ⟩
        Mτ f τf • ((Mτ g τg • Mτ e τ₂) • Mτ h τh)   ≈⟨ cright assoc ⟩
        Mτ f τf • (Mτ g τg • (Mτ e τ₂ • Mτ h τh))   ≈⟨ cright cright Mτ-Mτ e τ₂ h τh (ne< eh) ⟩
        Mτ f τf • (Mτ g τg • (Mτ h τh • Mτ e τ₂))   ≈⟨ cright sym assoc ⟩
        Mτ f τf • ((Mτ g τg • Mτ h τh) • Mτ e τ₂)   ≈⟨ sym assoc ⟩
        F • Mτ e τ₂                                 ∎
      eA : Mτ e τ₂ • A ≈ A • Mτ e τ₂
      eA = begin
        Mτ e τ₂ • (Mτ a τa • (Mτ b τb • Mτ c τc))   ≈⟨ trans (sym assoc) (cleft Mτ-Mτ e τ₂ a τa (gt ae)) ⟩
        (Mτ a τa • Mτ e τ₂) • (Mτ b τb • Mτ c τc)   ≈⟨ assoc ⟩
        Mτ a τa • (Mτ e τ₂ • (Mτ b τb • Mτ c τc))   ≈⟨ cright (trans (sym assoc) (cleft Mτ-Mτ e τ₂ b τb (gt be))) ⟩
        Mτ a τa • ((Mτ b τb • Mτ e τ₂) • Mτ c τc)   ≈⟨ cright assoc ⟩
        Mτ a τa • (Mτ b τb • (Mτ e τ₂ • Mτ c τc))   ≈⟨ cright cright Mτ-Mτ e τ₂ c τc (gt ce) ⟩
        Mτ a τa • (Mτ b τb • (Mτ c τc • Mτ e τ₂))   ≈⟨ cright sym assoc ⟩
        Mτ a τa • ((Mτ b τb • Mτ c τc) • Mτ e τ₂)   ≈⟨ sym assoc ⟩
        A • Mτ e τ₂                                 ∎

    -- D₁ = A (-1)_[d]^τ.
    D₁-A : ∀ τ → Mτ a τa • (Mτ b τb • (Mτ c τc • Mτ d τ)) ≈ A • Mτ d τ
    D₁-A τ = trans (cright sym assoc) (sym assoc)

    -- X commutes with F and A.
    through3 : ∀ {G m₁ m₂ m₃ : Word (Gen n)} → m₁ • G ≈ G • m₁ → m₂ • G ≈ G • m₂ → m₃ • G ≈ G • m₃ →
               (m₁ • (m₂ • m₃)) • G ≈ G • (m₁ • (m₂ • m₃))
    through3 {G} {m₁} {m₂} {m₃} h₁ h₂ h₃ = begin
      (m₁ • (m₂ • m₃)) • G      ≈⟨ assoc ⟩
      m₁ • ((m₂ • m₃) • G)      ≈⟨ cright assoc ⟩
      m₁ • (m₂ • (m₃ • G))      ≈⟨ cright cright h₃ ⟩
      m₁ • (m₂ • (G • m₃))      ≈⟨ cright (trans (sym assoc) (cleft h₂)) ⟩
      m₁ • ((G • m₂) • m₃)      ≈⟨ cright assoc ⟩
      m₁ • (G • (m₂ • m₃))      ≈⟨ trans (sym assoc) (cleft h₁) ⟩
      (G • m₁) • (m₂ • m₃)      ≈⟨ assoc ⟩
      G • (m₁ • (m₂ • m₃))      ∎

    FX : F • [ X₀ ]ʷ ≈ [ X₀ ]ʷ • F
    FX = through3 (sign-g f τf X₀ (gt df , gt ef)) (sign-g g τg X₀ (gt dg , gt eg)) (sign-g h τh X₀ (gt dh , gt eh))

    AX : A • [ X₀ ]ʷ ≈ [ X₀ ]ʷ • A
    AX = through3 (sign-g a τa X₀ (ne< ad , ne< ae)) (sign-g b τb X₀ (ne< bd , ne< be)) (sign-g c τc X₀ (ne< cd , ne< ce))

    FAX : (F • A) • [ X₀ ]ʷ ≈ [ X₀ ]ʷ • (F • A)
    FAX = begin
      (F • A) • [ X₀ ]ʷ        ≈⟨ assoc ⟩
      F • (A • [ X₀ ]ʷ)        ≈⟨ cright AX ⟩
      F • ([ X₀ ]ʷ • A)        ≈⟨ sym assoc ⟩
      (F • [ X₀ ]ʷ) • A        ≈⟨ cleft FX ⟩
      ([ X₀ ]ʷ • F) • A        ≈⟨ assoc ⟩
      [ X₀ ]ʷ • (F • A)        ∎

    -- One side, down to Z and the signs.
    Pre : ∀ τ₁ τ₂ → ([ K₂ ]ʷ • ([ K₁ ]ʷ • (S • ([ K₂ ]ʷ • (Mτ e τ₂ • F))))) • ([ K₁ ]ʷ • (Mτ a τa • (Mτ b τb • (Mτ c τc • Mτ d τ₁))))
                    ≈ Z • ((F • A) • (Mτ d τ₁ • Mτ e τ₂))
    Pre τ₁ τ₂ = begin
      (K′w • (Kw • (S • (K′w • De)))) • (Kw • Dd)        ≈⟨ assoc ⟩
      K′w • ((Kw • (S • (K′w • De))) • (Kw • Dd))        ≈⟨ cright assoc ⟩
      K′w • (Kw • ((S • (K′w • De)) • (Kw • Dd)))        ≈⟨ cright cright assoc ⟩
      K′w • (Kw • (S • ((K′w • De) • (Kw • Dd))))        ≈⟨ cright cright cright assoc ⟩
      K′w • (Kw • (S • (K′w • (De • (Kw • Dd)))))        ≈⟨ cright cright cright cright (trans (sym assoc) (cleft D₂K τ₂)) ⟩
      K′w • (Kw • (S • (K′w • ((Kw • De) • Dd))))        ≈⟨ cright cright cright cright assoc ⟩
      K′w • (Kw • (S • (K′w • (Kw • (De • Dd)))))        ≈⟨ cright cright cright sym assoc ⟩
      K′w • (Kw • (S • ((K′w • Kw) • (De • Dd))))        ≈⟨ cright cright sym assoc ⟩
      K′w • (Kw • ((S • (K′w • Kw)) • (De • Dd)))        ≈⟨ cright sym assoc ⟩
      K′w • ((Kw • (S • (K′w • Kw))) • (De • Dd))        ≈⟨ sym assoc ⟩
      Z • (De • Dd)                                      ≈⟨ cright cright D₁-A τ₁ ⟩
      Z • (De • (A • Mτ d τ₁))                           ≈⟨ cright regroup τ₁ τ₂ ⟩
      Z • ((F • A) • (Mτ d τ₁ • Mτ e τ₂))                ∎
      where
      Kw = [ K₁ ]ʷ
      K′w = [ K₂ ]ʷ
      De = Mτ e τ₂ • F
      Dd = Mτ a τa • (Mτ b τb • (Mτ c τc • Mτ d τ₁))

    -- The signs on d and e, across X.
    swapX : (Mτ d τe • Mτ e τd) • [ X₀ ]ʷ ≈ [ X₀ ]ʷ • (Mτ d τd • Mτ e τe)
    swapX = begin
      (Mτ d τe • Mτ e τd) • Xw        ≈⟨ assoc ⟩
      Mτ d τe • (Mτ e τd • Xw)        ≈⟨ cright sym (Mτ-X′ de τd) ⟩
      Mτ d τe • (Xw • Mτ d τd)        ≈⟨ sym assoc ⟩
      (Mτ d τe • Xw) • Mτ d τd        ≈⟨ cleft sym (Mτ-X de τe) ⟩
      (Xw • Mτ e τe) • Mτ d τd        ≈⟨ assoc ⟩
      Xw • (Mτ e τe • Mτ d τd)        ≈⟨ cright Mτ-Mτ e τe d τd (gt de) ⟩
      Xw • (Mτ d τd • Mτ e τe)        ∎
      where Xw = [ X₀ ]ʷ

  -- The square.
  square : [ X₀ ]ʷ • Z ≈ Z • [ X₀ ]ʷ →
           ([ X₀ ]ʷ • ([ K₂ ]ʷ • ([ K₁ ]ʷ • (S • ([ K₂ ]ʷ • D₂))))) • ([ K₁ ]ʷ • D₁)
           ≈ (([ K₂ ]ʷ • ([ K₁ ]ʷ • (S • ([ K₂ ]ʷ • D₂′)))) • ([ K₁ ]ʷ • D₁′)) • [ X₀ ]ʷ
  square xz = begin
    (Xw • P) • (Kw • D₁)                                 ≈⟨ assoc ⟩
    Xw • (P • (Kw • D₁))                                 ≈⟨ cright Pre τd τe ⟩
    Xw • (Z • ((F • A) • (Mτ d τd • Mτ e τe)))           ≈⟨ sym assoc ⟩
    (Xw • Z) • ((F • A) • (Mτ d τd • Mτ e τe))           ≈⟨ cleft xz ⟩
    (Z • Xw) • ((F • A) • (Mτ d τd • Mτ e τe))           ≈⟨ assoc ⟩
    Z • (Xw • ((F • A) • (Mτ d τd • Mτ e τe)))           ≈⟨ cright sym assoc ⟩
    Z • ((Xw • (F • A)) • (Mτ d τd • Mτ e τe))           ≈⟨ cright cleft sym FAX ⟩
    Z • (((F • A) • Xw) • (Mτ d τd • Mτ e τe))           ≈⟨ cright assoc ⟩
    Z • ((F • A) • (Xw • (Mτ d τd • Mτ e τe)))           ≈⟨ cright cright sym swapX ⟩
    Z • ((F • A) • ((Mτ d τe • Mτ e τd) • Xw))           ≈⟨ cright sym assoc ⟩
    Z • (((F • A) • (Mτ d τe • Mτ e τd)) • Xw)           ≈⟨ sym assoc ⟩
    (Z • ((F • A) • (Mτ d τe • Mτ e τd))) • Xw           ≈⟨ cleft sym (Pre τe τd) ⟩
    (P′ • (Kw • D₁′)) • Xw                               ∎
    where
    Xw = [ X₀ ]ʷ
    Kw = [ K₁ ]ʷ
    P = [ K₂ ]ʷ • ([ K₁ ]ʷ • (S • ([ K₂ ]ʷ • D₂)))
    P′ = [ K₂ ]ʷ • ([ K₁ ]ʷ • (S • ([ K₂ ]ʷ • D₂′)))
