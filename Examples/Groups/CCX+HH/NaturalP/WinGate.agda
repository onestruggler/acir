------------------------------------------------------------------------
-- Presentations of groups
--
-- A window gate seen from a larger window.
--
-- On 4 + k + c wires a window gate is ⌈ inv A ⌉ • Λw k (Λw c Y) • ⌈ A ⌉
-- for an affine word A and a circuit Y on four wires: Y on the states
-- whose bottom k + c wires are 0, carried back by A.  Its frame is
-- what A carries onto those states, A⁻¹ of the window of the top four
-- wires.  If an affine word B sends that frame into the larger window,
-- the states whose bottom k wires are 0, then conjugating the gate by
-- B gives a gate on the larger window, Λw k X for a circuit X on the
-- top 4 + c wires (`conj-gate`).
--
-- X is ⌈ T ⌉ • Λw c Y • ⌈ inv T ⌉, where T is an affine word on the top
-- 4 + c wires that agrees with B ∘ A⁻¹ on the small window (two routes,
-- RouteTo.To, and a translation).  Then S = inv (T ↑ᵃ k) • B • inv A
-- fixes the small window, so ⌈ S ⌉ passes the gate (Nest.stab₂), and
-- what is left is T above the k controls, which passes into them
-- (`conj-Λw`, from LambdaLaws.under).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)
import Examples.Groups.CCX+HH.NaturalP.Schema as S

module Examples.Groups.CCX+HH.NaturalP.WinGate
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
open import Data.Bool.Properties using (xor-same ; xor-assoc ; xor-identityʳ)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (zero ; suc ; _+_ ; z≤n ; s≤s)
open import Data.Product.Base using (Σ ; _,_)
open import Relation.Binary.PropositionalEquality
  using (refl ; sym ; trans ; cong ; cong₂ ; subst ; subst₂)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)
open import Notations using (₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.Lambda using (Λw)
open import Examples.Groups.CCX+HH.NaturalP.LambdaLaws complete≤ using (under)
open import Examples.Groups.CCX+HH.NaturalP.Affine complete≤
  using (AGen ; _↥ₐ ; ιP ; ⌈_⌉ ; inv ; inv-r ; affine-complete ; act⇒interpret)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute
  using (A⟦_⟧ ; A-cong ; A-↑ ; A-inv ; A-injective ; _↑ₐ ; _⊕_ ; Lin ; Emb ; word-lin ; lin-∘)
open import Examples.Groups.CCX+HH.NaturalP.Window
  using (low ; high ; join ; join-lh ; join-resp ; low-⊕ ; high-⊕ ; low-resp ; high-resp)
open import Examples.Groups.CCX+HH.NaturalP.Nest complete≤ using (stab₂)
open import Examples.Groups.CCX+HH.NaturalP.Route4 using (tr ; tr-act ; stack)
open import Examples.Groups.CCX+HH.NaturalP.RouteTo using (module To)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_ ; lower)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros ; cons-cong)

private
  variable
    n c : ℕ

------------------------------------------------------------------------
-- Affine words above the controls

infixl 9 _↑ᵃ_
_↑ᵃ_ : Word (AGen (₄₊ c)) → ∀ k → Word (AGen (₄₊ (k + c)))
w ↑ᵃ zero  = w
w ↑ᵃ suc k = (w ↑ᵃ k) ↑ₐ

↑ᵃ-act : ∀ k (w : Word (AGen (₄₊ c))) (a : State k) (h : State (₄₊ c)) →
  A⟦ w ↑ᵃ k ⟧ (join k a h) ≈s join k a (A⟦ w ⟧ h)
↑ᵃ-act zero    w a h i = refl
↑ᵃ-act (suc k) w a h i =
  trans (A-↑ (w ↑ᵃ k) (a zero) (join k (lower a) h) i) (cons-cong refl (↑ᵃ-act k w (lower a) h) i)

inv-↑ : (w : Word (AGen n)) → inv (w ↑ₐ) ≡ inv w ↑ₐ
inv-↑ [ g ]ʷ  = refl
inv-↑ ε       = refl
inv-↑ (u • v) = cong₂ _•_ (inv-↑ v) (inv-↑ u)

inv-↑ᵃ : ∀ k (w : Word (AGen (₄₊ c))) → inv (w ↑ᵃ k) ≡ inv w ↑ᵃ k
inv-↑ᵃ zero    w = refl
inv-↑ᵃ (suc k) w = trans (inv-↑ (w ↑ᵃ k)) (cong _↑ₐ (inv-↑ᵃ k w))

inv-inv : (w : Word (AGen n)) → inv (inv w) ≡ w
inv-inv [ g ]ʷ  = refl
inv-inv ε       = refl
inv-inv (u • v) = cong₂ _•_ (inv-inv u) (inv-inv v)

⌈⌉-↑ : (w : Word (AGen n)) → ⌈ w ↑ₐ ⌉ ≡ ⌈ w ⌉ ↑
⌈⌉-↑ [ g ]ʷ  = refl
⌈⌉-↑ ε       = refl
⌈⌉-↑ (u • v) = cong₂ _•_ (⌈⌉-↑ u) (⌈⌉-↑ v)

-- The other cancellation.
A-inv′ : (w : Word (AGen n)) (s : State n) → A⟦ w ⟧ (A⟦ inv w ⟧ s) ≈s s
A-inv′ w s i = subst (λ v → A⟦ v ⟧ (A⟦ inv w ⟧ s) i ≡ s i) (inv-inv w) (A-inv (inv w) s i)

-- Words with the same action have inverses with the same action.
A-inv-same : (a b : Word (AGen n)) → (∀ s → A⟦ a ⟧ s ≈s A⟦ b ⟧ s) →
  ∀ s → A⟦ inv a ⟧ s ≈s A⟦ inv b ⟧ s
A-inv-same a b e s i =
  trans (sym (A-inv b (A⟦ inv a ⟧ s) i))
    (A-cong (inv b) (λ j → trans (sym (e (A⟦ inv a ⟧ s) j)) (A-inv′ a s j)) i)

-- An affine word above the controls passes into them.
conj-Λw : ∀ k (w : Word (AGen (₄₊ c))) (X : Circuit (₄₊ c)) →
  (₄₊ (k + c)) ⊢ ⌈ w ↑ᵃ k ⌉ • (Λw k X • ⌈ inv (w ↑ᵃ k) ⌉) ≈ Λw k (⌈ w ⌉ • (X • ⌈ inv w ⌉))
conj-Λw zero    w X = PB.refl
conj-Λw (suc k) w X =
  subst₂ (λ L R → _ ⊢ L • (Λw (suc k) X • R) ≈ Λw (suc k) (⌈ w ⌉ • (X • ⌈ inv w ⌉)))
    (sym (⌈⌉-↑ (w ↑ᵃ k)))
    (sym (trans (cong ⌈_⌉ (inv-↑ (w ↑ᵃ k))) (⌈⌉-↑ (inv (w ↑ᵃ k)))))
    (under (just false) (inv-r (w ↑ᵃ k)) (conj-Λw k w X))

------------------------------------------------------------------------
-- The window of the top four wires

private
  stack-add : ∀ m (h h′ : State 4) → stack m zeros (h ⊕ h′) ≈s stack m zeros h ⊕ stack m zeros h′
  stack-add zero    h h′ i       = refl
  stack-add (suc m) h h′ zero    = refl
  stack-add (suc m) h h′ (suc i) = stack-add m h h′ i

  stack-resp : ∀ m {h h′ : State 4} → h ≈s h′ → stack m zeros h ≈s stack m zeros h′
  stack-resp zero    e i       = e i
  stack-resp (suc m) e zero    = refl
  stack-resp (suc m) e (suc i) = stack-resp m e i

  stack-inj : ∀ m (h : State 4) → stack m zeros h ≈s zeros → h ≈s zeros
  stack-inj zero    h z i = z i
  stack-inj (suc m) h z i = stack-inj m h (λ j → z (suc j)) i

  stack-zeros : ∀ m → stack m zeros zeros ≈s zeros
  stack-zeros zero    i       = refl
  stack-zeros (suc m) zero    = refl
  stack-zeros (suc m) (suc i) = stack-zeros m i

  join-zeros : ∀ k {c} → join {c} k zeros zeros ≈s zeros
  join-zeros zero    i       = refl
  join-zeros (suc k) zero    = refl
  join-zeros (suc k) (suc i) = join-zeros k i

  stack-join : ∀ k c (h : State 4) → stack (k + (c + 0)) zeros h ≈s join k zeros (join c zeros h)
  stack-join zero    c h i       = stk0 c i
    where
    stk0 : ∀ c → stack (c + 0) zeros h ≈s join {0} c zeros h
    stk0 zero    i       = refl
    stk0 (suc c) zero    = refl
    stk0 (suc c) (suc i) = stk0 c i
  stack-join (suc k) c h zero    = refl
  stack-join (suc k) c h (suc i) = stack-join k c h i

stackE : ∀ m → Emb 4 (₄₊ m)
stackE m = record
  { f = stack m zeros ; lin = record { add = stack-add m ; resp = stack-resp m } ; inj = stack-inj m }

------------------------------------------------------------------------
-- The gate

module _ (k c : ℕ) where

  private
    W : ℕ
    W = ₄₊ (k + (c + 0))

  -- The small window, inside.
  ι₄ : State 4 → State W
  ι₄ = stack (k + (c + 0)) zeros

  conj-gate : (A B : Word (AGen W)) (Y : Circuit 4) →
    (∀ h → low k (A⟦ B ⟧ (A⟦ inv A ⟧ (ι₄ h))) ≈s zeros) →
    Σ (Circuit (₄₊ (c + 0))) λ X →
      W ⊢ ⌈ B ⌉ • ((⌈ inv A ⌉ • (Λw k (Λw c Y) • ⌈ A ⌉)) • ⌈ inv B ⌉) ≈ Λw k X
  conj-gate A B Y into = (⌈ T ⌉ • (Λw c Y • ⌈ inv T ⌉)) , chain
    where
    Lw : Word (AGen W)
    Lw = B • inv A
    t₀′ : State W
    t₀′ = A⟦ Lw ⟧ zeros
    L′w : Word (AGen W)
    L′w = tr t₀′ • Lw
    L′-zero : A⟦ L′w ⟧ zeros ≈s zeros
    L′-zero i = trans (tr-act t₀′ (A⟦ Lw ⟧ zeros) i) (xor-same (t₀′ i))
    L′-lin : Lin A⟦ L′w ⟧
    L′-lin = word-lin L′w L′-zero
    high-lin : Lin (high {c + 0} k)
    high-lin = record { add = high-⊕ k ; resp = high-resp k }
    -- The small window is carried into the large one.
    in-low : ∀ h → low k (A⟦ L′w ⟧ (ι₄ h)) ≈s zeros
    in-low h i =
      trans (low-resp k (tr-act t₀′ (A⟦ Lw ⟧ (ι₄ h))) i)
      (trans (low-⊕ k (A⟦ Lw ⟧ (ι₄ h)) t₀′ i)
        (cong₂ _xor_ (into h i)
          (trans (low-resp k (A-cong Lw (λ j → sym (stack-zeros (k + (c + 0)) j))) i)
            (into zeros i))))
    in-join : ∀ h → A⟦ L′w ⟧ (ι₄ h) ≈s join k zeros (high k (A⟦ L′w ⟧ (ι₄ h)))
    in-join h i = trans (sym (join-lh k (A⟦ L′w ⟧ (ι₄ h)) i))
      (join-resp k (in-low h) (λ _ → refl) i)
    M : State 4 → State (₄₊ (c + 0))
    M h = high k (A⟦ L′w ⟧ (ι₄ h))
    M-lin : Lin M
    M-lin = lin-∘ high-lin (lin-∘ L′-lin (Emb.lin (stackE (k + (c + 0)))))
    M-inj : ∀ h → M h ≈s zeros → h ≈s zeros
    M-inj h z = stack-inj (k + (c + 0)) h (A-injective L′w (λ i →
      trans (in-join h i) (trans (join-resp k (λ _ → refl) z i)
        (trans (join-zeros k i) (sym (L′-zero i))))))
    E′ : Emb 4 (₄₊ (c + 0))
    E′ = record { f = M ; lin = M-lin ; inj = M-inj }
    module R = To (s≤s (s≤s (s≤s (s≤s z≤n)))) (stackE (c + 0)) E′
    t₀ : State (₄₊ (c + 0))
    t₀ = high k t₀′
    T : Word (AGen (₄₊ (c + 0)))
    T = tr t₀ • R.B
    -- T agrees with B ∘ A⁻¹ on the small window.
    T-ok : ∀ h → A⟦ T ⟧ (stack (c + 0) zeros h) ≈s high k (A⟦ Lw ⟧ (ι₄ h))
    T-ok h i =
      trans (tr-act t₀ (A⟦ R.B ⟧ (stack (c + 0) zeros h)) i)
      (trans (cong (_xor t₀ i) (R.B-ok h i))
      (trans (cong (_xor t₀ i)
               (trans (high-resp k (tr-act t₀′ (A⟦ Lw ⟧ (ι₄ h))) i)
                 (high-⊕ k (A⟦ Lw ⟧ (ι₄ h)) t₀′ i)))
      (trans (xor-assoc (high k (A⟦ Lw ⟧ (ι₄ h)) i) (t₀ i) (t₀ i))
      (trans (cong (high k (A⟦ Lw ⟧ (ι₄ h)) i xor_) (xor-same (t₀ i)))
        (xor-identityʳ _)))))
    Tk : Word (AGen W)
    Tk = T ↑ᵃ k
    Sw : Word (AGen W)
    Sw = inv Tk • Lw
    -- S fixes the small window.
    S-fix : ∀ x → low {c + 0} k x ≈s zeros → low {0} c (high {c + 0} k x) ≈s zeros → A⟦ Sw ⟧ x ≈s x
    S-fix x z₁ z₂ i =
      trans (A-cong (inv Tk) (λ j → trans (A-cong Lw (λ y → sym (x-ι y)) j) (lw j)) i)
      (trans (A-cong (inv Tk) (λ j → join-resp k (λ _ → refl) (λ y → sym (T-ok h y)) j) i)
      (trans (subst (λ v → A⟦ v ⟧ (join k zeros (A⟦ T ⟧ H)) i ≡ join k zeros (A⟦ inv T ⟧ (A⟦ T ⟧ H)) i)
                (sym (inv-↑ᵃ k T)) (↑ᵃ-act k (inv T) zeros (A⟦ T ⟧ H) i))
      (trans (join-resp k (λ _ → refl) (A-inv T H) i)
        (x-ι i))))
      where
      h : State 4
      h = high c (high k x)
      H : State (₄₊ (c + 0))
      H = stack (c + 0) zeros h
      x-ι : join k zeros H ≈s x
      x-ι y = trans (join-resp k (λ _ → refl) (stack-join 0 c h) y)
        (trans (join-resp k (λ _ → refl) (λ j → trans (join-resp c (λ l → sym (z₂ l)) (λ _ → refl) j)
                                          (join-lh c (high k x) j)) y)
        (trans (join-resp k (λ l → sym (z₁ l)) (λ _ → refl) y) (join-lh k x y)))
      -- ι₄ h is that state too.
      ι-x : ι₄ h ≈s join k zeros H
      ι-x y = trans (stack-join k c h y) (join-resp k (λ _ → refl) (λ j → sym (stack-join 0 c h j)) y)
      lw : A⟦ Lw ⟧ (join k zeros H) ≈s join k zeros (high k (A⟦ Lw ⟧ (ι₄ h)))
      lw y = trans (A-cong Lw (λ j → sym (ι-x j)) y)
        (trans (sym (join-lh k (A⟦ Lw ⟧ (ι₄ h)) y)) (join-resp k (into h) (λ _ → refl) y))
    aff₁ : W ⊢ ⌈ Lw ⌉ ≈ ⌈ Tk • Sw ⌉
    aff₁ = affine-complete Lw (Tk • Sw) (act⇒interpret Lw (Tk • Sw) (λ s i → sym (A-inv′ Tk (A⟦ Lw ⟧ s) i)))
    aff₂ : W ⊢ ⌈ A ⌉ • ⌈ inv B ⌉ ≈ ⌈ inv Sw ⌉ • ⌈ inv Tk ⌉
    aff₂ = subst (λ v → W ⊢ ⌈ v ⌉ • ⌈ inv B ⌉ ≈ ⌈ inv Sw ⌉ • ⌈ inv Tk ⌉) (inv-inv A)
      (affine-complete (inv Lw) (inv (Tk • Sw))
        (act⇒interpret (inv Lw) (inv (Tk • Sw))
          (A-inv-same Lw (Tk • Sw) (λ s i → sym (A-inv′ Tk (A⟦ Lw ⟧ s) i)))))
    Λ₁ : Circuit W
    Λ₁ = Λw k (Λw c Y)
    chain : W ⊢ ⌈ B ⌉ • ((⌈ inv A ⌉ • (Λ₁ • ⌈ A ⌉)) • ⌈ inv B ⌉) ≈ Λw k (⌈ T ⌉ • (Λw c Y • ⌈ inv T ⌉))
    chain =
      PB.trans (PB.cong PB.refl PB.assoc)
      (PB.trans (PB.sym PB.assoc)
      (PB.trans (PB.cong PB.refl PB.assoc)
      (PB.trans (PB.cong aff₁ (PB.cong PB.refl aff₂))
      (PB.trans PB.assoc
      (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.sym PB.assoc)))
      (PB.trans (PB.cong PB.refl (PB.sym PB.assoc))
      (PB.trans (PB.cong PB.refl (PB.cong (stab₂ k c 0 Sw S-fix Y) PB.refl))
        (conj-Λw k T (Λw c Y)))))))))
