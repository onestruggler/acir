------------------------------------------------------------------------
-- Presentations of groups
--
-- The pieces of a gate, as states.
--
-- Merge.recover-win writes a gate x as window gates, one for each
-- colouring p of the controls, moved back by trW p • N.  Read backwards
-- that word sends the window state of h to F h = N⁻¹ (ι₄ h ⊕ col p),
-- where col p is the colouring as a state, zero on the top four wires
-- (`trW-inv-act`, `col-top`).  So the sixteen states of a piece, listed
-- by h, have increasing indices (`emb`, from GateMono), and they lie in
-- the span of the five states F 0 and F (unit j) ⊕ F 0 (`F-span`), F
-- being affine.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)
import Examples.Groups.CCX+HH.NaturalP.Schema as S

module Examples.Groups.CCX+HH.NaturalP.GatePieces
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
open import Data.Bool.Properties using (xor-identityʳ ; xor-assoc ; xor-comm ; xor-same)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (zero ; suc ; _+_ ; _^_)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup ; tabulate ; _++_)
open import Relation.Binary.PropositionalEquality
  using (refl ; sym ; trans ; cong ; cong₂ ; subst ; subst₂)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₄₊)

open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_ ; lower)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros ; cons-view)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (cons ; idx ; bits ; idx-cong)
open import Examples.Groups.CCX+HH.NaturalP.Schema using (Gen)
open import Examples.Groups.CCX+HH.NaturalP.AffineWords using (AGen ; ax ; inv)
import Examples.Groups.CCX+HH.NaturalP.AffineRoute as AR
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute
  using (A⟦_⟧ ; A-cong ; A-↑ ; _↑ₐ ; _⊕_ ; unit ; Lin ; lin-zero ; lin-ext ; aff)
open import Examples.Groups.CCX+HH.NaturalP.Window
  using (low ; high ; join ; join-lh ; join-resp ; join-⊕ ; high-join ; high-resp)
open import Examples.Groups.CCX+HH.NaturalP.Span using (InSpan ; E4 ; comb)
open import Examples.Groups.CCX+HH.NaturalP.SpanEmb using (comb-lin ; comb-unit ; span-++ˡ)
open import Examples.Groups.CCX+HH.NaturalP.Transport using (placed)
open import Examples.Groups.CCX+HH.NaturalP.GateMono using (ι₄ ; top4 ; mono-placed)
open import Examples.Groups.CCX+HH.NaturalP.WinGate complete≤ using (_↑ᵃ_ ; ↑ᵃ-act ; inv-↑ᵃ ; stackE)
open import Examples.Groups.CCX+HH.NaturalP.Merge complete≤ using (trC ; trW)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Colourings as states

vs : ∀ {k} → Vec Bool k → State k
vs s i = lookup s i

private
  inv-↑ : (w : Word (AGen n)) → inv (w ↑ₐ) ≡ inv w ↑ₐ
  inv-↑ [ g ]ʷ  = refl
  inv-↑ ε       = refl
  inv-↑ (u • v) = cong₂ _•_ (inv-↑ v) (inv-↑ u)

  up-act : (w : Word (AGen n)) (y : State (suc n)) →
    A⟦ inv (w ↑ₐ) ⟧ y ≈s cons (y zero) (A⟦ inv w ⟧ (lower y))
  up-act w y i =
    trans (cong (λ v → A⟦ v ⟧ y i) (inv-↑ w))
      (trans (A-cong (inv w ↑ₐ) (λ j → sym (cons-view y j)) i) (A-↑ (inv w) (y zero) (lower y) i))

trC-inv-act : ∀ {c} k (s : Vec Bool k) (x : State (₄₊ (k + c))) →
  A⟦ inv (trC {c = c} s) ⟧ x ≈s x ⊕ join k (vs s) zeros
trC-inv-act zero    []          x i = sym (xor-identityʳ (x i))
trC-inv-act (suc k) (true ∷ s)  x i =
  trans (up-act (trC s) (A⟦ [ ax ]ʷ ⟧ x) i) (at i)
  where
  at : ∀ i → cons (x zero xor true) (A⟦ inv (trC s) ⟧ (lower x)) i ≡ (x ⊕ join (suc k) (vs (true ∷ s)) zeros) i
  at zero    = refl
  at (suc i) = trC-inv-act k s (lower x) i
trC-inv-act (suc k) (false ∷ s) x i = trans (up-act (trC s) x i) (at i)
  where
  at : ∀ i → cons (x zero) (A⟦ inv (trC s) ⟧ (lower x)) i ≡ (x ⊕ join (suc k) (vs (false ∷ s)) zeros) i
  at zero    = sym (xor-identityʳ (x zero))
  at (suc i) = trC-inv-act k s (lower x) i

-- The colouring of both levels, as a state.
col : ∀ k c → Vec Bool k → Vec Bool c → State (₄₊ (k + (c + 0)))
col k c s₁ s₂ = join k (vs s₁) (join {0} c (vs s₂) zeros)

private
  b3 : ∀ a b c → (a xor b) xor c ≡ (a xor c) xor b
  b3 a b c = trans (xor-assoc a b c) (trans (cong (a xor_) (xor-comm b c)) (sym (xor-assoc a c b)))

trW-inv-act : ∀ k c (s₁ : Vec Bool k) (s₂ : Vec Bool c) (x : State (₄₊ (k + (c + 0)))) →
  A⟦ inv (trW k c s₁ s₂) ⟧ x ≈s x ⊕ col k c s₁ s₂
trW-inv-act k c s₁ s₂ x i =
  trans (trC-inv-act k s₁ (A⟦ inv (T₂ ↑ᵃ k) ⟧ x) i)
  (trans (cong (_xor join k (vs s₁) zeros i) (inner i))
    (fin i))
  where
  T₂ = trC {c = 0} s₂
  J = join {0} c (vs s₂) zeros
  inner : A⟦ inv (T₂ ↑ᵃ k) ⟧ x ≈s join k (low k x) (high k x ⊕ J)
  inner j =
    trans (cong (λ v → A⟦ v ⟧ x j) (inv-↑ᵃ k T₂))
    (trans (A-cong (inv T₂ ↑ᵃ k) (λ l → sym (join-lh k x l)) j)
    (trans (↑ᵃ-act k (inv T₂) (low k x) (high k x) j)
      (join-resp k (λ _ → refl) (trC-inv-act c s₂ (high k x)) j)))
  fin : ∀ j → join k (low k x) (high k x ⊕ J) j xor join k (vs s₁) zeros j ≡ (x ⊕ col k c s₁ s₂) j
  fin j =
    trans (cong (_xor join k (vs s₁) zeros j)
            (trans (join-resp k (λ l → sym (xor-identityʳ (low k x l))) (λ _ → refl) j)
              (join-⊕ k (low k x) zeros (high k x) J j)))
    (trans (b3 (join k (low k x) (high k x) j) (join k zeros J j) (join k (vs s₁) zeros j))
    (trans (xor-assoc (join k (low k x) (high k x) j) (join k (vs s₁) zeros j) (join k zeros J j))
    (cong₂ _xor_ (join-lh k x j)
      (trans (sym (join-⊕ k (vs s₁) zeros zeros J j))
        (join-resp k (λ l → xor-identityʳ (vs s₁ l)) (λ l → refl) j)))))

col-top : ∀ k c (s₁ : Vec Bool k) (s₂ : Vec Bool c) → top4 k c (col k c s₁ s₂) ≈s zeros
col-top k c s₁ s₂ i =
  trans (high-resp c (high-join k (vs s₁) (join {0} c (vs s₂) zeros)) i) (high-join c (vs s₂) zeros i)

------------------------------------------------------------------------
-- One piece

module Piece (k c : ℕ) (x : Gen (₄₊ (k + (c + 0)))) (s₁ : Vec Bool k) (s₂ : Vec Bool c) where

  W : ℕ
  W = ₄₊ (k + (c + 0))

  N : Word (AGen W)
  N = proj₁ (placed k c x)

  -- The window gate of the piece is moved back by this word.
  A′ : Word (AGen W)
  A′ = trW k c s₁ s₂ • N

  F : State 4 → State W
  F h = A⟦ inv A′ ⟧ (ι₄ k c h)

  F-col : ∀ h → F h ≈s A⟦ inv N ⟧ (ι₄ k c h ⊕ col k c s₁ s₂)
  F-col h = A-cong (inv N) (trW-inv-act k c s₁ s₂ (ι₄ k c h))

  -- Its sixteen states, by index.
  pts : Fin 16 → Fin (2 ^ W)
  pts y = idx W (F (bits 4 y))

  emb : Emb 16 (2 ^ W)
  emb = record { ι = pts ; mono = λ {y} {y′} lt →
    subst₂ _<_ (sym (e y)) (sym (e y′))
      (mono-placed k c x (col k c s₁ s₂) (col-top k c s₁ s₂) y y′ lt) }
    where
    e : ∀ y → pts y ≡ idx W (A⟦ inv N ⟧ (ι₄ k c (bits 4 y) ⊕ col k c s₁ s₂))
    e y = idx-cong W (F-col (bits 4 y))

  -- F is affine: its differences from F 0 are linear.
  G : State 4 → State W
  G h = F h ⊕ F zeros

  private
    ι-lin : Lin (ι₄ k c)
    ι-lin = AR.Emb.lin (stackE (k + (c + 0)))

    ι-zero : ι₄ k c zeros ≈s zeros
    ι-zero = lin-zero ι-lin

    c1 : ∀ a b z → ((a xor b) xor z) xor z ≡ a xor b
    c1 a b z = trans (xor-assoc (a xor b) z z) (trans (cong ((a xor b) xor_) (xor-same z)) (xor-identityʳ _))

    c2 : ∀ a b z → (a xor z) xor (b xor z) ≡ a xor b
    c2 a b z = trans (cong ((a xor z) xor_) (xor-comm b z))
      (trans (xor-assoc a z (z xor b))
      (trans (cong (a xor_) (trans (sym (xor-assoc z z b)) (cong (_xor b) (xor-same z)))) refl))

  G-lin : Lin G
  G-lin = record
    { add  = λ h h′ i →
        trans (cong (_xor F zeros i)
                (trans (A-cong (inv A′) (λ j → trans (Lin.add ι-lin h h′ j)
                          (trans (sym (xor-identityʳ _)) (cong ((ι₄ k c h j xor ι₄ k c h′ j) xor_) (sym (ι-zero j))))) i)
                  (aff (inv A′) (ι₄ k c h) (ι₄ k c h′) (ι₄ k c zeros) i)))
          (trans (c1 (F h i) (F h′ i) (F zeros i)) (sym (c2 (F h i) (F h′ i) (F zeros i))))
    ; resp = λ e i → cong (_xor F zeros i) (A-cong (inv A′) (Lin.resp ι-lin e) i) }

  dirs : Vec (State W) 4
  dirs = G (unit zero) ∷ G (unit (suc zero)) ∷ G (unit (suc (suc zero))) ∷ G (unit (suc (suc (suc zero)))) ∷ []

  -- The frame of the piece: F 0, the four differences, and the unit
  -- vectors of the bottom four wires.
  frameP : Vec (State W) 9
  frameP = (F zeros ∷ dirs) ++ E4

  private
    G-comb : ∀ h → G h ≈s comb dirs (tabulate h)
    G-comb = lin-ext G (λ h → comb dirs (tabulate h)) G-lin (comb-lin dirs) at
      where
      at : ∀ i → G (unit i) ≈s comb dirs (tabulate (unit i))
      at zero                   j = sym (comb-unit dirs zero j)
      at (suc zero)             j = sym (comb-unit dirs (suc zero) j)
      at (suc (suc zero))       j = sym (comb-unit dirs (suc (suc zero)) j)
      at (suc (suc (suc zero))) j = sym (comb-unit dirs (suc (suc (suc zero))) j)

  F-span : ∀ h → InSpan frameP (F h)
  F-span h = span-++ˡ {xs = F zeros ∷ dirs} E4 ((true ∷ tabulate h) , λ i →
    trans (cong (F zeros i xor_) (sym (G-comb h i)))
      (trans (cong (F zeros i xor_) (xor-comm (F h i) (F zeros i)))
      (trans (sym (xor-assoc (F zeros i) (F zeros i) (F h i)))
        (cong (_xor F h i) (xor-same (F zeros i))))))
