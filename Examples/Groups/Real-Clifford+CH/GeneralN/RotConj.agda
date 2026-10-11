------------------------------------------------------------------------
-- Presentations of groups
--
-- A rotation conjugated by a rotation on one of its controls (Clément,
-- Lemma 8.5, the instance of rules (43) and (44))
--
-- At width 5 + k, with R β the rotation on wire 0 controlled by the
-- wires 1 … (RotCol) and Y β the rotation on wire 1 controlled by the
-- wires 2 …, wire 0 idle, the rotation Y of either sign turns the
-- colour of R's control on wire 1 over:
--
--   Y true  • R β • Y false ≈ X₁ • R β • X₁      (`l85′`)
--   Y false • R β • Y true  ≈ X₁ • R β • X₁      (`l85`)
--
-- The paper's proof (Appendix E.3).  Over every colouring of its
-- controls the rotation Y true merges to ZX = X • Z on wire 1
-- (RotMerge), and ZX carries R to its white copy, since Z on a control
-- passes R ((19) under the swap and a two-wire fact).  Every colouring
-- but the black one is separated from R, and from its white copy, on a
-- wire off both targets, so passes them ((351)/(352), RotAnywhere).
-- So the black factor Y true alone carries R to its white copy (the
-- D-trick, MergeGen.pass-last′).  For the other sign, Y false is Y true
-- times Q = Y false • Y false, and Q passes R: by (354) twice and (355)
-- it is X B X • B, with B the box on wire 1, and both halves invert R
-- (Canon31.K1).  (The product of the XZ-rotations would give `l85`
-- directly, but its last step needs Z° = X Z X to pass R.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.RotConj
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Nat using (ℕ ; s≤s ; z≤n)
open import Data.Product using (Σ ; _,_)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module S ; X² ; X²↑ ; Z² ; Ex² ; S-Z↓ ; S-X↑)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Auxiliary using (CH-Z↑)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs² ; σAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt ; placeAt-place ; placeAt-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceCalc using (placeAt-zero)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃ using (box-Z₀)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX355 complete₂ complete₃ using (eq355)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX354 complete₂ complete₃ using (eq354₁ ; eq354₁′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon31 complete₂ complete₃ using (K1)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotAnywhere complete₂ complete₃ using (rot-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotMerge complete₂ complete₃ using (merge-rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.MergeGen using (pass-last′ ; ∏-↑)
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol

private
  -- A white bit of a colouring that is not all black.
  white : ∀ {n} (c : Bits n) → c ≢ replicate n true → Σ (Fin n) (λ j → lookupℕ (toℕ j) c ≡ false)
  white []          ne = ⊥-elim (ne Eq.refl)
  white (false ∷ c) ne = 0F , Eq.refl
  white (true ∷ c)  ne with white c (λ e → ne (Eq.cong (true ∷_) e))
  ... | j , e = sF j , e

  lk-ones : ∀ {n} (j : Fin n) → lookupℕ (toℕ j) (replicate n true) ≡ true
  lk-ones 0F     = Eq.refl
  lk-ones (sF j) = lk-ones j

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    module I = Invol (canonN k completes) complete₂

  open Tools (N VRel,_===_)

  -- The rotations: R β on wire 0, Y β on wire 1 with wire 0 idle.
  R Y : Bool → Circuit N
  R β = rot β
  Y β = rot {₁₊ k} β ↑

  private
    X₁ Z₁ Λ B : Circuit N
    X₁ = X ↑
    Z₁ = Z ↑
    Λ  = Λ□ (₄₊ k)
    B  = Ex ↓ • Λ • Ex ↓

    ones : Bits (₃₊ k)
    ones = replicate (₃₊ k) true

    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    pass₂ : ∀ {y a b : Circuit N} → y • a ≈ a • y → y • b ≈ b • y → y • (a • b) ≈ (a • b) • y
    pass₂ pa pb = trans (sym assoc) (trans (front _ pa) (trans assoc (trans (back _ pb) (sym assoc))))

    -- The rotation on wire 1 with wire 0 as a control.
    Rb : Bool → Circuit N
    Rb β = Ex • R β • Ex

    Z₁² : Z₁ • Z₁ ≈ ε
    Z₁² = lemma-cong↑ _ _ Z²

    ----------------------------------------------------------------------
    -- Z on wire 1 passes the rotation

    Z₁-B : Z₁ • B ≈ B • Z₁
    Z₁-B = S.⟪⟫-≈ (box-Z₀ (₂₊ k)) (S.⟪⟫-•₂ S-Z↓ refl) (S.⟪⟫-•₂ refl S-Z↓)

    Z₁-CH : Z₁ • CH ≈ CH • Z₁
    Z₁-CH = sym CH-Z↑

    Z₁-R : ∀ β → Z₁ • R β ≈ R β • Z₁
    Z₁-R true  = pass₂ Z₁-CH (pass₂ Z₁-B (pass₂ Z₁-CH Z₁-B))
    Z₁-R false = pass₂ Z₁-B (pass₂ Z₁-CH (pass₂ Z₁-B Z₁-CH))

    ----------------------------------------------------------------------
    -- Y as the product of its two colourings on wire 0 ((354))

    -- The idle wire 1 of a placement is wire 0 under the swap.
    Y-place : ∀ β → Y β ≈ Ex • placeAt 1 (rot {₁₊ k} β) • Ex
    Y-place β = sym (conj-sym Ex² (sym (trans (placeAt-step 0 u (s≤s z≤n)) (back _ (front _ (placeAt-zero u))))))
      where
      u : Circuit (₄₊ k)
      u = rot {₁₊ k} β

    Yeq : ∀ β → Y β ≈ (X • Rb β • X) • Rb β
    Yeq β = trans (Y-place β)
                  (trans (S.⟪⟫-cong (trans (≡→≈ (placeAt-place 1 (rot {₁₊ k} β))) (sym (eq354₁ k below β))))
                         (S.⟪⟫-•₂ (S.⟪⟫-•₃ S-X↑ refl S-X↑) refl))

    Yeq′ : ∀ β → Y β ≈ Rb β • (X • Rb β • X)
    Yeq′ β = trans (Y-place β)
                   (trans (S.⟪⟫-cong (trans (≡→≈ (placeAt-place 1 (rot {₁₊ k} β))) (sym (eq354₁′ k below β))))
                          (S.⟪⟫-•₂ refl (S.⟪⟫-•₃ S-X↑ refl S-X↑)))

    ----------------------------------------------------------------------
    -- The two signs of Y are inverse ((317) at the full width)

    Rtf : Rb true • Rb false ≈ ε
    Rtf = trans (sym (S.⟪⟫-• _ _)) (trans (S.⟪⟫-cong I.zx-xz) S.⟪⟫-ε)

    Rft : Rb false • Rb true ≈ ε
    Rft = trans (sym (S.⟪⟫-• _ _)) (trans (S.⟪⟫-cong I.xz-zx) S.⟪⟫-ε)

    xconj : ∀ {u v : Circuit N} → u • v ≈ ε → (X • u • X) • (X • v • X) ≈ ε
    xconj {u} {v} e = begin
      (X • u • X) • (X • v • X)     ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      X • u • (X • X) • v • X       ≈⟨ back _ (back _ (trans (front _ X²) left-unit)) ⟩
      X • u • v • X                 ≈⟨ back _ (trans (sym assoc) (trans (front _ e) left-unit)) ⟩
      X • X                         ≈⟨ X² ⟩
      ε ∎

    inv-pair : ∀ {a b a′ b′ : Circuit N} → a • b ≈ ε → (b′ • (X • a • X)) • ((X • b • X) • a′) ≈ b′ • a′
    inv-pair {a} {b} {a′} {b′} e = begin
      (b′ • (X • a • X)) • ((X • b • X) • a′)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
      b′ • ((X • a • X) • (X • b • X)) • a′     ≈⟨ back _ (trans (front _ (xconj e)) left-unit) ⟩
      b′ • a′ ∎

    Y-inv : Y true • Y false ≈ ε
    Y-inv = trans (cong (Yeq′ true) (Yeq false)) (trans (inv-pair Rtf) Rtf)

    Y-inv′ : Y false • Y true ≈ ε
    Y-inv′ = trans (cong (Yeq′ false) (Yeq true)) (trans (inv-pair Rft) Rft)

    ----------------------------------------------------------------------
    -- Y true over every colouring of its controls is ZX on wire 1

    g : Bits (₃₊ k) → Circuit N
    g c = col (true ∷ true ∷ c) (Y true)

    G : Circuit N
    G = ∏ (allBits (₃₊ k)) g

    G-ZX : G ≈ X₁ • Z₁
    G-ZX = trans (≡→≈ (∏-↑ (allBits (₃₊ k)) (λ c → col (true ∷ c) (rot {₁₊ k} true))))
                 (lemma-cong↑ _ _ (merge-rot k below true))

    -- ZX on wire 1 carries R to its white copy.
    G-R : ∀ β → G • R β ≈ (X₁ • R β • X₁) • G
    G-R β = begin
      G • R β                          ≈⟨ front _ G-ZX ⟩
      (X₁ • Z₁) • R β                  ≈⟨ trans assoc (back _ (Z₁-R β)) ⟩
      X₁ • (R β • Z₁)                  ≈⟨ back _ (back _ (sym (trans (front _ X²↑) left-unit))) ⟩
      X₁ • (R β • ((X₁ • X₁) • Z₁))    ≈⟨ by-passoc (□ • (□ • ((□ • □) • □))) ((□ • □ • □) • (□ • □)) Eq.refl ⟩
      (X₁ • R β • X₁) • (X₁ • Z₁)      ≈⟨ back _ (sym G-ZX) ⟩
      (X₁ • R β • X₁) • G ∎

    ----------------------------------------------------------------------
    -- Every colouring but the black one passes R and its white copy

    -- The colourings, and R as a placement.
    colX : ∀ (W : Bits (₄₊ k)) (w : Circuit N) → col (true ∷ W) (X • w • X) ≈ col (false ∷ W) w
    colX W w = begin
      m • (X • w • X) • m          ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (m • X) • w • (X • m)        ≈⟨ front _ (sym (X-↑ (negsB W))) ⟩
      (X • m) • w • (X • m) ∎
      where
      m : Circuit N
      m = negsB W ↑

    col-• : ∀ (s : Bits N) a b → col s (a • b) ≈ col s a • col s b
    col-• s a b = sym (begin
      (negsB s • a • negsB s) • (negsB s • b • negsB s)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
      negsB s • a • ((negsB s • negsB s) • b • negsB s)
        ≈⟨ back _ (back _ (trans (front _ (negs² s)) left-unit)) ⟩
      negsB s • a • (b • negsB s)
        ≈⟨ back _ (sym assoc) ⟩
      negsB s • (a • b) • negsB s ∎)

    col-cong : ∀ (s : Bits N) {a b : Circuit N} → a ≈ b → col s a ≈ col s b
    col-cong s e = back _ (front _ e)

    -- The factor g c as two placed rotations on wire 1.
    split : ∀ c → g c ≈ place (σAt 0) (false ∷ true ∷ c) (rot true) • place (σAt 0) (true ∷ true ∷ c) (rot true)
    split c = trans (col-cong (true ∷ true ∷ c) (Yeq true))
                    (trans (col-• (true ∷ true ∷ c) _ _) (front _ (colX (true ∷ c) (Rb true))))

    -- R and its white copy as placements.
    ones₅ wh : Bits N
    ones₅ = replicate N true
    wh    = true ∷ false ∷ ones

    P-ones : ∀ β → R β ≈ place ε ones₅ (rot β)
    P-ones β = sym (trans (≡→≈ (Eq.cong (λ z → z • (ε • rot β • ε) • z) (allT N)))
                          (trans left-unit (trans right-unit (trans left-unit right-unit))))

    P-X₁ : ∀ β → X₁ • R β • X₁ ≈ place ε wh (rot β)
    P-X₁ β = sym (trans (≡→≈ (Eq.cong (λ z → (X • z ↑) ↑ • (ε • rot β • ε) • (X • z ↑) ↑) (allT (₃₊ k))))
                        (cong right-unit (cong (trans left-unit right-unit) right-unit)))

    tf : true ≢ false
    tf ()

    -- A rotation on wire 0 coloured s passes one on wire 1 coloured
    -- γ ∷ true ∷ c when c has a white bit where s is black ((351)/(352)).
    rc : ∀ α β (s : Bits N) γ c (j : Fin (₃₊ k)) → lookupℕ 0 s ≡ true →
         lookupℕ (toℕ j) c ≡ false → lookupℕ (toℕ (sF (sF j))) s ≡ true →
         place ε s (rot β) • place (σAt 0) (γ ∷ true ∷ c) (rot α) ≈
         place (σAt 0) (γ ∷ true ∷ c) (rot α) • place ε s (rot β)
    rc α β s γ c j s0 cj sj =
      rot-comm k below β α ε (σAt 0) 0F (sF 0F) Eq.refl Eq.refl s (γ ∷ true ∷ c) s0 Eq.refl
               (sF (sF j)) (λ ()) (λ ()) (λ e → tf (Eq.trans (Eq.sym sj) (Eq.trans e cj)))

    pass-g : ∀ (s : Bits N) β → lookupℕ 0 s ≡ true →
             (∀ (j : Fin (₃₊ k)) → lookupℕ (toℕ (sF (sF j))) s ≡ true) →
             ∀ c → c ≢ replicate (₃₊ k) true → place ε s (rot β) • g c ≈ g c • place ε s (rot β)
    pass-g s β s0 hi c ne with white c ne
    ... | j , cj = trans (back _ (split c))
                         (trans (pass₂ (rc true β s false c j s0 cj (hi j)) (rc true β s true c j s0 cj (hi j)))
                                (front _ (sym (split c))))

    via-l : ∀ {y y′ a : Circuit N} → y ≈ y′ → y′ • a ≈ a • y′ → y • a ≈ a • y
    via-l e p = trans (front _ e) (trans p (back _ (sym e)))

    R-g : ∀ β c → c ≢ replicate (₃₊ k) true → R β • g c ≈ g c • R β
    R-g β c ne = via-l (P-ones β) (pass-g ones₅ β Eq.refl (λ j → lk-ones j) c ne)

    xR-g : ∀ β c → c ≢ replicate (₃₊ k) true → (X₁ • R β • X₁) • g c ≈ g c • (X₁ • R β • X₁)
    xR-g β c ne = via-l (P-X₁ β) (pass-g wh β Eq.refl (λ j → lk-ones j) c ne)

    -- The black factor is Y true, whose inverse is Y false.
    g-ones : g (replicate (₃₊ k) true) • Y false ≈ ε
    g-ones = trans (≡→≈ (Eq.cong (λ z → (z • Y true • z) • Y false) (allT N)))
                   (trans (front _ (trans left-unit right-unit)) Y-inv)

    ----------------------------------------------------------------------
    -- The D-trick

    D : Circuit N
    D = G • Y false

    R-D : ∀ β → R β • D ≈ D • R β
    R-D β = pass-last′ (₃₊ k) g (R-g β) g-ones

    xR-D : ∀ β → (X₁ • R β • X₁) • D ≈ D • (X₁ • R β • X₁)
    xR-D β = pass-last′ (₃₊ k) g (xR-g β) g-ones

    G≈DY : G ≈ D • Y true
    G≈DY = sym (trans assoc (trans (back _ Y-inv′) right-unit))

    ZX-inv : (Z₁ • X₁) • G ≈ ε
    ZX-inv = trans (back _ G-ZX)
                   (trans (by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl)
                          (trans (back _ (trans (front _ X²↑) left-unit)) Z₁²))

    Dinv-D : (Y true • (Z₁ • X₁)) • D ≈ ε
    Dinv-D = trans (by-passoc ((□ • (□ • □)) • (□ • □)) (□ • ((□ • □) • □) • □) Eq.refl)
                   (trans (back _ (trans (front _ ZX-inv) left-unit)) Y-inv)

    cancelL : ∀ {a b : Circuit N} → D • a ≈ D • b → a ≈ b
    cancelL {a} {b} e =
      trans (sym (trans (front _ Dinv-D) left-unit))
            (trans assoc (trans (back _ e) (trans (sym assoc) (trans (front _ Dinv-D) left-unit))))

    stepA : ∀ β → D • (Y true • R β) ≈ D • ((X₁ • R β • X₁) • Y true)
    stepA β = begin
      D • (Y true • R β)               ≈⟨ sym assoc ⟩
      (D • Y true) • R β               ≈⟨ front _ (sym G≈DY) ⟩
      G • R β                          ≈⟨ G-R β ⟩
      (X₁ • R β • X₁) • G              ≈⟨ back _ G≈DY ⟩
      (X₁ • R β • X₁) • (D • Y true)   ≈⟨ sym assoc ⟩
      ((X₁ • R β • X₁) • D) • Y true   ≈⟨ front _ (xR-D β) ⟩
      (D • (X₁ • R β • X₁)) • Y true   ≈⟨ assoc ⟩
      D • ((X₁ • R β • X₁) • Y true) ∎

  ----------------------------------------------------------------------
  -- Lemma 8.5 at the canonical position, Y true first

  l85′ : ∀ β → Y true • R β • Y false ≈ X ↑ • R β • X ↑
  l85′ β = begin
    Y true • R β • Y false                ≈⟨ sym assoc ⟩
    (Y true • R β) • Y false              ≈⟨ front _ (cancelL (stepA β)) ⟩
    ((X₁ • R β • X₁) • Y true) • Y false  ≈⟨ trans assoc (trans (back _ Y-inv) right-unit) ⟩
    X₁ • R β • X₁ ∎

  private
    ----------------------------------------------------------------------
    -- Q = Y false • Y false passes R

    Q Qi : Circuit N
    Q  = Y false • Y false
    Qi = Y true • Y true

    Bf : Rb false • Rb false ≈ B
    Bf = trans (sym (S.⟪⟫-• (R false) (R false))) (S.⟪⟫-cong (sym (eq355 k below)))

    ab-ba : (X • Rb false • X) • Rb false ≈ Rb false • (X • Rb false • X)
    ab-ba = trans (sym (Yeq false)) (Yeq′ false)

    aa : (X • Rb false • X) • (X • Rb false • X) ≈ X • B • X
    aa = begin
      (X • Rb false • X) • (X • Rb false • X)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      X • Rb false • (X • X) • Rb false • X
        ≈⟨ back _ (back _ (trans (front _ X²) left-unit)) ⟩
      X • Rb false • Rb false • X
        ≈⟨ back _ (trans (sym assoc) (front _ Bf)) ⟩
      X • B • X ∎

    Q-form : Q ≈ (X • B • X) • B
    Q-form = begin
      Y false • Y false
        ≈⟨ cong (Yeq false) (Yeq false) ⟩
      ((X • Rb false • X) • Rb false) • ((X • Rb false • X) • Rb false)
        ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
      (X • Rb false • X) • (Rb false • (X • Rb false • X)) • Rb false
        ≈⟨ back _ (front _ (sym ab-ba)) ⟩
      (X • Rb false • X) • ((X • Rb false • X) • Rb false) • Rb false
        ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
      ((X • Rb false • X) • (X • Rb false • X)) • (Rb false • Rb false)
        ≈⟨ cong aa Bf ⟩
      (X • B • X) • B ∎

    -- Both halves invert R (Canon31.K1, black and white on wire 0).
    Kb : ∀ β → R β • B ≈ B • R (not β)
    Kb β = trans (back _ (sym eb)) (trans (K1 k below β true true) (front _ eb))
      where
      eb : col (true ∷ true ∷ ones) B ≈ B
      eb = trans (≡→≈ (Eq.cong (λ z → z • B • z) (allT N))) (trans left-unit right-unit)

    Kw : ∀ β → R β • (X • B • X) ≈ (X • B • X) • R (not β)
    Kw β = trans (back _ (sym ew)) (trans (K1 k below β false true) (front _ ew))
      where
      ew : col (false ∷ true ∷ ones) B ≈ X • B • X
      ew = trans (≡→≈ (Eq.cong (λ z → (X • z ↑) • B • (X • z ↑)) (allT (₄₊ k))))
                 (cong right-unit (back _ right-unit))

    pq : ∀ β → R β • ((X • B • X) • B) ≈ ((X • B • X) • B) • R (not (not β))
    pq β = trans (sym assoc) (trans (front _ (Kw β)) (trans assoc (trans (back _ (Kb (not β))) (sym assoc))))

    Q-R : ∀ β → Q • R β ≈ R β • Q
    Q-R true  = sym (trans (back _ Q-form) (trans (pq true) (front _ (sym Q-form))))
    Q-R false = sym (trans (back _ Q-form) (trans (pq false) (front _ (sym Q-form))))

    Yf≈ : Y false ≈ Y true • Q
    Yf≈ = sym (trans (sym assoc) (trans (front _ Y-inv) left-unit))

    Yt≈ : Y true ≈ Qi • Y false
    Yt≈ = sym (trans assoc (trans (back _ Y-inv) right-unit))

    Q-Qi : Q • Qi ≈ ε
    Q-Qi = trans (by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl)
                 (trans (back _ (trans (front _ Y-inv′) left-unit)) Y-inv′)

  ----------------------------------------------------------------------
  -- Lemma 8.5 at the canonical position, Y false first

  l85 : ∀ β → Y false • R β • Y true ≈ X ↑ • R β • X ↑
  l85 β = begin
    Y false • R β • Y true                  ≈⟨ cong Yf≈ (back _ Yt≈) ⟩
    (Y true • Q) • R β • (Qi • Y false)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □) • □ • □) Eq.refl ⟩
    Y true • (Q • R β) • Qi • Y false       ≈⟨ back _ (front _ (Q-R β)) ⟩
    Y true • (R β • Q) • Qi • Y false       ≈⟨ by-passoc (□ • (□ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
    Y true • R β • (Q • Qi) • Y false       ≈⟨ back _ (back _ (trans (front _ Q-Qi) left-unit)) ⟩
    Y true • R β • Y false                  ≈⟨ l85′ β ⟩
    X ↑ • R β • X ↑ ∎
