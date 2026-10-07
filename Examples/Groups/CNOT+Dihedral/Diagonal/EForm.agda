------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical forms of the wire-0 part of a diagonal circuit
--
-- On ₁₊ m wires, the part of a phase polynomial involving x₀ is
--
--     x₀ (a + 2 Σⱼ βⱼ xⱼ + 4 Σⱼ<ₖ γⱼₖ xⱼ xₖ),   a ∈ ℤ₈, βⱼ ∈ ℤ₄, γⱼₖ ∈ ℤ₂,
--
-- and its canonical circuit is T ^ a • F β γ, where F is built one
-- wire at a time: CS ^ β₁ on wires (0, 1), the rest one wire up with
-- wire 0 swapped past wire 1, and the CCZs on (0, 1, k) (C3B).  The
-- controlled phases C₂ ℓ and C₃ ℓ of Diagonal.Split are such forms
-- (C₂≈F, C₃≈C3B), and the forms add (F-•).  Every circuit here is
-- diagonal — equal to a diagonal expression (Diag) — so any two of
-- them commute (diag-comm), which is all the rearranging needs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Diagonal.EForm where

open import Data.Bool using (Bool ; true ; false ; _xor_)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sucF)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _*_ ; _%_)
open import Data.Nat.DivMod using (_mod_ ; m%n<n)
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (Vec ; [] ; _∷_ ; replicate ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Reasoning
open import Examples.Groups.CNOT+Dihedral.Powers
open import Examples.Groups.CNOT+Dihedral.Linear.Base using (NZ ; e₀ ; cx ; sw ; vec ; swap ; _↥ₗ)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Calculus
open import Examples.Groups.CNOT+Dihedral.Diagonal.Gates
open import Examples.Groups.CNOT+Dihedral.Diagonal.Split

private
  variable
    n m k : ℕ

------------------------------------------------------------------------
-- Diagonal circuits commute

Diag : (m : ℕ) → Circuit m → Set
Diag m w = Σ (DE m) (λ d → m ⊢ w ≈ ⟦ d ⟧ᴰ)

⟦⟧ₑ-comm : (e e' : ℕ × PE m) → m ⊢ ⟦ e ⟧ₑ • ⟦ e' ⟧ₑ ≈ ⟦ e' ⟧ₑ • ⟦ e ⟧ₑ
⟦⟧ₑ-comm {m} (s , pe) (t , qe) = begin
  (ω ^ s • prod pe) • ω ^ t • prod qe
    ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  ω ^ s • (prod pe • ω ^ t) • prod qe
    ≈⟨ back _ (front _ (sym (ωᵏ-comm t (prod pe)))) ⟩
  ω ^ s • (ω ^ t • prod pe) • prod qe
    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (ω ^ s • ω ^ t) • prod pe • prod qe
    ≈⟨ cong (Pow.pow-comm₂ m s t refl) (prod-comm pe qe) ⟩
  (ω ^ t • ω ^ s) • prod qe • prod pe
    ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  ω ^ t • (ω ^ s • prod qe) • prod pe
    ≈⟨ back _ (front _ (ωᵏ-comm s (prod qe))) ⟩
  ω ^ t • (prod qe • ω ^ s) • prod pe
    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (ω ^ t • prod qe) • ω ^ s • prod pe ∎
  where open Width m

diag-comm : ∀ {a b : Circuit m} → Diag m a → Diag m b → m ⊢ a • b ≈ b • a
diag-comm {m} {a} {b} (d , p) (d' , q) = begin
  a • b                        ≈⟨ cong (trans p (D-sound d)) (trans q (D-sound d')) ⟩
  ⟦ toPE d ⟧ₑ • ⟦ toPE d' ⟧ₑ   ≈⟨ ⟦⟧ₑ-comm (toPE d) (toPE d') ⟩
  ⟦ toPE d' ⟧ₑ • ⟦ toPE d ⟧ₑ   ≈⟨ sym (cong (trans q (D-sound d')) (trans p (D-sound d))) ⟩
  b • a                        ∎
  where open Width m

------------------------------------------------------------------------
-- The data and the forms

Tri : ℕ → Set
Tri zero    = ⊤
Tri (suc k) = Vec Bool k × Tri k

tri0 : (k : ℕ) → Tri k
tri0 zero    = tt
tri0 (suc k) = replicate k false , tri0 k

cz : Bool → Circuit (₃₊ n)
cz true  = CCZ
cz false = ε

C3B : Vec Bool m → Circuit (₂₊ m)
C3B []       = ε
C3B (c ∷ cs) = cz c • πL • C3B cs ↑ • πR

F : Vec (Fin 4) k → Tri k → Circuit (₁₊ k)
F []       tt       = ε
F (b ∷ bs) (c , cs) = CS ^ toℕ b • (SWAP • F bs cs ↑ • SWAP) • C3B c

------------------------------------------------------------------------
-- They are diagonal

private
  π-form : ∀ {X : Circuit (₂₊ n)} (d : DE (₂₊ n)) → (₂₊ n) ⊢ X ≈ ⟦ d ⟧ᴰ →
           (₃₊ n) ⊢ πL • X ↑ • πR ≈ ⟦ `c (swap ↥ₗ) (`c swap (d `↑)) ⟧ᴰ
  π-form {n} d e = trans (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl)
                   (back _ (front _ (back _ (front _ (lift e)))))
    where open Width (₃₊ n)

cz-diag : (c : Bool) → Diag (₃₊ n) (cz c)
cz-diag {n} true  = dCCZ , Width.refl
cz-diag {n} false = `ε , Width.refl

C3B-diag : (cs : Vec Bool m) → Diag (₂₊ m) (C3B cs)
C3B-diag {m} [] = `ε , Width.refl
C3B-diag {m} (c ∷ cs) =
  proj₁ (cz-diag c) `• `c (swap ↥ₗ) (`c swap (proj₁ (C3B-diag cs) `↑)) ,
  Width.cong (proj₂ (cz-diag c)) (π-form (proj₁ (C3B-diag cs)) (proj₂ (C3B-diag cs)))

F-diag : (bs : Vec (Fin 4) k) (cs : Tri k) → Diag (₁₊ k) (F bs cs)
F-diag {k} [] tt = `ε , Width.refl
F-diag {suc k} (b ∷ bs) (c , cs) =
  dCS `^ toℕ b `• `c swap (proj₁ (F-diag bs cs) `↑) `• proj₁ (C3B-diag c) ,
  Width.cong (Width.refl)
    (Width.cong (Width.back (₂₊ k) SWAP (Width.front (₂₊ k) SWAP (lift (proj₂ (F-diag bs cs)))))
                (proj₂ (C3B-diag c)))

------------------------------------------------------------------------
-- The zero forms

private
  πLR : (₃₊ n) ⊢ πL • πR ≈ ε
  πLR {n} = begin
    (SWAP ↑ • SWAP) • SWAP • SWAP ↑     ≈⟨ by-assoc Eq.refl ⟩
    SWAP ↑ • (SWAP • SWAP) • SWAP ↑     ≈⟨ back _ (front _ (ax swap-order)) ⟩
    SWAP ↑ • ε • SWAP ↑                 ≈⟨ back _ left-unit ⟩
    SWAP ↑ • SWAP ↑                     ≈⟨ lift (ax swap-order) ⟩
    ε                                   ∎
    where open Width (₃₊ n)

  πRL : (₃₊ n) ⊢ πR • πL ≈ ε
  πRL {n} = begin
    (SWAP • SWAP ↑) • SWAP ↑ • SWAP     ≈⟨ by-assoc Eq.refl ⟩
    SWAP • (SWAP ↑ • SWAP ↑) • SWAP     ≈⟨ back _ (front _ (lift (ax swap-order))) ⟩
    SWAP • ε • SWAP                     ≈⟨ back _ left-unit ⟩
    SWAP • SWAP                         ≈⟨ ax swap-order ⟩
    ε                                   ∎
    where open Width (₃₊ n)

  -- πL • X ↑ • πR with X ≈ ε.
  π-ε : ∀ {X : Circuit (₂₊ n)} → (₂₊ n) ⊢ X ≈ ε → (₃₊ n) ⊢ πL • X ↑ • πR ≈ ε
  π-ε {n} e = trans (back _ (trans (front _ (lift e)) left-unit)) πLR
    where open Width (₃₊ n)

  -- SWAP • X ↑ • SWAP with X ≈ ε.
  S-ε : ∀ {X : Circuit (₁₊ n)} → (₁₊ n) ⊢ X ≈ ε → (₂₊ n) ⊢ SWAP • X ↑ • SWAP ≈ ε
  S-ε {n} e = trans (back _ (trans (front _ (lift e)) left-unit)) (ax swap-order)
    where open Width (₂₊ n)

C3B-zero : (m : ℕ) → (₂₊ m) ⊢ C3B (replicate m false) ≈ ε
C3B-zero zero    = Width.refl
C3B-zero (suc m) = Width.trans Width.left-unit (π-ε (C3B-zero m))

F-zero : (k : ℕ) → (₁₊ k) ⊢ F (replicate k 0F) (tri0 k) ≈ ε
F-zero zero    = Width.refl
F-zero (suc k) = begin
  ε • (SWAP • F (replicate k 0F) (tri0 k) ↑ • SWAP) • C3B (replicate k false)
    ≈⟨ left-unit ⟩
  (SWAP • F (replicate k 0F) (tri0 k) ↑ • SWAP) • C3B (replicate k false)
    ≈⟨ cong (S-ε (F-zero k)) (C3B-zero k) ⟩
  ε • ε
    ≈⟨ left-unit ⟩
  ε ∎
  where open Width (₂₊ k)

------------------------------------------------------------------------
-- The controlled phases as forms

bvec : NZ k → Vec (Fin 4) k
bvec {suc k} e₀ = sucF 0F ∷ replicate k 0F
bvec (cx ℓ)     = sucF 0F ∷ bvec ℓ
bvec (sw ℓ)     = 0F ∷ bvec ℓ

cvec : NZ k → Tri k
cvec {suc k} e₀     = replicate k false , tri0 k
cvec {suc k} (cx ℓ) = vec ℓ , cvec ℓ
cvec {suc k} (sw ℓ) = replicate k false , cvec ℓ

C₃≈C3B : (ℓ : NZ (₁₊ k)) → (₃₊ k) ⊢ C₃ ℓ ≈ C3B (vec ℓ)
C₃≈C3B {k} e₀ = begin
  C₃ e₀                                       ≈⟨ C₃-e₀ ⟩
  CCZ                                         ≈⟨ sym right-unit ⟩
  CCZ • ε                                     ≈⟨ back CCZ (sym (π-ε (C3B-zero k))) ⟩
  CCZ • πL • C3B (replicate k false) ↑ • πR   ∎
  where open Width (₃₊ k)
C₃≈C3B {suc k} (sw ℓ) = begin
  C₃ (sw ℓ)                       ≈⟨ C₃-sw ℓ ⟩
  πL • (C₃ ℓ) ↑ • πR              ≈⟨ back _ (front _ (lift (C₃≈C3B ℓ))) ⟩
  πL • C3B (vec ℓ) ↑ • πR         ≈⟨ sym left-unit ⟩
  ε • πL • C3B (vec ℓ) ↑ • πR     ∎
  where open Width (₄₊ k)
C₃≈C3B {suc k} (cx ℓ) = begin
  C₃ (cx ℓ)                       ≈⟨ C₃-cx ℓ ⟩
  CCZ • πL • (C₃ ℓ) ↑ • πR        ≈⟨ back _ (back _ (front _ (lift (C₃≈C3B ℓ)))) ⟩
  CCZ • πL • C3B (vec ℓ) ↑ • πR   ∎
  where open Width (₄₊ k)

C₂≈F : (ℓ : NZ (₁₊ k)) → (₂₊ k) ⊢ C₂ ℓ ≈ F (bvec ℓ) (cvec ℓ)
C₂≈F {k} e₀ = begin
  C₂ e₀
    ≈⟨ C₂-e₀ ⟩
  CS
    ≈⟨ sym (trans (back CS (cong (S-ε (F-zero k)) (C3B-zero k))) (trans (back CS left-unit) right-unit)) ⟩
  CS • (SWAP • F (replicate k 0F) (tri0 k) ↑ • SWAP) • C3B (replicate k false) ∎
  where open Width (₂₊ k)
C₂≈F {suc k} (sw ℓ) = begin
  C₂ (sw ℓ)
    ≈⟨ C₂-sw ℓ ⟩
  SWAP • (C₂ ℓ) ↑ • SWAP
    ≈⟨ back _ (front _ (lift (C₂≈F ℓ))) ⟩
  SWAP • F (bvec ℓ) (cvec ℓ) ↑ • SWAP
    ≈⟨ sym (trans left-unit (trans (back _ (C3B-zero (suc k))) right-unit)) ⟩
  ε • (SWAP • F (bvec ℓ) (cvec ℓ) ↑ • SWAP) • C3B (replicate (suc k) false) ∎
  where open Width (₃₊ k)
C₂≈F {suc k} (cx ℓ) = begin
  C₂ (cx ℓ)
    ≈⟨ C₂-cx ℓ ⟩
  CS • (SWAP • (C₂ ℓ) ↑ • SWAP) • C₃ ℓ
    ≈⟨ back CS (cong (back _ (front _ (lift (C₂≈F ℓ)))) (C₃≈C3B ℓ)) ⟩
  CS • (SWAP • F (bvec ℓ) (cvec ℓ) ↑ • SWAP) • C3B (vec ℓ) ∎
  where open Width (₃₊ k)

------------------------------------------------------------------------
-- Adding forms

infixl 6 _+₄_
_+₄_ : Fin 4 → Fin 4 → Fin 4
a +₄ b = (toℕ a + toℕ b) mod 4

triXor : Tri k → Tri k → Tri k
triXor {zero}  tt       tt         = tt
triXor {suc k} (c , cs) (c' , cs') = zipWith _xor_ c c' , triXor cs cs'

CS-+ : (a b : Fin 4) → (₂₊ n) ⊢ CS ^ toℕ a • CS ^ toℕ b ≈ CS ^ toℕ (a +₄ b)
CS-+ {n} a b = begin
  CS ^ toℕ a • CS ^ toℕ b           ≈⟨ sym (Pow.pow-+ (₂₊ n) CS (toℕ a) (toℕ b)) ⟩
  CS ^ (toℕ a + toℕ b)              ≈⟨ Pow.pow-mod-by (₂₊ n) CS 4 CS⁴ (toℕ a + toℕ b) ⟩
  CS ^ ((toℕ a + toℕ b) % 4)        ≈⟨ refl' (Eq.cong (CS ^_) (Eq.sym (toℕ-fromℕ< (m%n<n (toℕ a + toℕ b) 4)))) ⟩
  CS ^ toℕ (a +₄ b)                 ∎
  where open Width (₂₊ n)

cz-xor : (c c' : Bool) → (₃₊ n) ⊢ cz c • cz c' ≈ cz (c xor c')
cz-xor {n} true  true  = CCZ²
cz-xor {n} true  false = Width.right-unit
cz-xor {n} false c'    = Width.left-unit

C3B-• : (cs cs' : Vec Bool m) → (₂₊ m) ⊢ C3B cs • C3B cs' ≈ C3B (zipWith _xor_ cs cs')
C3B-• {m} [] [] = left-unit
  where open Width (₂₊ m)
C3B-• {suc m} (c ∷ cs) (c' ∷ cs') = begin
  (cz c • πL • G₁ ↑ • πR) • cz c' • πL • G₂ ↑ • πR
    ≈⟨ by-passoc ((□ • □ • □ • □) • □ • □ • □ • □) (□ • (□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
  cz c • (πL • G₁ ↑ • πR) • cz c' • (πL • G₂ ↑ • πR)
    ≈⟨ back _ (trans (sym assoc) (trans (front _ (diag-comm πX (cz-diag c'))) assoc)) ⟩
  cz c • cz c' • (πL • G₁ ↑ • πR) • (πL • G₂ ↑ • πR)
    ≈⟨ by-passoc (□ • □ • (□ • □ • □) • (□ • □ • □)) ((□ • □) • □ • □ • (□ • □) • □ • □) Eq.refl ⟩
  (cz c • cz c') • πL • G₁ ↑ • (πR • πL) • G₂ ↑ • πR
    ≈⟨ back _ (back _ (back _ (trans (front _ πRL) left-unit))) ⟩
  (cz c • cz c') • πL • G₁ ↑ • G₂ ↑ • πR
    ≈⟨ cong (cz-xor c c') (back _ (trans (sym assoc) (front _ (lift (C3B-• cs cs'))))) ⟩
  cz (c xor c') • πL • C3B (zipWith _xor_ cs cs') ↑ • πR ∎
  where
  open Width (₃₊ m)
  G₁ = C3B cs
  G₂ = C3B cs'
  πX : Diag (₃₊ m) (πL • G₁ ↑ • πR)
  πX = `c (swap ↥ₗ) (`c swap (proj₁ (C3B-diag cs) `↑)) , π-form (proj₁ (C3B-diag cs)) (proj₂ (C3B-diag cs))

F-• : (bs bs' : Vec (Fin 4) k) (cs cs' : Tri k) →
      (₁₊ k) ⊢ F bs cs • F bs' cs' ≈ F (zipWith _+₄_ bs bs') (triXor cs cs')
F-• {zero} [] [] tt tt = Width.left-unit
F-• {suc k} (b ∷ bs) (b' ∷ bs') (c , cs) (c' , cs') = begin
  (A • B • C) • A' • B' • C'
    ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
  A • B • (C • A') • B' • C'
    ≈⟨ back A (back B (front _ (diag-comm dC dA'))) ⟩
  A • B • (A' • C) • B' • C'
    ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
  A • (B • A') • C • B' • C'
    ≈⟨ back A (front _ (diag-comm dB dA')) ⟩
  A • (A' • B) • C • B' • C'
    ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • □ • (□ • □) • □) Eq.refl ⟩
  A • A' • B • (C • B') • C'
    ≈⟨ back A (back A' (back B (front _ (diag-comm dC dB')))) ⟩
  A • A' • B • (B' • C) • C'
    ≈⟨ by-passoc (□ • □ • □ • (□ • □) • □) ((□ • □) • (□ • □) • (□ • □)) Eq.refl ⟩
  (A • A') • (B • B') • (C • C')
    ≈⟨ cong (CS-+ b b') (cong BB (C3B-• c c')) ⟩
  CS ^ toℕ (b +₄ b') • (SWAP • F (zipWith _+₄_ bs bs') (triXor cs cs') ↑ • SWAP) •
    C3B (zipWith _xor_ c c') ∎
  where
  open Width (₂₊ k)
  A  = CS ^ toℕ b
  A' = CS ^ toℕ b'
  B  = SWAP • F bs cs ↑ • SWAP
  B' = SWAP • F bs' cs' ↑ • SWAP
  C  = C3B c
  C' = C3B c'
  dA' : Diag (₂₊ k) A'
  dA' = dCS `^ toℕ b' , refl
  dB : Diag (₂₊ k) B
  dB = `c swap (proj₁ (F-diag bs cs) `↑) , back _ (front _ (lift (proj₂ (F-diag bs cs))))
  dB' : Diag (₂₊ k) B'
  dB' = `c swap (proj₁ (F-diag bs' cs') `↑) , back _ (front _ (lift (proj₂ (F-diag bs' cs'))))
  dC : Diag (₂₊ k) C
  dC = C3B-diag c
  BB : (₂₊ k) ⊢ B • B' ≈ SWAP • F (zipWith _+₄_ bs bs') (triXor cs cs') ↑ • SWAP
  BB = begin
    (SWAP • F bs cs ↑ • SWAP) • SWAP • F bs' cs' ↑ • SWAP
      ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    SWAP • F bs cs ↑ • (SWAP • SWAP) • F bs' cs' ↑ • SWAP
      ≈⟨ back _ (back _ (trans (front _ (ax swap-order)) left-unit)) ⟩
    SWAP • F bs cs ↑ • F bs' cs' ↑ • SWAP
      ≈⟨ back _ (trans (sym assoc) (front _ (lift (F-• bs bs' cs cs')))) ⟩
    SWAP • F (zipWith _+₄_ bs bs') (triXor cs cs') ↑ • SWAP ∎

------------------------------------------------------------------------
-- Multiples of a form

_·b_ : ℕ → Vec (Fin 4) k → Vec (Fin 4) k
_·b_ {k} zero    bs = replicate k 0F
_·b_     (suc j) bs = zipWith _+₄_ bs (j ·b bs)

_·t_ : ℕ → Tri k → Tri k
_·t_ {k} zero    cs = tri0 k
_·t_     (suc j) cs = triXor cs (j ·t cs)

F-^ : (j : ℕ) (bs : Vec (Fin 4) k) (cs : Tri k) →
      (₁₊ k) ⊢ F bs cs ^ j ≈ F (j ·b bs) (j ·t cs)
F-^ {k} zero    bs cs = sym (F-zero k)
  where open Width (₁₊ k)
F-^ {k} (suc j) bs cs = begin
  F bs cs ^ suc j                          ≈⟨ Pow.pow-suc (₁₊ k) (F bs cs) j ⟩
  F bs cs • F bs cs ^ j                    ≈⟨ back _ (F-^ j bs cs) ⟩
  F bs cs • F (j ·b bs) (j ·t cs)          ≈⟨ F-• bs (j ·b bs) cs (j ·t cs) ⟩
  F (suc j ·b bs) (suc j ·t cs)            ∎
  where open Width (₁₊ k)
