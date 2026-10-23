------------------------------------------------------------------------
-- Presentations of groups
--
-- Transporting four-wire equations along wire permutations and colourings
--
-- A gadget block is a middle word between two copies of a set of X
-- letters (`Blk`).  Conjugating a word of blocks by an adjacent swap
-- renames every letter (the table `tbl`) and keeps the block structure
-- (`relB`); conjugating it by an X letter toggles that wire in every
-- block's set, the middle words untouched (`togB`).  So an equation
-- between words of blocks, proved once at a canonical placement, holds
-- at every placement reached by a sequence of such conjugations
-- (`transport`) — which is how the facts of Lemma 8.8 at four wires are
-- carried from their canonical configurations to the decoded letters.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Proofs ; Win ; get)
open import Examples.Groups.Clifford+CS.Four.CStmt using (clemmas)

module Examples.Groups.Clifford+CS.Four.Transport (C : Proofs clemmas) where

open import Data.Bool using (Bool ; true ; false ; T ; _∧_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.List.Properties using (map-++ ; ++-assoc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.TransportTables C

------------------------------------------------------------------------
-- Lines

∷≈ : ∀ x xs → ⟪ x ∷ xs ⟫ʷ ≈ ⟪ x ⟫ • ⟪ xs ⟫ʷ
∷≈ x []       = sym right-unit
∷≈ x (y ∷ xs) = refl

++≈ : ∀ xs ys → ⟪ xs ++ ys ⟫ʷ ≈ ⟪ xs ⟫ʷ • ⟪ ys ⟫ʷ
++≈ []       ys = sym left-unit
++≈ (x ∷ xs) ys =
  trans (∷≈ x (xs ++ ys))
  (trans (back ⟪ x ⟫ (++≈ xs ys))
  (trans (sym assoc) (front ⟪ ys ⟫ʷ (sym (∷≈ x xs)))))

≡≈ : ∀ {w v : Circuit 4} → w ≡ v → w ≈ v
≡≈ Eq.refl = refl

-- Conjugating by an involutive letter.
conj : Mac → Circuit 4 → Circuit 4
conj c w = ⟪ c ⟫ • w • ⟪ c ⟫

-- A letter conjugating the concatenation of two lines.
conj-++ : ∀ c xs ys → ⟪ c ∷ c ∷ [] ⟫ʷ ≈ ε →
          conj c ⟪ xs ++ ys ⟫ʷ ≈ conj c ⟪ xs ⟫ʷ • conj c ⟪ ys ⟫ʷ
conj-++ c xs ys cc = begin
  ⟪ c ⟫ • ⟪ xs ++ ys ⟫ʷ • ⟪ c ⟫                          ≈⟨ back ⟪ c ⟫ (front ⟪ c ⟫ (++≈ xs ys)) ⟩
  ⟪ c ⟫ • (⟪ xs ⟫ʷ • ⟪ ys ⟫ʷ) • ⟪ c ⟫                    ≈⟨ back ⟪ c ⟫ assoc ⟩
  ⟪ c ⟫ • ⟪ xs ⟫ʷ • (⟪ ys ⟫ʷ • ⟪ c ⟫)                    ≈⟨ back ⟪ c ⟫ (back ⟪ xs ⟫ʷ (sym left-unit)) ⟩
  ⟪ c ⟫ • ⟪ xs ⟫ʷ • (ε • (⟪ ys ⟫ʷ • ⟪ c ⟫))              ≈⟨ back ⟪ c ⟫ (back ⟪ xs ⟫ʷ (front _ (sym cc))) ⟩
  ⟪ c ⟫ • ⟪ xs ⟫ʷ • ((⟪ c ⟫ • ⟪ c ⟫) • (⟪ ys ⟫ʷ • ⟪ c ⟫)) ≈⟨ back ⟪ c ⟫ (back ⟪ xs ⟫ʷ assoc) ⟩
  ⟪ c ⟫ • ⟪ xs ⟫ʷ • (⟪ c ⟫ • (⟪ c ⟫ • (⟪ ys ⟫ʷ • ⟪ c ⟫))) ≈⟨ back ⟪ c ⟫ (sym assoc) ⟩
  ⟪ c ⟫ • ((⟪ xs ⟫ʷ • ⟪ c ⟫) • (⟪ c ⟫ • (⟪ ys ⟫ʷ • ⟪ c ⟫))) ≈⟨ sym assoc ⟩
  (⟪ c ⟫ • (⟪ xs ⟫ʷ • ⟪ c ⟫)) • (⟪ c ⟫ • (⟪ ys ⟫ʷ • ⟪ c ⟫)) ∎

-- A line between two copies of a letter.
conj-line : ∀ c xs → conj c ⟪ xs ⟫ʷ ≈ ⟪ c ∷ xs ++ c ∷ [] ⟫ʷ
conj-line c xs = sym (begin
  ⟪ c ∷ xs ++ c ∷ [] ⟫ʷ                ≈⟨ ∷≈ c (xs ++ c ∷ []) ⟩
  ⟪ c ⟫ • ⟪ xs ++ c ∷ [] ⟫ʷ            ≈⟨ back ⟪ c ⟫ (++≈ xs (c ∷ [])) ⟩
  ⟪ c ⟫ • (⟪ xs ⟫ʷ • ⟪ c ⟫)            ∎)

------------------------------------------------------------------------
-- Letters a swap acts on

allok : List Mac → Bool
allok []       = true
allok (x ∷ xs) = ok x ∧ allok xs

hd : ∀ {x xs} → T (allok (x ∷ xs)) → T (ok x)
hd {x} p with ok x
... | true  = tt
... | false = ⊥-elim p

tl : ∀ {x xs} → T (allok (x ∷ xs)) → T (allok xs)
tl {x} p with ok x
... | true  = p
... | false = ⊥-elim p

allok-map : ∀ s xs → allok (map (πL s) xs) ≡ allok xs
allok-map s []       = Eq.refl
allok-map s (x ∷ xs) = Eq.cong₂ _∧_ (ok-π s x) (allok-map s xs)

-- Conjugating a line by a swap renames it.
rel1 : ∀ s xs → T (allok xs) → conj (swL s) ⟪ xs ⟫ʷ ≈ ⟪ map (πL s) xs ⟫ʷ
rel1 s []       _ = trans (back σ left-unit) (swsw s) where σ = ⟪ swL s ⟫
rel1 s (x ∷ xs) p = begin
  σ • ⟪ x ∷ xs ⟫ʷ • σ                       ≈⟨ back σ (front σ (∷≈ x xs)) ⟩
  σ • (⟪ x ⟫ • ⟪ xs ⟫ʷ) • σ                 ≈⟨ back σ assoc ⟩
  σ • ⟪ x ⟫ • (⟪ xs ⟫ʷ • σ)                 ≈⟨ back σ (back ⟪ x ⟫ (sym left-unit)) ⟩
  σ • ⟪ x ⟫ • (ε • (⟪ xs ⟫ʷ • σ))           ≈⟨ back σ (back ⟪ x ⟫ (front _ (sym (swsw s)))) ⟩
  σ • ⟪ x ⟫ • ((σ • σ) • (⟪ xs ⟫ʷ • σ))     ≈⟨ back σ (back ⟪ x ⟫ assoc) ⟩
  σ • ⟪ x ⟫ • (σ • (σ • (⟪ xs ⟫ʷ • σ)))     ≈⟨ back σ (sym assoc) ⟩
  σ • ((⟪ x ⟫ • σ) • (σ • (⟪ xs ⟫ʷ • σ)))   ≈⟨ sym assoc ⟩
  (σ • (⟪ x ⟫ • σ)) • (σ • (⟪ xs ⟫ʷ • σ))   ≈⟨ cong (tbl s x (hd {x} {xs} p)) (rel1 s xs (tl {x} {xs} p)) ⟩
  ⟪ πL s x ⟫ • ⟪ map (πL s) xs ⟫ʷ          ≈⟨ sym (∷≈ (πL s x) (map (πL s) xs)) ⟩
  ⟪ πL s x ∷ map (πL s) xs ⟫ʷ              ∎
  where σ = ⟪ swL s ⟫

------------------------------------------------------------------------
-- Blocks

record Blk : Set where
  constructor blk
  field
    bx  : XB
    mw  : List Mac

flatB : Blk → List Mac
flatB (blk b m) = Xs b ++ m ++ Xs b

flat : List Blk → List Mac
flat []       = []
flat (k ∷ ks) = flatB k ++ flat ks

-- The middle words a swap acts on.
okB : List Blk → Bool
okB []             = true
okB (blk b m ∷ ks) = allok m ∧ okB ks

relB : Sw → Blk → Blk
relB s (blk b m) = blk (πB s b) (map (πL s) m)

togB : Wi → Blk → Blk
togB w (blk b m) = blk (tog w b) m

okB-rel : ∀ s ks → okB (map (relB s) ks) ≡ okB ks
okB-rel s []             = Eq.refl
okB-rel s (blk b m ∷ ks) = Eq.cong₂ _∧_ (allok-map s m) (okB-rel s ks)

okB-tog : ∀ w ks → okB (map (togB w) ks) ≡ okB ks
okB-tog w []             = Eq.refl
okB-tog w (blk b m ∷ ks) = Eq.cong (allok m ∧_) (okB-tog w ks)

-- X letters are all acted on.
allok-Xs : ∀ b → allok (Xs b) ≡ true
allok-Xs (xb a b c d) = lemma a b c d
  where
    opt-ok : ∀ e x → ok x ≡ true → ∀ r → allok (opt e x ++ r) ≡ allok r
    opt-ok true  x o r = Eq.cong (_∧ allok r) o
    opt-ok false x o r = Eq.refl
    last : ∀ d → allok (opt d X3) ≡ true
    last true  = Eq.refl
    last false = Eq.refl
    lemma : ∀ a b c d → allok (Xs (xb a b c d)) ≡ true
    lemma a b c d =
      Eq.trans (opt-ok a X0 Eq.refl _) (Eq.trans (opt-ok b X1 Eq.refl _)
      (Eq.trans (opt-ok c X2 Eq.refl _) (last d)))

allok-++ : ∀ xs ys → allok (xs ++ ys) ≡ allok xs ∧ allok ys
allok-++ []       ys = Eq.refl
allok-++ (x ∷ xs) ys rewrite allok-++ xs ys with ok x
... | true  = Eq.refl
... | false = Eq.refl

T∧ : ∀ {a b} → T a → T b → T (a ∧ b)
T∧ {true} {true} _ _ = tt

T∧₁ : ∀ {a b} → T (a ∧ b) → T a
T∧₁ {true} _ = tt

T∧₂ : ∀ {a b} → T (a ∧ b) → T b
T∧₂ {true} p = p

T≡ : ∀ {a b} → a ≡ b → T b → T a
T≡ Eq.refl p = p

okB-flat : ∀ ks → T (okB ks) → T (allok (flat ks))
okB-flat []             _ = tt
okB-flat (blk b m ∷ ks) p =
  T≡ (allok-++ (flatB (blk b m)) (flat ks))
     (T∧ (T≡ (Eq.trans (allok-++ (Xs b) (m ++ Xs b))
               (Eq.cong₂ _∧_ (allok-Xs b) (Eq.trans (allok-++ m (Xs b)) (Eq.cong (allok m ∧_) (allok-Xs b)))))
             (T∧ tt (T∧ (T∧₁ p) tt)))
         (okB-flat ks (T∧₂ p)))

-- A swap conjugating a word of blocks.
blockπ : ∀ s b m →
         ⟪ map (πL s) (Xs b ++ m ++ Xs b) ⟫ʷ ≈ ⟪ Xs (πB s b) ++ map (πL s) m ++ Xs (πB s b) ⟫ʷ
blockπ s b m = begin
  ⟪ map (πL s) (Xs b ++ m ++ Xs b) ⟫ʷ
    ≡⟨ Eq.cong ⟪_⟫ʷ (Eq.trans (map-++ (πL s) (Xs b) (m ++ Xs b))
                      (Eq.cong (map (πL s) (Xs b) ++_) (map-++ (πL s) m (Xs b)))) ⟩
  ⟪ map (πL s) (Xs b) ++ map (πL s) m ++ map (πL s) (Xs b) ⟫ʷ
    ≈⟨ ++≈ (map (πL s) (Xs b)) _ ⟩
  ⟪ map (πL s) (Xs b) ⟫ʷ • ⟪ map (πL s) m ++ map (πL s) (Xs b) ⟫ʷ
    ≈⟨ back _ (++≈ (map (πL s) m) _) ⟩
  ⟪ map (πL s) (Xs b) ⟫ʷ • (⟪ map (πL s) m ⟫ʷ • ⟪ map (πL s) (Xs b) ⟫ʷ)
    ≈⟨ cong (xr s b) (back _ (xr s b)) ⟩
  ⟪ Xs (πB s b) ⟫ʷ • (⟪ map (πL s) m ⟫ʷ • ⟪ Xs (πB s b) ⟫ʷ)
    ≈⟨ back _ (sym (++≈ (map (πL s) m) _)) ⟩
  ⟪ Xs (πB s b) ⟫ʷ • ⟪ map (πL s) m ++ Xs (πB s b) ⟫ʷ
    ≈⟨ sym (++≈ (Xs (πB s b)) _) ⟩
  ⟪ Xs (πB s b) ++ map (πL s) m ++ Xs (πB s b) ⟫ʷ ∎

mapflat : ∀ s ks → ⟪ map (πL s) (flat ks) ⟫ʷ ≈ ⟪ flat (map (relB s) ks) ⟫ʷ
mapflat s []             = refl
mapflat s (blk b m ∷ ks) = begin
  ⟪ map (πL s) (flatB (blk b m) ++ flat ks) ⟫ʷ
    ≡⟨ Eq.cong ⟪_⟫ʷ (map-++ (πL s) (flatB (blk b m)) (flat ks)) ⟩
  ⟪ map (πL s) (flatB (blk b m)) ++ map (πL s) (flat ks) ⟫ʷ
    ≈⟨ ++≈ (map (πL s) (flatB (blk b m))) _ ⟩
  ⟪ map (πL s) (flatB (blk b m)) ⟫ʷ • ⟪ map (πL s) (flat ks) ⟫ʷ
    ≈⟨ cong (blockπ s b m) (mapflat s ks) ⟩
  ⟪ flatB (relB s (blk b m)) ⟫ʷ • ⟪ flat (map (relB s) ks) ⟫ʷ
    ≈⟨ sym (++≈ (flatB (relB s (blk b m))) _) ⟩
  ⟪ flat (map (relB s) (blk b m ∷ ks)) ⟫ʷ ∎

rel-blocks : ∀ s ks → T (okB ks) → conj (swL s) ⟪ flat ks ⟫ʷ ≈ ⟪ flat (map (relB s) ks) ⟫ʷ
rel-blocks s ks p = trans (rel1 s (flat ks) (okB-flat ks p)) (mapflat s ks)

-- An X letter conjugating a word of blocks.
col-blocks : ∀ w ks → conj (xL w) ⟪ flat ks ⟫ʷ ≈ ⟪ flat (map (togB w) ks) ⟫ʷ
col-blocks w []             = trans (back x left-unit) (xx w) where x = ⟪ xL w ⟫
col-blocks w (blk b m ∷ ks) = begin
  conj (xL w) ⟪ flatB (blk b m) ++ flat ks ⟫ʷ
    ≈⟨ conj-++ (xL w) (flatB (blk b m)) (flat ks) (xx w) ⟩
  conj (xL w) ⟪ Xs b ++ m ++ Xs b ⟫ʷ • conj (xL w) ⟪ flat ks ⟫ʷ
    ≈⟨ cong blk≈ (col-blocks w ks) ⟩
  ⟪ flatB (togB w (blk b m)) ⟫ʷ • ⟪ flat (map (togB w) ks) ⟫ʷ
    ≈⟨ sym (++≈ (flatB (togB w (blk b m))) _) ⟩
  ⟪ flat (map (togB w) (blk b m ∷ ks)) ⟫ʷ ∎
  where
    x = ⟪ xL w ⟫
    blk≈ : conj (xL w) ⟪ Xs b ++ m ++ Xs b ⟫ʷ ≈ ⟪ Xs (tog w b) ++ m ++ Xs (tog w b) ⟫ʷ
    blk≈ = begin
      x • ⟪ Xs b ++ m ++ Xs b ⟫ʷ • x
        ≈⟨ back x (front x (trans (++≈ (Xs b) _) (back _ (++≈ m (Xs b))))) ⟩
      x • (⟪ Xs b ⟫ʷ • (⟪ m ⟫ʷ • ⟪ Xs b ⟫ʷ)) • x
        ≈⟨ trans (back x assoc) (trans (back x (back _ assoc)) (sym assoc)) ⟩
      (x • ⟪ Xs b ⟫ʷ) • (⟪ m ⟫ʷ • (⟪ Xs b ⟫ʷ • x))
        ≈⟨ cong (trans (sym (∷≈ (xL w) (Xs b))) (xt w b))
                (back _ (trans (sym (++≈ (Xs b) (xL w ∷ []))) (xs w b))) ⟩
      ⟪ Xs (tog w b) ⟫ʷ • (⟪ m ⟫ʷ • ⟪ Xs (tog w b) ⟫ʷ)
        ≈⟨ sym (trans (++≈ (Xs (tog w b)) _) (back _ (++≈ m (Xs (tog w b))))) ⟩
      ⟪ Xs (tog w b) ++ m ++ Xs (tog w b) ⟫ʷ ∎

------------------------------------------------------------------------
-- Frames

-- A frame is a sequence of conjugations, the first the outermost.
data Op : Set where
  rel : Sw → Op
  col : Wi → Op

opL : Op → Mac
opL (rel s) = swL s
opL (col w) = xL w

-- The conjugate of a word by a frame.
F⟪_⟫_ : List Op → Circuit 4 → Circuit 4
F⟪ [] ⟫ w     = w
F⟪ o ∷ os ⟫ w = conj (opL o) (F⟪ os ⟫ w)

-- The blocks it carries a word of blocks to.
stepB : Op → List Blk → List Blk
stepB (rel s) ks = map (relB s) ks
stepB (col w) ks = map (togB w) ks

TF : List Op → List Blk → List Blk
TF []       ks = ks
TF (o ∷ os) ks = stepB o (TF os ks)

okB-TF : ∀ os ks → okB (TF os ks) ≡ okB ks
okB-TF []           ks = Eq.refl
okB-TF (rel s ∷ os) ks = Eq.trans (okB-rel s (TF os ks)) (okB-TF os ks)
okB-TF (col w ∷ os) ks = Eq.trans (okB-tog w (TF os ks)) (okB-TF os ks)

F-cong : ∀ os {w v} → w ≈ v → F⟪ os ⟫ w ≈ F⟪ os ⟫ v
F-cong []       e = e
F-cong (o ∷ os) e = back _ (front _ (F-cong os e))

F-blocks : ∀ os ks → T (okB ks) → F⟪ os ⟫ ⟪ flat ks ⟫ʷ ≈ ⟪ flat (TF os ks) ⟫ʷ
F-blocks []           ks p = refl
F-blocks (rel s ∷ os) ks p =
  trans (back _ (front _ (F-blocks os ks p)))
        (rel-blocks s (TF os ks) (T≡ (okB-TF os ks) p))
F-blocks (col w ∷ os) ks p =
  trans (back _ (front _ (F-blocks os ks p))) (col-blocks w (TF os ks))

-- An equation of words of blocks holds at every placement.
transport : ∀ os ls rs → T (okB ls) → T (okB rs) →
            ⟪ flat ls ⟫ʷ ≈ ⟪ flat rs ⟫ʷ → ⟪ flat (TF os ls) ⟫ʷ ≈ ⟪ flat (TF os rs) ⟫ʷ
transport os ls rs pl pr e =
  trans (sym (F-blocks os ls pl)) (trans (F-cong os e) (F-blocks os rs pr))
