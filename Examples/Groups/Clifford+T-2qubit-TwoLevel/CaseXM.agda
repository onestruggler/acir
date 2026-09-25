------------------------------------------------------------------------
-- Presentations of groups
--
-- The hard subcase of Cases 3–5, in dimension at most 4: k > 0, the
-- first two odd entries of w are j < α, and w_β is odd, β = α + 1.
-- Then there is a fourth odd entry ℓ′.  With D_s the powers of ω that
-- make w_j, w_α, w_β, w_ℓ′ equal to 1 + a δ³, 1 + b δ³, 1 + c δ³ and
-- 1 + d δ³, the square closes through G′ = V_r⁻¹ B V_s (HardRel).  In
-- dimension 4 the sum a + b + c + d is even (OddSum), so ≡ 0 or δ
-- (mod δ²), and B is the first or the second path of the thesis
-- accordingly (FourOdd): along either, each state has an even entry
-- j, so lies below s.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s ; _+_ ; _∸_)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.CaseXM {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary.Decidable using (recompute)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Residue
  using (δ²ᶻ ; δ³ᶻ ; _∣_ ; _,_ ; ∣-+ ; ∣-* ; zOf-spec ; zOf-< ; par ; c1 ; oddP-par ; δ²∣-par ; δ²∣-δ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Lde
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Column
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics hiding (_!_ ; U)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Pivot using (pivot ; pivot-just ; Beyond ; level ; _<ₗ_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syllable
  using (syl ; step ; Within ; Within-^ ; Beyond-actM ; Beyond-actMʷ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Levels using (Bℓ ; Minimal-X)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Derived {n} using (_⁻¹)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Basic {n} using (Letters≤)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Reduction {n} using (Square ; Below)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.MainTools {n}
  using (sound-vec ; lt-step ; square-syl ; syl-of ; word-below-all ; pivot-stay ; ne-𝕀 ; bℓ-below ; level-le)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.FourOdd {n}
  using (zz ; y₁ ; y₂ ; dd₀ ; dd₁ ; s₂j ; t₃j ; even-y₁ ; even-s₂j ; even-t₃j)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.FourOdd {n} as FourOdd
import Examples.Groups.Clifford+T-2qubit-TwoLevel.HardRel {n} as HardRel
import Examples.Groups.Clifford+T-2qubit-TwoLevel.OddSum as OddSum
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.CaseX {n} using (module Common ; Hard)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.PivotColumn as PivotColumn

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open ZG using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

------------------------------------------------------------------------
-- Residues modulo δ³

-- x ≡ 1 (mod δ³): x = 1 + c δ³.
to-zz : ∀ x → δ³ᶻ ∣ (x ZR.- ZR.1#) → ∃ λ c → x ≡ zz c
to-zz x (c , e) =
  c , ≡.trans (ZG.solve 1 (λ x → x := con ZR.1# :+ (x :- con ZR.1#)) ≡.refl x) (≡.cong (ZR.1# ZR.+_) e)

-- ωᶻ u ≡ v and ωᶠ v ≡ 1 give ω^(f + z) u ≡ 1.
chain : ∀ f z u v → δ³ᶻ ∣ ((ωᶻ ^ᶻ z) ZR.* u ZR.- v) → δ³ᶻ ∣ ((ωᶻ ^ᶻ f) ZR.* v ZR.- ZR.1#) →
        δ³ᶻ ∣ ((ωᶻ ^ᶻ (f + z)) ZR.* u ZR.- ZR.1#)
chain f z u v h₁ h₂ = ≡.subst (δ³ᶻ ∣_) (≡.sym eq) (∣-+ (∣-* (ωᶻ ^ᶻ f) h₁) h₂)
  where
  eq : (ωᶻ ^ᶻ (f + z)) ZR.* u ZR.- ZR.1# ≡
       (ωᶻ ^ᶻ f) ZR.* ((ωᶻ ^ᶻ z) ZR.* u ZR.- v) ZR.+ ((ωᶻ ^ᶻ f) ZR.* v ZR.- ZR.1#)
  eq = ≡.trans (≡.cong (λ y → y ZR.* u ZR.- ZR.1#) (^ᶻ-+ ωᶻ f z))
         (ZG.solve 4 (λ F Q u v → (F :* Q) :* u :- con ZR.1# := F :* (Q :* u :- v) :+ (F :* v :- con ZR.1#))
                     ≡.refl (ωᶻ ^ᶻ f) (ωᶻ ^ᶻ z) u v)

-- ω^z′ u ≡ w and ωᵉ u ≡ 1 give ωᵍ w ≡ 1, when g + z′ = e + 8.
chain′ : ∀ e z′ g u w → g + z′ ≡ e + 8 → δ³ᶻ ∣ ((ωᶻ ^ᶻ z′) ZR.* u ZR.- w) →
         δ³ᶻ ∣ ((ωᶻ ^ᶻ e) ZR.* u ZR.- ZR.1#) → δ³ᶻ ∣ ((ωᶻ ^ᶻ g) ZR.* w ZR.- ZR.1#)
chain′ e z′ g u w gz h₁ h₂ = ≡.subst (δ³ᶻ ∣_) (≡.sym eq) (∣-+ (∣-* (ZR.- Gω) h₁) h₂′)
  where
  Gω = ωᶻ ^ᶻ g
  Zω = ωᶻ ^ᶻ z′
  GZ : Gω ZR.* Zω ≡ ωᶻ ^ᶻ e
  GZ = ≡.trans (≡.sym (^ᶻ-+ ωᶻ g z′))
         (≡.trans (≡.cong (ωᶻ ^ᶻ_) gz) (≡.trans (^ᶻ-+ ωᶻ e 8) (ZR.*-identityʳ (ωᶻ ^ᶻ e))))
  h₂′ : δ³ᶻ ∣ ((Gω ZR.* Zω) ZR.* u ZR.- ZR.1#)
  h₂′ = ≡.subst (λ y → δ³ᶻ ∣ (y ZR.* u ZR.- ZR.1#)) (≡.sym GZ) h₂
  eq : Gω ZR.* w ZR.- ZR.1# ≡ (ZR.- Gω) ZR.* (Zω ZR.* u ZR.- w) ZR.+ ((Gω ZR.* Zω) ZR.* u ZR.- ZR.1#)
  eq = ZG.solve 4 (λ G Q u w → G :* w :- con ZR.1# := (:- G) :* (Q :* u :- w) :+ ((G :* Q) :* u :- con ZR.1#))
                  ≡.refl Gω Zω u w

------------------------------------------------------------------------
-- The subcase

module _ (n≤4 : n ℕ.≤ 4) (α β : Fin n) (αβ1 : toℕ β ≡ suc (toℕ α))
         (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p) where

  open Common α β αβ1
  open PivotColumn s o ps

  hard : Hard α β αβ1 s o ps
  hard {K′} {j} ks fo nx oβ = go (third ks fo nx αβ oβ (λ x αx xβ → ⊥-elim (none-αβ αx xβ)))
    where
    jα : j < α
    jα = proj₁ (nextOdd-spec W nx)
    oj : Odd (W ! j)
    oj = proj₁ (firstOdd-spec W fo)
    oα : Odd (W ! α)
    oα = proj₁ (proj₂ (nextOdd-spec W nx))
    k = suc K′
    v≡ₖ : v ≡ scV k W
    v≡ₖ = ≡.trans v≡ (≡.cong (λ k → scV k W) ks)
    lvl′ : level s ≡ (suc (toℕ p) , k , nodd W)
    lvl′ = ≡.trans lvl (≡.cong (λ k → (suc (toℕ p) , k , nodd W)) ks)
    z = zOf (W ! j) (W ! α)
    z′ = zOf (W ! j) (W ! β)
    r = actM G s
    t = step s
    syl-s : syl s ≡ H j α jα • ω j ^ z
    syl-s = ≡.trans syl≡ (≡.trans (≡.cong (λ k → sylData p k W) ks) (sylData-pair {p = p} K′ W fo nx jα))

    cong-act : (w : Word (Gen n)) {x y : Vec D n} → x ≡ y → actVʷ w x ≡ actVʷ w y
    cong-act w ≡.refl = ≡.refl

    go : (∃ λ ℓ′ → nextOdd β W ≡ just ℓ′) → Square (X-gen α β αβ) s o
    go (ℓ′ , nx′) = with-c (to-zz _ dj) (to-zz _ dα) (to-zz _ dβ) (to-zz _ dℓ′)
      where
      βℓ′ : β < ℓ′
      βℓ′ = proj₁ (nextOdd-spec W nx′)
      oℓ′ : Odd (W ! ℓ′)
      oℓ′ = proj₁ (proj₂ (nextOdd-spec W nx′))
      ℓ′≤p : ℓ′ ≤ p
      ℓ′≤p = odd≤ oℓ′

      module F = FourOdd.Four jα αβ βℓ′ W

      j≤ℓ′ : toℕ j ℕ.≤ toℕ ℓ′
      j≤ℓ′ = ℕP.<⇒≤ F.jℓ′
      α≤ℓ′ : toℕ α ℕ.≤ toℕ ℓ′
      α≤ℓ′ = ℕP.<⇒≤ F.αℓ′
      β≤ℓ′ : toℕ β ℕ.≤ toℕ ℓ′
      β≤ℓ′ = ℕP.<⇒≤ βℓ′
      j≤p = ℕP.≤-trans j≤ℓ′ ℓ′≤p
      α≤p = ℕP.≤-trans α≤ℓ′ ℓ′≤p
      β≤p = ℕP.≤-trans β≤ℓ′ ℓ′≤p

      -- The normal edge from r = X_[α,β] s is H_[j,α] ω_[j]^z′.
      U = Xᶻ α β W
      colU : col r p ≡ scV k U
      colU = ≡.trans (col-actM G s p) (≡.trans (≡.cong (actV G) v≡ₖ) (actV-X α β αβ k W))
      minU : Minimal k U
      minU = Minimal-X α β α≢β W (≡.subst (λ k → Minimal k W) ks min)
      pr : pivot r ≡ just p
      pr = pivot-stay G s β≤p ps (ne-𝕀 r p K′ U colU minU)
      syl-r : syl r ≡ H j α jα • ω j ^ z′
      syl-r = ≡.trans (syl-of r pr k U colU minU)
                (≡.trans (sylData-pair {p = p} K′ U foU nxU jα)
                  (≡.cong₂ (λ x y → H j α jα • ω j ^ zOf x y) Uj (Xᶻ-α W)))
        where
        jβ = ℕP.<-trans jα αβ
        Uj : U ! j ≡ W ! j
        Uj = Xᶻ-≢ W (FinP.<⇒≢ jα) (FinP.<⇒≢ jβ)
        foU : firstOdd U ≡ just j
        foU = firstOdd-char U (≡.subst Odd (≡.sym Uj) oj)
                (λ x xj → ≡.subst Even (≡.sym (Xᶻ-≢ W (FinP.<⇒≢ (ℕP.<-trans xj jα)) (FinP.<⇒≢ (ℕP.<-trans xj jβ))))
                                  (proj₂ (firstOdd-spec W fo) x xj))
        nxU : nextOdd j U ≡ just α
        nxU = nextOdd-char U jα (≡.subst Odd (≡.sym (Xᶻ-α W)) oβ)
                (λ x jx xα → ≡.subst Even (≡.sym (Xᶻ-≢ W (FinP.<⇒≢ xα) (FinP.<⇒≢ (ℕP.<-trans xα αβ))))
                                     (proj₂ (proj₂ (nextOdd-spec W nx)) x jx xα))

      -- The exponents: ω^(f + z) w_j, ωᶠ w_α, ωᵍ w_β, ωᵐ w_ℓ′ ≡ 1 (mod δ³).
      f = zOf (W ! α) ZR.1#
      m = zOf (W ! ℓ′) ZR.1#
      z′≤8 : z′ ℕ.≤ 8
      z′≤8 = ℕP.≤-trans (ℕP.<⇒≤ (zOf-< (W ! j) (W ! β))) (s≤s (s≤s (s≤s (s≤s z≤n))))
      g = f + z + (8 ∸ z′)
      g+z′ : g + z′ ≡ (f + z) + 8
      g+z′ = ≡.trans (ℕP.+-assoc (f + z) (8 ∸ z′) z′) (≡.cong ((f + z) +_) (ℕP.m∸n+n≡m z′≤8))

      dα = zOf-spec (W ! α) ZR.1# oα ≡.refl
      dj = chain f z (W ! j) (W ! α) (zOf-spec (W ! j) (W ! α) oj oα) dα
      dβ = chain′ (f + z) z′ g (W ! j) (W ! β) g+z′ (zOf-spec (W ! j) (W ! β) oj oβ) dj
      dℓ′ = zOf-spec (W ! ℓ′) ZR.1# oℓ′ ≡.refl

      Vs Ds : Word (Gen n)
      Vs = (ω β ^ g • ω ℓ′ ^ m) • (ω j ^ f • ω α ^ f)
      Ds = ω j ^ (f + z) • ω α ^ f • ω β ^ g • ω ℓ′ ^ m

      Vs-letters : Letters≤ ℓ′ Vs
      Vs-letters = (HardRel.Letters≤-^ (ω β) β≤ℓ′ g , HardRel.Letters≤-^ (ω ℓ′) ℕP.≤-refl m) ,
                   (HardRel.Letters≤-^ (ω j) j≤ℓ′ f , HardRel.Letters≤-^ (ω α) α≤ℓ′ f)

      -- Words of transpositions and powers of ω at indices ≤ ℓ′ act on
      -- indices ≤ p.
      within : (w : Word (Gen n)) → Letters≤ ℓ′ w → Within p w
      within [ X-gen a b _ ]ʷ h = ℕP.≤-trans h ℓ′≤p
      within [ H-gen a b _ ]ʷ ()
      within [ ω-gen a ]ʷ h = ℕP.≤-trans h ℓ′≤p
      within ε _ = tt
      within (u • w) (hu , hw) = within u hu , within w hw

      L = level s
      bℓ′ : Bℓ ℓ′ <ₗ L
      bℓ′ = ≡.subst (Bℓ ℓ′ <ₗ_) (≡.sym lvl′) (bℓ-below (nodd W) (s≤s z≤n) ℓ′≤p)
      lv : ∀ (M : Matrix n n D) → Beyond p M → (N : Vec Z n) → col M p ≡ scV k N →
           nodd N ℕ.< nodd W → level M <ₗ L
      lv M be N eq lt = ≡.subst (level M <ₗ_) (≡.sym lvl′) (level-le M be k N eq lt)
      nodd< : ∀ x₁ x₂ x₃ x₄ → Even x₁ → nodd (F.Nv x₁ x₂ x₃ x₄) ℕ.< nodd W
      nodd< x₁ x₂ x₃ x₄ e = F.nodd-N x₁ x₂ x₃ x₄ e oj oα oβ oℓ′

      -- The square, through a path B from V_s t.
      T₀ : Matrix n n D
      T₀ = actMʷ Vs t

      finish : (B : Word (Gen n)) → H j α jα • X α β αβ ≈ B • H j α jα → Below L B T₀ →
               level (actMʷ B T₀) <ₗ L → Square G s o
      finish B bottom bB l-end =
        square-syl G s o (H j α jα • ω j ^ z′) HR.G′ pr syl-r below (trans HR.rel (cright refl′ (≡.sym syl-s)))
        where
        module HR = HardRel.Hard jα αβ βℓ′ B bottom f z z′ m z′≤8
        below : Below L HR.G′ t
        below = (word-below-all HR.Vs HR.Vs-letters t (lt-step s o ps) bℓ′ , bB) ,
                word-below-all (HR.Vr ⁻¹) HR.Vr⁻¹-letters (actMʷ B T₀) l-end bℓ′

      with-c : (∃ λ a → (ωᶻ ^ᶻ (f + z)) ZR.* (W ! j) ≡ zz a) → (∃ λ b → (ωᶻ ^ᶻ f) ZR.* (W ! α) ≡ zz b) →
               (∃ λ c → (ωᶻ ^ᶻ g) ZR.* (W ! β) ≡ zz c) → (∃ λ d → (ωᶻ ^ᶻ m) ZR.* (W ! ℓ′) ≡ zz d) →
               Square G s o
      with-c (a , ea) (b , eb) (c , ec) (d , ed) = byA (oddᶻ A) ≡.refl
        where
        A = (a ZR.+ b) ZR.+ (c ZR.+ d)

        cong4 : ∀ {x x′ y y′ u u′ w w′ : Z} → x ≡ x′ → y ≡ y′ → u ≡ u′ → w ≡ w′ → F.Nv x y u w ≡ F.Nv x′ y′ u′ w′
        cong4 ≡.refl ≡.refl ≡.refl ≡.refl = ≡.refl

        -- The first two states, H_[j,α] D_s s and H_[β,ℓ′] of it.
        col₀ : col T₀ p ≡ scV k (F.Nv (y₁ a b) (y₂ a b) (zz c) (zz d))
        col₀ = ≡.trans (col-actMʷ (Vs • syl s) s p)
                 (≡.trans (≡.cong (λ w → actVʷ (Vs • w) v) syl-s)
                   (≡.trans (sound-vec (sym (HardRel.face jα αβ βℓ′ f z g m)) v)
                     (≡.trans (≡.cong (actV (H-gen j α jα))
                                (≡.trans (cong-act Ds v≡ₖ)
                                  (≡.trans (F.diag k (f + z) f g m) (≡.cong (scV k) (cong4 ea eb ec ed)))))
                              (F.step₀ k a b c d))))

        be₀ : Beyond p T₀
        be₀ = Beyond-actMʷ (Vs • syl s) {M = s}
                (within Vs Vs-letters , ≡.subst (Within p) (≡.sym syl-s) (α≤p , Within-^ (ω j) j≤p z))
                (proj₂ (pivot-just s ps))

        T₁ = actM (H-gen β ℓ′ βℓ′) T₀

        col₁ : col T₁ p ≡ scV k (F.Nv (y₁ a b) (y₂ a b) (y₁ c d) (y₂ c d))
        col₁ = ≡.trans (col-actM (H-gen β ℓ′ βℓ′) T₀ p)
                 (≡.trans (≡.cong (actV (H-gen β ℓ′ βℓ′)) col₀) (F.step₁ k a b c d))

        be₁ = Beyond-actM (H-gen β ℓ′ βℓ′) {M = T₀} ℓ′≤p be₀
        l₀ = lv T₀ be₀ _ col₀ (nodd< _ _ _ _ (even-y₁ a b))
        l₁ = lv T₁ be₁ _ col₁ (nodd< _ _ _ _ (even-y₁ a b))

        -- The sum a + b + c + d is even.
        unit₁ : ⟨ col T₁ p , col T₁ p ⟩ ≡ DR.1#
        unit₁ = recompute (⟨ col T₁ p , col T₁ p ⟩ ≟ᴰ DR.1#)
                          (col-unit (ColOrth-actMʷ (H β ℓ′ βℓ′ • (Vs • syl s)) o) p)

        evenA : oddᶻ A ≡ false
        evenA = OddSum.even-sum n≤4 jα αβ βℓ′ W K′ a b c d (col T₁ p) unit₁ col₁

        -- The first path, when a + b + c + d = δ² A₂.
        path₀ : δ²ᶻ ∣ A → Square G s o
        path₀ (A₂ , eA) = finish (HardRel.B₀ jα αβ βℓ′) (HardRel.bottom₀ jα αβ βℓ′)
                            (((l₀ , l₁) , ((((l₁ , l₂) , (l₂ , l₃)) , (l₃ , l₄)) , (l₄ , l₅)) , (l₅ , l₆)) , (l₆ , l₇))
                            l₇
          where
          d′ = dd₀ a b c A₂
          ed′ : d ≡ d′
          ed′ = ≡.trans (ZG.solve 4 (λ a b c d → d := ((a :+ b) :+ (c :+ d)) :- (a :+ b :+ c)) ≡.refl a b c d)
                        (≡.cong (ZR._- (a ZR.+ b ZR.+ c)) eA)
          module P = F.Path₀ k a b c A₂
          T₂ = actM (H-gen j β F.jβ) T₁
          T₃ = actM (H-gen α ℓ′ F.αℓ′) T₂
          T₄ = actM (X-gen α β αβ) T₃
          T₅ = actM (H-gen α ℓ′ F.αℓ′) T₄
          T₆ = actM (H-gen j β F.jβ) T₅
          T₇ = actM (H-gen β ℓ′ βℓ′) T₆
          c₁ : col T₁ p ≡ scV k (F.Nv (y₁ a b) (y₂ a b) (y₁ c d′) (y₂ c d′))
          c₁ = ≡.subst (λ x → col T₁ p ≡ scV k (F.Nv (y₁ a b) (y₂ a b) (y₁ c x) (y₂ c x))) ed′ col₁
          c₂ = ≡.trans (col-actM (H-gen j β F.jβ) T₁ p) (≡.trans (≡.cong (actV (H-gen j β F.jβ)) c₁) P.step₂)
          c₃ = ≡.trans (col-actM (H-gen α ℓ′ F.αℓ′) T₂ p) (≡.trans (≡.cong (actV (H-gen α ℓ′ F.αℓ′)) c₂) P.step₃)
          c₄ = ≡.trans (col-actM (X-gen α β αβ) T₃ p) (≡.trans (≡.cong (actV (X-gen α β αβ)) c₃) P.step₄)
          c₅ = ≡.trans (col-actM (H-gen α ℓ′ F.αℓ′) T₄ p) (≡.trans (≡.cong (actV (H-gen α ℓ′ F.αℓ′)) c₄) P.step₅)
          c₆ = ≡.trans (col-actM (H-gen j β F.jβ) T₅ p) (≡.trans (≡.cong (actV (H-gen j β F.jβ)) c₅) P.step₆)
          c₇ = ≡.trans (col-actM (H-gen β ℓ′ βℓ′) T₆ p)
                 (≡.trans (≡.cong (actV (H-gen β ℓ′ βℓ′)) c₆) (F.step₇ k a b c d′))
          be₂ = Beyond-actM (H-gen j β F.jβ) {M = T₁} β≤p be₁
          be₃ = Beyond-actM (H-gen α ℓ′ F.αℓ′) {M = T₂} ℓ′≤p be₂
          be₄ = Beyond-actM (X-gen α β αβ) {M = T₃} β≤p be₃
          be₅ = Beyond-actM (H-gen α ℓ′ F.αℓ′) {M = T₄} ℓ′≤p be₄
          be₆ = Beyond-actM (H-gen j β F.jβ) {M = T₅} β≤p be₅
          be₇ = Beyond-actM (H-gen β ℓ′ βℓ′) {M = T₆} ℓ′≤p be₆
          l₂ = lv T₂ be₂ _ c₂ (nodd< _ _ _ _ (even-s₂j A₂))
          l₃ = lv T₃ be₃ _ c₃ (nodd< _ _ _ _ (even-s₂j A₂))
          l₄ = lv T₄ be₄ _ c₄ (nodd< _ _ _ _ (even-s₂j A₂))
          l₅ = lv T₅ be₅ _ c₅ (nodd< _ _ _ _ (even-s₂j A₂))
          l₆ = lv T₆ be₆ _ c₆ (nodd< _ _ _ _ (even-y₁ a c))
          l₇ = lv T₇ be₇ _ c₇ (nodd< _ _ _ _ (even-y₁ a c))

        -- The second path, when a + b + c + d = δ + δ² A₂.
        path₁ : δ²ᶻ ∣ (A ZR.- δᶻ) → Square G s o
        path₁ (A₂ , eA) = finish (HardRel.B₁ jα αβ βℓ′) (HardRel.bottom₁ jα αβ βℓ′)
                            (((l₀ , l₁) , ((((l₁ , l₂) , (l₂ , l₃)) , (l₃ , l₄)) , (l₄ , l₅)) , (l₅ , l₆)) , (l₆ , l₇))
                            l₇
          where
          d′ = dd₁ a b c A₂
          ed′ : d ≡ d′
          ed′ = ≡.trans (ZG.solve 4 (λ a b c d → d := (con δᶻ :+ (((a :+ b) :+ (c :+ d)) :- con δᶻ)) :- (a :+ b :+ c))
                                    ≡.refl a b c d)
                        (≡.cong (λ y → δᶻ ZR.+ y ZR.- (a ZR.+ b ZR.+ c)) eA)
          module P = F.Path₁ k a b c A₂
          T₂ = actM (H-gen α β αβ) T₁
          T₃ = actM (H-gen j ℓ′ F.jℓ′) T₂
          T₄ = actM (X-gen α ℓ′ F.αℓ′) T₃
          T₅ = actM (H-gen j ℓ′ F.jℓ′) T₄
          T₆ = actM (H-gen α β αβ) T₅
          T₇ = actM (H-gen β ℓ′ βℓ′) T₆
          c₁ : col T₁ p ≡ scV k (F.Nv (y₁ a b) (y₂ a b) (y₁ c d′) (y₂ c d′))
          c₁ = ≡.subst (λ x → col T₁ p ≡ scV k (F.Nv (y₁ a b) (y₂ a b) (y₁ c x) (y₂ c x))) ed′ col₁
          c₂ = ≡.trans (col-actM (H-gen α β αβ) T₁ p) (≡.trans (≡.cong (actV (H-gen α β αβ)) c₁) P.step₂)
          c₃ = ≡.trans (col-actM (H-gen j ℓ′ F.jℓ′) T₂ p) (≡.trans (≡.cong (actV (H-gen j ℓ′ F.jℓ′)) c₂) P.step₃)
          c₄ = ≡.trans (col-actM (X-gen α ℓ′ F.αℓ′) T₃ p) (≡.trans (≡.cong (actV (X-gen α ℓ′ F.αℓ′)) c₃) P.step₄)
          c₅ = ≡.trans (col-actM (H-gen j ℓ′ F.jℓ′) T₄ p) (≡.trans (≡.cong (actV (H-gen j ℓ′ F.jℓ′)) c₄) P.step₅)
          c₆ = ≡.trans (col-actM (H-gen α β αβ) T₅ p) (≡.trans (≡.cong (actV (H-gen α β αβ)) c₅) P.step₆)
          c₇ = ≡.trans (col-actM (H-gen β ℓ′ βℓ′) T₆ p)
                 (≡.trans (≡.cong (actV (H-gen β ℓ′ βℓ′)) c₆) (F.step₇ k a b c d′))
          be₂ = Beyond-actM (H-gen α β αβ) {M = T₁} β≤p be₁
          be₃ = Beyond-actM (H-gen j ℓ′ F.jℓ′) {M = T₂} ℓ′≤p be₂
          be₄ = Beyond-actM (X-gen α ℓ′ F.αℓ′) {M = T₃} ℓ′≤p be₃
          be₅ = Beyond-actM (H-gen j ℓ′ F.jℓ′) {M = T₄} ℓ′≤p be₄
          be₆ = Beyond-actM (H-gen α β αβ) {M = T₅} β≤p be₅
          be₇ = Beyond-actM (H-gen β ℓ′ βℓ′) {M = T₆} ℓ′≤p be₆
          l₂ = lv T₂ be₂ _ c₂ (nodd< _ _ _ _ (even-y₁ a b))
          l₃ = lv T₃ be₃ _ c₃ (nodd< _ _ _ _ (even-t₃j a b c A₂))
          l₄ = lv T₄ be₄ _ c₄ (nodd< _ _ _ _ (even-t₃j a b c A₂))
          l₅ = lv T₅ be₅ _ c₅ (nodd< _ _ _ _ (even-y₁ a c))
          l₆ = lv T₆ be₆ _ c₆ (nodd< _ _ _ _ (even-y₁ a c))
          l₇ = lv T₇ be₇ _ c₇ (nodd< _ _ _ _ (even-y₁ a c))

        byA : (b₀ : Bool) → oddᶻ A ≡ b₀ → Square G s o
        byA true od = ⊥-elim (t≢f (≡.trans (≡.sym od) evenA))
          where
          t≢f : true ≢ false
          t≢f ()
        byA false ev = by-c1 (c1 (par A)) ≡.refl
          where
          by-c1 : (b₁ : Bool) → c1 (par A) ≡ b₁ → Square G s o
          by-c1 false e1 = path₀ (δ²∣-par A (≡.trans (oddP-par A) ev) e1)
          by-c1 true e1 = path₁ (δ²∣-δ A (≡.trans (oddP-par A) ev) e1)
