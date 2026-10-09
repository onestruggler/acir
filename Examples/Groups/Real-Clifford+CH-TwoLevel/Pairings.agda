------------------------------------------------------------------------
-- Presentations of groups
--
-- The three pairings of four indices a < b < c < d,
--
--   Π_A = H_[a,b] H_[c,d],   Π_B = H_[a,c] H_[b,d],   Π_C = H_[a,d] H_[b,c],
--
-- and the relations between them that the four-entry diamond uses:
-- (f1) and (f2) of the paper (Propositions A.11 and A.12), derived
-- here as there, from (d3) and the relations (a)–(d):
--
--   (f1)  Π_A Π_B ≈ Π_B Π_A,          (f2)  (Π_B Π_C)² ≈ X_[a,b] X_[c,d].
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Pairings {n : ℕ} where

open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
import Relation.Binary.Reasoning.Setoid as SR

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (<⇒≢)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (X-X ; H-H ; Z-Z ; comm-gen)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

------------------------------------------------------------------------
-- (d2) and (c1), rearranged

module _ {a b : Fin n} (ab : a < b) where

  -- H Z_[b] H = X.
  HZH : H a b ab • Zʷ b • H a b ab ≈ X a b ab
  HZH = begin
    H a b ab • Zʷ b • H a b ab        ≈⟨ cright axiom (d2 ab) ⟩
    H a b ab • H a b ab • X a b ab    ≈⟨ sym assoc ⟩
    (H a b ab • H a b ab) • X a b ab  ≈⟨ cleft H-H ab ⟩
    ε • X a b ab                      ≈⟨ left-unit ⟩
    X a b ab                          ∎

  -- H X = Z_[b] H.
  HX : H a b ab • X a b ab ≈ Zʷ b • H a b ab
  HX = sym (axiom (d2 ab))

  -- X Z_[b] = Z_[a] X.
  XZ : X a b ab • Zʷ b ≈ Zʷ a • X a b ab
  XZ = sym (axiom (c1 ab))

------------------------------------------------------------------------
-- Four sorted indices

module Sorted {a b c d : Fin n} (ab : a < b) (bc : b < c) (cd : c < d) where

  ac : a < c
  ac = FinP.<-trans ab bc

  bd : b < d
  bd = FinP.<-trans bc cd

  ad : a < d
  ad = FinP.<-trans ab bd

  private
    sym≢ : ∀ {x y : Fin n} → x ≢ y → y ≢ x
    sym≢ ne e = ne (≡.sym e)
    a≢b = <⇒≢ ab ; a≢c = <⇒≢ ac ; a≢d = <⇒≢ ad
    b≢c = <⇒≢ bc ; b≢d = <⇒≢ bd ; c≢d = <⇒≢ cd
    b≢a = sym≢ a≢b ; c≢a = sym≢ a≢c ; d≢a = sym≢ a≢d
    c≢b = sym≢ b≢c ; d≢b = sym≢ b≢d ; d≢c = sym≢ c≢d

  Hab = H a b ab
  Hcd = H c d cd
  Hac = H a c ac
  Hbd = H b d bd
  Had = H a d ad
  Hbc = H b c bc
  Xab = X a b ab
  Xcd = X c d cd
  Xbd = X b d bd
  Zb = Zʷ b
  Zd = Zʷ d

  ΠA ΠB ΠC : Word (Gen n)
  ΠA = Hab • Hcd
  ΠB = Hac • Hbd
  ΠC = Had • Hbc

  ----------------------------------------------------------------------
  -- Commutations of disjoint generators

  bd-ac : Hbd • Hac ≈ Hac • Hbd
  bd-ac = comm-gen (H-gen b d bd) (H-gen a c ac) ((b≢a ∷ b≢c ∷ []) ∷ (d≢a ∷ d≢c ∷ []) ∷ [])

  cd-ab : Hcd • Hab ≈ Hab • Hcd
  cd-ab = comm-gen (H-gen c d cd) (H-gen a b ab) ((c≢a ∷ c≢b ∷ []) ∷ (d≢a ∷ d≢b ∷ []) ∷ [])

  bc-ad : Hbc • Had ≈ Had • Hbc
  bc-ad = comm-gen (H-gen b c bc) (H-gen a d ad) ((b≢a ∷ b≢d ∷ []) ∷ (c≢a ∷ c≢d ∷ []) ∷ [])

  ab-Xcd : Hab • Xcd ≈ Xcd • Hab
  ab-Xcd = comm-gen (H-gen a b ab) (X-gen c d cd) ((a≢c ∷ a≢d ∷ []) ∷ (b≢c ∷ b≢d ∷ []) ∷ [])

  Zd-ac : Zd • Hac ≈ Hac • Zd
  Zd-ac = comm-gen (Z-gen d) (H-gen a c ac) ((d≢a ∷ d≢c ∷ []) ∷ [])

  Zb-cd : Zb • Hcd ≈ Hcd • Zb
  Zb-cd = comm-gen (Z-gen b) (H-gen c d cd) ((b≢c ∷ b≢d ∷ []) ∷ [])

  -- The pairing words are involutions.
  ΠB² : ΠB • ΠB ≈ ε
  ΠB² = begin
    (Hac • Hbd) • (Hac • Hbd)    ≈⟨ by-assoc auto ⟩
    Hac • (Hbd • Hac) • Hbd      ≈⟨ cright cleft bd-ac ⟩
    Hac • (Hac • Hbd) • Hbd      ≈⟨ by-assoc auto ⟩
    (Hac • Hac) • (Hbd • Hbd)    ≈⟨ cong (H-H ac) (H-H bd) ⟩
    ε • ε                        ≈⟨ left-unit ⟩
    ε                            ∎

  ΠC² : ΠC • ΠC ≈ ε
  ΠC² = begin
    (Had • Hbc) • (Had • Hbc)    ≈⟨ by-assoc auto ⟩
    Had • (Hbc • Had) • Hbc      ≈⟨ cright cleft bc-ad ⟩
    Had • (Had • Hbc) • Hbc      ≈⟨ by-assoc auto ⟩
    (Had • Had) • (Hbc • Hbc)    ≈⟨ cong (H-H ad) (H-H bc) ⟩
    ε • ε                        ≈⟨ left-unit ⟩
    ε                            ∎

  ----------------------------------------------------------------------
  -- (f1)

  private
    T : Word (Gen n)
    T = Hcd • Hac • Hbd

    d3′ : T ^ 4 ≈ Hab • Hcd
    d3′ = axiom (d3 ab ac bd cd b≢c)

    RT : (Hbd • Hac • Hcd) • T ≈ ε
    RT = begin
      (Hbd • Hac • Hcd) • (Hcd • Hac • Hbd)  ≈⟨ by-assoc auto ⟩
      Hbd • Hac • (Hcd • Hcd) • Hac • Hbd    ≈⟨ cright cright cleft H-H cd ⟩
      Hbd • Hac • ε • Hac • Hbd              ≈⟨ cright cright left-unit ⟩
      Hbd • Hac • Hac • Hbd                  ≈⟨ cright sym assoc ⟩
      Hbd • (Hac • Hac) • Hbd                ≈⟨ cright cleft H-H ac ⟩
      Hbd • ε • Hbd                          ≈⟨ cright left-unit ⟩
      Hbd • Hbd                              ≈⟨ H-H bd ⟩
      ε                                      ∎

  f1′ : Hab • Hcd • Hac • Hbd ≈ Hbd • Hac • Hcd • Hab
  f1′ = begin
    Hab • Hcd • Hac • Hbd                            ≈⟨ by-assoc auto ⟩
    (Hab • Hcd) • (Hac • Hbd)                        ≈⟨ cleft sym d3′ ⟩
    T ^ 4 • (Hac • Hbd)                              ≈⟨ by-assoc auto ⟩
    (T • T • T • Hcd) • ((Hac • Hbd) • (Hac • Hbd))  ≈⟨ cright ΠB² ⟩
    (T • T • T • Hcd) • ε                            ≈⟨ right-unit ⟩
    T • T • T • Hcd                                  ≈⟨ sym left-unit ⟩
    ε • (T • T • T • Hcd)                            ≈⟨ cleft sym RT ⟩
    ((Hbd • Hac • Hcd) • T) • (T • T • T • Hcd)      ≈⟨ by-assoc auto ⟩
    (Hbd • Hac • Hcd) • (T ^ 4 • Hcd)                ≈⟨ cright cleft d3′ ⟩
    (Hbd • Hac • Hcd) • ((Hab • Hcd) • Hcd)          ≈⟨ by-assoc auto ⟩
    (Hbd • Hac • Hcd • Hab) • (Hcd • Hcd)            ≈⟨ cright H-H cd ⟩
    (Hbd • Hac • Hcd • Hab) • ε                      ≈⟨ right-unit ⟩
    Hbd • Hac • Hcd • Hab                            ∎

  -- Π_A and Π_B commute.
  f1 : ΠA • ΠB ≈ ΠB • ΠA
  f1 = begin
    (Hab • Hcd) • (Hac • Hbd)    ≈⟨ by-assoc auto ⟩
    Hab • Hcd • Hac • Hbd        ≈⟨ f1′ ⟩
    Hbd • Hac • Hcd • Hab        ≈⟨ by-assoc auto ⟩
    (Hbd • Hac) • (Hcd • Hab)    ≈⟨ cong bd-ac cd-ab ⟩
    (Hac • Hbd) • (Hab • Hcd)    ∎

  ----------------------------------------------------------------------
  -- (f2)

  private
    -- H_[a,d] H_[b,c] = X_[c,d] H_[a,c] H_[b,d] X_[c,d].
    s1 : Had • Hbc ≈ Xcd • Hac • Hbd • Xcd
    s1 = begin
      Had • Hbc                          ≈⟨ cright sym left-unit ⟩
      Had • ε • Hbc                      ≈⟨ cright cleft sym (X-X cd) ⟩
      Had • (Xcd • Xcd) • Hbc            ≈⟨ by-assoc auto ⟩
      (Had • Xcd) • (Xcd • Hbc)          ≈⟨ cong (axiom (c5 ac cd)) (sym (axiom (c5 bc cd))) ⟩
      (Xcd • Hac) • (Hbd • Xcd)          ≈⟨ by-assoc auto ⟩
      Xcd • Hac • Hbd • Xcd              ∎

    -- X_[c,d] = H_[a,b] H_[c,d] Z_[d] H_[c,d] H_[a,b].
    s2 : Xcd ≈ Hab • Hcd • Zd • Hcd • Hab
    s2 = begin
      Xcd                                ≈⟨ sym left-unit ⟩
      ε • Xcd                            ≈⟨ cleft sym (H-H ab) ⟩
      (Hab • Hab) • Xcd                  ≈⟨ assoc ⟩
      Hab • (Hab • Xcd)                  ≈⟨ cright ab-Xcd ⟩
      Hab • (Xcd • Hab)                  ≈⟨ cright cleft sym (HZH cd) ⟩
      Hab • ((Hcd • Zd • Hcd) • Hab)     ≈⟨ by-assoc auto ⟩
      Hab • Hcd • Zd • Hcd • Hab         ∎

    -- Π_B Π_A = Π_A Π_B, and with Π_A as H_[c,d] H_[a,b].
    f1-r : (Hac • Hbd) • (Hab • Hcd) ≈ (Hab • Hcd) • (Hac • Hbd)
    f1-r = sym f1
    f1-l : (Hcd • Hab) • (Hac • Hbd) ≈ (Hac • Hbd) • (Hcd • Hab)
    f1-l = begin
      (Hcd • Hab) • (Hac • Hbd)          ≈⟨ cleft cd-ab ⟩
      (Hab • Hcd) • (Hac • Hbd)          ≈⟨ f1 ⟩
      (Hac • Hbd) • (Hab • Hcd)          ≈⟨ cright sym cd-ab ⟩
      (Hac • Hbd) • (Hcd • Hab)          ∎

    -- H_[a,c] H_[b,d] Z_[d] H_[a,c] H_[b,d] = H_[b,d] Z_[d] H_[b,d].
    s3 : Hac • Hbd • Zd • Hac • Hbd ≈ Hbd • Zd • Hbd
    s3 = begin
      Hac • Hbd • Zd • Hac • Hbd           ≈⟨ cright cright sym assoc ⟩
      Hac • Hbd • (Zd • Hac) • Hbd         ≈⟨ cright cright cleft Zd-ac ⟩
      Hac • Hbd • (Hac • Zd) • Hbd         ≈⟨ by-assoc auto ⟩
      Hac • (Hbd • Hac) • Zd • Hbd         ≈⟨ cright cleft bd-ac ⟩
      Hac • (Hac • Hbd) • Zd • Hbd         ≈⟨ by-assoc auto ⟩
      (Hac • Hac) • Hbd • Zd • Hbd         ≈⟨ cleft H-H ac ⟩
      ε • Hbd • Zd • Hbd                   ≈⟨ left-unit ⟩
      Hbd • Zd • Hbd                       ∎

  -- The word Π_B Π_C, rewritten.
  G≈ : ΠB • ΠC ≈ Hab • Hcd • Xbd • Zd • Hcd • Hab
  G≈ = begin
    (Hac • Hbd) • (Had • Hbc)
      ≈⟨ cright s1 ⟩
    (Hac • Hbd) • (Xcd • Hac • Hbd • Xcd)
      ≈⟨ cright cleft s2 ⟩
    (Hac • Hbd) • ((Hab • Hcd • Zd • Hcd • Hab) • Hac • Hbd • Xcd)
      ≈⟨ by-assoc auto ⟩
    ((Hac • Hbd) • (Hab • Hcd)) • Zd • ((Hcd • Hab) • (Hac • Hbd)) • Xcd
      ≈⟨ cong f1-r (cright cleft f1-l) ⟩
    ((Hab • Hcd) • (Hac • Hbd)) • Zd • ((Hac • Hbd) • (Hcd • Hab)) • Xcd
      ≈⟨ by-assoc auto ⟩
    Hab • Hcd • (Hac • Hbd • Zd • Hac • Hbd) • Hcd • Hab • Xcd
      ≈⟨ cright cright cleft s3 ⟩
    Hab • Hcd • (Hbd • Zd • Hbd) • Hcd • Hab • Xcd
      ≈⟨ cright cright cleft HZH bd ⟩
    Hab • Hcd • Xbd • Hcd • Hab • Xcd
      ≈⟨ cright cright cright cright ab-Xcd ⟩
    Hab • Hcd • Xbd • Hcd • Xcd • Hab
      ≈⟨ cright cright cright sym assoc ⟩
    Hab • Hcd • Xbd • (Hcd • Xcd) • Hab
      ≈⟨ cright cright cright cleft HX cd ⟩
    Hab • Hcd • Xbd • (Zd • Hcd) • Hab
      ≈⟨ cright cright cright assoc ⟩
    Hab • Hcd • Xbd • Zd • Hcd • Hab
      ∎

  -- (f2): (Π_B Π_C)² = X_[a,b] X_[c,d].
  f2 : (ΠB • ΠC) • (ΠB • ΠC) ≈ Xab • Xcd
  f2 = begin
    (ΠB • ΠC) • (ΠB • ΠC)
      ≈⟨ cong G≈ G≈ ⟩
    (Hab • Hcd • Xbd • Zd • Hcd • Hab) • (Hab • Hcd • Xbd • Zd • Hcd • Hab)
      ≈⟨ by-assoc auto ⟩
    Hab • Hcd • Xbd • Zd • Hcd • (Hab • Hab) • Hcd • Xbd • Zd • Hcd • Hab
      ≈⟨ cright cright cright cright cright cleft H-H ab ⟩
    Hab • Hcd • Xbd • Zd • Hcd • ε • Hcd • Xbd • Zd • Hcd • Hab
      ≈⟨ cright cright cright cright cright left-unit ⟩
    Hab • Hcd • Xbd • Zd • Hcd • Hcd • Xbd • Zd • Hcd • Hab
      ≈⟨ cright cright cright cright sym assoc ⟩
    Hab • Hcd • Xbd • Zd • (Hcd • Hcd) • Xbd • Zd • Hcd • Hab
      ≈⟨ cright cright cright cright cleft H-H cd ⟩
    Hab • Hcd • Xbd • Zd • ε • Xbd • Zd • Hcd • Hab
      ≈⟨ cright cright cright cright left-unit ⟩
    Hab • Hcd • Xbd • Zd • Xbd • Zd • Hcd • Hab
      ≈⟨ cright cright sym assoc ⟩
    Hab • Hcd • (Xbd • Zd) • Xbd • Zd • Hcd • Hab
      ≈⟨ cright cright cleft XZ bd ⟩
    Hab • Hcd • (Zb • Xbd) • Xbd • Zd • Hcd • Hab
      ≈⟨ by-assoc auto ⟩
    Hab • Hcd • Zb • (Xbd • Xbd) • Zd • Hcd • Hab
      ≈⟨ cright cright cright cleft X-X bd ⟩
    Hab • Hcd • Zb • ε • Zd • Hcd • Hab
      ≈⟨ cright cright cright left-unit ⟩
    Hab • Hcd • Zb • Zd • Hcd • Hab
      ≈⟨ cright sym assoc ⟩
    Hab • (Hcd • Zb) • Zd • Hcd • Hab
      ≈⟨ cright cleft sym Zb-cd ⟩
    Hab • (Zb • Hcd) • Zd • Hcd • Hab
      ≈⟨ by-assoc auto ⟩
    Hab • Zb • (Hcd • Zd • Hcd) • Hab
      ≈⟨ cright cright cleft HZH cd ⟩
    Hab • Zb • Xcd • Hab
      ≈⟨ cright cright sym ab-Xcd ⟩
    Hab • Zb • Hab • Xcd
      ≈⟨ by-assoc auto ⟩
    (Hab • Zb • Hab) • Xcd
      ≈⟨ cleft HZH ab ⟩
    Xab • Xcd
      ∎

  -- (f2), as the diamond uses it: Π_B Π_C = X_[a,b] X_[c,d] Π_C Π_B.
  f2′ : ΠB • ΠC ≈ (Xab • Xcd) • ΠC • ΠB
  f2′ = begin
    ΠB • ΠC                                      ≈⟨ sym right-unit ⟩
    (ΠB • ΠC) • ε                                ≈⟨ cright sym ΠB² ⟩
    (ΠB • ΠC) • (ΠB • ΠB)                        ≈⟨ cright cleft sym right-unit ⟩
    (ΠB • ΠC) • ((ΠB • ε) • ΠB)                  ≈⟨ cright cleft cright sym ΠC² ⟩
    (ΠB • ΠC) • ((ΠB • (ΠC • ΠC)) • ΠB)          ≈⟨ by-assoc auto ⟩
    ((ΠB • ΠC) • (ΠB • ΠC)) • (ΠC • ΠB)          ≈⟨ cleft f2 ⟩
    (Xab • Xcd) • ΠC • ΠB                        ∎
