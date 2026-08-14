------------------------------------------------------------------------
-- Presentations of groups
--
-- A factor set from generator data.
--
-- Given two presented groups — K = ⟨ Y | R ⟩, required to be abelian,
-- and Q = ⟨ X | S ⟩ — and an action φ of Q on K, a factor set for φ is a
-- map on WORDS satisfying the four conditions of IsNormalisedCocycle
-- (ForStdlib.Algebra.Construct.FactorSetExtension).  This module builds
-- one from data on the GENERATORS: a map
--
--     G : X → Word X → Word Y
--
-- saying what correction a single quotient generator carries against a
-- word, extended to
--
--     f ε        v = ε
--     f [ a ]ʷ   v = G a v
--     f (u • u') v = (f u u' ⁻¹ • act u (f u' v)) • f u (u' • v).
--
-- The third clause is the cocycle identity itself, solved for its second
-- term.  Since Word is the free monoid — u • v always exposes that
-- clause — the identity then holds for ALL words by construction, with
-- no hypothesis on G whatsoever (`f-cocycle` below): the two sides
-- differ by f u v • f u v ⁻¹.  Normalisation on the left is likewise
-- definitional.
--
-- What the generator data has to supply is the rest:
--
--   * G-ε    : G a ε ≈ ε              — normalisation on generators;
--   * G-cong : G a respects ≈ in its word argument;
--   * f-axiom: each relator of S carries the same correction on either
--              side, ∀ v → f u v ≈ f u' v for u === v in S.
--
-- From these, f-cong follows in both arguments, and with it f-εʳ.  The
-- second-argument congruence is a structural induction on the first
-- argument; the first-argument congruence is an induction on the
-- derivation of u ≈ u′, and each of its cases — cong, assoc, the two
-- units, axiom — reduces to those two, which is what keeps it
-- well-founded.
--
-- K must be abelian, and the module takes that in the form the relation
-- set R can actually provide: `gen-comm`, that any two GENERATORS
-- commute.  `word-comm` lifts it to words, and that is what makes K an
-- AbelianGroup — the kernel of a factor-set extension has to be one.
--
-- The final section, `Pairs`, narrows the data further to a map on
-- pairs of generators, f₀ : X → X → Word Y, by extending it letterwise.
-- That is a genuine choice — the cocycle identity leaves
-- f [ a ]ʷ (v • v′) free — and it is the one that makes f
-- bimultiplicative, as the Weyl cocycle ½·sform is.  It pays for itself:
-- normalisation becomes definitional and G-cong drops to a condition on
-- the relators of S.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Presentation.Construct.Properties.CocycleGen where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
open import Level using (0ℓ)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)

open import ForStdlib.Algebra.Construct.SemiDirectProduct using (Action)
open import ForStdlib.Algebra.Construct.FactorSetExtension
  using (IsNormalisedCocycle ; FactorSet)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

------------------------------------------------------------------------
-- The two presented groups

module _ {X Y : Set}
         (ΓK : WRel Y) (ΓQ : WRel X)
         (glK : Grouplike ΓK) (glQ : Grouplike ΓQ)
         (gen-comm : ∀ (x y : Y) →
                     PB._≈_ ΓK ([ x ]ʷ • [ y ]ʷ) ([ y ]ʷ • [ x ]ʷ))
         where

  private
    module KB = PB ΓK
    module QB = PB ΓQ
    module KG = Group-Lemmas ΓK glK
    module QG = Group-Lemmas ΓQ glQ

  ----------------------------------------------------------------------
  -- K is commutative
  --
  -- Generators commute by hypothesis, so words do: split each word and
  -- push the letters of one past the other.

  word-comm : ∀ (u v : Word Y) → KB._≈_ (u • v) (v • u)
  word-comm [ x ]ʷ  [ y ]ʷ   = gen-comm x y
  word-comm [ x ]ʷ  ε        = KB.trans KB.right-unit (KB.sym KB.left-unit)
  word-comm [ x ]ʷ  (v • w)  =
    KB.trans (KB.sym KB.assoc)
      (KB.trans (KB.cong (word-comm [ x ]ʷ v) KB.refl)
        (KB.trans KB.assoc
          (KB.trans (KB.cong KB.refl (word-comm [ x ]ʷ w))
                    (KB.sym KB.assoc))))
  word-comm ε       v        = KB.trans KB.left-unit (KB.sym KB.right-unit)
  word-comm (u • u') v       =
    KB.trans KB.assoc
      (KB.trans (KB.cong KB.refl (word-comm u' v))
        (KB.trans (KB.sym KB.assoc)
          (KB.trans (KB.cong (word-comm u v) KB.refl) KB.assoc)))

  -- The kernel: words over Y modulo R, an abelian group.
  K : AbelianGroup 0ℓ 0ℓ
  K = record
    { isAbelianGroup = record
      { isGroup = Group.isGroup KG.•-ε-group
      ; comm    = word-comm
      }
    }

  -- The quotient: words over X modulo S.
  Q : Group 0ℓ 0ℓ
  Q = QG.•-ε-group

  ----------------------------------------------------------------------
  -- The action

  module _ (φ : Action (AbelianGroup.rawMonoid K) (Group.rawMonoid Q)) where

    private
      module K = AbelianGroup K
      module Q = Group Q
    open Action φ
    open ≈-Reasoning K.setoid

    private
      -- Acting is a monoid endomorphism of K, hence preserves inverses.
      module MM = MonoidMorphisms (Group.rawMonoid (AbelianGroup.group K))
                                  (Group.rawMonoid (AbelianGroup.group K))

      act-mon : ∀ u → MM.IsMonoidHomomorphism (act u)
      act-mon u = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = act-cong Q.refl }
          ; homo              = act-∙-homo u
          }
        ; ε-homo = act-ε-homo u
        }

    act-⁻¹ : ∀ u w → act u (w K.⁻¹) K.≈ (act u w) K.⁻¹
    act-⁻¹ u =
      GroupMorphisms.IsGroupHomomorphism.⁻¹-homo
        (isMonoidHomomorphism⇒isGroupHomomorphism
          (AbelianGroup.group K) (AbelianGroup.group K) (act-mon u))

    private
      -- Rearrangements in the abelian group K, for the assoc case of
      -- f-cong₁.  Both sides of that case are products of the same six
      -- factors, two of which are inverse to one another.

      interchange : ∀ a b c d →
                    (a K.∙ b) K.∙ (c K.∙ d) K.≈ (a K.∙ c) K.∙ (b K.∙ d)
      interchange a b c d = begin
        (a K.∙ b) K.∙ (c K.∙ d)  ≈⟨ K.assoc a b (c K.∙ d) ⟩
        a K.∙ (b K.∙ (c K.∙ d))  ≈⟨ K.∙-congˡ (K.sym (K.assoc b c d)) ⟩
        a K.∙ ((b K.∙ c) K.∙ d)  ≈⟨ K.∙-congˡ (K.∙-congʳ (K.comm b c)) ⟩
        a K.∙ ((c K.∙ b) K.∙ d)  ≈⟨ K.∙-congˡ (K.assoc c b d) ⟩
        a K.∙ (c K.∙ (b K.∙ d))  ≈⟨ K.sym (K.assoc a c (b K.∙ d)) ⟩
        (a K.∙ c) K.∙ (b K.∙ d)  ∎

      -- (((a ⁻¹ ∙ b) ∙ c) ⁻¹ ∙ d) ∙ ((a ⁻¹ ∙ e) ∙ g)
      --   ≈ (c ⁻¹ ∙ ((b ⁻¹ ∙ d) ∙ e)) ∙ g
      -- The two a's cancel; what is left is the same product on both
      -- sides, reassociated.
      shuffle : ∀ a b c d e g →
                ((((a K.⁻¹ K.∙ b) K.∙ c) K.⁻¹ K.∙ d) K.∙ ((a K.⁻¹ K.∙ e) K.∙ g))
                K.≈ ((c K.⁻¹ K.∙ ((b K.⁻¹ K.∙ d) K.∙ e)) K.∙ g)
      shuffle a b c d e g = begin
        (((a K.⁻¹ K.∙ b) K.∙ c) K.⁻¹ K.∙ d) K.∙ ((a K.⁻¹ K.∙ e) K.∙ g)
          ≈⟨ K.∙-congʳ (K.∙-congʳ inv-expand) ⟩
        (((a K.∙ b K.⁻¹) K.∙ c K.⁻¹) K.∙ d) K.∙ ((a K.⁻¹ K.∙ e) K.∙ g)
          ≈⟨ collect ⟩
        (a K.∙ a K.⁻¹) K.∙ ((((b K.⁻¹ K.∙ c K.⁻¹) K.∙ d) K.∙ e) K.∙ g)
          ≈⟨ K.∙-congʳ (K.inverseʳ a) ⟩
        K.ε K.∙ ((((b K.⁻¹ K.∙ c K.⁻¹) K.∙ d) K.∙ e) K.∙ g)
          ≈⟨ K.identityˡ _ ⟩
        (((b K.⁻¹ K.∙ c K.⁻¹) K.∙ d) K.∙ e) K.∙ g
          ≈⟨ K.∙-congʳ regroup ⟩
        (c K.⁻¹ K.∙ ((b K.⁻¹ K.∙ d) K.∙ e)) K.∙ g ∎
        where
        -- The syntactic inverse reverses a product on the nose, so the
        -- left-hand side already reads c ⁻¹ ∙ (b ⁻¹ ∙ (a ⁻¹) ⁻¹).
        inv-expand : ((a K.⁻¹ K.∙ b) K.∙ c) K.⁻¹ K.≈ (a K.∙ b K.⁻¹) K.∙ c K.⁻¹
        inv-expand = begin
          ((a K.⁻¹ K.∙ b) K.∙ c) K.⁻¹
            ≈⟨ K.∙-congˡ (K.∙-congˡ KG.⁻¹-involutive) ⟩
          c K.⁻¹ K.∙ (b K.⁻¹ K.∙ a)
            ≈⟨ K.∙-congˡ (K.comm (b K.⁻¹) a) ⟩
          c K.⁻¹ K.∙ (a K.∙ b K.⁻¹)
            ≈⟨ K.comm _ _ ⟩
          (a K.∙ b K.⁻¹) K.∙ c K.⁻¹ ∎

        -- Both factors give up their a, and the interchange law brings
        -- the two together.
        collect : (((a K.∙ b K.⁻¹) K.∙ c K.⁻¹) K.∙ d) K.∙ ((a K.⁻¹ K.∙ e) K.∙ g)
                  K.≈ (a K.∙ a K.⁻¹)
                       K.∙ ((((b K.⁻¹ K.∙ c K.⁻¹) K.∙ d) K.∙ e) K.∙ g)
        collect = begin
          (((a K.∙ b K.⁻¹) K.∙ c K.⁻¹) K.∙ d) K.∙ ((a K.⁻¹ K.∙ e) K.∙ g)
            ≈⟨ K.∙-cong pull-a pull-a⁻¹ ⟩
          (a K.∙ ((b K.⁻¹ K.∙ c K.⁻¹) K.∙ d)) K.∙ (a K.⁻¹ K.∙ (e K.∙ g))
            ≈⟨ interchange a ((b K.⁻¹ K.∙ c K.⁻¹) K.∙ d) (a K.⁻¹) (e K.∙ g) ⟩
          (a K.∙ a K.⁻¹) K.∙ (((b K.⁻¹ K.∙ c K.⁻¹) K.∙ d) K.∙ (e K.∙ g))
            ≈⟨ K.∙-congˡ (K.sym (K.assoc _ e g)) ⟩
          (a K.∙ a K.⁻¹) K.∙ ((((b K.⁻¹ K.∙ c K.⁻¹) K.∙ d) K.∙ e) K.∙ g) ∎
          where
          pull-a : ((a K.∙ b K.⁻¹) K.∙ c K.⁻¹) K.∙ d
                   K.≈ a K.∙ ((b K.⁻¹ K.∙ c K.⁻¹) K.∙ d)
          pull-a = begin
            ((a K.∙ b K.⁻¹) K.∙ c K.⁻¹) K.∙ d
              ≈⟨ K.∙-congʳ (K.assoc a (b K.⁻¹) (c K.⁻¹)) ⟩
            (a K.∙ (b K.⁻¹ K.∙ c K.⁻¹)) K.∙ d
              ≈⟨ K.assoc a (b K.⁻¹ K.∙ c K.⁻¹) d ⟩
            a K.∙ ((b K.⁻¹ K.∙ c K.⁻¹) K.∙ d) ∎
          pull-a⁻¹ : (a K.⁻¹ K.∙ e) K.∙ g K.≈ a K.⁻¹ K.∙ (e K.∙ g)
          pull-a⁻¹ = K.assoc (a K.⁻¹) e g

        regroup : ((b K.⁻¹ K.∙ c K.⁻¹) K.∙ d) K.∙ e
                  K.≈ c K.⁻¹ K.∙ ((b K.⁻¹ K.∙ d) K.∙ e)
        regroup = begin
          ((b K.⁻¹ K.∙ c K.⁻¹) K.∙ d) K.∙ e
            ≈⟨ K.∙-congʳ (K.∙-congʳ (K.comm (b K.⁻¹) (c K.⁻¹))) ⟩
          ((c K.⁻¹ K.∙ b K.⁻¹) K.∙ d) K.∙ e
            ≈⟨ K.∙-congʳ (K.assoc (c K.⁻¹) (b K.⁻¹) d) ⟩
          (c K.⁻¹ K.∙ (b K.⁻¹ K.∙ d)) K.∙ e
            ≈⟨ K.assoc (c K.⁻¹) (b K.⁻¹ K.∙ d) e ⟩
          c K.⁻¹ K.∙ ((b K.⁻¹ K.∙ d) K.∙ e) ∎

    ------------------------------------------------------------------
    -- The extension of the generator data

    module _ (G : X → Word X → Word Y) where

      f : Word X → Word X → Word Y
      f ε        v = ε
      f [ a ]ʷ   v = G a v
      f (u • u') v = ((f u u') K.⁻¹ K.∙ act u (f u' v)) K.∙ f u (u' • v)

      ----------------------------------------------------------------
      -- The cocycle identity, unconditionally
      --
      -- f (u • v) w is the third clause, which is exactly this identity
      -- solved for it; so the identity holds for every triple, whatever
      -- G is.

      f-cocycle : ∀ u v w →
                  (f u v K.∙ f (u • v) w) K.≈ (act u (f v w) K.∙ f u (v • w))
      f-cocycle u v w = begin
        f u v K.∙ (((f u v) K.⁻¹ K.∙ act u (f v w)) K.∙ f u (v • w))
          ≈⟨ K.sym (K.assoc _ _ _) ⟩
        (f u v K.∙ ((f u v) K.⁻¹ K.∙ act u (f v w))) K.∙ f u (v • w)
          ≈⟨ K.∙-congʳ (K.sym (K.assoc _ _ _)) ⟩
        ((f u v K.∙ (f u v) K.⁻¹) K.∙ act u (f v w)) K.∙ f u (v • w)
          ≈⟨ K.∙-congʳ (K.∙-congʳ (K.inverseʳ _)) ⟩
        (K.ε K.∙ act u (f v w)) K.∙ f u (v • w)
          ≈⟨ K.∙-congʳ (K.identityˡ _) ⟩
        act u (f v w) K.∙ f u (v • w) ∎

      -- Normalisation on the left is the first clause.
      f-εˡ : ∀ v → f ε v K.≈ K.ε
      f-εˡ v = K.refl

      ----------------------------------------------------------------
      -- What the generator data has to supply

      module _ (G-cong : ∀ a {v v'} → v Q.≈ v' → G a v K.≈ G a v')
               (G-ε    : ∀ a → G a ε K.≈ K.ε)
               where

        -- Congruence in the acted-on argument, by structural induction
        -- on the OTHER one: the recursion never inspects it.
        f-cong₂ : ∀ u {v v'} → v Q.≈ v' → f u v K.≈ f u v'
        f-cong₂ ε        e = K.refl
        f-cong₂ [ a ]ʷ   e = G-cong a e
        f-cong₂ (u • u') e =
          K.∙-cong (K.∙-congˡ (act-cong Q.refl (f-cong₂ u' e)))
                   (f-cong₂ u (QB.cong QB.refl e))

        -- …and normalisation on the right follows.
        f-εʳ : ∀ u → f u ε K.≈ K.ε
        f-εʳ ε      = K.refl
        f-εʳ [ a ]ʷ = G-ε a
        f-εʳ (u • u') = begin
          ((f u u') K.⁻¹ K.∙ act u (f u' ε)) K.∙ f u (u' • ε)
            ≈⟨ K.∙-congʳ (K.∙-congˡ (act-cong Q.refl (f-εʳ u'))) ⟩
          ((f u u') K.⁻¹ K.∙ act u K.ε) K.∙ f u (u' • ε)
            ≈⟨ K.∙-congʳ (K.∙-congˡ (act-ε-homo u)) ⟩
          ((f u u') K.⁻¹ K.∙ K.ε) K.∙ f u (u' • ε)
            ≈⟨ K.∙-congʳ (K.identityʳ _) ⟩
          (f u u') K.⁻¹ K.∙ f u (u' • ε)
            ≈⟨ K.∙-congˡ (f-cong₂ u QB.right-unit) ⟩
          (f u u') K.⁻¹ K.∙ f u u'
            ≈⟨ K.inverseˡ _ ⟩
          K.ε ∎

        ----------------------------------------------------------------
        -- Congruence in the acting argument
        --
        -- Induction on the derivation of u ≈ u′.  Every case reduces to
        -- f-cong₂ and to the induction hypotheses, so nothing here
        -- climbs back up a derivation.

        module _ (f-axiom : ∀ {u u' : Word X} → ΓQ u u' →
                            ∀ v → f u v K.≈ f u' v)
                 where

          f-cong₁ : ∀ {u u'} → u Q.≈ u' → ∀ v → f u v K.≈ f u' v
          f-cong₁ QB.refl          v = K.refl
          f-cong₁ (QB.sym e)       v = K.sym (f-cong₁ e v)
          f-cong₁ (QB.trans e₁ e₂) v = K.trans (f-cong₁ e₁ v) (f-cong₁ e₂ v)
          f-cong₁ (QB.axiom r)     v = f-axiom r v

          f-cong₁ (QB.cong {w} {w'} {y} {y'} e₁ e₂) v =
            K.∙-cong
              (K.∙-cong (K.⁻¹-cong (K.trans (f-cong₁ e₁ y) (f-cong₂ w' e₂)))
                        (act-cong e₁ (f-cong₁ e₂ v)))
              (K.trans (f-cong₁ e₁ (y • v))
                       (f-cong₂ w' (QB.cong e₂ QB.refl)))

          f-cong₁ (QB.left-unit {w}) v = begin
            (K.ε K.⁻¹ K.∙ act ε (f w v)) K.∙ ε
              ≈⟨ K.identityʳ _ ⟩
            K.ε K.⁻¹ K.∙ act ε (f w v)
              ≈⟨ K.∙-congʳ (KG.⁻¹-ε) ⟩
            K.ε K.∙ act ε (f w v)
              ≈⟨ K.identityˡ _ ⟩
            act ε (f w v)
              ≈⟨ act-identity _ ⟩
            f w v ∎

          f-cong₁ (QB.right-unit {w}) v = begin
            ((f w ε) K.⁻¹ K.∙ act w (f ε v)) K.∙ f w (ε • v)
              ≈⟨ K.∙-congʳ (K.∙-congʳ (K.⁻¹-cong (f-εʳ w))) ⟩
            (K.ε K.⁻¹ K.∙ act w K.ε) K.∙ f w (ε • v)
              ≈⟨ K.∙-congʳ (K.∙-congˡ (act-ε-homo w)) ⟩
            (K.ε K.⁻¹ K.∙ K.ε) K.∙ f w (ε • v)
              ≈⟨ K.∙-congʳ (K.trans (K.identityʳ _) KG.⁻¹-ε) ⟩
            K.ε K.∙ f w (ε • v)
              ≈⟨ K.identityˡ _ ⟩
            f w (ε • v)
              ≈⟨ f-cong₂ w QB.left-unit ⟩
            f w v ∎

          f-cong₁ (QB.assoc {w} {y} {z}) v = begin
            ((f (w • y) z) K.⁻¹ K.∙ act (w • y) (f z v)) K.∙ f (w • y) (z • v)
              ≈⟨ K.∙-congʳ (K.∙-congˡ (act-compose w y (f z v))) ⟩
            ((f (w • y) z) K.⁻¹ K.∙ act w (act y (f z v))) K.∙ f (w • y) (z • v)
              ≈⟨ shuffle (f w y) (act w (f y z)) (f w (y • z))
                         (act w (act y (f z v))) (act w (f y (z • v)))
                         (f w (y • (z • v))) ⟩
            ((f w (y • z)) K.⁻¹
              K.∙ (((act w (f y z)) K.⁻¹ K.∙ act w (act y (f z v)))
                    K.∙ act w (f y (z • v))))
              K.∙ f w (y • (z • v))
              ≈⟨ K.∙-congʳ (K.∙-congˡ (K.sym act-inner)) ⟩
            ((f w (y • z)) K.⁻¹ K.∙ act w (f (y • z) v)) K.∙ f w (y • (z • v))
              ≈⟨ K.∙-congˡ (f-cong₂ w (QB.sym QB.assoc)) ⟩
            ((f w (y • z)) K.⁻¹ K.∙ act w (f (y • z) v)) K.∙ f w ((y • z) • v) ∎
            where
            act-inner : act w (f (y • z) v)
                        K.≈ (((act w (f y z)) K.⁻¹ K.∙ act w (act y (f z v)))
                              K.∙ act w (f y (z • v)))
            act-inner = begin
              act w (((f y z) K.⁻¹ K.∙ act y (f z v)) K.∙ f y (z • v))
                ≈⟨ act-∙-homo w _ _ ⟩
              act w ((f y z) K.⁻¹ K.∙ act y (f z v)) K.∙ act w (f y (z • v))
                ≈⟨ K.∙-congʳ (act-∙-homo w _ _) ⟩
              (act w ((f y z) K.⁻¹) K.∙ act w (act y (f z v)))
                K.∙ act w (f y (z • v))
                ≈⟨ K.∙-congʳ (K.∙-congʳ (act-⁻¹ w (f y z))) ⟩
              (((act w (f y z)) K.⁻¹ K.∙ act w (act y (f z v)))
                K.∙ act w (f y (z • v))) ∎

          ----------------------------------------------------------------
          -- The factor set

          f-cong : ∀ {u u' v v'} → u Q.≈ u' → v Q.≈ v' → f u v K.≈ f u' v'
          f-cong {u} {u'} {v} {v'} eu ev =
            K.trans (f-cong₁ eu v) (f-cong₂ u' ev)

          isNormalisedCocycle : IsNormalisedCocycle K Q φ f
          isNormalisedCocycle = record
            { f-cong  = f-cong
            ; f-εˡ    = f-εˡ
            ; f-εʳ    = f-εʳ
            ; cocycle = f-cocycle
            }

          factorSet : FactorSet K Q φ
          factorSet = record
            { f                   = f
            ; isNormalisedCocycle = isNormalisedCocycle
            }

    ------------------------------------------------------------------
    -- Generator pairs
    --
    -- G's second argument can be narrowed from Word X to X, at the cost
    -- of one choice.  The cocycle identity does NOT determine
    -- f [ a ]ʷ (v • v′): it holds by construction whatever that value
    -- is, so nothing forces it.  Extending letterwise,
    --
    --     pair-word a (v • v′) = pair-word a v • pair-word a v′,
    --
    -- is the choice that makes f bimultiplicative — with the twist, it
    -- gives f (u • u′) v ≈ act u (f u′ v) • f u v and
    -- f u (v • v′) ≈ f u v • f u v′ — and it is the one the Weyl cocycle
    -- ½·sform makes, that form being bilinear.
    --
    -- What it buys: normalisation is then free, and the congruence
    -- G-cong drops to a condition on the RELATORS of S, proved here by
    -- induction on the derivation.  So from
    --
    --     f₀ : X → X → Word Y
    --
    -- the whole factor set needs only two relator-level hypotheses, one
    -- per argument.

    module Pairs (f₀ : X → X → Word Y) where

      pair-word : X → Word X → Word Y
      pair-word a ε        = ε
      pair-word a [ c ]ʷ   = f₀ a c
      pair-word a (v • v') = pair-word a v • pair-word a v'

      -- Normalisation, on the nose.
      pair-word-ε : ∀ a → pair-word a ε K.≈ K.ε
      pair-word-ε a = K.refl

      module _ (pair-axiom : ∀ a {v v'} → ΓQ v v' →
                             pair-word a v K.≈ pair-word a v')
               where

        -- Letterwise extension turns the monoid laws of Q into those of
        -- K, so only the relators are left to assume.
        pair-word-cong : ∀ a {v v'} → v Q.≈ v' →
                         pair-word a v K.≈ pair-word a v'
        pair-word-cong a QB.refl          = K.refl
        pair-word-cong a (QB.sym e)       = K.sym (pair-word-cong a e)
        pair-word-cong a (QB.trans e₁ e₂) =
          K.trans (pair-word-cong a e₁) (pair-word-cong a e₂)
        pair-word-cong a (QB.cong e₁ e₂)  =
          K.∙-cong (pair-word-cong a e₁) (pair-word-cong a e₂)
        pair-word-cong a QB.assoc         = K.assoc _ _ _
        pair-word-cong a QB.left-unit     = K.identityˡ _
        pair-word-cong a QB.right-unit    = K.identityʳ _
        pair-word-cong a (QB.axiom r)     = pair-axiom a r

        module _ (f-axiom : ∀ {u u' : Word X} → ΓQ u u' →
                            ∀ v → f pair-word u v K.≈ f pair-word u' v)
                 where

          pairFactorSet : FactorSet K Q φ
          pairFactorSet =
            factorSet pair-word pair-word-cong pair-word-ε f-axiom
