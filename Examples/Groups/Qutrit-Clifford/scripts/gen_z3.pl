#!/usr/bin/perl
# Generates Examples/Groups/Qutrit-Clifford/Z3.agda: arithmetic modulo 3
# on Fin 3, with its laws proved by enumeration.
use strict; use warnings; use utf8;
binmode STDOUT, ':encoding(UTF-8)';
my @n = ('𝟎', '𝟏', '𝟐');
sub add { ($_[0] + $_[1]) % 3 }
sub mul { ($_[0] * $_[1]) % 3 }

print <<'EOF';
------------------------------------------------------------------------
-- Presentations of groups
--
-- Arithmetic modulo 3
--
-- The phases ω^σ of qutrit Pauli operators, the exponents of X and Z,
-- and the digits of basis vectors are elements of ℤ/3, here Fin 3 with
-- addition and multiplication by tables.  The laws are checked case by
-- case (the module is generated: scratchpad qt/gen_z3.pl).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Qutrit-Clifford.Z3 where

open import Data.Fin.Base using (Fin ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans ; sym ; cong)

Z3 : Set
Z3 = Fin 3

pattern 𝟎 = zero
pattern 𝟏 = suc zero
pattern 𝟐 = suc (suc zero)

infixl 6 _⊞_
infixl 7 _⊠_
infix  8 ⊟_

EOF

print "_⊞_ : Z3 → Z3 → Z3\n";
for my $a (0..2) { for my $b (0..2) { print "$n[$a] ⊞ $n[$b] = $n[add($a,$b)]\n"; } }
print "\n_⊠_ : Z3 → Z3 → Z3\n";
for my $a (0..2) { for my $b (0..2) { print "$n[$a] ⊠ $n[$b] = $n[mul($a,$b)]\n"; } }
print "\n⊟_ : Z3 → Z3\n";
for my $a (0..2) { print "⊟ $n[$a] = $n[(3 - $a) % 3]\n"; }

sub law1 { my ($name, $ty, $f) = @_;
  print "\n$name : $ty\n";
  for my $a (0..2) { print "$name $n[$a] = refl\n"; } }
sub law2 { my ($name, $ty) = @_;
  print "\n$name : $ty\n";
  for my $a (0..2) { for my $b (0..2) { print "$name $n[$a] $n[$b] = refl\n"; } } }
sub law3 { my ($name, $ty) = @_;
  print "\n$name : $ty\n";
  for my $a (0..2) { for my $b (0..2) { for my $c (0..2) {
    print "$name $n[$a] $n[$b] $n[$c] = refl\n"; } } } }

law1('⊞-identityʳ', '∀ a → a ⊞ 𝟎 ≡ a');
law1('⊞-identityˡ', '∀ a → 𝟎 ⊞ a ≡ a');
law1('⊞-inverseʳ', '∀ a → a ⊞ ⊟ a ≡ 𝟎');
law1('⊟-twice', '∀ a → 𝟐 ⊠ a ≡ ⊟ a');
law1('⊠-one', '∀ a → 𝟏 ⊠ a ≡ a');
law2('⊞-comm', '∀ a b → a ⊞ b ≡ b ⊞ a');
law2('⊠-comm', '∀ a b → a ⊠ b ≡ b ⊠ a');
law2('⊞-cancelʳ', '∀ a b → a ⊞ b ⊞ ⊟ b ≡ a');
law2('⊟-⊞', '∀ a b → ⊟ (a ⊞ b) ≡ ⊟ a ⊞ ⊟ b');
law2('⊟-⊠', '∀ a b → ⊟ (a ⊠ b) ≡ ⊟ a ⊠ b');
law3('⊞-assoc', '∀ a b c → a ⊞ b ⊞ c ≡ a ⊞ (b ⊞ c)');
law3('⊠-assoc', '∀ a b c → a ⊠ b ⊠ c ≡ a ⊠ (b ⊠ c)');
law3('⊠-distribˡ', '∀ a b c → a ⊠ (b ⊞ c) ≡ a ⊠ b ⊞ a ⊠ c');

print <<'EOF';

-- Equal sums with a common summand have equal other summands.
⊞-cancel : ∀ a a' b → a ⊞ b ≡ a' ⊞ b → a ≡ a'
⊞-cancel a a' b e = trans (sym (⊞-cancelʳ a b)) (trans (cong (_⊞ ⊟ b) e) (⊞-cancelʳ a' b))
EOF
