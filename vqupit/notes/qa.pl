use strict; use warnings; use utf8;
binmode STDOUT, ':utf8';
my @files = ('main.tex', glob('sections/*.tex'));
my $all = '';
for my $f (@files) { open my $h, '<:utf8', $f or die; local $/; $all .= <$h>; }
my %labels = map { $_ => 1 } ($all =~ /\\label\{([^}]*)\}/g);
my %refs   = map { $_ => 1 } ($all =~ /\\ref\{([^}]*)\}/g);
print "MISSING label: $_\n" for grep { !$labels{$_} } sort keys %refs;
print "unreferenced label: $_\n" for grep { !$refs{$_} } sort keys %labels;
open my $b, '<:utf8', 'refs.bib' or die; my $bib = do { local $/; <$b> };
my %keys = map { $_ => 1 } ($bib =~ /^@\w+\{([^,]+),/mg);
my %cites; for my $c ($all =~ /\\cite\{([^}]*)\}/g) { $cites{$_}=1 for split /\s*,\s*/, $c; }
print "MISSING bib: $_\n" for grep { !$keys{$_} } sort keys %cites;
for my $f ($all =~ /\\(?:ufig|fitfig)(?:\[[^\]]*\])?\{([^}]*)\}/g) { print "MISSING figure: $f\n" unless -f "figures/$f.tikz"; }
open my $s, '<:utf8', 'agda-style.sty' or die; my $sty = do { local $/; <$s> };
my %lit; while ($sty =~ /\{([^{}]+)\}\{\{[^\n]*?\}\}(\d)/g) { $lit{$_}=1 for split //, $1; }
my %decl = map { chr(hex($_)) => 1 } ($sty =~ /DeclareUnicodeCharacter\{([0-9A-Fa-f]+)\}/g);
my %bad;
while ($all =~ /\\begin\{agdacode\}(.*?)\\end\{agdacode\}/gs) { for my $ch (split //, $1) { next if ord($ch) < 128; $bad{"code:$ch (U+".sprintf("%04X",ord $ch).")"}=1 unless $lit{$ch}; } }
while ($all =~ /\\aid\{((?:[^{}]|\{[^{}]*\})*)\}/g) { for my $ch (split //, $1) { next if ord($ch) < 128; $bad{"aid:$ch (U+".sprintf("%04X",ord $ch).")"}=1 unless $decl{$ch}; } }
my $prose = $all; $prose =~ s/\\begin\{agdacode\}.*?\\end\{agdacode\}//gs; $prose =~ s/\\aid\{(?:[^{}]|\{[^{}]*\})*\}//g;
for my $ch (split //, $prose) { next if ord($ch) < 128; $bad{"prose:$ch (U+".sprintf("%04X",ord $ch).")"}=1 unless $decl{$ch}; }
print "UNICODE not covered: $_\n" for sort keys %bad;
print "QA done\n";
