"""Per-development settings for gen_toppad.py."""
from gen_toppad import header

CONFIGS = {}


def cfg(name, **kw):
    if 'rel_prefix' in kw:
        kw['rel-prefix'] = kw.pop('rel_prefix')
    kw.setdefault('rel', 'SRel')
    kw.setdefault('rel-op', kw['rel'])
    kw.setdefault('gate', 'Gate')
    kw.setdefault('srel', '_SRel,_===_')
    kw.setdefault('lift', 'srel')
    CONFIGS[name] = kw


cfg('Real-Clifford',
    src='Examples/Groups/Real-Clifford/Syntactics.agda',
    out='Examples/Groups/Real-Clifford/TopPad.agda',
    grouplike='grouplike',
    header=header("Makary, Ross and Selinger's real Clifford relations (R1–R16)",
                  'Examples.Groups.Real-Clifford.TopPad',
                  'open import Examples.Groups.Real-Clifford.Syntactics\n\nopen Circuit.TopPad Gate using (_⇓)'))

cfg('Qubit-Clifford',
    src='Examples/Groups/Qubit-Clifford/Syntactics.agda',
    out='Examples/Groups/Qubit-Clifford/TopPad.agda',
    grouplike='grouplike',
    header=header("Selinger's Clifford relations (C1–C15)",
                  'Examples.Groups.Qubit-Clifford.TopPad',
                  'open import Examples.Groups.Qubit-Clifford.Syntactics\n\nopen Circuit.TopPad Gate using (_⇓)'))

cfg('Clifford+CS',
    src='Examples/Groups/Clifford+CS/Syntactics.agda',
    out='Examples/Groups/Clifford+CS/TopPad.agda',
    grouplike='grouplike',
    header=header("Bian and Selinger's Clifford+CS relations",
                  'Examples.Groups.Clifford+CS.TopPad',
                  'open import Examples.Groups.Clifford+CS.Syntactics\n\nopen Circuit.TopPad Gate using (_⇓)'))

PRIME = ' (p-2 : ℕ) (p-prime : Prime (2+ p-2))'
PRIME_IMPORTS = 'open import Data.Nat using (2+)\nopen import Data.Nat.Primality using (Prime)\n\n'

cfg('Selinger',
    src='Examples/Groups/Clifford/Qubit/Selinger/Figure8.agda',
    out='Examples/Groups/Clifford/Qubit/Selinger/TopPad.agda',
    rel='Sel', gate='ExactGate', srel='_Sel,_===_', grouplike='grouplike',
    header=header("Selinger's Figure 8, C1–C15",
                  'Examples.Groups.Clifford.Qubit.Selinger.TopPad',
                  PRIME_IMPORTS + 'open import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime\n\nopen Circuit.TopPad ExactGate using (_⇓)',
                  params=PRIME))

cfg('Selinger2',
    src='Examples/Groups/Clifford/Qubit/Selinger2/Figure8.agda',
    out='Examples/Groups/Clifford/Qubit/Selinger2/TopPad.agda',
    rel='Sel', gate='ExactGate', srel='_Sel,_===_', grouplike='grouplike',
    header=header("Selinger's Figure 8, C1–C15",
                  'Examples.Groups.Clifford.Qubit.Selinger2.TopPad',
                  'open import Examples.Groups.Clifford.Qubit.Selinger2.Figure8\n\nopen Circuit.TopPad ExactGate using (_⇓)'))

cfg('Figure8-Mod-Scalar',
    src='Examples/Groups/ProjectiveClifford/Qubit/Selinger/Figure8-Mod-Scalar.agda',
    out='Examples/Groups/ProjectiveClifford/Qubit/Selinger/TopPad.agda',
    rel='Sel', gate='SympGate', srel='_Sel,_===_', lift='Fig8.srel',
    header=header("Selinger's Figure 8 without its scalar",
                  'Examples.Groups.ProjectiveClifford.Qubit.Selinger.TopPad',
                  PRIME_IMPORTS + 'open import Examples.Groups.Symplectic.Syntactics p-2 p-prime using (module Symplectic)\nopen Symplectic\nopen import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime as Fig8\n\nopen Circuit.TopPad SympGate using (_⇓)',
                  params=PRIME))

cfg('CNOT+Dihedral',
    src='Examples/Groups/CNOT+Dihedral/Syntactics.agda',
    out='Examples/Groups/CNOT+Dihedral/TopPad.agda',
    prop='SWAP-gate', lift='srel (srel {})', grouplike='grouplike',
    header=header("Amy, Chen and Ross's CNOT-dihedral relations (R₁–R₁₃)",
                  'Examples.Groups.CNOT+Dihedral.TopPad',
                  'open import Examples.Groups.CNOT+Dihedral.Syntactics\n\nopen Circuit.TopPad Gate using (_⇓)',
                  prop=True))

SYMP_IMPORTS = ('open import ForStdlib.Data.Fin.Mod\nopen PrimeModulus p-2 p-prime\n'
                'open import Examples.Groups.Symplectic.Syntactics.Gates p-2 p-prime\n'
                'open Symplectic\n'
                'open Symplectic-GroupLike using (grouplike)\n\n'
                'open Circuit.TopPad SympGate using (_⇓)\n'
                'open import Circuit.TopPad.Closed SympGate using (⇓-same)')

STUCK_NOTE = ("Powers whose exponent is not a numeral (S ^ p, S^ k) do not compute "
              "under ⇓, so the padded rules and the rules ⇓'d go through "
              "Circuit.TopPad.Closed's ⇓-same.")


def qualify(mod):
    return lambda s: '(' + mod + '.' + s[1:] if s.startswith('(') else mod + '.' + s


cfg('Symplectic',
    src='Examples/Groups/Symplectic/Syntactics/Gates.agda',
    out='Examples/Groups/Symplectic/Syntactics/TopPad.agda',
    gate='SympGate', srel='Base._SRel,_===_', rel_prefix='Base._SRel,_===_',
    wrap=qualify('Base'),
    stuck=True, grouplike='grouplike',
    header=header("The symplectic relations of Syntactics.Gates",
                  'Examples.Groups.Symplectic.Syntactics.TopPad',
                  SYMP_IMPORTS, params=PRIME, note=STUCK_NOTE))

QUPIT_PRE = ('open import Data.Fin using (toℕ)\n'
             'open import Data.Nat using (ℕ ; suc)\n'
             'open import Data.Nat.Primality using (Prime)\n'
             'open import Data.Product using (_,_ ; ∃)\n'
             'open import Relation.Binary.PropositionalEquality using (_≡_)\n\n'
             'open import ForStdlib.Data.Fin.Mod\n'
             'open import ForStdlib.Data.Fin.Mod.Prime.Fermat\n'
             'open import Notations\n\n')

QUPIT_PARAMS = ('\n  (p-3 : ℕ)\n  (let p-2 = ₁₊ p-3)\n  (p-prime : Prime (suc (₁₊ p-2)))\n'
                '  (let open PrimeModulus\' p-2 p-prime)\n  (g*@(g , g≠0) : ℤ* ₚ)\n'
                '  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)\n ')

QUPIT_ARGS = 'p-3 p-prime g* g-gen'


def qupit(name, dirname, title, glmod, glname, inner='Clifford-Relations',
          root='Examples/Groups/ProjectiveClifford/Qupit/'):
    path = root + dirname
    modname = (root + dirname).replace('/', '.')
    imports = (f'open Primitive-Root-Modp\' g* g-gen\n'
               f'open import {modname}.Syntactics {QUPIT_ARGS}\n'
               f'open {inner}\n'
               f'open import {modname}.{glmod} {QUPIT_ARGS} using (module {glname})\n'
               f'open {glname} using (grouplike)\n\n'
               'open Circuit.TopPad SympGate using (_⇓)\n'
               'open import Circuit.TopPad.Closed SympGate using (⇓-same)')
    cfg(name, src=path + '/Syntactics.agda', out=path + '/TopPad.agda',
        gate='SympGate', srel='Base._SRel,_===_', rel_prefix='Base._SRel,_===_',
        wrap=qualify('Base'), stuck=True, grouplike='grouplike',
        header=header(title, modname + '.TopPad', imports, params=QUPIT_PARAMS,
                      pre=QUPIT_PRE, note=STUCK_NOTE))


qupit('Paper-V0', 'Paper-V0', "Figure 1 with the multiplier over R (Paper-V0)",
      'Lemmas', 'Paper-GroupLike')
qupit('Paper-V1', 'Paper-V1', "Figure 1 with the multiplier over S (Paper-V1)",
      'Lemmas.GroupLike', 'Paper-GroupLike')
qupit('Simplified-V1', 'Simplified-V1', "The simplified qupit Clifford relations (Simplified-V1)",
      'Lemmas', 'Clifford-GroupLike')
V1 = 'Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1'
V2 = 'Examples.Groups.ProjectiveClifford.Qupit.Simplified-V2'
cfg('Simplified-V2',
    src='Examples/Groups/ProjectiveClifford/Qupit/Simplified-V2/Syntactics.agda',
    out='Examples/Groups/ProjectiveClifford/Qupit/Simplified-V2/TopPad.agda',
    gate='SympGate', srel='Base._SRel,_===_', rel_prefix='Base._SRel,_===_',
    wrap=qualify('Base'), stuck=True, grouplike='grouplike',
    **{'pre-defs': [
        "-- Simplified-Relations' own two words, which it keeps private.",
        'Wg : ∀ {n} → Word (Gen (₁₊ n))',
        'Wg = S ^ toℕ (g* .proj₁) • H • S ^ toℕ ((g* ⁻¹) .proj₁) • H •',
        '     S ^ toℕ (g* .proj₁) • H',
        '',
        'zX : ℕ',
        'zX = toℕ ((g* .proj₁ + (- 1ₚ)) * 1/2)',
        '']},
    header=header("The simplified qupit Clifford relations (Simplified-V2)",
                  V2 + '.TopPad',
                  "open Primitive-Root-Modp' g* g-gen\n"
                  f'open import {V1}.Syntactics {QUPIT_ARGS}\n'
                  'open Clifford-Relations hiding\n'
                  '  ( _QRel,_===_ ; order-S ; order-H ; M-power ; semi-MR ; order-SH\n'
                  '  ; comm-HHSHHS ; semi-M↑CZ ; semi-M↓CZ ; rel-X↑-CZ ; rel-X↓-CZ\n'
                  '  ; order-CZ ; comm-CZ-S↓ ; comm-CZ-S↑ ; selinger-c10 ; selinger-c11\n'
                  '  ; selinger-c12 ; selinger-c13 ; selinger-c14 ; selinger-c15\n'
                  '  ; comm-H ; comm-S ; comm-CZ ; cong↑ ; lemma-cong↑ ; srel ; comm₁\n'
                  '  ; comm₂ ; module Base )\n'
                  f'open import {V2}.Syntactics {QUPIT_ARGS}\n'
                  'open Simplified-Relations\n'
                  f'open import {V2}.Structural {QUPIT_ARGS}\n'
                  '  using (module Simplified-GroupLike-S)\n'
                  'open Simplified-GroupLike-S using (grouplike)\n\n'
                  'open Circuit.TopPad SympGate using (_⇓)\n'
                  'open import Circuit.TopPad.Closed SympGate using (⇓-same)',
                  params=QUPIT_PARAMS,
                  pre=QUPIT_PRE.replace('using (_,_ ; ∃)', 'using (_,_ ; ∃ ; proj₁)'),
                  note=STUCK_NOTE))

SIM = 'Examples.Groups.Symplectic.Simplified'
cfg('Symplectic-Simplified',
    src='Examples/Groups/Symplectic/Simplified/Syntactics.agda',
    out='Examples/Groups/Symplectic/Simplified/TopPad.agda',
    gate='SympGate', srel='SimBase._SRel,_===_', rel_prefix='SimBase._SRel,_===_',
    wrap=qualify('SimBase'), stuck=True, grouplike='grouplike',
    header=header("The simplified symplectic relations",
                  SIM + '.TopPad',
                  "open Primitive-Root-Modp' g* g-gen\n"
                  f'open import {SIM}.Syntactics p-2 p-prime g* g-gen\n'
                  'open Symplectic\n'
                  '  hiding (_QRel,_===_ ; srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑)\n'
                  'open Simplified-Relations\n'
                  f'open import {SIM}.Lemmas p-2 p-prime g* g-gen\n'
                  '  using (module Symplectic-Sim-GroupLike)\n'
                  'open Symplectic-Sim-GroupLike using (grouplike)\n\n'
                  'open Circuit.TopPad SympGate using (_⇓)\n'
                  'open import Circuit.TopPad.Closed SympGate using (⇓-same)',
                  params=QUPIT_PARAMS.replace('(p-3 : ℕ)\n  (let p-2 = ₁₊ p-3)', '(p-2 : ℕ)'),
                  pre=QUPIT_PRE, note=STUCK_NOTE))

EXT = 'Examples.Groups.Symplectic.ExtendedGate'
cfg('ExtendedGate',
    src='Examples/Groups/Symplectic/ExtendedGate/Syntactics.agda',
    out='Examples/Groups/Symplectic/ExtendedGate/TopPad.agda',
    rel='Q', srel='_Q,_===_', stuck=True, grouplike='grouplike',
    header=header("The symplectic relations over the extended gates",
                  EXT + '.TopPad',
                  'open import Data.Fin using (toℕ)\n'
                  'open import ForStdlib.Data.Fin.Mod\n'
                  'open PrimeModulus p-2 p-prime\n'
                  f'open import {EXT}.Syntactics p-2 p-prime\n'
                  'open Symplectic-Derived-Gen\n'
                  'open Symplectic-Derived-GroupLike using (grouplike)\n\n'
                  'open Circuit.TopPad Gate using (_⇓)\n'
                  'open import Circuit.TopPad.Closed Gate using (⇓-same)',
                  params=PRIME, note=STUCK_NOTE))

PAULI = 'Examples.Groups.ProjectivePauli'
cfg('Pauli-Alt',
    src='Examples/Groups/ProjectivePauli/Presentation-Alt.agda',
    out='Examples/Groups/ProjectivePauli/TopPad-Alt.agda',
    gate='XZGate', srel='Base._SRel,_===_', rel_prefix='Base._SRel,_===_',
    wrap=qualify('Base'), stuck=True, grouplike='grouplike',
    header=header("The projective Pauli relations of Presentation-Alt",
                  PAULI + '.TopPad-Alt',
                  'open import ForStdlib.Data.Fin.Mod\n'
                  'open PrimeModulus p-2 p-prime\n'
                  f'open import {PAULI}.Presentation-Alt p-2 p-prime\n'
                  'open XZ-GroupLike using (grouplike)\n\n'
                  'open import Circuit.Base XZGate using (Circuit)\n'
                  'open Circuit.TopPad XZGate using (_⇓)\n'
                  'open import Circuit.TopPad.Closed XZGate using (⇓-same)',
                  params=PRIME, note=STUCK_NOTE))

CM1 = 'Examples/Groups/Clifford+MinusOne/Qupit/'
qupit('Figure1-ModScalar', 'Figure1/ModScalar', "Figure 1 with its scalars erased",
      'Lemmas.GroupLike', 'Paper-GroupLike', root=CM1)
qupit('Figure1-MS-ModScalar', 'Figure1-MS/ModScalar',
      "Figure 1 (multiplier conjugating S) with its scalars erased",
      'Lemmas.GroupLike', 'Paper-GroupLike', root=CM1)


def figure1(name, dirname, title, gl):
    mod = (CM1 + dirname).replace('/', '.')
    cfg(name, src=CM1 + dirname + '/Syntactics.agda', out=CM1 + dirname + '/TopPad.agda',
        rel='Fig1', gate='Fig1Gate', srel='_Fig1,_===_', stuck=True, grouplike=gl,
        **{'same-by': 'lemmas', 'pre-defs': [
            '-- The Legendre symbol is a word chosen by a case split on a label,',
            '-- stuck for good: ⇓ goes through it by cases.',
            'legendre-by-⇓ : ∀ {n} {y : ℤ ₚ} (d : Dec (toℕ y ≡ 1)) →',
            '                _⇓ {n} (legendre-by d) ≡ legendre-by d',
            'legendre-by-⇓ (yes _) = Eq.refl',
            'legendre-by-⇓ (no _)  = ⇓-same',
            '',
            '-- (Quoted from the module itself: a goal shows the original, not the',
            '-- copy an applied import makes.)',
            'lemmas : List (Name × Name × ℕ)',
            'lemmas = (quote Figure1.legendre-by , quote legendre-by-⇓ , 1) ∷ []',
            '']},
        header=header(title, mod + '.TopPad',
                      'open import Data.List using (List ; [] ; _∷_)\n'
                      'import Data.Nat as Nat\n'
                      'open import Reflection using (Name)\n'
                      'open import Relation.Nullary using (Dec ; yes ; no)\n'
                      'import Relation.Binary.PropositionalEquality as Eq\n\n'
                      "open Primitive-Root-Modp' g* g-gen\n"
                      f'open import {mod}.Syntactics {QUPIT_ARGS}\n'
                      f'import {CM1.replace("/", ".")}Figure1.Syntactics as Figure1\n'
                      f'open import {CM1.replace("/", ".")}Figure1-MS.FF-Iso {QUPIT_ARGS}\n'
                      f'  using ({gl})\n\n'
                      'open Circuit.TopPad Fig1Gate using (_⇓)\n'
                      'open import Circuit.TopPad.Closed Fig1Gate using (⇓-same ; ⇓-same-by)',
                      params=QUPIT_PARAMS,
                      pre=QUPIT_PRE.replace('using (_,_ ; ∃)', 'using (_×_ ; _,_ ; ∃)'),
                      note=STUCK_NOTE + " The Legendre symbol, chosen by a case split, "
                           "goes through by cases (legendre-by-⇓)."))


figure1('Figure1', 'Figure1', "Figure 1 with its scalar -ω (c0–c15)", 'grouplike-F')
figure1('Figure1-MS', 'Figure1-MS', "Figure 1 with C4 conjugating S (c0–c15)", 'grouplike-F′')

QPA = 'Examples.Groups.Qupit-Phase-Affine'
cfg('Qupit-Phase-Affine',
    src='Examples/Groups/Qupit-Phase-Affine/Syntactics.agda',
    out='Examples/Groups/Qupit-Phase-Affine/TopPad.agda',
    prop='SWAP-gate', lift='srel (srel {})', stuck=True, grouplike='grouplike',
    header=header("Blake's phase-affine relations at every level",
                  QPA + '.TopPad',
                  'open import Data.Product.Base using (proj₁)\n\n'
                  f'open import {QPA}.Field p-2 p-prime\n'
                  '  using (F ; F* ; p ; 0F ; 1F ; 2F ; half ; binom2 ; binom3 ; _+_ ; _*_\n'
                  '        ; -_ ; _-_ ; 1* ; -1* ; _⊛_)\n'
                  f'open import {QPA}.Syntactics p-2 p-prime lv\n'
                  f'open import {QPA}.Basic p-2 p-prime lv using (grouplike)\n\n'
                  'open Circuit.TopPad Gate using (_⇓)\n'
                  'open import Circuit.TopPad.Closed Gate using (⇓-same)',
                  params=' (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ)',
                  pre='open import Data.Nat.Base using (ℕ ; _≤_)\n'
                      'open import Data.Nat.Primality using (Prime)\n'
                      'open import Notations using (₂₊)\n\n',
                  prop=True, note=STUCK_NOTE, options='--without-K --safe'))

RCCH = 'Examples.Groups.Real-Clifford+CH'
cfg('Real-Clifford+CH',
    src='Examples/Groups/Real-Clifford+CH/Syntactics.agda',
    out='Examples/Groups/Real-Clifford+CH/TopPad.agda',
    grouplike='grouplike',
    **{'extra-base': [
           '-- (19) is already on its own wires: the box holds every wire.',
           'box-Zᴮ : ∀ k → (₁₊ (₄₊ k)) Base, Z ↓ • Λ□ (₄₊ k) === Λ□ (₄₊ k) • Z ↓'],
       'extra-defs': [
           '',
           "-- TopWeakening's top is ⇓ (its own copy of _↧), so (19) with an idle",
           "-- wire on top is TopWeakening's top-cong.",
           '↧≡ : (g : Gen n) → g TW.↧ ≡ g ↧',
           '↧≡ (gate₀ h) = Eq.refl',
           '↧≡ (gate₁ h) = Eq.refl',
           '↧≡ (gate₂ h) = Eq.refl',
           '↧≡ (g ↥)     = Eq.cong _↥ (↧≡ g)',
           '',
           'top≡⇓ : (w : Circuit n) → TW.top w ≡ w ⇓',
           'top≡⇓ [ g ]ʷ  = Eq.cong [_]ʷ (↧≡ g)',
           'top≡⇓ ε       = Eq.refl',
           'top≡⇓ (u • t) = Eq.cong₂ _•_ (top≡⇓ u) (top≡⇓ t)',
           '',
           'top-⇓ : (₁₊ n) ⊢ TW.top w ≈ TW.top v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓',
           'top-⇓ {w = w} {v} e =',
           '  Eq.subst₂ (λ a b → _ ⊢ᴸ a ≈ b) (top≡⇓ w) (top≡⇓ v) e'],
       'extra-pad': ['pad (box-Z k) = PB.axiom (TP.srel (box-Zᴮ k))'],
       'extra-unpad': ['unpad (box-Zᴮ k) = PB.axiom (srel (box-Z k))'],
       'extra-srel-⇓': ['srel-⇓ (box-Z k) = top-⇓ (TW.top-cong (PB.axiom (srel (box-Z k))))']},
    header=header("Clément's Figure 4 with the swap rules of Remark 1",
                  RCCH + '.TopPad',
                  'import Relation.Binary.PropositionalEquality as Eq\n'
                  'open Eq using (_≡_)\n\n'
                  f'open import {RCCH}.Syntactics\n'
                  f'import {RCCH}.TopWeakening as TW\n\n'
                  'open Circuit.TopPad Gate using (_↧ ; _⇓)',
                  note="(19), the schema box-Z, is stated on exactly the wires its box "
                       "holds already, so it is a rule on its own wires as it stands; "
                       "with an idle wire on top it is TopWeakening's top-cong."))
