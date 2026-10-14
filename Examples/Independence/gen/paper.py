"""The derivations of Blake's paper, read from its LaTeX source.

A derivation environment is a chain of figures joined by equalities,
each citing the rules of its step (\\eqeqref{a}, \\eqdeuxeqref{a}{b},
\\eqtroiseqref{a}{b}{c}, or a bare = for a rearrangement).  derivations
returns, for each label, the chain as [(figure, [cited labels])]; lines
turns one into derive's lines, reading each figure with figparse and
renaming the cited labels by a fragment's map (a label mapped to None
is a definition of a shortcut, already spelled out, and cites nothing;
one mapped to a list cites each of its names).

The source is the paper's arXiv source unpacked (arXiv:2602.09874);
its directory is SRC below or the environment variable BLAKE_SRC."""
import os
import re
import figparse

SRC = os.environ.get('BLAKE_SRC', '')

TOKEN = re.compile(r'\\tikzfig\{([^}]*)\}|\\eqeqref\{([^}]*)\}|\\eqdeuxeqref\{([^}]*)\}\{([^}]*)\}|'
                   r'\\eqtroiseqref\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}|(?<![\\a-z])=')


def derivations(texfile):
    """{label: [(figure, [labels])]}, the first figure with no labels."""
    tex = open(os.path.join(SRC, texfile), encoding='utf-8').read()
    out = {}
    for m in re.finditer(r'\\begin\{derivation\}\\label\{([^}]*)\}(.*?)\\end\{derivation\}', tex, re.S):
        label, body = m.group(1), m.group(2)
        body = re.sub(r'%[^\n]*', '', body)
        chain = []
        pending = None
        for t in TOKEN.finditer(body):
            if t.group(1) is not None:
                chain.append((t.group(1), pending if chain else None))
                pending = None
            elif t.group(2) is not None:
                pending = [t.group(2)]
            elif t.group(3) is not None:
                pending = [t.group(3), t.group(4)]
            elif t.group(5) is not None:
                pending = [t.group(5), t.group(6), t.group(7)]
            else:
                pending = []
        out[label] = chain
    return out


def figure(name):
    return figparse.parse(os.path.join(SRC, 'figures', name + '.pdf'))


def lines(chain, rename):
    """derive's lines for a chain, labels renamed (None: definitional)."""
    out = []
    for fig, labs in chain:
        if labs is None:
            out.append((figure(fig), None))
            continue
        names = []
        for l in labs:
            r = rename.get(l, l)
            if isinstance(r, list):
                names += r
            elif r is not None:
                names.append(r)
        out.append((figure(fig), names))
    return out
