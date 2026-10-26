#!/usr/bin/env python3
"""Mark the code blocks in latexdiff's diff.tex (run by `make diff`).

The submitted version typeset its Agda code as `agdacode` listings; the
revision typesets it with Agda's LaTeX backend (`code` blocks).  The two
never match, so latexdiff sees every listing deleted and every code block
added, but it shows neither: it comments out a deleted verbatim
environment, and an added `code` block (a picture environment to it)
gets no visible markup.  This script restores each deleted listing as a
red block with a red bar and puts a blue bar beside each visible code
block of the revision; the bars sit in the left margin, so the code
keeps its width.  The old listings are typeset line by line in red
typewriter type through the Unicode declarations of agda-style.sty, not
with listings, whose literate table breaks once agda.sty is loaded.
Tables and figures are compared as whole blocks too: restore deleted
floats, distinguish their labels, and mark added/revised captions. Keep
tables and old code lines within the page width.
Usage: diffcode.py diff.tex (edited in place).
"""
import re
import sys

PREAMBLE = r"""\usepackage{framed}%DIF CODE
\usepackage{adjustbox}%DIF CODE
\hypersetup{hypertexnames=false}%DIF CODE
\sloppy\emergencystretch=\linewidth%DIF CODE
\definecolor{DIFcodeadd}{rgb}{0,0,1}%DIF CODE
\definecolor{DIFcodedel}{rgb}{1,0,0}%DIF CODE
\newenvironment{DIFaddcode}{\def\FrameCommand{\hskip-5.5pt{\color{DIFcodeadd}\vrule width 1.5pt}\hspace{4pt}}\MakeFramed{\FrameRestore}}{\endMakeFramed}%DIF CODE
\newenvironment{DIFdelcode}{\par\smallskip\def\FrameCommand{\hskip-5.5pt{\color{DIFcodedel}\vrule width 1.5pt}\hspace{4pt}}\MakeFramed{\FrameRestore}\begingroup\small\ttfamily\color{DIFcodedel}\parindent=0pt\parskip=0pt}{\par\endgroup\endMakeFramed\smallskip}%DIF CODE
\newcommand{\DIFcodeline}[1]{\adjustbox{max width=\linewidth}{#1}\par}%DIF CODE
"""

DELETED = re.compile(r'%DIFDELCMD < \\begin\{agdacode\}(.*?)\n%DIFDELCMD < \\end\{agdacode\}', re.S)
ADDED = re.compile(r'\\begin\{code\}(?!\[hide\])(.*?)\\end\{code\}', re.S)
DELETED_FLOAT = re.compile(
    r'%DIFDELCMD < \\begin\{(table|figure)\}(.*?)'
    r'\n%DIFDELCMD < \\end\{\1\}', re.S)
ADDED_FLOAT = re.compile(
    r'(?<!< )\\begin\{(table|figure)\}(.*?)\\end\{\1\}', re.S)
TABULAR = re.compile(r'\\begin\{tabular\}.*?\\end\{tabular\}', re.S)

ESCAPE = {'\\': r'\textbackslash{}', '{': r'\{', '}': r'\}', '$': r'\$',
          '&': r'\&', '#': r'\#', '%': r'\%', '_': r'\_', '^': r'\^{}',
          '~': r'\textasciitilde{}', ' ': '~', '-': '-{}'}


def line(s):
    return r'\DIFcodeline{' + ''.join(ESCAPE.get(c, c) for c in s.rstrip()) + '}'


def deleted(m):
    lines = [re.sub(r'^%DIFDELCMD <( |$)', '', l) for l in m.group(1).split('\n')]
    # lines[0] is the rest of the \begin line: empty, or an option list
    return ('\n\\begin{DIFdelcode}\n' + '\n'.join(line(l) for l in lines[1:])
            + '\n\\end{DIFdelcode}')


def added(m):
    return '\\begin{DIFaddcode}\n' + m.group(0) + '\n\\end{DIFaddcode}'


path = sys.argv[1]
t = open(path, encoding='utf-8').read()
i = t.index('\n\\begin{document}') + 1
head, body = t[:i], t[i:]
active_labels = set(re.findall(
    r'\\label\{([^}]+)\}', re.sub(r'(?m)^%.*$', '', body)))
old_labels = set()


def float_caption(block, kind, color):
    return block.replace(
        r'\caption{',
        r'\captionsetup{labelfont={color=' + color
        + r'},textfont={color=' + color + r'}}\caption{' + kind + ': ', 1)


def added_float(m):
    return float_caption(m.group(0), 'Added/revised', 'DIFcodeadd')


def deleted_float(m):
    block = re.sub(r'(?m)^%DIFDELCMD < ?', '', m.group(0))
    labels = re.findall(r'\\label\{([^}]+)\}', block)
    old_labels.update(labels)
    block = re.sub(r'\\label\{([^}]+)\}', r'\\label{DIFold:\1}', block)
    # Resolve figure assets in the submitted snapshot, including any
    # figure that retains the same filename in the revision.
    block = block.replace('{figures/', '{submitted/figures/')
    return float_caption(block, 'Deleted', 'DIFcodedel')


# Mark new floats before restoring old ones, so the latter are not
# mistaken for additions. Whole-float matching keeps table cells intact.
body = ADDED_FLOAT.sub(added_float, body)
body, nf = DELETED_FLOAT.subn(deleted_float, body)
for label in old_labels - active_labels:
    body = body.replace(r'\ref{' + label + '}', r'\ref{DIFold:' + label + '}')
body = TABULAR.sub(
    lambda m: r'\begin{adjustbox}{max width=\linewidth}' + '\n'
    + m.group(0) + '\n' + r'\end{adjustbox}', body)
body, nd = DELETED.subn(deleted, body)
body, na = ADDED.subn(added, body)
open(path, 'w', encoding='utf-8').write(head + PREAMBLE + body)
print('diffcode.py: %d deleted listings, %d added code blocks, %d deleted floats'
      % (nd, na, nf))
