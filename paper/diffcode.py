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
Usage: diffcode.py diff.tex (edited in place).
"""
import re
import sys

PREAMBLE = r"""\usepackage{framed}%DIF CODE
\definecolor{DIFcodeadd}{rgb}{0,0,1}%DIF CODE
\definecolor{DIFcodedel}{rgb}{1,0,0}%DIF CODE
\newenvironment{DIFaddcode}{\def\FrameCommand{\hskip-5.5pt{\color{DIFcodeadd}\vrule width 1.5pt}\hspace{4pt}}\MakeFramed{\FrameRestore}}{\endMakeFramed}%DIF CODE
\newenvironment{DIFdelcode}{\par\smallskip\def\FrameCommand{\hskip-5.5pt{\color{DIFcodedel}\vrule width 1.5pt}\hspace{4pt}}\MakeFramed{\FrameRestore}\begingroup\small\ttfamily\color{DIFcodedel}\parindent=0pt\parskip=0pt}{\par\endgroup\endMakeFramed\smallskip}%DIF CODE
\newcommand{\DIFcodeline}[1]{\mbox{#1}\par}%DIF CODE
"""

DELETED = re.compile(r'%DIFDELCMD < \\begin\{agdacode\}(.*?)\n%DIFDELCMD < \\end\{agdacode\}', re.S)
ADDED = re.compile(r'\\begin\{code\}(?!\[hide\])(.*?)\\end\{code\}', re.S)

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
body, nd = DELETED.subn(deleted, body)
body, na = ADDED.subn(added, body)
open(path, 'w', encoding='utf-8').write(head + PREAMBLE + body)
print('diffcode.py: %d deleted listings, %d added code blocks' % (nd, na))
