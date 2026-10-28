# Where the generators read and write.  Run them from any directory; the
# environment variables redirect the output (to compare a regeneration with
# the committed files) and the intermediate pickles.
import os

HERE = os.path.dirname(os.path.abspath(__file__))
# The folder QCert/CliffordT2, where the generated Lean modules go.
OUT = os.environ.get('CT2_OUT', os.path.join(HERE, '..'))
# Intermediate results: cliffnf.pkl, eqcerts.pkl (not committed).
WORK = os.environ.get('CT2_WORK', os.path.join(HERE, 'work'))
# The `anc/` directory of the arXiv source of 2204.02217 (not committed).
ANC = os.environ.get('CT2_ANC', os.path.join(HERE, 'anc'))
os.makedirs(WORK, exist_ok=True)
