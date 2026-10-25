"""Rebuild the round-two 1,110-state union reader from the coordinator's own,
unmodified source (left_multi_vacuum_reader.py and its imports), run its
built-in controls, and export T (int16, shape (1110,2)) and the 14 patterns.
Usage: python export_t1110.py <scratch copy of evidence/left-future-history-multi> <outdir>
Run it on a SCRATCH COPY: the package writes nothing here, but keep the
archived evidence untouched."""
import sys, json, os
sys.path.insert(0, sys.argv[1])
import numpy as np
import left_multi_vacuum_reader as m
T, pats, states, c = m.build()
assert c['all_passed'] and c['binary_reader_states'] == 1110
np.save(os.path.join(sys.argv[2], 'T1110.npy'), T)
json.dump([{k: p[k] for k in ['necklace', 'phase', 'transient', 'period', 'left_bits']} for p in pats],
          open(os.path.join(sys.argv[2], 'pats.json'), 'w'))
print(json.dumps(c))
