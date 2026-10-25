"""Version the terminal-aware reader without modifying the failed baseline."""
import hashlib,json,shutil
from pathlib import Path

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'ordered-reader-v2'
OUT.mkdir(exist_ok=True)
source=(ROOT/'train_ordered_rank_reader.py').read_text(encoding='utf-8')
source=source.replace('its energy is a SUM of squared prefix readouts, not a bounded mean.',
 'its energy sums squared prefix readouts and a squared terminal readout.\nThe terminal readout avoids the independently verified prefix-monotone barrier.')
source=source.replace('nn.init.normal_(self.head.weight,0,.03);',
 'self.terminal_head=nn.Embedding(phases,32);self.terminal_bias=nn.Embedding(phases,1)\n  nn.init.normal_(self.terminal_head.weight,0,.03);nn.init.constant_(self.terminal_bias.weight,1.0)\n  nn.init.normal_(self.head.weight,0,.03);')
source=source.replace('return (score.square()*(words!=4)).sum(-1)+self.constant(phase).flatten().square()',
 '''lengths=(words!=4).sum(-1)
  last=h[torch.arange(len(words),device=words.device),(lengths-1).clamp_min(0)]
  terminal=(last*self.terminal_head(phase)).sum(-1)+self.terminal_bias(phase).flatten()
  terminal=terminal.square()*(lengths>0)
  return (score.square()*(words!=4)).sum(-1)+self.constant(phase).flatten().square()+terminal''')
source=source.replace("p.add_argument('--seconds',type=float,default=165);a=p.parse_args()",
 "p.add_argument('--seconds',type=float,default=165);p.add_argument('--epochs',type=int,default=4000);p.add_argument('--seed',type=int,default=302536);a=p.parse_args()")
source=source.replace('torch.manual_seed(302536);np.random.seed(302536)', 'torch.manual_seed(a.seed);np.random.seed(a.seed)')
source=source.replace('for epoch in range(1000):','for epoch in range(a.epochs):')
source=source.replace("key=(tr['nonfinite']+he['nonfinite'],tr['violations_1e4']+he['violations_1e4'],he['maximum_residual'])",
 "key=(tr['nonfinite'],tr['violations_1e4'],tr['maximum_residual'])")
source=source.replace("'energy':'nonnegative phase constant squared plus sum of squared ordered prefix readouts'",
 "'energy':'nonnegative phase constant squared plus sum of squared ordered prefix readouts plus squared word-dependent terminal readout','version':2,'checkpoint_selection':'training only','seed':a.seed,'requested_epochs':a.epochs,'seconds_budget':a.seconds")
assert source.count('terminal.square()')==1
assert "key=(tr['nonfinite'],tr['violations_1e4'],tr['maximum_residual'])" in source
(OUT/'train_ordered_rank_reader.py').write_text(source,encoding='utf-8',newline='\n')
for n in ['actual-bothzero-ordered.npz','data-manifest.json']:
 shutil.copyfile(ROOT/'order-reader-data'/n,OUT/n)
shutil.copyfile(ROOT/'guard_order_reader_v2_remote.py',OUT/'guard_order_reader_v2_remote.py')
shutil.copyfile(ROOT/'validate_ordered_reader_v2.py',OUT/'validate_ordered_reader_v2.py')
(OUT/'OWNER.txt').write_text('Rule30 terminal-aware ordered rank reader v2; 2026-10-25\n',encoding='utf-8')
(OUT/'README.md').write_text('''# Terminal-aware ordered rank reader V2

The baseline nonnegative prefix sum is impossible: the independently
reconstructed R=0x3496 example has two actual white-spatial transitions with
total reward 1, and the resulting same-phase word extends the original word.
The exact extension is [2,1,0,0]. Lean checks the word extension and the
algebraic contradiction; Python checks physical evolution independently.

V2 adds a squared readout of the last ACTIVE hidden state. Energy remains
nonnegative, but it need not increase under word extension. Padding must not
affect energy. The old source/results are unchanged. This is an architectural
repair, not a claimed universal rank. Training-only checkpoint selection;
the longer selection set from the baseline is now used only for reporting.
Neither finite training nor longer validation can prove an all-length claim.
No Wolfram submission or machine configuration changes are made.
''',encoding='utf-8')
names=['train_ordered_rank_reader.py','guard_order_reader_v2_remote.py','validate_ordered_reader_v2.py','actual-bothzero-ordered.npz','data-manifest.json']
(OUT/'sources.json').write_text(json.dumps({n:hashlib.sha256((OUT/n).read_bytes()).hexdigest() for n in names},indent=2)+'\n',encoding='utf-8')
(OUT/'baseline-provenance.json').write_text(json.dumps({'baseline_source_sha256':hashlib.sha256((ROOT/'train_ordered_rank_reader.py').read_bytes()).hexdigest(),'baseline_guard_sha256':hashlib.sha256((ROOT/'guard_order_reader_remote.py').read_bytes()).hexdigest(),'builder_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'new_architecture_excludes_prefix_monotonicity':True},indent=2)+'\n',encoding='utf-8')
print({'created':str(OUT),'baseline_unchanged':True},flush=True)
