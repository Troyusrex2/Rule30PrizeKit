# Next experiments: keep the canonical relation

Problem 1 is open. The broad target remains a complete proof or disproof,
not more finite exclusions or another restatement. Existing work, failed
experiments and exact sources are linked from the parent handoff README.

## One precise unbounded target

For U>V>=0, let A(t,p)=cell(U+t,p), B(t,p)=cell(V+t,p), and delta=A XOR B.
All arithmetic below is over F2. Consider a field h satisfying, for every
t>=0 and every integer p,

    h(t+1,p) = h(t,p-1)
             + (1+B(t,p+1))*h(t,p)
             + (1+A(t,p))*h(t,p+1),

    delta(t,p+1)*h(t,p) + delta(t,p)*h(t,p+1) = 0.

Assume h(0,p)=0 whenever delta(0,p)=0, and h(t,0)=0 for every t.
Can one prove h(0,-U)=0, with no bound on U, V or the observation time?
An even stronger version drops the initial subset restriction, retaining
only initial support in [-U,U]; that is not necessary for the prize bridge.

Why this would suffice: an eventual center period P after time V gives the
actual field h=delta for U=V+P. It satisfies the displayed identities, the
subset restriction and zero center observations, while delta(0,-U)=1.
This is a sufficient target, not a proved theorem. Do not assume a uniform
deadline. Finite certificates exist for all 820 canonical pairs through older
time 40 in the recorded common-field construction; they do not prove the
quantifier over all pairs.

Useful new work would construct a uniform adjoint certificate, explain how
canonical seed ancestry prevents an invisible left-edge mode, or refute an
explicitly stated stronger replacement while preserving the actual geometry.
If using a learner, target a falsifiable lemma or certificate construction;
return the extracted mechanism and adversarial tests, not accuracy alone.

## Constraints that must not be dropped

- A and B are the two rows of the SAME single-seed orbit at the specified
  ages. Support geometry or a few canonical edge cells do not replace this.
- h is an auxiliary divided-difference field. Neither h nor delta is
  generally itself a Rule30 history. The catalog's three-history XOR rigidity
  cannot simply be applied to them.
- Four distinct FINITE PHYSICAL histories can form a permanent XOR rectangle.
  The starts {-1}, {0,-1}, {-1,-3}, {0,-1,-3} provide a checked example.
  Its escaping right-edge mode does not refute the canonical target above.
- Infinite-background invisible modes already exist, and short inverse-seam
  escape deadlines fail. Preserve their precise scopes when comparing them.
- Translation-invariant finite-window product parity conservation is already
  classified at every width in PR27. Arbitrary position-dependent one-cell
  old/new parity scores are also trivial under the translated pulse tests.
  These do not exclude all nonlocal ranks or local multipliers for the
  constrained A/B/h system; a new proposal must state its exact premises.
- The catalog already has EdgeObservable -> full Problem 1, stripe trace
  relations, response rewrites, a three-state Mealy model, and the related
  automaton-group formulation. Do not present those rediscoveries as new.

The fixed-depth solver diagnostic and periodic-tail census in this folder
are finite experiments, not Lean premises. The local notebook canary is a
tool test. No new unbounded theorem was obtained in this followup.

## Return multiple responses without collisions

Use the existing response schema and a NEW unique response_id for every
agent/version. Put all findings of one response in its findings array and
number the associated files. Never edit another response, old archive or
coordinator worktree.

- Shared machine: D:\MWB\Rule30\agent-inbox\<response_id>\ ; write READY last.
- GitHub: research/agent-experiments/responses/<response_id>/ in your own
  branch or fork, following the parent handoff's pull-request instructions.

Separate proved statements, exact finite evidence, solver timeouts, failed
hypotheses and proposals. For a proof include exact source hashes, verifier
pin and unchanged checker output, including full kernel replay and axioms.
Do not use sorry, axioms, native_decide, decide +native, bv_decide or kernel
skips. Existing verified results may be cited with their exact source and
scope; unverified outside claims are not proof premises.
