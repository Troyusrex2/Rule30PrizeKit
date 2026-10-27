# Fixed cut-31 packet extraction

Scope fixed before computation: use the SAME single 3-gap gate as root's `period5-carrier-defect-20261027T0820`, with black positions ..., -5, 0, 3, 8, ... . Compute ONLY X31 and X32 on the cone necessary for t=-25,...,0, and extract

    A=X31, B=X32, delta=B XOR a(t+2), L=A AND NOT B.

No new depths beyond32, different defect histories, period/width scans, or enlarged trace. The prior source computed a much larger enclosing rectangle; it did not save every cell, so this phase recomputes just the needed finite cone, with an independent recursive scalar comparison.

Before computation, locality sharpens the proposed conservative support bound[-30,5] to[-25,0]: a agrees with the past period10 carrier for every t<=5 and with the future phase-shifted carrier for every t>=1. X32 reads a[t..t+31]. On both pure carriers B=a(t+2) and L=0. Thus both delta and L vanish outside[-25,0]. The finite extraction, together with this paper bound, describes the full packet.

Compare the exact identity delta(t+1) XOR delta(t) XOR L(t) against root's already saved base-depth2 residual. Check only the natural unforced/one-parity-black shape after shear u=t+2. Analyze separated short events with q>=3 by locality, without computing additional histories. Packet front motion is not a finite-support descent.
