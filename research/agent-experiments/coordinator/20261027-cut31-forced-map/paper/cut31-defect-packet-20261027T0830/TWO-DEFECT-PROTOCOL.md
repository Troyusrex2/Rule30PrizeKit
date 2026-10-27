# One adjacent short-gap interaction

Authorized after the fixed single packet, before this computation. Keep the single source and PACKET.json unchanged.

The only new history has short-gap starts 0 and 8, with black events

    ..., -10, -5, 0, 3, 8, 11, 16, 21, ... .

This is the q=1 run between two short starts. Use the same cut31 and definitions delta=X32 XOR a(t+2), L=X31 AND NOT X32. Compute only times[-25,16], requiring scalar input[-25,47] through depth32. Compare with XOR sums of the saved single packet at physical translations0 and16. Record every interaction position and its parity. No other gap separation, depth or history will be computed.

Paper bounds precede the calculation: the full two-defect packet is supported in[-25,16]. Its interaction with the XOR sum vanishes outside[-9,0], since the two history agrees with the first single defect through boundary time21 and with the shifted second single defect from time1 onward. The corresponding X32 cones separate at t=-10 and t=1.

A possible uniform formula requires a separate locality proof: individual active corridors are[2e-25,2e], short starts are separated by at least16 physical ticks, and three such intervals cannot share a point. Prove that defects outside an active set cannot alter the local carrier phase of the cone after anchoring its latest/earliest black event. The finite pair test alone is not such a proof. No claim of iteration closure or CQ01Empty follows.
