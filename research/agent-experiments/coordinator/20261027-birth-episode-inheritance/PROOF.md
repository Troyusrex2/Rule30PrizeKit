# Proof and scope

Write `F(t,i)` and `G(t,i)` for two Boolean histories satisfying the official physical update

```text
F(t+1,i+1) = F(t,i) XOR (F(t,i+1) OR F(t,i+2)),
```

and similarly for `G`. Column zero is an arbitrary boundary of this positive half-line. Set `h_i(t)=F(t,i) XOR G(t,i)`. A column-one birth at source tick `t` is the transition `h_1(t)=0`, `h_1(t+1)=1`.

## Local death termination

Assume at a source tick `d` that the centers agree, `h_1(d)=1`, `h_1(d+1)=0`, and `h_2(d)=h_2(d+1)=1`. The two local column-one/column-two pairs are complementary. Because the column-one outputs agree under the common center, their OR values must agree; the pairs must therefore be `10` and `01`.

Exchange the two histories if needed and take the first pair to be `10`. Its column-two update is `1 XOR F(d,3)`. The other column-two update is one, so their assumed difference at the next time forces the first output to zero and hence `F(d,3)=1`. The next column-three output in that history is then one, independently of column four. At the following column-two update, both histories therefore have OR input one and the same column-one value. Their outputs agree: `h_2(d+2)=0`.

The formal helper checks all nine local Boolean inputs by ordinary kernel `decide`. The theorem connects it explicitly to `IsR30` at the two successive updates. Only center agreement at `d` is needed, not at `d+1`.

## Finite interval consequence

Suppose `h_2(t)=1` and the centers agree for each integer reading `A <= t <= Z`. If there are two births at `a<b` in that source interval, then `h_1(a+1)=1` while `h_1(b)=0`. A simple induction finds a death source `d` with `a+1 <= d < b`.

Both `d` and `d+1` lie inside `[A,Z]`, so the local result gives `h_2(d+2)=0`. Continuous mismatch implies `Z < d+2`. Combining this with `d<b<=Z` yields `b=Z=d+1`, and the parent mismatch is zero at `b+1`. A third ordered birth source in `[A,Z]` is consequently impossible.

The interval is closed for parent readings and for child birth sources. A birth at the final source `Z` uses the child reading at `Z+1`; that reading is retained in the definition rather than silently excluded. The theorem does not require the interval to be a maximal episode.

## Actual ancestry adapter

Define `seedHistory(age)(t,i)=Rule30Jen.cell(age+t,i)`. The literal official cell recurrence proves this is an `IsR30` history. Taking ages `Q` and zero gives the same-orbit mismatch `cell(Q+t,i) XOR cell(t,i)`. At age `s=Q+t`, this is the backward lag-`Q` mismatch, without a natural-subtraction boundary case.

All three main conclusions are instantiated with these two histories. There is no free-strip replacement or independently chosen past. The statements permit any natural `Q`; when `Q=0`, their nonzero mismatch premises cannot hold.

## What remains open

The result bounds births within one continuous column-two mismatch interval under the specified center agreement. It does not bound the number of such intervals. Child feedback can initiate another parent interval; moreover, common center forcing at this cut does not automatically become common forcing at the next spatial cut. A bounded first/terminal label is not a unique deeper ancestry path or a non-reusable charge. No global upper birth budget or proof of Problem 1 follows here.
