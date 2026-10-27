# Exact type-0 cutoff family and its first two images

Paper deduction from the literal physical rule and checked catalog identities. No numerical run or new Lean claim. The earlier five-file audit seal remains unchanged. Its sufficient cutoff condition N>=5 is valid; this note sharpens it to N>=2 and computes the full images.

## Definitions and cutoff convention

Use physical Rule30

```
step x(p) = x(p-1) XOR (x(p) OR x(p+1)).
```

The exact official examples are

```
L(p) = [p=-3 or p=-1]  if p<=0, otherwise [p mod3=2],
R(p) = [p=-3 or p=-2]  if p<=0, otherwise [p mod3=1].
cut_N x(p) = x(p) if p<=N, otherwise false.
```

Thus this is a right cutoff, including site N; the entire left portion is preserved. `Rule30TraceMerge.one_step_images` proves that both infinite examples have the first image

```
C_infinity(p) = [-4<=p and p!=-2].
```

`common_second_image` proves that its next image is the finite row

```
F = {-5,-4,-1}.
```

The same module proves equal complete center traces for L and R. The checked `Rule30TraceAmbiguity.cutoff_trace` gives equality between a cutoff and its original at the center for every time t<=N.

## All-horizon type-0 ambiguity

For N>=2, let k_L be the last positive black site of cut_N L, and k_R the last positive black site of cut_N R. They exist and satisfy

```
k_L>=2, k_L mod3=2;     k_R>=1, k_R mod3=1.
```

The two cells immediately left of each k are white. At the smallest possible left-example endpoint k_L=2 these are sites1 and0; at the smallest right-example endpoint k_R=1 they are sites0 and-1, both white by the literal R definition. Thus both cutoff rows have primitive front 100, even in the smallest cases. This proves type0 without taking an unsupported large-N limit.

They remain finite, share left edge -3, and differ at site -1. For any H, choose `N=max(2,H)`. For every t<H the checked cutoff theorem and infinite-example trace equality yield equal finite center observations. Consequently the prior all-H ambiguity theorem has the additional type-0 premise, by this explicit construction. It does not produce a fixed finite pair with equal infinite traces.

## Uniform first and second images

Define `C_K(p)=[-4<=p<=K and p!=-2]`. For either example cut at its actual last positive black k, with the applicable k>=1 and residue above,

```
step(cut_N example) = C_(k+1),
step(C_(k+1)) = F union {k+2}.                 (1)
```

Here cut_N example equals cut_k example because there is no black site between k and N.

Proof of the first identity: at p<=k-1 the three inputs are unchanged, so the image is the checked C_infinity. At p=k, the input triple is (0,1,0), whose image is1. At p=k+1 it is (1,0,0), also giving1. At p>k+1 all inputs are0. These cases give C_(k+1) at every integer site.

For the second identity put K=k+1>=2. At p<=K-1, the inputs of C_K coincide with C_infinity, so the output is F there. At p=K the triple is (1,1,0), giving0, which is F(K). At p=K+1 the triple is (1,0,0), giving1. At every p>K+1 the output is0. The added site K+1=k+2>=3 is disjoint from F. This proves the complete equality in (1), not only a finite window.

For a common cutoff N>=2, the exact endpoint table is:

| N mod3 | (k_L,k_R) | first-image endpoints (K_L,K_R) | second-image isolated sites |
|---|---|---|---|
| 0 | (N-1,N-2) | (N,N-1) | (N+1,N) |
| 1 | (N-2,N) | (N-1,N+1) | (N,N+2) |
| 2 | (N,N-1) | (N+1,N) | (N+2,N+1) |

All coordinates are physical sites. The two isolated sites are distinct. In the residue-0 row N>=3, and in the residue-1 row N>=4; hence the displayed subtraction never creates a nonexistent positive endpoint.

## What the concrete gadget does and does not establish

After two steps the pairs are exactly `F union {r}` and `F union {s}`, with (r,s) in the last table. They have common left edge -5, agree at every site except r and s, and both have primitive front100. The first two original observations agree already. Therefore equality of their complete future center traces would be equivalent to equality of the complete center traces of the original cutoff pair; neither equality is proved.

Their center traces do agree whenever `t+2<=N`, by evolution restart and cutoff_trace. Choosing N arbitrarily large gives arbitrarily long finite agreement for this much more concrete family: one fixed three-black left block and one isolated far-right black cell at two different positions. The time at which the far-right defect reaches the common block cannot be omitted; finite propagation alone gives the lower agreement interval, not eventual visibility or permanent invisibility.

Thus full-trace type-0 injectivity survives the existing all-time source audit, but a proof must distinguish these distant single-cell perturbations over unbounded time. This is an exact reduced test family, not a finite alias, a new counterexample to EdgeObservable, or the actual single-seed genealogy.
