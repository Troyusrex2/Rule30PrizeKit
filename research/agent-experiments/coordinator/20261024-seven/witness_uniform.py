"""Exact uniform-initial-neighborhood controls for temporal witness entropy."""
from collections import Counter
import math
from core import save

def entropy(c):
    n=sum(c.values());return -sum(v/n*math.log2(v/n) for v in c.values())

def main():
    results=[]
    for k in range(1,8):
        width=2*k+3;c=k+1;joint=Counter();past=Counter()
        for a in range(1<<width):
            word=[]
            for t in range(k+1):
                word.append(4*((a>>(c-1))&1)+2*((a>>c)&1)+((a>>(c+1))&1))
                a=(a<<1)^(a|(a>>1))
            joint[tuple(word)]+=1;past[tuple(word[:-1])]+=1
        result={'witness_context_length':k,'uniform_initial_cells':width,
                'exhaustive_initial_words':1<<width,'conditional_entropy':entropy(joint)-entropy(past),
                'distinct_past_contexts':len(past),'distinct_joint_words':len(joint)}
        results.append(result);print(result,flush=True)
    save('witness-uniform.json',{'records':results,'interpretation':'Uniform random initial neighborhoods, not a theorem that the single-seed orbit is distributed this way.'})

if __name__=='__main__':main()
