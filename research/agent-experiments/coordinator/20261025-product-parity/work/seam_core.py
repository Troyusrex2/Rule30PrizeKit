"""Exact finite inverse seam with packed vertical time columns.

This reconstructs initial negative cells. It proves no unbounded property.
"""
def F(a):return (a<<1)^(a|(a>>1))

class Canonical:
    def __init__(self,maximum):
        self.origin=maximum+4;self.rows=[1<<self.origin]
        for _ in range(maximum):self.rows.append(F(self.rows[-1]))
        self.center=[(r>>self.origin)&1 for r in self.rows]
    def initial_positive(self,V):return self.rows[V]>>(self.origin+1)
    def negative(self,V,N):
        return sum(((self.rows[V]>>(self.origin-d))&1)<<(d-1) for d in range(1,N+1))

def reconstruct(background,U,V,N):
    assert U+N<len(background.rows) and N<=background.origin
    C=sum(background.center[U+t]<<t for t in range(N+1))
    original_C=C;r=background.initial_positive(V);R=0
    for t in range(N):
        R|=(r&1)<<t
        r=F(r)^((original_C>>t)&1)
    first_right=R;negative=0
    for depth in range(1,N+1):
        n=N+1-depth
        L=((C>>1)^(C|R))&((1<<n)-1)
        negative|=(L&1)<<(depth-1);R,C=C,L
    outside=negative>>V
    first_escape=V+(outside&-outside).bit_length() if outside else None
    return {'U':U,'V':V,'through':N,'negative_hex':hex(negative),
        'center_trace_hex':hex(original_C),'right_column_hex':hex(first_right),
        'first_black_depth_beyond_V':first_escape,
        'initial_center_matches_younger':background.center[U]==background.center[V],
        'first_actual_canonical_center_disagreement':next((t for t in range(N+1)
            if background.center[U+t]!=background.center[V+t]),None)}
