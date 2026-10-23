"""Independent checks of the research instruments, not infinite claims."""
import importlib.util
from pathlib import Path
import unittest

ROOT=Path(__file__).parent


def load(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/(name+'.py'))
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


obs=load('trace-observability')
side=load('sideways-candidate')
normal=load('collision-normalization')


def lut_trace(number,width,steps,rule=30):
    # Position-indexed reference implementation; no packed update formula.
    row={p:(number>>(width-p))&1 for p in range(-width,width+1)}
    result=[]
    for t in range(steps):
        result.append(row.get(0,0))
        row={p:(rule >> ((row.get(p-1,0)<<2)|(row.get(p,0)<<1)|row.get(p+1,0)))&1
             for p in range(-width-t-1,width+t+2)}
    return result


class Experiments(unittest.TestCase):
    def test_rule30_integer_encoding(self):
        for width in range(5):
            for row in range(1<<(2*width+1)):
                actual=obs.center_trace(row,width,24)
                expected=sum(x<<t for t,x in enumerate(lut_trace(row,width,24)))
                self.assertEqual(actual,expected)

    def test_edge_recovery_small_cases(self):
        for width,expected in enumerate([1,4,7,7,15]):
            result=obs.scan(width,32,64)
            self.assertEqual(result['mixed_left_edge_groups'],0)
            self.assertEqual(result['minimum_edge_observation_length'],expected)
            a,b=result['last_ambiguous_edge_pair']
            self.assertNotEqual(a.bit_length(),b.bit_length())
            self.assertEqual(obs.center_trace(a,width,expected-1),obs.center_trace(b,width,expected-1))
            self.assertNotEqual(obs.center_trace(a,width,expected),obs.center_trace(b,width,expected))

    def test_negative_controls(self):
        # Reflection gives equal center traces with different left edges in
        # rules 90 and 150. These controls reject a generic permutivity argument.
        for rule in [90,150]:
            self.assertEqual(lut_trace(4,1,64,rule),lut_trace(1,1,64,rule))
        self.assertNotEqual(lut_trace(4,1,64,30),lut_trace(1,1,64,30))

    def test_long_agreement_is_not_an_infinite_equivalence(self):
        for a,b,width,first in [(329,337,7,132),(3487,3625,6,139),
                                (19204870,8785767,12,37),(20110911,10934896,12,38)]:
            delta=obs.center_trace(a,width,256)^obs.center_trace(b,width,256)
            self.assertEqual((delta&-delta).bit_length()-1,first)

    def test_sideways_exact_truncation_death(self):
        for right in [0,1,2,3,5,13]:
            full=side.candidate(right,512)
            for width in range(1,129):
                tail=full >> width
                self.assertNotEqual(tail,0)
                next_black=width+(tail&-tail).bit_length()
                truncated=full & ((1<<width)-1)
                actual=side.direct_trace(truncated,right,next_black+1)
                self.assertEqual(actual[:next_black],[1-t%2 for t in range(next_black)])
                self.assertNotEqual(actual[next_black],1-next_black%2)

    def test_stripe_tail_reduction(self):
        for width in range(5):
            for row in range(1<<(2*width+1)):
                reduced=normal.normalize(row,width)
                self.assertEqual(lut_trace(row,width,24),lut_trace(reduced,width,24))


if __name__=='__main__':
    unittest.main(verbosity=2)
