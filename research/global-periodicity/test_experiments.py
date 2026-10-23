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
periodic=load('periodic-right-fibers')
caps=load('finite-preimage-caps')


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

    def test_periodic_right_rigidity_counterexample(self):
        a,b=(10,'010'),(12,'100')
        self.assertNotEqual(periodic.cell(a,-1),periodic.cell(b,-1))
        self.assertTrue(periodic.one_step_merge(a,b))
        for p in range(-24,25):
            expected=int(p>=-4 and p!=-2)
            self.assertEqual(periodic.image(a,p),expected)
            self.assertEqual(periodic.image(b,p),expected)
        ta=obs.center_trace(periodic.encode(*a,512),511,512)
        tb=obs.center_trace(periodic.encode(*b,512),511,512)
        self.assertEqual(ta,tb)

    def test_right_cone_cutoff(self):
        # Arbitrary additions beyond position H-1 cannot affect H observations.
        for h in range(1,17):
            center=h-1
            for depth in range(5):
                for free in [0,(1<<depth)-1]:
                    a=(((1<<depth)|free)<<center)|((1<<center)-1)
                    expected=obs.center_trace(a,center,h)
                    for extra in range(8):
                        self.assertEqual(expected,obs.center_trace((a<<3)|extra,center+3,h))

    def test_finite_fixed_depth_ambiguity_witnesses(self):
        # Positive control: test the depth-two decoder on every relevant
        # initial cone with the separate cellwise implementation.
        for prefix in range(4,8):
            for right in range(8):
                c0,c1,c2,c3=lut_trace((prefix<<3)|right,3,4)
                decoded=(1-c1) if c0 else c2 if c1 else c2 & (1-c3)
                self.assertEqual(decoded,(prefix>>1)&1)
        # Truncate the periodic merge pair. Check FINITE witnesses using
        # the separate cellwise implementation, including very short cones.
        for horizon in [0,1,2,9,32,128]:
            a=periodic.encode(10,'010',horizon+1)
            b=periodic.encode(12,'100',horizon+1)
            self.assertEqual(a.bit_length(),horizon+4)
            self.assertEqual(b.bit_length(),horizon+4)
            self.assertNotEqual((a>>(horizon+1))&1,(b>>(horizon+1))&1)
            width=max(horizon,3)
            self.assertEqual(lut_trace(a<<(width-horizon),width,horizon),
                             lut_trace(b<<(width-horizon),width,horizon))
        # Truncating the infinite pair must not be mistaken for preserving
        # its infinite trace equality. This finite pair later separates.
        h=1024
        a=periodic.encode(10,'010',h+1)
        b=periodic.encode(12,'100',h+1)
        delta=obs.center_trace(a,h,4096)^obs.center_trace(b,h,4096)
        self.assertEqual((delta&-delta).bit_length()-1,2601)

    def test_finite_inverse(self):
        for row in range(512):
            self.assertEqual(caps.finite_inverse(obs.phi(row)),row)
        self.assertIsNone(caps.finite_inverse(1))
        self.assertIsNone(caps.finite_inverse(2))


if __name__=='__main__':
    unittest.main(verbosity=2)
