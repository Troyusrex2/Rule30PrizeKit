"""Rebuild every research dependency and replay each module's declarations.

Run in a prepared reference checkout. Each child compiler/checker retains
the existing 300-second, 8-GiB, 2-GiB-free guard. No parallel builds.
"""
import argparse,subprocess,sys
from core import HERE
from verification_context import add_reference_options,reference,unchanged

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    add_reference_options(parser)
    parser.add_argument('--resume-endpoints',action='store_true',
                        help='Retain exact-source endpoint passes and existing objects')
    args=parser.parse_args();project,lake,checker=reference(args)
    common=['--project',str(project),'--lake',str(lake)]
    stages=[['audit_five_tail.py'],['verify_front_lift.py'],
            ['verify_front_lift.py','--period'],['verify_front_lanes.py'],
            ['verify_front_jump.py','--all']+(['--resume'] if args.resume_endpoints else []),
            ['verify_front_map.py'],['verify_front_cycle.py'],['verify_front_return_map.py']]
    for script,*extra in stages:
        print({'stage':script,'options':extra},flush=True)
        subprocess.run([sys.executable,str(HERE/script),*extra,*common],check=True,cwd=HERE)
        unchanged(project,checker)
    print({'status':'all_modules_rebuilt_and_replayed','full_problem_solved':False},flush=True)

if __name__=='__main__':main()
