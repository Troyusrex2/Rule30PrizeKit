"""Select and validate the reference project; never alter its checker."""
from pathlib import Path
import hashlib, subprocess
from core import BASE

PIN = '3eca23c0a9fa6b153313655e6d51835406c2d06e'

def add_reference_options(parser):
    parser.add_argument('--project', type=Path, default=BASE/'current-reference-3eca-20261024')
    parser.add_argument('--lake', type=Path, default=BASE/'toolchain/lean-4.35.0-windows/bin/lake.exe')

def reference(args):
    project, lake = args.project.resolve(), args.lake.resolve()
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip()
    if actual != PIN:
        raise RuntimeError(f'Reference pin mismatch: {actual}; required {PIN}')
    checker = subprocess.check_output(['git', 'show', PIN+':Check.lean'], cwd=project)
    if (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') != checker:
        raise RuntimeError('Reference checker has been modified')
    return project, lake, checker

def unchanged(project, checker):
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip() == PIN
    assert (project/'Check.lean').read_bytes().replace(b'\r\n', b'\n') == checker

def identity(checker):
    return {'kit_commit': PIN, 'checker_unchanged': True,
            'checker_sha256': hashlib.sha256(checker).hexdigest()}
