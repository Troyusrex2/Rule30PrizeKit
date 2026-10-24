"""Reproduce PR #1's source transport audit from its recorded public manifest.

This compares source bodies; it does not replace the separate kernel replay.
Use a checkout containing the original commit and the revised PR #1 sources.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def canonical(text):
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif string:
            out.append(text[i])
            if text[i] == '\\' and i+1 < len(text):
                i += 1
                out.append(text[i])
            elif text[i] == '"':
                string = False
            i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            string = text[i] == '"'
            out.append(text[i])
            i += 1
    assert depth == 0 and not string
    text = '\n'.join(line for line in ''.join(out).splitlines()
                     if line.strip() not in {'module', '@[expose] public section'}
                     and not re.match(r'^(?:public )?import ', line))
    for old, new in [('if_pos', 'ite_eq_left'), ('if_neg', 'ite_eq_right'),
                     ('if_true', 'ite_true'), ('if_false', 'ite_false')]:
        text = re.sub(r'\b'+old+r'\b', new, text)
    return re.sub(r'\s+', '', text)


def transport(text, module_mapping, namespace_mapping, namespace_opens):
    lines, seen = [], set()
    for line in text.splitlines():
        match = re.fullmatch(r'(?:public )?import ([\w.]+)', line)
        if match:
            module = module_mapping.get(match[1], match[1])
            if module in seen:
                continue
            seen.add(module)
            line = 'public import '+module
        lines.append(line)
    text = '\n'.join(lines)+'\n'
    for old, new in sorted(namespace_mapping.items(), key=lambda kv: -len(kv[0])):
        text = text.replace(old, new)
    text = re.sub(r'\b([A-Za-z_][A-Za-z_0-9]*)Research\b', r'\1', text)
    for module, opening in namespace_opens.items():
        if 'namespace '+module+'\n' in text:
            assert text.count(opening['after']) == 1
            text = text.replace(opening['after'], opening['after']+opening['insert'])
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--manifest', type=Path,
                        default=Path(__file__).with_name('pr1-consolidation-manifest.json'))
    args = parser.parse_args()
    project = args.project.resolve()
    report = json.loads(args.manifest.read_text(encoding='utf-8'))
    original = report['original_commit']
    checked = 0
    for item in report['modules']:
        expected = []
        for component in item['original_components']:
            path = 'lean/'+component.replace('.', '/')+'.lean'
            source = subprocess.check_output(['git', 'show', original+':'+path], cwd=project)
            assert hashlib.sha256(source).hexdigest() == report['original_source_sha256'][component]
            expected.append(canonical(transport(source.decode('utf-8'), report['module_mapping'],
                                                report['namespace_mapping'], report['namespace_open_transport'])))
            checked += 1
        new_path = project/'lean'/Path(item['module'].replace('.', '/')).with_suffix('.lean')
        actual = new_path.read_bytes()
        assert hashlib.sha256(actual).hexdigest() == item['source_sha256']
        body = canonical(actual.decode('utf-8'))
        assert body == ''.join(expected), item['module']
        assert hashlib.sha256(body.encode()).hexdigest() == item['canonical_body_sha256']
    print(json.dumps({'AllPassed': True, 'source_components': checked,
                      'revised_modules': len(report['modules']),
                      'Lean_verified_by_this_script': False,
                      'scope': 'Source transport only; separate kernel reports verify the proofs'}), flush=True)


if __name__ == '__main__':
    main()
