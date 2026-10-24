"""Split the published edge-pair declarations without changing their bodies."""
import hashlib
import json
import re
from pathlib import Path


def replay_split_source(project, lake, output, raw, guard, checker):
    text = raw.decode('utf-8')
    marker = 'namespace Rule30Submission\n'
    begin = text.index(marker)
    preamble = text[:begin]
    body = text[begin+len(marker):text.rindex('\nend Rule30Submission')]
    assert not re.search(r'(?m)^(private |local |section\b|end\b|set_option |attribute )', body)

    def position(name):
        found = re.search(r'(?m)^theorem '+re.escape(name)+r'\b', body)
        assert found, name
        return found.start()

    entries = [('Core', 0, ['centers_spec', 'separationB']),
               ('Eight', position('d8_0'), ['sep_8']),
               ('ThirteenData0', position('d13_0'), ['d13_0', 'd13_31']),
               ('ThirteenData1', position('d13_32'), ['d13_32', 'd13_63']),
               ('ThirteenTheorem', position('blocks13'), ['sep_13']),
               ('FourteenData0', position('d14_0'), ['d14_0', 'd14_31']),
               ('FourteenData1', position('d14_32'), ['d14_32', 'd14_63']),
               ('FourteenData2', position('d14_64'), ['d14_64', 'd14_95']),
               ('FourteenData3', position('d14_96'), ['d14_96', 'd14_127']),
               ('FourteenTheorem', position('blocks14'), ['sep_14']),
               ('Witnesses', body.index('/-! ## 10.'), ['attained_8', 'attained_13', 'attained_14'])]
    starts = [p for _, p, _ in entries]+[len(body)]
    assert starts == sorted(starts) and len(set(starts)) == len(starts)
    segments = [body[starts[i]:starts[i+1]] for i in range(len(entries))]
    assert ''.join(segments) == body
    output.mkdir(parents=True, exist_ok=True)
    original_sha = hashlib.sha256(raw).hexdigest()
    records = []
    progress_path = output/'edge-pairs-split-progress.json'
    previous = None
    for (suffix, _, heads), segment in zip(entries, segments):
        module = 'Rule30ExternalEdgePairs'+suffix
        source = ('import '+previous+'\n\n' if previous else '')+preamble+marker
        if previous:
            source += 'open Ruliology.CellularAutomata Rule30Jen Rule30Realization\n\n'
        source += segment+'\nend Rule30Submission\n'
        target = project/(module+'.lean')
        encoded = source.encode('utf-8')
        if target.exists() and target.read_bytes() != encoded:
            legacy = preamble+('import '+previous+'\n\n' if previous else '')+marker
            if previous:
                legacy += 'open Ruliology.CellularAutomata Rule30Jen Rule30Realization\n\n'
            legacy += segment+'\nend Rule30Submission\n'
            if target.read_bytes() != legacy.encode('utf-8'):
                raise RuntimeError('Different split source exists: '+str(target))
        target.write_bytes(encoded)
        artifact = project/'.lake/build/lib/lean'/(module+'.olean')
        progress = {'verdict': 'in_progress', 'original_source_sha256': original_sha,
                    'module_in_progress': module, 'completed': records,
                    'full_problem_solved': False}
        progress_path.write_text(json.dumps(progress, indent=2)+'\n', encoding='utf-8')
        print(json.dumps({'module': module, 'stage': 'compile'}), flush=True)
        try:
            seconds = guard.guarded([lake, 'env', 'lean', '-o', str(artifact), str(target)],
                                    project, output/(module+'.build.log'))
            argv = [lake, 'env', 'lean', '--run', 'Check.lean', module, '--claim', 'partial']
            for head in heads:
                argv += ['--headline', 'Rule30Submission.'+head]
            print(json.dumps({'module': module, 'stage': 'full_kernel_replay'}), flush=True)
            log = output/(module+'.check.log')
            elapsed = guard.guarded(argv, project, log)
            check = json.loads([s for s in log.read_text(encoding='utf-8').splitlines() if s.startswith('{')][-1])
            assert check['verdict'] == 'pass' and check['replay']['ok'] and not check['newAxioms']
            assert all(h['ok'] for h in check['headlines'])
        except Exception:
            progress['verdict'] = 'incomplete'
            progress_path.write_text(json.dumps(progress, indent=2)+'\n', encoding='utf-8')
            raise
        records.append({'module': module, 'source_sha256': hashlib.sha256(encoded).hexdigest(),
                        'verbatim_body_sha256': hashlib.sha256(segment.encode('utf-8')).hexdigest(),
                        'build_seconds': seconds, 'replay_seconds': elapsed, 'check': check})
        print(json.dumps({'module': module, 'verdict': 'pass',
                          'constants': check['replay']['constants']}), flush=True)
        previous = module
    report = {'verdict': 'pass', 'submission_id': 'R30-20261024-991a71',
              'source_url': 'https://www.wolframcloud.com/obj/rule-30-prize/Agents/api/file?id=R30-20261024-991a71&kind=lean',
              'source_sha256': original_sha, 'source_bytes': len(raw),
              'source_adaptations': 'Namespace/import wrappers and module boundaries only; concatenated original bodies byte-identical',
              'original_body_coverage_checked': True,
              'original_body_sha256': hashlib.sha256(body.encode('utf-8')).hexdigest(),
              'authors': 'Gareth Herbert; Claude (Anthropic); GPT (OpenAI)',
              'kit_commit': guard.KIT, 'checker_unchanged': True,
              'checker_sha256': hashlib.sha256(checker).hexdigest(),
              'modules': records, 'constants': sum(x['check']['replay']['constants'] for x in records),
              'scope': 'Three fixed left-edge pairs with arbitrary right tails; no uniform all-edge result',
              'full_problem_solved': False}
    assert report['constants'] == 583, 'Declaration count differs from the verified original source'
    (output/'edge-pairs-report.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8', newline='\n')
    progress_path.write_text(json.dumps({'verdict': 'pass', 'completed_modules': len(records),
        'original_source_sha256': original_sha, 'constants': report['constants']}, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'verdict': 'pass', 'modules': len(records), 'constants': report['constants']}), flush=True)
