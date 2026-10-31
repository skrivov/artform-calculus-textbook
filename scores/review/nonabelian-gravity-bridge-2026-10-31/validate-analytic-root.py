#!/usr/bin/env python3
"""Validate the reviewed analytic extension; preserve historical first-batch receipts."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
import tomllib

ROOT = Path(__file__).resolve().parents[3]
PACKET = Path(__file__).resolve().parent
BASE = 'c64e8eb26946797e191a6c7a5455c809fd91591e'
OLD_MODULES = ['Geometry', 'Dynamics', 'Controls', 'Process', 'Descent', 'Double',
               'Maurer', 'WordBinding', 'Scaling', 'Statements', 'Theorems']
NEW_MODULES = ['Differential', 'QuaternionForm', 'AnalyticForm', 'UnitQuaternionWitness',
               'AnalyticWitness', 'Stabilizers', 'GeometryPreflight', 'AnalyticStatements',
               'AnalyticTheorems']
os.environ['PATH'] = str(Path.home() / '.elan/bin') + os.pathsep + os.environ['PATH']
checks = []


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run(argv, output=None):
    start = time.monotonic()
    if output:
        target = ROOT / output
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('wb') as stream:
            result = subprocess.run(argv, cwd=ROOT, stdout=stream, stderr=subprocess.PIPE)
        stdout = target.read_bytes()
    else:
        result = subprocess.run(argv, cwd=ROOT, capture_output=True)
        stdout = result.stdout
    checks.append({'command': argv, 'exit_code': result.returncode,
                   'seconds': round(time.monotonic() - start, 3),
                   'stdout_sha256': digest(stdout), 'stderr_sha256': digest(result.stderr)})
    print(('PASS ' if result.returncode == 0 else 'FAIL ') + ' '.join(argv), flush=True)
    if result.returncode:
        print(stdout.decode(errors='replace')[-5000:])
        print(result.stderr.decode(errors='replace')[-5000:])
        raise SystemExit(result.returncode)
    return stdout


def baseline(path):
    return subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=ROOT)


run(['lake', 'build', '--wfail'])
run(['lake', 'env', 'lean', '--run', 'scripts/Report.lean'], 'build/report.json')
run(['lake', 'env', 'lean', '--run', 'scripts/LedgerReport.lean'], 'build/ledger-report.json')
run(['python3', 'scripts/ledger_status.py', '--write'])
for command in [
    ['python3', 'scripts/status.py', '--check'],
    ['python3', 'scripts/check_tree.py', '--identity'],
    ['python3', 'scripts/ledger_status.py', '--check'],
    ['python3', 'scripts/one_mode_certificates.py', '--check'],
    ['python3', 'scripts/extent_certificates.py', '--check'],
    ['python3', 'scripts/gravity_r2_certificates.py', '--check'],
    ['python3', 'scripts/status.py', '--drift'],
    ['python3', 'scripts/ledger_status.py', '--drift'],
]:
    run(command)
for module in NEW_MODULES:
    run(['lake', 'env', 'leanchecker', 'ArtformScores.NonabelianGravity.' + module])

old_manifest = tomllib.loads(baseline('scores/manifest.toml').decode())['statement']
manifest = tomllib.loads((ROOT / 'scores/manifest.toml').read_text())['statement']
assert len(manifest) == 269 and len(old_manifest) == 266
assert manifest[:258] == old_manifest[:258]
for old, new in zip(old_manifest[258:], manifest[258:266]):
    assert {k: v for k, v in old.items() if k not in {'reviewed', 'review_text_sha256'}} == {
        k: v for k, v in new.items() if k not in {'reviewed', 'review_text_sha256'}}
assert sum(bool(e.get('reviewed')) and not e.get('review_return') for e in manifest) == 265
assert {e['key'] for e in manifest if not e.get('reviewed')} == {
    e['key'] for e in old_manifest[:258] if not e.get('reviewed')}
for module in OLD_MODULES:
    path = 'scores/ArtformScores/NonabelianGravity/' + module + '.lean'
    assert (ROOT / path).read_bytes() == baseline(path), path
paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE], cwd=ROOT)
for path in paths.decode().splitlines():
    if path.endswith('.lean') and path != 'scores/ArtformScores.lean':
        assert (ROOT / path).read_bytes() == baseline(path), path
assert (ROOT / 'scores/ArtformScores.lean').read_text() == (
    baseline('scores/ArtformScores.lean').decode() +
    '\nimport ArtformScores.NonabelianGravity.AnalyticTheorems\n')

rows = json.loads((ROOT / 'build/ledger-report.json').read_text())
statements = {r['decl']: r for r in rows if r['kind'] == 'statement'}
proofs = [r for r in rows if r['kind'] == 'proof' and r['label'].startswith('NGB:')]
assert len(proofs) == 11
assert all(set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for r in proofs)
for entry in manifest:
    if not entry.get('reviewed') or entry.get('review_return'):
        continue
    row = statements[entry['lean_statement']]
    assert digest('\n\n'.join([row['text'], *row['surface']]).encode()) == entry['review_text_sha256']
claims = json.loads((PACKET / 'claims.json').read_text())
canonical = (PACKET / 'ALGEBRA-OF-SCORES.md').read_text()
assert len(claims) == 11
for claim in claims:
    entry = next(e for e in manifest if e['key'] == claim['key'])
    assert claim['statement'] in canonical
    assert entry['statement'].strip() == claim['statement']
    assert entry['lean_statement'] == claim['lean_statement']
    assert entry['lean_proof'] == claim['lean_proof']
verdicts = []
for number, expected in [('01', 8), ('02', 3)]:
    verdict = json.loads((PACKET / ('verdict-independent-' + number + '.json')).read_text())
    entries = verdict['entries']
    assert len(entries) == expected and all(e['verdict'] == 'approve' for e in entries)
    for reviewed in entries:
        entry = next(e for e in manifest if e['key'] == reviewed['key'])
        assert entry['review_text_sha256'] == reviewed['review_text_sha256']
        assert digest(entry['statement'].strip().encode()) == reviewed['canonical_literal_sha256']
    verdicts.append({'file': 'verdict-independent-' + number + '.json', 'approvals': expected})

pins = json.loads((PACKET / 'analytic-source-pins.json').read_text())
for pin in pins['local_inputs']:
    path = (ROOT / pin['repository_path'] if 'repository_path' in pin
            else ROOT.parent / pin['workspace_path'])
    assert digest(path.read_bytes()) == pin['sha256'], path.name

campaign = json.loads((PACKET / 'campaign.json').read_text())
assert campaign['new_registered_claims'] == campaign['new_independent_approvals'] == 11
assert campaign['additional_workers_launched'] == 1
assert campaign['new_material_gravity_applications'] == 0
assert campaign['completed_investigations'] == 12
assert all(i['status'] == 'planned' for i in campaign['investigations'] if i['stage'] in ['C', 'D'])
assert campaign['decisions']['decision12']['status'] == 'unpassed'

files = list(PACKET.rglob('*')) + [ROOT / ('scores/ArtformScores/NonabelianGravity/' + m + '.lean')
                                for m in OLD_MODULES + NEW_MODULES]
hashes = {str(f.relative_to(ROOT)): digest(f.read_bytes()) for f in files
          if f.is_file() and f.name != 'validation-analytic-root.json' and '__pycache__' not in f.parts}
receipt = {'date': '2026-10-31', 'scope': 'reviewed analytic extension and preserved baseline',
           'baseline_commit': BASE, 'checks': checks, 'file_sha256': hashes,
           'score_counts': {'total': 269, 'approved': 265, 'pending_CNI': 4},
           'new_module_kernel_replays': len(NEW_MODULES), 'independent_verdicts': verdicts,
           'approved_baseline_production_changed': False, 'new_material_gravity_applications': 0,
           'decision12': 'unpassed: smooth quasi-Hamiltonian regular reduction/domain binding',
           'result': 'passed'}
(PACKET / 'validation-analytic-root.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS analytic extension validation; 265 approvals, 4 CNI pending, no gravity gate credited')
