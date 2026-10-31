#!/usr/bin/env python3
"""Validate source-bound native spatial/history/quantum boundary continuation."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
import tomllib

ROOT = Path(__file__).resolve().parents[3]
PACKET = Path(__file__).resolve().parent
BASE = 'bf99338b742126a7a539198b3d7a0c1bdb0c718b'
OLD_MODULES = ['AnalyticForm', 'AnalyticStatements', 'AnalyticTheorems', 'AnalyticWitness', 'Controls', 'Descent', 'Differential', 'Dipole', 'DipoleConnection', 'DipoleErasure', 'DipoleStatements', 'DipoleTheorems', 'Double', 'Dynamics', 'Geometry', 'GeometryPreflight', 'LegendreBinding', 'LegendreBoundary', 'LegendreComposition', 'LegendreCompositionData', 'LegendreGluing', 'LegendreMatrix', 'LegendreMatrixData', 'LegendrePolynomial', 'LegendreRows', 'LegendreSchur', 'LegendreSource', 'LegendreStatements', 'LegendreTheorems', 'LegendreVariation', 'Maurer', 'NativeBoundary', 'NativeRotation', 'NativeStatements', 'NativeTheorems', 'Process', 'QuaternionForm', 'Scaling', 'SphericalFixture', 'SphericalGluing', 'SphericalGram', 'SphericalOrthant', 'SphericalTransport', 'Stabilizers', 'Statements', 'SurfaceCoordinates', 'SurfaceQuotient', 'SurfaceStatements', 'SurfaceTheorems', 'SurfaceTwists', 'Theorems', 'TransportControls', 'TransportStatements', 'TransportTheorems', 'UnitQuaternionWitness', 'WordBinding']
NEW_MODULES = ['BoundaryCircle', 'BoundaryConditioning', 'BoundaryHistoryColumns', 'BoundaryHistoryDefs', 'BoundaryHistoryKernel', 'BoundaryQuantum', 'BoundaryRotation', 'BoundaryStatements', 'BoundaryStencil', 'BoundarySymbol', 'BoundaryTheorems']
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


parser = argparse.ArgumentParser(description=__doc__)
modes = parser.add_mutually_exclusive_group()
modes.add_argument('--prepare-only', action='store_true')
modes.add_argument('--reuse-prepared-reports', action='store_true')
parser.add_argument('--reuse-reviewed-kernels', action='store_true',
                    help='Authenticate and reuse exact independent09 kernel replays instead of repeating them.')
args = parser.parse_args()
prepared_path = ROOT / 'build/ngb-boundary-prepared.json'


def source_fingerprint():
    paths = set(subprocess.check_output(['git', 'ls-files', '*.lean'], cwd=ROOT).decode().splitlines())
    paths.update('scores/ArtformScores/NonabelianGravity/' + m + '.lean' for m in NEW_MODULES)
    paths.add('lake-manifest.json')
    return {p: digest((ROOT / p).read_bytes()) for p in sorted(paths)}


report_paths = ['build/report.json', 'build/ledger-report.json']
if args.reuse_prepared_reports:
    prepared = json.loads(prepared_path.read_text())
    assert prepared['source_fingerprint'] == source_fingerprint()
    assert prepared['report_sha256'] == {p: digest((ROOT / p).read_bytes()) for p in report_paths}
    checks.extend(prepared['checks'])
    print('PASS reuse exact prepared build/reports: all Lean source and report hashes unchanged', flush=True)
else:
    run(['lake', 'build', '--wfail'])
    run(['lake', 'env', 'lean', '--run', 'scripts/Report.lean'], 'build/report.json')
    run(['lake', 'env', 'lean', '--run', 'scripts/LedgerReport.lean'], 'build/ledger-report.json')
    prepared = {'source_fingerprint': source_fingerprint(), 'checks': list(checks),
                'report_sha256': {p: digest((ROOT / p).read_bytes()) for p in report_paths}}
    prepared_path.write_text(json.dumps(prepared, indent=2) + '\n')
run(['python3', 'scripts/ledger_status.py', '--write'])
if args.prepare_only:
    print('PASS preparation complete; independent review may read the fresh reports')
    raise SystemExit(0)
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
for script in ['legendre-root.py', 'composition-root.py']:
    run(['python3', str((PACKET / script).relative_to(ROOT)), '--check'])
if args.reuse_reviewed_kernels:
    review_path = PACKET / 'validation-independent-09.json'
    verdict = json.loads((PACKET / 'verdict-independent-09.json').read_text())
    review = json.loads(review_path.read_text())
    assert review['root_prepared_receipt']['sha256'] == digest(prepared_path.read_bytes())
    for path, expected_hash in verdict['reviewed_file_sha256'].items():
        assert digest((ROOT / path).read_bytes()) == expected_hash, path
    replays = review['separate_kernel_replays']
    assert len(replays) == len(NEW_MODULES)
    assert {row['module'] for row in replays} == set(NEW_MODULES)
    for row in replays:
        command = ['lake', 'env', 'leanchecker', 'ArtformScores.NonabelianGravity.' + row['module']]
        assert row['command'] == command and row['exit_code'] == 0
        checks.append({'command': command, 'exit_code': 0,
                       'reused_exact_review_receipt': str(review_path.relative_to(ROOT)),
                       'receipt_sha256': digest(review_path.read_bytes())})
    print('PASS reuse all11 independent kernel replays: exact source/preparation hashes authenticated', flush=True)
else:
    for module in NEW_MODULES:
        run(['lake', 'env', 'leanchecker', 'ArtformScores.NonabelianGravity.' + module])
run(['python3', str((PACKET / 'replay-independent-09.py').relative_to(ROOT))],
    'build/ngb-boundary-independent-replay.json')

old_manifest = tomllib.loads(baseline('scores/manifest.toml').decode())['statement']
manifest = tomllib.loads((ROOT / 'scores/manifest.toml').read_text())['statement']
assert len(manifest) == 281 and len(old_manifest) == 278
assert manifest[:278] == old_manifest
assert sum(bool(e.get('reviewed')) and not e.get('review_return') for e in manifest) == 277
assert {e['key'] for e in manifest if not e.get('reviewed')} == {
    e['key'] for e in old_manifest if not e.get('reviewed')}
for module in OLD_MODULES:
    path = 'scores/ArtformScores/NonabelianGravity/' + module + '.lean'
    assert (ROOT / path).read_bytes() == baseline(path), path
paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE], cwd=ROOT)
for path in paths.decode().splitlines():
    if path.endswith('.lean') and path != 'scores/ArtformScores.lean':
        assert (ROOT / path).read_bytes() == baseline(path), path
assert (ROOT / 'scores/ArtformScores.lean').read_text() == (
    baseline('scores/ArtformScores.lean').decode() +
    '\nimport ArtformScores.NonabelianGravity.BoundaryTheorems\n')

rows = json.loads((ROOT / 'build/ledger-report.json').read_text())
statements = {r['decl']: r for r in rows if r['kind'] == 'statement'}
proofs = [r for r in rows if r['kind'] == 'proof' and r['label'].startswith('NGB:')]
assert len(proofs) == 23
assert all(set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for r in proofs)
for entry in manifest:
    if not entry.get('reviewed') or entry.get('review_return'):
        continue
    row = statements[entry['lean_statement']]
    assert digest('\n\n'.join([row['text'], *row['surface']]).encode()) == entry['review_text_sha256']
claims = json.loads((PACKET / 'claims.json').read_text())
canonical = (PACKET / 'ALGEBRA-OF-SCORES.md').read_text()
assert canonical.startswith(baseline(str((PACKET / 'ALGEBRA-OF-SCORES.md').relative_to(ROOT))).decode())
assert len(claims) == 23
assert claims[:20] == json.loads(baseline(str((PACKET / 'claims.json').relative_to(ROOT))))
for claim in claims:
    entry = next(e for e in manifest if e['key'] == claim['key'])
    assert claim['statement'] in canonical
    assert entry['statement'].strip() == claim['statement']
    assert entry['lean_statement'] == claim['lean_statement']
    assert entry['lean_proof'] == claim['lean_proof']
verdicts = []
for number, expected in [('01', 8), ('02', 3), ('04', 2), ('05', 2), ('06', 2), ('07', 1), ('08', 2), ('09', 3)]:
    verdict = json.loads((PACKET / ('verdict-independent-' + number + '.json')).read_text())
    entries = verdict['entries']
    assert len(entries) == expected and all(e['verdict'] == 'approve' for e in entries)
    for reviewed in entries:
        entry = next(e for e in manifest if e['key'] == reviewed['key'])
        assert entry['review_text_sha256'] == reviewed['review_text_sha256']
        assert digest(entry['statement'].strip().encode()) == reviewed['canonical_literal_sha256']
    if number == '09':
        for path, expected_hash in verdict['reviewed_file_sha256'].items():
            assert digest((ROOT / path).read_bytes()) == expected_hash, path
        assert digest((PACKET / 'ALGEBRA-OF-SCORES.md').read_bytes()) == verdict['canonical_file_sha256']
        assert digest((PACKET / 'replay-independent-09.py').read_bytes()) == verdict['independent_replay_sha256']
        assert digest((PACKET / 'data-fidelity-independent-09.py').read_bytes()) == verdict['independent_data_fidelity_sha256']
    verdicts.append({'file': 'verdict-independent-' + number + '.json', 'approvals': expected})

pins = json.loads((PACKET / 'native-source-pins.json').read_text())
for pin in pins['local_inputs']:
    path = (ROOT / pin['repository_path'] if 'repository_path' in pin
            else ROOT.parent / pin['workspace_path'])
    assert digest(path.read_bytes()) == pin['sha256'], path.name

campaign = json.loads((PACKET / 'campaign.json').read_text())
assert campaign['new_registered_claims'] == campaign['new_independent_approvals'] == 23
assert campaign['additional_workers_launched'] == 2
assert campaign['active_review_workers'] == 0
assert campaign['maximum_concurrent_review_workers'] == 1
assert campaign['new_material_gravity_applications'] == 0
assert campaign['completed_investigations'] == 12
assert all(i['status'] == 'planned' for i in campaign['investigations'] if i['stage'] in ['C', 'D'])
assert campaign['decisions']['decision12']['status'] == 'unpassed'

files = list(PACKET.rglob('*')) + [ROOT / ('scores/ArtformScores/NonabelianGravity/' + m + '.lean')
                                for m in OLD_MODULES + NEW_MODULES]
hashes = {str(f.relative_to(ROOT)): digest(f.read_bytes()) for f in files
          if f.is_file() and f.name != 'validation-boundary-root.json' and '__pycache__' not in f.parts}
receipt = {'date': '2026-10-31', 'scope': 'actual circle mixed-cut symbol, kernel-aware nonuniform estimate, third-cell source guard and finite quantum kernel tests',
           'baseline_commit': BASE, 'checks': checks, 'file_sha256': hashes,
           'score_counts': {'total': 281, 'approved': 277, 'pending_CNI': 4},
           'new_module_kernel_replays': len(NEW_MODULES),
           'kernel_replay_provenance': ('exact independent09 receipt' if args.reuse_reviewed_kernels
                                        else 'root replay'), 'independent_verdicts': verdicts,
           'approved_baseline_production_changed': False, 'new_material_gravity_applications': 0,
           'decision12': 'unpassed: smooth quasi-Hamiltonian regular reduction/domain binding',
           'result': 'passed'}
(PACKET / 'validation-boundary-root.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS native boundary continuation; 277 approvals, 4 CNI pending; no selected quantum gravity theory credited')
