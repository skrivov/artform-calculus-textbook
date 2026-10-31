#!/usr/bin/env python3
"""Author checks for the first research batch; never records independent approval."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
import tomllib

ROOT = Path(__file__).resolve().parents[3]
PACKET = Path(__file__).resolve().parent
BASE = '095caeef9a3780d25e8a0a25bf3c564dd91644f7'
MODULES = ['Geometry', 'Dynamics', 'Controls', 'Process', 'Descent', 'Double',
           'Maurer', 'WordBinding', 'Scaling', 'Statements', 'Theorems']
CHECKS = []
os.environ['PATH'] = str(Path.home() / '.elan/bin') + os.pathsep + os.environ['PATH']


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
    CHECKS.append({'command': argv, 'exit_code': result.returncode,
                   'seconds': round(time.monotonic() - start, 3),
                   'stdout_sha256': digest(stdout), 'stderr_sha256': digest(result.stderr)})
    print(('PASS ' if result.returncode == 0 else 'FAIL ') + ' '.join(argv), flush=True)
    if result.returncode:
        print(stdout.decode(errors='replace')[-5000:])
        print(result.stderr.decode(errors='replace')[-5000:])
        raise SystemExit(result.returncode)
    return stdout


prefix = str(PACKET.relative_to(ROOT))
formal = run(['python3', prefix + '/formal-replay.py'], 'build/ngb-formal-replay.json')
assert json.loads(formal) == json.loads((PACKET / 'formal-replay.json').read_text())
phase = run(['python3', prefix + '/phase-space-replay.py'], 'build/ngb-phase-space-replay.log')
text = phase.decode()
phase_json = json.loads(text[text.index('{\n    "scope"'):] if '{\n    "scope"' in text
                        else text[text.index('{\n  "scope"'):])
assert phase_json == json.loads((PACKET / 'phase-space-replay.json').read_text())
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
for module in MODULES:
    run(['lake', 'env', 'leanchecker', 'ArtformScores.NonabelianGravity.' + module])


def baseline(path):
    return subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=ROOT)


old_manifest = tomllib.loads(baseline('scores/manifest.toml').decode())['statement']
manifest = tomllib.loads((ROOT / 'scores/manifest.toml').read_text())['statement']
assert len(old_manifest) == 258 and manifest[:258] == old_manifest
assert len(manifest) == 266 and all(not e['reviewed'] for e in manifest[258:])
assert all(not e['review_text_sha256'] for e in manifest[258:])
assert sum(bool(e.get('reviewed')) and not e.get('review_return') for e in manifest) == 254
old_paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE], cwd=ROOT).decode().splitlines()
for path in old_paths:
    if path.endswith('.lean') and path != 'scores/ArtformScores.lean':
        assert (ROOT / path).read_bytes() == baseline(path), path
assert (ROOT / 'scores/ArtformScores.lean').read_text() == (
    baseline('scores/ArtformScores.lean').decode() + '\nimport ArtformScores.NonabelianGravity.Theorems\n')
rows = json.loads((ROOT / 'build/ledger-report.json').read_text())
statements = {r['decl']: r for r in rows if r['kind'] == 'statement'}
for entry in old_manifest:
    if not entry.get('reviewed') or entry.get('review_return'):
        continue
    row = statements[entry['lean_statement']]
    surface_hash = digest('\n\n'.join([row['text'], *row['surface']]).encode())
    assert surface_hash == entry['review_text_sha256'], entry['key']
proofs = [r for r in rows if r['kind'] == 'proof' and r['label'].startswith('NGB:')]
assert len(proofs) == 8
assert all(set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for r in proofs)
claims = json.loads((PACKET / 'claims.json').read_text())
canonical = (PACKET / 'ALGEBRA-OF-SCORES.md').read_text()
assert {c['key'] for c in claims} == {e['key'] for e in manifest[258:]}
for claim in claims:
    assert claim['statement'] in canonical
    entry = next(e for e in manifest if e['key'] == claim['key'])
    assert entry['statement'].strip() == claim['statement']
    assert entry['lean_statement'] == claim['lean_statement']
    assert entry['lean_proof'] == claim['lean_proof']
pins = json.loads((PACKET / 'source-pins.json').read_text())
workspace = ROOT.parent
for source in pins['local_inputs']:
    path = source['workspace_path']
    if path.startswith(ROOT.name + '/'):
        data = baseline(path[len(ROOT.name) + 1:])
    else:
        data = (workspace / path).read_bytes()
    assert digest(data) == source['sha256'], path
campaign = json.loads((PACKET / 'campaign.json').read_text())
assert campaign['completed_investigations'] == 12 and campaign['additional_workers_launched'] == 0
assert sum(e['status'] == 'research_disposition_recorded' for e in campaign['investigations']) == 12
assert all(e['status'] == 'planned' for e in campaign['investigations'] if e['stage'] in 'CD')
assert campaign['decisions']['decision12']['status'] == 'unpassed'
files = list((ROOT / 'scores/ArtformScores/NonabelianGravity').glob('*.lean'))
files += [p for p in PACKET.rglob('*') if p.is_file() and p.suffix != '.pyc'
          and p.name != 'validation-research-root.json']
receipt = {
    'date': '2026-10-31', 'author': 'root', 'additional_workers': 0,
    'independent_fidelity_review': False, 'new_approvals': 0, 'baseline': BASE,
    'checks': CHECKS, 'separate_new_module_kernel_replays': len(MODULES),
    'prior_approvals_preserved': 254, 'inherited_pending_submissions_preserved': 4,
    'prior_statement_definition_hashes_preserved': True, 'old_lean_modules_unchanged': True,
    'umbrella_import_additive': True, 'new_checked_claims': 8,
    'new_manifest_status': 'stated_pending_independent_review',
    'total_claims': 266, 'proved': 254, 'stated': 12,
    'research_dispositions': 12, 'fully_answered_model_algebra_questions': 7,
    'scoped_partial_results': 4, 'continuation_decision': 'unpassed',
    'new_material_native_gravity_applications': 0,
    'new_proof_axioms': {r['label']: r['axioms'] for r in proofs},
    'planning_inputs_authenticated': len(pins['local_inputs']),
    'planning_repo_inputs_authenticated_at_commit': BASE,
    'files': {str(p.relative_to(ROOT)): digest(p.read_bytes()) for p in sorted(files)},
}
(PACKET / 'validation-research-root.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('Preserved254 approvals and4 pending CNI claims;8 new checked submissions remain pending.', flush=True)
