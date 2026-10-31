#!/usr/bin/env python3
"""Author publication checks; never records independent review or approvals."""
import hashlib
import json
from pathlib import Path
import subprocess
import time
import tomllib

ROOT = Path(__file__).resolve().parents[3]
REVIEW = Path(__file__).resolve().parent
BASE = 'af36dc2024d00af61589ddfae5416edfab00dc58'
CHECKS = []


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
        result = subprocess.run(argv, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stdout = result.stdout
    CHECKS.append(dict(command=argv, exit_code=result.returncode,
                       seconds=round(time.monotonic() - start, 3),
                       stdout_sha256=digest(stdout), stderr_sha256=digest(result.stderr)))
    print('PASS' if result.returncode == 0 else 'FAIL', ' '.join(argv), flush=True)
    if result.returncode:
        print(stdout.decode(errors='replace')[-5000:])
        print(result.stderr.decode(errors='replace')[-5000:])
        raise SystemExit(result.returncode)


run(['python3', str((REVIEW / 'replay-root.py').relative_to(ROOT)), '--check'])
run(['lake', 'build', '--wfail'])
run(['lake', 'env', 'lean', '--run', 'scripts/Report.lean'], 'build/report.json')
run(['lake', 'env', 'lean', '--run', 'scripts/LedgerReport.lean'], 'build/ledger-report.json')
run(['python3', 'scripts/ledger_status.py', '--write'])
for argv in [
    ['python3', 'scripts/status.py', '--check'],
    ['python3', 'scripts/check_tree.py', '--identity'],
    ['python3', 'scripts/ledger_status.py', '--check'],
    ['python3', 'scripts/one_mode_certificates.py', '--check'],
    ['python3', 'scripts/extent_certificates.py', '--check'],
    ['python3', 'scripts/gravity_r2_certificates.py', '--check'],
    ['python3', 'scripts/status.py', '--drift'],
    ['python3', 'scripts/ledger_status.py', '--drift'],
]:
    run(argv)
for module in ['Geometry', 'Dynamics', 'Descent', 'Process', 'Controls', 'Statements', 'Theorems']:
    run(['lake', 'env', 'leanchecker', 'ArtformScores.ClassicalNonabelian.' + module])
base_manifest = tomllib.loads(subprocess.check_output(
    ['git', 'show', BASE + ':scores/manifest.toml'], cwd=ROOT).decode())['statement']
manifest = tomllib.loads((ROOT / 'scores/manifest.toml').read_text())['statement']
assert len(base_manifest) == 254 and manifest[:254] == base_manifest
assert len(manifest) == 258 and all(not e['reviewed'] for e in manifest[254:])
assert all(not e['review_text_sha256'] for e in manifest[254:])
old_paths = subprocess.check_output(
    ['git', 'ls-tree', '-r', '--name-only', BASE], cwd=ROOT).decode().splitlines()
for path in old_paths:
    if path.endswith('.lean') and path != 'scores/ArtformScores.lean':
        assert (ROOT / path).read_bytes() == subprocess.check_output(
            ['git', 'show', BASE + ':' + path], cwd=ROOT), path
old_umbrella = subprocess.check_output(
    ['git', 'show', BASE + ':scores/ArtformScores.lean'], cwd=ROOT).decode()
assert (ROOT / 'scores/ArtformScores.lean').read_text() == (
    old_umbrella + '\nimport ArtformScores.ClassicalNonabelian.Theorems\n')
rows = json.loads((ROOT / 'build/ledger-report.json').read_text())
statements = {r['decl']: r for r in rows if r['kind'] == 'statement'}
for entry in base_manifest:
    row = statements[entry['lean_statement']]
    surface_hash = digest('\n\n'.join([row['text'], *row['surface']]).encode())
    assert surface_hash == entry['review_text_sha256'], entry['key']
proofs = [r for r in rows if r['kind'] == 'proof' and r['label'].startswith('CNI:')]
assert len(proofs) == 4
assert all(set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for r in proofs)
claims = json.loads((REVIEW / 'claims.json').read_text())
canonical = (REVIEW / 'ALGEBRA-OF-SCORES.md').read_text()
assert {c['key'] for c in claims} == {c['key'] for c in manifest[254:]}
for claim in claims:
    assert claim['statement'] in canonical
    entry = next(e for e in manifest if e['key'] == claim['key'])
    assert entry['statement'].strip() == claim['statement']
pins = json.loads((REVIEW / 'source-pins.json').read_text())
for source in pins['local_sources']:
    assert digest((ROOT / source['snapshot']).read_bytes()) == source['sha256']
files = list((ROOT / 'scores/ArtformScores/ClassicalNonabelian').glob('*.lean'))
files += [p for p in REVIEW.rglob('*') if p.is_file() and p.name != 'validation-root.json']
receipt = dict(date='2026-10-31', author='root', additional_workers=0,
               independent_fidelity_review=False, new_approvals=0,
               baseline=BASE, checks=CHECKS, prior_approvals_preserved=254,
               prior_statement_definition_hashes_preserved=True,
               old_lean_modules_unchanged=True, umbrella_import_additive=True,
               new_checked_claims=4, new_manifest_status='stated_pending_independent_review',
               new_proof_axioms={r['label']: r['axioms'] for r in proofs},
               files={str(p.relative_to(ROOT)): digest(p.read_bytes()) for p in sorted(files)})
(REVIEW / 'validation-root.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('Preserved254 approvals;4 checked submissions remain unapproved. No extra workers.', flush=True)
