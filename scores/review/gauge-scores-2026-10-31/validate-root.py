#!/usr/bin/env python3
"""Required publication checks and additive-preservation receipt, no approvals."""
import hashlib
import json
from pathlib import Path
import subprocess
import time
import tomllib

ROOT = Path(__file__).resolve().parents[3]
REVIEW = Path(__file__).resolve().parent
BASE = '01448c7d261a8f5e5620c39be447d527deddb469'
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
        result = subprocess.run(argv, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stdout = result.stdout
    checks.append(dict(command=argv, exit_code=result.returncode,
                       seconds=round(time.monotonic()-start, 3),
                       stdout_sha256=digest(stdout), stderr_sha256=digest(result.stderr)))
    print('PASS' if result.returncode == 0 else 'FAIL', ' '.join(argv), flush=True)
    if result.returncode:
        print(result.stderr.decode(errors='replace')[-5000:])
        print(stdout.decode(errors='replace')[-5000:])
        raise SystemExit(result.returncode)


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
    ['lake', 'env', 'leanchecker', 'ArtformScores.Gauge.Theorems'],
]:
    run(command)
base_manifest = tomllib.loads(subprocess.check_output(
    ['git', 'show', BASE+':scores/manifest.toml'], cwd=ROOT).decode())['statement']
manifest = tomllib.loads((ROOT/'scores/manifest.toml').read_text())['statement']
assert len(base_manifest) == 239
assert manifest[:239] == base_manifest
changed = subprocess.check_output(['git', 'diff', BASE, '--name-only'], cwd=ROOT).decode().splitlines()
old_paths = set(subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE],
                                        cwd=ROOT).decode().splitlines())
changed_old_modules = [p for p in changed if p in old_paths and p.endswith('.lean')
                       and p != 'scores/ArtformScores.lean']
assert not changed_old_modules, changed_old_modules
rows = json.loads((ROOT/'build/ledger-report.json').read_text())
new_proofs = [r for r in rows if r['kind'] == 'proof' and r['label'].startswith(('GSC:', 'GSM:'))]
assert len(new_proofs) == 9
assert all(set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for r in new_proofs)
claims = json.loads((REVIEW/'claims.json').read_text())
source = (REVIEW/'ALGEBRA-OF-SCORES.md').read_text()
assert all(c['statement'] in source for c in claims)
assert {c['key'] for c in claims} == {c['key'] for c in manifest[239:]}
for c in claims:
    row = next(e for e in manifest if e['key'] == c['key'])
    assert row['statement'].strip() == c['statement']
files = list((ROOT/'scores/ArtformScores/Gauge').glob('*.lean'))
files += [REVIEW/name for name in ['ALGEBRA-OF-SCORES.md', 'claims.json', 'source-pins.json',
                                  'APPLICATIONS.md', 'README.md', 'validate-root.py']]
receipt = dict(date='2026-10-31', author='root', baseline=BASE, checks=checks,
               old_approved_entries=239, old_manifest_entries_unchanged=True,
               old_lean_modules_unchanged=True, umbrella_additive_import=True,
               new_labels=[c['key'] for c in claims],
               new_proof_axioms={r['label']:r['axioms'] for r in new_proofs},
               files={str(p.relative_to(ROOT)):digest(p.read_bytes()) for p in files})
(REVIEW/'validation-root.json').write_text(json.dumps(receipt, indent=2)+'\n')
print('Preserved 239 earlier approvals; 9 checked new claims, with independent review recorded separately.', flush=True)
