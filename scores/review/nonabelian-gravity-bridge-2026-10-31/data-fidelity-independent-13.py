#!/usr/bin/env python3
"""Independent baseline, pinned source and canonical preservation checks."""
import pathlib,json,hashlib,subprocess
P=pathlib.Path(__file__).resolve().parent;R=P.parents[2];BASE='79e9ce11d21c737d1c955dc8c92e6b1ba71b0e2f'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def old(p):return subprocess.check_output(['git','show',BASE+':'+str(p)],cwd=R)
entries=subprocess.check_output(['git','ls-tree','-rz',BASE],cwd=R).split(b'\0');n=0
for e in entries:
 if not e:continue
 header,name=e.split(b'\t');name=name.decode()
 if not name.endswith('.lean'):continue
 if name=='scores/ArtformScores.lean':
  assert (R/name).read_bytes()==old(pathlib.Path(name))+b'\nimport ArtformScores.NonabelianGravity.SuccessorTheorems\n'
  continue
 data=(R/name).read_bytes();assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==header.decode().split()[2],name;n+=1
pins=0
for name in ('native-source-pins.json','followup-source-pins.json'):
 for pin in json.loads((P/name).read_text())['local_inputs']:
  f=R/pin['repository_path'] if 'repository_path' in pin else R.parent/pin['workspace_path'];assert sha(f)==pin['sha256'];pins+=1
  if 'repository_snapshot' in pin:assert sha(R/pin['repository_snapshot'])==pin['sha256']
assert pins==17
rel=P.relative_to(R)
claims=json.loads((P/'claims.json').read_text());prior=json.loads(old(rel/'claims.json'));assert claims[:len(prior)]==prior
for name in ('ALGEBRA-OF-SCORES.md',):assert (P/name).read_bytes().startswith(old(rel/name))
assert (R/'scores/manifest.toml').read_bytes().startswith(old(pathlib.Path('scores/manifest.toml')))
print(json.dumps({'result':'passed','baseline':BASE,'old_Lean_files_byte_identical':n,'original_pins':pins,'previous_claim_objects':len(prior),'canonical_and_manifest_prefixes_preserved':True},indent=2))
