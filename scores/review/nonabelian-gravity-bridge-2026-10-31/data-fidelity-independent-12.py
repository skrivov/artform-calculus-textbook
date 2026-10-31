#!/usr/bin/env python3
"""Authenticate original-source snapshots and compare independent jet evidence.
Uses the reviewer's standalone nonlinear replay, not a root evaluator.
"""
import pathlib,json,hashlib,subprocess,sys
P=pathlib.Path(__file__).resolve().parent;R=P.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
n=0
for name in ('native-source-pins.json','followup-source-pins.json'):
 for pin in json.loads((P/name).read_text())['local_inputs']:
  p=R/pin['repository_path'] if 'repository_path' in pin else R.parent/pin['workspace_path'];assert sha(p)==pin['sha256'];n+=1
  if 'repository_snapshot' in pin:assert sha(R/pin['repository_snapshot'])==pin['sha256']
assert n==17
r=subprocess.run([sys.executable,str(P/'nonlinear-isotropic-independent.py')],capture_output=True,text=True,check=True)
own=json.loads(r.stdout.split('\n',1)[1]);stored=json.loads((P/'nonlinear-isotropic-independent-data.json').read_text());assert own==stored
root=json.loads((P/'nonlinear-isotropic-root-data.json').read_text());assert root['isotropic_inactive_force']==own['inactive0_force'];assert root['curvature']==own['curvature'];assert root['torsion']==own['torsion'];assert root['all40_linear_owned_rows_zero']==own['all40_owned_first_order_force_zero'];assert 'formal jets' in root['scope']
print('PASS17 original/native pins and exact snapshot bytes; independent stored jet evidence and root40501/curvature/torsion controls agree with scope retained')
