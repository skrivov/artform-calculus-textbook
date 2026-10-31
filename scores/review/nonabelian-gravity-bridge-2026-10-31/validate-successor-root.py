#!/usr/bin/env python3
"""Validate the additive three-question successor stage against its immediately published baseline."""
import argparse,hashlib,json,os,subprocess,time,tomllib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];PACKET=Path(__file__).resolve().parent
os.environ['PATH']=str(Path.home()/'.elan/bin')+os.pathsep+os.environ['PATH']
p=argparse.ArgumentParser(description=__doc__);p.add_argument('stage',choices=['13']);p.add_argument('--prepare-only',action='store_true');p.add_argument('--reuse-prepared-reports',action='store_true');a=p.parse_args()
cfg=json.loads((PACKET/('successor-stage-'+a.stage+'.json')).read_text());BASE=cfg['baseline_commit'];MODULES=cfg['modules'];checks=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def base(p):return subprocess.check_output(['git','show',BASE+':'+p],cwd=ROOT)
def run(cmd,out=None):
 t=time.monotonic()
 if out:
  with (ROOT/out).open('wb') as f:r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.PIPE)
  stdout=(ROOT/out).read_bytes()
 else:r=subprocess.run(cmd,cwd=ROOT,capture_output=True);stdout=r.stdout
 checks.append({'command':cmd,'exit_code':r.returncode,'seconds':round(time.monotonic()-t,3),'stdout_sha256':sha(stdout),'stderr_sha256':sha(r.stderr)})
 print(('PASS 'if not r.returncode else 'FAIL ')+' '.join(cmd),flush=True)
 if r.returncode:print(stdout.decode(errors='replace')[-5000:]+r.stderr.decode(errors='replace')[-5000:]);raise SystemExit(r.returncode)
 return stdout

def fingerprint():
 paths=set(subprocess.check_output(['git','ls-files','*.lean'],cwd=ROOT).decode().splitlines());paths.update('scores/ArtformScores/NonabelianGravity/'+m+'.lean'for m in MODULES);paths.add('lake-manifest.json')
 return {p:sha((ROOT/p).read_bytes())for p in sorted(paths)}
prepared=ROOT/('build/ngb-successor-'+a.stage+'-prepared.json');reports=['build/report.json','build/ledger-report.json']
if a.reuse_prepared_reports:
 q=json.loads(prepared.read_text());assert q['source_fingerprint']==fingerprint();assert q['report_sha256']=={p:sha((ROOT/p).read_bytes())for p in reports};checks.extend(q['checks']);print('PASS exact prepared source/report receipts authenticated',flush=True)
else:
 run(['lake','build','--wfail']);run(['lake','env','lean','--run','scripts/Report.lean'],reports[0]);run(['lake','env','lean','--run','scripts/LedgerReport.lean'],reports[1]);prepared.write_text(json.dumps({'source_fingerprint':fingerprint(),'checks':checks,'report_sha256':{p:sha((ROOT/p).read_bytes())for p in reports}},indent=2)+'\n')
run(['python3','scripts/ledger_status.py','--write'])
if a.prepare_only:raise SystemExit(0)
for cmd in [['python3','scripts/status.py','--check'],['python3','scripts/check_tree.py','--identity'],['python3','scripts/ledger_status.py','--check'],['python3','scripts/one_mode_certificates.py','--check'],['python3','scripts/extent_certificates.py','--check'],['python3','scripts/gravity_r2_certificates.py','--check'],['python3','scripts/status.py','--drift'],['python3','scripts/ledger_status.py','--drift']]:run(cmd)
for name in cfg['replays']:run(['python3',str((PACKET/name).relative_to(ROOT))],'build/ngb-stage'+a.stage+'-'+name+'.json')
for name in ['legendre-root.py','composition-root.py','history-emitter-root.py']:run(['python3',str((PACKET/name).relative_to(ROOT)),'--check'])
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',BASE],cwd=ROOT).decode().splitlines()
for p in paths:
 if p.endswith('.lean') and p!='scores/ArtformScores.lean':assert (ROOT/p).read_bytes()==base(p),p
assert (ROOT/'scores/ArtformScores.lean').read_text()==base('scores/ArtformScores.lean').decode()+'\nimport ArtformScores.NonabelianGravity.'+cfg['entry_module']+'\n'
m=tomllib.loads((ROOT/'scores/manifest.toml').read_text())['statement'];old=tomllib.loads(base('scores/manifest.toml').decode())['statement'];assert len(m)==cfg['total_scores']and len(old)==len(m)-3 and m[:-3]==old
assert sum(bool(e.get('reviewed'))and not e.get('review_return')for e in m)==cfg['approved_scores'];assert {e['key']for e in m if not e.get('reviewed')}=={e['key']for e in old if not e.get('reviewed')}
can=PACKET/'ALGEBRA-OF-SCORES.md';assert can.read_bytes().startswith(base(str(can.relative_to(ROOT))))
claims=json.loads((PACKET/'claims.json').read_text());assert len(claims)==cfg['ngb_claims'];assert claims[:-3]==json.loads(base(str((PACKET/'claims.json').relative_to(ROOT))))
for c in claims:
 e=next(e for e in m if e['key']==c['key']);assert c['statement']in can.read_text()
 for k in ['statement','lean_statement','lean_proof']:assert e[k].strip()==c[k]
rows=json.loads((ROOT/'build/ledger-report.json').read_text());sts={r['decl']:r for r in rows if r['kind']=='statement'}
for e in m:
 if e.get('reviewed')and not e.get('review_return'):
  r=sts[e['lean_statement']];assert sha('\n\n'.join([r['text'],*r['surface']]).encode())==e['review_text_sha256']
proofs=[r for r in rows if r['kind']=='proof'and r['label'].startswith('NGB:')];assert len(proofs)==cfg['ngb_claims']and all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'}for r in proofs)
ver=json.loads((PACKET/('verdict-independent-'+a.stage+'.json')).read_text())
assert {v['key']for v in ver['entries']}==set(cfg['keys'])
assert all(v['verdict']=='approve'for v in ver['entries'])
for p,h in ver['reviewed_file_sha256'].items():assert sha((ROOT/p).read_bytes())==h,p
assert sha(can.read_bytes())==ver['canonical_file_sha256']
for v in ver['entries']:
 e=next(e for e in m if e['key']==v['key'])
 assert e['review_text_sha256']==v['review_text_sha256']
 assert sha(e['statement'].strip().encode())==v['canonical_literal_sha256']
review=json.loads((PACKET/('validation-independent-'+a.stage+'.json')).read_text());assert review['root_prepared_receipt']['sha256']==sha(prepared.read_bytes());replays=review['separate_kernel_replays'];assert {r['module']for r in replays}==set(MODULES);assert all(r['exit_code']==0 and r['command']==['lake','env','leanchecker','ArtformScores.NonabelianGravity.'+r['module']]for r in replays)
for n in ['01','02','04','05','06','07','08','09','10','11','12']:
 v=json.loads((PACKET/('verdict-independent-'+n+'.json')).read_text())
 for r in v['entries']:
  e=next(e for e in m if e['key']==r['key']);assert e['review_text_sha256']==r['review_text_sha256'];assert sha(e['statement'].strip().encode())==r['canonical_literal_sha256']
for f in ['native-source-pins.json','followup-source-pins.json']:
 for pin in json.loads((PACKET/f).read_text())['local_inputs']:
  p=ROOT/pin['repository_path']if'repository_path'in pin else ROOT.parent/pin['workspace_path'];assert sha(p.read_bytes())==pin['sha256'],p.name
  if'repository_snapshot'in pin:assert sha((ROOT/pin['repository_snapshot']).read_bytes())==pin['sha256']
receipt={'date':'2026-10-31','stage':a.stage,'baseline_commit':BASE,'result':'passed','checks':checks,'separate_kernel_replays_reused_from_exact_independent_receipt':len(replays),'review_receipt_sha256':sha((PACKET/('validation-independent-'+a.stage+'.json')).read_bytes()),'prior_approved_production_changed':False,'scores':{'total':cfg['total_scores'],'approved':cfg['approved_scores'],'pending_CNI':4},'new_material_physical_gravity_applications':0}
(PACKET/cfg['validation_output']).write_text(json.dumps(receipt,indent=2)+'\n');print('PASS additive successor publication stage'+a.stage,flush=True)
