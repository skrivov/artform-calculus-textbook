#!/usr/bin/env python3
"""Run the reviewer's separately transcribed source controls for stage13.
No production/root evaluator imports. Companion replay14 additionally compares
emitted data against the independently computed native matrix.
"""
import hashlib,json,pathlib,subprocess,sys
P=pathlib.Path(__file__).resolve().parent
results=[]
for name in ('successor-full40-jet-independent.py','successor-history-independent.py','replay-independent-14.py'):
 p=P/name;r=subprocess.run([sys.executable,str(p)],capture_output=True,check=True)
 results.append({'script':name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'exit_code':r.returncode,'stdout':r.stdout.decode(),'stdout_sha256':hashlib.sha256(r.stdout).hexdigest(),'stderr_sha256':hashlib.sha256(r.stderr).hexdigest()})
print(json.dumps({'result':'passed','scope':'Independent finite native source, second-order jet controls and Schur rational data; universal analytic/domain theorems separately Lean reviewed.','checks':results},indent=2))
