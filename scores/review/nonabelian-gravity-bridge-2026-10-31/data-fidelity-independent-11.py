#!/usr/bin/env python3
"""Compare root exploratory controls to separately derived reviewer data.
The underlying reviewer quantum-slice-independent.py is separately rerun;
these comparisons do not promote host Schur controls to Lean theorems.
"""
import json,pathlib
P=pathlib.Path(__file__).resolve().parent
own=json.loads((P/'quantum-slice-independent-data.json').read_text());root=json.loads((P/'quantum-reference-root-data.json').read_text())
names=['full66','first36','Schur30','second30','Schur36']
assert root['determinants_G_A_S_D_T']==[own['blocks'][n]['determinant'] for n in names]
assert root['inertias_G_A_S_D_T']==[[own['blocks'][n]['positive'],own['blocks'][n]['negative']] for n in names]
I=[i for i in range(40) if i not in (0,4,8,12)];J=[i for i in I if i not in (1,2,3,6,7,11)]
assert root['slice_original_coordinate_indices']==I+[40+i for i in J]
assert not root['physical_measure_selected'] and own['opposite_orders_source_contact']
assert 'not a Lean' in root['proof_status']
print('Independent comparison passed: all five exact determinants/inertias and66 native slice indices; host-only scope retained')
