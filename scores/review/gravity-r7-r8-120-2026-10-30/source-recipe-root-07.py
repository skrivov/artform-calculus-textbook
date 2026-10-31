"""Replay the supplied fixed-reference source expression using exact fractions."""

from fractions import Fraction as Q
import json

def residue(q):
    q = Q(q)
    assert q.denominator % 13
    return q.numerator * pow(q.denominator, -1, 13) % 13
kap = Q(1, 101)
a = Q(101, 103)
g = Q(101, 97)
e = Q(202, 9991)
hd = Q(9999, 9991)
d = Q(10201, 10300)
bp = Q(101, 39964)
b3 = Q(1, 19982)
b = Q(-10201, 20600)
cv = b3 - 2 * Q(-1, 82400)
k = (1, 2, 3)
u = tuple((Q(x, 103) + 2 * Q(y, 9991) - Q(z, 20600) for x, y, z in zip((31, 2582, -1419), (98, 2716, -1218), (2059, 3314, 3765))))
kinv = [[Q(i == j) / hd + (1 / d - 1 / hd) * k[i] * k[j] / 14 for j in range(3)] for i in range(3)]
y = tuple((Q(101, 490) * sum((kinv[i][j] * u[j] for j in range(3))) for i in range(3)))

def moment(n, v):
    return sum((ki ** n * vi for ki, vi in zip(k, v)))
m1, m2, m3 = (moment(n, y) for n in (1, 2, 3))
w1 = 18 * (hd + d) * m1 + 7 * (d - hd) * m2 - Q(7056, 5) * kap * b
w2 = 18 * (hd + d) * m2 + 49 * (d - hd) * m1 + (1876 * hd - 18144 * kap * b) / 5
p1 = -w1 / (7 * d)
p2 = -(w2 / hd + (1 / d - 1 / hd) * Q(18, 7) * w1) / 7
n1 = Q(-297, 505) - Q(10300, 707) * cv * (14 * m2 - 36 * m1)
n2 = (202 / hd * (Q(38, 7) * cv * m1 - Q(5332, 5) * b3) + 36 * n1) / 14
bm = 14 * p2 - 36 * p1
cm = -36 * m2 + 98 * m1
dm = -14 * m3 + 98 * m1
rz = 14 * n2 - 36 * n1
hm = bm - dm
a5 = kap * a * a / 12
c4 = kap * kap * a * a * g * g / 2
bc4 = (1 - 4 * kap) * c4
l5 = a5 + e / 24
l4e = -a5 + bc4 + e / 24
l4s = c4 - e / 24
f3 = kap * kap * g * a * hm / 2 - kap * e * rz / 2
v2 = -f3 / 6 + Q(1092, 5) * b3 - 36 * kap * (hd + e) * b3
v3 = Q(3752, 5) * kap * kap * g * a * bp
v4 = kap * kap * a * a * rz / 12
v5 = kap * ((341 * a5 + 2935 * bc4) / 5 + Q(6211, 120) * e) - kap * (l5 * bm + l4e * cm + l4s * dm) / 2
values = (v2, v3, v4, v5)
total = sum(values)
assert tuple(map(residue, values)) == (0, 3, 3, 9) and residue(total) == 2 and (total != 0)
principal = [[hd * Q(i == j) + (d - hd) * k[i] * k[j] / 14 for j in range(3)] for i in range(3)]
assert all((sum((principal[i][j] * y[j] for j in range(3))) == Q(101, 490) * u[i] for i in range(3)))
output = {'status': 'passed', 'scope': 'Independent exact replay of supplied fixed-reference recipe and coupled moment recurrences; actual full40/source/constructor identification not inferred.', 'y_residues': list(map(residue, y)), 'moment_residues': [residue(x) for x in (m1, m2, m3, p1, p2, n1, n2)], 'group_residues': list(map(residue, values)), 'total_residue': residue(total), 'group_values': [str(x) for x in values], 'total_value': str(total), 'total_bitlengths': [total.numerator.bit_length(), total.denominator.bit_length()], 'original_principal_equation_verified': True, 'new_physical_credit': 0, 'historical_saving_credit': 0}
print(json.dumps(output, indent=2))
