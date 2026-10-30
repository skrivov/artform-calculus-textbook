# 057. The classes of a phase: how a law glues its light cone, and the cut of its reading

Campaign S3 of `BRAINSTORM-SCHEMES-2026-10-29.md` (2026-10-29), part 2.
- The author: "Start campaign S3: the classification axes and normal forms of schemes, using S1's phase and cut as
  invariants."
- Code: `code/scheme_classes.py`, checks 4-7 (`data/scheme-classes.json`). Finding 045 holds the axes, the index and
  the normal forms.
- Plate: 26.

**Question.** Finding 045 showed that the phase does not fix a law: the face and link forms share a phase and differ at
the zero mode. What exactly does the phase leave free? And what does the cut, the reading of a run, add?

**Setting.**
- **Ticks.** A tick is T = [[a, b], [c, d]] ∈ SL₂(F[x, 1/x]), over a field F of characteristic not 2.
  - Its phase is t = a + d.
  - Two ticks are *the same law up to processing* when T′ = P T P⁻¹ for a local P with a local inverse.
- **The curve.** The dispersion relation λ + 1/λ = t(x) is a curve C_t, with x = e^(ik) the shift's eigenvalue and λ the
  tick's. Its ring is A = F[x, 1/x][λ]/(λ² − tλ + 1), and λ is a unit of A.
- **The leapfrog phase** is t = 2 − κλg, g = 2 − x − 1/x, with h² = κλ. It is the phase of the book's tick, of M K,
  Strang and position Verlet, and of the link form.

## 1. Latimer-MacDuffee: a law of a given phase is an ideal class of its curve

**Theorem (Latimer-MacDuffee 1933, over any principal ideal domain).**
- Suppose t² − 4 is not a square in F(x). Then the local conjugacy classes of ticks of phase t correspond one to one
  with the classes of fractional ideals of A, under multiplication by elements of the fraction field.
- The tick T goes to the class of the ideal (c, λ − a). This ideal is cut out by T's left eigenvector u = (c, λ − a),
  for which u T = λ u on C_t.

**Two readings of the same class.**
- *The quadratic form.* Q_T(v) = det[v | T v] = c v₁² + (d − a) v₁v₂ − b v₂² is a binary quadratic form of
  discriminant t² − 4: Gauss's side of the correspondence.
- *The trivial class.*
  - T is in the trivial class iff Q_T represents a unit. A vector v with that property is a *cyclic vector*:
    P = [v | T v] gives T P = P C_t, where C_t = [[0, −1], [1, t]] is the companion tick.
  - So the trivial class is the class of the two-step recurrence u(n+1) + u(n−1) = t u(n) on one channel. It holds
    every tick with c or b a unit.
- *The gluing.*
  - Where two branches of C_t cross, at t(x₀) = ±2, the module of T is invertible exactly when T(x₀) is a Jordan block
    (glued).
  - When T(x₀) = ±I (unglued), it is a module over the curve's normalization there.

## 2. Theorem S3.4: the classes of the leapfrog phase

**Theorem S3.4.** Let h² = κλ ∈ F*, with h² ≠ 1 and t = 2 − h²g.
1. **The curve.**
   - C_t, given by (λ − 1)² x = h²(x − 1)² λ, is rational, with one singular point: a node at the zero mode
     (x, λ) = (1, 1).
   - Its normalization is the s-line, s = (λ − 1)/(x − 1):
     x = h²(1 − s)/(s(s − h²)), λ = s(1 − s)/(s − h²).
   - Four points are missing, s = 0, 1, h², ∞, where x is 0 or ∞.
   - The node's two branches are s = +h and s = −h, the light-cone directions λ − 1 ≈ ±h(x − 1): right- and
     left-moving light.
2. **The classes.**
   - The glued (invertible) classes form the group U/⟨−1, ρ⟩, with ρ = (1 − h)/(1 + h).
   - U = F* when h ∈ F (a split node). When h ∉ F (a non-split node), U is the norm-one group of F(h).
   - There is exactly one unglued class.
   - On a dial C_p, |U| = p − 1 when κλ is a square mod p and p + 1 when it is not.
3. **The class of a tick.**
   - T is glued iff T(1) ≠ I.
   - Then its primitive left eigenvector ũ(s) takes, on the two branches, multiples α₊ and α₋ of T(1)'s one
     eigenvector.
   - Its class is γ(T) = α₊/α₋ modulo ⟨−1, ρ⟩: the ratio in which the law glues right- and left-moving light at the
     zero mode.
4. **The schemes.** The face form, M K, Strang and position Verlet are the trivial class. The link form and link Strang
   are the unglued class.
5. **Time reversal.** T ↦ T⁻¹ swaps the two branches, and sends γ to γ⁻¹.

*Proof.*
- **1.**
  - Clearing 1/x, λ² − tλ + 1 = 0 becomes F = x(λ − 1)² − h²(x − 1)²λ = 0. A singular point has
    F = ∂F/∂λ = ∂F/∂x = 0. From F and ∂F/∂λ, x(λ − 1)(λ + 1) = 0, so λ = ±1.
  - λ = 1 forces x = 1: the node, with tangent cone (λ − 1)² = h²(x − 1)².
  - λ = −1 forces x = 1 − 2/h² and h² = 1, which is excluded.
  - The parametrization is the line through the node of slope s. t² − 4 = h²(x − 1)² q(x)/x² with q not a square, so
    C_t is irreducible.
- **2.**
  - The conductor square of the node gives the exact sequence 1 → A* → Ã* × F* → (Ã/𝔠)* → Pic A → Pic Ã.
  - Ã is a localization of F[s], so Pic Ã = 0, and Ã* = F* × ⟨s, s − 1, s − h²⟩.
  - (Ã/𝔠)* = F* × F* at the two branches in the split case, and F(h)* in the non-split case.
  - Modulo the diagonal F*, the class is the ratio f(h)/f(−h), and in the non-split case z/z̄ (Hilbert 90).
  - The units s, s − 1, s − h² give −1, ρ and −ρ.
  - A node is a Gorenstein (Bass) singularity, so every fractional ideal is invertible or a module over the
    normalization at the node. The latter form one class, since Pic Ã = 0.
- **3.**
  - This is the patching datum of the module M_T. The left eigenvector, made primitive over Ã, trivializes M_T ⊗ Ã.
  - At the node both branch values lie in the fibre of M_T, which is the eigenline of the Jordan block.
- **4.**
  - The face form, M K and position Verlet all have c = κ, a unit, so all three are trivial. Strang is
    K(κ/2) T K(−κ/2), a conjugate of the face form's T.
  - The link form has T(1) = I, and so does link Strang.
- **5.** The module of T⁻¹ is that of T with λ replaced by 1/λ. On the curve λ ↦ 1/λ is the involution
  s ↦ (s − h²)/(s − 1), which swaps the branches s = +h and s = −h, so γ goes to γ⁻¹ (up to the units). ∎

**Over the reals** the glued classes are R*/⟨−1, ρ⟩ = R_(>0)/ρ^Z for 0 < h < 1: a circle of laws of one phase, plus the
unglued one. On a dial the circle becomes a finite cyclic group, of order (p ∓ 1)/|⟨−1, ρ⟩|.

At most (p ∓ 1)/4 classes are glued, with equality exactly at κλ = −1.
- ρ = 1 would need h = 0, and ρ = −1 is impossible, so ρ has order at least 3.
- If its order is 3, then |⟨−1, ρ⟩| = 6. Order 4 needs ρ² = −1, which is (1 − h)² = −(1 + h)², or h² = −1. Then
  ρ = −h and ⟨−1, ρ⟩ = ⟨ρ⟩ has order 4.
- So |⟨−1, ρ⟩| ≥ 4. There are 5 glued classes on C_19 and 9 on C_37.

*Checked* (checks 4 and 5). The ticks are T = [[a, b], [c, t − a]] over F_p, with a supported on x⁻¹, 1, x and
bc = a(t − a) − 1 factored in every way (b monic).

| dial p | κλ | node | \|U\| | glued classes, predicted | labels found | ticks | class sizes (0, 1, …; U) | same-class P of width ≤ 3 found |
|---|---|---|---|---|---|---|---|---|
| 7 | 2 | split | 6 | 1 | 2 | 1056 | 954; 102 | 12/12 |
| 13 | 4 | split | 12 | 2 | 3 | 8520 | 5580, 2520; 420 | 9/12 |
| 13 | 12 | split | 12 | 3 | 4 | 8520 | 4740, 1680, 1680; 420 | 9/12 |
| 17 | 16 = −1 | split | 16 | 4 | 5 | 20256 | 10480, 3008, 3008, 3008; 752 | 7/12 |
| 19 | 6 | split | 18 | 3 | 4 | 28872 | 16470, 5724, 5724; 954 | 6/12 |
| 7 | 3 | non-split | 8 | 1 | 2 | 1260 | 1158; 102 | 12/12 |
| 11 | 10 = −1 | non-split | 12 | 3 | 4 | 5500 | 2890, 1160, 1160; 290 | 11/12 |
| 17 | 11 | non-split | 18 | 3 | 4 | 21760 | 11984, 4512, 4512; 752 | 7/12 |
| 19 | 18 = −1 | non-split | 20 | 5 | 6 | 30780 | 14562, 3816, 3816, 3816, 3816; 954 | 10/12 |

On all nine dials the labels found are exactly the predicted classes. Two regularities are observed: the
non-trivial glued classes of one dial have equal sizes, and the size of the unglued class depends only on p.

On every dial:
- **The labels.**
  - The labels realized are exactly the predicted number of classes.
  - 120 random local conjugations never change a label.
  - No conjugator of width ≤ 2 links different labels.
  - Time reversal sends l to −l, and the unglued class to itself.
- **Cyclic vectors** (searched exhaustively at width 1, and at width 2 on p ≤ 13):
  - No tick outside the trivial class has one.
  - Trivial ticks have them. Each one found gives P with T P = P C_t and det P a unit monomial.
- **The schemes** sit where part 4 says.
- **Same-class conjugators.** The bounded search (width ≤ 3) finds them for most pairs. The rest need wider P.

## 3. Theorem S3.5: the magic step, two light cones glued twice

**Theorem S3.5.** At κλ = 1 the phase is x + 1/x, and C_t is the two light cones λ = x and λ = 1/x, which cross at x = 1
(λ = 1) and x = −1 (λ = −1). The classes are:
- those **glued at both crossings**, F*/{±1}. The invariant is the ratio r(−1)/r(1) of the two gluings, where r(x₀) is
  the ratio of the two cones' eigenvector germs at x₀;
- **glued at x = 1 only**, **glued at x = −1 only**, and **glued at neither**: one class each.

On C_p there are (p − 1)/2 + 3 classes.
- The book's face form, M K, Strang and position Verlet are the trivial class (glued at both, ratio 1).
- The link form is glued at −1 only.
- The split movers diag(x, 1/x) are glued at neither.

*Proof.* Each cone is a copy of F[x, 1/x], whose units c xᵐ rescale the two eigenvector germs. That changes the
gluings at x = 1 and x = −1 by (c₁/c₂, (c₁/c₂)(−1)^(m₁−m₂)), so only r(−1)/r(1), mod ±1, survives. A class glued at
one crossing only has no invariant left. ∎

*Checked* (check 6):

| dial p | ticks | classes found | (p − 1)/2 + 3 | glued at both (class sizes) | at x = 1 only | at x = −1 only | neither |
|---|---|---|---|---|---|---|---|
| 5 | 707 | 5 | 5 | 324, 232 | 72 | 72 | 5 |
| 7 | 2211 | 6 | 6 | 858, 516, 516 | 156 | 156 | 7 |
| 11 | 9683 | 8 | 8 | 3150, 1420, 1420, 1420, 1420 | 420 | 420 | 11 |
| 13 | 16515 | 9 | 9 | 5100, 2040, 2040, 2040, 2040, 2040 | 600 | 600 | 13 |

Two counts are symmetric.
- Classes glued at one crossing only come in equal numbers at x = 1 and at x = −1, as the symmetry (x, λ) ↦ (−x, −λ)
  of the phase requires: it fixes x + 1/x up to sign, keeps the curve and swaps the two crossings.
- The non-trivial classes glued at both crossings have equal sizes (observed).

"Neither" counts the split ticks that were added by hand (b = 0 or c = 0).

## 4. Theorem S3.6: the cut is the reading, and a cut-free reading needs a symmetric class

**Theorem S3.6.**
1. **The reading.**
   - From rest, the output of a tick of phase t is fixed by its reading a, through
     b_n = [cos nθ + ((a − d)/2) sin nθ / sin θ] b_0 (finding 044).
   - Conversely the output fixes a: b_1 = a b_0.
   - So (t, a) is the complete invariant of the output, and the cut a − d = 2a − t is the reading.
2. **Free readings.** In the trivial class every reading occurs: T = [[a, 1], [a(t − a) − 1, t − a]], for any a.
3. **Cut-free readings need a symmetric class.**
   - A palindromic tick (a = d, cut 0) satisfies P₀ T P₀ = T⁻¹ with P₀ = diag(1, −1). So its class is fixed by time
     reversal: γ² = 1 in U/⟨−1, ρ⟩, or the unglued class.
   - In a cyclic group of order m this leaves one or two glued classes.
   - In every other class the cut cannot be removed by processing.

*Proof.*
- **1.** b_1 = a b_0 and b_2 = (ta − 1) b_0.
- **2.** b = 1 is a unit.
- **3.** Theorem S3.4, part 5. ∎

*Checked* (check 7), on C_17 with κλ = 16, which has four glued classes:
- On a ring of 9 faces from an impulse, two ticks of the phase have the same outputs for 12 ticks when their a agree,
  and different ones when their a differ.
- Every reading tried lies in the trivial class.
- The 960 palindromic ticks lie in classes 0, 2 and U, exactly the classes time reversal fixes. They never lie in 1 or
  3, and they do lie in 2: here a cut-free reading exists exactly in the symmetric classes.

## 5. What the classes mean

- **The phase is the curve, and the curve crosses itself.** At the zero mode the right- and left-moving branches of light
  meet. A local law must say how its eigenvectors on the two branches join there.
- **The book's schemes glue them as the two-step recurrence does.** That is the trivial class. The face form is the
  recurrence e(n+1) + e(n−1) = t e(n) of its potential, and (b, e) ↔ (e(n), e(n+1)) is a local change of variables,
  since b(n) = (e(n+1) − e(n))/κ.
- **The link form leaves the crossing unglued.** There the zero mode decouples into static fields, the class over the
  curve's normalization.
- **Every other glued class twists the junction by γ.** On a dial these laws form a cyclic group whose order is
  (p − 1) or (p + 1) over |⟨−1, ρ⟩|, according to the Legendre symbol (κλ/p). Over the reals they form a circle.
- **The cut is not a property of the law.** It is the reading of a run. But a cut-free (time-symmetric) reading exists
  only in the classes time reversal fixes. So for most laws of a phase, Strang's trick cannot be played.

## What is known, and what looks new

*Known:*
- Latimer and MacDuffee 1933, and Taussky 1949: matrices, ideals and Gauss's forms.
- Bass 1963 on Gorenstein orders; Milnor 1971 on patching. Generalized Jacobians of singular curves (Rosenlicht;
  Serre, Algebraic Groups and Class Fields).
- Isospectral matrices and line bundles on the spectral curve (van Moerbeke and Mumford 1979; Beauville 1990). There
  the conjugations are constant; here they are local, which gives the affine curve's Picard group.

*New, as far as we found:*
- The dispersion curve of the book's tick is a rational curve with a node at the zero mode, and its class group
  classifies the laws of that phase. The group is U/⟨−1, ρ⟩, with the p ∓ 1 dichotomy of (κλ/p).
- The face and link forms are the trivial and the unglued class.
- The magic step has (p − 1)/2 + 3 classes.
- Cut-free readings exist only in classes fixed by time reversal.

## Open

- **Higher-order phases.** The curves of Forest-Ruth and Suzuki have higher genus. Their Picard groups then contain a
  Jacobian, so the number of laws of such a phase on C_p is a point count of a curve. That is the ledger's arithmetic
  in a new role (findings 028-029).
- **2D.** The dispersion surface has a conical (A₁) singularity at the zero mode, whose local class group is Z/2. Are the
  face and link forms its two classes?
- **Laws of a class.** Which physical schemes realize the non-trivial glued classes (kicks with smoothing stencils)?
  Do their runs differ visibly from the book's?

## References

- C. G. Latimer, C. C. MacDuffee, Ann. of Math. 34 (1933) 313-316; O. Taussky, Canad. J. Math. 1 (1949) 300-302.
- H. Bass, Math. Z. 82 (1963) 8-28; J. Milnor, Introduction to Algebraic K-Theory, Princeton 1971.
- J.-P. Serre, Algebraic Groups and Class Fields, Springer 1988 (generalized Jacobians).
- P. van Moerbeke, D. Mumford, Acta Math. 143 (1979) 93-154; A. Beauville, Acta Math. 164 (1990) 211-235.
