# 064. The laws of a higher-order phase: the frequency curve counts them

Campaign S3 of `BRAINSTORM-SCHEMES-2026-10-29.md` (2026-10-29), part 3: the open problem "higher-order phases" of
finding 057.
- The author: "do higher genus phases".
- Code: `code/scheme_genus.py`, seven checks, all pass (`data/scheme-genus.json`, about 2.5 min).
- Plate: 27.

**Question.** Finding 057 classified the laws of the leapfrog phase: a rational curve with one node, U/⟨−1, ρ⟩ glued
classes and one unglued class. A scheme of higher order has a phase of higher degree, whose curve has higher genus.
How many laws does such a phase have on a dial? And where do the schemes sit among them?

**Setting.** As in finding 057.
- **Laws.** A tick is T = [[a, b], [c, d]] ∈ SL₂(F_p[x, 1/x]) on the channels (b, e). Two ticks are the same law when
  T′ = P T P⁻¹ for a local P with a local inverse (processing). By Latimer and MacDuffee the laws of a phase t = a + d
  are the ideal classes of A = F_p[x, 1/x][λ]/(λ² − tλ + 1), and T goes to the class of the ideal (c, λ − a).
- **Phases of degree m.** t = P(g) with g = 2 − x − 1/x, P(0) = 2 and P′(0) = −κλ = −h²; write P − 2 = gQ.
  - Degree 1 is the leapfrog, t = 2 − h²g (finding 057).
  - Degree 2: the **fourth-order stencil**, t = 2 − κλ(g + g²/12). Its face form is M(−λG₄)K(κ) with
    G₄ = g + g²/12 = (x² − 16x + 30 − 16/x + 1/x²)/12.
  - Degree 3: **Forest-Ruth**, K(θ/2) M(θ) K((1 − θ)/2) M(1 − 2θ) K((1 − θ)/2) M(θ) K(θ/2), with moves M(−wλg) and
    6θ(θ − 1)² = 1. On a dial this needs θ ∈ F_p: θ = 4 on C₅, 2 on C₁₁, 14 on C₁₇, 18 on C₂₃.
  - Suzuki's fourth-order score has degree 5.

## 1. Theorem S3.7: the curve of a phase of degree m

**Theorem S3.7.** Let t = P(g) have degree m ≥ 1, and let F(x) = −x^(2m−1) Q(g)(P(g) + 2) be squarefree (the generic
case).
1. **The node and the genus.**
   - The curve C: λ + 1/λ = t has exactly one singular point, a node at the zero mode (x, λ) = (1, 1). Its branches
     are λ − 1 ≈ ±h(x − 1), the light moving right and left.
   - Its normalization C̃ is the hyperelliptic curve Y² = F(x), with Y = (2λ − t) xᵐ/(x − 1). It has degree 4m − 2 and
     genus 2m − 2. The node's branches are the points (1, ±2h).
2. **The frequency curve and its twist.**
   - Parity ι: x ↦ 1/x and time reversal τ: λ ↦ 1/λ act on C̃ as a Klein four-group. τ is the hyperelliptic
     involution.
   - The quotient by ι is the **frequency curve** E: λ + 1/λ = P(g), that is y² = P(g)² − 4 over the g-line. It is
     the dispersion relation with the direction of the wave forgotten.
   - The quotient by ιτ is its **twist** E′: w² = (g − 4)Q(g)(P(g) + 2), with w = (x − 1/x)(λ − 1/λ)/g.
   - Both have genus m − 1, and the Jacobian splits up to isogeny: J(C̃) ∼ J(E) × J(E′). So on a dial
     #J(F_p) = #J_E(F_p) · #J_E′(F_p).
   - On E the zero mode g = 0 is a smooth point, a branch point of y. The node of C comes from the double zero of
     g = −(x − 1)²/x.
3. **The cusps.**
   - Four points of C̃ lie over x = 0 and x = ∞: P₀± and P_∞±, on the branch where λ → ∞ (+) or λ → 0 (−).
   - x and λ are units, so div x = P₀⁺ + P₀⁻ − P_∞⁺ − P_∞⁻ and div λ = m(P₀⁻ + P_∞⁻ − P₀⁺ − P_∞⁺).
   - Hence e₁ = [P₀⁺ − P_∞⁻] has order dividing 2m: 2m·e₁ = div(xᵐ/λ). Let e₂ = [P₀⁻ − P_∞⁻]. The cusps generate
     H = ⟨e₁, e₂⟩ ⊂ J(F_p).
   - ι fixes e₁ and negates e₂, so e₁ lies on the E side and e₂ on the E′ side.

*Proof.*
- **1.**
  - t² − 4 = gQ(g)(P(g) + 2) = (x − 1)² F(x)/x^(2m), so Y² = F, and F has degree 4m − 2.
  - A singular point of C needs a multiple root of t² − 4 in x. When F is squarefree, the only one is the double root
    x = 1 of g.
  - There (λ − 1)²/λ = gQ(g) ≈ −Q(0)(x − 1)² = h²(x − 1)², which is a node.
- **2.**
  - ι fixes g, hence t and λ. Its fixed field is F(g, λ), the curve E.
  - w changes sign under both ι and τ, so it is fixed by ιτ, and w² = (g − 4)Q(g)(P(g) + 2) from
    (x − 1/x)² = g(g − 4) and (λ − 1/λ)² = P² − 4.
  - For a Klein group of automorphisms with quotients of genus g₁, g₂, g₃, J(C̃) ∼ J₁ × J₂ × J₃ (Kani and Rosen
    1989). Here the genera are m − 1, m − 1 and 0, and indeed 2m − 2 = (m − 1) + (m − 1).
  - Isogenous abelian varieties over F_p have the same number of points.
- **3.**
  - Near x = 0 the two branches are λ ≈ t ≈ x^(−m) and λ ≈ 1/t.
  - ι maps P₀± to P_∞± and keeps the sign.
    - By div x, [P_∞⁺ − P_∞⁻] = e₁ + e₂. So ι(e₁) = [P_∞⁺ − P₀⁻] = (e₁ + e₂) − e₂ = e₁.
    - ι(e₂) = [P_∞⁻ − P₀⁻] = −e₂. ∎

*Checked* (check 1, nine dials of the fourth-order phase and three of Forest-Ruth):
- F is squarefree of degree 4m − 2.
- #J from the zeta function, out of point counts over F_p ... F_(p^(2m−2)), equals #J_E · #J_E′.
- div x = 0 and 2m·e₁ = 0 hold exactly, also with the gluing at the node; e₁ has order exactly 2m on every dial.
- [Q⁺ − Q⁻] has order m on E.
- On six dials Cantor's group law is associative. The rational points generate J, with #J elements, and the
  generalized Jacobian J_𝔪 of the node, with #J · (p ∓ 1) elements.

| phase | dial | κλ | genus | #J | #J_E · #J_E′ | order of e₁ |
|---|---|---|---|---|---|---|
| fourth-order | C₅ | 1 | 2 | 64 | 8 · 8 | 4 |
| fourth-order | C₇ | 2 | 2 | 96 | 8 · 12 | 4 |
| fourth-order | C₁₁ | 1 | 2 | 168 | 12 · 14 | 4 |
| fourth-order | C₁₁ | 2 | 2 | 128 | 8 · 16 | 4 |
| fourth-order | C₁₃ | 1 | 2 | 192 | 16 · 12 | 4 |
| fourth-order | C₁₃ | 2 | 2 | 216 | 12 · 18 | 4 |
| fourth-order | C₁₃ | 12 | 2 | 320 | 16 · 20 | 4 |
| fourth-order | C₁₇ | 2 | 2 | 384 | 16 · 24 | 4 |
| fourth-order | C₁₇ | 3 | 2 | 256 | 16 · 16 | 4 |
| Forest-Ruth | C₅ | 3 | 4 | 768 | 24 · 32 | 6 |
| Forest-Ruth | C₁₁ | 2 | 4 | 19584 | 144 · 136 | 6 |
| Forest-Ruth | C₁₁ | 3 | 4 | 14976 | 144 · 104 | 6 |

## 2. Theorem S3.8: the number of laws on a dial

**Theorem S3.8.** Under the hypotheses of S3.7, on C_p:
- the **unglued laws** (T(1) = I) form Pic Ã = J(F_p)/H, so there are #J/|H| of them;
- the **glued laws** (T(1) a Jordan block) form Pic A, an extension of J/H by U/V, so there are #J·|U|/(|H|·|V|).

Here:
- U = F_p* when κλ is a square mod p (a split node) and the norm-one group of F_(p²) when it is not, so |U| = p ∓ 1;
- V ⊂ U is the set of gluings f(P⁺)/f(P⁻) of the units f of Ã.

In all, N = (#J_E(F_p) · #J_E′(F_p)/|H|) · (1 + |U|/|V|) laws: point counts of the frequency curve and its twist,
divided by what the cusps generate. For m = 1, J = 0 and V = ⟨−1, ρ⟩, and this is Theorem S3.4.

*Proof.*
- **Pic Ã.**
  - Ã is the ring of C̃ with the four cusps removed. C̃ has rational points, so Pic⁰ C̃ = J(F_p).
  - Removing points divides by the classes they generate, so Pic Ã = J(F_p)/H.
- **Pic A.**
  - The conductor square of the node gives 1 → A* → Ã* → U → Pic A → Pic Ã → 0, exactly as in finding 057.
  - The image of Ã* in U is V.
  - Equivalently, Pic A = J_𝔪(F_p)/H_𝔪. Here J_𝔪 is the generalized Jacobian of the node (Rosenlicht; Serre), an
    extension of J by the torus U, and H_𝔪 is generated by the cusps.
- **The unglued laws.** A node is a Gorenstein singularity. So every fractional ideal that is not invertible is a
  module over the normalization at the node, and those form Pic Ã. ∎

**How the classes are computed.** The ideal (c, λ − a) is a divisor on C̃, the Mumford pair
(c, Y ≡ 2xᵐ(a − 1)/(x − 1) + x^(m−1)(x − 1)Q(g) mod c). An unglued tick first gives
(c/(x − 1), s − (a − 1)/(x − 1)), with s = (λ − 1)/(x − 1).
- Cantor's algorithm runs on the odd model at a rational root r of F, with x = r + 1/z and W = Y z^(2m−1).
- Each reduction step D = D′ + div((W − v)/u′) multiplies the gluing μ by the ratio of the leading coefficients of
  W − v at the two branches (1, ±2h). Functions of x alone have the same leading coefficient on both branches.
- This gives every tick a label (a reduced divisor, μ) in J_𝔪. A label modulo H_𝔪 is its law.

*Checked* (check 2). The ticks are T = [[a, b], [c, t − a]] over F_p, with a supported on x⁻¹, 1, x (on x⁻² ... x² for
Forest-Ruth) and bc = a(t − a) − 1 factored in every way (b monic).

| phase | dial | κλ | node | #J | \|H\| | \|U\| | \|V\| | glued: predicted = found | unglued: predicted = found | ticks |
|---|---|---|---|---|---|---|---|---|---|---|
| fourth-order | C₅ | 1 | split | 64 | 16 | 4 | 2 | 8 | 4 | 869 |
| fourth-order | C₇ | 2 | split | 96 | 12 | 6 | 3 | 16 | 8 | 2385 |
| fourth-order | C₁₁ | 1 | split | 168 | 28 | 10 | 5 | 12 | 6 | 8499 |
| fourth-order | C₁₁ | 2 | non-split | 128 | 32 | 12 | 6 | 8 | 4 | 8091 |
| fourth-order | C₁₃ | 1 | split | 192 | 12 | 12 | 3 | 64 | 16 | 12745 |
| fourth-order | C₁₃ | 2 | non-split | 216 | 36 | 14 | 7 | 12 | 6 | 15559 |
| Forest-Ruth | C₅ | 3 | non-split | 768 | 48 | 6 | 1 | 96 | 16 | 25174 |

On all seven dials the enumeration finds exactly the predicted laws, no more and no fewer. With a supported on
x⁻¹, 1, x only, Forest-Ruth on C₅ shows 82 + 14 of its 96 + 16 laws: higher genus needs wider ticks.

*Checked* (check 3, C₁₃ and C₁₁):
- 120 random local conjugations, each by a score of four shears with random stencils, never change a law.
- The conjugates of the 80 (and 12) class representatives stay in distinct classes.
- T⁻¹ always has the negative class.

**Across the dials** (check 7). There are 31 pairs (p, κλ) with p ≤ 19 where the fourth-order curve has no further
singular point and an odd model exists. On each, #J = #E · #E′, 4 divides #E, e₁ has order 4 and [Q⁺ − Q⁻] has order 2.
The predicted number of laws runs from 12 (C₅, κλ = 1) to 252 (C₁₉, κλ = 8: 240 glued and 12 unglued). |U/V| is 2 on
21 of the dials and 4, 6, 14 or 20 on the others. So the count swings with the point counts and with the units.

## 3. Theorem S3.9: symmetric scores live on the frequency curve

A tick is *symmetric* when its entries are polynomials in g, so it commutes with parity. This covers the face form
of every score whose kicks are constants and whose moves are M(−wλg): the leapfrog, Strang, position Verlet,
Forest-Ruth, Suzuki and every triple jump.

**Theorem S3.9.**
1. **The classes on E.** Symmetric ticks of phase P, up to conjugation over F_p[g], are the ideal classes of
   A_E = F_p[g][λ]/(λ² − Pλ + 1), the ring of the frequency curve with its two points over g = ∞ removed (Q⁺, Q⁻).
2. **Their number.**
   - When F is squarefree, A_E is smooth, so Pic A_E = J_E(F_p)/⟨[Q⁺ − Q⁻]⟩.
   - [Q⁺ − Q⁻] has order dividing m (div λ = m(Q⁻ − Q⁺)).
   - So there are #J_E(F_p)/m classes. For the fourth-order stencil that is #E(F_p)/2.
3. **Glued.** Every symmetric tick is glued. Its law is the pullback π*: Pic A_E → Pic A along x ↦ g, and the kernel
   of π* lies in the 2-torsion.

*Proof.*
- **1.** Latimer-MacDuffee over the principal ideal domain F_p[g].
- **2.** As in Theorem S3.8, with the zero mode a smooth point of E.
- **3.**
  - A = A_E ⊗ F_p[x, 1/x] over F_p[g], so the module of the tick over A is the pullback. A pullback of an
    invertible module is invertible, hence glued.
  - Pushing forward after pulling back multiplies by the degree, 2, so the kernel of π* lies in the 2-torsion. ∎

*Checked* (check 4). The symmetric ticks are [[a, b], [c, P − a]] over F_p[g], with deg a ≤ 2 (≤ 1 for Forest-Ruth on
C₁₁) and bc = a(P − a) − 1 factored in every way:

| phase | dial | κλ | #J_E | order of [Q⁺ − Q⁻] | classes on E: predicted = found | laws they give | map | symmetric ticks |
|---|---|---|---|---|---|---|---|---|
| fourth-order | C₇ | 2 | 8 | 2 | 4 | 4 | one to one | 1470 |
| fourth-order | C₁₁ | 1 | 12 | 2 | 6 | 6 | one to one | 6050 |
| fourth-order | C₁₃ | 1 | 16 | 2 | 8 | 8 | one to one | 11076 |
| fourth-order | C₁₃ | 2 | 12 | 2 | 6 | 6 | one to one | 9204 |
| Forest-Ruth | C₅ | 3 | 24 | 3 | 8 | 4 | two to one | 562 |
| Forest-Ruth | C₁₁ | 3 | 144 | 3 | 48 | 24 | two to one | 610 |

So of the 80 laws on C₁₃ (κλ = 1), the symmetric ones are 8, the points of the frequency curve modulo its 2-torsion
point [Q⁺ − Q⁻].

## 4. Theorem S3.10: the face form, the link form, and where the schemes sit

**Theorem S3.10.** Take a score of constant kicks K(wκ) and moves M(−wλg), with κ times the sum W of its kick
weights nonzero. On a nodal phase its face form is glued and its link form (kicks K(wκD*), moves M(−wλD))
is unglued. The link form forgets the gluing at the zero mode: the extended eigenvector ideals on the
normalization satisfy I_link Ã = (D*) I_face Ã, so they have the same fractional ideal class.
The intertwining identity holds for every score, including Wκ = 0; gluedness does not.

*Proof.*
- **The two forms at the zero mode.** The link form is Λ T Λ⁻¹ with Λ = diag(1, D*), so a, d are the same,
  c_link = D* c and b_link = b/D*.
  - At x = 1 every move vanishes, so T(1) = K(Wκ) and c(1) = Wκ ≠ 0: the face form is glued.
    Empty scores and cancelling kick weights show why this hypothesis is necessary.
  - The link form has T_link(1) = I: it is unglued.
- **Over Ã.**
  - Away from x = 1, D* is a unit, so the two ideals agree.
  - At the branches (1, ±2h), (c, λ − a) is the unit ideal. (D* c, λ − a) is the maximal ideal of each branch,
    because D* c has a simple zero there and λ − a vanishes there.
  - Algebraically, a−1, b and d−1 are divisible by (D*)². The characteristic equation makes
    (λ−a)² divisible by (D*)². Integral closedness gives λ−a = D*z. Since c and D* are coprime,
    (c,z) = (c,D*z). Hence (D*c,λ−a) = (D*)(c,λ−a). This is the Lean theorem
    `faceAndLinkNormalization`, valid in every normal domain extension and awaiting independent review. ∎

**The fourth-order stencil.** Its face form has c = κ, a unit, so it is the trivial class: locally, the two-step
recurrence of its phase. Its link form is the trivial unglued class (check 6, six dials).

**Laws in two steps with split kicks.** M(f)K(e) with ef = t − 2 is a law of the phase for every factorization of
t − 2 = −(κλ/12)(x − 1)²(x² − 14x + 1)/x². Its reading is a = t − 1, the face form's.
- On C₁₃ (κλ = 1), x² − 14x + 1 = (x − 4)(x − 10). The 12 factorizations give 6 laws: the trivial class, three other
  glued laws, the trivial unglued class and one other unglued law.
- The kick e = x − 4 has a root at a static point of the curve: a point with λ = 1 other than the zero mode, on
  x² − 14x + 1 = 0. Over the reals that is x = 7 ± 4√3, an evanescent wave; on C₁₃ it is x = 4 or 10. The kick gives
  a glued law outside the trivial class.
- From a bump on a uniform flux at rest, on a ring of 24 faces, it gives the face form's b at every one of 20 ticks
  and a different e (Plate 27d).
- The law is invisible in the reading and visible in the other channel. This is Theorem S3.6 at work: (t, a) fixes
  the output from rest.

**Forest-Ruth.** Its face form is a symmetric tick with c of degree 3 in g, so its law is a point of the frequency
curve's Jacobian.

| dial | θ | steps κλ checked | face form outside the trivial class | link form outside the trivial unglued class |
|---|---|---|---|---|
| C₅ | 4 | 1 | 1 | 0 |
| C₁₁ | 2 | 6 | 6 | 4 |
| C₁₇ | 14 | 11 | 10 | 10 |
| C₂₃ | 18 | 17 | 17 | 13 |

(Check 6: every step κλ with a smooth curve away from the node and an odd model.)
- In 34 of 35 cases Forest-Ruth's face form is not the trivial class. So no local change of variables makes it the
  two-step recurrence of its phase on one channel. The leapfrog, Strang and the fourth-order face form are that
  recurrence.
- On C₅ the difference lies only in the gluing at the zero mode (its link form is trivial). On most other dials it
  is a nontrivial point of J/H.
- The link form forgets the gluing every time.

## 5. Time reversal and cut-free readings

- Time reversal T ↦ T⁻¹ is τ, the hyperelliptic involution. It acts on J as −1 and swaps the node's branches, so it
  inverts the gluing μ. Hence the law of T⁻¹ is the negative of T's (check 3).
- A palindromic tick (a = d, cut 0) satisfies P₀ T P₀ = T⁻¹ with P₀ = diag(1, −1) (Theorem S3.6). So its law is fixed
  by time reversal: it is 2-torsion in the class group.

*Checked* (check 5):

| phase | dial | κλ | laws | fixed by time reversal | palindromic ticks |
|---|---|---|---|---|---|
| fourth-order | C₇ | 2 | 24 | 12 | 48 |
| fourth-order | C₁₁ | 2 | 12 | 12 | 96 |
| fourth-order | C₁₃ | 1 | 80 | 12 | 48 |
| fourth-order | C₁₃ | 2 | 18 | 6 | 24 |
| Forest-Ruth | C₅ | 3 | 112 | 24 | 192 |

On the higher-order cases listed in this table the enumerated palindromic ticks meet every law fixed by time
reversal. This is a finite-case observation. In general only the forward implication holds: a palindrome
lies in a time-reversal-fixed class. The converse fails, including for the leapfrog at (p, κλ) = (11, 8)
(ALGEBRA-OF-SCORES, T12). Here the palindromes are the ticks with a = t/2, and
bc = (t² − 4)/4 is factored in every way.

## 6. What the classes mean

- **A phase of degree m fixes a law up to a point of a curve of genus 2m − 2, and a gluing.** For the leapfrog the
  curve is rational, so only the gluing at the zero mode is left (finding 057). From degree 2 on there is also a point
  of a Jacobian: a law can join its eigenvectors over the whole curve in #J/|H| inequivalent ways before the node is
  even reached.
- **The frequency curve does the counting.** J ∼ J_E × J_E′. E is the dispersion relation λ + 1/λ = P(g) with the
  direction of the wave forgotten; E′ is its twist by g(g − 4) = (x − 1/x)². The cusps cut J down by H.
  - On the E side the time step gives e₁, of order dividing 2m; the computed cases have exact order 2m.
  - On the E′ side lies e₂. Its order is a regulator: J(F_p) is finite, so some multiple of e₂ is the divisor of a
    unit of the dial.
  So the number of laws on a dial is a class number of the curve: #J divided by a regulator, as in Artin's class
  number formula for quadratic function fields.
- **Symmetric schemes are points of the frequency curve.** Every face form built from constant kicks and g-moves is a
  class of E, #J_E/m of them on a dial. The fourth-order stencil sits at the origin. Forest-Ruth almost never does.
  So Forest-Ruth, though built from leapfrog steps, is not locally the recurrence of its own phase: it remembers how it
  was composed.
- **The link form forgets the gluing.** Putting e on links keeps the law on the normalization and drops the gluing at
  the zero mode, for scores with nonzero κ times total kick.
- **What a run shows.** The law is invisible in the reading b, which (t, a) fixes, and visible in the other channel
  (Plate 27d).

## What is known, and what looks new

*Known:*
- Latimer and MacDuffee 1933; the conductor square, Gorenstein orders and patching (Bass 1963; Milnor 1971);
  generalized Jacobians (Rosenlicht; Serre).
- Cantor's algorithm for hyperelliptic Jacobians (Cantor 1987).
- Jacobians split by a Klein group of automorphisms (Kani and Rosen 1989).
- The class number formula of a quadratic function field, h·R = #J (Artin 1924), and S-class numbers (Rosen 2002,
  ch. 14).
- Forest-Ruth and Yoshida's fourth-order compositions (1990); Suzuki 1990.

*New, as far as we found:*
- The laws of a two-channel phase of degree m are classes on a curve of genus 2m − 2. Their number on C_p is
  #J_E · #J_E′ · (1 + |U|/|V|)/|H|, and it is verified by enumeration.
- Symmetric scores live on the frequency curve E.
- Forest-Ruth's face form is outside the trivial class on almost every dial.
- For nonzero κ times total kick, the link form is the face form with the gluing forgotten.
- Palindromes lie in time-reversal-fixed laws; they fill those laws in the listed higher-order computations only.

## Open

- **Over Q and R.** Over Q the unglued laws are J(Q)/H, a quotient of a Mordell-Weil group, and over R a quotient of
  the real torus J(R). Is Forest-Ruth's point on E of infinite order over Q(∛2)? Then the dials where it is trivial
  (C₁₇, κλ = 10) would be the primes where a fixed global point reduces into ⟨[Q⁺ − Q⁻]⟩.
- **Suzuki.** Degree 5 gives genus 8. Its point counts are within reach; the enumeration here is not.
- **Which laws are physical.** The two-step laws with split kicks reach a few classes. Which kicks and moves reach the
  rest, and do their runs differ beyond the hidden channel?
- **2D.** Finding 057's question about the conical singularity of the 2D face form still stands.

## References

- C. G. Latimer, C. C. MacDuffee, Ann. of Math. 34 (1933) 313-316.
- H. Bass, Math. Z. 82 (1963) 8-28; J. Milnor, Introduction to Algebraic K-Theory, Princeton 1971.
- M. Rosenlicht, Ann. of Math. 59 (1954) 505-530; J.-P. Serre, Algebraic Groups and Class Fields, Springer 1988.
- D. G. Cantor, Math. Comp. 48 (1987) 95-101.
- E. Kani, M. Rosen, Math. Ann. 284 (1989) 307-327.
- E. Artin, Math. Z. 19 (1924) 153-246; M. Rosen, Number Theory in Function Fields, Springer GTM 210, 2002.
- E. Forest, R. D. Ruth, Physica D 43 (1990) 105-117; H. Yoshida, Phys. Lett. A 150 (1990) 262-268;
  M. Suzuki, Phys. Lett. A 146 (1990) 319-323.
