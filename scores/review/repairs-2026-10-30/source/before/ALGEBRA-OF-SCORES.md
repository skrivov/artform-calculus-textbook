# The algebra of scores: one presentation (2026-10-29)

Proposal P3 of `BRAINSTORM-ARTFORM-CALCULUS-2026-10-29.md`. The author: "Start P3: write the algebra of scores as one
presentation (generators, relations, semantics, theorems), then plan it for Lean."

**What this is.** It puts the schemes programme's results (findings 037-045, 057, 064, 079, 080) into the form of a
calculus:
- a syntax (scores);
- a semantics (the realizer);
- rules (relations) that are sound;
- theorems about what the scores can express, which identities the rules prove, when two laws are the same, and what a
  run reveals.

Two results are new here, in `code/scheme_presentation.py` (two checks, all pass, under a second):
- the rules are sound, over F_p and over the Laurent ring;
- on one mode over a prime dial the rules are complete (Theorem T4).

The Lean plan is `LEAN-PLAN-ALGEBRA-OF-SCORES.md`.

**Marks.**
- *Proved here* cites a ledger finding or check.
- *Known* cites the literature.
- *To check* marks a statement to verify before it is cited.
- *Open* marks a question.

**The book's words** are those of the brainstorm: artform frame (`def:frame-instance`), control tapestry
(`def:control-tapestry`), realizer (`def:realizer`) and law in steps (`def:law-steps`).

---

## 1. Syntax: artforms, steps, scores

**Definition 1 (a lattice artform).** A = (Λ, c, R).
- **The parts.**
  - **Cells.** Λ = Z^d is the lattice of cells; a window on a dial is a torus Z^d/NZ^d.
  - **Channels.** c is the number of channels in each cell.
  - **The dial.** R is a commutative ring: F_p, Z/n, Z, Q or R.
- **States.** A state gives each cell c values in R.
- **The stencil ring.** The shifts x_1, …, x_d act on states. A translation-invariant linear map is a c × c matrix over
  the stencil ring S = R[x_1^±1, …, x_d^±1]. A stencil is an element of S, a finite combination of shifts with weights
  in R.

**Definition 2 (steps).** An elementary step e_ij(f) adds f times channel j to channel i, for i ≠ j and a stencil f.
- With two channels (b, e) there are two kinds of step:
  - the kick K(f) = e_21(f), e += f b;
  - the move M(f) = e_12(f), b += f e.
- The book's face form uses K(κ) and M(−λg), with g = 2 − x − 1/x on a line and g = 4 − S in the plane.
- Its link form uses K(κD*) and M(−λD).
- Steps are local, translation-invariant and invertible: e_ij(f)⁻¹ = e_ij(−f).

**Definition 3 (place, by blocking).** A step that acts only on some cells uses a place, such as red faces or the x
links.
- Fix a sublattice Λ′ ⊂ Λ of index m, such that the place is a union of cosets of Λ′.
- The blocked artform B(A) = (Λ′, mc, R) reads a state of A as a state with mc channels per cell of Λ′. On B(A) the
  placed step is translation-invariant.
- Red-black on Z² blocks by the checkerboard sublattice, of index 2, so 2c channels. The dimension split needs no
  blocking: its place (x or y) is in the stencil.

**Definition 4 (score).** A score is a word in the free group F(Σ) on the steps Σ of A. It is read in time order, the
first letter first. It is the row of the book's control tapestry that says which step is open (`def:law-steps`).
- One period of a repeating score is a tick.
- A forward-only score is a word in the free monoid.
- The score's other rows are:
  - **weight:** the coefficients of each step's stencil;
  - **place:** blocking;
  - **call:** Definition 5.

**Definition 5 (call, caller).** A caller chooses each tick's score from a finite set W, by a rule read from fresh,
equally prepared response cells (`prob:controller`).
- Its weights are counts of patterns.
- It is a stochastic realizer (`def:realizer`): a probability measure μ on W, applied tick by tick.

## 2. Semantics: the realizer

**Definition 6 (the realizer).** ⟦·⟧ : F(Σ) → GL_c(S).
- On steps, ⟦e_ij(f)⟧ = 1 + f E_ij.
- On words, ⟦w₁w₂⟧ = ⟦w₂⟧⟦w₁⟧: the later step acts after the earlier one.
- Its image is the elementary group E_c(S), which lies in SL_c(S). These are the laws in steps.

**Readings of a law T = ⟦w⟧** (c = 2; findings 044, 045, 057):
- the phase t = tr T, the dispersion relation λ + 1/λ = t;
- the reading a = T₁₁, and the cut a − d;
- the fibres T(x₀) at the crossings t(x₀) = ±2;
- the class of the ideal (c, λ − a) (Definition 7).

On a dial window of N cells the laws act through S/(x^N − 1).

**Examples.**
- The book's tick is ⟦K(κ) M(−λg)⟧ = M(−λg)K(κ).
- Strang is ⟦K(κ/2) M(−λg) K(κ/2)⟧. Forest-Ruth is the seven-letter word of finding 064.
- The dimension split is ⟦K(¼) M(−λg_x) K(½) M(−λg_y) K(¼)⟧, on a plane with κ = 1.
- Red-black is a word on B(A).

**Definition 7 (processing).** Laws T and T′ are the same up to processing when T′ = P T P⁻¹ for some P ∈ GL_c(S),
a local change of variables with a local inverse. Scores are processing-equivalent when their laws are.

## 3. The rules

The relations on scores. Each holds in the semantics, so it is sound.

- **(R1) Merging.** e_ij(f) e_ij(g) = e_ij(f + g), and e_ij(0) = 1.
- **(R2) Commutation** (c ≥ 3, Steinberg's relations):
  - [e_ij(f), e_kl(g)] = 1 for j ≠ k and i ≠ l;
  - [e_ij(f), e_jk(g)] = e_ik(fg) for distinct i, j, k.
- **(R3) Whitehead** (c = 2). For a unit u of S (u = r x^k with r ∈ R*), let w(u) = M(u) K(−u⁻¹) M(u), the matrix
  [[0, u], [−u⁻¹, 0]]. Then w(u) M(f) w(u)⁻¹ = K(−u⁻² f), and w(u) K(f) w(u)⁻¹ = M(−u² f).
- **(R4) Balanced movers.** Let h(u) = w(u) w(1)⁻¹ = diag(u, u⁻¹). Then h(u) h(v) = h(uv).
  - h(x) is the balanced pair of movers of finding 045, six shears.
- **(R5) Time reversal.** The anti-automorphism ρ reverses a word and inverts its letters: ⟦ρ(w)⟧ = ⟦w⟧⁻¹. A tick with
  a = d satisfies P₀ T P₀ = T⁻¹, with P₀ = diag(1, −1) (Theorem S3.6).
- **(R6) Blocking** commutes with the realizer: ⟦B(w)⟧ = B(⟦w⟧).
  - *In Lean* (commits `a96c177` and `206ea95`), `blocking`, `redBlack`, `cosets` and `checkerboardRedBlack` in the
    library `ArtformScores`, awaiting the judge. `blocking` holds on any free blocking, and the shifts by coset
    representatives make every sublattice blocking free. Red-black is a law of the blocked artform, and the blocking
    of a law of A only if κ²β = 0. On the checkerboard of Z², the face form's black part is −(1 + 1/u + 1/v + 1/(uv)),
    so red-black with M(−λg/2) is the blocking of no law of the plane when κ²λ ≠ 0.

- *In Lean* (commit `1e29e9e`), `steinbergRules`: R1 and R2 on c channels, awaiting the judge. The commutator in (R2)
  holds for the laws as matrices. Scores read in time order, so that law is the score e_jk(−g), e_ij(−f), e_jk(g),
  e_ij(f), and the word e_ij(f), e_jk(g), e_ij(−f), e_jk(−g) has the law e_ik(−fg).

*Proved here* (`code/scheme_presentation.py`, check 1):
- (R1), (R3) and (R4) hold in SL(2, F_p) for p = 5 … 13;
- over F₇[x, 1/x] they hold for the stencils 1 − x + 3/x and 2 + x² and the units 3x and 2x².
(R2) and (R5) are matrix identities. Merging and commuting steps on disjoint places are what make a batch order-free
(`def:law-steps`).

---

## 4. Theorems

### 4.1 Expressiveness: which laws are scores

**T1 (one dimension, every dial).** For d = 1, c = 2, and R = F_p, Z/p^k or Z/n: E₂(S) = SL₂(S).
- *Proved here* (Theorem S3.3, finding 045).
- *In Lean* for every field, Z/p^k and Z/n (n ≥ 1): `everyLawIsAScore`, `everyLawIsAScorePrimePower` and
  `everyLawIsAScoreModulus` in the library `ArtformScores` (commits `eb89954`, `35b23fb`), awaiting the judge.
- **The normal form.** Euclid's algorithm with the width writes every law of determinant 1 as a score. Lifting from
  F_p to Z/p^k uses R = K(m) diag(u, 1/u) M(v), and the Chinese remainder theorem covers Z/n.
- **The fewest steps.** One for a shear. Two exactly when d = 1 or a = 1. Otherwise three or more (Strang needs
  three). *In Lean* (commit `1e29e9e`), `fewestSteps`, over every commutative ring, awaiting the judge.

**T2 (the index).** GL₂(S)/E₂(S) ≅ S* = {r x^k}, through the determinant.
- *Proved here* (S3.2): every score has det 1, so the chiral mover diag(x, 1) is no score.
- The balanced pair diag(x, 1/x) is a score of six shears (Whitehead).
- *Known:* in 1D this is the GNVW index, and K₁(R[x^±1]) ≅ K₁(R) ⊕ K₀(R) (Bass, Heller and Swan).
- *In Lean* (commit `1e29e9e`), `indexGroup`, over every field, awaiting the judge. S* = {r x^k} needs a field: over
  Z/p², 1 + p x is a unit too.

**T3 (more variables).**
- *Known:* for c ≥ 3 and R a field, SL_c(S) = E_c(S) in every dimension (Suslin 1977).
- *Known:* for c = 2 it fails in 2D over Z and over Q (Bachmuth-Mochizuki 1982; Ionin-Semidetnov 2026), and in 3D over
  every field (Bachmuth-Mochizuki).
- *Open:* 2D over F_p (finding 045 §5).
- So adding channels makes more laws scores. This is stabilization; RK4's registers are an example.

### 4.2 Completeness: which identities the rules prove

**T4 (one mode on a prime dial).** Let S = F_p (constant stencils, one mode). The group presented by merging (R1)
and Whitehead's rule (R3), on X = M(1) and Y = K(1), is SL₂(F_p) for p = 5, 7, 11 and 13. So two constant scores give
the same tick exactly when the two rules turn one into the other.
- *Proved here* (`code/scheme_presentation.py`, check 2).
  - *In Lean* (commit `dddd29c`), `oneModeComplete` in the library `ArtformScores`, awaiting the judge. Its relators
    are all instances of (R1) and (R3), and a deduction certificate of the coset table of ⟨X⟩ bounds the group.
  - Coset enumeration (Todd-Coxeter, HLT) finds that the subgroup ⟨X⟩ has index p² − 1.
  - Since X^p = 1 by (R1), the presented group has order at most p(p² − 1) = |SL₂(F_p)|.
  - It maps onto SL₂(F_p), so it is SL₂(F_p).
  - As a test, the same enumerator finds the binary icosahedral group's order, 120. The balanced movers' rule (R4)
    is not needed on these dials.
- *Known* for every prime p ≥ 5, with (R4) added: Steinberg's presentation of the rank-one group, whose kernel, the
  Schur multiplier of SL₂(F_q), is trivial for q ≠ 4, 9. *To check:* the rank-one statement in Steinberg's Lectures,
  §6-§7.

**T5 (windows, enough channels).** Let S = F_p[x^±1] and c be large.
- The identities between scores that (R1) and (R2) do not prove form K₂(S).
- *Known:* by Quillen's fundamental theorem for regular rings, K₂(S) ≅ K₂(F_p) ⊕ K₁(F_p). K₂ of a finite field is 0,
  so K₂(S) ≅ F_p*.
- It is generated by the symbols {x, u} = h(xu) h(x)⁻¹ h(u)⁻¹, for u ∈ F_p*.
- So the hidden identities are exactly the balanced movers' rule h(xu) = h(x) h(u), and adding (R4) makes the
  calculus complete. *To check:* the stable range for c (injective stability for K₂, van der Kallen).
- In words: "the balanced mover times a constant squeeze is the squeezed mover" is true for the laws, but merging and
  commutation alone cannot prove it unless u = 1.

**T6 (windows, two channels).** With (R1), (R3) and (R4), the calculus for d = 1 and c = 2 is complete exactly when
F_p[x^±1] is "universal for GE₂" in Cohn's sense (Cohn 1966).
- *Known:* Cohn proved universality for discretely normed rings such as F[x] and Z.
- *Open:* the Laurent ring.

### 4.3 Equivalence: when two laws are the same

**T7 (Latimer-MacDuffee; finding 057 §1).** The laws of phase t, up to processing, correspond one to one with the
classes of fractional ideals of A_t = S[λ]/(λ² − tλ + 1). The law T goes to the class of (c, λ − a).
- *In Lean* (commits `db318d0` and `8f7660c`), `classInvariance`, `classesOneToOne`, `classesOnto` and
  `trivialClass` in the library `ArtformScores`, awaiting the judge: the correspondence in full, one to one over every
  integral domain and onto over every principal ideal domain, F[x, 1/x] among them; the trivial class is the class
  of the laws with a cyclic vector.

**T8 (the leapfrog phase; S3.4).** The curve is rational with a node at the zero mode. There are U/⟨−1, ρ⟩ glued
classes, with ρ = (1 − h)/(1 + h) and |U| = p ∓ 1, plus one unglued class. At the magic step there are
(p − 1)/2 + 3 (S3.5).
- *In Lean* (the eight `T8:` entries of `scores/manifest.toml`, awaiting the judge), over every field of characteristic
  not 2: the curve and its parametrization; the map to U/⟨−1, ρ⟩ and one more class, one to one on laws up to processing;
  the unglued class as T(1) = I, the trivial class as a cyclic vector, time reversal as the inverse; the counts p ∓ 1 and
  |⟨−1, ρ⟩| ≥ 4; the split node; the schemes; and S3.5 by the normal form [[x, 0], [w, 1/x]]. The nine rows of finding
  057's table and its four at the magic step are computed from the theorems.

**T9 (phases of degree m; S3.7-S3.8).** The curve has genus 2m − 2, and its Jacobian is J_E × J_E′ up to isogeny. There
are #J·|U|/(|H||V|) glued laws and #J/|H| unglued.

**T10 (symmetric scores; S3.9).** Scores whose stencils are polynomials in g are the classes of the frequency curve E,
#J_E/m of them.

**T11 (face and link; S3.10).** The link form of a score is its face form with the gluing at the zero mode forgotten.
- *In Lean* (commit `1e29e9e`), `faceAndLink`, awaiting the judge: T_link Λ = Λ T_face, the zero mode, and the link ideal
  between D* times the face ideal and the face ideal. The image under Pic A → Pic Ã is not in Lean.

### 4.4 Observation: what a run reveals

**T12 (the reading; S1.2, S3.6).**
- From rest the output depends only on (t, a): b_n = [cos nθ + ((a − d)/2) sin nθ/sin θ] b₀. The pair (t, a) is the
  complete invariant of the output, and the cut is the reading.
- Palindromes (a = d) lie in classes that time reversal fixes (findings 057 and 064).
- *Correction (2026-10-30).* This line used to add that palindromes meet each such class. That held on the dials checked,
  and it is false in general. By the labels of `code/scheme_classes.py`, with every factorization of bc = (t² − 4)/4
  tried, a fixed class holds no palindrome at (p, κλ) = (11, 8), (13, 10), (19, 13), (19, 15), (23, 20), (29, 6), (29, 7),
  (29, 24), (37, 4), (37, 11), (37, 26), (37, 34), (41, 10), (41, 21).
- *In Lean* (commit `1e29e9e`), `palindromeCriterion`, awaiting the judge: over a principal ideal domain with 2
  invertible, T is processing-equivalent to a palindrome exactly when some P has P T P⁻¹ = T⁻¹ with −det P a square.
- *In Lean*, `leapfrogPalindromes` and `palindromeGap`, awaiting the judge. New, and exact for the leapfrog phase: a law
  is processed from a palindrome exactly when it lies in the unglued class, the trivial class or, when 1 − κλ = w², the
  class of κ = (1 − r)/w, with κ² = ρ. A separate count reproduces the fourteen exceptions above, and no others, up to
  p = 41. At each of the fourteen a law is processed into its inverse, and no palindrome is processed into it. That they
  are the only exceptions up to p = 41 is not in Lean.

### 4.5 Step groups and their geometry

**T13 (Theorems Q, U, Y; findings 037-038).**
- The one-mode tick has order 6, 4 and 3 at the crystallographic pulls μ = 1, 2 and 3.
- On C_n the step group acts as the rotation group of the regular map {3, n}: the tetrahedron, octahedron and
  icosahedron for n = 3, 4, 5.
- The book's two squares are the projective line over F₅.
- *In Lean* (commit `fb06427`), `tickGrowth`, `stepGroups`, `stepGroupsFree`, `regularMap`, `platonicSolids`,
  `stepsAreTurns`, `tickCells` and `twoSquaresProjective`, awaiting the judge: Theorems Q, U and Y. The solids are stated
  by their counts and type.
- *In Lean*, `stepPresentations` and `pslAlternating`, awaiting the judge. Theorem Q's table as presentations: at
  μ = 1, 2, 3 a word in K and M has the identity law exactly when the table's relations imply it. Also Γ¹(3) ≅ Z ∗ Z₃,
  Γ¹(4) free, and PSL(2, 5) ≅ A₅. The proof is a ping-pong on the lines of ℤ², in place of the finding's Hopfian argument.

### 4.6 Random scores

**T14 (S8; findings 079-080).** A caller is a measure μ on scores.
- **The averaged law** is ∫⟦w⟧ dμ.
- **On a dial** the law of the state is a random walk on E. Its rate is the Cayley graph's gap, and the infinite
  group's edge is (1 + 2√2)/4.
- **Cancellation.** A caller cancels the dimension split's cut exactly when its weights are equal. The book's caller,
  which turns on 11, has weight 1/4.
- **One cue.** One cue for all cells keeps every realized law in E, translation-invariant. Coins per cell leave E:
  multiplication by a random indicator is no stencil.
- *In Lean* (commit `1e29e9e`), `callerRules` and `oneCue`, with `callerCut`, awaiting the judge. Spectral gaps stay out.

### 4.7 The same shape on other artforms

**T15 (the bells).**
- The artform: N positions, values a permutation.
- The steps: the changes, products of disjoint adjacent transpositions s_i. The rules: Coxeter's s_i² = 1,
  (s_i s_{i+1})³ = 1, and (s_i s_j)² = 1 for |i − j| ≥ 2. The semantics: S_N.
- *Known:* expressive and complete (Moore 1897).
- *Proved here* (findings 042-043):
  - plain hunt is light in a mirror box;
  - every method is light in the boxes its score cuts;
  - extents obey parity, lifting and the Fibonacci rule.
- From finding 082 (the physics thread): painted ringing in 2D is a linear permutation law, so by Theorem K
  (finding 016) it can only transport.
- *In Lean* (commits `72ba80d`, `674384d`, `0c20ed6` and `5d3fbef`), `methodsAreLight`, `plainHuntIsLight`,
  `mirrorModes`, `bellsPresentation`, `rankinParity`, `extentLifting`, `fibonacciRule`, `oneBackStep`,
  `catMapNeverRings`, `backStepBalance`, `twoSquaresBackTurns`, `fewestBackSteps`, `forwardExtentTable` and
  `permutationLawsTransport` in the library `ArtformScores`, awaiting the judge: Theorems S5.1 and S5.2 for every N, the
  modes, Moore's presentation for every N, and all of finding 043 (the Fibonacci rule for every odd prime, the cat map
  for every n ≥ 3, the table with its counts 2, 16 and 768, and the fewest back-steps). A new lemma, the balance,
  generalizes Lemma 3. Finding 082's reading is proved directly for permutation laws in any dimension, without
  Theorem K.

**T16 (the duet).** A finite artform with steps (phrases), a score (the cue row) and a stochastic realizer (the
caller). One cue read by both dancers keeps the phrase legal. That is the book's lesson in `06-controller.tex`, which
S8.6 carries to lattices.
- *In Lean* (commit `1e29e9e`), `duet`, awaiting the judge: the book's counts, and independent choices that always agree
  are fixed.

---

## 5. The shape of the calculus

| artform | generators | rules | semantics | expressive | complete |
|---|---|---|---|---|---|
| one mode on F_p | X = M(1), Y = K(1) | R1, R3 | SL₂(F_p) | yes (Euclid) | yes, p = 5 … 13 by enumeration; all p ≥ 5 with R4 (Steinberg) |
| 1D window, c = 2 | K(f), M(f) | R1, R3, R4 | E₂(F_p[x^±1]) = SL₂ | yes, on every dial (T1); not the index (T2) | open (T6, Cohn) |
| 1D window, c large | e_ij(f) | R1, R2, R4 | E_c = SL_c | yes | yes with R4; without it K₂ ≅ F_p* is hidden (T5) |
| 2D window, c = 2 | K(f), M(f) | R1, R3, R4 | E₂ ⊂ SL₂ | open on F_p; no over Z, Q | open |
| 2D or 3D, c ≥ 3 | e_ij(f) | R1, R2 | E_c = SL_c (Suslin) | yes | K₂ of the Laurent ring in d variables |
| bells | s_i | Coxeter | S_N | yes | yes (Moore) |
| a caller | measures on W | convex combination | random walks on E | — | — |

Every row has the same four parts. That is the claim of the brainstorm, made precise:
- **Generators:** the local steps of the artform.
- **Rules:** sound local relations.
- **Semantics:** the realizer into the state artform's automorphisms.
- **Two measured gaps:** what no score reaches (the cokernel: index, K₁, Haah's obstruction) and which identities
  the rules miss (the kernel: K₂).

## 6. Open problems

- **O1 (proposal P1).** Is E₂ = SL₂ over F_p[x^±1, y^±1]? That is the two-channel face form in 2D on a dial.
- **O2.** Is F_p[x^±1] universal for GE₂ (T6)? If it is, the 1D two-channel calculus with R1, R3 and R4 is complete.
- **O3.** Write the symbols {x, u} of T5 as explicit identities between Whitehead words, and test their failure for
  merging and commutation alone.
- **O4.** A presentation for nonlinear laws in steps: the rounded steps on dials, and the demon law. *Known* for
  reversible cellular automata in 1D: block permutations (Kari 1996).
- **O5.** The quantum artform: the QCA index, and Clifford circuits against Haah's 3D obstruction.

## References

- P. M. Cohn, Publ. Math. IHÉS 30 (1966) 5-53 (GE₂-rings; universality).
- R. Steinberg, Lectures on Chevalley Groups, Yale 1967 (the presentation; the Schur multiplier). *To check* §6-§7.
- J. Milnor, Introduction to Algebraic K-Theory, Princeton 1971 (Steinberg groups, symbols, K₂).
- D. Quillen, Higher algebraic K-theory I, LNM 341 (1973) (the fundamental theorem); Ann. of Math. 96 (1972) 552-586
  (the K-theory of finite fields).
- H. Bass, A. Heller, R. G. Swan, Publ. Math. IHÉS 22 (1964) 61-79; A. A. Suslin, Math. USSR Izv. 11 (1977) 221-238;
  W. van der Kallen, Injective stability for K₂, LNM 551 (1976) (*to check*).
- S. Bachmuth, H. Y. Mochizuki, J. Algebra (1982); Y. Ionin, I. Semidetnov, arXiv:2609.04275 (2026).
- C. G. Latimer, C. C. MacDuffee, Ann. of Math. 34 (1933) 313-316.
- E. H. Moore, Proc. London Math. Soc. 28 (1897) 357-366 (the presentation of S_N).
- J. Kari, Math. Systems Theory 29 (1996) 47-61.
- D. F. Holt, B. Eick, E. A. O'Brien, Handbook of Computational Group Theory, Chapman & Hall 2005 (coset enumeration).
