# 080. Random orders on windows: what a fair caller cancels, and why every face must read the same cue

Campaign S8 of `BRAINSTORM-SCHEMES-2026-10-29.md` (2026-10-29), part 2.
- The author: "Start campaign S8: random scores."
- Code: `code/scheme_random.py`, checks 5-7 (`data/scheme-random.json`).
- Finding 079 has the one-mode gaps. Plate: 28.

**Questions** (the brief, §7, S8).
- On windows, does a random order of x- and y-steps, or of red and black, keep light on the reals (error
  cancellation)?
- What does it do to the carpets on a dial: the expected zero share, the averaged law?
- The book's link: a caller reading response cells to choose the next step.

**Setting.**
- **The schemes** are S1's (finding 044), in the face form, one mode with pulls g_x, g_y, or on a torus.
  - The dimension split K(1/4) M_x K(1/2) M_y K(1/4) and its mirror with x and y exchanged.
  - Red-black K_red M(1/2) K_black M(1/2) and its mirror. On a pair of modes k, k + (π, π) it is a 4 × 4 tick, since
    a colour's kick couples the two.
- **The caller.** Each tick it reads fresh response cells and calls one order. Its rule fixes the weights, which are
  counts of equally prepared patterns (the probability chapter, `06-controller.tex`).

## 1. Theorem S8.4: a fair caller cancels the dimension split's cut, and nothing of red-black's

**Theorem S8.4.**
1. **The split.** The two orders of the dimension split have cuts a − d = ±h²(g_x − g_y)/2 (Theorem S1.2).
   - A caller that calls xy with weight q has a mean tick (the average over callers) with cut (2q − 1)h²(g_x − g_y)/2.
   - So the mean over callers is second order exactly when q = 1/2.
   - One caller's run is of order 3/2: the ± cut errors add as a random walk, h²√n = h^(3/2)√τ.
   - A fixed order is first order.
2. **Heating.** Runs heat, with a positive Lyapunov exponent, except on the diagonal g_x = g_y, where the two orders
   are the same tick.
3. **Red-black.** Random red/black order cancels nothing at first order: its mean over fair callers stays first
   order, and its runs heat.

*Proof of 1.* The mean tick is (q T_xy + (1 − q) T_yx), whose cut is the weighted mean of the cuts, and its trace is
both orders' trace. Order 3/2 is S1.3's argument, with the cut in place of the commutator. ∎

*Checked* (check 6). One mode, g_x = 1, g_y = 1/4, τ = 2, from (b, e) = (1, 0); errors against the exact flow:

| h | 0.2 | 0.1 | 0.05 | 0.025 | order |
|---|---|---|---|---|---|
| split, fixed order xy | 2.48e-2 | 1.28e-2 | 6.48e-3 | 3.27e-3 | 0.97 |
| split, one random caller (rms of 16) | 2.45e-2 | 8.20e-3 | 3.46e-3 | 1.17e-3 | 1.57 |
| split, mean over fair callers | 4.82e-3 | 1.21e-3 | 3.04e-4 | 7.61e-5 | 2.00 |
| red-black (g = 3/2), mean over fair callers | 6.88e-2 | 2.67e-2 | 1.15e-2 | 5.31e-3 | 1.23 (local 1.37, 1.21, 1.12) |

- **The cuts.** They are ±h²(g_x − g_y)/2 to 1e-12 at every h.
- **Lyapunov exponents** at h = 0.2:
  - for the split, 7.7e-4 at (g_x, g_y) = (4, 0), 3.1e-4 at (3, 1), and 4e-6 at (2, 2), where it is zero exactly;
  - for red-black, 4.4e-4, 6.9e-4 and 8.3e-4 at g = 1/2, 2 and 4.

So the answer to the brief is split.
- A fair random order of x and y keeps light on average: its mean is second order, like Strang. Each run is order
  3/2 and heats slowly.
- A random order of red and black does not: its first-order error survives the average.

## 2. Theorem S8.5: the caller's rule decides the cancellation

The book's caller reads two named response cells, with four equally prepared patterns, and calls the turn only on 11.
Used to call xy, it gives q = 1/4.

**Theorem S8.5.** A caller reading equally prepared response cells calls xy with weight q, the share of patterns its
rule sends to xy.
- The mean over callers cancels the cut only when q = 1/2.
- The book's rule (turn on 11) leaves a cut of −h²(g_x − g_y)/4, so its mean is first order.
- The rules "turn on a = 1" and "turn on a ≠ b" have q = 1/2, so their means are second order.

*Checked* (check 7): the fitted orders of the mean are 1.09 for "turn on 11", and 2.00 for both balanced rules. The
probability that makes a scheme accurate on average is a count of the caller's patterns, as in the book's
`prob:counting`.

## 3. Theorem S8.6: every face must read the same cue

**Theorem S8.6.** Take a random red/black order on a torus.
- **One cue.** If one cue is read by every face, each tick is a stencil law: it commutes with the shifts. A plane
  wave of mode k then stays in the pair k, k + (π, π).
- **A coin per face.** If each face tosses its own coin to choose its colour for the tick, the tick is still reversible.
  It still keeps Gauss's law, because the kicks stay on faces (S1.1). But it no longer commutes with the shifts: the
  medium is random, and light scatters out of the pair.

*Proof.* A cue read by all faces makes each half-step a kick on all red or all black faces, which are stencils. A coin
per face makes the kicked set random, and multiplication by its indicator is not a stencil. ∎

*Checked* (check 7): a 32 × 32 torus, h = 0.2, from the plane wave k = (3, 1), 60 ticks.
- The share of the energy |b̂|² + |ê|² outside the pair is 1.2e-30 with one cue.
- With a coin per face it is 1.9e-2 after 60 ticks, and growing.

This is the book's lesson about the two dancers, carried to schemes. Two dancers with their own coins disagree, and
the phrase stalls. Faces with their own coins disagree, and the law stops being one law. As the book puts it, "two
choices can agree every time only through a cause they share" (`06-controller.tex`).

## 4. On a dial: the carpets and the averaged law

- **The averaged law.** On a dial the average over callers is a walk on the states. Its stationary law is uniform on
  the orbit of the start under the steps. Every step keeps the total flux Σb (M changes b by g e, whose sum is zero,
  and K leaves b alone), so the orbit lies in a hyperplane Σb = const.
- **The zero share.** If each face's b were uniform on F_p, the expected zero share would be 1/p. For one mode it is
  exactly 1/(p + 1) (finding 079).
- *Checked* (check 5): a ring of 24 faces on C₁₃ (κ = λ = 1) from a bump on a uniform flux.
  - The leapfrog's zero share swings between 0 and 3/8 over 120 ticks: its carpet keeps its structure.
  - The mean over 300 random-score callers settles at 0.0767 over steps 100-240, against 1/13 = 0.0769, as if each
    face's b were uniform.
- So a random caller whitens the carpet. Over the reals the same caller heats (S1.3); on a dial it mixes, at the
  Cayley graph's rate.

## What is known, and what looks new

*Known:*
- Randomized product formulas: the average is second order (Childs, Ostrander and Su 2019). Random-scan and
  systematic-scan Gibbs samplers make the same contrast.
- S1's Theorem S1.3 for the random order of K and M.

*New, as far as we found:*
- The cut cancellation of the dimension split, and its failure for red-black.
- The rule of the caller as the condition for cancellation: q = 1/2, which the book's "turn on 11" violates.
- The shared cue as what keeps a random score one translation-invariant law.
- The dial's carpet whitening to 1/p.

## Open

- **Red-black's leading error.** Is it colour-symmetric for every score that alternates colours, so that no random
  order cancels it?
- **The scattering rate.** For coins per face, how fast does light leave its mode, as a function of h and k? Is it a
  diffusion in k?
- **The dial's rate on a ring.** How does the slowest mode's Cayley gap set the whitening time of a whole carpet?

## References

- A. M. Childs, A. Ostrander, Y. Su, Quantum 3 (2019) 182; E. Campbell, Phys. Rev. Lett. 123 (2019) 070503.
- H. Furstenberg, Trans. Amer. Math. Soc. 108 (1963) 377-428.
