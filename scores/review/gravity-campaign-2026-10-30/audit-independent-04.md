# Independent memory and stencil review, 30 October 2026

Reviewed freeze: `4fc465dc188cf764eb8be326e231c84b6539f59b`.
Reviewer: the distinct `gravity_fidelity_review_01` agent, which authored none
of MemoryDefs, MemoryStatements, Memory, StencilDefs, StencilStatements or
Stencil. The pre-freeze review was read-only. No proof, definition or original
approval was changed; all 73 earlier approvals stand.

**Verdict: approve both entries; return none.** Both are faithful algebraic
foundations. Neither supplies an additional native gravity application.
The literal ledger quotations, findings 110–111, six new modules and their
positive examples were read independently of compilation.

See [verdict-independent-04.json](verdict-independent-04.json) for the input
hashes and per-key verdicts, and
[validation-independent-04.json](validation-independent-04.json) for the
independent reproduction results and report-output hashes.

## GAC:block-memory — approve

The first conjunct quantifies over arbitrary semirings, modules with additive
commutative monoids, all four linear blocks and both full sequences. It assumes
both displayed recurrences. The eliminated auxiliary sequence is exactly

    z_n=D^n z_0+sum_(j<n) D^(n-1-j) C x_j.

Substitution through B yields the exact visible recurrence, including the
separate term `B D^n z_0` and every earlier visible state. The exponent is
natural subtraction only inside `j<n`, and n=0 gives the original first step
with an empty history sum. No initial register, endpoint term, inverse,
finite-dimensional premise or convergence assumption is inserted or removed.

The second conjunct assumes the actual graph condition
`C y+D(J y)=J(A y+B(J y))` for every y. It gives the full pair-valued orbit
from `(y,J y)`, with visible map `U y=A y+B(J y)`. This is an invariant
preparation. It does not reset the auxiliary state after each step.

The third conjunct concerns the unrestricted full initial-state domain:
`A x+B z=U x` must hold for every x,z. U is an arbitrary function, so the
proof does not impose linearity on a proposed visible closure. Evaluating at
zero identifies U(0) and then every Bz; the condition is exactly B=0.
The converse uses U=A. This criterion is distinct from autonomy on a prepared
graph with nonzero B.

The final conjunct uses the fixed initial preparation z_0=0 only once.
`quarterVisible n x` reads the full quarter-turn iterate, rather than an
iterated read/reset operation. Its readings are `x,0,-x,0,x,...`.
The two initial data x=0 and x=1 have the same reading 0 at time 1 and
different next readings 0 and -1. Hence no one autonomous map works for all
initial visible data and times, even with the same initial preparation.

The positive examples identify this block with the actual existing rational
Whitehead score at unit 1, with matrix `[[0,1],[-1,0]]`. They also exhibit the
nontrivial invariant graph for `(A,B,C,D)=(2,1,1,1)` and
`J=(sqrt(5)-1)/2>0`, where `J²+J=1`. The graph condition and all finite
iterates are checked; B is nonzero. These are concrete original-score and
prepared-graph data, rather than an empty or zero-only model.

Finding 110 correctly retains the missing native dynamic-block bridge. A
stationary first-lift correction is not made into a native memory recurrence
by assigning it a block name. The theorem supplies no native gravity kernel,
boundary condition, admitted-domain or physical-equivalence claim.

## GAC:stencil-support — approve

The kernel is the actual finite-support additive monoid algebra. The action
is `sum_a p_a*v(x+a)` for all K-valued fields on the declared monoid. The
composition identity keeps the order of both coefficient multiplication and
displacements. Its proof uses associativity and distributivity, not
commutativity of K or G. For two single terms both sides give
`c*d*v((x+a)+b)` with `x+(a+b)` identified by associativity.

The all-field injectivity claim is genuinely global: a unit impulse at a,
read at the monoid origin, recovers exactly the coefficient p_a. It does not
claim injectivity from constant fields or from a prescribed Fourier band.
No additive inverse or group cancellation is silently required of G.

The support statement is precisely inclusion in the ordered sum of support
sets. On `Fin d -> Z`, the coordinate absolute-value inequality gives radius
at most r+s for every finite d. It is an upper bound, and cancellation may
make it strict. The explicit rational `(1-T)(1+T)=1-T²` witness has displacement
1 in the sum of supports and absent from the product support.

For each size N=n+1, the averaging matrix is exactly the rational matrix
with every entry 1/N. Positivity of the integer N makes every entry nonzero,
and finite summation shows that every constant field is fixed. The two-cell
example has off-diagonal entry 1/2 while the identity has entry zero there.
Thus restricted agreement does not determine the full kernel. It leaves the
local identity available on that same restricted subspace and makes no
physical-equivalence or impossibility claim.

The positive shift example is in dimension one, with nonzero rational
coefficient at displacement 1. Its square has displacement 2 and fails the
radius-1 bound, so the additive bound is attained in this class. The old
kick-then-move score example checks its actual realizer entry `1+q*p`, with
the established score time order. The generic semiring action and the old
commutative-ring score are used with their appropriate assumptions.

Finding 111 keeps the full native stencil/domain and approximation obligations
separate. A constant-field averaging example proves no quantitative native
inverse, convergence estimate or Fourier-band locality statement.

## Validation packaging and checks

At the parent's explicit request, the submission's validation-B03-D01.json
was compacted from 79,934,866 bytes to 5,453 bytes. The two complete generated
report strings were replaced by their UTF-8 byte counts and SHA-256 hashes.
Every original command, return code and timing remains, as do bounded other
outputs. The original validation file's byte count and SHA-256 are preserved
in its packaging metadata. This changes validation packaging only.

The independent full warnings-as-failures build, both reports, both status
checks, tree/identity check, both existing certificate checks, gravity R2
certificate check and separate Memory/Stencil kernel replays passed. Both
tagged proofs have exactly their tagged target and only allowed axioms.
Book and scores approved-surface drift checks are clear. All 73 earlier
manifest entries and the six submitted proof/definition files remain unchanged.
