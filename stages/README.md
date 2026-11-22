# The stage algebra in Lean

The library `ArtformStages` proves the core of the author's research ledger on a layered
universe. It is not book text. Its source is the ledger's `THEORY.md` and its charter
(definitions D1 and D2), in the author's workspace under
`physics/ledgers/multilayered-universe/`; the statements below are quoted in the
ledger's words, with THEORY.md's labels.

**State.** Every statement listed is proved. The library has no `sorry` and no new axiom,
and builds with `lake build ArtformStages --wfail`. No judge has reviewed the Lean forms
against the ledger's text: the statements are proved, not approved.

## The words

| the ledger's word | in Lean | what it is |
|---|---|---|
| an act, a walk | `α`, `FreeGroup α` | acts made one after another, each of which can be undone |
| a stage | `Stage α` | its rules: the walks laid as rest. A rule "u and v are the same" is the walk `u * v⁻¹` |
| rest | `Stage.rest` | the walks that the rules make rest |
| a law, the world | `Stage.law`, `Stage.World` | a walk up to the rules |
| over; forgetting | `Stage.IsOver`, `Stage.forget` | everything at rest in `C` is at rest in `S` |
| the kept laws | `Stage.keptLaws` | what the walks at rest in `S` do in `C` |
| a carry | `Stage.IsCarry` | over `S`, and any two kept laws pass each other |
| lay, add | `Stage.lay`, `Stage.add` | more rules; one more act with no rule |
| keep | `Stage.keep`, `Stage.keepCommon`, `Stage.keepTrail` | the richest carry; kept in common; `keep(S; M)` |
| a line, a chain | `α × S.World`, `Stage.Chain` | a whole number on every line of the map |
| the trail | `Stage.trail` | what a walk leaves on the lines, forward less back |
| a filling of one mark | `R[G]`, Mathlib's `MonoidAlgebra R G` | a number of the dial `R` at finitely many laws of the space `G`; a shift is `single g r` |
| a state of light | `LightState R n` | `A` on the lines and `E` on the dual lines, numbers of a commutative ring `R` |
| the kick, the drift, Pair | `kick`, `drift`, `pair`, `unpair` | `E` gains `S A`; then `A` loses `L E`; Pair is the drift after the kick |
| periodization | Mathlib's `MonoidAlgebra.mapDomainRingHom` | along a map of spaces, the sum of a filling's values over each fiber |
| turning over | `turnOver`, `turned` | each law to its inverse; on a table, its transpose read with every stencil turned over |
| the reading | `realize`, `realizeVec`, `realizeState` | on a finite space, a table of stencils read as a table of numbers: at `(i, h), (j, h')` the number of `C i j` at `h h'⁻¹` |
| a relabeling of cells | `relabel` | a table `P` with `Pᵀ P = 1`, a bijection of cells with a sign on each among them, applied to both parts of a state |
| the Pair of one place | `pairOne`, `qOne`, `OrbitsBounded` | `e' = e + σ a`, `a' = a - ℓ e'`; its energy `σ a² + ℓ e² + σ ℓ a e`; every orbit keeps `a² + e²` below a bound |
| a scaling | `scale` | the lines by `D'` and the dual lines by `D`, with `D D' = D' D = 1`: for a drift by sorts, `D` is its square root |

## The statements

| label | in the ledger's words | Lean | file |
|---|---|---|---|
| T1(a) | forgetting reaches every law | `Stage.forget_surjective` | `Basic.lean` |
| T1(b) | the laws that forgetting sends to rest are the kept laws | `Stage.ker_forget` | `Basic.lean` |
| T1(c) | a stage over `S` has as many laws as `S`, times the kept laws | `Stage.card_world` | `Basic.lean` |
| rule 1 | obeying twice is obeying once, in either order | `Stage.lay_lay`, `Stage.rest_lay_comm` | `Basic.lean` |
| rule 2, T1(d) | keeping, and then obeying what was kept, changes nothing | `Stage.rest_lay_rules`, `Stage.rest_lay_keep` | `Basic.lean`, `Carry.lean` |
| rule 6 | adding an act and obeying a rule that does not use it, in either order | `Stage.add_lay` | `Basic.lean` |
| add keeps old equalities | two laws of `S` that are one law after an act is added are one law | `Stage.addHom_injective` | `Basic.lean` |
| lay is first | a choice of laws under which the rules are rest extends in one way | `Stage.lay_first` | `Basic.lean` |
| Theorem A, with commutators | `C` is a carry over `S` exactly when its rest lies between the commutators of the rest of `S` and the rest of `S` | `Stage.isCarry_iff` | `Carry.lean` |
| Theorem B, with commutators | every normal subgroup between them is the rest of a carry | `Stage.isCarry_ofRest` | `Carry.lean` |
| the richest carry | keep is a carry, and is over every carry | `Stage.keep_isCarry`, `Stage.keep_isOver_of_isCarry` | `Carry.lean` |
| kept in common | a carry in which the kept laws pass every law | `Stage.keepCommon_isCarry`, `Stage.keepCommon_central` | `Carry.lean` |
| rule 3 | `S` is a carry over what is laid on it exactly when the walks that the laying puts at rest pass each other in `S` | `Stage.isCarry_lay_iff` | `Carry.lean` |
| rule 4 | obeying one rule and keeping another, in either order | `Stage.rest_keepExcept_union` | `Carry.lean` |
| keep is first | a choice of laws under which the closed walks of `S` pass each other extends in one way; the same for kept in common | `Stage.keep_first`, `Stage.keepCommon_first` | `Carry.lean` |
| Lemma 1.2 | the trail adds along a walk, the second part looked at from where the first ends | `Stage.trail_mul` | `Trail.lean` |
| Lemma 1.3 | the trail of a walk undone | `Stage.trail_inv` | `Trail.lean` |
| Lemma 1.6 | after a closed walk the trail simply adds | `Stage.trail_mul_of_mem_rest`, `Stage.trail_inv_of_mem_rest` | `Trail.lean` |
| Lemma 1.7 | a closed walk made at the end of a walk has its trail looked at from that dot | `Stage.trail_conj` | `Trail.lean` |
| Lemma 2.4 | a closed walk has the trail 0 exactly when it is made of commutators of closed walks | `Stage.trail_eq_zero_iff` | `Trail.lean` |
| T4(a) | in the richest carry two walks are one law exactly when they end at one dot and leave one trail | `Stage.keep_law_eq_iff` | `Trail.lean` |
| Theorem A, 1 and 2 | `C` is a carry over `S` exactly when it keeps of a walk nothing but its dot in `S` and its trail | `Stage.isCarry_iff_trail` | `KeepTrail.lean` |
| T2(a) | every face has one kept law, its carry | `Stage.law_conj_eq_of_law_eq` | `KeepTrail.lean` |
| T2(b) | what a closed walk does in a carry is fixed by its trail | `Stage.law_eq_of_trail_eq` | `KeepTrail.lean` |
| Theorem B | `keep(S; M)` is a carry over `S`; a walk is rest in it exactly when it is a closed walk of `S` with its trail in `M` | `Stage.keepTrail_isCarry`, `Stage.mem_rest_keepTrail` | `KeepTrail.lean` |
| Theorem B, with `M` the trail 0 | the whole trail kept is the richest carry | `Stage.rest_keepTrail_bot` | `KeepTrail.lean` |
| Theorems A and B | every carry over `S` is `keep(S; M)`, with `M` its own trails | `Stage.rest_eq_keepTrail_of_isCarry` | `KeepTrail.lean` |
| the smallest case | keeping the whole trail over a wheel gives the count | `Stage.rest_keep_wheel`, `Stage.count_isCarry_wheel` | `Examples.lean` |
| rule 5 | a carry over a carry need not be a carry | `Stage.carry_of_carry_need_not_be_carry` | `Examples.lean` |
| rule 7 | adding an act and keeping cannot be done in either order | `Stage.keep_add_ne_add_keep` | `Examples.lean` |
| one rule is one stencil (charter, D16) | a law of one mark that adds and is the same at every place is the table of one stencil | `law_eq_mul_stencil` | `OneMark.lean` |
| only the shifts | on a space with two unique products, on a dial without zero divisors, two fillings whose product is one mark at rest have one place each | `eq_single_of_mul_eq_one` | `OneMark.lean` |
| one mark has no law but the shifts | there a law of one mark that adds, is the same at every place and can be undone is a shift with one number | `law_of_one_mark_is_a_shift`, `Stage.law_of_one_mark_is_a_shift` | `OneMark.lean` |
| the lattices | rows that pass, in any number, are such a space | `lattice_twoUniqueProds`, `lattice_law_of_one_mark_is_a_shift` | `OneMark.lean` |
| PA1 (finding 422, T332(a)) | Pair is the drift after the kick, and unpair undoes it on both sides, for every `S` and `L` | `pair_eq_drift_kick`, `unpair_pair`, `pair_unpair` | `Pair.lean` |
| PA2 (T332(b)) | with `S` and `L` symmetric, Pair keeps the alternating pairing | `omega_kick`, `omega_drift`, `omega_pair` | `Pair.lean` |
| PA3 (T332(c)) | with `S` and `L` symmetric, Pair keeps the staggered invariant `A ⬝ S A + E ⬝ L E + A ⬝ S (L E)` | `qstar_pair` | `Pair.lean` |
| PA4 (T332(d)) | with `S = Cᵀ K C` and `C D = 0`, Pair passes the gauge and keeps the charge `Dᵀ E` | `pair_gauge`, `charge_pair` | `Pair.lean` |
| PA5 (T332(e)) | Pair commutes with maps of rings; periodization is one, by sums over fibers, and commutes with turning over; so it sends Pair to Pair | `pair_map`, `coeff_periodize`, `periodize_antipode`, `periodize_pair` | `Pair.lean` |
| RZ2 (finding 424, T334(a)) | on a finite space the reading takes products of stencils to products of tables and turning over to the transpose, and loses nothing | `coeff_mul_fintype`, `realize_mulVec`, `realize_mul`, `realize_turned`, `realizeVec_injective` | `Realize.lean` |
| RZ3 (T334(b)) | the reading of Pair is the Pair of the readings; with periodization, the plane's Pair read on its closed quotient is the Pair of the board whose kick is `Cᵀ K C` | `realize_pair`, `realize_periodize_pair` | `Realize.lean` |
| RS1 to RS3 (T334(c)) | Pair commutes with a relabeling of cells, which keeps the alternating pairing and the staggered energy | `pair_conj`, `omega_conj`, `qstar_conj` | `Relabel.lean` |
| WN1, WN2 (finding 425, T335(a), (b)) | completing the square: `4 Q⋆ = (2E + S A) ⬝ L (2E + S A) + 4 A ⬝ S A - S A ⬝ L (S A)`; so `Q⋆` is nowhere negative exactly when `L` is and `S A ⬝ L (S A) ≤ 4 A ⬝ S A` | `four_qstar`, `qstar_nonneg_iff` | `Window.lean` |
| WN3 (T335(c)) | on a level `S v = s v`, with the drift `ℓ` on every cell, Pair is the Pair of one place | `pair_on_level` | `Window.lean` |
| WN4 (T335(d)) | the Pair of one place keeps every orbit bounded exactly when `0 < ℓ σ < 4`, or `ℓ = σ = 0` | `bounded_iff_window` | `Window.lean` |
| WS1, WS2 (finding 427, T337(a), (b)) | Pair with the drift `D D`, scaled, is Pair with the kick `D S D` and the drift 1; with `D` symmetric the scaling keeps the alternating pairing | `pair_scale`, `omega_scale` | `Scale.lean` |
| WS3 (T337(c)) | on a level of the pair, `L S v = μ v`, Pair is the Pair of one place with `σ = 1` and `ℓ = μ` | `pair_on_pair_level` | `Scale.lean` |
| WD1 (finding 428, T338(a)) | for positive definite `A` and `D`, `D - Bᴴ A⁻¹ B` is positive semidefinite exactly when `A - B D⁻¹ Bᴴ` is: the window read on the lines is the window read on the squares | `window_dual` | `Dual.lean` |
| SD1 (finding 430, T340(a)) | the same with positive definite: the open window on the lines is the open window on the squares | `window_dual_strict` | `Strict.lean` |
| SD2 (T340(b)) | a real symmetric table each of whose rows has its sizes summing to less than twice its diagonal entry is positive definite: the local test of the window | `posDef_of_rowsum` | `Strict.lean` |
| BT1 (finding 432, T342(a)) | on a board, given by an incidence with entries `-1`, `0`, `1` and two squares at each line, `κ σ p σ < 2` at every square makes the table on the squares positive definite | `squareTable`, `roundDrift`, `board_local_sufficient` | `Board.lean` |
| BT2 (T342(b)) | a positive definite table on the squares has `κ σ p σ < 4` at every square | `board_local_necessary` | `Board.lean` |
| BI1 (finding 434, T344(a)) | a closed board turned one way, given by the four corners of each square in its turn: its incidence has `C² = |C|`, two squares at each line, and columns summing to `0` | `Board`, `Board.incidence`, `Board.incidence_sq`, `Board.incidence_col`, `Board.incidence_col_sum` | `Incidence.lean` |
| BI2 (T344(b)) | `C D = 0` for the board's gauge `D`, so Pair with the kick `Cᵀ K C` passes the gauge on every board | `Board.gauge`, `Board.incidence_mul_gauge`, `Board.pair_gauge` | `Incidence.lean` |
| BI3 (T344(c)) | the drift round a square is the sum of `λ` over its four sides, and the local tests of the window hold on every board | `Board.roundDrift_incidence`, `Board.certificate`, `Board.asked` | `Incidence.lean` |
| BI4 (T344(d)) | with every `λ > 0`, the same test makes the table on the lines, `4 / λ` less `Cᵀ diag(κ) C`, positive definite | `Board.window` | `Incidence.lean` |
| BI5 (T344(e)) | the torus of `n` by `m` squares is a board, and on it `κ λ < 1 / 2` makes the table on the squares positive definite | `torus`, `torus_certificate` | `Incidence.lean` |
| BO1 (finding 436, T346(a)) | with `S` positive semidefinite, `L = D D` for a symmetric `D` with an inverse `D'`, and `4 D' D' - S`, the window `4 L⁻¹ - S`, positive definite, every orbit of Pair from `(A, S w)` is bounded | `OrbitBounded`, `orbit_bounded_of_window` | `Bounded.lean` |
| BO2 (T346(b)) | on a board, `κ σ` times the sum of `λ` over the four sides of `σ` below `2` at every square keeps every orbit of Pair from `(A, S w)` bounded | `Board.orbit_bounded` | `Bounded.lean` |
| BO3 (T346(c)) | an orbit whose `E` lies on the level 0 of the kick drifts, `(-k y, L' y)` at step `k`, so it is not bounded | `pair_iterate_kernel`, `not_orbitBounded_of_kernel` | `Bounded.lean` |
| BG1 (finding 438, T348(a)) | along a level `L S v = μ v`, the orbit of Pair from `(a v, e S v)` is the orbit of the Pair of one place with `σ = 1` and `λ = μ`, carried by `v` and `S v` | `pair_iterate_on_pair_level` | `Converse.lean` |
| BG2 (T348(b)) | a level of `L S` below `0`, or at `4` or more, has an orbit from some `(A, S w)` that is not bounded | `exists_not_orbitBounded_of_level` | `Converse.lean` |
| BG3 (T348(c)) | with `S` positive semidefinite and `L = D D` for a symmetric `D` with an inverse `D'`, every orbit of Pair from `(A, S w)` is bounded exactly when `4 D' D' - S` is positive definite | `orbit_bounded_iff_window` | `Converse.lean` |
| BG4 (T348(d)) | on a board with `κ > 0` and `λ > 0`, every orbit of Pair from `(A, S w)` is bounded exactly when `4 / λ` less `Cᵀ diag(κ) C` is positive definite | `Board.orbit_bounded_iff` | `Converse.lean` |
| RC2 (finding 439, T349(b)) | where the image of `C` holds `e σ - e τ` for every two squares, on at least three squares, two different `K` give two different kicks `Cᵀ diag(K) C` | `kick_injective` | `Classes.lean` |
| FL1 (finding 440, T350(a)) | on a wide board, a kick `M` of reach 1 with `M G = 0` (blind to a change at a corner) and `Gᵀ M = 0` (it keeps Gauss's law) is `Cᵀ diag(K) C` | `Board.kick_forced` | `Forced.lean` |
| FL2 (T350(b)) | on every board, every `Cᵀ diag(K) C` has reach 1, `Cᵀ diag(K) C G = 0` and `Gᵀ Cᵀ diag(K) C = 0` | `Board.kick_meets` | `Forced.lean` |
| FL3 (T350(c)) | on every board, a kick of reach 0 with `M G = 0` is `0` | `Board.reach_zero` | `Forced.lean` |
| FL4 (T350(d)) | on a joined board the image of `C` holds `e σ - e τ`; so on a wide joined board of at least three squares each such kick is `Cᵀ diag(K) C` for exactly one `K` | `Board.joined_image`, `Board.kick_forced_unique` | `Forced.lean` |
| MX1 (finding 441, T351(a)) | Pair with a current `J`, `E' = E + S A - J`, `A' = A - L E'`, is Pair when `J = 0`; with `S = Cᵀ K C` the field `B = C A` loses `C L E'` (Faraday) and `E' = E + Cᵀ K B - J` (Ampère) | `pairWith_zero`, `faraday_pairWith`, `ampere_pairWith` | `Maxwell.lean` |
| MX2 (T351(b)) | with `C G = 0`, the divergence `-Gᵀ E` of `E'` is that of `E` less that of `J` | `divergence_pairWith` | `Maxwell.lean` |
| MX3 (T351(c)) | with `C G = 0`, every state with divergence `ρ` goes to one with divergence `ρ'` exactly when `ρ' = ρ - div J` | `gauss_kept_iff` | `Maxwell.lean` |
| MX4 (T351(d)) | with `C G = 0`, a change `G g` of `A` passes through Pair with a current | `pairWith_gauge` | `Maxwell.lean` |
| MX5 (T351(e)) | with `S`, `L` symmetric, `Q⋆` after the step is `Q⋆` before less `J ⬝ L (E + E')` | `qstar_pairWith` | `Maxwell.lean` |
| MX6 (T351(f)) | a state is still exactly when `Cᵀ K C A = J` and `C L E = 0`; its current has no divergence; with no current and every `κ > 0`, `C A = 0` | `pairWith_still_iff`, `still_current_divergence`, `still_field_zero` | `Maxwell.lean` |
| MX7 (T351(g)) | on every board the divergence of every `E` sums to `0` over the corners | `Board.divergence_sum` | `Maxwell.lean` |
| SO1 (finding 442, T352(a)) | on the cubic torus of side `n`, `(G g)(w, i) = g (w + e i) - g w`, `C A` at a face is `A` summed round it with the signs of its turn, `V B` at a cube is `B` summed out of it | `cubeGauge_mulVec`, `cubeIncidence_mulVec`, `cubeBoundary_mulVec` | `Solid.lean` |
| SO2 (T352(b)) | on the cubic torus `C G = 0` | `cube_incidence_mul_gauge` | `Solid.lean` |
| SO3 (T352(c)) | on the cubic torus `V C = 0`, so `V (C A) = 0`: no magnetic charge | `cube_boundary_mul_incidence`, `cube_div_curl` | `Solid.lean` |
| SO4 (T352(d)) | where `V C = 0`, Faraday's step keeps `V B` for every `B` | `faraday_keeps_magnetic_charge` | `Solid.lean` |
| SO5 (T352(e)) | on the cubic torus Gauss's law is kept exactly under continuity, and the divergence of every `E` sums to `0` | `cube_gauss_kept_iff`, `cube_divergence_sum` | `Solid.lean` |
| LW1 (finding 443, T353(a)) | every orbit of Pair obeys the wave equation in steps: `A'' - A' = (A' - A) - L S A'`, `E'' - E' = (E' - E) - S L E'` | `pair_wave`, `pair_wave_E` | `Waves.lean` |
| LW2 (T353(b)) | if `C Cᵀ ψ = μ ψ` then `Cᵀ diag(κ) C (Cᵀ ψ) = κ μ Cᵀ ψ` | `transverse_level` | `Waves.lean` |
| LW3 (T353(c)) | on every board `C A` sums `A` round a square with the sides' signs, and `Cᵀ y` at a line is `y` at its square along less `y` at its square against | `Board.incidence_mulVec`, `Board.incidence_transpose_mulVec` | `Waves.lean` |
| LW4 (T353(d)) | on the torus `C Cᵀ` is the five-point stencil | `torus_laplacian` | `Waves.lean` |
| LW5 (T353(e)) | the plane wave `χ(p w₁) χ(q w₂)` is a level of the stencil at `4 - 2 cos θ₁ - 2 cos θ₂` | `stencil_plane_wave` | `Waves.lean` |
| LW6 (T353(f)) | on the torus with one `κ`, the real part `ψ` of a plane wave gives `S (Cᵀ ψ) = κ (4 - 2 cos θ₁ - 2 cos θ₂) Cᵀ ψ` | `torus_transverse_wave` | `Waves.lean` |
| LW7 (T353(g)) | with `μ = 2 - 2 cos ω`, `cos (k ω + φ)` obeys `a (k + 2) = (2 - μ) a (k + 1) - a k` | `cos_orbit` | `Waves.lean` |
| CL1 (finding 444, T354(a)) | on every board `G φ` at a line is `φ` at its head less `φ` at its tail | `Board.gauge_mulVec` | `Coulomb.lean` |
| CL2 (T354(b)) | on a board whose corners are joined, `G φ = 0` makes `φ` constant | `Board.gauge_const` | `Coulomb.lean` |
| CL3 (T354(c)) | there, with every `λ > 0`, a charge `ρ` is `Gᵀ diag(1/λ) G φ` for some `φ` exactly when it sums to `0` | `Board.coulomb` | `Coulomb.lean` |
| CL4 (T354(d)) | there the potential is unique up to a constant | `Board.coulomb_unique` | `Coulomb.lean` |
| CL5 (T354(e)) | there a charge is the divergence of a still field, `C diag(λ) E = 0`, exactly when it sums to `0` | `Board.coulomb_field` | `Coulomb.lean` |
| IN1 (finding 445, T355(a)) | Gauss's theorem: the divergence of `E` summed over a set `U` of corners is the flux of `E` out of `U`; on a board a line's outward sign is `[tail ∈ U] - [head ∈ U]` | `gauss_theorem`, `Board.outward_eq` | `Integral.lean` |
| IN2 (T355(b)) | Stokes's theorem: `C A` summed over a set `P` of squares is the circulation of `A` round its edge; on a board the edge is `[square along ∈ P] - [square against ∈ P]`, and the whole board has none | `stokes_theorem`, `Board.edge_eq`, `Board.flux_total` | `Integral.lean` |
| IN3 (T355(c)) | Faraday's law of induction: the flux of `C A` through `P` changes in a step by minus the circulation of `L E'` round its edge | `faraday_integral` | `Integral.lean` |
| IN4 (T355(d)) | with `C G = 0`, the charge in `U` changes in a step by minus the flux of the current out of `U` | `continuity_integral` | `Integral.lean` |
| IN5 (T355(e)) | where `V C = 0`, no flux of `C A` leaves a set of cubes | `magnetic_flux_out` | `Integral.lean` |
| HO1 (finding 446, T356(a)) | on the torus the circulation of `A` round a row passes every gauge change | `row_circulation_gauge` | `Holonomy.lean` |
| HO2, HO3 (T356(b), (c)) | the row field, `a` on every line of the direction `0`, has `C A = 0` and the circulation `n a` round every row | `row_field_curl`, `row_field_circulation` | `Holonomy.lean` |
| HO4 (T356(d)) | for `a ≠ 0`, `rowField a + G g ≠ 0` for every `g`: no gauge change removes it | `row_field_not_gauge` | `Holonomy.lean` |
| HO5 (T356(e)) | the row field has no divergence | `row_field_divergence` | `Holonomy.lean` |
| HO6 (T356(f)) | Pair sends `(rowField a, rowField ε)` after `k` steps to `(rowField (a - k λ ε), rowField ε)` | `row_field_pair`, `row_field_pair_iterate` | `Holonomy.lean` |
| DI1 (finding 447, T357(a)) | the Pair of one place with `μ = 4 sin² θ` sends `(2 sin θ, - sin θ)` after `k` steps to `(2 sin θ cos (2 k θ), sin ((2 k - 1) θ))` | `pairOne_wave` | `Dispersion.lean` |
| DI2 (T357(b)) | every `μ` in `[0, 4]` is `4 sin² θ` | `exists_angle` | `Dispersion.lean` |
| DI3 (T357(c)) | Pair carries every level of `L S` at `4 sin² θ` as that wave | `level_wave` | `Dispersion.lean` |
| DI4 (T357(d)) | `4 - 2 cos θ₁ - 2 cos θ₂ = 4 (sin² (θ₁/2) + sin² (θ₂/2))`, and the dispersion relation | `dispersion_identity`, `dispersion_relation` | `Dispersion.lean` |
| DI5 (T357(e)) | on the torus with one `κ` and one `λ`, the transverse plane wave turns by `2 θ` per step, `4 sin² θ = λ κ (4 - 2 cos θ₁ - 2 cos θ₂)` | `torus_dispersion` | `Dispersion.lean` |
| DL1 (finding 448, T358(a)) | a board's incidence and gauge over every commutative ring have `C G = 0`, and over the real numbers they are the board's own | `Board.incidenceR_mul_gaugeR`, `Board.incidenceR_real`, `Board.gaugeR_real` | `Dial.lean` |
| DL2, DL3 (T358(b), (c)) | the book's tick, Pair over `ZMod N` with the kick `Cᵀ C` and the drift `1` (TE1 with `N = 8`), keeps Gauss's law and passes the gauge | `Board.bookTick_charge`, `Board.bookTick_gauge` | `Dial.lean` |
| DL4, DL5 (T358(d), (e)) | it keeps `Ω` and `Q⋆` on the dial, is undone by `unpair`, and obeys the wave equation | `Board.bookTick_omega`, `Board.bookTick_qstar`, `Board.bookTick_unpair`, `Board.bookTick_wave` | `Dial.lean` |
| DL6 (T358(f)) | with a current on the dial, the divergence of `E` falls by that of the current | `Board.bookTick_continuity` | `Dial.lean` |
| DL7 (T358(g)) | on a finite board every light returns after some number of ticks | `Board.bookTick_returns` | `Dial.lean` |
| OR1 (finding 449, T359(a)) | on a wide board the far weight of `Cᵀ diag(K) C` at a flag of `σ`, read along the turn of `σ`, is `K σ` | `Board.farWeightRead_kick` | `OneRule.lean` |
| OR2, OR3 (T359(b), (c)) | a kick of reach 1 meeting A10, A11 and one rule for the far weights (a function of the flag's six paints read either way) is `Cᵀ diag(K) C` with `K` the same on squares whose flags have the same paints, and so on each class | `Board.one_rule_flags`, `Board.one_rule_classes` | `OneRule.lean` |
| OR4, OR5 (T359(d), (e)) | where every corner has one paint, such a kick is `Cᵀ diag(κ) C` with one `κ`, and a drift that is one rule is one number | `Board.one_rule_one_number`, `Board.drift_one_number` | `OneRule.lean` |
| SP1, SP2 (finding 450, T360(a), (b)) | `ω (θ) = 2 arcsin (c sin (θ / 2))` has `ω 0 = 0` and the derivative `c` at `0`, and meets the dispersion along an axis | `axisAngle_zero`, `axisAngle_hasDerivAt`, `axisAngle_dispersion` | `Speed.lean` |
| SP3 (T360(c)) | on the torus with one `κ` and one `λ`, `0 ≤ κ λ ≤ 1`, the transverse plane wave of wave numbers `(p, 0)` turns by `ω (θ₁)` per step with `c = √(κ λ)` | `torus_axis_wave` | `Speed.lean` |
| HD1 (finding 451, T361(a)) | for every real `A` and `x`, `A Aᵀ y = A x` has a solution `y` | `mul_transpose_solve` | `Hodge.lean` |
| HD2 to HD4 (T361(b) to (d)) | wherever `C G = 0`, every field is `G φ + Cᵀ ψ + h` with `Gᵀ h = 0` and `C h = 0`, the three parts orthogonal and each unique | `hodge_exists`, `hodge_orthogonal`, `hodge_unique` | `Hodge.lean` |
| HD5, HD6 (T361(e), (f)) | the gradient part carries the divergence and the transverse part the curl; the kick of Pair moves only the transverse part of `E` | `hodge_charge`, `hodge_curl`, `pair_parts` | `Hodge.lean` |
| FC1, FC2 (finding 452, T362(a), (b)) | on a wide complex of squares, where a line may be a side of any number of faces, a kick of reach 1 with `M G = 0` and `Gᵀ M = 0` is `Cᵀ diag(K) C`; and every `Cᵀ diag(K) C` is one | `SquareComplex.kick_forced`, `SquareComplex.kick_meets` | `ForcedComplex.lean` |
| FC3 (T362(c)) | every board is a complex of squares with the same incidence and gauge, wide when the board is | `Board.toSquareComplex`, `Board.toSquareComplex_incidence`, `Board.toSquareComplex_gauge`, `Board.toSquareComplex_wide` | `ForcedComplex.lean` |
| FC4, FC5 (T362(d), (e)) | the cubic torus of side `n > 1` is a complex of squares with the incidence and gauge of `Solid.lean`, and for `n ≥ 3` it is wide | `cubeComplex`, `cubeComplex_incidence`, `cubeComplex_gauge`, `cubeComplex_wide` | `ForcedComplex.lean` |
| FC6 (T362(f)) | on the cubic torus of side `n ≥ 3` the law of light is forced: such a kick is `Cᵀ diag(K) C` | `cube_kick_forced` | `ForcedComplex.lean` |
| BB1 (finding 453, T363(a)) | the line `(w, 0)` of the torus has the flags `(w, 0)`, along, and `(w - (0, 1), 2)`, against; the line `(w, 1)` has `(w - (1, 0), 1)` and `(w, 3)` | `torus_flag_zero`, `torus_flag_one` | `BookBoard.lean` |
| BB2, BB3 (T363(b), (c)) | for `n, m ≥ 3` the torus is wide, and for `n, m ≥ 2` every corner has the paint 4 | `torus_wide`, `torus_paint` | `BookBoard.lean` |
| BB4 (T363(d)) | on the torus a kick of reach 1 that meets A10, A11 and one rule for the far weights is `Cᵀ diag(κ) C` with one `κ`, and a drift that is one rule is one number | `torus_kick_forced`, `torus_drift_forced` | `BookBoard.lean` |
| JN1, JN2 (finding 454, T364(a), (b)) | the squares of the torus are joined, and so are its corners | `torus_joined`, `torus_corners_joined` | `TorusJoined.lean` |
| JN3, JN4 (T364(c), (d)) | for `n, m ≥ 3` a kick of reach 1 on the torus with `M G = 0` and `Gᵀ M = 0` is `Cᵀ diag(K) C` for exactly one `K`, and with one rule for the far weights for exactly one number `κ` | `torus_kick_unique`, `torus_kick_one_weight` | `TorusJoined.lean` |
| JN5 (T364(e)) | on the torus, with every `λ > 0`, a charge is `M φ` exactly when it sums to `0`, the potential is unique up to a constant, and such a charge is the divergence of a still field | `torus_coulomb`, `torus_coulomb_unique`, `torus_coulomb_field` | `TorusJoined.lean` |
| HM1 (finding 455, T365(a)) | on the torus, `Gᵀ h` at a corner is what its lines bring in less what they take out, and `C h` at a square is `h` round it | `torus_gaugeT_mulVec`, `torus_incidence_mulVec` | `TorusHarmonic.lean` |
| HM2 to HM4 (T365(b) to (d)) | on the torus a field with no divergence and no curl is uniform, one number on the lines of each direction, and every uniform field is one: the torus has two harmonic fields | `torus_harmonic_uniform`, `torus_uniform_harmonic`, `torus_harmonic_iff` | `TorusHarmonic.lean` |
| HM5 (T365(e)) | the row field of `Holonomy.lean` is the uniform field of `a` and `0` | `rowField_uniform` | `TorusHarmonic.lean` |
| HM6, HM7 (T365(f), (g)) | every field on the torus is `G φ + Cᵀ ψ` plus the uniform field of its two means, which are the only two numbers there; Pair keeps the means of `E` | `torus_hodge`, `torus_hodge_mean`, `torus_pair_mean` | `TorusHarmonic.lean` |
| IS1, IS2 (finding 456, T366(a), (b)) | `θ² - θ⁴ / 12 ≤ 4 sin² (θ / 2) ≤ θ²`, so the level of every plane wave is the square of the length of its wave vector up to the fourth order, in every direction | `four_sin_sq_half_bounds`, `level_isotropic` | `Isotropy.lean` |
| IS3, IS4 (T366(c), (d)) | on the torus of `n` by `n` squares the diagonal wave turns by `axisAngle √(2 κ λ) θ₁` per step, and as a function of the length of its wave vector its angle has the derivative `c` at `0`, as along an axis | `torus_diagonal_wave`, `diagonalAngle_hasDerivAt` | `Isotropy.lean` |
| MO1, MO2 (finding 457, T367(a), (b)) | on the torus Pair with a current `J` moves the means of `E` by minus the means of `J`, and with no current every number of steps keeps them | `torus_pairWith_mean`, `torus_pair_iterate_mean` | `TorusMomenta.lean` |
| MO3, MO4 (T367(c), (d)) | with one drift `λ` each step moves the means of `A` by `-λ` times the means of `E`, so after `k` steps by `-k λ` times them | `torus_pair_mean_A`, `torus_pair_iterate_mean_A` | `TorusMomenta.lean` |
| CG1, CG2 (finding 458, T368(a), (b)) | wherever `C G = 0`, every potential has exactly one gauge-equivalent potential with no divergence | `coulomb_gauge_exists`, `coulomb_gauge_unique` | `CoulombGauge.lean` |
| CG3, CG4 (T368(c), (d)) | with no charge, Pair with every kick `Cᵀ K C` and one drift keeps a potential with no divergence, step after step | `pair_keeps_coulomb_gauge`, `pair_iterate_keeps_coulomb_gauge` | `CoulombGauge.lean` |
| MD1, MD2 (finding 459, T369(a), (b)) | on the torus `Cᵀ ψ = 0` exactly when `ψ` is constant, and `G φ = 0` exactly when `φ` is | `torus_transpose_ker`, `torus_gauge_ker` | `TorusModes.lean` |
| MD3 to MD5 (T369(c) to (e)) | the gradients and the transverse fields of the torus each form a space of dimension `n m - 1`, the harmonic fields one of dimension `2`, together the `2 n m` lines | `torus_gradient_finrank`, `torus_transverse_finrank`, `torus_harmonic_finrank`, `torus_finrank_sum` | `TorusModes.lean` |
| EV1, EV2 (finding 460, T370(a), (b)) | `y ≤ arcsin y ≤ y / √(1 - y²)`, so in every direction `u` the angle per step of the plane wave of wave vector `t u` lies between `c t √(1 - t² / 12)` and `c t / √(1 - c² t² / 4)` | `le_arcsin_self`, `arcsin_le_div_sqrt`, `planeAngle_bounds` | `SpeedEveryDirection.lean` |
| EV3, EV4 (T370(c), (d)) | that angle divided by `t` tends to `c` as `t` tends to `0`, in every direction; and on the torus every plane wave turns by it per step | `planeAngle_speed`, `torus_plane_wave` | `SpeedEveryDirection.lean` |
| DM1 (finding 461, T371(a)) | on a wide board, in every naming of a domino, six different corners, seven different lines and two different squares, whose gauge and incidence, read with the naming's signs, are two fixed tables | `Board.domino_corner_injective`, `Board.domino_line_injective`, `Board.domino_square_ne`, `Board.domino_gauge`, `Board.domino_incidence` | `DominoRule.lean` |
| DM2, DM3 (T371(b), (c)) | every square at a line is a named square of its domino, and every side and corner of one is named; a kick that meets D17 meets one rule for the far weights | `Board.domino_reach`, `Board.d17_oneRuleFar` | `DominoRule.lean` |
| DM4, DM5 (T371(d), (e)) | so A10, A11, reach 1 and D17 leave `Cᵀ diag(K) C` with `K` one number on each class, one `κ` where every corner has one paint and on the torus of sides at least 3; and `Cᵀ diag(κ) C` meets D17 | `Board.d17_classes`, `Board.d17_one_number`, `torus_d17`, `Board.kick_rowRead`, `Board.kick_meets_d17` | `DominoRule.lean` |
| EU1 (finding 462, T372(a)) | on every map with `C G = 0` the dimension of the harmonic fields, `rank G` and `rank C` add up to the number of lines | `harmonic_count` | `EulerCount.lean` |
| EU2 (T372(b)) | on a board whose squares are joined `Cᵀ ψ = 0` exactly for `ψ` the same on every square, so `rank C + 1 = F`; where its corners are joined, `rank G + 1 = V` | `Board.transpose_ker_iff`, `Board.incidence_rank`, `Board.gauge_rank` | `EulerCount.lean` |
| EU3, EU4 (T372(c), (d)) | so on a board whose squares and corners are joined the harmonic fields have the dimension `2 - χ`; on the torus, `2` | `Board.harmonic_euler`, `torus_harmonic_euler` | `EulerCount.lean` |
| WN1, WN2 (finding 463, T373(a), (b)) | the window of `a` by `b` squares with open edges is a complex of squares whose maps close up; it is wide, so A10 and A11 with reach 1 leave `Cᵀ diag(K) C` | `windowComplex`, `window_incidence_mul_gauge`, `window_wide`, `window_kick_forced` | `OpenWindow.lean` |
| WN3, WN4 (T373(c), (d)) | on the window `G φ = 0` only for constants and `Cᵀ ψ = 0` only for `ψ = 0`, so it has no harmonic field | `window_gauge_ker`, `window_transpose_ker`, `window_harmonic_finrank`, `window_no_harmonic` | `OpenWindow.lean` |
| WN5 (T373(e)) | every field on the window is one gradient and one transverse field, each unique, and its charges sum to `0` | `window_hodge`, `window_divergence_sum` | `OpenWindow.lean` |
| OS1, OS2 (finding 464, T374(a), (b)) | on a wide complex the far weight of `Cᵀ diag(K) C` at a flag of `σ` is `K σ`, so `K` is unique; where every corner has one paint, one rule read on paints leaves one `κ`, and a drift that is one rule one `λ` | `SquareComplex.farWeightRead_kick`, `SquareComplex.kick_unique`, `SquareComplex.one_rule_one_number`, `SquareComplex.drift_one_number` | `SolidRule.lean` |
| OS3, OS4 (T374(c), (d)) | every corner of the cubic torus has one paint, so for side `n ≥ 3` the askings and one rule leave `κ Cᵀ C` for exactly one `κ`, and one `λ` | `cube_paint_const`, `cube_kick_one_number`, `cube_drift_one_number` | `SolidRule.lean` |
| WS1, WS2 (finding 465, T375(a), (b)) | on the cubic torus `Cᵀ ψ` and `Gᵀ A` read on the lines and corners, and `Cᵀ C + G Gᵀ` is the stencil of seven points on each direction | `cube_transpose_mulVec`, `cube_gaugeT_mulVec`, `cube_hodge_laplacian` | `SolidWaves.lean` |
| WS3, WS4 (T375(c), (d)) | the plane waves are the stencil's levels at `6 - 2 cos θ₁ - 2 cos θ₂ - 2 cos θ₃`, and the wave of an amplitude with no divergence is transverse light at `κ` times that level | `cube_stencil_wave`, `cube_transverse_wave` | `SolidWaves.lean` |
| WS5, WS6 (T375(e), (f)) | for each wave vector other than `0` the amplitudes with no divergence form a space of dimension `2`; Pair turns the wave by `2 θ` per step, `sin² θ = κ λ Σ sin² (θ_d / 2)` | `cube_polarizations`, `cube_dispersion`, `cube_dispersion_relation` | `SolidWaves.lean` |
| SM1, SM2 (finding 466, T376(a), (b)) | on the cubic torus the sum of `g` times its stencil is the sum of the squares of its steps, so a stencil `0` leaves `g` the same everywhere; a field is harmonic exactly when it is uniform | `cube_energy`, `cube_stencil_const`, `cube_harmonic_iff` | `SolidModes.lean` |
| SM3 to SM5 (T376(c) to (e)) | the harmonic fields, the gradients and the transverse fields form spaces of dimensions `3`, `n³ - 1` and `2 (n³ - 1)`; Pair keeps the three means of `E` | `cube_harmonic_finrank`, `cube_gradient_finrank`, `cube_transverse_finrank`, `cube_pair_mean` | `SolidModes.lean` |
| VS1, VS2 (finding 467, T377(a), (b)) | in every direction `u` of a solid the level of the plane wave of wave vector `t u` lies between `t² - t⁴ / 12` and `t²`, and such a level gives an angle per step between `c t √(1 - t² / 12)` and `c t / √(1 - c² t² / 4)` | `solid_level_direction`, `angle_of_level_bounds` | `SolidSpeed.lean` |
| VS3, VS4 (T377(c), (d)) | so the angle per step in every direction of a solid lies between those bounds, its ratio to `t` tends to `c`, and on the cubic torus every transverse plane wave turns by it | `solidAngle_bounds`, `solidAngle_speed`, `cube_plane_wave` | `SolidSpeed.lean` |
| GS1 (finding 468, T378(a)) | the angle per step of a plane wave in `k` dimensions, `2 arcsin (c √S)`, has in each angle the derivative `c sin (θ_j / 2) cos (θ_j / 2) / (√S √(1 - c² S))`, the group velocity; in two and three dimensions it is the plane and the solid angle | `waveAngle_hasDerivAt`, `waveAngle_two`, `waveAngle_three` | `GroupSpeed.lean` |
| GS2, GS3 (T378(b), (c)) | where `c² k ≤ 1` the group velocity has the size at most `c`; along an axis, for `0 < c < 1`, the group speed is below `c` at every shorter wave and `0` at `θ = π` | `groupVel_sq_le`, `axisAngle_hasDerivAt_at`, `axis_group_speed_lt`, `axis_group_speed_pi` | `GroupSpeed.lean` |
| CP1 to CP3 (finding 469, T379(a) to (c)) | on the torus the divergence summed over a box of `s` by `s` corners is the flux out through the `4 s` lines of its ring; at distance `r` from a lone charge `q` the mean outward field on the ring is `q / (8 r + 4)`, and some line carries at least the mean | `torus_box_gauss`, `torus_ring_mean`, `torus_ring_strongest` | `CoulombFall.lean` |
| CS1 to CS3 (finding 470, T380(a) to (c)) | on the cubic torus the divergence summed over a cube of `s³` corners is the flux out through the `6 s²` lines of its shell; at distance `r` from a lone charge `q` the mean outward field on the shell is `q / (6 (2 r + 1)²)`, and some line carries at least the mean | `cube_box_gauss`, `cube_shell_mean`, `cube_shell_strongest` | `CoulombFallSolid.lean` |
| KP1 (finding 471, C458) | the ends of a chain, at each dot what its lines bring in less what they take out; the ends of the trail of a walk are one at its dot less one at rest (Lemma 1.1) | `Stage.head`, `Stage.ends`, `Stage.ends_apply`, `Stage.ends_trail` | `KeepField.lean` |
| KP2, KP3 (C458) | the values of the ends of every chain add up to `0`; every assignment on the dots whose values add up to `0` is the ends of some chain | `Stage.ends_sum`, `Stage.exists_ends` | `KeepField.lean` |
| KP4 (C458) | the chain with the count `k` on the line `(a, g)` and nothing elsewhere has the ends `k` at the head less `k` at the tail; so one act is a hop, the making of a pair or an unmaking | `Stage.ends_single`, `Stage.ends_write` | `KeepField.lean` |
| KP5 (C458) | with finitely many acts and laws, on the dial of `n ≥ 1`, the ends of fillings form a map of additive groups; an assignment is the ends of some filling exactly when its values add up to `0` in `ℤ/n`, and then of exactly `n ^ r` fillings, `r = |acts| |laws| - |laws| + 1`; so `k` charges of one click stand alone exactly when `n` divides `k` | `Stage.endsDial`, `Stage.endsDial_mem_range_iff`, `Stage.card_endsDial_fiber`, `Stage.cast_fiber_exponent`, `Stage.charges_alone_iff` | `KeepField.lean` |
| KP6 (C458) | for `n, m ≥ 2` the world of the stage of two rows that pass is `ℤ/n × ℤ/m`, by an isomorphism that sends the law of `a` to `(1, 0)` and that of `b` to `(0, 1)` | `twoRows`, `twoRowsWorld`, `twoRowsWorld_law_a`, `twoRowsWorld_law_b` | `KeepField.lean` |
| KP7 (C458) | read through it, with `(a, g)` the line across at the corner of `g` and `(b, g)` the line up, the ends of every chain at every corner are minus the divergence of the field that the chain gives the torus's lines | `twoRowsField`, `twoRows_ends_eq_neg_divergence` | `KeepField.lean` |
| WV1 (finding 472, C459) | a wave is a complex number on every filling of a finite stage on the dial of `n`; the reading of `ℓ` after the write of `ℓ'` is the turn of `1` if `ℓ = ℓ'`, of `0` otherwise, times the write after the reading, and after the kept law of `z` it is the turn of `z`'s count on `ℓ` times the kept law after the reading; writes and kept laws pass each other, and readings pass each other | `Stage.Wave`, `Stage.waveWrite`, `Stage.waveRead`, `Stage.waveKept`, `Stage.read_write`, `Stage.read_kept`, `Stage.write_comm`, `Stage.write_kept_comm`, `Stage.read_comm` | `FillingWaves.lean` |
| WV2 (C459) | a kept law and a reading take every charge sector to itself, and the write of `ℓ` takes the sector of `ρ` to the sector of `ρ` with one more at the head of `ℓ` and one less at its tail | `Stage.waveSector`, `Stage.waveKept_sector`, `Stage.waveRead_sector`, `Stage.waveWrite_sector` | `FillingWaves.lean` |
| WV3 (C459) | each of the three kinds of table keeps the sum, over the fillings, of the squares of the sizes of a wave's numbers | `Stage.waveWrite_norm`, `Stage.waveRead_norm`, `Stage.waveKept_norm` | `FillingWaves.lean` |
| WV4 (C459) | every linear map of the waves to themselves is a sum, with complex coefficients, of products of writes and readings | `Stage.span_write_read` | `FillingWaves.lean` |
| WV5 (C459) | kept laws pass each other; writes and kept laws keep every part, with its numbers, and the reading of `ℓ` multiplies each kept law's number by the turn of that law's count on `ℓ`, to the power `-1` | `Stage.kept_comm`, `Stage.wavePart`, `Stage.write_part`, `Stage.kept_part`, `Stage.read_part` | `FillingWaves.lean` |
| ID1 (finding 475, C462) | on the ring of `N ≥ 5` places, with `S` the shift, the table `a S⁻¹ + b + c S` of reach 1, the same at every place, keeps the sum of the squares of the sizes of every wave exactly when `‖a‖² + ‖b‖² + ‖c‖² = 1` and two of `a`, `b` and `c` are `0`: it shifts rigidly, or it stands and turns (Meyer's theorem) | `reachOne`, `scalar_reach_one_unitary_iff` | `InnerDirection.lean` |
| ID2 (C462) | anticommuting involutions: two and three exist of size 2, and four of size 4; there are no two of any odd size, so none of size 1, and no four of size 2 | `AnticommutingInvolutions`, `pauli_anticommute`, `dirac_anticommute`, `no_anticommuting_odd`, `no_anticommuting_one`, `no_four_anticommuting_two` | `InnerDirection.lean` |
| ID3 (C462) | there are complex 2 × 2 matrices `A`, `B` and `C`, the quarter, third and half turns of the cube, with `A⁴ = B³ = C² = A B C = -1`, such that `A σx A⁻¹ = σy`, and `B` moves `σx` to `σy` to `σz` to `σx` | `turnA`, `turnB`, `turnC`, `turn_relations`, `turnA_moves`, `turnB_moves` | `InnerDirection.lean` |
| ID4 (C462) | no complex numbers `x`, `y` and `w` give `(x A)⁴ = (y B)³ = (w C)² = (x A)(y B)(w C) = 1`: the turns act on the half part only up to a sign that no rescaling removes | `spinor_no_rescaling` | `InnerDirection.lean` |
| ID7 (C462) | in the stage of `m` rows that pass up to a kept sign, every family of anticommuting involutions of size `d` gives a map of the world into the invertible `d × d` matrices, `gᵢ ↦ γᵢ` and `z ↦ -1`; every such map that sends `z` to `-1` sends the `gᵢ` to anticommuting involutions | `rowsStage`, `halfPart_hom`, `halfPart_anticommute` | `InnerDirection.lean` |
| KN1 (finding 473, C460) | the waves of one line on the dial of `n` with numbers in a field `K`, functions from `ℤ/n` to `K`, have the write and the reading by a turn `χ`, an additive character; where `n` is not `0` in `K` and `χ` is faithful (`χ k = 1` only for `k = 0`), every `K`-linear map of them is a sum of products of the write and the reading | `lineWrite`, `lineRead`, `span_write_read_of_faithful` | `KindOfNumber.lean` |
| KN2 (C460) | if `χ k = 1` for some `k ≠ 0`, the write made `k` times passes the write and the reading and is no multiple of `1`, so the products of the write and the reading do not make every table | `not_span_write_read_of_not_faithful` | `KindOfNumber.lean` |
| KN3 (C460) | a faithful turn into `K` exists exactly when `K` has a primitive `n`-th root of unity | `exists_faithful_iff` | `KindOfNumber.lean` |
| KN4 (C460) | for `n ≥ 3` every real turn of `ℤ/n` takes only the values `1` and `-1`, and none is faithful | `real_turn_not_faithful` | `KindOfNumber.lean` |
| KN5 (C460) | the dial's standard turn is faithful, its values have size `1`, and its reading keeps the sum of the squares of the sizes | `stdAddChar_faithful`, `stdAddChar_norm`, `lineRead_stdAddChar_norm` | `KindOfNumber.lean` |
| WK1 (finding 476, C463) | a complex 2 × 2 table `a · 1 + b · σx` keeps the sum of the squares of the sizes of every two numbers exactly when `‖a‖² + ‖b‖² = 1` and the real part of `a` times the conjugate of `b` is `0`, and exactly when `a = u cos θ` and `b = u i sin θ` for one `u` of size 1 and one angle `θ`: the link gate of `θ`, times `u` | `exchange_unitary_iff` | `TheWalk.lean` |
| WK2 (C463) | the walk, the coin `cos μ · 1 - i sin μ · σx` at every place and then the shift of the first number one place on and the second one place back, acts on the wave `e^{ikx}` of the ring, `k = 2 π j / N`, times two numbers, by its table `diag(e^{-ik}, e^{ik})` times the coin, whose trace is `2 cos μ cos k` and determinant `1` | `coin`, `walk`, `walkSymbol`, `walk_acts_by_symbol`, `walkSymbol_trace`, `walkSymbol_det` | `TheWalk.lean` |
| WK3 (C463) | `e^{-iε}` is a level of the walk's table at `k` exactly when `cos ε = cos μ cos k`; with `e^{-iε}` its inverse `e^{iε}` is a level too, so the levels come in pairs of opposite sign | `IsWalkLevel`, `walk_level_iff`, `walk_levels_pair` | `TheWalk.lean` |
| WK4 (C463) | the walk's table at `k + π` is minus its table at `k`, so every level `e^{-iε}` at `k` has the twin `-e^{-iε}`, the level of `ε + π`, at `k + π` | `walkSymbol_add_pi` | `TheWalk.lean` |
| ST1 (finding 477, C464) | with the symmetric sign, a whole number of charges on each level, if some level is below zero then for every number `M` some occupation has an energy below `M`: no occupation is lowest | `occupationEnergy`, `symmetric_no_lowest` | `Statistics.lean` |
| ST2 (C464) | with the alternating sign, `0` or `1` on each level, every occupation has an energy at least the sum of the levels below zero, and the sea, every level below zero filled once and no other, has exactly that energy | `IsAlternating`, `sea`, `alternating_energy_ge`, `sea_energy` | `Statistics.lean` |
| ST3 (C464) | for a coin angle `μ` strictly between `0` and `π / 2` and every wave number `k`, the walk's table has a level `e^{-iε}` with `ε` strictly between `0` and `π`, and its pair `e^{iε}`: read as energies, one above zero and one below | `walk_level_signs` | `Statistics.lean` |

## Notes

- **Lemma 2.4 is the theorem of Magnus and Fox.** Its proof here follows THEORY.md's, with
  any choice of a walk to each dot in place of the first walks; no spanning tree is used.
  In the literature the trail is the Fox derivative of a word, read in the group ring, and
  the geometric flow of its path on the Cayley graph; T4(a) is in print as a theorem on
  flows (Droms, Lewin and Servatius; Vershik and Dobrynin; Myasnikov, Roman'kov, Ushakov
  and Vershik).
- **Rules 5 and 7 are proved by example**: the six orders of three things over the wheel of
  two, and the wheel of two with one more act.
- **Pair** is the law of light of the ledger's wave 39 (astra's): its laws are held there by
  scripts, and proved here over any commutative ring (finding 422 of the ledger). Its reading on
  a finite board and its window of stability are findings 424 and 425; its window with a drift by
  sorts is finding 427, that window read on the squares is finding 428, its strict form and local
  test are finding 430, the local tests on a board's incidence are finding 432, and the board
  itself, its gauge, the window on its lines and the torus are finding 434; the step from the
  window to bounded orbits, on many places and on every board, is finding 436; that the window
  is exact, and that two different weights on the squares give two different kicks, are findings
  438 and 439; that on a wide board the askings leave the kicks `Cᵀ diag(K) C` and no other is
  finding 440; Pair with a current, and Maxwell's equations for it on every map with `C G = 0`, are
  finding 441; the cubic torus, its three maps and its magnetic charge are finding 442; the wave equation of Pair
  and the plane waves of light on the torus are finding 443; Coulomb's problem on a board is finding
  444; Maxwell's equations in integral form are finding 445; a flat field on the torus that no gauge
  removes is finding 446; the dispersion of light on the torus is finding 447; the book's
  tick on the dial of eight is finding 448; one rule, finding 421's T331(b), is finding 449;
  the speed of light along an axis is finding 450; the three parts of a field are finding 451;
  the law of light forced on every wide complex of squares, and in the cubic torus, is finding 452;
  the torus as a wide board of one paint, where Pair's kick and drift are forced, is finding 453; its
  squares and its corners joined, one weight for each kick and Coulomb's problem on it, finding 454;
  its two harmonic fields, the uniform ones, and the means of `E` that Pair keeps, finding 455;
  one speed of light along the axes and the diagonals, and a level of the fourth order, finding 456;
  the two momenta of the torus, kept, and the means of `A` that they move uniformly, finding 457;
  the Coulomb gauge, which Pair keeps where there is no charge, finding 458; the dimensions of the
  three parts of a field on the torus, `n m - 1`, `n m - 1` and `2`, finding 459; one speed of light
  in every direction at long waves, finding 460; D17 read on the dominos of a wide board, which
  gives one rule for the far weights, finding 461; the count of the harmonic fields on every map
  with `C G = 0`, and `2 - χ` on every closed board whose squares and corners are joined, finding
  462; the book's window with open edges, where the law is forced and no field is harmonic,
  finding 463; one rule in the cubic torus, read on paints, which leaves one `κ` and one `λ`,
  finding 464; light in a solid, its stencil, its two polarizations and its dispersion, finding
  465; the three momenta of the cubic torus and the dimensions of its fields, finding 466; one speed
  of light in every direction of a solid, finding 467; the group speed, at most `c` where the
  window holds, finding 468; the fall of Coulomb's field in the plane, as `1/r` in the mean,
  finding 469, and in a solid, as `1/r²` in the mean, finding 470; the ends of a trail, which give
  Gauss's law on every stage and on every dial, and the torus as the map of two rows that pass,
  finding 471; waves on the fillings, with Weyl's relation, Gauss's law as the charge sectors and
  the parts, finding 472; the inner direction that a charge's motion forces, the half part of rows
  that pass up to a kept sign, on which the cube's turns act only up to a sign, finding 475; the
  kind of number, which a dial of 3 or more values forces to hold a turn that no real number is,
  finding 473; the walk of a charge, forced up to its angles, with the levels `cos ε = cos μ cos k`
  and a twin at `k + π`, finding 476; the statistics of a charge whose walk has levels of both
  signs, with no lowest energy for the symmetric sign and the sea for the alternating sign, finding
  477.
- **Not in the library:** the count of closed trails by first
  walks (Lemma 2.3); Theorems C and D; T3, T5 and T6; and the comparison of a run's own cell
  tables with a read board, which is a finite check of that run's data.
