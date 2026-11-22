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
  squares and its corners joined, one weight for each kick and Coulomb's problem on it, finding 454.
- **Not in the library:** the ends of a trail (Lemma 1.1); the count of closed trails by first
  walks (Lemma 2.3); Theorems C and D; T3, T5 and T6; the step from D17's one rule to one rule
  for the far weights (finding 449, on paper); and the comparison of a run's own cell tables
  with a read board, which is a finite check of that run's data.
