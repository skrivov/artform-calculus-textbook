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
  sorts is finding 427, that window read on the squares is finding 428, and its strict form and
  local test are finding 430.
- **Not in the library:** the ends of a trail (Lemma 1.1); the count of closed trails by
  first walks (Lemma 2.3); Theorems C and D; T3, T5 and T6; that pair's kick is forced
  (finding 421); and the comparison of a run's own cell tables with a read board, which is a
  finite check of that run's data.
