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

## Notes

- **Lemma 2.4 is the theorem of Magnus and Fox.** Its proof here follows THEORY.md's, with
  any choice of a walk to each dot in place of the first walks; no spanning tree is used.
  In the literature the trail is the Fox derivative of a word, read in the group ring, and
  the geometric flow of its path on the Cayley graph; T4(a) is in print as a theorem on
  flows (Droms, Lewin and Servatius; Vershik and Dobrynin; Myasnikov, Roman'kov, Ushakov
  and Vershik).
- **Rules 5 and 7 are proved by example**: the six orders of three things over the wheel of
  two, and the wheel of two with one more act.
- **Not in the library:** the ends of a trail (Lemma 1.1); the count of closed trails by
  first walks (Lemma 2.3); Theorems C and D; T3, T5 and T6; pair.
