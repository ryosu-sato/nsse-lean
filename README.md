# Decidability of non-structural subtype entailment (Lean 4)

This repository contains a Lean 4 formalization that decides **non-structural subtype entailment** (NSSE) over
finite, regular and arbitrary trees, for signatures with bottom `bot` and top `top`:

* **one constructor** `f` of arity `d > 0`, either covariant or with arbitrary variance (each argument covariant or
  contravariant, given by a polarity vector; function types `{bot, ->, top}` are `d = 2` with polarity
  (contravariant, covariant));
* **several constructors** of arbitrary finite arities, either all covariant or with head- and argument-dependent
  variance (for example `{bot, ->, *, top}`); see [Several constructors](#several-constructors).

Countermodels are computed when entailment fails.

The development was produced with the help of AI assistants (Anthropic's Claude and OpenAI's Codex/ChatGPT) and is
machine-checked by Lean. It has **not** yet been reviewed by a human referee; please treat it as research material.
A written explanation exists only for the one-constructor covariant case (`paper_en.pdf`).

## The problem

Trees are possibly infinite trees whose nodes are labelled `bot`, `top` or a constructor; a node labelled by a
constructor of arity `k` has `k` children. The order is the non-structural one: `bot <= t <= top`, two trees with
different constructors at the root are incomparable, and `g(a_1,...,a_k) <= g(b_1,...,b_k)` iff `a_i <= b_i` at
covariant and `b_i <= a_i` at contravariant positions. On infinite trees the order is the greatest such relation. An
input is a finite list of premises `s <= t` and `s = t` between arbitrarily nested terms over variables, `bot`, `top`
and the constructors, together with a query `a <= b` between two terms. The question is whether every valuation
satisfying the premises satisfies the query. Three semantic domains are treated separately: arbitrary trees, regular
trees (finite graphs), and finite trees.

## One constructor

All final theorems of this part carry the hypothesis `0 < d`. Each Boolean below is a computable definition.

| result | module | theorems |
|---|---|---|
| covariant, term input | `NSSE/TermEntailmentDecision.lean` | `decideAll_correct`, `decideRegular_correct`, `decideFinite_correct`, `regular_entails_iff_all`, satisfiability: `decideAllSatisfiable_correct`, `decideFiniteSatisfiable_correct` |
| covariant, countermodels | `NSSE/TermCountermodelExtraction.lean` | `extractRegular_correct` (finite-graph countermodel), `extractFinite_correct` (finite countermodel) |
| covariant, counted complexity | `NSSE/SevenExpTime.lean` | `result`, `bound_explicit` (see below) |
| arbitrary variance, term input | `NSSE/ContraTermEntailmentDecision.lean` | `decideAll_correct`, `decideRegular_correct`, `decideFinite_correct`, `regular_entails_iff_all` |
| arbitrary variance, flat input with countermodels | `NSSE/ContraEntailmentDecision.lean`, `NSSE/ContraFiniteEntailment.lean` | `decideEntails_correct`, `extract_correct` (regular countermodel); `decideFiniteEntails_correct`, `extractFinite_correct` (finite countermodel) |

For example, the arbitrary-variance theorem over arbitrary trees reads

```lean
theorem NSSE.ContraTermEntailmentDecision.decideAll_correct
    {n d : Nat} {POL : ContraTrees.Polarity d} (Q : SubtypeTerms.Query n d) (hd : 0 < d) :
    ContraTermDecision.termDecideEntails POL Q hd = true <->
      ContraTermSemantics.Entails (ContraConstraints.treeConstructor POL) Q
```

where `ContraConstraints.treeConstructor POL` is the constructor on the type of all trees with the order defined as
the greatest simulation (`NSSE/ContraTrees.lean`, `IsSim`, `Le`).

**Complexity.** For the one-constructor covariant decision, `NSSE/SevenExpTime.lean` bounds a counted step measure
of the implementation by seven exponentials of a polynomial in the encoded input length. The count covers decoding
the bit string and the decision itself, but not the conversion of the decoded query into the decision's internal
form (`toQuery`, `packQuery` in `NSSE/CodedTermEntailment.lean`). It is a statement about this counted cost model,
not about machine time. `NSSE/SevenExpTimeTarget.lean` writes down a machine-level target, but its machine model
(`BitDecider`) puts no finiteness condition on `State`, so as stated it is not a meaningful open problem; the model
needs repair. No complexity bound is claimed for the other decisions. The procedures prove decidability; they are
not practical: the full decision does not finish on small inputs.

## Several constructors

Here the constructors are the elements of a finite type `H` of heads, each `h : H` with arity `arity h` (nullary heads and
an empty `H` are allowed). Terms, premises and the query are as in [The problem](#the-problem) (`NSSE/MultiConstructorTerms.lean`,
`Query`). With `H` a one-element type this includes the one-constructor case, formalized separately.

| result | module | theorems |
|---|---|---|
| covariant, term input | `NSSE/MultiConstructorTermDecision.lean` | `inspectAll_correct`, `inspectRegular_correct`, `inspectFinite_correct`, satisfiability: `inspectAllSatisfiable_correct`, `inspectFiniteSatisfiable_correct` |
| head- and argument-dependent variance, term input | `NSSE/MultiVarianceTermDecision.lean` | `inspectAll_correct`, `inspectRegular_correct`, `inspectFinite_correct`, satisfiability as above |
| same, countermodels | `NSSE/MultiVarianceTermExtraction.lean` | `all_none`, `all_some` (finite-graph countermodel), `regular_none`, `finite_none`, `finite_some` (finite countermodel) |

The variance is a polarity `pol : (h : H) -> Fin (arity h) -> Bool` (`NSSE/MultiVarianceEncoding.lean`); `pol h i = true`
makes argument `i` of `h` contravariant; the all-`false` polarity is the covariant case, so the countermodel
theorems also cover it. `NSSEMultiConstructor.lean` imports the three modules; build it with
`lake build NSSEMultiConstructor`. Only the modules these theorems depend on are included (about 340 files). No
complexity bound is claimed, and the procedures are not practical.

## Trust base

* Lean `v4.19.0`, Mathlib `v4.19.0`.
* No `sorry`, no added axioms, no `native_decide`. `#print axioms` on the final theorems gives
  `[propext, Classical.choice, Quot.sound]`.
* `lake build` builds the default targets `NSSE` (one constructor and the research-side modules) and
  `NSSEMultiConstructor` (several constructors); `NSSE/` holds about 1,320 modules.

```sh
lake exe cache get   # optional: downloads Mathlib build files
lake build
```

To check the axioms, compile a file such as

```lean
import NSSE.TermEntailmentDecision
import NSSE.ContraTermEntailmentDecision
import NSSEMultiConstructor
#print axioms NSSE.TermEntailmentDecision.decideAll_correct
#print axioms NSSE.ContraTermEntailmentDecision.decideAll_correct
#print axioms NSSE.MultiConstructorTermDecision.inspectAll_correct
#print axioms NSSE.MultiVarianceTermDecision.inspectAll_correct
#print axioms NSSE.MultiVarianceTermExtraction.all_some
```

with `lake env lean <file>`.

## How the proof goes (one constructor)

This section describes the one-constructor proof, which `paper_en.pdf` explains for the covariant case. The
several-constructor proof is not described here; no written explanation of it has been prepared.

1. **From entailment to words (Part I).** A failure of entailment is witnessed at a finite path of the trees.
   Support closure, clash conditions and a two-set least model decide satisfiability. A finite automaton reads
   paths, and its acceptance is proved sound (accepted paths are safe in every solution) and complete (for a
   rejected path, a terminal gadget extending the premises is clash-free, and its least model is a regular
   countermodel). For the covariant constructor this is the forward direction of the Niehren-Priesnitz
   characterisation by cap automata, proved again. For arbitrary variance, labels are adjusted by path polarity,
   which turns the order into a pointwise order (`ContraTrees.le_iff_plabel`, `ContraTrees.E`), and the automaton
   carries a polarity bit.
2. **Deciding the word problem (Part II).** Universality of the resulting restricted cap set expressions is
   decided. The candidate words split into a live part, where coverage is forced to be eventually periodic and is
   decided by one regular inclusion, and a nonlive part, where every suffix has boundedly many borders. A bounded
   tower of block encodings then reduces the nonlive part to a first-order sentence over the finite alphabet.
   Both versions use this part unchanged.
3. **Finite trees.** A cycle test on a signed pair graph characterises finite satisfiability. It is invariant under
   the terminal gadget, so the same automaton decides finite entailment.

A shortcut that does **not** work: splitting each variable into a covariant and a contravariant copy and calling the
covariant decision. For unary contravariant `f`, `{x <= f(z), f(z) <= x, f(y) <= z, f(y) <= y}` entails `x <= y`, but the
split covariant system does not.

## Files

* The final theorems and the modules they depend on are listed above. The `Contra*` modules (S1-S7) contain the
  arbitrary-variance development: `ContraTrees`, `ContraConstraints`, `ContraSupport`, `ContraSatisfiability`,
  `ContraAutomaton`, `ContraSoundness`, `ContraGadget*`, `ContraCompleteness`, `ContraEntailmentDecision`,
  `ContraFinite*`, `ContraTerm*`.
* The several-constructor theorems depend on the modules imported, directly or not, by `NSSEMultiConstructor.lean`:
  mostly `MultiConstructor*`, `MultiVariance*` and `P0*`, plus two older modules (`GeneralCopyGrid`,
  `PeriodicCopyHeadNormalization`).
* Many other modules are research-side developments from earlier attempts at the several-constructor case and at
  related combinatorial questions. They are checked by Lean.
* `paper_en.pdf` explains the one-constructor covariant proof (the paper does not cover the other results).
* `NSSE/Erratum.lean` and `NSSE/ErratumInstance.lean` formalize the core of an erratum to Niehren and Priesnitz,
  *Information and Computation* 186(2), 2003: Proposition 16(2) and Theorem 4 (the back translation) are false as
  stated, and the minimal three-state counterexample to Proposition 16(2) is proved in Lean.

## Related work

* J. Niehren and T. Priesnitz characterised non-structural entailment by cap automata (TACS 2001;
  *Information and Computation* 2003). The covariant proof here uses the forward direction of that
  characterisation, proved again, and not the statements covered by the erratum above.
* F. Henglein and J. Rehof proved PSPACE-hardness of non-structural entailment.
* Independent Lean-certified decisions of the one-constructor case were announced in October 2026:
  F. Henglein, J. Rehof, M. Henglein et al., <https://github.com/mhenglein/subtype-entailment>
  (bottom and a covariant binary product), and Y. Zhao, <https://github.com/noti0na1/deci-nsse>
  (bottom, top and one constructor of any arity and variance). The proofs are different.

## Author

Ryosuke Sato (Tokyo University of Agriculture and Technology)
