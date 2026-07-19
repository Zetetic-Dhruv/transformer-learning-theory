# The model store: a query-answering identification machine

**The object (line one).**

```
answer_with_cert :
  ( store : List C,  decode D : C → X'→Y',  context s : List (X'×Y'),  query q ∈ Q )
      →  ( answer : ⟦q⟧,  certificate : version space V(s) )
```

The banked characterization is the single instance q = q₀ (least-survivor identification: return the least-indexed candidate consistent with every observation in the context). The query language Q (observational-layer version-space functionals: membership, consistency, count, output-marginal, least-survivor; enlarged by do-operators at the interventional and counterfactual layers) is the machine's specification and carries status OPEN: the family is unbuilt, and the nine results below are its q₀ slice. The banked half, titled honestly: first-fit identification over a store, completely characterized.

**One sentence.** A model store is a finite list of candidate models read as a white-box retrieval machine: it consumes a context (a stream of observation pairs), keeps exactly the candidates consistent with every observation so far (the version space), and returns the least-indexed survivor, with that version space emitted as the certificate.

## The input/output diagram

```
  query q ∈ Q            banked slice: q₀ = least-survivor identification
      │
      ▼
  context s = [ (x₁,y₁), (x₂,y₂), … ]              decode D : C → X'→Y'
      │
      ▼
  ┌────────────────────────────────────────────────┐
  │  VERSION SPACE   V(s) = { c ∈ store :           │ ══ certificate ══►  co-output
  │                  c fits every (xᵢ,yᵢ) in s }    │    (every reachable machine
  │  monotone: shrinks with s, never grows          │     state decodes to V(s);
  └────────────────────────────────────────────────┘     white-box, M2)
      │                                    │
      │ SUPPORT                            │ WEIGHTS
      │ which candidates survive;          │ softmax vector over candidates:
      │ the argmax partition (M3, M4)      │ margins, calibration, loser geometry
      ▼                                    ▼
  ┌───────────────────────────┐     tempering (T → 0) acts ONLY here:
  │  SELECTION HEAD           │     the support is frozen, the weights flow;
  │  ⟦q₀⟧ = least survivor    │     unidentifiable from the hard channel
  │  (the Occam optimum, M6)  │     (CONJECTURE, M6)
  └───────────────────────────┘
      │
      ▼
  answer = some (least-indexed survivor)      or      none   (V(s) = ∅)
```

## The machine: one argument in ten movements

One shape recurs at four scales: a determiner escapes its finite frame, and the object is completed by enlarging the frame. A single query escapes (what the store is, is not fixed by q₀ alone), and the completion is the query family Q. A finite context escapes (no finite prefix fixes the limit answer), and the completion is the countable-union-of-intersections at the limit (M9). Representability escapes (a target outside the candidate list cannot be identified), and the completion is the tell-tale condition that would raise consistency-convergence to target-identification (M8). The observational layer escapes (observationally equivalent stores answer alike), and the completion is the do-operator enlargement that separates them (M10). The nine banked movements M1 through M9 fix the object at q₀; the escape-and-enlargement shape they exhibit is what the frontier M10 and the open query family inherit.

**M1. One function, two faithful realizations.** The store's answer to any context is computed identically by a machine that threads a state left to right through the context (sequential) and by an order-free machine that reads each observation once and combines them under one commutative operation (pooled). The two agree on every context, for every decode, with no side condition. The store is one function with two realizations, sequential and parallel at once. (Positioning: sequential automaton against weight-tied single-pass and pooled architectures.)

**M2. White-box: every internal state is its version space, and that set is the certificate.** At every computation step the machine's state decodes, by a reading proved to be a homomorphism onto the mask dynamics, to exactly the version space consistent with the context so far: the initial state reads as the full store, each step as the keep-filter. Two faithful readings agree at every reachable state, so the reading is canonical along the trajectory and there is no hidden internal freedom, and the answer is a checkable function of this set. White-box holds universally for the canonical machines and presentation-relatively for the optimized machine (faithful on its declared presentation), and is not yet discharged for a neural realization; emitting the certificate as an explicit co-output of one function is the standing interface obligation. (Positioning: forward simulation and refinement mappings; proof-carrying and self-explaining output; knowledge compilation.)

**M3. An exact capacity price, not a bound.** The smallest machine reproducing the store's answers has size exactly the number of distinct version-space configurations the store can reach: an equality (the version-space index) that fixes the price rather than bounding it. Two resources pay this one price at a fixed exchange rate, with sequential state count and parallel width-times-precision the same number, converted by complementation. Whatever computes the store costs precisely what its reachable version-space structure costs, and never less. (Positioning: state minimization; version spaces; the exchange is De Morgan.)

**M4. Order is a resource the store can spend or refuse.** The store's information splits cleanly: everything depending only on which candidates survive is recovered by the order-free machine, and everything depending on the order of elimination provably escapes it, since no function of any order-free aggregate recovers that order while a sequential thread recovers it exactly. The boundary between the two grades is sharp and proved from both sides. (Positioning: permutation-invariant pooling has strictly less resolving power than a thread.)

**M5. The revision budget is exactly the store size.** As the context grows the store changes its answer at most once per candidate, because each revision permanently eliminates the candidate just returned and eliminated candidates never return, so revisions are bounded by the store size on every context. A kill family (an adversarial elimination schedule that removes one candidate per observation) spends the budget to the last unit, so the worst case equals the store size and is realized at separable stores. The sharper model-grain form, revisions bounded by the count of distinct models rather than by code-list length (duplicate codes are eliminated together), is conjecture-grade, targeted by the geometry arc. (Positioning: mind-change complexity, as an exact count and not an asymptotic order.)

**M6. Temperature-free, Occam-biased retrieval; tempering flows in the weights, the answer stays fixed.** The returned candidate is at once the least-indexed survivor, the unique optimum under every complexity-decreasing weighting simultaneously, and the top choice of a soft differentiable selection over fit-scores at every temperature. Tempering the soft training regime down to the hard decode regime therefore never moves the answer: the support (the version space and its argmax partition) is frozen, and only the weights the store places on candidates flow, so all information tempering exposes beyond the answer lives in how strongly the store rejects non-survivors (the loser geometry). The identifiability claim, that these tempering degrees of freedom are exactly the weight stratum and are unidentifiable from the hard-output channel (two stores with identical survivor trajectories can carry different tempered weight vectors), is conjecture-grade, targeted by the geometry arc. (Positioning: MAP and Occam under a complexity-decreasing prior; softmax top-1 equals hard retrieval, temperature-unconditional; the loser geometry is the formal locus of Hinton's dark knowledge.)

**M7. Settling is simultaneous across every dial.** On any unbounded stream the version space is eventually constant, and every observable of the store (its answer, its size, every readable dial) freezes at one common time. Settling is a property of the version space, and each dial inherits it, so after a single settling moment nothing about the store moves again. (Positioning: convergence on a decreasing chain in a finite lattice.)

**M8. Identification in the limit, and its one genuine boundary.** If some candidate is consistent with the entire stream, the limit answer is a candidate consistent with every prefix (the least such, by the Occam bias of M6), reached after at most the store's model-count in revisions. As banked this is realizable consistency-convergence with an Occam bias; it does not deliver target-identification, since the limit representative need not equal the intended target, and the store cannot identify a target outside its candidate list at all (it returns its simplest consistent approximation). Realizability is the machine's one genuine incapacity (LAW-SCOPING: a boundary of the object that no construction removes), and raising consistency-convergence to target-identification is a closure obligation, discharged by a tell-tale or finite-thickness condition on the candidate class. (Positioning: Gold identification in the limit on realizable text; Angluin 1980 tell-tales and finite thickness are the closure; class-level uniqueness of the limit is a separate adjoined condition.)

**M9. Genuinely infinitary, bracketed exactly, with a necessarily existential lower bound.** The limit event equals a countable union of countable intersections of finite-context events: the universal upper half, holding for every store with no hypothesis. No finite context determines the limit answer, and already at a two-candidate store two streams agreeing on any finite prefix settle on different candidates: the lower half. This lower half is existential of necessity, since single-candidate stores are prefix-determined (their answer is fixed at the empty prefix) so a universal lower bound is false; the bracket is a universal upper identity together with an existential prefix-escape witness. Placing the along-stream limit event and the across-parameter certificate in one formal frame is an open machine-level obligation (ALIGN-ONE-FRAME). (Positioning: the second Borel and arithmetical level, Σ⁰₂-shaped; the label is a gloss on the proved set-identity; de Brecht-Yamamoto is where a lightface refinement would live.)

**M10. The frontier: a search engine over models, causal ones included (conjecture).** When the candidates are structured models, in particular small causal structures, the query "which model fits this context?" makes the store a search engine over model space, retrieving the simplest consistent model at the exact capacity price of M3 and the exact revision budget of M5. The open frontier is whether a large model with confounders and counterfactuals can be reconstructed by search from small atoms (bow models) held in the store at an exact query price, with the witness obligation the exact do-query complexity of reconstructing the bow class up to observational equivalence together with a matching lower bound (the causal analog of the M5 pair). The banked corpus does not reconstruct SCMs and the in-house causal-identification scaffold is placeholder-grade; the novelty claimed is the exact version-space price for causal identifiability, which the bounds-only causal-discovery literature lacks. (Positioning: Tian-Pearl c-component factorization; Shpitser-Pearl ID and IDC; the Causal Hierarchy Theorem, where do-words as separating enlargements are generic non-collapse; Markov equivalence; active causal discovery and experiment design, Eberhardt, Hauser-Bühlmann, Shanmugam, the true home; the exact-price seam is the distinction.)

## The method: six principles and a soundness seed

The method is a way of doing machine-learning theory, stated without the store so it transfers to the next object.

1. **Claims are locked before they are proved.** Each result is written first as a statement (a type) and fixed; the proof follows, may change the construction, and never the statement.
2. **Statements are never weakened under proof pressure.** When a proof is hard, the construction is strengthened and the claim held: simplify the proof, keep the theorem. A special case is a turn-scoped probe, never a renamed goal.
3. **Every argument is carried by a kernel-checked witness.** Each claim is a machine-verified declaration with an audited axiom footprint and zero gaps. What is not checked is not banked.
4. **Witnesses execute, they compute and do not merely typecheck.** Where a claim has a finite instance, that instance is run by the kernel's decision procedure as a second independent check; here a run caught a real off-by-one in a revision count.
5. **Exactness is preferred over bounds.** Where the tradition offers an inequality, the method seeks the equality: capacity priced exactly, the revision budget counted exactly, selection-rule agreement proved as identity.
6. **The primary artifact is an evidence bank.** Results are deposited as named, typed, kernel-checked declarations, composable by later results and re-checkable by anyone; exposition overlays the bank.

**The meta-theorem seed.** The transferable core is a soundness transport: a certified witness implies ideal machine behavior. The banked seed is the forward-simulation statement that a step-faithful code's behavior equals the reference decode (`behavior_eq_of_stepFaithful`), instantiated per machine. Promoting the seed to one soundness meta-theorem quantifying over an abstract witness class (certified witness ⟹ ideal behavior, for any witness in the class) is the named method obligation.

**Why it transfers.** The method separates the strength of an argument from the construction of its witness: the claim's strength is a property of the ideal object, and every construction condition is a property of the witness. The kernel rejects any statement it has not proved, so the qualifications that survive are exactly the ones written into a statement, explicit and locatable, and a characterization becomes a conjunction of banked theorems a referee can quote field by field. Exact invariants that run are measurements, so the same method points at the next object (the capacity store, the exchange law, the neural realization) where the theory must compute against a real artifact and not only describe one.

## The claim ledger

Hypothesis types: **LAW-SCOPING** (a genuine boundary of the object; a machine caveat), **EXTREMAL-SCOPING** (scopes a worst-case achievement claim while the universal upper claim stays hypothesis-free; the worst case is realized at separable stores), **CHART-FIXING** (a presentation, convention, or witness size; the general claim is discharged with no extra hypothesis). Litmus: a hypothesis is CHART-FIXING exactly when a universal banked theorem discharges the general claim without it; if the general claim needs the hypothesis, it is LAW-SCOPING or EXTREMAL-SCOPING. Status vocabulary: witnessed-exactly, witnessed-at-instance, conjecture, open.

| Arg | Statement at q₀ | Type of every hypothesis | Witness status | Lean declarations |
|---|---|---|---|---|
| M1 | Sequential and pooled machines both compute the reference decode on every context. | none | witnessed-exactly | `StoreCharacterization.compiled`, `.pooled`; `behavior_eq_of_stepFaithful`; `pooledBehavior_killUnionPooled` |
| M2 | Every reachable state decodes to the version space; the reading is canonical along the trajectory. | CHART-FIXING (presentation-relative for the optimized machine); certificate co-output = open interface | witnessed-exactly (canonical machines); witnessed-at-instance (optimized machine) | `StepFaithful`; `behavior_eq_of_stepFaithful`; `stepFaithfulOn_dec_unique` |
| M3 | Least machine size equals the version-space index, exactly (IsLeast). | CHART-FIXING (complete-and-sound articulated presentation); EXTREMAL-SCOPING (separation, aligning codes with models) | witnessed-exactly | `StoreCharacterization.price`; `pooledIndex_isLeast`; `versionIndexOn_le_pow_of_pooledComputes` |
| M4 | No order-free aggregate recovers elimination order; a thread recovers it exactly. | none (two-sided) | witnessed-exactly | `no_pooledReadout_mindChanges`; `mindChangeFold_eq` |
| M5 | Revisions ≤ store size on every context; equal to store size under a kill family. | EXTREMAL-SCOPING (kill family for the equality); CHART-FIXING (the terminal-drop counting convention, k against k−1) | witnessed-exactly | `StoreCharacterization.revisions`, `.revisions_tight`; `mindChanges_le_length`; `mindChanges_killEnum` |
| M6 | Least-survivor = Occam optimum = softmax top-1 at every temperature; tempering degrees of freedom are the weight stratum, unidentifiable from the hard channel. | CHART-FIXING (⊤-σ-algebra on the soft face); tempering identifiability = conjecture | witnessed-exactly (hard face); witnessed-at-instance (soft face); conjecture (tempering) | `StoreCharacterization.selection`; `abduce_eq_some_get_min'`; `gibbs_top1_eq_abduce`; `abduce_eq_fitRouter_route`; `min'_unique_argmax_of_strictAnti` |
| M7 | The version space and every dial settle at one common time. | none | witnessed-exactly | `StoreCharacterization.settles`; `abduce_settles`; `fitSet_settles`; `dials_settle` |
| M8 | Realizable: the limit answer is the least globally consistent candidate. | LAW-SCOPING (realizability is a boundary; target-identification via tell-tale is an open closure) | witnessed-exactly (consistency-convergence); open (target-identification) | `StoreCharacterization.gold`; `limitAbduce_gold` |
| M9 | Limit event = ⋃⋂ of prefix atoms (universal upper); escapes every finite prefix (existential lower). | LAW-SCOPING (the existential lower bound is necessary; ALIGN-ONE-FRAME is open); CHART-FIXING (the Σ⁰₂ label is informal) | witnessed-exactly (upper); witnessed-at-instance (lower, two-candidate store) | `StoreCharacterization.floor`; `limitAbduce_event_eq_iUnion_iInter`; `limit_event_not_prefixDetermined` |
| M10 | Store as a model-space search engine; exact do-query price for bow-class reconstruction up to observational equivalence. | conjecture (machine reach); placeholder-grade substrate (in-house causal-ID) | conjecture; open | none banked |

Machine theorem: `modelStore_characterized : ∀ D cands, StoreCharacterization D cands`, the universal nine-field characterization. Method meta-theorem (seed): `behavior_eq_of_stepFaithful`, the forward-simulation soundness transport; promotion to a witness-class-general soundness statement is open.

## Related work

- **Angluin 1988 (queries and concept learning).** The (store, context, query) frame is the query-learning frame; we add an exact version-space price per query and a certified white-box state readout.
- **Angluin 1980 (tell-tales, finite thickness).** The condition that would raise our consistency-convergence to target-identification; this is the named gap of M8, not a distinction in our favor.
- **Gold 1967; Case-Smith 1983; Freivalds-Smith 1993; de Brecht-Yamamoto 2010.** Identification in the limit, mind-change complexity, mind-change against Borel rank; cited as the home of M5, M8, M9, and re-sold as nothing.
- **Darwiche-Marquis 2002 (knowledge compilation map).** The store is a compiled query-answering artifact; we add the exact state-price and a certified per-step semantics.
- **Valiant 2000; Juba 2013; Michael 2010 (PAC-Semantics, implicit learning).** Answering queries from data with a certificate; ours is a certified version-space object with an exact price.
- **Necula 1997 (proof-carrying code); Alvarez-Melis-Jaakkola 2018 (self-explaining); Vovk et al. (conformal).** The answer-plus-certificate and white-box output; ours is a proved semantic homomorphism (M2), not a learned explanation or a coverage guarantee.
- **Tian-Pearl 2002 (c-component and Q-factorization).** Reconstruct a large SCM from small atoms; distinct only if search under a query at an exact price beats the fixed algorithm.
- **Shpitser-Pearl 2006 (ID and IDC); Huang-Valtorta 2006.** do-calculus completeness and the hedge; we would add a capacity and experiment price in version-space currency.
- **Bareinboim-Correa-Ibeling-Icard 2022 (Causal Hierarchy Theorem).** do-words as separating enlargements are generic non-collapse; ours is a relabeling unless tied to the exact price.
- **Brito-Pearl 2002 (bow); Verma-Pearl, Andersson-Madigan-Perlman (Markov equivalence).** The bow atom and observational-equivalence classes; the distinction is the price, not the atom.
- **Eberhardt-Glymour-Scheines; Hauser-Bühlmann (I-MEC, GIES); Shanmugam et al. 2015; Hyttinen-Eberhardt-Hoyer.** Active causal discovery and experiment design, the true home of M10; they bound intervention counts, we would price them exactly and certify the machine.
- **Anand-Ribeiro-Tian-Bareinboim 2023 (cluster DAGs).** Modular SCM identification from sub-structures, the compositional ancestor; the distinction is again the exact price.
