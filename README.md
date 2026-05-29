# Transformer Learning Theory

Lean4 formalization of measurability-theoretic foundations for transformer architectures. Builds on the [formal-learning-theory-kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel) measurability infrastructure. It makes precise — and machine-checks — the measurability assumptions that [Krapp–Wirth (2024)](https://arxiv.org/abs/2410.10243) identify as tacit in the Fundamental Theorem of Statistical Learning.

## Architecture

This repo imports the FLT kernel as a dependency and applies its measurability framework (NullMeasurableSet, WellBehavedVCMeasTarget, MeasurableBatchLearner) to attention-based architectures.

```
formal-learning-theory-kernel (dependency)
  └── MeasurableBatchLearner, closure algebra, Borel-analytic bridge,
      amalgamation, interpolation descent

transformer-learning-theory (this repo)
  └── Attention routing measurability, softmax-argmax equivalence,
      parametric attention learners, non-Borel strictness witness,
      measurability dichotomy, base-up MoE cascade (mixing-insensitivity)
```

## Current Results

### Attention Routing

| Theorem | File | Result |
|---------|------|--------|
| `BinaryAttentionRouterCode.route_measurable` | Attention/BinaryRouting | Binary score-comparison routing is jointly measurable |
| `attentionOfRouter_route_eq` | Attention/BinaryRouting | Every measurable Boolean router IS binary attention (universality) |
| `binaryAttentionPatch_wellBehaved` | Attention/BinaryRouting | Attention-patched concept classes satisfy WellBehavedVCMeasTarget |
| `sharedRouterAmalgClass_eq_patchRange` | Attention/BinaryRouting | Shared-router routing = amalgamation |

### Finite-Head Routing

| Theorem | File | Result |
|---------|------|--------|
| `FiniteScoreRouterCode.route_measurable` | Attention/FiniteRouting | k-head argmax routing is jointly measurable |
| `attentionOfFiniteRouter_route_eq` | Attention/FiniteRouting | Every measurable k-valued router IS argmax attention (universality) |
| `top1_softmax_eq_argmax` | Attention/FiniteRouting | Softmax top-1 = argmax (measurability equivalence) |
| `multiHeadArgmax_wellBehaved` | Attention/FiniteRouting | Multi-head argmax routing satisfies WellBehavedVCMeasTarget |
| `attention_requires_nullMeasurable` | Attention/FiniteRouting | NullMeasurable regime is necessary for attention |

### Parametric Attention Learners

| Theorem | File | Result |
|---------|------|--------|
| `ParametricLearnerFamily.instMeasurableBatchLearner` | Learner/AttentionLearner | Parametric learner families are MeasurableBatchLearner |
| `ParametricBinaryAttentionLearner.instMBL` | Learner/AttentionLearner | Binary attention learners are MeasurableBatchLearner |
| `ParametricFiniteHeadAttentionLearner.instMBL'` | Learner/AttentionLearner | k-head attention learners are MeasurableBatchLearner |

### Non-Borel Strictness Witness

| Theorem | File | Result |
|---------|------|--------|
| `quadraticCostRouter` | Strictness/NonBorelWitness | Witness `BinaryAttentionRouterCode ℝ` from a continuous parameterization `g : β → ℝ` of an analytic non-Borel set |
| `patchEval_class_eq_singletonClassOn` | Strictness/NonBorelWitness | The witness's patchEval class equals `singletonClassOn (range g)` |
| `witnessBadEventSet_not_measurable` | Strictness/NonBorelWitness | The witness's sample-space bad event is not Borel-measurable |
| `attention_architecture_produces_non_borel_bad_event` | Strictness/NonBorelWitness | Architecturally honest binary attention with continuous score functions over a Polish parameter space produces a non-Borel sample-space bad event |

### Measurability Dichotomy (P0_settle_debate)

| Theorem | File | Result |
|---------|------|--------|
| `measurableSet_range_of_continuous_of_sigmaCompact` | Tame/SigmaCompactParam | Over a σ-compact parameter space, every continuous score map has a measurable *score range* (range reflection) |
| `singletonBadEvent_measurableSet_iff` | Tame/SingletonBadEventBorel | **Sharp characterization**: the singleton-class empirical-process bad event is Borel **iff** the underlying set is Borel |
| `singletonBadEvent_measurable_of_sigmaCompact` | Tame/SingletonBadEventBorel | (tame) Over a σ-compact parameter space the singleton bad event is Borel — the bad-event-level tame counterpart of the wild witness; finite-dimensional transformers are measurability-free |
| `attention_measurability_dichotomy` | Boundary/Location | Conjoins (tame) σ-compact ⇒ measurable score range **and** Borel bad event, (wild) ∃ a Polish, non-σ-compact attention router with a non-Borel bad event, and a depth-uniform cascade leg. The boundary sits exactly at `SigmaCompactSpace` |

### Base-up MoE Cascade (P4_cascade)

| Theorem | File | Result |
|---------|------|--------|
| `witnessCascade` | Boundary/Cascade | A genuine base-up MoE cascade — the witness's own quadratic-cost router, stacked as real 2-head routing layers above the base (not a degenerate layer) |
| `cascadeBadEvent_eq_singletonBadEvent` | Boundary/Cascade | **Mixing-insensitivity**: per-input MoE routing enlarges the realizable *class*, yet the m=1 bad *event* collapses to the single-layer (singleton) bad event at *every* depth |
| `cascadeReductionInvariant` | Boundary/Cascade | The depth-`L` bad event is a continuous-surjection pullback of the planar witness, uniformly in depth |
| `cascadeNonInvariance` | Boundary/Cascade | At every routing depth `L`, the cascade bad event is analytic but **not** Borel — the wild side, depth-uniform |
| `universalRepair` | Boundary/UniversalRepair | At every depth and for every finite measure, the cascade bad event is `NullMeasurableSet` (analytic ⇒ null-measurable) — the pathology never escapes null-measurability |

## Build

```bash
lake build   # First build fetches Mathlib + FLT kernel (~25 min clean)
```

Lean `v4.29.0-rc6` | Mathlib4 pinned to `fde0cc5` | FLT kernel from `main`

## Roadmap

- [ ] MeasurableConfidenceLearner typeclass
- [ ] Compositional calibration bounds
- [ ] NullMeasurable necessity for confidence under composition
- [ ] MoE routing efficiency bounds
- [ ] Conformal prediction integration

## References

- L. S. Krapp and L. Wirth, *Measurability in the Fundamental Theorem of Statistical Learning* (with an appendix by L. Wirth), arXiv:[2410.10243](https://arxiv.org/abs/2410.10243) (2024). Identifies the minimal measurability assumptions tacit in the Fundamental Theorem of Statistical Learning — their *well-behavedness*, i.e. measurability of the uniform-convergence bad event. The measurability dichotomy here makes that boundary precise and machine-checks it: the tame side is exactly where their well-behavedness holds; the wild side is a concrete instance where it fails. The tame and `FiniteCellScoreRouter` proofs are grounded in their well-behavedness conditions (§A.2) and o-minimal cells-are-Borel lemma (Lemma A.9).

## Citation

If you use this work, please cite it:

```bibtex
@software{gupta2026transformer,
  author       = {Gupta, Dhruv},
  title        = {Transformer Learning Theory},
  year         = {2026},
  url          = {https://github.com/Zetetic-Dhruv/transformer-learning-theory},
  license      = {Apache-2.0}
}
```

Or use the [CITATION.cff](CITATION.cff) file — GitHub will automatically generate an "APA" and "BibTeX" citation from it via the repo sidebar.

## License

Copyright (c) 2026 Dhruv Gupta. Licensed under the [Apache License 2.0](LICENSE).
