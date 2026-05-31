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
      measurability dichotomy, Krapp–Wirth well-behavedness,
      mixture-of-experts routing cascade, TorchLean integration
      (real attention/softmax over IEEE floats, fp32 rounding channel,
      α-parametric transformer object with proof-carrying resolutions)
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

### Finite-Cell Argmax Partition

| Theorem | File | Result |
|---------|------|--------|
| `FiniteScoreRouterCode.routeCell_measurable` / `jointArgmaxCell_measurable` | Tame/FiniteCellRouter | Each argmax routing cell is Borel — a finite intersection of measurable score-inequalities; the Krapp–Wirth Lemma A.9 "every cell is Borel" realized for measurable scores |
| `FiniteScoreRouterCode.iUnion_routeCell` / `routeCell_disjoint` | Tame/FiniteCellRouter | The `k` argmax cells form a finite Borel partition of the input space — they cover it and are pairwise disjoint, and the router is constant on each cell |
| `FiniteScoreRouterCode.route_measurable_via_cells` | Tame/FiniteCellRouter | Joint route-measurability derived *from* the Borel cells — the §A.3 implication "finite union of Borel cells ⟹ measurable routing" |
| `finiteCellRouter_wellBehaved` | Tame/FiniteCellRouter | The finite-cell argmax router's patched class satisfies `WellBehavedVCMeasTarget`, closed *through* the explicit cell partition |

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

### Measurability Dichotomy

| Theorem | File | Result |
|---------|------|--------|
| `measurableSet_range_of_continuous_of_sigmaCompact` | Tame/SigmaCompactParam | Over a σ-compact parameter space, every continuous score map has a measurable *score range* (range reflection) |
| `singletonBadEvent_measurableSet_iff` | Tame/SingletonBadEventBorel | **Sharp characterization**: the singleton-class empirical-process bad event is Borel **iff** the underlying set is Borel |
| `singletonBadEvent_measurable_of_sigmaCompact` | Tame/SingletonBadEventBorel | Over a σ-compact parameter space the singleton bad event is Borel — the bad-event-level counterpart of the non-Borel witness; for finite-dimensional transformers the bad event is always Borel |
| `attention_measurability_dichotomy` | Boundary/Location | Conjoins three facts: over a σ-compact parameter space the score range is measurable **and** the bad event is Borel; there exists a Polish, non-σ-compact attention router with a non-Borel bad event; and a cascade conjunct that holds uniformly in depth. The boundary sits exactly at `SigmaCompactSpace` |

### Krapp–Wirth Well-Behavedness

| Theorem | File | Result |
|---------|------|--------|
| `singletonClass_oneSidedBadEvent_measurable` | Tame/SingletonWellBehaved | For a measurable set `A` and a measurable target `c`, the singleton-class empirical-process bad event is Borel at every sample size `m`, generalizing the `m=1`, zero-target slice |
| `singletonClassOn_wellBehavedVCMeasTarget` | Tame/SingletonWellBehaved | For `MeasurableSet A`, the singleton class satisfies Krapp–Wirth measurable-target well-behavedness (`WellBehavedVCMeasTarget`), discharged at the strict Borel level |

### Mixture-of-Experts Routing Cascade

| Theorem | File | Result |
|---------|------|--------|
| `witnessCascade` | Boundary/Cascade | A mixture-of-experts cascade — the witness's own quadratic-cost router, stacked as genuine two-head routing layers above the base (not a degenerate layer) |
| `cascadeBadEvent_eq_singletonBadEvent` | Boundary/Cascade | Per-input expert routing enlarges the realizable *class*, yet the `m=1` bad *event* collapses to the single-layer (singleton) bad event at *every* depth |
| `cascadeReductionInvariant` | Boundary/Cascade | The depth-`L` bad event is a continuous-surjection pullback of the planar witness, uniformly in depth |
| `cascadeNonInvariance` | Boundary/Cascade | At every routing depth `L`, the cascade bad event is analytic but **not** Borel — non-Borel uniformly in depth |
| `universalRepair` | Boundary/UniversalRepair | At every depth and for every finite measure, the cascade bad event is `NullMeasurableSet` (analytic ⇒ null-measurable) — the non-Borel set is nonetheless null-measurable at every depth |
| `cascadeBadEvent_measurableSet_iff` | Boundary/CascadeTame | The depth-`L` cascade bad event is Borel **iff** the base score range is Borel — the sharp dichotomy, uniform in depth (the tame counterpart of `cascadeNonInvariance`) |
| `cascadeBadEvent_measurable_of_sigmaCompact` | Boundary/CascadeTame | Over a σ-compact base parameter space the cascade bad event is Borel at every depth |

### TorchLean Integration

These results connect the measurability framework to [TorchLean](https://github.com/lean-dojo/TorchLean) (lean-dojo), a Lean formalization of neural networks — using TorchLean's *actual* attention scores (`Spec.dot`, the `Q Kᵀ` entry), softmax, and IEEE-float semantics. The two repos are reconciled onto one toolchain (`v4.29.0`, Mathlib `8a17838`); TorchLean is required as a local-path dependency on the design-lab vendored source.

A common scaffold `TransformerObject` (Bridge/TransformerRoot) packages TorchLean's `Spec.Transformer` parametrically in the numeric backend — one object serving both `ℝ` (learning theory) and `IEEE32Exec` (binary32 execution) — together with a proof-carrying `Resolution` type that records each property proved (`discharged`) or refuted (`refuted`) about it. Properties of a transformer are then stated and resolved against this single object.

| Theorem | File | Result |
|---------|------|--------|
| `attentionRouting_wellBehaved` | Bridge/TorchLeanAttention | The argmax router scored by TorchLean's actual `Spec.dot` satisfies `WellBehavedVCMeasTarget` |
| `softAttention_wellBehaved` | Bridge/SoftAttention | The real softmax-weighted attention output `∑ᵢ softmax(⟨x,Kᵢ⟩)ᵢ·Vᵢ`, thresholded, gives a well-behaved concept class — beyond the argmax idealization (all prior results are argmax/top-1) |
| `soft_vs_hard_attention_separation` | Bridge/SoftHardSeparation | Soft (softmax) attention is *unconditionally* well-behaved, while hard (argmax) attention admits a non-Borel witness — softmax removes the measurability pathology argmax can exhibit |
| `neuralUlp_le_rel_on_normal` | Bridge/FP32Channel | On the normal range (`mag x ≥ −125`), binary32's unit-in-the-last-place satisfies `ulp(x) ≤ 2⁻²³·|x|` — the relative-error foundation for the IEEE-`Float32`/ℝ rounding-error channel |
| `fp32Sum_error_le` | Bridge/FP32Channel | On the binary32 normal range, the round-to-nearest fold sum differs from the exact sum by at most an accumulated relative-error budget — a self-contained summation enclosure for the rounding channel |
| `transformerAttention_wellBehaved` | Bridge/TransformerAttention | The scaled-dot-product attention routing at a real transformer's embedding dimension is well-behaved, recorded as a discharged `Resolution` of the `TransformerObject` |

## Build

```bash
lake build   # First build fetches Mathlib + FLT kernel (~25 min clean)
```

Lean `v4.29.0` | Mathlib4 pinned to `8a17838` | FLT kernel from `main` | TorchLean integrated as a local-path dependency (design-lab vendored source)

> The TorchLean-integration branch reconciles this repo's toolchain with TorchLean's (`v4.29.0`, Mathlib `8a17838`). It requires the design-lab vendored TorchLean at a local path, so it does not build standalone; the core results above are independent of the TorchLean bridge.

## Roadmap

- [ ] MeasurableConfidenceLearner typeclass
- [ ] Compositional calibration bounds
- [ ] NullMeasurable necessity for confidence under composition
- [ ] Mixture-of-experts routing efficiency bounds
- [ ] Conformal prediction integration

## References

- L. S. Krapp and L. Wirth, *Measurability in the Fundamental Theorem of Statistical Learning* (with an appendix by L. Wirth), arXiv:[2410.10243](https://arxiv.org/abs/2410.10243) (2024). Identifies the minimal measurability assumptions tacit in the Fundamental Theorem of Statistical Learning — their *well-behavedness*, i.e. measurability of the uniform-convergence bad event. The measurability dichotomy here makes that boundary precise and machine-checks it: the σ-compact side is exactly where their well-behavedness holds; the non-σ-compact side is a concrete instance where it fails. The σ-compact and `FiniteCellScoreRouter` proofs are grounded in their well-behavedness conditions (§A.2) and o-minimal cells-are-Borel lemma (Lemma A.9).

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
