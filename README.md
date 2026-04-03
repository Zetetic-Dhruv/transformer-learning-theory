# Transformer Learning Theory

Lean4 formalization of measurability-theoretic foundations for transformer architectures. Builds on the [formal-learning-theory-kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel) measurability infrastructure.

## Architecture

This repo imports the FLT kernel as a dependency and applies its measurability framework (NullMeasurableSet, WellBehavedVCMeasTarget, MeasurableBatchLearner) to attention-based architectures.

```
formal-learning-theory-kernel (dependency)
  └── MeasurableBatchLearner, closure algebra, Borel-analytic bridge,
      amalgamation, interpolation descent

transformer-learning-theory (this repo)
  └── Attention routing measurability, softmax-argmax equivalence,
      parametric attention learners, compositional confidence theory
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
