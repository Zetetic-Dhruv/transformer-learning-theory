# Transformer Learning Theory

A Lean 4 formalization of a **certified, computable generalization bound for a transformer attention model that holds for the IEEE binary32 program it actually runs** — together with a proof that the certified model is TorchLean's literal `scaledDotProductAttention`. The same network is read two ways: as exact real arithmetic (for the theorems) and as bit‑exact float32 (for execution), with machine‑checked bridges between them. The bound extends from the single attention head to a **depth‑`L` transformer stack** (the capacity constant grows with depth), and the certified attention is bound to the **literal `MultiHeadAttention.forward`** that TorchLean's `TransformerEncoderLayer` runs.

[![Documentation](https://img.shields.io/badge/docs-API%20reference-0b4f8b)](https://zetetic-dhruv.github.io/transformer-learning-theory/) [![Lean](https://img.shields.io/badge/Lean-v4.29.0-blue)](https://github.com/leanprover/lean4/releases/tag/v4.29.0) ![sorry 0](https://img.shields.io/badge/sorry-0-brightgreen) [![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

**Documentation (doc‑gen4 API reference):** [zetetic‑dhruv.github.io/transformer‑learning‑theory](https://zetetic-dhruv.github.io/transformer-learning-theory/)

## Main result

For an executed (IEEE binary32) attention head with a learnable value projection, except on a sample event of McDiarmid‑small probability,

```
R_true^exec  ≤  R̂_emp^exec  +  2·(12√2·B/√m)  +  ε  +  2·L·envBound
```

Every term is computable from the actual weights: `B` is the affine Dudley entropy integral (with the optimal `12√2` chaining constant), `envBound` is the float32 rounding envelope, and the input cap `K = {‖x‖ ≤ B}` is the hypothesis that self‑attention's lack of a global Lipschitz constant (Kim et al. 2021) forces. The bound is stated about the executed operation: the ideal map is proven equal — in coordinates — to TorchLean's literal `Spec.scaledDotProductAttention`, and the executed op enters through its rounding envelope.

`attnHead_executed_certified_generalization` · `attnHead_certified_generalization` · `matCoords_scaledDotProductAttention`

All results reduce to only `propext`, `Classical.choice`, `Quot.sound` — no `sorry`, no added axioms. (The strictness/non‑Borel results below additionally take the existence of an analytic non‑Borel subset of ℝ as an explicit hypothesis — a standard descriptive‑set‑theory fact, supplied as an argument.)

## Results

### The generalization bound

| Result | Module | Statement |
|---|---|---|
| `attnHead_executed_certified_generalization` | `Bridge/AttentionExecutedCertificate` | the certified bound **about the executed IEEE32 attention op**: its ideal is the literal `scaledDotProductAttention` (the binding), its `exec` the executed op, its rounding envelope `rnd` the float32 correction `2·Lℓ·rnd` |
| `attnHead_certified_generalization` | `Bridge/AttentionTransformerCertificate` | the certified float32 bound, instantiated on a dot‑product attention head with a learnable value projection (the learnable weight is an attention weight, so the capacity term measures the attention class) |
| `certified_executed_generalization_dudley` | `Bridge/CertifiedTransformerBound` | the abstract capstone: executed true risk ≤ executed empirical risk + closed capacity‑and‑rounding budget, off a McDiarmid‑small sample event |
| `matCoords_scaledDotProductAttention` | `Bridge/AttentionSpecBridge` | the certified head equals TorchLean's literal `Spec.scaledDotProductAttention`, read in coordinates |
| `multiHeadAttention_forward_one` | `Bridge/EncoderLayerSpecBridge` | TorchLean's literal `MultiHeadAttention.forward` (the op `TransformerEncoderLayer.forward` calls), at one head with identity projections, **is** a reshape of the certified `selfAttn` — the head‑split/combine reshape carries no pathology |
| `empiricalCapacityReal_le_computable` | `Capacity/CoveringDischarge` | the optimal‑constant (`12√2`) Dudley entropy‑integral capacity bound, discharged to a closed affine form via the Euclidean covering number |
| `minimalFFN_certified_generalization` | `Bridge/MinimalFFNCertificate` | the bound instantiated on a two‑layer ReLU network `x ↦ W₂·relu(W₁·x)` |

### The depth‑graded transformer stack

| Result | Module | Statement |
|---|---|---|
| `normAttnStack_certified_generalization` | `Bridge/AttnStackCertificate` | the certified float32 bound for a depth‑`L` stack of post‑norm self‑attention blocks `layerNorm(X + selfAttn X)`; the capacity constant `lparamLipBound(replicate L block)` **grows with depth `L`** |
| `transformerEncoderStack_certified_generalization` | `Bridge/TransformerStackCertificate` | the certified bound for a depth‑`L` stack of full encoder layers (attention block ∘ feed‑forward block, each layer‑norm‑terminated) — the full transformer, depth‑graded |
| `normAttnStack_weight_lip` · `transformerEncoderStack_weight_lip` | `Bridge/AttnStackCertificate`, `Bridge/TransformerStackCertificate` | the depth‑`L` stack is `lparamLipBound`‑Lipschitz in its weights on the forward‑invariant activation ball — the depth‑grading made a theorem |
| `ffnCoord_input_lipschitz` | `Bridge/TransformerStackCertificate` | the feed‑forward block is *globally* `bW₁·bW₂`‑Lipschitz (no input cap — unlike self‑attention) |

### The Lipschitz constant of self‑attention

| Result | Module | Statement |
|---|---|---|
| `attnOut_lipschitz_on_ball` | `Bridge/AttentionLipschitz` | attention moves by `≤ 2·nK·bV·(dB/scale)·(‖ΔQ‖+‖ΔK‖) + ‖ΔV‖` on `‖Q‖,‖K‖ ≤ B`; no global constant exists (Kim et al. 2021) |
| `selfAttnExecLayer` · `execLayerOfForwardInvariant` | `Bridge/BoundedExecLayer` | self‑attention as a certificate‑side `ExecLayer` over the metric subtype `↥(closedBall 0 B)` — the input cap carried by the type |
| `layerNormCoord_lipschitz` | `Bridge/LayerNormLipschitz` | layer normalization is globally `Cγ·(2√d+2)/√ε`‑Lipschitz |
| `matMulSpecExecLayer` · `reluSpecExecLayer` | `Bridge/SpecExecLayers` | the literal `matMulSpec`/`reluSpec`, in coordinates, as operator‑norm Lipschitz `ExecLayer`s |

### Float32 execution

| Result | Module | Statement |
|---|---|---|
| `transformerForwardMap_executed_measurable` | `Bridge/ExecutedForward` | IEEE round‑to‑nearest, and the whole executed forward, is measurable |
| `executed_risk_transfer` · `execComp_risk_transfer` | `Bridge/ExecutedForward`, `Bridge/ForwardEnvelope` | for an `L`‑Lipschitz loss, `|R_exec − R_ideal| ≤ L·envBound`, with `envBound` a closed form in the weights |
| `fp32FoldlErrorBudget_closed_form` · `ie32_foldl_closed_envelope` | `Bridge/Fp32Reduction` | the γₙ recursive‑summation backward‑error bound, and the IEEE32 reduction sitting inside it |
| `get2_layerNorm` · `toReal_foldl_add` | `Bridge/LayerNormSpec`, `Bridge/Fp32Reduction` | TorchLean's literal `Spec.layerNorm` and the float fold equal their coordinate / rounding models |

### The measurability boundary

| Result | Module | Statement |
|---|---|---|
| `attention_measurability_dichotomy` | `Boundary/Location` | the attention uniform‑convergence bad event is Borel over a σ‑compact parameter space, and non‑Borel over a Polish non‑σ‑compact one — uniformly in depth |
| `transformerAttentionBadEvent_borel` | `Bridge/TransformerAttention` | for a concrete `RealTransformer`, the bad event of its attention scoring over its finite‑dimensional key‑parameter space is Borel |
| `cascadeNonInvariance` · `universalRepair` | `Boundary/Cascade`, `Boundary/UniversalRepair` | a mixture‑of‑experts cascade is analytic‑but‑not‑Borel at every depth, yet null‑measurable at every depth |
| `soft_vs_hard_attention_separation` | `Bridge/SoftHardSeparation` | softmax attention's bad event is Borel over any parameter space; argmax attention's only over σ‑compact ones |
| `singletonClassOn_wellBehavedVCMeasTarget` | `Tame/SingletonWellBehaved` | the measurable‑target well‑behavedness of Krapp–Wirth (2024, Def. 3.2), at the strict Borel level |

## Build

```bash
lake build   # first build fetches Mathlib + the FLT kernel (~25 min clean)
```

Lean `v4.29.0` · Mathlib4 pinned to `8a17838` · FLT kernel from `main` · TorchLean integrated as a local‑path dependency (design‑lab vendored source).

> The TorchLean bridge requires the design‑lab vendored TorchLean at a local path, so the `Bridge/*` modules do not build standalone. The measurability core (`Attention/*`, `Boundary/*`, `Tame/*`, `Strictness/*`) is independent of the TorchLean bridge.

## References

Full BibTeX is in [`references.bib`](references.bib). A source is listed only where a theorem here *strictly* formalizes its stated result, or where a stated open problem is one the program attacks.

**Strictly formalized in this repository**
- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM (2002) — unit roundoff (§2.2) and the γₙ recursive‑summation backward error (§4.2).
- P. H. Sterbenz, *Floating‑Point Computation*, Prentice‑Hall (1974) — the exact‑subtraction lemma (Thm 4.3.1).
- J. L. Ba, J. R. Kiros, G. E. Hinton, *Layer Normalization*, arXiv:[1607.06450](https://arxiv.org/abs/1607.06450) (2016).
- A. Vaswani et al., *Attention Is All You Need*, NeurIPS (2017), arXiv:[1706.03762](https://arxiv.org/abs/1706.03762).
- L. S. Krapp and L. Wirth, *Measurability in the Fundamental Theorem of Statistical Learning*, arXiv:[2410.10243](https://arxiv.org/abs/2410.10243) (2024) — well‑behavedness (Def. 3.2) and cells‑are‑Borel (Lemma A.9).
- R. M. Dudley, *The sizes of compact subsets of Hilbert space and continuity of Gaussian processes*, J. Funct. Anal. 1 (1967) — the metric‑entropy (chaining) bound.
- C. McDiarmid, *On the method of bounded differences*, Surveys in Combinatorics, LMS Lecture Note Ser. 141 (1989) — the bounded‑differences concentration inequality.

**Open problems the program attacks**
- S. Ben‑David, P. Hrubeš, S. Moran, A. Shpilka, A. Yehudayoff, *Learnability can be undecidable*, Nature Machine Intelligence 1 (2019), [doi:10.1038/s42256‑018‑0002‑3](https://doi.org/10.1038/s42256-018-0002-3).
- Z. Hao et al., *Low‑Precision Training of Large Language Models*, arXiv:[2505.01043](https://arxiv.org/abs/2505.01043) (2025).
- H. Kim, G. Papamakarios, A. Mnih, *The Lipschitz Constant of Self‑Attention*, ICML (2021), arXiv:[2006.04710](https://arxiv.org/abs/2006.04710).

**Companion paper and software**
- D. Gupta, *Null Measurability at the Symmetrization Interface in VC Learning*, arXiv:[2604.25028](https://arxiv.org/abs/2604.25028) (2026).
- [TorchLean](https://github.com/lean-dojo/TorchLean) (lean‑dojo) — executable neural‑network semantics in Lean.
- [formal‑learning‑theory‑kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel) — the measurability infrastructure this repo depends on.
- [lean‑stat‑learning‑theory](https://github.com/YuanheZ/lean-stat-learning-theory) (Zhang–Lee–Liu) — the vendored optimal‑constant (`12√2`) Dudley entropy‑integral chaining used by the capacity bound.

## Citation

```bibtex
@software{gupta2026transformer,
  author  = {Gupta, Dhruv},
  title   = {Transformer Learning Theory},
  year    = {2026},
  url     = {https://github.com/Zetetic-Dhruv/transformer-learning-theory},
  license = {Apache-2.0}
}
```

Or use the [CITATION.cff](CITATION.cff) file — GitHub generates an APA/BibTeX citation from it via the repo sidebar.

## License

Copyright (c) 2026 Dhruv Gupta. Licensed under the [Apache License 2.0](LICENSE).
