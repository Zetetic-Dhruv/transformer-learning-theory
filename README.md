# Transformer Learning Theory

**A formal laboratory for transformers — where the same network is at once a literal IEEE‑754 float32 program you can execute and a mathematical object you can prove hard learning‑theoretic theorems about in exact real arithmetic, with machine‑checked bridges carrying guarantees between the two.**

[![Documentation](https://img.shields.io/badge/docs-API%20reference-0b4f8b)](https://zetetic-dhruv.github.io/transformer-learning-theory/) [![Lean](https://img.shields.io/badge/Lean-v4.29.0-blue)](https://github.com/leanprover/lean4/releases/tag/v4.29.0) ![sorry 0](https://img.shields.io/badge/sorry-0-brightgreen) [![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

**Documentation (doc‑gen4 API reference):** [zetetic‑dhruv.github.io/transformer‑learning‑theory](https://zetetic-dhruv.github.io/transformer-learning-theory/)

Most theory about neural networks is written in ℝ and silently assumed to survive contact with float32 hardware; most empirical work runs in float32 and silently assumes the ℝ theory applies. This project removes the "silently": it puts both regimes inside one proof assistant, on one transformer object, and forces every claim that crosses between them to be a theorem.

It is built on the [formal‑learning‑theory‑kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel) (measurability infrastructure for statistical learning) and on [TorchLean](https://github.com/lean-dojo/TorchLean)'s executable neural‑network semantics, and it makes precise — and machine‑checks — the measurability assumptions that [Krapp–Wirth (2024)](https://arxiv.org/abs/2410.10243) identify as tacit in the Fundamental Theorem of Statistical Learning. Its measurability foundations are developed further in the companion paper, [*Null Measurability at the Symmetrization Interface in VC Learning*](https://arxiv.org/abs/2604.25028).

---

## Two regimes, one object

A single scaffold, `TransformerObject` (`Bridge/TransformerRoot`), packages TorchLean's `Spec.Transformer` parametrically in its numeric backend `α`. The *same* definition is read two ways:

| Backend | What it is | What you do with it |
|---|---|---|
| **`α = ℝ`** | exact real arithmetic | prove hard theorems — measurability, continuity, Lipschitz envelopes, learning‑theoretic risk bounds |
| **`α = IEEE32Exec`** | bit‑exact binary32 | *execute* — the literal float32 forward pass, rounding and all, as a Lean computation you can run |

Properties are stated once and resolved against this one object through a proof‑carrying `Resolution` type that records each property as `discharged` (proved) or `refuted` (a witnessed counterexample). The transformer is not a diagram in a paper — it is a thing in the kernel that you can both run and reason about.

## The bridges (this is the point)

The two regimes are connected by **verified** transfer theorems, so a result in one becomes a result in the other:

- **`toReal` of the executed reduction `=` the rounded real model** (`Fp32Reduction.toReal_foldl_add`) — the literal float fold *is* the real‑valued rounding model, so error theorems about ℝ apply to the running float code.
- **The literal layer‑norm op‑tree `=` its coordinate model** (`LayerNormSpec.get2_layerNorm`) — TorchLean's actual `Spec.layerNorm` agrees coordinatewise with the analytic definition, so continuity/measurability proved on one transfers to the other.
- **Executed risk is envelope‑controlled** (`ExecutedForward.executed_risk_transfer`, `ForwardEnvelope.execComp_risk_transfer`) — under a rounding envelope and a Lipschitz loss, the float32 expected risk is within `L·ε` of the ideal.

A theorem proved in ℝ thus *converts into a float32‑executable insight*; a float32 experiment can in turn *falsify or motivate* a theorem. That loop is the laboratory.

---

## Open questions the laboratory is built to attack

The program targets *stated, citable* open problems at the seam between learning theory and numerical execution. Each is matched to a machine‑checked foundation already in the kernel — concrete traction, not just an interest.

**Is statistical learnability decidable, and where is it even measurable?** Ben‑David, Hrubeš, Moran, Shpilka and Yehudayoff proved in *Nature Machine Intelligence* that "learnability can be undecidable" — general (EMX) learnability is independent of ZFC [[Ben‑David et al. 2019]](https://doi.org/10.1038/s42256-018-0002-3) — and Krapp–Wirth showed the Fundamental Theorem of Statistical Learning holds only under measurability assumptions usually left tacit [[Krapp–Wirth 2024]](https://arxiv.org/abs/2410.10243). *Traction here:* the kernel machine‑checks exactly where attention‑based learning stays measurable (the σ‑compact, finite‑dimensional regime) and exhibits a concrete architecture whose uniform‑convergence bad event leaves the Borel σ‑algebra (`attention_measurability_dichotomy`, `attention_architecture_produces_non_borel_bad_event`); the analysis is carried further in the companion paper [[Gupta 2026]](https://arxiv.org/abs/2604.25028).

**Does low numerical precision preserve learnability?** Surveys of low‑precision training note that convergence guarantees "suffer from dimension‑dependent bounds" and that provable accuracy outside convex settings is open [[Hao et al. 2025]](https://arxiv.org/abs/2505.01043). *Traction here:* the kernel carries a *bit‑exact* float32 forward pass together with a machine‑checked envelope `|R_exec − R_ideal| ≤ L·envBound`, with `envBound` a closed form in the weights (`executed_risk_transfer`, `fp32FoldlErrorBudget_closed_form`, `execComp_risk_transfer`).

**What is the Lipschitz constant of self‑attention?** Kim, Papamakarios and Mnih proved standard dot‑product self‑attention "is not Lipschitz for unbounded input domain" [[Kim et al. 2021]](https://arxiv.org/abs/2006.04710); tight, certified constants remain open. *Traction here:* the kernel now carries a **constructive on‑domain constant** — single‑query attention moves by at most `2·nK·bV·(dB/scale)·(‖ΔQ‖+‖ΔK‖) + ‖ΔV‖` on `‖Q‖,‖K‖ ≤ B` (`attnOut_lipschitz_on_ball`), with the non‑Lipschitzness isolated entirely to the bilinear score map and the softmax mixing globally Lipschitz — and it turns the Kim et al. boundary into a *layer instance*: although self‑attention has no global constant, it is a genuine certificate‑side `ExecLayer` over the metric subtype `↥(closedBall 0 B)` (`selfAttnExecLayer`, via `execLayerOfForwardInvariant`), the bounded‑input cap carried by the type. Together with the linear/ReLU operator‑norm constants (`matMulSpecExecLayer`, `reluSpecExecLayer`) and the global layer‑norm constant (`layerNormCoord_lipschitz`), these are the assembled building blocks of a certified network constant.

The kernel proves the singleton‑class uniform‑convergence bad event is Borel over *any* σ‑compact parameter space (`Tame.singletonBadEvent_measurable_of_sigmaCompact`), and now **instantiates this end‑to‑end on the concrete transformer object**: for every `RealTransformer T`, the bad event of its scaled‑dot‑product attention scoring — taken over `T`'s *actual* key‑parameter space `Fin nK → Fin cfg.embedDim → ℝ`, which is finite‑dimensional hence σ‑compact, with `T`'s continuous score — is Borel (`transformerAttentionBadEvent_borel`, a discharged `Resolution`; axiom‑clean and unconditional). So "a finite transformer is on the tame side of the measurability boundary" is a theorem about the concrete transformer, not a prose step.

---

## Foundations already in place

Everything below is machine‑checked. It is organized by idea, not by file.

### 1 · The execution bridge — measurable though discontinuous

The executed forward, read over real coordinates, is a step function — discontinuous on the rounding‑cell boundaries — yet **measurable**, because IEEE round‑to‑nearest decomposes into measurable atoms (base‑2 magnitude `⌊log₂⌋`, canonical exponent, base power, round‑to‑nearest‑even) with no appeal to continuity. Measurability is what makes expected risk a well‑defined integral, so it is the property the learning theory actually needs.

| Result | Module | What it says |
|---|---|---|
| `measurable_fp32Round` · `transformerForwardMap_executed_measurable` | `Bridge/ExecutedForward` | IEEE round‑to‑nearest, and hence the whole executed forward, is measurable |
| `executed_risk_transfer` | `Bridge/ExecutedForward` | under a rounding envelope and an `L`‑Lipschitz loss, executed risk is within `L·ε` of ideal |
| `get2_layerNorm` · `measurable_matCoords_layerNorm` · `continuous_matCoords_layerNorm` | `Bridge/LayerNormSpec` | the literal `Spec.layerNorm` — the layer normalization of [[Ba et al. 2016]](https://arxiv.org/abs/1607.06450) — equals its coordinate model; measurable for all `ε ≥ 0`, continuous for `ε > 0` |

### 2 · The float error theory — from one rounding step to a closed form

A self‑contained account of binary32 summation error, from the per‑step relative bound up to a backward‑error closed form, bound to the *literal* executed reduction.

| Result | Module | What it says |
|---|---|---|
| `neuralUlp_le_rel_on_normal` · `fp32Sum_error_le` | `Bridge/FP32Channel` | the relative‑error channel and the normal‑range summation enclosure — the standard model of [[Higham 2002]](https://doi.org/10.1137/1.9780898718027) (§2.2, §4.2) |
| `fp32FoldlErrorBudget_closed_form` | `Bridge/Fp32Reduction` | the backward‑error bound `≤ u·(n·|acc| + (n+1)·Σ|xᵢ|)/(1 − n·u)` — the classical γₙ recursive‑summation bound [[Higham 2002]](https://doi.org/10.1137/1.9780898718027) (§4.2) |
| `ie32_foldl_closed_envelope` | `Bridge/Fp32Reduction` | the executed `IEEE32Exec` reduction sits inside that closed‑form envelope |
| `layerNorm_cancellation_secondOrder` · `cancellation_term_zero_of_exact` | `Boundary/CancellationRepair` | mean‑centering demotes the naive‑variance cancellation to second order, with the 2‑adic exactness refinement of Sterbenz (1974), Thm 4.3.1 |

### 3 · The network rounding envelope — composing error through the forward pass

Per‑layer data — an ideal Lipschitz constant `Λ` and a uniform local rounding bound `δ` — composes through the standard error recurrence to a network‑level envelope, then into the risk machinery. The backbone is substrate‑independent; the instances make it concrete on real ops.

| Result | Module | What it says |
|---|---|---|
| `execComp_envelope` | `Bridge/ForwardEnvelope` | the network envelope `∀x, dist(executed, ideal) ≤ envBound` — per‑layer rounding budgets amplified by downstream Lipschitz products |
| `execComp_risk_transfer` · `executed_risk_transfer` | `Bridge/ForwardEnvelope`, `Bridge/ExecutedForward` | **the executed‑risk certificate** — for an `L`‑Lipschitz loss, `\|R_exec − R_ideal\| ≤ L·envBound`, with `envBound` a closed form in the weights |
| `reluExecLayer` · `linearExecLayer` | `Bridge/ExecLayerInstances` | ReLU (1‑Lipschitz, rounding‑free) and linear (operator‑norm Lipschitz) layers as `ExecLayer`s |
| `reluSpecExecLayer` · `matMulSpecExecLayer` | `Bridge/SpecExecLayers` | the **literal** TorchLean `reluSpec`/`matMulSpec`, read in coordinates, as `ExecLayer`s |

A structural fact discovered here: because fp32 error is *relative*, every arithmetic layer's uniform `δ` exists only on a bounded input domain — the same boundary that makes attention's Lipschitz constant domain‑dependent is universal across the arithmetic ops.

### 4 · The tameness boundary — where attention‑based learning stays measurable

The complementary pillar: a precise, machine‑checked characterization of *where* attention routing remains learning‑theoretically well‑behaved and where it does not. The boundary sits exactly at σ‑compactness of the parameter space.

| Result | Module | What it says |
|---|---|---|
| `route_measurable` · `top1_softmax_eq_argmax` | `Attention/BinaryRouting`, `Attention/FiniteRouting` | score‑comparison and `k`‑head argmax routing are jointly measurable; softmax top‑1 = argmax — over the scaled dot‑product attention of [[Vaswani et al. 2017]](https://arxiv.org/abs/1706.03762) |
| `attention_measurability_dichotomy` | `Boundary/Location` | over a σ‑compact parameter space the bad event is Borel; there is a Polish, non‑σ‑compact router whose bad event is **not** Borel — uniform in depth |
| `transformerAttentionBadEvent_borel` | `Bridge/TransformerAttention` | the tame side **instantiated on a concrete `RealTransformer`**: the bad event of its attention scoring over its actual finite‑dimensional key‑parameter space is Borel — a discharged `Resolution`, axiom‑clean and unconditional |
| `attention_architecture_produces_non_borel_bad_event` | `Strictness/NonBorelWitness` | an architecturally honest attention router with continuous scores over a Polish parameter space yields a non‑Borel bad event |
| `cascadeNonInvariance` · `universalRepair` · `cascadeBadEvent_measurableSet_iff` | `Boundary/Cascade`, `UniversalRepair`, `CascadeTame` | a mixture‑of‑experts cascade is analytic‑but‑not‑Borel at every depth, yet null‑measurable at every depth; Borel iff the base score range is |
| `soft_vs_hard_attention_separation` | `Bridge/SoftHardSeparation` | softmax attention's joint measurability makes its bad event Borel over *any* parameter space; argmax attention is well‑behaved over σ‑compact (e.g. finite‑dimensional) parameter spaces — `attentionRouting_wellBehaved`, `finiteCellRouter_wellBehaved` — but admits the non‑Borel witness over a non‑σ‑compact one. Softmax removes the pathology *unconditionally*; argmax removes it only on the tame side |
| `singletonClassOn_wellBehavedVCMeasTarget` | `Tame/SingletonWellBehaved` | the measurable‑target well‑behavedness of [[Krapp–Wirth 2024]](https://arxiv.org/abs/2410.10243) (Def. 3.2), discharged at the strict Borel level |

### 5 · The generalization bound — a certified, computable capacity‑and‑rounding budget

The capstone the laboratory is built toward: a high‑probability bound on the *executed* (float32) true risk in terms of the executed empirical risk plus a budget **computable from the actual weights** — `R_true^exec ≤ R̂_emp^exec + 2·(12√2·B/√m) + ε + 2·L·envBound`, where `B` is the affine Dudley entropy integral and `envBound` is §3's rounding envelope. Every term is determinate in the weight‑ball radius, the parameter‑Lipschitz constant, the dimension, the loss bound and the sample size. The capacity side is the optimal‑constant (`12√2`) Dudley chaining bound; the rounding side is the float32 envelope; the boundary is the input cap `K = {‖x‖ ≤ B}` that self‑attention's non‑global Lipschitzness forces — the same cap appearing as a hypothesis, not a patch.

| Result | Module | What it says |
|---|---|---|
| `certified_executed_generalization_dudley` | `Bridge/CertifiedTransformerBound` | the certified computable float32 bound — executed true risk ≤ executed empirical risk + closed capacity‑and‑rounding budget, except on a McDiarmid‑small sample event |
| `certified_executed_generalization_computable` | `Bridge/CertifiedCapacityBound` | the capstone with an abstract per‑sample capacity budget: the bounded‑differences concentration [[McDiarmid 1989]](https://doi.org/10.1017/9781107359949.008) composed with the executed‑risk certificate |
| `empiricalCapacityReal_le_computable` | `Capacity/CoveringDischarge` | the uniform Dudley capacity bound — the entropy integral [[Dudley 1967]](https://doi.org/10.1016/0022-1236(67)90017-1) discharged to a closed affine form via the Euclidean covering number, with the optimal `12√2` chaining constant |
| `layerNormCoord_lipschitz` | `Bridge/LayerNormLipschitz` | layer‑norm is globally `Cγ·(2√d+2)/√ε`‑Lipschitz — `σ = √(var+ε)` is globally `2`‑Lipschitz, so the `1/√ε` enters only through the final quotient (cf. self‑attention, which has no global constant) |
| `attnOut_lipschitz_on_ball` · `selfAttnExecLayer` | `Bridge/AttentionLipschitz`, `Bridge/BoundedExecLayer` | attention's on‑domain Lipschitz constant, and the bounded‑activation `ExecLayer` constructor (`execLayerOfForwardInvariant`) that makes self‑attention a certificate‑side layer over `↥(closedBall 0 B)` |
| `minimalFFN_certified_generalization` | `Bridge/MinimalFFNCertificate` | the bound instantiated on a two‑layer ReLU network `x ↦ W₂·relu(W₁·x)` |

The bound is *assembled* and axiom‑clean. Instantiating it end‑to‑end on the full `Spec.Transformer` — the per‑layer Lipschitz / forward‑invariance roster for every op over one bounded activation domain, then the TorchLean binding — is the active frontier.

---

## Using the laboratory

1. **Run a transformer.** Instantiate `TransformerObject` at `α = IEEE32Exec` and evaluate the forward pass — a literal float32 computation inside Lean, rounding included.
2. **Prove a property.** State it once against the object and discharge it (at `α = ℝ`) as a `Resolution`; a refutation is a witnessed counterexample, not a gap.
3. **Transfer.** Carry the result across the regimes with the bridge theorems (`get2_layerNorm`, `toReal_foldl_add`, `execComp_risk_transfer`) — an ℝ guarantee becomes an executable float32 certificate, and a float experiment becomes a target for proof.

## Status

- **Machine‑checked:** everything in *Foundations* above. The headline results (`transformerForwardMap_executed_measurable`, `executed_risk_transfer`, `get2_layerNorm`, `fp32FoldlErrorBudget_closed_form`, `ie32_foldl_closed_envelope`, `execComp_envelope`/`execComp_risk_transfer`, the generalization capstone `certified_executed_generalization_dudley`, and the Lipschitz constants `layerNormCoord_lipschitz` / `attnOut_lipschitz_on_ball` / `selfAttnExecLayer`) reduce to only `propext`, `Classical.choice`, `Quot.sound` — no `sorry`, no added axioms.
- **Two honesty caveats on that claim.** (i) The strictness/non‑Borel results (`attention_measurability_dichotomy`, `cascadeNonInvariance`, `soft_vs_hard_attention_separation`) are *conditional* theorems: they take the existence of an analytic non‑Borel subset of ℝ as an explicit hypothesis (a standard descriptive‑set‑theory fact), supplied as a theorem argument rather than re‑derived — so it is a hypothesis, not an axiom, but the results are conditional on it. (ii) The full build is green *locally*; the `Bridge/*` modules require the vendored TorchLean at a private local path and are therefore not CI‑buildable, so only the TorchLean‑independent measurability core can be independently green‑checked on CI.
- **Open (the questions above):** machine‑checking that reduced precision preserves learnability, and that the rounding envelope and capacity budget are non‑vacuous certificates against the statistical rate on a trained model.
- **In progress:** instantiating the assembled generalization capstone end‑to‑end on the full `Spec.Transformer` — discharging its `hlip` (value‑vector weight‑Lipschitz) and certificate‑side `ExecLayer` list by assembling every op (attention, layer‑norm, linear, ReLU, residual) over **one** bounded activation domain, with forward‑invariance re‑established by layer‑norm, then binding to the literal TorchLean forward. The Lipschitz‑constant atoms (layer‑norm, attention) are done; the per‑op domain‑composition roster and the binding are the remaining work.

## Build

```bash
lake build   # first build fetches Mathlib + the FLT kernel (~25 min clean)
```

Lean `v4.29.0` · Mathlib4 pinned to `8a17838` · FLT kernel from `main` · TorchLean integrated as a local‑path dependency (design‑lab vendored source).

> The TorchLean bridge requires the design‑lab vendored TorchLean at a local path, so the `Bridge/*` modules do not build standalone. The measurability foundations (pillar 4) are independent of the TorchLean bridge.

## Relationship to Krapp–Wirth and the FLT kernel

Krapp–Wirth identify the minimal measurability assumption tacit in the Fundamental Theorem of Statistical Learning — *well‑behavedness*, the measurability of the uniform‑convergence bad event. This repository makes that boundary precise for attention architectures and machine‑checks it: the σ‑compact side is exactly where their well‑behavedness holds, the non‑σ‑compact side is a concrete failure, and the o‑minimal "cells are Borel" lemma (their Lemma A.9) is realized for measurable scores in `Tame/FiniteCellRouter`. The kernel supplies the measurability algebra (`MeasurableBatchLearner`, the Borel–analytic bridge, amalgamation) these results are built on.

## References

Full BibTeX is in [`references.bib`](references.bib). A source is listed only where a theorem here *strictly* formalizes its stated result, or where a stated open problem is one the program attacks — no indirect or background citations.

**Strictly formalized in this repository**
- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM (2002) — unit roundoff (§2.2) and the γₙ recursive‑summation backward error (§4.2).
- P. H. Sterbenz, *Floating‑Point Computation*, Prentice‑Hall (1974) — the exact‑subtraction lemma (Thm 4.3.1).
- J. L. Ba, J. R. Kiros, G. E. Hinton, *Layer Normalization*, arXiv:[1607.06450](https://arxiv.org/abs/1607.06450) (2016).
- A. Vaswani et al., *Attention Is All You Need*, NeurIPS (2017), arXiv:[1706.03762](https://arxiv.org/abs/1706.03762).
- L. S. Krapp and L. Wirth, *Measurability in the Fundamental Theorem of Statistical Learning*, arXiv:[2410.10243](https://arxiv.org/abs/2410.10243) (2024) — well‑behavedness (Def. 3.2) and cells‑are‑Borel (Lemma A.9).
- R. M. Dudley, *The sizes of compact subsets of Hilbert space and continuity of Gaussian processes*, J. Funct. Anal. 1 (1967) — the metric‑entropy (chaining) bound on the suprema of the empirical process.
- C. McDiarmid, *On the method of bounded differences*, Surveys in Combinatorics, LMS Lecture Note Ser. 141 (1989) — the bounded‑differences concentration inequality.

**Open problems the program attacks**
- S. Ben‑David, P. Hrubeš, S. Moran, A. Shpilka, A. Yehudayoff, *Learnability can be undecidable*, Nature Machine Intelligence 1 (2019), [doi:10.1038/s42256‑018‑0002‑3](https://doi.org/10.1038/s42256-018-0002-3).
- Z. Hao et al., *Low‑Precision Training of Large Language Models: Methods, Challenges, and Opportunities*, arXiv:[2505.01043](https://arxiv.org/abs/2505.01043) (2025).
- H. Kim, G. Papamakarios, A. Mnih, *The Lipschitz Constant of Self‑Attention*, ICML (2021), arXiv:[2006.04710](https://arxiv.org/abs/2006.04710).

**Companion paper and software**
- D. Gupta, *Null Measurability at the Symmetrization Interface in VC Learning*, arXiv:[2604.25028](https://arxiv.org/abs/2604.25028) (2026).
- [TorchLean](https://github.com/lean-dojo/TorchLean) (lean‑dojo) — executable neural‑network semantics in Lean.
- [formal‑learning‑theory‑kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel) — the measurability infrastructure this repo depends on.
- [lean‑stat‑learning‑theory](https://github.com/YuanheZ/lean-stat-learning-theory) (Zhang–Lee–Liu) — the vendored optimal‑constant (`12√2`) Dudley entropy‑integral chaining used by the capacity bound.

## Citation

```bibtex
@software{gupta2026transformer,
  author       = {Gupta, Dhruv},
  title        = {Transformer Learning Theory},
  year         = {2026},
  url          = {https://github.com/Zetetic-Dhruv/transformer-learning-theory},
  license      = {Apache-2.0}
}
```

Or use the [CITATION.cff](CITATION.cff) file — GitHub generates an APA/BibTeX citation from it via the repo sidebar.

## License

Copyright (c) 2026 Dhruv Gupta. Licensed under the [Apache License 2.0](LICENSE).
