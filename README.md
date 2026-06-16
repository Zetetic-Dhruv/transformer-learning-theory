# Transformer Learning Theory

A Lean 4 formalization of a **certified, computable generalization bound for a transformer attention model that holds for the IEEE binary32 program it actually runs**, together with a proof that the certified model is TorchLean's literal `scaledDotProductAttention`. The same network is read two ways: as exact real arithmetic (for the theorems) and as bit‑exact float32 (for execution), with machine‑checked bridges between them. The bound extends from the single attention head to a **depth‑`L` transformer stack** (the capacity constant grows with depth), and the certified attention is bound to the **literal `MultiHeadAttention.forward`** that TorchLean's `TransformerEncoderLayer` runs.

[![Documentation](https://img.shields.io/badge/docs-API%20reference-0b4f8b)](https://zetetic-dhruv.github.io/transformer-learning-theory/) [![Lean](https://img.shields.io/badge/Lean-v4.29.0-blue)](https://github.com/leanprover/lean4/releases/tag/v4.29.0) ![sorry 0](https://img.shields.io/badge/sorry-0-brightgreen) [![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

**Documentation (doc‑gen4 API reference):** [zetetic‑dhruv.github.io/transformer‑learning‑theory](https://zetetic-dhruv.github.io/transformer-learning-theory/)

## Main result

For an executed (IEEE binary32) attention head with a learnable value projection, except on a sample event of McDiarmid‑small probability,

```
R_true^exec  ≤  R̂_emp^exec  +  2·(12√2·B/√m)  +  ε  +  2·L·envBound
```

Every term is computable from the actual weights: `B` is the affine Dudley entropy integral (with the optimal `12√2` chaining constant), `envBound` is the float32 rounding envelope, and the input cap `K = {‖x‖ ≤ B}` is the hypothesis that self‑attention's lack of a global Lipschitz constant (Kim et al. 2021) forces. The bound is stated about the executed operation: the ideal map is proven equal, in coordinates, to TorchLean's literal `Spec.scaledDotProductAttention`, and the executed op enters through its rounding envelope. For the single attention head this is sharpened to the **literal kernel itself**. `attnHead_literal_certified_generalization` certifies TorchLean's `IEEE32Exec scaledDotProductAttention` read over ℝ, run on its finite fp32 input grid, with the rounding correction **derived**: the softmax, score, and value‑mix roundings composed down to a single named atom (the binary32 `exp` bound), with no input‑quantization slack.

`attnHead_executed_certified_generalization` · `attnHead_literal_certified_generalization` · `attnHead_certified_generalization` · `matCoords_scaledDotProductAttention`

All results reduce to only `propext`, `Classical.choice`, `Quot.sound`: no `sorry`, no added axioms. (The strictness/non‑Borel results below additionally take the existence of an analytic non‑Borel subset of ℝ as an explicit hypothesis, a standard descriptive‑set‑theory fact, supplied as an argument.)

## Results

### The generalization bound

| Result | Module | Statement |
|---|---|---|
| `attnHead_executed_certified_generalization` | `Bridge/Certificate/AttentionExecutedCertificate` | the certified bound **about the executed IEEE32 attention op**: its ideal is the literal `scaledDotProductAttention` (the binding), its `exec` the executed op, its rounding envelope `rnd` the float32 correction `2·Lℓ·rnd` |
| `attnHead_certified_generalization` | `Bridge/Certificate/AttentionTransformerCertificate` | the certified float32 bound, instantiated on a dot‑product attention head with a learnable value projection (the learnable weight is an attention weight, so the capacity term measures the attention class) |
| `certified_executed_generalization_dudley` | `Bridge/Certificate/CertifiedTransformerBound` | the abstract capstone: executed true risk ≤ executed empirical risk + closed capacity‑and‑rounding budget, off a McDiarmid‑small sample event |
| `matCoords_scaledDotProductAttention` | `Bridge/Spec/ScaledDotProductAttentionCorrespondence` | the certified head equals TorchLean's literal `Spec.scaledDotProductAttention`, read in coordinates |
| `multiHeadAttention_forward_one` | `Bridge/Spec/MultiHeadAttentionSingleHeadReduction` | TorchLean's literal `MultiHeadAttention.forward` (the op `TransformerEncoderLayer.forward` calls), at one head with identity projections, **is** a reshape of the certified `selfAttn`; the head‑split/combine reshape carries no pathology |
| `empiricalCapacityReal_le_computable` | `Capacity/Chaining/LipschitzCoveringDischarge` | the optimal‑constant (`12√2`) Dudley entropy‑integral capacity bound, discharged to a closed affine form via the Euclidean covering number |
| `minimalFFN_certified_generalization` | `Bridge/Certificate/MinimalFFNCertificate` | the bound instantiated on a two‑layer ReLU network `x ↦ W₂·relu(W₁·x)` |

### The literal float32 attention head

The sharpest form of the head bound: stated not about a real‑arithmetic model of the executed op but about TorchLean's **literal `IEEE32Exec scaledDotProductAttention`** read back over ℝ, with the rounding correction **derived** down to one conditionally‑discharged `exp` atom rather than supplied as data.

| Result | Module | Statement |
|---|---|---|
| `attnHead_literal_certified_generalization` | `Bridge/Certificate/AttentionLiteralExecutedBinding` | the certified float32 bound for the **literal** kernel `execAttnLit` (TorchLean's `IEEE32Exec scaledDotProductAttention`, read over ℝ), run on its finite fp32 input grid; the rounding correction `2·Lℓ·rndLit` is **derived**, not supplied |
| `attnHead_literal_certified_generalization_of_bundle` | `Bridge/Certificate/AttentionLiteralExecutedBinding` | the capstone with the **forward‑error premise discharged**: from the per‑input operating‑regime bundle `ExecAttnLitNormal` (finiteness of every intermediate, the denominator floor `Dlo`, the exp‑sum cap `E_lit`, channel normality) and the `exp`‑atom bound, the certificate holds with no `hfwd` hypothesis. `Dlo`/`E_lit` bound executed intermediates, so a numerical instantiation certifies them per input, a regime hypothesis, Higham‑standard |
| `attnLiteralForwardError` | `Bridge/Certificate/AttentionLiteralExecutedBinding` | the literal kernel is within the closed form `rndLit` of `attnHead` at the executed scale `1/√d`; the softmax, score, and value‑mix roundings are derived, leaving one **conditionally‑discharged** atom `δ_exp`. Its analytic content (Taylor remainder, Horner fixed‑point error, the log‑2 anchor, the IEEE round, the dyadic decode) is proven in `exec32_exp_error` / `ExpPolynomialError`, with only the main‑branch and range‑reduction code‑unfolding (`hbranch`/`hval`) outstanding |
| `gridExec_exec_close` · `gridExec_eq_kernel_of_mem` | `Bridge/Certificate/AttentionLiteralExecutedBinding` | `IEEE32Exec` is finite, so the fp32 input grid is finite: `gridExec` is the literal kernel on the grid and the ideal head off it, carrying the per‑input forward error with **no input‑quantization slack**; and on the grid, where the input law lives, `gridExec` *is* the kernel |
| `gridExec_ae_eq_kernel` | `Bridge/Certificate/AttentionLiteralExecutedBinding` | the grid‑support hypothesis made exact: under `P(regime) = 1`, `gridExec` equals the literal kernel `execAttnLit` **`P`‑almost‑everywhere**. Without it, an atomless `P` makes the finite regime `P`‑null and the bound degenerates to the ideal head plus slack; with it, the "program it runs" reading is exact |
| `genSoftmaxTV` | `Bridge/Fp32/GenSoftmaxForwardError` | the stabilized (max‑subtracted) float32 softmax is within a closed total‑variation bound of the exact softmax, the softmax leg of the derived forward error |

> **Scope.** Single head. The four depth‑stack capstones below still take per‑layer `rnd` as supplied
> data; lifting this literal forward error through the full block (layerNorm + multi‑head + residual, at
> depth) is the remaining fp32 node. The head bound is conditional on two explicit hypotheses: the
> per‑input operating‑regime bundle (`Dlo`/`E_lit` are bounds on executed intermediates, certified per
> input when instantiating numerically) and the conditionally‑discharged `exp` atom. Both are stated,
> neither a hidden error budget.

### The depth‑graded transformer stack

| Result | Module | Statement |
|---|---|---|
| `normAttnStack_certified_generalization` | `Bridge/Certificate/AttnStackCertificate` | the certified float32 bound for a depth‑`L` stack of post‑norm self‑attention blocks `layerNorm(X + selfAttn X)`; the capacity constant `lparamLipBound(replicate L block)` **grows with depth `L`** |
| `transformerEncoderStack_certified_generalization` | `Bridge/Certificate/TransformerStackCertificate` | the certified bound for a depth‑`L` stack of full encoder layers (attention block ∘ feed‑forward block, each layer‑norm‑terminated): the full transformer, depth‑graded |
| `normMultiHeadStack_certified_generalization` · `normMultiHeadStack_untied_certified_generalization` | `Bridge/Lipschitz/MultiHeadAttnCertificate` | the certified bound for a depth‑`L` stack of **true multi‑head** attention blocks `layerNorm(X + ∑_{h<H} headQK^h(X))`: distinct learnable query/key/value projections per head; capacity **linear in the head count `H`** and **sequence‑length‑free**. Stated both **weight‑tied** (universal‑transformer, `replicate`) and **untied** (standard transformer, `ofFn` of `L` distinct blocks reading disjoint parameter coordinates) |
| `transformerEncoderStackMH_certified_generalization` | `Bridge/Certificate/MultiHeadEncoderStack` | the same with the **interleaved feed‑forward block**: the full true‑multi‑head encoder layer (multi‑head attention block ∘ FFN block), depth‑graded |
| `multiHeadAttn_weight_lip` · `multiHeadAttn_input_lip` | `Bridge/Lipschitz/MultiHeadAttnCertificate` | multi‑head attention is Lipschitz in its weights and input, the constant linear in `H`, no cross‑head interaction, no sequence‑length factor (Edelman et al. 2022, App. A.6; Trauger–Tewari 2024, §4.2) |
| `normMultiHeadStack_executed_at_depth` · `idealComp_clampExecLayer_cons` | `Bridge/Forward/ExecutedStackAtDepth` | the executed forward **at depth, discharged by construction**: `idealComp (clampExecLayer ρ :: Es) = lparamComp St θ ∘ clampCoord ρ` (pre‑clamped blocks + forward‑invariance drops the inner clamps), so the certified bound holds with the depth‑composed rounding envelope and no abstract `hagree` |
| `normAttnStack_weight_lip` · `transformerEncoderStack_weight_lip` | `Bridge/Certificate/AttnStackCertificate`, `Bridge/Certificate/TransformerStackCertificate` | the depth‑`L` stack is `lparamLipBound`‑Lipschitz in its weights on the forward‑invariant activation ball: the depth‑grading made a theorem |
| `ffnCoord_input_lipschitz` | `Bridge/Certificate/TransformerStackCertificate` | the feed‑forward block is *globally* `bW₁·bW₂`‑Lipschitz (no input cap, unlike self‑attention) |

> **Scope of the multi‑head stack capstones.** Heads are full‑width (head‑dim = model‑dim `d`), so
> standard split‑head attention (head‑dim `d/H`) is the rank‑restricted subfamily, covered, at the
> full‑width constant. The executed forward **at depth is discharged by construction** for **all four**
> stacks (tied + untied multi‑head, FFN‑union encoder): given float32 executed layers `Es` whose
> per‑layer ideals are the **pre‑clamped** blocks, `Ls = clampExecLayer ρ :: Es` has
> `idealComp Ls = lparamComp St θ ∘ clampCoord ρ`, the bridge `idealComp_clampExecLayer_cons`, a
> forward‑invariance induction dropping the inner clamps, so each McDiarmid bound holds with the
> **depth‑composed** rounding envelope `envBound Ls` and **no abstract `hagree`**, and
> `executedForward_envelope_at_depth` bounds the IEEE‑binary32 forward by `envBound` of the clamped spec
> stack at depth. The per‑layer `rnd` is supplied as data (as the single‑layer executed certificate
> does); the **single attention head's** literal fp32 forward error is now **derived** (`attnLiteralForwardError`, in *The literal float32 attention head* above), and the lift through the full block is **done at the block level**: the feed‑forward block is bound to the literal `Spec.FeedForward.forward` at `IEEE32Exec` (`ffnLiteral_forward_error`, `Bridge/Certificate/FFNLiteralExecutedBinding`), and both residual+LayerNorm block carriers are built as `Es`‑ready `ExecLayer`s (`mhBlockRootExecLayer` / `ffnBlockRootExecLayer`, `Bridge/Certificate/{MH,FFN}BlockRootBinding`), each within a closed forward error of its ideal block. The LayerNorm enters as a **faithful executed ℝ‑model** on the genuine fp32 mean/std `Vexec` reductions, with a fully floor‑driven budget (`lnStarExec_residual_budget`, `Bridge/Certificate/LNBudgetDischarge`): no abstract LayerNorm slot.
>
> **Literal LayerNorm: done.** `toReal∘Spec.layerNorm` now binds op‑by‑op, the same idiom as the
> attention and feed‑forward sub‑layers. `get2_layerNorm_litAffine` (`Bridge/Certificate/LayerNormLiteralExecutedBinding`)
> reads the output coordinate `[i,j]` of `Spec.layerNorm` at `IEEE32Exec` as exactly the executed affine
> `((x − mean)/std · γ + β)` of the literal per‑row mean/std, through the shipped `_ie` coordinate
> reductions (`subSpec`/`divSpec`/`mulSpec` + the two broadcasts); the `reduceMean`/`reduceVar` reductions
> enter as opaque per‑row scalars (no general‑axis unfolding), their rounding the `ρm`/`ρs` budget
> `lnExec_forward_error` already carries. `toReal_layerNorm_forward_error` bounds it against the ℝ‑model
> `layerNormCoord`, reusing `lnExec_forward_error` verbatim: no new error machinery, with the per‑op affine
> rounding the explicit `δ` regime (dischargeable from the read equation and the shipped `toReal_sub`/`div`/`mul`/`add`
> atoms). **All three sub‑layers (attention, FFN, LayerNorm) are bound to their literal `Spec` ops.** The
> named concrete‑capstone bundle plugging both block carriers into the depth‑`L` Dudley generalization bound
> is `litMHEncoderStack_literal_certified_generalization` (`Bridge/Certificate/LiteralStackCertConcrete`).
>
> **Depth dependence of the envelope.** The generic `envBound` amplifies each layer's rounding by the
> product of the downstream ideal Lipschitz constants, which is **exponential in depth** when the
> per‑layer constant exceeds `1`, and layer normalization's `1/√ε` makes it exceed `1` for typical
> regularizers `ε`. `execComp_envelope_linear` (`Bridge/Forward/NonExpansiveDepthEnvelope`) isolates the sharp
> condition that removes this: on a **non‑expansive** stack (every `lip ≤ 1`) the envelope is at most
> `(#layers)·ρ`, **linear** in depth, and the executed bound is non‑vacuous at every depth.
> `normMultiHeadBlock_nonexpansive` identifies the regime in which the post‑norm block satisfies
> `lip ≤ 1`: `Cγ(2√d+2)/√ε·(1+L_mha) ≤ 1`, achieved by small `‖γ‖`, residual scaling, or large `ε`,
> the stabilization studied for deep transformers (Wang et al., *DeepNet*, 2022; signal‑propagation
> analyses). Outside that regime the linear bound does not apply: non‑vacuity at depth is **conditional**
> on certified non‑expansiveness, not automatic. The per‑layer scale is pinned by the post‑norm output
> cap: `normMultiHeadBlock_image_le` bounds the block image by `R = √d·Cγ + Cβ` uniformly in the input,
> so a relatively‑rounded executed block (`dist(exec, ideal) ≤ u·‖ideal‖`, `u` the unit roundoff) has
> per‑layer rounding `≤ u·R` and the depth‑`L` envelope is `≤ L·u·R` (`replicate_boundedRelRound_envelope`):
> machine‑epsilon × depth. The relative‑rounding `u` is still supplied as a hypothesis; deriving it
> (and the exact per‑operation `γₙ` telescoping) is the remaining concrete fp32 node.

### The Lipschitz constant of self‑attention

| Result | Module | Statement |
|---|---|---|
| `attnOut_lipschitz_on_ball` | `Bridge/Lipschitz/AttentionLipschitzOnBall` | attention moves by `≤ 2·bV·(dB/scale)·(‖ΔQ‖+‖ΔK‖) + ‖ΔV‖` on `‖Q‖,‖K‖ ≤ B`: **sequence‑length‑free** (softmax rows are probability vectors, so the absolute softmax‑Jacobian constant is `2`, matching Edelman et al. 2022, Cor. A.7); no global constant exists (Kim et al. 2021) |
| `selfAttnExecLayer` · `execLayerOfForwardInvariant` | `Bridge/Forward/BoundedExecLayer` | self‑attention as a certificate‑side `ExecLayer` over the metric subtype `↥(closedBall 0 B)`: the input cap carried by the type |
| `layerNormCoord_lipschitz` | `Bridge/Lipschitz/LayerNormLipschitz` | layer normalization is globally `Cγ·(2√d+2)/√ε`‑Lipschitz |
| `matMulSpecExecLayer` · `reluSpecExecLayer` | `Bridge/Spec/ReluMatMulExecLayers` | the literal `matMulSpec`/`reluSpec`, in coordinates, as operator‑norm Lipschitz `ExecLayer`s |

### Float32 execution

| Result | Module | Statement |
|---|---|---|
| `transformerForwardMap_executed_measurable` | `Bridge/Forward/ExecutedForward` | IEEE round‑to‑nearest, and the whole executed forward, is measurable |
| `executed_risk_transfer` · `execComp_risk_transfer` | `Bridge/Forward/ExecutedForward`, `Bridge/Forward/ForwardEnvelope` | for an `L`‑Lipschitz loss, `|R_exec − R_ideal| ≤ L·envBound`, with `envBound` a closed form in the weights |
| `execComp_envelope_linear` · `execComp_risk_transfer_linear` | `Bridge/Forward/NonExpansiveDepthEnvelope` | when every layer is **non‑expansive** (`lip ≤ 1`) with uniform per‑layer rounding `ρ`, the envelope is `≤ (#layers)·ρ`: **linear, not exponential, in depth** (the amplifying `∏ lip` collapses to a sum); the sharp condition removing the depth blow‑up |
| `normMultiHeadBlock_nonexpansive` | `Bridge/Forward/NonExpansiveDepthEnvelope` | the post‑norm multi‑head block contracts (`lip ≤ 1`) exactly when `Cγ(2√d+2)/√ε·(1+L_mha) ≤ 1`: the certified‑non‑expansive regime (small `‖γ‖` / residual scaling / large `ε`) under which the linear‑in‑depth envelope applies |
| `replicate_boundedRelRound_envelope` · `normMultiHeadBlock_image_le` | `Bridge/Forward/NonExpansiveDepthEnvelope` | with the **post‑norm output cap** `‖block X‖ ≤ √d·Cγ + Cβ` (layer‑norm bounds the signal uniformly in the input), a relatively‑rounded (`u` = unit roundoff) non‑expansive depth‑`L` block stack has forward error `≤ L·u·(√d·Cγ + Cβ)`: **machine‑epsilon × depth**, non‑vacuous for any realistic `L ≲ 1/(u·R)` |
| `fp32FoldlErrorBudget_closed_form` · `ie32_foldl_closed_envelope` | `Bridge/Fp32/SequentialSummationBackwardError` | the γₙ recursive‑summation backward‑error bound, and the IEEE32 reduction sitting inside it |
| `fp32Foldl_error_le_of_sum_bound` | `Bridge/Fp32/ClampedReductionRounding` | on the clamp (`∑ᵢ\|xᵢ\| ≤ S`), the fp32 reduction is within `u·(n+1)·S/(1−nu)` of the exact sum (`u=2⁻²⁴`): the **derived** (not supplied) rounding atom every block reduction (matMul / scores / value‑mix / layer‑norm mean & variance) reduces to; the three non‑reduction ops (`exp`, `sqrt`, `÷`) are supplied by the IEEE‑754 standard model |
| `get2_layerNorm` · `toReal_foldl_add` | `Bridge/Spec/LayerNormCorrespondence`, `Bridge/Fp32/SequentialSummationBackwardError` | TorchLean's literal `Spec.layerNorm` and the float fold equal their coordinate / rounding models |

### The measurability boundary

| Result | Module | Statement |
|---|---|---|
| `attention_router_measurability_dichotomy` | `Boundary/AttentionRouterMeasurabilityDichotomy` | the attention uniform‑convergence bad event is Borel over a σ‑compact parameter space, and non‑Borel over a Polish non‑σ‑compact one, uniformly in depth |
| `transformerAttentionBadEvent_borel` | `Bridge/Attention/TransformerAttentionWellBehaved` | for a concrete `RealTransformer`, the bad event of its attention scoring over its finite‑dimensional key‑parameter space is Borel |
| `cascadeNonInvariance` · `universalRepair` | `Boundary/BaseUpMoECascade`, `Boundary/CascadeNullMeasurable` | a mixture‑of‑experts cascade is analytic‑but‑not‑Borel at every depth, yet null‑measurable at every depth |
| `soft_vs_hard_attention_measurabilitySeparation` | `Bridge/Attention/SoftHardMeasurabilitySeparation` | softmax attention's bad event is Borel over any parameter space; argmax attention's only over σ‑compact ones |
| `singletonClassOn_wellBehavedVCMeasTarget` | `Tame/SingletonWellBehaved` | the measurable‑target well‑behavedness of Krapp–Wirth (2024, Def. 3.2), at the strict Borel level |

### The measurability cliff

The capstone of the measurability strand: a **strict** descriptive‑complexity drop located exactly at attention's softmax/argmax boundary, on the objects the library actually certifies.

| Result | Module | Statement |
|---|---|---|
| `measurabilityCliff` | `Boundary/MeasurabilityCliff` | **the cliff.** The library's most general transformer (the full multi‑head encoder stack) satisfies the strong **Borel ghost‑gap condition** (KW: the ghost‑gap supremum is measurable); the hard argmax MoE cascade strictly does *not*: **no** measurable function has its bad event as a `½`‑superlevel set, while it remains **learnable** (null‑measurable under every finite measure). The strict separation `KW ⊊ WB_meas`, located at the softmax/argmax boundary. The third conjunct is *proven* (a measurable supremum would Borel‑ify the bad event, contradicting `cascadeNonInvariance`), so the theorem is the strict separation itself |
| `transformerFunctional_isKW` | `Boundary/MeasurabilityCliff` | the **soft endpoint**: the general transformer weight‑functional `F` (continuous in the weights) has a measurable ghost‑gap supremum (KW) from the *same* `hFcont`/`hFmeas` the certified‑generalization framework discharges, so it covers `transformerEncoderStackMH` and every instance below it |
| `measurable_iSup_gap_of_continuous` | `Boundary/MeasurabilityCliff` | the **engine**: parameter‑continuity over a separable parameter space collapses the uncountable supremum to a countable dense one, so the supremum ghost‑gap is Borel; continuity alone, no σ‑compactness or measurable selection |
| `temperatureCliff` | `Boundary/TemperatureCliff` | the cliff made **concrete in the routing temperature**: for the non‑Borel witness, the soft (finite‑τ) margin ghost‑gap is measurable (Borel) while the argmax (τ = ∞) cascade is non‑Borel at every depth and null‑measurable, the argmax route identified as the softmax top‑1. Temperature is the toggle |
| `depthTemperatureCliff` | `Boundary/TemperatureCliffDepth` | the temperature cliff **depth‑uniform on the same tree object**: the soft cascade margin (softmax‑blending the subtree margins over the MoE tree parameter) is Borel at every depth `L`, while the argmax cascade over that same tree is non‑Borel; continuity‑of‑the‑blend ⊕ separability of the tree at every depth |

> **Non‑triviality.** The drop is a proved separation, and it is not a route‑measurability artifact: the routing is measurable; the non‑Borelness is the parameter *projection* (a Suslin operation), which does not preserve Borelness and so survives the closure of Borel functions under pointwise limits. It is well‑posed: analytic ⇒ universally measurable (Luzin), so the hard model stays learnable via the weakened symmetrization interface (Gupta, arXiv:2604.25028, Prop. 2.3). The cliff is a Borel→analytic complexity drop forced by the smooth‑to‑discrete argmax limit, the **temperature instance** of Gupta, arXiv:2604.25028, Theorem 4.1, located for the first time at attention's regularization boundary.

### Measurability is the certificate's precondition

The two strands meet. The executed generalization certificate carries a measurability hypothesis, and the cliff is exactly where it fails.

| Result | Module | Statement |
|---|---|---|
| `executedCertificate_precondition_satisfied_and_violated` | `Bridge/Certificate/MeasurabilityPrecondition` | measurability is the hinge: the executed (IEEE‑rounded) transformer forward **is** measurable (the certificate's `hFmeas` holds and the bound applies), while for the argmax cascade **no** measurable functional represents the bad event, so `hFmeas` is *unsatisfiable* there. The positive certificate and the negative cliff are the satisfied and the violated face of one assumption |

### The architecture design law

The certified capacity bound, indexed by the backend‑independent architecture shape `TransformerConfig` (four `Nat`s).

| Result | Module | Statement |
|---|---|---|
| `config_capacity_law` | `Bridge/Certificate/ConfigDesignLaw` | the capacity leg as a map **out of configuration space**: every `TransformerConfig` admits a certified generalization budget, the four architecture Nats flowing through the parameter‑perturbation envelope into the Dudley capacity term (the budget grows with depth and head count) |
| `TransformerDesignLaw` | `Bridge/Certificate/ConfigDesignLaw` | the design law at a config, assembled from its legs: capacity (`config_capacity_law`) ⊕ measurability (the spine) ⊕ **expressivity**, the config‑indexed expressivity lower bound, supplied as an *explicit open hypothesis*. The full law is two‑of‑three legs proved, with the expressivity floor the open obligation, now discharged for the constrained argmax‑routed model in *The expressivity hierarchy* below |

### The Tempered Design Law: two certificates on one routed‑symbol gap

A second design‑law strand (`TLT_Proofs/TemperedDesignLaw/`). A transformer router reads a discrete symbol, the `leastArgmax` route, from continuous attention scores, and is certified by **two complementary generalization certificates that bound the same gap**: a smooth (Dudley) certificate that is tighter at low routing sharpness `β`, and a hard (arrangement‑VC Sauer–Shelah) certificate that is tighter at high `β`, with an explicit crossover sharpness `βStar`. The capstone `temperedDesignLawCertificate` is an inhabited record assembled from the legs below, a value rather than a theorem about a record's shape, and `temperedDesignLawCertificate_real` carries the **real** Sauer generalization statistics of the literal attention router.

| Result | Module | Statement |
|---|---|---|
| `symbolClass_growth_prod` · `symbolClass_growth_uniform` | `TemperedDesignLaw/ArrangementVC` | the symbol channel's combinatorial capacity: the route comparison classes' growth function is bounded by the arrangement‑VC Sauer–Shelah product over the `k²` ordered score‑pairs, under a per‑pair finite‑dimensional linearity hypothesis |
| `temperedStack_smooth_cert` · `dudley_window_smoothWitness` | `TemperedDesignLaw/SmoothCertDischarge` | the smooth (Dudley) certificate for the depth‑`n` tempered stack, with the affine over‑bound that dominates the super‑affine Dudley constant on the certified `β`‑window |
| `symbolRoute_gen_gap` · `comparisonClass_gen_gap_sauer` | `TemperedDesignLaw/SymbolRouteGenGap`, `TemperedDesignLaw/SymbolChannelGenGap` | the hard arm: the symbol route's population generalization gap, bounded by the Sauer polynomial × Hoeffding, through the FLT Bool symmetrization step, which needs only that the class's concepts are measurable, not the discrete‑`X` cone |
| `temperedSymbol_expectedGap_hard_le` | `TemperedDesignLaw/GapIdentification` | the abstract `gap` bound to the family's **real** expected risk gap, so the certificate bounds the object it is meant to |
| `temperedDesignLawCertificate` · `temperedDesignLawCertificate_real` | `TemperedDesignLaw/CertificateAssembly`, `TemperedDesignLaw/CertificateReal` | the assembled certificate (capacity, numerical cone window, measurability cliff, hard‑tame legs) as a genuine inhabitant, and the form carrying the real Sauer statistics on the literal attention router, its measurability discharged through the achievable `WellBehavedVCMeasTarget`. The universal "finite VC + measurable hypotheses ⇒ well‑behaved" is **false** (refuted in the FLT kernel), so the measurable‑target predicate is the correct route, not a shortcut |
| `zeroOne_le_marginRamp` · `routeRampSurrogateLoss` | `TemperedDesignLaw/SurrogateBridge` | the margin‑ramp surrogate that puts both certificates on the **same 0‑1 route gap**: the 0‑1 routing loss is dominated by an output‑Lipschitz `RouteFactoredLoss` (the clamped Bartlett–Mendelson ramp, `Lℓ = 2/γ`), so the smooth certificate controls the discrete route channel the hard certificate bounds |
| `softRouteLossConcept_mem_routeLossClass` | `TemperedDesignLaw/SymbolRouteFactoredLoss` | the symbol‑channel soft↔hard bridge: at `β > 0` the soft top‑one route‑loss equals the hard route‑loss (the symbol channel does not see the temperature), so the hard bound certifies the soft symbol channel verbatim |
| `temperedDesignLawCertificate_binary` · `binaryExpressivityLadder` · `sauerEnvelope_pos` | `TemperedDesignLaw/MuxCertificate`, `TemperedDesignLaw/CertificateReal` | the certificate **type forces genuine content**: the hard-tame leg carries an `expressivity_strict` field (a proper depth inclusion `grade L L ⊂ grade (L+1) (L+1)`, which a collapsed grade cannot inhabit) and a `symbolBound_pos` field (a strictly positive statistical bound, so `symbolGap ≤ symbolBound` is never the trivial `0 ≤ 0`), each discharged at the binary carrier by the constrained-cascade depth ladder (`binCascadeGrade_ssubset_succ`) and the positive Sauer envelope (`sauerEnvelope_pos`); no inhabitant can be built with empty expressivity or zero statistical data |

> **Scope.** The certificate is **conditional**: it carries its genuinely‑external inputs as explicit hypotheses (the gap‑bound facts the capacity legs discharge, a classical non‑Borel base score range, and the hard‑arm statistical inputs) and is an inhabited record, not a shape theorem. Its expressivity and statistical legs are **type‑forced**: the record cannot be inhabited with a collapsed expressivity grade (the `expressivity_strict` field requires a proper `⊂`) or a zero statistical bound (the `symbolBound_pos` field requires `0 < symbolBound`), so the carried content is forced, not a permissive shape. Committing the smooth and hard sides to a single gap is the margin‑surrogate factorization, one design choice of factorization strength.

### The expressivity hierarchy: depth and width strictly buy expressivity

The expressivity floor the architecture design law leaves open, **proved for the constrained argmax‑routed mux‑cascade model** (`TLT_Proofs/TemperedDesignLaw/Mux*`). The unconstrained route lattice is first shown **degenerate**: a bare argmax router already realizes every measurable route function, so its grade is constant and any "separation" there is non‑measurable artifact rather than expressivity. Under the two‑part constraint, affine scores together with `n`‑way mux‑gated piecewise‑affine region maps, depth and width each **strictly** enlarge the realizable route class, at every level.

| Result | Module | Statement |
|---|---|---|
| `bareRouter_realizes_measurable` · `strict_separation_not_genuine` | `TemperedDesignLaw/ExpressivityDegeneracy` | **the degeneracy.** With unconstrained scores the depth‑0 router realizes every measurable route function, so on measurable functions the depth grades coincide and the unconstrained separation is not a genuine expressivity bound. This is why the constraint below is needed, and it sits exactly at the first‑order/second‑order boundary: affine scores are first‑order; arbitrary‑region scores are second‑order, and that is the collapse |
| `muxCascadeGrade` · `muxCascade_pieces_le_prod` | `TemperedDesignLaw/MuxHierarchy` | the constrained route grade (affine scores + mux‑gated affine branches) and its **region‑count bound**: a depth‑`L` cascade carves at most `∏ᵢ arityᵢ` maximal affine pieces. `linFun_mem_coordSpan` puts the score family in the *same* finite‑dimensional `W` as the capacity bound |
| `muxCascadeGrade_zero_ssubset_one` | `TemperedDesignLaw/MuxHierarchy` | the **base separation** `grade 0 ⊊ grade 1`: a non‑convex (XOR) route, realized at depth 1 by an explicit fold, is provably not a depth‑0 route, since depth‑0 route cells are convex power‑diagram cells and the XOR cell is not. A real non‑membership |
| `argmaxCell_convex` · `argmaxCell_eq_halfspaces` | `TemperedDesignLaw/ArgmaxPowerDiagram` | **the depth‑1 power‑diagram characterization** (the neurosymbolic argmax atom): for affine scores, each symbol cell `{x | leastArgmax (scores · x) = i}` is `Convex ℝ`, the exact intersection of the affine half‑spaces `score_i ≥ score_j` (all `j`) and `score_j < score_i` (for `j < i`). Single‑argmax routes realize exactly the convex power‑diagram (weighted Voronoi) partitions; non‑convex partitions such as XOR need depth `> 1`, the positive side of the base separation above |
| `binCascadeGrade_ssubset_succ` | `TemperedDesignLaw/MuxDepthLadderGeneral` | **the uniform depth hierarchy**: `grade L ⊊ grade (L+1)` for *every* `L` at fixed arity, so deeper strictly beats shallower at every rung. The witness is an iterated tent fold whose route has `2^{L+1}` alternations, exceeding the depth‑`L` bound of `2^{L+1} − 1` |
| `binCascadeGrade_ssubset_succ_dim` | `TemperedDesignLaw/MuxDepthSeparationDim` | **the depth hierarchy at the general carrier** `(Fin d → ℝ, Fin k)`, for every input dimension `d ≥ 1` and route count `k ≥ 2`: `grade L ⊊ grade (L+1)` for every `L`. The new ingredient is a `d`‑general line‑alternation bound (any `d`‑dimensional arity‑2 cascade restricted to a line alternates at most `2^{L+1} − 1` times, via one affine‑on‑the‑line bridge back to the 1‑D calculus); the lifted tent witness alternates `2^{L+1}` times. Threaded through `dimExpressivityLadder` / `temperedDesignLawCertificate_dim`, this closes the certificate's `expressivity_strict` at the full attention carrier, not only the binary case |
| `constArityGrade_ssubset_succ` | `TemperedDesignLaw/MuxWidth` | **the width hierarchy**: `arity n ⊊ arity (n+1)` for *every* `n` at fixed depth, so wider strictly beats narrower. The witness is an arity‑`(n+1)` fan whose route alternates `2n+1` times, exceeding the arity‑`n` bound of `2n − 1` |
| `affineArg_alternations_le` · `arg_win_ordConnected` | `TemperedDesignLaw/MuxDepthLadderGeneral` | the **1‑D linear‑region calculus** powering both separations: the `leastArgmax` of `n` affine functions of one real variable changes at most `n − 1` times, because each index wins on an interval (its strict‑win set is an intersection of affine half‑lines). The reusable engine |
| `quadraticArgmaxCell_not_convex` · `quadArg_alternations_le` | `TemperedDesignLaw/QuadraticExpressivity` | **the self-attention (low-rank bilinear) regime.** Full self-attention scores are quadratic (`xᵀ(QᵀK)x`); the picture splits. The convex power-diagram cells become **non-convex** semialgebraic cells (the power-diagram characterization is refuted, by an explicit cell `{x | x₀² ≤ x₁²}` that is not convex), while the region count **survives** as a Davenport-Schinzel order-2 bound: the argmax of `n` one-variable quadratics alternates `≤ 2n²` times, since each pairwise difference has `≤ 2` roots. `widthSeparation` is a real arity 1-vs-2 non-membership; the general-`n` separation is closed below via the tight order-2 Davenport-Schinzel bound `λ₂(n) ≤ 2n − 1` |
| `quadraticRouter_growth_prod` · `quadSpan` | `TemperedDesignLaw/QuadraticTameness` | **the tameness bridge: self-attention scores stay learnable.** The quadratic score-differences live in `quadSpan d`, the degree-≤2 monomial span (`finrank ≤ d² + d + 1`), so the affine arrangement-VC bound `symbolClass_growth_prod` applies verbatim with `W := quadSpan d`: the quadratic route class has finite VC. Tameness survives because polynomial scores are finite-dimensional; only non-polynomial (arbitrary) scores escape to infinite VC |
| `ds_order2_length_le` · `quadArg_alternations_le_tight` · `quadWidthGrade_ssubset_succ` | `TemperedDesignLaw/QuadraticWidth` | **the sharp self-attention width hierarchy** via order-2 Davenport-Schinzel (`λ₂(n) ≤ 2n − 1`, the tight bound, not in Mathlib). A sequence over `n` symbols with no immediate repeat and no `a,b,a,b` subsequence has length `≤ 2n − 1`; each pairwise quadratic difference has `≤ 2` roots, so the argmax envelope of `n` parabolas is no-`abab`, lifting the alternation cap from the crude `2n²` to the tight `2n − 2`. A fan of `n+1` parabolas (flat hub + `n` spikes) achieves `2n` alternations, exceeding the arity-`n` ceiling, so `quadWidthGrade n ⊊ quadWidthGrade (n+1)` for every `n`. The width hierarchy holds at general `n` under self-attention, with the sharp region count `2n − 1` (the quantitative upgrade of A3's "finite") |
| `quadRoute_alternations_le` · `seqChanges_blockRefine_le_two` · `quadDepthGrade_zero_ssubset_one` | `TemperedDesignLaw/QuadraticDepth` | **the self-attention depth bound + base rung** for quadratic-gated cascades (quadratic gate, affine branch). The per-layer order-2 switch (`λ₂` at arity 2: `≤ 2`) composes over depth via the new base-3 block-refine `seqChanges ≤ 3·u + 2`, giving the depth-`L` line bound `≤ 3^{L+1} − 1` at general `L` (the quadratic analogue of the affine `≤ 2^{L+1} − 1`). The base rung `quadDepthGrade 0 ⊊ quadDepthGrade 1` is a real `∉`: a depth-1 quadratic witness fires in the middle of a 3-point sample (alternates `2`), while depth-0 is the bare affine argmax (caps at `1`). The general-`L` depth witness needs an iterated ternary tent and is the named remaining step |

> **Scope.** Affine scores at carrier `ℝ` / `ℝᵈ` drive the hierarchy; the full self-attention (quadratic) regime is treated in `QuadraticExpressivity` / `QuadraticTameness` / `QuadraticWidth` / `QuadraticDepth`. All separations are real proved non-memberships, kernel-verified. The affine depth hierarchy holds at the general carrier `(Fin d → ℝ, Fin k)` for all `d ≥ 1`, `k ≥ 2`. Under full self-attention the convex power-diagram characterization is refuted, while the region count and finite-VC learnability both survive (polynomial scores are finite-dimensional). The general-`n` self-attention WIDTH separation is closed via the tight order-2 Davenport-Schinzel bound `λ₂(n) ≤ 2n − 1`; the depth-`L` line bound `≤ 3^{L+1} − 1` is proved at general `L`, with the base rung depth separation closed. Open and stated as such: the general-`L` depth separation (the depth-`L` bound + base rung are proved; an iterated-tent depth-`(L+1)` witness is the named remaining step), strict separation of the full any-arity grade with depth and arity varying together, and the full o-minimality-vs-tameness equivalence (the polynomial implies finite-dim implies tame direction is proved).

## Build

```bash
lake build   # first build fetches Mathlib + the FLT kernel (~25 min clean)
```

Lean `v4.29.0` · Mathlib4 pinned to `8a17838` · FLT kernel from `main` · TorchLean integrated as a local‑path dependency (design‑lab vendored source).

> The TorchLean bridge requires the design‑lab vendored TorchLean at a local path, so the `Bridge/*` modules do not build standalone. The measurability core (`Attention/*`, `Boundary/*`, `Tame/*`, `Strictness/*`) is independent of the TorchLean bridge.

## References

Full BibTeX is in [`references.bib`](references.bib). A source is listed only where a theorem here *strictly* formalizes its stated result, or where a stated open problem is one the program attacks.

**Strictly formalized in this repository**
- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM (2002): unit roundoff (§2.2) and the γₙ recursive‑summation backward error (§4.2).
- P. H. Sterbenz, *Floating‑Point Computation*, Prentice‑Hall (1974): the exact‑subtraction lemma (Thm 4.3.1).
- J. L. Ba, J. R. Kiros, G. E. Hinton, *Layer Normalization*, arXiv:[1607.06450](https://arxiv.org/abs/1607.06450) (2016).
- A. Vaswani et al., *Attention Is All You Need*, NeurIPS (2017), arXiv:[1706.03762](https://arxiv.org/abs/1706.03762).
- L. S. Krapp and L. Wirth, *Measurability in the Fundamental Theorem of Statistical Learning*, arXiv:[2410.10243](https://arxiv.org/abs/2410.10243) (2024): well‑behavedness (Def. 3.2) and cells‑are‑Borel (Lemma A.9).
- R. M. Dudley, *The sizes of compact subsets of Hilbert space and continuity of Gaussian processes*, J. Funct. Anal. 1 (1967): the metric‑entropy (chaining) bound.
- C. McDiarmid, *On the method of bounded differences*, Surveys in Combinatorics, LMS Lecture Note Ser. 141 (1989): the bounded‑differences concentration inequality.

**Open problems the program attacks**
- S. Ben‑David, P. Hrubeš, S. Moran, A. Shpilka, A. Yehudayoff, *Learnability can be undecidable*, Nature Machine Intelligence 1 (2019), [doi:10.1038/s42256‑018‑0002‑3](https://doi.org/10.1038/s42256-018-0002-3).
- Z. Hao et al., *Low‑Precision Training of Large Language Models*, arXiv:[2505.01043](https://arxiv.org/abs/2505.01043) (2025).
- H. Kim, G. Papamakarios, A. Mnih, *The Lipschitz Constant of Self‑Attention*, ICML (2021), arXiv:[2006.04710](https://arxiv.org/abs/2006.04710).

**Companion paper and software**
- D. Gupta, *Null Measurability at the Symmetrization Interface in VC Learning*, arXiv:[2604.25028](https://arxiv.org/abs/2604.25028) (2026).
- [TorchLean](https://github.com/lean-dojo/TorchLean) (lean‑dojo): executable neural‑network semantics in Lean.
- [formal‑learning‑theory‑kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel): the measurability infrastructure this repo depends on.
- [lean‑stat‑learning‑theory](https://github.com/YuanheZ/lean-stat-learning-theory) (Zhang–Lee–Liu): the vendored optimal‑constant (`12√2`) Dudley entropy‑integral chaining used by the capacity bound.

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

Or use the [CITATION.cff](CITATION.cff) file: GitHub generates an APA/BibTeX citation from it via the repo sidebar.

## License

Copyright (c) 2026 Dhruv Gupta. Licensed under the [Apache License 2.0](LICENSE).
