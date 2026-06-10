import Lake
open Lake DSL

package TransformerLearningTheory where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib TLT_Proofs where
  roots := #[
    `TLT_Proofs.Boundary.AttentionRouterMeasurabilityDichotomy,
    `TLT_Proofs.Boundary.BaseUpMoECascade,
    `TLT_Proofs.Boundary.CascadeBorelDichotomy,
    `TLT_Proofs.Boundary.CascadeNullMeasurable,
    `TLT_Proofs.Boundary.MeasurabilityCliff,
    `TLT_Proofs.Boundary.TemperatureCliff,
    `TLT_Proofs.Boundary.TemperatureCliffDepth,
    `TLT_Proofs.Bridge.Attention.SoftAttentionWellBehaved,
    `TLT_Proofs.Bridge.Attention.SoftHardMeasurabilitySeparation,
    `TLT_Proofs.Bridge.Attention.TransformerAttentionWellBehaved,
    `TLT_Proofs.Bridge.Certificate.AttentionExecutedCertificate,
    `TLT_Proofs.Bridge.Certificate.AttentionLiteralExecutedBinding,
    `TLT_Proofs.Bridge.Certificate.AttentionTransformerCertificate,
    `TLT_Proofs.Bridge.Certificate.AttnStackCertificate,
    `TLT_Proofs.Bridge.Certificate.CertifiedCapacityBound,
    `TLT_Proofs.Bridge.Certificate.CertifiedRiskBound,
    `TLT_Proofs.Bridge.Certificate.CertifiedTransformerBound,
    `TLT_Proofs.Bridge.Certificate.ConfigDesignLaw,
    `TLT_Proofs.Bridge.Certificate.FFNBlockRootBinding,
    `TLT_Proofs.Bridge.Certificate.FFNLiteralExecutedBinding,
    `TLT_Proofs.Bridge.Certificate.FullBlockLiteralExecutedBinding,
    `TLT_Proofs.Bridge.Certificate.GridExtension,
    `TLT_Proofs.Bridge.Certificate.LNBudgetDischarge,
    `TLT_Proofs.Bridge.Certificate.LiteralStackCertConcrete,
    `TLT_Proofs.Bridge.Certificate.MHBlockRootBinding,
    `TLT_Proofs.Bridge.Certificate.MeasurabilityPrecondition,
    `TLT_Proofs.Bridge.Certificate.MinimalFFNCertificate,
    `TLT_Proofs.Bridge.Certificate.MultiHeadEncoderStack,
    `TLT_Proofs.Bridge.Certificate.TransformerCertificate,
    `TLT_Proofs.Bridge.Certificate.TransformerStackCertificate,
    `TLT_Proofs.Bridge.Certificate.TransformerStackLiteralExecutedBinding,
    `TLT_Proofs.Bridge.Forward.BoundedExecLayer,
    `TLT_Proofs.Bridge.Forward.ExecLayerInstances,
    `TLT_Proofs.Bridge.Forward.ExecutedForward,
    `TLT_Proofs.Bridge.Forward.ExecutedStackAtDepth,
    `TLT_Proofs.Bridge.Forward.ForwardContinuity,
    `TLT_Proofs.Bridge.Forward.ForwardEnvelope,
    `TLT_Proofs.Bridge.Forward.LayerConsistency,
    `TLT_Proofs.Bridge.Forward.LiteralBlockComposition,
    `TLT_Proofs.Bridge.Forward.LiteralStackMargin,
    `TLT_Proofs.Bridge.Forward.NonExpansiveDepthEnvelope,
    `TLT_Proofs.Bridge.Forward.TransformerForwardRegularity,
    `TLT_Proofs.Bridge.Fp32.AttentionForwardError,
    `TLT_Proofs.Bridge.Fp32.ClampedReductionRounding,
    `TLT_Proofs.Bridge.Fp32.ExpConeError,
    `TLT_Proofs.Bridge.Fp32.ExpExecutedValue,
    `TLT_Proofs.Bridge.Fp32.ExpPolynomialError,
    `TLT_Proofs.Bridge.Fp32.FFNBiasForwardError,
    `TLT_Proofs.Bridge.Fp32.FFNForwardError,
    `TLT_Proofs.Bridge.Fp32.GenSoftmaxForwardError,
    `TLT_Proofs.Bridge.Fp32.LayerNormForwardError,
    `TLT_Proofs.Bridge.Fp32.RelativeUlpAndSummation,
    `TLT_Proofs.Bridge.Fp32.SequentialSummationBackwardError,
    `TLT_Proofs.Bridge.Fp32.StackActivationExecutedValue,
    `TLT_Proofs.Bridge.Lipschitz.AttentionLipschitzOnBall,
    `TLT_Proofs.Bridge.Lipschitz.LayerNormLipschitz,
    `TLT_Proofs.Bridge.Lipschitz.LinearLayerWeightLipschitz,
    `TLT_Proofs.Bridge.Lipschitz.MultiHeadAttnCertificate,
    `TLT_Proofs.Bridge.Lipschitz.ParameterPerturbationEnvelope,
    `TLT_Proofs.Bridge.Lipschitz.SoftmaxJacobian,
    `TLT_Proofs.Bridge.Spec.LayerNormCorrespondence,
    `TLT_Proofs.Bridge.Spec.MultiHeadAttentionSingleHeadReduction,
    `TLT_Proofs.Bridge.Spec.ReluMatMulExecLayers,
    `TLT_Proofs.Bridge.Spec.ScaledDotProductAttentionCorrespondence,
    `TLT_Proofs.Bridge.Spec.ScaledDotProductScoreRouter,
    `TLT_Proofs.Bridge.Spec.TransformerObjectVocabulary,
    `TLT_Proofs.Capacity.Chaining.ChainingNets,
    `TLT_Proofs.Capacity.Chaining.DudleyEntropyIntegralFiniteness,
    `TLT_Proofs.Capacity.Chaining.LipschitzCoveringDischarge,
    `TLT_Proofs.Capacity.Chaining.McDiarmidInequality,
    `TLT_Proofs.Capacity.Chaining.MetricEntropy,
    `TLT_Proofs.Capacity.Chaining.RademacherDudleyBound,
    `TLT_Proofs.Capacity.Chaining.RademacherSymmetrization,
    `TLT_Proofs.Capacity.Discretization.DenseBaseChangeCapacity,
    `TLT_Proofs.Capacity.Discretization.DenseIndexRealization,
    `TLT_Proofs.Capacity.Discretization.DyadicNumericalBase,
    `TLT_Proofs.Capacity.Discretization.Float32IsDyadic,
    `TLT_Proofs.Capacity.Discretization.SymmetrizationBaseInvariantBound,
    `TLT_Proofs.Capacity.SubGaussianRademacher.EmpiricalRademacherDudleyBound,
    `TLT_Proofs.Capacity.SubGaussianRademacher.EmpiricalRademacherIsSubGaussian,
    `TLT_Proofs.Capacity.SubGaussianRademacher.EmpiricalRademacherProcess,
    `TLT_Proofs.Capacity.SubGaussianRademacher.MassartFiniteClassMaximalInequality,
    `TLT_Proofs.Capacity.SubGaussianRademacher.SubGaussianProcess,
    `TLT_Proofs.Capacity.SubGaussianRademacher.UniformGapMcDiarmidConcentration,
    `TLT_Proofs.Learner.MeasurableParametricAttentionLearner,
    `TLT_Proofs.Numerics.LayerNormVarianceCancellation,
    `TLT_Proofs.Routing.MeasurableScoreRouting,
    `TLT_Proofs.Strictness.AttentionNonBorelWitness,
    `TLT_Proofs.Tame.FiniteCellRouter,
    `TLT_Proofs.Tame.SigmaCompactParam,
    `TLT_Proofs.Tame.SingletonBadEventBorel,
    `TLT_Proofs.Tame.SingletonWellBehaved
  ]

-- SLT (lean-stat-learning-theory, Zhang–Lee–Liu): the 7-file Dudley entropy-integral cone
-- (SubGaussian, Chaining, MetricEntropy, CoveringNumber, MeasureInfrastructure, SeparableSpaceSup,
-- Dudley), vendored under `vendor/SLT`. Used from N5 onward for the optimal-constant (12√2) chaining
-- bound; TLT_Proofs.Capacity.* remain TLT's own native foundations (N1–N4). Upstream is on Lean
-- v4.27 + `mathlib@master`; re-pinned here to TLT's `8a17838` (no longer floating). Two source edits
-- vs upstream: (1) SeparableSpaceSup `ConditionallyCompleteLattice.le_csSup` → `le_csSup` (v4.27→v4.29
-- rename); (2) MeasureInfrastructure `exp_mul_sup'_le_sum` → `slt_exp_mul_sup'_le_sum` (avoids a
-- top-level name clash with the FLT kernel's identically-named lemma, so a TLT file may import both).
-- `SLT.dudley` is sorry-free and axiom-clean against this pin.
lean_lib SLTVendor where
  srcDir := "vendor"
  globs := #[Glob.submodules `SLT]

require FLT from git
  "https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel" @ "main"

-- TorchLean: the design-lab vendored source at the Mathlib-8a17838-pinned commit
-- (60e3f151, no longer on public lean-dojo/TorchLean main). Local-path require.
require TorchLean from
  "/Users/polaris/Documents/Epistemology and Zetesis/Noumenal/design-lab/neural-networks"

-- Mathlib required last so its dependency versions take precedence over FLT's/TorchLean's
-- (Lake resolves later requires with higher priority; needed for `cache get` hashes).
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "8a178386ffc0f5fef0b77738bb5449d50efeea95"
