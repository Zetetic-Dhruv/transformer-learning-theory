import Lake
open Lake DSL

package TransformerLearningTheory where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib TLT_Proofs where
  roots := #[
    `TLT_Proofs.Attention.BinaryRouting,
    `TLT_Proofs.Attention.FiniteRouting,
    `TLT_Proofs.Learner.AttentionLearner,
    `TLT_Proofs.Strictness.NonBorelWitness,
    `TLT_Proofs.Tame.SigmaCompactParam,
    `TLT_Proofs.Tame.SingletonBadEventBorel,
    `TLT_Proofs.Tame.SingletonWellBehaved,
    `TLT_Proofs.Tame.FiniteCellRouter,
    `TLT_Proofs.Boundary.Location,
    `TLT_Proofs.Boundary.Cascade,
    `TLT_Proofs.Boundary.CascadeTame,
    `TLT_Proofs.Boundary.UniversalRepair,
    `TLT_Proofs.Boundary.CancellationRepair,
    `TLT_Proofs.Bridge.TorchLeanAttention,
    `TLT_Proofs.Bridge.SoftAttention,
    `TLT_Proofs.Bridge.SoftHardSeparation,
    `TLT_Proofs.Bridge.FP32Channel,
    `TLT_Proofs.Bridge.TransformerRoot,
    `TLT_Proofs.Bridge.TransformerAttention,
    `TLT_Proofs.Bridge.ForwardContinuity,
    `TLT_Proofs.Bridge.TransformerForwardContinuous,
    `TLT_Proofs.Bridge.ExecutedForward,
    `TLT_Proofs.Bridge.Fp32Reduction,
    `TLT_Proofs.Bridge.LayerNormSpec,
    `TLT_Proofs.Bridge.ForwardEnvelope,
    `TLT_Proofs.Bridge.ExecLayerInstances,
    `TLT_Proofs.Bridge.SpecExecLayers,
    `TLT_Proofs.Capacity.SubGaussianMax,
    `TLT_Proofs.Capacity.SubGaussianProcess,
    `TLT_Proofs.Capacity.MetricEntropy,
    `TLT_Proofs.Capacity.Chaining,
    `TLT_Proofs.Bridge.CertifiedRiskBound,
    `TLT_Proofs.Bridge.ParamLipschitz,
    `TLT_Proofs.Bridge.Softmax,
    `TLT_Proofs.Bridge.AttentionLipschitz,
    `TLT_Proofs.Bridge.TransformerCertificate,
    `TLT_Proofs.Capacity.RademacherProcess,
    `TLT_Proofs.Capacity.RademacherSubGaussian,
    `TLT_Proofs.Capacity.RademacherDudley,
    `TLT_Proofs.Capacity.Symmetrization,
    `TLT_Proofs.Capacity.SymmetrizationDudley,
    `TLT_Proofs.Capacity.NumericalBase,
    `TLT_Proofs.Capacity.DyadicBase,
    `TLT_Proofs.Capacity.BaseInvariantBound,
    `TLT_Proofs.Capacity.McDiarmid,
    `TLT_Proofs.Capacity.FloatDyadic,
    `TLT_Proofs.Capacity.EntropyIntegralFinite,
    `TLT_Proofs.Capacity.DenseIndex,
    `TLT_Proofs.Capacity.GapConcentration,
    `TLT_Proofs.Capacity.CoveringDischarge,
    `TLT_Proofs.Bridge.CertifiedCapacityBound,
    `TLT_Proofs.Bridge.CertifiedTransformerBound,
    `TLT_Proofs.Bridge.LayerNormLipschitz,
    `TLT_Proofs.Bridge.MinimalFFNCertificate,
    `TLT_Proofs.Bridge.LayerConsistency,
    `TLT_Proofs.Bridge.LayerParamLipschitz,
    `TLT_Proofs.Bridge.ParamLipschitzLocal,
    `TLT_Proofs.Bridge.BoundedExecLayer,
    `TLT_Proofs.Bridge.AttentionTransformerCertificate,
    `TLT_Proofs.Bridge.AttentionSpecBridge,
    `TLT_Proofs.Bridge.AttentionExecutedCertificate,
    `TLT_Proofs.Bridge.AttnStackCertificate,
    `TLT_Proofs.Bridge.TransformerStackCertificate,
    `TLT_Proofs.Bridge.EncoderLayerSpecBridge,
    `TLT_Proofs.Bridge.MultiHeadAttnCertificate,
    `TLT_Proofs.Bridge.MultiHeadEncoderStack,
    `TLT_Proofs.Bridge.ExecutedStackAtDepth,
    `TLT_Proofs.Bridge.NonExpansiveDepthEnvelope,
    `TLT_Proofs.Bridge.Fp32DerivedRounding
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
