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
    `TLT_Proofs.Bridge.ForwardEnvelope
  ]

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
