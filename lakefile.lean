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
    `TLT_Proofs.Boundary.UniversalRepair
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "fde0cc508f5375f278f515cb2f50a34a545a4c5c"

require FLT from git
  "https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel" @ "main"
