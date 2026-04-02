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
    `TLT_Proofs.Learner.AttentionLearner
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "fde0cc508f5375f278f515cb2f50a34a545a4c5c"

require FLT from git
  "https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel" @ "main"
