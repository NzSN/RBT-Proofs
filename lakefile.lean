import Lake
open Lake DSL

package «RBT-Proofs» where

@[default_target]
lean_lib «RBTProofs» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"
