import Lake
open Lake DSL

package «NelsonNL» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib NL

lean_exe nlDemo where
  root := `Main