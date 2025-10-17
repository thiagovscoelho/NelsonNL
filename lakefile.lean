import Lake
open Lake DSL

package «NelsonNL» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

@[default_target]
lean_lib NL where
  srcDir := "."

lean_exe nlDemo where
  root := `Main
