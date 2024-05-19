import Lake
open Lake DSL

package «TT-model» where

lean_lib «TT-model» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe «tt-model» where
  root := `Main
