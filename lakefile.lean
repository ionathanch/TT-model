import Lake
open Lake DSL

package «BFCUL» where

lean_lib «src» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe «bfcul» where
  root := `Main
