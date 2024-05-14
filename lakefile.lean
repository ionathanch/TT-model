import Lake
open Lake DSL

package «TT-model» where
  -- add package configuration options here

lean_lib «TT-model» where
  -- add library configuration options here

@[default_target]
lean_exe «tt-model» where
  root := `Main
