import Lake
open Lake DSL

package «Shootout» where
  -- add package configuration options here

lean_lib «Shootout» where
  -- add library configuration options here

require LeanSAT from git "https://github.com/leanprover/leansat" @ "main"

@[default_target]
lean_exe «shootout» where
  root := `Main
