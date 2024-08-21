import Lake
open Lake DSL

package «Main» where
  -- add package configuration options here

@[default_target]
lean_lib «Main» where
  -- add library configuration options here

require LeanSAT from git "https://github.com/leanprover/leansat" @ "main"
