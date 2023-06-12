import Lake
open Lake DSL

package «proven-zk» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «ProvenZk» {
  moreLeanArgs := #["--tstack=1000000"]
  -- add any library configuration options here
}
