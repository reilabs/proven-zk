import Lake
open Lake DSL

package «proven-zk» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"26d0eab43f05db777d1cf31abd31d3a57954b2a9"

@[default_target]
lean_lib «ProvenZk» {
  moreLeanArgs := #["--tstack=1000000"]
  -- add any library configuration options here
}
