import Lake
open Lake DSL

package cndsemantics

@[default_target]
lean_lib CndSemantics

require batteries from
  git "https://github.com/leanprover-community/batteries" @ "main"
