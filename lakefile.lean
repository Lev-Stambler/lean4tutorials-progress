import Lake
open Lake DSL

package «hello» {
  -- add package configuration options here
}

lean_lib «Hello» {
  -- add library configuration options here
}

lean_lib «IncrRuntimeAttr» {
} 

lean_lib «bigO» {
} 

@[default_target]
lean_exe «hello» {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"