import Lake
open Lake DSL

package «AlignmentTrap» where
  -- add package configuration options here

lean_lib «AlignmentTrap» where
  -- add library configuration options here

@[default_target]
lean_exe «alignmenttrap» where
  root := `AlignmentTrap.Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
