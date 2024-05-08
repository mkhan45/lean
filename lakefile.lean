import Lake
open Lake DSL

package «idk» where
  -- add package configuration options here

lean_lib «Idk» where
  -- add library configuration options here

@[default_target]
lean_exe «idk» where
  root := `Main
