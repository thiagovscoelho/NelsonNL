import Lake
open Lake DSL

package «nl» where

lean_lib NL where
  -- srcDir defaults to `./`, so `NL/*.lean` is fine.

-- optional: an executable for quick tests
@[default_target]
lean_exe nlDemo where
  root := `Main
