import Lake
open Lake DSL

package ziku where
  version := v!"0.1.0"

lean_lib Ziku

lean_exe ziku where
  root := `Main

@[test_driver]
lean_exe «golden-test» where
  root := `tests.GoldenTest
