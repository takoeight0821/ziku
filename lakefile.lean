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

lean_exe «ir-eval-test» where
  root := `tests.IREvalTest

lean_exe «trace-test» where
  root := `tests.TraceTest

lean_exe «truncate-test» where
  root := `tests.TruncateTest

lean_exe «scheme-backend» where
  root := `Backend.SchemeMain
