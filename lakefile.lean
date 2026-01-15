import Lake
open Lake DSL

package ziku where
  version := v!"0.1.0"
  moreLeanArgs := #[
    "-Dlinter.missingDocs=true",
    "-Dlinter.unusedVariables=true",
    "-Dlinter.deprecated=true",
    "-Dlinter.unusedSectionVars=true"
  ]

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "main"

lean_lib Ziku

lean_lib Tests where
  globs := #[.submodules `tests]

@[default_target]
lean_exe ziku where
  root := `Main

-- Master test runner (combines all test suites)
@[test_driver]
lean_exe «test-runner» where
  root := `tests.TestRunner

-- Legacy golden test runner (kept for backward compatibility)
lean_exe «golden-test» where
  root := `tests.GoldenTest

-- Legacy truncate test runner (kept for backward compatibility)
lean_exe «truncate-test» where
  root := `tests.TruncateTest

@[default_target]
lean_exe «scheme-backend» where
  root := `Backend.SchemeMain

@[default_target]
lean_exe «ziku-test» where
  root := `ZikuTest

@[default_target]
lean_exe «emit-compiled-code» where
  root := `tests.EmitCompiledCode
