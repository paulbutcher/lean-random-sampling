/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package «random-sampling-test» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

require «random-sampling» from ".."

@[default_target]
lean_lib RandomSamplingTest where
  globs := #[.submodules `RandomSamplingTest]

@[default_target]
lean_exe tests where
  root := `Main

@[test_driver]
script test do
  let child ← IO.Process.spawn { cmd := "lake", args := #["exe", "tests"], cwd := __dir__ }
  child.wait
