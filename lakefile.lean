import Lake
open Lake DSL

package jumpProcessesLean where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]
  -- keep two-way branches as branches: a select on the tree descent's child index makes each
  -- level's load wait for the previous comparison
  moreLeancArgs := #["-mllvm", "-two-entry-phi-node-folding-threshold=0"]

require floatlib from git "https://github.com/lean-dojo/FloatLib.git" @
  "1e83f09ed8c41a953cf8f93d26c210778177b94a"

@[default_target]
lean_lib JumpProcessesLean

lean_lib Tests

@[test_driver]
lean_exe jumpTests where
  root := `Tests.Main

lean_exe jumpBench where
  root := `JumpBench
