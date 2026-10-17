import Lake
open Lake DSL

package jumpProcessesLean where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]
  -- keep two-way branches as branches: a select on the tree descent's child index makes each
  -- level's load wait for the previous comparison; include/noexport_hidden.h hides every symbol
  -- in the objects that executables link, so that constants are read without the GOT
  moreLeancArgs := #["-mllvm", "-two-entry-phi-node-folding-threshold=0",
    "-include", (__dir__ / "include" / "noexport_hidden.h").toString]

require floatlib from git "https://github.com/lean-dojo/FloatLib.git" @
  "1e83f09ed8c41a953cf8f93d26c210778177b94a"

-- executables link the objects built without `LEAN_EXPORTING` (as Lake does on Windows)
@[default_target]
lean_lib JumpProcessesLean where
  nativeFacets := fun shouldExport =>
    if shouldExport then #[Module.oExportFacet] else #[Module.oNoExportFacet]

lean_lib Tests

@[test_driver]
lean_exe jumpTests where
  root := `Tests.Main

lean_exe jumpBench where
  root := `JumpBench
