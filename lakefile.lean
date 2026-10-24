import Lake
open Lake DSL System

package «lean-sudo» where
  -- The C shim dlopen()s libpam at runtime, so only libdl/libutil are needed at link time.
  moreLinkArgs := #["-ldl", "-lutil"]

/-- C shim translation units (each owned by one Lean `LeanSudo.Sys.*` module). -/
def shimSources : Array String := #["core", "exec", "ts", "visudo"]

def shimCFlags : Array String :=
  #["-fPIC", "-O2", "-Wall", "-Wextra", "-Werror", "-D_GNU_SOURCE",
    "-fstack-protector-strong", "-D_FORTIFY_SOURCE=2"]

extern_lib leansudoshim pkg := do
  let leanInc := (← getLeanIncludeDir).toString
  let objs ← shimSources.mapM fun src => do
    let oFile := pkg.buildDir / "c" / s!"{src}.o"
    let srcJob ← inputTextFile <| pkg.dir / "c" / s!"{src}.c"
    buildO oFile srcJob #["-I", leanInc] shimCFlags "cc" getLeanTrace
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leansudoshim") objs

@[default_target]
lean_lib LeanSudo where

@[default_target]
lean_exe sudo where
  root := `Main

/-- Compile-time unit tests (`#guard`/`example`), one module per area: `lake build Tests`. -/
lean_lib Tests where
  srcDir := "test"
  globs := #[.submodules `Tests]

/-- IO smoke executables for the C shim (run unprivileged; root-only paths are
exercised by the docker integration suite). -/
lean_exe «smoke-core» where
  srcDir := "test"
  root := `Smoke.Core

lean_exe «smoke-exec» where
  srcDir := "test"
  root := `Smoke.Exec

lean_exe «smoke-ts» where
  srcDir := "test"
  root := `Smoke.Ts

@[default_target]
lean_exe visudo where
  root := `Visudo
