import Lake
open Lake DSL System

package «lean-sudo» where
  moreLinkArgs := #["-ldl", "-lutil",
    if System.Platform.isOSX then "-Wl,-export_dynamic" else "-Wl,--export-dynamic"]

def shimSources : Array String := #[
  "core", "prim_exec", "prim_timestamp", "visudo", "prim_edit", "sys", "prim_iolog",
  "prim_visudo",
  "prim_plugins", "prim_logsrv", "prim_intercept", "prim_lookup",
  "prim_corefacts", "prim_posix",
  "prim_pam", "prim_store", "prim_sss", "prim_groupplugin", "prim_extra", "prim_corelogs"]

def shimCFlags : Array String :=
  #["-fPIC", "-O2", "-Wall", "-Wextra", "-Werror", "-D_GNU_SOURCE",
    "-fstack-protector-strong", "-D_FORTIFY_SOURCE=2"] ++
    (if System.Platform.isOSX then #[] else #["-fstack-clash-protection"])

def shimHeaders : Array String := #[
  "sudo_plugin.h", "shim.h"]

extern_lib leansudoshim pkg := do
  let leanInc := (← getLeanIncludeDir).toString
  let objs ← shimSources.mapM fun src => do
    let oFile := pkg.buildDir / "c" / s!"{src}.o"
    let srcJob ← inputTextFile <| pkg.dir / "c" / s!"{src}.c"
    let depTrace : JobM BuildTrace := do
      let hs ← shimHeaders.mapM fun (h : String) =>
        BuildTrace.compute (TextFilePath.mk (pkg.dir / "c" / h))
      return hs.foldl BuildTrace.mix (← getLeanTrace)
    buildO oFile srcJob #["-I", leanInc] shimCFlags "cc" depTrace
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leansudoshim") objs

@[default_target]
lean_lib LeanSudo where

@[default_target]
lean_exe sudo where
  root := `Main

@[default_target]
lean_exe visudo where
  root := `Visudo
