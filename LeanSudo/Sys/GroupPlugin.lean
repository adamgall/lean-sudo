import LeanSudo.Sys.Core
import LeanSudo.Sys.Prim.GroupPlugin
import LeanSudo.Sys.Prim.Posix

namespace LeanSudo.Sys.GroupPlugin

open Prim.Store

structure State where
  library : Ptr
  queryFn : Ptr
  cleanupFn : Ptr
  args : Ptr
  count : Nat

structure Handle where
  state : IO.Ref (Option State)

def splitConfig (config : String) : String × Array String :=
  let words := config.splitOn "\t" |>.flatMap (·.splitOn " ")
  let name := words.headD ""
  let path := if name.startsWith "/" then name else "/usr/libexec/sudo/" ++ name
  (path, (words.drop 1 |>.filter (!·.isEmpty)).toArray)

def fallbackPath (native : Constants) (path : String) : Option String := do
  let components := path.splitOn "/"
  if components.length < 2 then none else do
    let base := components.getLast!
    let directory := "/".intercalate
      ((components.dropLast.reverse.dropWhile (·.isEmpty)).reverse)
    if !directory.endsWith "/lib" then none else
      let alternate := (directory.dropEnd 4).toString ++ "/lib64/" ++ base
      if alternate.utf8ByteSize < native.pathMax.toNat then some alternate else none

private def logMessage (kind : UInt32) (message : String) : IO UInt32 := do
  try
    let output ← if kind &&& 255 == 4 then IO.getStdout else IO.getStderr
    output.putStr message
    return message.utf8ByteSize.toUInt32
  catch _ => return 4294967295

private def freeArgs (args : Ptr) (count : Nat) : IO Unit := do
  if args != 0 then
    for i in [:count] do free (← pointer args i.toUSize)
    free args

private def closeState (ref : IO.Ref (Option State)) : IO Unit := do
  let some state ← ref.get | return
  ref.set none
  Prim.GroupPlugin.cleanup state.cleanupFn
  dlclose state.library
  freeArgs state.args state.count

private def makeArgs (texts : Array String) : IO Ptr := do
  let native ← native
  if texts.isEmpty then return 0
  let args ← calloc (texts.size + 1).toUSize native.pointerSize.toUSize
  if args == 0 then throw (IO.userError "unable to allocate memory")
  try
    for i in [:texts.size] do
      let text ← strdup texts[i]!
      if text == 0 then throw (IO.userError "unable to allocate memory")
      setPointer args i.toUSize text
    return args
  catch e =>
    freeArgs args texts.size
    throw e

private def initializePlugin (library : Ptr) (path : String) (args : Array String) :
    IO (Option Handle) := do
  let plugin ← dlsym library "group_plugin"
  if plugin == 0 then
    throw (IO.userError s!"unable to find symbol \"group_plugin\" in {path}")
  let version := (← Prim.GroupPlugin.version plugin) >>> 16
  if version != 1 then
    throw (IO.userError s!"{path}: incompatible group plugin major version {version}, expected 1")
  let (init, query, cleanup) ← Prim.GroupPlugin.functions plugin
  if init == 0 || query == 0 || cleanup == 0 then
    throw (IO.userError s!"{path}: incomplete group plugin interface")
  let argv ← makeArgs args
  try
    Prim.GroupPlugin.logger logMessage
    if (← Prim.GroupPlugin.init init argv) != 1 then
      freeArgs argv args.size
      dlclose library
      return none
    let state ← IO.mkRef (some {
      library
      queryFn := query
      cleanupFn := cleanup
      args := argv
      count := args.size : State })
    return some { state }
  catch e =>
    freeArgs argv args.size
    throw e

private def loadPath (name : String) (args : Array String) : IO (Option Handle) := do
  let native ← native
  let name := if name.contains '\x00' then
    String.ofList (name.toList.takeWhile (· != '\x00')) else name
  if name.utf8ByteSize ≥ native.pathMax.toNat then
    throw (IO.userError s!"{name}: {← strerror native.enametoolong}")
  let mut path := name
  let mut library ← dlopen path (native.dlLazy ||| native.dlGlobal)
  if library == 0 then
    if let some alternate := fallbackPath native path then
      if (← Sys.stat alternate).isSome then
        path := alternate
        library ← dlopen path (native.dlLazy ||| native.dlGlobal)
  if library == 0 then
    throw (IO.userError s!"unable to load {path}: {← dlerror}")
  try initializePlugin library path args
  catch e =>
    dlclose library
    throw e

def load (config : String) : IO (Option Handle) :=
  let (path, args) := splitConfig config
  loadPath path args

def accepts (result : UInt32) : Bool := result == 1

theorem accepts_iff (result : UInt32) : accepts result = true ↔ result = 1 := by
  simp [accepts]

private partial def queryWithPasswd (fn : Ptr) (user group : String) (size : Nat) :
    IO Bool := do
  let header := Prim.GroupPlugin.passwdSize ()
  if size > USize.size - 1 - header.toNat then
    throw (IO.userError "unable to allocate memory")
  let record ← calloc 1 (header.toNat + size).toUSize
  if record == 0 then throw (IO.userError "unable to allocate memory")
  let retry : Option Bool ← try
    let (error, found) ← Prim.GroupPlugin.passwd user record
      (record + header.toUInt64) size.toUSize
    if error == Prim.Posix.ERANGE () then pure none else do
      let result ← Prim.GroupPlugin.query fn user group
        (if error == 0 && found then record else 0)
      pure (some (accepts result))
  finally free record
  if let some accepted := retry then return accepted
  queryWithPasswd fn user group (size * 2)

def query (handle : Handle) (user group : String) : IO Bool := do
  let some state ← handle.state.get | return false
  queryWithPasswd state.queryFn user group 1024

def close (handle : Handle) : IO Unit :=
  closeState handle.state

end LeanSudo.Sys.GroupPlugin
