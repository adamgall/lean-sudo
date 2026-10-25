import LeanSudo.LogSrv
import LeanSudo.Intercept.Seccomp

namespace LeanSudo.Intercept.Protocol

open LogSrv.Wire

structure Request where
  command : String
  cwd : String := ""
  argv : Array String := #[]
  env : Array String := #[]
  deriving Repr

def stringValue (value : Value) : Option String := do
  let text ← asString value
  if text.contains '\x00' then none else some text

def parseFields : List Field → Option String → Option String → Bool →
    Array String → Array String → Option Request
  | [], command, cwd, _, argv, env => do
    let command ← command
    if command.isEmpty then none else
      some { command, cwd := cwd.getD ""
             argv := if argv.isEmpty then #[command] else argv.set! 0 command
             env }
  | (tag, value) :: rest, command, cwd, pidSeen, argv, env => do
    match tag with
    | 1 =>
      if command.isSome then none else
        parseFields rest (some (← stringValue value)) cwd pidSeen argv env
    | 2 =>
      if cwd.isSome then none else
        parseFields rest command (some (← stringValue value)) pidSeen argv env
    | 3 => parseFields rest command cwd pidSeen (argv.push (← stringValue value)) env
    | 4 => parseFields rest command cwd pidSeen argv (env.push (← stringValue value))
    | 5 =>
      let pid ← asNumber value
      if pidSeen || pid > 2147483647 then none else
        parseFields rest command cwd true argv env
    | _ => none

def policy (bytes : ByteArray) : Option Request := do
  let fields ← fieldsArray bytes
  match fields with
  | [(1, .bytes body)] => parseFields (← LogSrv.Wire.fields body) none none false #[] #[]
  | _ => none

def hello (bytes : ByteArray) : Bool :=
  match fieldsArray bytes with
  | some [(2, .bytes body)] =>
    match LogSrv.Wire.fields body with
    | some [(1, .number pid)] => pid > 0 && pid ≤ 2147483647
    | _ => false
  | _ => false

def frame (field : Nat) (body : List UInt8) : Option ByteArray :=
  let wire := bytes field body
  if wire.length > 2097152 then none
  else some ⟨(Seccomp.little 4 wire.length ++ wire).toArray⟩

def helloResponse (token : ByteArray) (port : Nat) (logOnly : Bool) : Option ByteArray :=
  if token.size ≠ 16 then none else
  frame 1 ([9] ++ (token.extract 0 8).data.toList ++
    [17] ++ (token.extract 8 16).data.toList ++ number 3 port ++
    number 4 (if logOnly then 1 else 0))

def policyResponse (request : Request) (result : Int) : Option ByteArray :=
  if result = 1 then
    frame 2 (text 1 request.command ++ request.argv.toList.flatMap (text 2) ++
      request.env.toList.flatMap (text 3))
  else frame (if result = 0 then 3 else 4)
    (text 1 (if result = 0 then "command rejected by policy" else "intercept policy error"))

def tokenMatches (expected actual : ByteArray) : Bool :=
  expected.size == 16 && actual.size == 16 &&
    (List.range 16).foldl (fun difference i =>
      difference ||| ((expected[i]?.getD 0) ^^^ (actual[i]?.getD 0))) (0 : UInt8) == 0

theorem tokenMatches_sizes (expected actual : ByteArray)
    (accepted : tokenMatches expected actual = true) :
    expected.size = 16 ∧ actual.size = 16 := by
  simp only [tokenMatches, Bool.and_eq_true, beq_iff_eq] at accepted
  exact accepted.1

theorem policy_rejects_unknown_outer (bytes : ByteArray) (tag : Nat) (body : List UInt8)
    (parsed : fieldsArray bytes = some [(tag, .bytes body)]) (unknown : tag ≠ 1) :
    policy bytes = none := by
  simp [policy, parsed]
  split <;> simp_all

theorem hello_rejects_zero (bytes : ByteArray) (body : List UInt8)
    (outer : fieldsArray bytes = some [(2, .bytes body)])
    (inner : LogSrv.Wire.fields body = some [(1, .number 0)]) :
    hello bytes = false := by
  simp [hello, outer, inner]

end LeanSudo.Intercept.Protocol
