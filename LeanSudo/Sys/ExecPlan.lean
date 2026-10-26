import Lean
import LeanSudo.Core.Types

namespace LeanSudo.Sys
structure ExecSpec where
  path : String
  argv : Array String
  env : Array String
  uid : Nat
  gid : Nat
  groups : Array Nat
  cwd : Option String
  umask : Nat
  usePty : Bool
  background : Bool
  closeFrom : Nat := 3
  cwdOptional : Bool := false
  timeout : Nat := 0
  noexecFile : Option String := none
  apparmorProfile : Option String := none
  rlimits : Array (String × String) := #[("rlimit_core", "0,0")]
  utmpUser : Option String := none
  execFd : Option Nat := none
  execBackground : Bool := false
  staySetuid : Bool := false
  chroot : Option String := none
  deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson

inductive ExitStatus where
  | exited (code : Nat)
  | signaled (sig : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Exec

def maxId : Nat := 0xFFFFFFFE

def toId? (n : Nat) : Option UInt32 :=
  if n ≤ maxId then some n.toUInt32 else none

theorem toUInt32_toNat_of_lt {n : Nat} (h : n < 4294967296) : n.toUInt32.toNat = n := by
  rw [Nat.toUInt32, UInt32.toNat_ofNat']
  omega

theorem toId?_some {n : Nat} {v : UInt32} (h : toId? n = some v) :
    v.toNat = n ∧ n ≤ maxId := by
  unfold toId? at h
  split at h
  · rename_i hle
    cases h
    unfold maxId at hle
    exact ⟨toUInt32_toNat_of_lt (by omega), hle⟩
  · cases h

theorem toId?_ne_sentinel {n : Nat} {v : UInt32} (h : toId? n = some v) :
    v ≠ 0xFFFFFFFF := by
  have ⟨hv, hle⟩ := toId?_some h
  intro heq
  subst heq
  unfold maxId at hle
  simp at hv
  omega

def decodeStatus (r : UInt32) : ExitStatus :=
  if r.toNat ≥ 0x10000 then .signaled (r.toNat - 0x10000) else .exited r.toNat

theorem decodeStatus_exited (c : Nat) (h : c < 0x10000) :
    decodeStatus c.toUInt32 = .exited c := by
  have hc := toUInt32_toNat_of_lt (n := c) (by omega)
  unfold decodeStatus
  rw [hc]
  split
  · omega
  · rfl

theorem decodeStatus_signaled (s : Nat) (h : s < 0x10000) :
    decodeStatus (0x10000 + s).toUInt32 = .signaled s := by
  have hc := toUInt32_toNat_of_lt (n := 0x10000 + s) (by omega)
  unfold decodeStatus
  rw [hc, Nat.add_sub_cancel_left]
  split
  · rfl
  · omega

def cSafe (s : String) : Bool := !s.contains '\x00'

def stringsSafe (s : ExecSpec) : Bool :=
  cSafe s.path && s.argv.all cSafe && s.env.all cSafe &&
    (s.cwd.map cSafe).getD true && (s.chroot.map cSafe).getD true &&
    (s.noexecFile.map cSafe).getD true &&
    (s.apparmorProfile.map cSafe).getD true && (s.utmpUser.map cSafe).getD true &&
    s.rlimits.all (fun (k, v) => cSafe k && cSafe v)

def validDescriptor (fd : Nat) : Bool := decide (3 ≤ fd ∧ fd ≤ 0x7FFFFFFF)

theorem validDescriptor_bounds {fd : Nat} (h : validDescriptor fd = true) :
    3 ≤ fd ∧ fd ≤ 0x7FFFFFFF := by
  simpa [validDescriptor] using h

theorem validDescriptor_exact {fd : Nat} (h : validDescriptor fd = true) :
    fd.toUInt32.toNat = fd ∧ fd.toUInt32 ≠ 0xFFFFFFFF := by
  have hb := validDescriptor_bounds h
  have he := toUInt32_toNat_of_lt (n := fd) (by omega)
  refine ⟨he, ?_⟩
  intro hs
  rw [hs] at he
  simp at he
  omega

def validExecFd : Option Nat → Bool
  | none => true
  | some fd => validDescriptor fd

theorem validExecFd_some {fd : Nat} (h : validExecFd (some fd) = true) :
    3 ≤ fd ∧ fd ≤ 0x7FFFFFFF := by
  exact validDescriptor_bounds h

theorem validExecFd_exact {fd : Nat} (h : validExecFd (some fd) = true) :
    fd.toUInt32.toNat = fd ∧ fd.toUInt32 ≠ 0xFFFFFFFF := by
  have hb := validExecFd_some h
  have he := toUInt32_toNat_of_lt (n := fd) (by omega)
  refine ⟨he, ?_⟩
  intro hs
  rw [hs] at he
  simp at he
  omega

def checkGroup (g : Nat) : Except String UInt32 :=
  match toId? g with
  | some v => .ok v
  | none => .error s!"invalid gid {g}"

def checkGroups (groups : Array Nat) : Except String (Array UInt32) :=
  groups.mapM checkGroup

theorem checkGroups_bounds {groups : Array Nat} {values : Array UInt32}
    (h : checkGroups groups = .ok values) :
    ∀ g ∈ groups, g ≤ maxId := by
  rcases groups with ⟨groups⟩
  unfold checkGroups at h
  simp only [List.mapM_toArray] at h
  induction groups generalizing values with
  | nil => simp
  | cons g gs ih =>
    simp only [List.mapM_cons] at h
    cases hg : toId? g with
    | none =>
      simp [checkGroup, hg, bind, Except.bind, Functor.map, Except.map] at h
    | some v =>
      have hv : checkGroup g = .ok v := by simp [checkGroup, hg]
      rw [hv] at h
      cases ht : List.mapM checkGroup gs with
      | error e =>
        rw [ht] at h
        contradiction
      | ok vs =>
        have hb := (toId?_some hg).2
        have hs := ih (values := vs.toArray) (by rw [ht]; rfl)
        intro x hx
        have hx' : x = g ∨ x ∈ gs := by simpa using hx
        rcases hx' with rfl | hx'
        · exact hb
        · exact hs x (by simpa using hx')

structure Checked where
  uid : UInt32
  gid : UInt32
  groups : Array UInt32
  umask : UInt32
  closeFrom : UInt32

def check (s : ExecSpec) : Except String Checked :=
  if !s.path.startsWith "/" then
    .error s!"unable to execute {s.path}: path is not absolute"
  else if !stringsSafe s then
    .error s!"unable to execute {s.path}: argument contains a NUL byte"
  else if s.argv.isEmpty then
    .error s!"unable to execute {s.path}: empty argument vector"
  else
    match toId? s.uid with
    | none => .error s!"invalid uid {s.uid}"
    | some uid =>
      match toId? s.gid with
      | none => .error s!"invalid gid {s.gid}"
      | some gid =>
        match checkGroups s.groups with
        | .error error => .error error
        | .ok groups =>
          if ¬s.umask ≤ 0o777 then
            .error s!"invalid umask {s.umask}"
          else if !validDescriptor s.closeFrom then
            .error s!"invalid closefrom value {s.closeFrom}"
          else if ¬s.timeout ≤ 0x7FFFFFFF then
            .error "invalid command timeout"
          else if !validExecFd s.execFd then
            .error "invalid executable descriptor"
          else
            .ok { uid, gid, groups, umask := s.umask.toUInt32,
                  closeFrom := s.closeFrom.toUInt32 }

theorem check_valid {s : ExecSpec} {checked : Checked} (h : check s = .ok checked) :
    stringsSafe s = true ∧
    s.uid ≤ maxId ∧ s.gid ≤ maxId ∧ (∀ g ∈ s.groups, g ≤ maxId) ∧
    s.umask ≤ 0o777 ∧ validDescriptor s.closeFrom = true ∧
    s.timeout ≤ 0x7FFFFFFF ∧ validExecFd s.execFd = true := by
  unfold check at h
  repeat first | contradiction | split at h
  exact ⟨by simpa using ‹¬(!stringsSafe s = true)›,
    (toId?_some (by assumption)).2, (toId?_some (by assumption)).2,
    checkGroups_bounds (by assumption), by omega,
    by simpa using ‹¬(!validDescriptor s.closeFrom = true)›, by omega,
    by simpa using ‹¬(!validExecFd s.execFd = true)›⟩

def StringField (s : ExecSpec) (value : String) : Prop :=
  value = s.path ∨ value ∈ s.argv ∨ value ∈ s.env ∨
    s.cwd = some value ∨ s.chroot = some value ∨ s.noexecFile = some value ∨
    s.apparmorProfile = some value ∨ s.utmpUser = some value ∨
    ∃ pair ∈ s.rlimits, value = pair.1 ∨ value = pair.2

theorem cSafe_iff (s : String) : cSafe s = true ↔ s.contains '\x00' = false := by
  simp [cSafe]

theorem optional_cSafe_iff (s : Option String) :
    (s.map cSafe).getD true = true ↔
      ∀ value, s = some value → value.contains '\x00' = false := by
  cases s <;> simp [cSafe]

theorem stringsSafe_noNul {s : ExecSpec} (h : stringsSafe s = true)
    {value : String} (hfield : StringField s value) :
    value.contains '\x00' = false := by
  simp only [stringsSafe, Bool.and_eq_true, Array.all_eq_true',
    optional_cSafe_iff, cSafe_iff] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hp, ha⟩, he⟩, hw⟩, hc⟩, hn⟩, hm⟩, hu⟩, hr⟩
  rcases hfield with rfl | ha' | he' | hw' | hc' | hn' | hm' | hu' | hr'
  · exact hp
  · exact ha value ha'
  · exact he value he'
  · exact hw value hw'
  · exact hc value hc'
  · exact hn value hn'
  · exact hm value hm'
  · exact hu value hu'
  · rcases hr' with ⟨pair, hpair, rfl | rfl⟩
    · exact (hr pair hpair).1
    · exact (hr pair hpair).2

theorem check_noNul {s : ExecSpec} {checked : Checked}
    (h : check s = .ok checked) {value : String} (hfield : StringField s value) :
    value.contains '\x00' = false :=
  stringsSafe_noNul (check_valid h).1 hfield

theorem check_rejects_nul {s : ExecSpec} {value : String}
    (hfield : StringField s value) (hnul : value.contains '\x00' = true) :
    ∀ checked, check s ≠ .ok checked := by
  intro checked h
  have hs := check_noNul h hfield
  rw [hnul] at hs
  contradiction

theorem check_rejects_uid {s : ExecSpec} (huid : maxId < s.uid) :
    ∀ checked, check s ≠ .ok checked := by
  intro checked h
  have := (check_valid h).2.1
  omega

theorem check_rejects_gid {s : ExecSpec} (hgid : maxId < s.gid) :
    ∀ checked, check s ≠ .ok checked := by
  intro checked h
  have := (check_valid h).2.2.1
  omega

theorem check_rejects_group {s : ExecSpec} {g : Nat}
    (hmem : g ∈ s.groups) (hgid : maxId < g) :
    ∀ checked, check s ≠ .ok checked := by
  intro checked h
  have := (check_valid h).2.2.2.1 g hmem
  omega

theorem check_rejects_closeFrom {s : ExecSpec}
    (hfd : s.closeFrom < 3 ∨ 0x7FFFFFFF < s.closeFrom) :
    ∀ checked, check s ≠ .ok checked := by
  intro checked h
  have := validDescriptor_bounds (check_valid h).2.2.2.2.2.1
  omega

theorem check_rejects_execFd {s : ExecSpec} {fd : Nat}
    (hfd : s.execFd = some fd) (hbound : fd < 3 ∨ 0x7FFFFFFF < fd) :
    ∀ checked, check s ≠ .ok checked := by
  intro checked h
  have hv := (check_valid h).2.2.2.2.2.2.2
  rw [hfd] at hv
  have := validExecFd_some hv
  omega

theorem check_staySetuid (s : ExecSpec) (stay : Bool) :
    check { s with staySetuid := stay } = check s := by
  rfl

end Exec
end LeanSudo.Sys
def LeanSudo.Core.RunPlan.toSpec (plan : LeanSudo.Core.RunPlan) (path : String)
    (argv env : Array String) (uid gid : Nat) (groups : List Nat) : LeanSudo.Sys.ExecSpec := {
  path, argv, env, uid, gid, groups := groups.toArray,
  cwd := plan.cwd, cwdOptional := plan.cwdOptional, chroot := plan.chroot,
  umask := plan.umask, usePty := plan.usePty, timeout := plan.timeout,
  rlimits := plan.rlimits.toArray, utmpUser := plan.utmpUser, closeFrom := plan.closeFrom,
  execBackground := plan.execBackground, noexecFile := plan.noexecFile,
  apparmorProfile := plan.apparmorProfile, background := false }
