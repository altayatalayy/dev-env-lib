/-!
Sets are characteristic functions over arbitrary
resource names; releases are arbitrary natural numbers. There are no finite
bounds on resources. One name still abstracts one tool/config pair, and each
installer/config/uninstall operation is atomic. See the coverage document for
where that abstraction differs from Zig.
-/
namespace DevEnv.Lifecycle

inductive Policy where
  | final | afterInstall | writeAhead | twoPhase
  deriving DecidableEq, Repr

inductive Phase where
  | idle | reserving | removing | installing | persisting | configuring | saving
  deriving DecidableEq, Repr

abbrev Names (α : Type) := α → Bool

structure State (α : Type) where
  hasLock : Bool := false
  lockRelease : Nat := 0
  desired : Names α := fun _ => false
  hasReceipt : Bool := false
  recRelease : Nat := 0
  tools : Names α := fun _ => false
  configs : Names α := fun _ => false
  owned : Names α := fun _ => false
  disk : Names α := fun _ => false
  stowed : Names α := fun _ => false
  phase : Phase := .idle
  install : Names α := fun _ => false
  remove : Names α := fun _ => false
  removeConfigs : Names α := fun _ => false

variable {α : Type}

def reserves (p : Policy) : Bool := p == .writeAhead || p == .twoPhase

def plan (s : State α) (release : Nat) (names : Names α) : State α :=
  { s with hasLock := true, lockRelease := release, desired := names }

def diffEmpty (s : State α) : Prop :=
  s.hasReceipt = true ∧ s.recRelease = s.lockRelease ∧
  (∀ x, s.tools x = s.desired x) ∧ (∀ x, s.configs x = s.desired x)

def start (p : Policy) (s : State α) : State α :=
  { s with
    install := fun x => s.desired x && (!s.hasReceipt ||
      s.recRelease != s.lockRelease || !s.tools x)
    remove := fun x => s.hasReceipt && s.tools x && !s.desired x
    removeConfigs := fun x => s.hasReceipt && s.configs x && !s.desired x
    phase := if reserves p then .reserving else .removing }

/-- One enabled apply action. Idle stutters; all other phases advance. -/
def advance (p : Policy) (s : State α) : State α :=
  match s.phase with
  | .idle => s
  | .reserving => { s with
      hasReceipt := true
      owned := fun x => s.owned x || s.disk x || s.stowed x || s.install x || s.desired x
      tools := fun x => s.tools x && !(p == .twoPhase && s.remove x)
      configs := fun x => s.configs x && !(p == .twoPhase && s.removeConfigs x)
      phase := .removing }
  | .removing => { s with disk := fun x => s.disk x && !s.remove x, phase := .installing }
  | .installing => { s with
      disk := fun x => s.disk x || s.install x
      phase := if p == .final then .configuring else .persisting }
  | .persisting => { s with
      hasReceipt := true
      recRelease := s.lockRelease
      tools := s.disk
      configs := fun x => s.configs x && s.stowed x
      owned := fun x => s.owned x || s.disk x || s.stowed x
      phase := .configuring }
  | .configuring => { s with stowed := s.desired, phase := .saving }
  | .saving => { s with
      hasReceipt := true
      recRelease := s.lockRelease
      tools := s.disk
      configs := s.stowed
      owned := fun x => s.owned x || s.disk x || s.stowed x
      phase := .idle }

def crash (s : State α) : State α := { s with phase := .idle }

def uninstall (s : State α) : State α :=
  { s with
    hasLock := false
    lockRelease := 0
    desired := fun _ => false
    hasReceipt := false
    recRelease := 0
    tools := fun _ => false
    configs := fun _ => false
    owned := fun _ => false
    disk := fun x => s.disk x && !(s.tools x || s.owned x)
    stowed := fun x => s.stowed x && !(s.configs x || s.owned x) }

/-- Arbitrary plans and crashes, plus explicit stuttering as in the old spec. -/
inductive Next (p : Policy) : State α → State α → Prop where
  | plan (s r names) : s.phase = .idle → Next p s (plan s r names)
  | start (s) : s.phase = .idle → s.hasLock = true → ¬diffEmpty s → Next p s (start p s)
  | advance (s) : Next p s (advance p s)
  | crash (s) : s.phase ≠ .idle → Next p s (crash s)
  | uninstall (s) : s.phase = .idle → s.hasReceipt = true → Next p s (uninstall s)
  | stutter (s) : Next p s s

inductive Reachable (p : Policy) : State α → Prop where
  | init : Reachable p {}
  | step : Reachable p s → Next p s t → Reachable p t

def OwnershipComplete (s : State α) : Prop := ∀ x,
  (s.disk x = true → s.tools x = true ∨ s.owned x = true) ∧
  (s.stowed x = true → s.configs x = true ∨ s.owned x = true)

def NoPhantomInstall (s : State α) : Prop := ∀ x,
  (s.tools x = true → s.disk x = true) ∧ (s.configs x = true → s.stowed x = true)

def NoReceiptEmpty (s : State α) : Prop := s.hasReceipt = false →
  ∀ x, s.disk x = false ∧ s.stowed x = false

/-- Strengthened induction invariant, including obligations of in-flight phases. -/
def InvAt (s : State α) (x : α) : Prop :=
  (s.disk x = true → s.tools x = true ∨ s.owned x = true) ∧
  (s.stowed x = true → s.configs x = true ∨ s.owned x = true) ∧
  (s.tools x = true → s.disk x = true) ∧
  (s.configs x = true → s.stowed x = true) ∧
  (s.hasReceipt = false → s.disk x = false ∧ s.stowed x = false ∧
    s.tools x = false ∧ s.configs x = false ∧ s.owned x = false) ∧
  (s.phase = .reserving →
    s.remove x = (s.hasReceipt && s.tools x && !s.desired x) ∧
    s.removeConfigs x = (s.hasReceipt && s.configs x && !s.desired x)) ∧
  (s.phase = .removing → s.tools x = true → s.remove x = false) ∧
  (s.phase = .removing ∨ s.phase = .installing ∨ s.phase = .persisting ∨
    s.phase = .configuring ∨ s.phase = .saving →
      s.hasReceipt = true ∧ (s.desired x = true → s.owned x = true) ∧
      (s.install x = true → s.owned x = true)) ∧
  (s.phase = .removing ∨ s.phase = .installing ∨ s.phase = .persisting ∨
    s.phase = .configuring → s.configs x = true → s.desired x = true)

def Inv (s : State α) : Prop := ∀ x, InvAt s x

theorem init_inv : Inv ({} : State α) := by simp [Inv, InvAt]

set_option maxHeartbeats 800000 in
theorem next_inv {s t : State α} (h : Inv s) (hn : Next .twoPhase s t) : Inv t := by
  intro x
  have hx := h x
  cases hn with
  | plan r names hi => simpa [InvAt, plan, hi] using hx
  | start hi hl hd =>
    simp_all [InvAt, start, reserves]
  | advance =>
    cases hp : s.phase <;> simp_all [InvAt, advance] <;> grind
  | crash hi => simp_all [InvAt, crash]
  | uninstall hi hr => simp_all [InvAt, uninstall] <;> grind
  | stutter => exact hx

theorem reachable_inv {s : State α} (h : Reachable .twoPhase s) : Inv s := by
  induction h with
  | init => exact init_inv
  | step _ hn ih => exact next_inv ih hn

/-- Safety holds even inside an apply, hence at every possible crash boundary. -/
theorem reachable_safety {s : State α} (h : Reachable .twoPhase s) :
    OwnershipComplete s ∧ NoPhantomInstall s ∧ NoReceiptEmpty s := by
  have hi := reachable_inv h
  refine ⟨fun x => ⟨(hi x).1, (hi x).2.1⟩,
    fun x => ⟨(hi x).2.2.1, (hi x).2.2.2.1⟩, ?_⟩
  intro hr x
  exact ⟨((hi x).2.2.2.2.1 hr).1, ((hi x).2.2.2.2.1 hr).2.1⟩

theorem diffEmpty_desired_present {s : State α} (h : NoPhantomInstall s)
    (hd : diffEmpty s) : ∀ x, s.desired x = true → s.disk x = true ∧ s.stowed x = true := by
  intro x hx
  exact ⟨(h x).1 (by rw [hd.2.2.1 x]; exact hx),
    (h x).2 (by rw [hd.2.2.2 x]; exact hx)⟩

theorem uninstall_leaves_nothing {s : State α} (h : OwnershipComplete s) :
    ∀ x, (uninstall s).disk x = false ∧ (uninstall s).stowed x = false := by
  intro x
  have hx := h x
  simp only [uninstall]
  grind

end DevEnv.Lifecycle
