import Mt.Task

namespace Mt

structure Thread (spec : Spec) where
  T : Type
  reservation : spec.Reservation
  task : TaskM spec T

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

def mk_thread {T : Type} (task : TaskM spec T) : Thread spec := {
  T
  reservation := IsReservation.empty
  task }

namespace Thread

def valid (thread : Thread spec) : Prop :=
  thread.task.valid_for_reservation thread.reservation

inductive IterationResult (spec : Spec) where
  | Done : spec.Reservation -> spec.State -> IterationResult spec
  | Panic : spec.Reservation -> spec.State -> IterationResult spec
  | Running : spec.State -> Thread spec -> IterationResult spec

def IterationResult.state : IterationResult spec -> spec.State
  | Done _ state => state
  | Panic _ state => state
  | Running state _ => state

def IterationResult.reservation : IterationResult spec -> spec.Reservation
  | Done r _ => r
  | Panic r _ => r
  | Running _ cont => cont.reservation

def iterate : Thread spec -> spec.State -> IterationResult spec
  | ⟨T, r, task⟩, state =>
    match task.iterate r state with
    | TaskM.IterationResult.Done r state' _ => IterationResult.Done r state'
    | TaskM.IterationResult.Panic r state' _ => IterationResult.Panic r state'
    | TaskM.IterationResult.Continuation reservation state' task => 
      IterationResult.Running state' { T, reservation, task }

theorem valid.def (thread : Thread spec) :
  thread.valid = 
    ∀ (state : spec.State) (env_r : spec.Reservation),
    spec.validate (env_r + thread.reservation) state →
    match thread.iterate state with
      | IterationResult.Done r' state' => spec.validate (env_r + r') state'
      | IterationResult.Panic .. => False
      | IterationResult.Running state' cont =>
        (spec.validate (env_r + cont.reservation) state') ∧ cont.valid :=by
  simp only [valid, iterate]
  rw [TaskM.valid_for_reservation.def]
  apply forall_ext ; intro state
  apply forall_ext ; intro env_r
  cases TaskM.iterate thread.task thread.reservation state <;> simp only []

end Thread

/-- Describes a system of zero or more threads running in parallel

  Systems can be iterated one atomic step at a time by choosing
  one of its threads. They keep track of the number of threads
  which panicked during execution
-/
structure System (spec : Spec) where
  state   : spec.State
  threads : List (Thread spec)
  panics  : Nat

namespace System

def ThreadIndex (s : System spec) : Type :=Fin s.threads.length
def done (s : System spec) : Bool :=s.threads.length = 0

protected def sum_reservations : List (Thread spec) -> spec.Reservation
  | [] => IsReservation.empty
  | thread :: threads => thread.reservation + System.sum_reservations threads

def reservations (s : System spec) : spec.Reservation :=
  System.sum_reservations s.threads

def other_reservations (s : System spec) (thread_idx : s.ThreadIndex) : spec.Reservation :=
  System.sum_reservations <| s.threads.eraseIdx thread_idx.val

theorem decompose_reservation (s : System spec) (thread_idx : s.ThreadIndex) :
  s.reservations = (s.other_reservations thread_idx) + (s.threads.get thread_idx).reservation :=by
  suffices
    ∀ (l : List <| Thread spec) (idx : Fin l.length),
    System.sum_reservations l = System.sum_reservations (l.eraseIdx idx.val) + (l.get idx).reservation from
    this s.threads thread_idx
  clear s thread_idx
  
  intro l
  induction l
  . intro idx
    have : idx.val < 0 :=idx.isLt
    contradiction
  . intro idx
    rename_i thread threads IH
    cases h : idx.val
    . have : idx = Fin.mk 0 (by simp_arith) :=Fin.eq_of_val_eq h
      simp only [this, List.get, List.eraseIdx, System.sum_reservations]
      exact IsReservation.toIsCommutative.comm _ _
    . rename_i n
      have idx_ok : n + 1 < (thread :: threads).length :=calc
        n + 1 = idx.val :=h.symm
        _ < _ :=idx.isLt
      have : idx = Fin.mk (n + 1) idx_ok :=Fin.eq_of_val_eq h
      simp only [this, List.get, List.eraseIdx, System.sum_reservations]
      clear this h idx
      rw [IsReservation.toIsAssociative.assoc]
      apply congrArg (thread.reservation + .)
      exact IH <| Fin.mk n (Nat.le_of_succ_le_succ idx_ok)

def iterate (s : System spec) : s.ThreadIndex -> System spec
  | thread_idx =>
    match (s.threads.get thread_idx).iterate s.state with
      | Thread.IterationResult.Done _ state =>
        {
          state
          threads := s.threads.eraseIdx thread_idx.val
          panics := s.panics
        }
      | Thread.IterationResult.Panic _ state =>
        {
          state
          threads := s.threads.eraseIdx thread_idx.val
          panics := s.panics + 1
        }
      | Thread.IterationResult.Running state thread =>
        {
          state
          threads := s.threads.set thread_idx.val thread
          panics := s.panics
        }
      
def reduces_single (a b : System spec) : Prop :=
  ∃ idx : a.ThreadIndex, a.iterate idx = b

def reduces_to : System spec -> System spec -> Prop :=TC reduces_single
def reduces_to_or_eq (a b : System spec) : Prop :=a = b ∨ a.reduces_to b

theorem reduces_to_or_eq.refl (a : System spec) : a.reduces_to_or_eq a :=Or.inl rfl
theorem reduces_to_or_eq.trans {a b c : System spec} :
  a.reduces_to_or_eq b → b.reduces_to_or_eq c → a.reduces_to_or_eq c :=by
  intro ab bc
  cases ab <;> cases bc <;> rename_i h₁ h₂
  . rw [h₁, h₂] ; exact Or.inl rfl
  . rw [h₁] ; exact Or.inr h₂
  . rw [h₂.symm] ; exact Or.inr h₁
  . exact Or.inr <| TC.trans a b c h₁ h₂

-- TODO: Is there a simpler way to prove this?
theorem single_reduce_get {s s' : System spec} (r : s.reduces_single s') :
  ∀ i : s'.ThreadIndex, ∃ (j : s.ThreadIndex) (state : spec.State),
  s.threads.get j = s'.threads.get i ∨
  (s.threads.get j).iterate s.state = Thread.IterationResult.Running state (s'.threads.get i) :=by
  intro i
  apply Exists.elim r ; intro thread_idx h
  simp only [iterate] at h
  cases h' : Thread.iterate (List.get s.threads thread_idx) s.state
  all_goals (
    simp only [h'] at h ; clear h'
    have :=Eq.symm <| congrArg (λ (s : System spec) => s.threads) h
    simp only [] at this
    clear h
  )
  . have :=list_helper s.threads s'.threads thread_idx.val this i
    apply this.elim ; intro j h ; exists j
    exists s.state
    exact Or.inl h.symm
  . have :=list_helper s.threads s'.threads thread_idx.val this i
    apply this.elim ; intro j h ; exists j
    exists s.state
    exact Or.inl h.symm
  . cases Decidable.em (thread_idx.val = i.val) <;> rename_i h
    . rw [h] at this
      
      sorry
    . sorry
where
  list_helper {T : Type 1} (l l' : List T) (e : Nat) (h : l' = l.eraseIdx e) :
    ∀ i : Fin l'.length, ∃ j : Fin l.length, l'.get i = l.get j :=sorry

/-- Central validation predicate for reasoning about systems.

  A valid system has the following property: Given any future
  iteration of the system (or the system itself), the following
  holds:
  * No threads have panicked yet (and they never will)
  * The combination of state and thread reservations are valid
    according to the specification
-/
def valid (s : System spec) : Prop :=
  ∀ s' : System spec, s.reduces_to_or_eq s' →
  s'.panics = 0 ∧ spec.validate s'.reservations s'.state

theorem fundamental_validation_theorem (s : System spec)
  (no_panics_yet : s.panics = 0)
  (initial_valid : spec.validate s.reservations s.state)
  (threads_valid : ∀ idx : s.ThreadIndex, (s.threads.get idx).valid)
  : s.valid :=by
  intro s' s_reduces_or_eq_to_s'
  cases s_reduces_or_eq_to_s' <;> rename_i h
  . rw [<- h]
    exact ⟨no_panics_yet, initial_valid⟩
  
  suffices
    (∀ idx : s'.ThreadIndex, (s'.threads.get idx).valid) ∧
    s'.panics = 0 ∧ Spec.validate spec (reservations s') s'.state
     from this.right

  induction h
  . clear s s' ; rename_i s s' s_single_reduces_to_s'
    constructor
    . intro i
      apply Exists.elim <| single_reduce_get s_single_reduces_to_s' i
      intro j h
      apply Exists.elim h ; clear h ; intro state h
      apply Or.elim h <;> (clear h ; intro h)
      . rw [<- h] ; exact threads_valid j
      . have :=threads_valid j
        have :=(Thread.valid.def (List.get s.threads j)).mp this s.state (s.other_reservations j)
        rw [h] at this
        simp only [] at this
        rw [<- decompose_reservation s j] at this
        exact (this initial_valid).right
    constructor
    . sorry
    . sorry
  . rename_i IHab IHbc
    have :=IHab no_panics_yet initial_valid threads_valid
    exact IHbc this.right.left this.right.right this.left

end System

end Mt
