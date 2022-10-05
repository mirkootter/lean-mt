import Mt.Task

-- utils
theorem list_get_in {T : Type u} (l : List T) (idx : Fin l.length)
  : (l.get idx) ∈ l :=match l, idx with
  | a::_, ⟨0, _⟩ => List.Mem.head a _
  | _::as, ⟨n + 1, isLt⟩ => List.Mem.tail _ <| list_get_in as ⟨n, Nat.le_of_succ_le_succ isLt⟩

theorem list_get_of_set {T : Type u} (l : List T) (idx : Nat) (a : T)
  (isLt : idx < (l.set idx a).length)
  : (l.set idx a).get ⟨idx, isLt⟩ = a :=match l, idx with
  | _::_, 0 => rfl
  | _::xs, n + 1 => list_get_of_set xs n a <| Nat.lt_of_succ_lt_succ isLt

theorem list_erase_subset {T : Type u} {a : T} (l : List T) (idx : Nat) 
  : a ∈ (l.eraseIdx idx) → a ∈ l :=match l, idx with
  | [], _ => id
  | x::xs, 0 => fun h => List.Mem.tail _ h
  | x::xs, n+1 => by
    intro h ; cases h
    . exact List.Mem.head ..
    . exact List.Mem.tail x <| list_erase_subset xs n (by assumption)

theorem list_set_subset {T : Type u} {a : T} (l : List T) (idx : Nat) (new_value : T)
  : a ∈ (l.set idx new_value) → a = new_value ∨ a ∈ l :=match l, idx with
  | [], _ => Or.inr
  | x::xs, 0 => by
    intro h ; cases h
    . exact Or.inl rfl
    . exact Or.inr <| List.Mem.tail _ (by assumption)
  | x::xs, n+1 => by
    intro h ; cases h
    . exact Or.inr <| List.Mem.head ..
    . cases list_set_subset xs n new_value (by assumption)
      . exact Or.inl (by assumption)
      . exact Or.inr <| List.Mem.tail _ (by assumption)

theorem list_index_exists {T : Type u} {a : T} (l : List T)
  : a ∈ l → ∃ i : Fin l.length, l.get i = a :=fun a_in_l => match l, a_in_l with
    | x::xs, a_in_l => by
      cases a_in_l
      . exists ⟨0, by simp_arith⟩
      . apply (list_index_exists xs (by assumption)).elim
        intro i xs_get_i
        exists ⟨i.val + 1, by simp_arith only [List.length] ; exact i.isLt⟩

theorem erase_set {T : Type u} (l : List T) (idx : Nat) (new_value : T)
  : (l.set idx new_value).eraseIdx idx = l.eraseIdx idx :=match l, idx with
  | [], _ => rfl
  | _::_, 0 => rfl
  | x::xs, n+1 => congrArg (x :: .) <| erase_set xs n new_value

namespace Mt

structure Thread (spec : Spec) where
  T : Type
  reservation : spec.Reservation
  wait_for : spec.Reservation -> Bool
  task : TaskM spec T

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

def mk_thread {T : Type} (task : TaskM spec T) : Thread spec := {
  T
  reservation := IsReservation.empty
  wait_for :=λ _ => true
  task }

namespace Thread

def valid (thread : Thread spec) : Prop :=
  thread.task.valid_for_reservation thread.reservation
    (λ r _ => r = IsReservation.empty)
    thread.wait_for

inductive IterationResult (spec : Spec) where
  | Done : spec.Reservation -> spec.State -> IterationResult spec
  | Panic : spec.Reservation -> spec.State -> IterationResult spec
  | Running : spec.State -> Thread spec ->
      IterationResult spec

def IterationResult.state : IterationResult spec -> spec.State
  | Done _ state => state
  | Panic _ state => state
  | Running state _ => state

def IterationResult.reservation : IterationResult spec -> spec.Reservation
  | Done r _ => r
  | Panic r _ => r
  | Running _ cont => cont.reservation

def iterate : Thread spec -> spec.State -> IterationResult spec
  | ⟨T, r, _, task⟩, state =>
    match task.iterate r state with
    | TaskM.IterationResult.Done r state' _ => IterationResult.Done r state'
    | TaskM.IterationResult.Panic r state' _ => IterationResult.Panic r state'
    | TaskM.IterationResult.Continuation reservation state' wait_for task => 
      IterationResult.Running state' { T, reservation, wait_for, task }

theorem valid.def (thread : Thread spec) :
  thread.valid = 
    ∀ (state : spec.State) (env_r : spec.Reservation),
    thread.wait_for (env_r + thread.reservation) →
    spec.validate (env_r + thread.reservation) state →
    match thread.iterate state with
      | IterationResult.Done r' state' =>
          spec.validate (env_r + r') state' ∧
          r' = IsReservation.empty
      | IterationResult.Panic .. => False
      | IterationResult.Running state' cont =>
        (spec.validate (env_r + cont.reservation) state') ∧ cont.valid :=by
  simp only [valid, iterate]
  rw [TaskM.valid_for_reservation.def]
  apply forall_ext ; intro state
  apply forall_ext ; intro env_r
  cases TaskM.iterate thread.task thread.reservation state
  <;> simp only [and_true]

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

protected theorem decompose_reservation'' (l : List (Thread spec)) (idx : Fin l.length) t :
  t = l.get idx →
  System.sum_reservations l = System.sum_reservations (l.eraseIdx idx.val) + t.reservation :=by
  intro t_def ; rw [t_def]  ; clear t_def
  revert idx

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

  
theorem decompose_reservation' (s : System spec) (thread_idx : s.ThreadIndex) t :
  t = s.threads.get thread_idx →
  s.reservations = (s.other_reservations thread_idx) + t.reservation :=
  System.decompose_reservation'' s.threads thread_idx t

theorem decompose_reservation (s : System spec) { t } (t_def : t ∈ s.threads) :
  ∃ idx : s.ThreadIndex, s.threads.get idx = t ∧
  s.reservations = (s.other_reservations idx) + t.reservation :=by
  apply (list_index_exists s.threads t_def).elim
  intro thread_idx idx_correct
  exists thread_idx
  exact ⟨idx_correct, s.decompose_reservation' thread_idx t idx_correct.symm⟩

def iterate (s : System spec) : s.ThreadIndex -> System spec
  | thread_idx =>
    if (s.threads.get thread_idx).wait_for (s.reservations) then 
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
    else
      s

theorem iterate_threads (s : System spec) (thread_idx : s.ThreadIndex)
  (waited_for : (s.threads.get thread_idx).wait_for s.reservations) :
  (s.iterate thread_idx).threads =
    match (s.threads.get thread_idx).iterate s.state with
      | Thread.IterationResult.Done .. => s.threads.eraseIdx thread_idx.val
      | Thread.IterationResult.Panic .. => s.threads.eraseIdx thread_idx.val
      | Thread.IterationResult.Running _ thread => s.threads.set thread_idx.val thread :=by
  rw [iterate]
  simp only [waited_for, ite_true]
  cases h : Thread.iterate (List.get s.threads thread_idx) s.state <;> rfl

theorem iterate_panics (s : System spec) (thread_idx : s.ThreadIndex)
  (waited_for : (s.threads.get thread_idx).wait_for s.reservations) :
  (s.iterate thread_idx).panics =
    match (s.threads.get thread_idx).iterate s.state with
      | Thread.IterationResult.Done .. => s.panics
      | Thread.IterationResult.Panic .. => s.panics + 1
      | Thread.IterationResult.Running .. => s.panics :=by
  rw [iterate]
  simp only [waited_for, ite_true]
  cases h : Thread.iterate (List.get s.threads thread_idx) s.state <;> rfl

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

theorem single_reduce_get {s s' : System spec} (r : s.reduces_single s') :
  ∀ t', t' ∈ s'.threads → ∃ (t : _) (state : spec.State), t ∈ s.threads ∧ (
  t = t' ∨ (
    t.wait_for s.reservations ∧
    t.iterate s.state = Thread.IterationResult.Running state t')) :=by
  intro t' t'_def
  
  apply Exists.elim r ; intro thread_idx h
  cases wait_for : Thread.wait_for (List.get s.threads thread_idx) s.reservations
  next =>
    . exists t', s.state
      constructor
      . simp only [iterate, wait_for, ite_false] at h
        rw [h]
        exact t'_def
      . exact Or.inl rfl
  have :=iterate_threads s thread_idx wait_for
  rw [h] at this ; clear h
  cases h' : Thread.iterate (List.get s.threads thread_idx) s.state
  all_goals (rw [h'] at this ; simp only [] at this)
  . have :=list_erase_subset s.threads thread_idx.val (this.subst t'_def)
    exists t' ; exists s.state
    exact ⟨this, Or.inl rfl⟩
  . have :=list_erase_subset s.threads thread_idx.val (this.subst t'_def)
    exists t' ; exists s.state
    exact ⟨this, Or.inl rfl⟩
  . rename_i state cont
    cases list_set_subset s.threads thread_idx.val cont (this.subst t'_def) <;> rename_i h
    . rw [h]
      exists List.get s.threads thread_idx
      exists state
      rw [<- h']
      constructor
      . exact list_get_in ..
      . exact Or.inr ⟨wait_for, rfl⟩
    . exists t' ; exists state
      exact ⟨h, Or.inl rfl⟩

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
  (threads_valid : ∀ t, t ∈ s.threads → t.valid)
  : s.valid :=by
  intro s' s_reduces_or_eq_to_s'
  cases s_reduces_or_eq_to_s' <;> rename_i h
  . rw [<- h]
    exact ⟨no_panics_yet, initial_valid⟩
  
  suffices
    (∀ t', t' ∈ s'.threads → t'.valid) ∧
    s'.panics = 0 ∧ Spec.validate spec (reservations s') s'.state
     from this.right

  induction h
  . clear s s' ; rename_i s s' s_single_reduces_to_s'
    
    

    constructor
    . -- show that threads are still valid after iteration
      intro t' t'_def
      apply Exists.elim <| single_reduce_get s_single_reduces_to_s' t' t'_def
      intro t h
      apply Exists.elim h ; clear h ; intro state h
      apply Or.elim h.right <;> (intro h')
      . rw [<- h'] ; exact threads_valid t h.left
      . have :=threads_valid t h.left
        apply (decompose_reservation s h.left).elim
        intro j ⟨_, decompose⟩
        have :=(Thread.valid.def t).mp this s.state (s.other_reservations j)
        rw [h'.right] at this
        rw [<- decompose] at this
        exact (this h'.left initial_valid).right

    apply Exists.elim s_single_reduces_to_s'
    intro i iteration ; rw [<- iteration]
    simp only [iterate]
    generalize t_def : List.get s.threads i = t
    cases wait_for : Thread.wait_for t (reservations s)
    next =>
      . simp only [ite_false]
        exact ⟨no_panics_yet, initial_valid⟩
    constructor
    . -- show s'.panic = 0, i.e. iterations do not panic
      cases h : Thread.iterate t s.state <;> (simp only [] ; try assumption)
      have :=list_get_in s.threads i ; rw [t_def] at this
      have t_valid :=threads_valid t this

      apply (decompose_reservation s this).elim
      intro j ⟨_, decompose⟩

      have :=(Thread.valid.def t).mp t_valid s.state (s.other_reservations j)
      simp only [h, <- decompose] at this
      exact (this wait_for initial_valid).elim
    . -- show that state/reservations are still valid after the iteration
      have t_is_sthread :=list_get_in s.threads i ; rw [t_def] at t_is_sthread
      have t_valid :=threads_valid t t_is_sthread
      have decompose :=s.decompose_reservation' i t t_def.symm
      simp only [ite_true]
      cases h : Thread.iterate t s.state <;> (simp only [reservations])
      . have :=(Thread.valid.def t).mp t_valid s.state (s.other_reservations i)
        simp only [h, <- decompose] at this
        
        rename_i r state
        rw [<- other_reservations]
        have :=this wait_for initial_valid
        rw [this.right, IsReservation.toIsCommutative.comm,
          IsReservation.empty_add] at this
        exact this.left
      . have :=(Thread.valid.def t).mp t_valid s.state (s.other_reservations i)
        simp only [h, <- decompose] at this
        exact (this wait_for initial_valid).elim
      . have :=(Thread.valid.def t).mp t_valid s.state (s.other_reservations i)
        simp only [h, <- decompose] at this
        
        rename_i state cont
        have :=this wait_for initial_valid
        
        have temp :=System.decompose_reservation''
          (List.set s.threads i.val cont)
          ⟨i.val, calc
            i.val < s.threads.length :=i.isLt
            _ = (List.set s.threads i.val cont).length :=by simp
          ⟩
          cont
          (Eq.symm <| list_get_of_set s.threads i.val cont _)
        rw [temp] ; clear temp
        simp only [erase_set]
        rw [<- other_reservations]
        exact this.left
  . rename_i IHab IHbc
    have :=IHab no_panics_yet initial_valid threads_valid
    exact IHbc this.right.left this.right.right this.left

end System

end Mt
