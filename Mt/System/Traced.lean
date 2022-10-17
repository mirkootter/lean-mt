import Mt.Thread.Traced
import Mt.System.Basic
import Mt.Utils.List

namespace Mt.Traced

structure TracedSystem (spec : Spec) where
  state   : spec.State
  threads : List (TracedThread spec)
  panics  : Nat

namespace TracedSystem

variable {spec : Spec}

local instance : IsReservation spec.Reservation :=spec.is_reservation

def ThreadIndex (s : TracedSystem spec) : Type :=Fin s.threads.length
def done (s : TracedSystem spec) : Bool :=s.threads.length = 0

def iterate (s : TracedSystem spec) (idx : s.ThreadIndex) : Thread.IterationResult spec :=
  (s.threads.get idx).iterate s.state

def update_thread (s : TracedSystem spec) (idx : Nat) (state : spec.State)
  (r : spec.Reservation) (cont : Thread spec) : TracedSystem spec :={
  state
  threads :=s.threads.set idx ⟨cont, r⟩
  panics :=s.panics
}

def remove_thread (s : TracedSystem spec) (idx : Nat) (state : spec.State)
  : TracedSystem spec :={
  state
  threads :=s.threads.eraseIdx idx
  panics :=s.panics
}

def reservations (s : TracedSystem spec) : spec.Reservation :=
  s.threads.foldl (λ env_r thread => env_r + thread.reservation) spec.is_reservation.empty

def other_reservations (s : TracedSystem spec) (idx : Nat) : spec.Reservation :=
  (s.threads.eraseIdx idx).foldl (λ env_r thread => env_r + thread.reservation) spec.is_reservation.empty

theorem decompose_reservations (s : TracedSystem spec) (idx : s.ThreadIndex) :
  s.reservations = s.other_reservations idx.val + (s.threads.get idx).reservation :=by
  -- TODO
  sorry

structure valid (s : TracedSystem spec) : Prop where
  no_panics_yet : s.panics = 0
  currently_valid : spec.validate s.reservations s.state
  threads_valid : ∀ t, t ∈ s.threads → t.valid 

inductive reduces_to : TracedSystem spec -> TracedSystem spec -> Prop where
| done {s : TracedSystem spec} (idx : s.ThreadIndex) {state}
  (blocked_until : (s.threads.get idx).block_until s.state)
  (iteration : s.iterate idx = Thread.IterationResult.Done state)
  : s.reduces_to (s.remove_thread idx.val state)
| running {s : TracedSystem spec} (idx : s.ThreadIndex) {state r cont}
  (is_valid : spec.validate (s.other_reservations idx.val + r) state)
  (cont_valid : cont.task.valid r cont.block_until λ _ r => r = IsReservation.empty)
  : s.reduces_to (s.update_thread idx.val state r cont)
| trans {a b c : TracedSystem spec} : a.reduces_to b -> b.reduces_to c -> a.reduces_to c

theorem valid_forever {s s': TracedSystem spec} :
  s.valid -> s.reduces_to s' -> s'.valid :=by
  intro ⟨no_panics_yet, currently_valid, threads_valid⟩
  intro s_to_s'
  induction s_to_s' <;> clear s s'
  . rename_i s idx state blocked_until iteration
    constructor
    . exact no_panics_yet
    . let t :=s.threads.get idx
      have t_valid :=threads_valid t (Utils.List.get_in ..)
      conv at iteration =>
        simp only [iterate]
        arg 1 ; arg 1 ; change t
      let env_r :=(s.remove_thread idx.val state).reservations
      have decompose 
        : s.reservations = env_r + _
        :=s.decompose_reservations idx
      rw [decompose] at currently_valid
      have :=TracedThread.valid_elim t_valid env_r s.state blocked_until currently_valid
      cases this
      rename_i r t_valid
      simp only [iteration] at t_valid
      have := t_valid.left
      rw [t_valid.right, IsReservation.toIsCommutative.comm, IsReservation.empty_add] at this
      exact this
    . intro t t_hyp
      exact threads_valid t <| Utils.List.erase_subset s.threads idx.val t_hyp
  . rename_i s idx state r cont is_valid cont_valid
    constructor
    . exact no_panics_yet
    . let s' :=s.update_thread idx.val state r cont
      have s'_def : s' = s.update_thread idx.val state r cont :=rfl
      rw [<- s'_def]
      let idx' : s'.ThreadIndex :=⟨idx.val, by calc
        idx.val < s.threads.length :=idx.isLt
              _ = s'.threads.length :=Eq.symm <| List.length_set ..⟩
      have decompose :=s'.decompose_reservations idx'

      conv at decompose =>
        rhs
        conv =>
          arg 1
          simp only [other_reservations, update_thread, Utils.List.erase_set]
        conv =>
          arg 2
          simp only [update_thread, Utils.List.get_of_set]
        
      rw [decompose]
      exact is_valid
    . intro t' t'_hyp
      cases Utils.List.set_subset s.threads idx.val _ t'_hyp
      <;> rename_i t'_hyp
      . rw [t'_hyp]
        exact cont_valid
      . exact threads_valid t' t'_hyp
    
  . rename_i a b _ _ _ IHab IHbc
    have b_valid :=IHab no_panics_yet currently_valid threads_valid
    exact IHbc b_valid.no_panics_yet b_valid.currently_valid b_valid.threads_valid

def to_system (s : TracedSystem spec) : System spec :={
  state := s.state
  threads := s.threads.map λ ⟨t, _⟩ => t
  panics := s.panics
}

def mk_initial (s : System spec) : TracedSystem spec :={
  state := s.state
  threads := s.threads.map λ t => ⟨t, IsReservation.empty⟩
  panics := s.panics
}

theorem mk_initial.valid (s : System spec)
  (no_panics_yet : s.panics = 0)
  (initial_valid : spec.validate IsReservation.empty s.state)
  (threads_valid : ∀ t, t ∈ s.threads → t.valid)
  : (mk_initial s).valid :=by
  constructor
  . exact no_panics_yet
  . simp only [mk_initial]
    induction s.threads
    . exact initial_valid
    . rename_i head tail IH
      simp only [List.map, Traced.TracedSystem.reservations, List.foldl, IsReservation.empty_add]
      exact IH
  . intro t t_hyp
    simp only [mk_initial] at t_hyp
    cases Utils.List.eq_of_in_map t_hyp
    rename_i t_orig t_orig_hyp
    rw [t_orig_hyp.right]
    exact threads_valid t_orig t_orig_hyp.left

theorem mk_initial.cancels_to_system {s : System spec} :
  (mk_initial s).to_system = s :=by
  simp only [mk_initial, to_system]
  rw [System.mk.injEq]
  constructor
  . rfl
  constructor
  . induction s.threads
    . rfl
    . rename_i head tail IH
      simp only [List.map]
      rw [IH]
  . rfl

theorem reduces_by_iteration (s s' : System spec)
  {idx : s.ThreadIndex}
  {ts : TracedSystem spec}
  (has_traced_system : s = ts.to_system)
  (iteration : s.iterate idx = s')
  (neq : s ≠ s')
  : ∃ ts' : TracedSystem spec,
    ts'.to_system = s' ∧ ts.reduces_to ts' :=by
  simp only [System.iterate] at iteration
  cases h : (s.threads.get idx).block_until s.state
  <;> simp only [h, ite_true, ite_false] at iteration
  . contradiction
  have blocked_until :=h ; clear h
  cases h : (s.threads.get idx).iterate s.state
  <;> simp only [h] at iteration
  . rename_i state
    exists ts.remove_thread idx.val state
    rw [<- iteration]
    simp only [remove_thread]
    constructor
    . simp only [to_system, has_traced_system, System.mk.injEq, and_true, true_and]
      -- TODO: Simple
      sorry
    . apply reduces_to.done ⟨idx.val, _⟩
      . sorry
      . simp only [iterate, TracedThread.iterate]
        sorry
      . sorry
  . sorry
  . sorry

end TracedSystem

end Mt.Traced