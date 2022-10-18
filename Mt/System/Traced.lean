import Mt.Thread.Traced
import Mt.System.Basic
import Mt.System.BasicAux
import Mt.Utils.List

namespace Mt.Traced

structure TracedSystem (spec : Spec) where
  state   : spec.State
  threads : List (TracedThread spec)

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
}

def remove_thread (s : TracedSystem spec) (idx : Nat) (state : spec.State)
  : TracedSystem spec :={
  state
  threads :=s.threads.eraseIdx idx
}

def reservations (s : TracedSystem spec) : spec.Reservation :=
  s.threads.foldl (λ env_r thread => env_r + thread.reservation) spec.is_reservation.empty

def other_reservations (s : TracedSystem spec) (idx : Nat) : spec.Reservation :=
  (s.threads.eraseIdx idx).foldl (λ env_r thread => env_r + thread.reservation) spec.is_reservation.empty

theorem decompose_reservations (s : TracedSystem spec) (idx : s.ThreadIndex) :
  s.reservations = s.other_reservations idx.val + (s.threads.get idx).reservation :=
  System.Traced.decompose_reservation s.threads idx _ rfl

structure valid (s : TracedSystem spec) : Prop where
  currently_valid : spec.validate s.reservations s.state
  threads_valid : ∀ t, t ∈ s.threads → t.valid 

def to_system (s : TracedSystem spec) : System spec :={
  state := s.state
  threads := s.threads.map λ ⟨t, _⟩ => t
  panics := 0
}

def mk_initial (s : System spec) : TracedSystem spec :={
  state := s.state
  threads := s.threads.map λ t => ⟨t, IsReservation.empty⟩
}

theorem mk_initial.valid (s : System spec)
  (initial_valid : spec.validate IsReservation.empty s.state)
  (threads_valid : ∀ t, t ∈ s.threads → t.valid)
  : (mk_initial s).valid :=by
  constructor
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

theorem mk_initial.cancels_to_system {s : System spec}
  (no_panics_yet : s.panics = 0)
  :
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
  . exact no_panics_yet.symm

theorem valid_by_iteration (s s' : System spec)
  {idx : s.ThreadIndex}
  {ts : TracedSystem spec}
  (has_traced_system : s = ts.to_system)
  (ts_valid : ts.valid)
  (iteration : s.iterate idx = s')
  : ∃ ts' : TracedSystem spec,
    ts'.to_system = s' ∧ ts'.valid :=by
  
  simp only [System.iterate] at iteration
  cases blocked_until : (s.threads.get idx).block_until s.state
  <;> simp only [blocked_until, ite_true, ite_false] at iteration
  . exists ts
    simp only [<- iteration, has_traced_system, ts_valid]
  
  have ts_state_eq : ts.state = s.state :=by rw [has_traced_system] ; rfl

  let idx' : ts.ThreadIndex :=Utils.Fin.cast idx (by
    rw [has_traced_system]
    exact List.length_map ..)
  have get_idx' : (ts.threads.get idx').thread = s.threads.get idx :=by
    have :=congrArg System.threads has_traced_system
    rw [Utils.List.get_congr idx this]
    simp only [to_system, Utils.List.get_of_map]
    rfl
  
  let env_r :=ts.other_reservations idx.val
  have decompose : ts.reservations = env_r + _ :=ts.decompose_reservations idx'

  have t_valid :=TracedThread.valid_elim
    (ts_valid.threads_valid (ts.threads.get idx') (Utils.List.get_in ..))
    env_r s.state
    (by
      simp only [TracedThread.block_until, get_idx']
      exact blocked_until)
    (by
      rw [<- decompose, <- ts_state_eq]
      exact ts_valid.currently_valid)
  cases t_valid
  rename_i r' t_valid
  rw [TracedThread.iterate, get_idx'] at t_valid

  cases h : (s.threads.get idx).iterate s.state
  <;> simp only [h] at iteration
  <;> simp only [h] at t_valid

  . rename_i state
    exists ts.remove_thread idx.val state
    rw [<- iteration] ; clear iteration s'
    simp only [remove_thread]
    constructor
    . simp only [to_system, has_traced_system, System.mk.injEq, and_true, true_and]
      exact Utils.List.erase_map_commutes ..
    . rw [t_valid.right, IsReservation.toIsCommutative.comm, IsReservation.empty_add] at t_valid
      constructor
      . exact t_valid.left
      . intro t (t_hyp : t ∈ ts.threads.eraseIdx idx.val)
        exact ts_valid.threads_valid t <| Utils.List.erase_subset _ _ t_hyp
  . rename_i state cont
    exists ts.update_thread idx.val state r' cont
    rw [<- iteration] ; clear iteration s'
    simp only [update_thread]
    constructor
    . simp only [to_system, System.mk.injEq, true_and, has_traced_system, and_true]
      exact Utils.List.set_map_commutes ..
    . constructor
      . let ts' :=ts.update_thread idx.val state r' cont
        show spec.validate ts'.reservations ts'.state
        
        let idx'' : ts'.ThreadIndex :=⟨idx.val, by calc
          idx.val < ts.threads.length :=idx'.isLt
                _ = ts'.threads.length :=Eq.symm <| List.length_set ..⟩
        have decompose' :=ts'.decompose_reservations idx''

        conv at decompose' =>
          rhs
          conv =>
            arg 1
            simp only [other_reservations, update_thread, Utils.List.erase_set]
          conv =>
            arg 2
            simp only [update_thread, Utils.List.get_of_set]
          arg 1
          change env_r
        
        rw [decompose']
        exact t_valid.left
      . intro t (t_hyp : t ∈ ts.threads.set idx.val ⟨cont, r'⟩)
        cases Utils.List.set_subset _ _ _ t_hyp <;> rename_i t_hyp
        . rw [t_hyp]
          exact t_valid.right
        . exact ts_valid.threads_valid t t_hyp

end TracedSystem

end Mt.Traced