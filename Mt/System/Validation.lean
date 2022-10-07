import Mt.System.Basic
import Mt.System.BasicAux
import Mt.Utils

namespace Mt.System

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

open Utils

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
      apply Exists.elim <| single_reduce_elim s_single_reduces_to_s' t' t'_def
      intro t h
      apply Exists.elim h ; clear h ; intro state h
      apply Or.elim h.right <;> (intro h')
      . rw [<- h'] ; exact threads_valid t h.left
      . have :=threads_valid t h.left
        apply (System.decompose_reservation s h.left).elim
        intro j ⟨_, decompose⟩
        have :=(Thread.valid.def t).mp this (s.other_reservations j) s.state
        rw [h'.right] at this
        rw [<- decompose] at this
        exact (this h'.left initial_valid).right

    apply Exists.elim s_single_reduces_to_s'
    intro i iteration ; rw [<- iteration]
    simp only [iterate]
    generalize t_def : List.get s.threads i = t
    cases block_until : Thread.block_until t (reservations s)
    next =>
      . simp only [ite_false]
        exact ⟨no_panics_yet, initial_valid⟩
    constructor
    . -- show s'.panic = 0, i.e. iterations do not panic
      cases h : Thread.iterate t s.state <;> (simp only [] ; try assumption)
      have :=list_get_in s.threads i ; rw [t_def] at this
      have t_valid :=threads_valid t this

      apply (System.decompose_reservation s this).elim
      intro j ⟨_, decompose⟩

      have :=(Thread.valid.def t).mp t_valid (s.other_reservations j) s.state
      simp only [h, <- decompose] at this
      exact (this block_until initial_valid).elim
    . -- show that state/reservations are still valid after the iteration
      have t_is_sthread :=list_get_in s.threads i ; rw [t_def] at t_is_sthread
      have t_valid :=threads_valid t t_is_sthread
      have decompose :=s.decompose_reservation' i t t_def.symm
      simp only [ite_true]
      cases h : Thread.iterate t s.state <;> (simp only [reservations])
      . have :=(Thread.valid.def t).mp t_valid (s.other_reservations i) s.state
        simp only [h, <- decompose] at this
        
        rename_i r state
        rw [<- other_reservations]
        have :=this block_until initial_valid
        rw [this.right, IsReservation.toIsCommutative.comm,
          IsReservation.empty_add] at this
        exact this.left
      . have :=(Thread.valid.def t).mp t_valid (s.other_reservations i) s.state
        simp only [h, <- decompose] at this
        exact (this block_until initial_valid).elim
      . have :=(Thread.valid.def t).mp t_valid (s.other_reservations i) s.state
        simp only [h, <- decompose] at this
        
        rename_i state cont
        have :=this block_until initial_valid
        
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

end Mt.System