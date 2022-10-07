import Mt.System.Basic
import Mt.Utils

namespace Mt.System

open Utils

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

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
  
protected theorem decompose_reservation' (s : System spec) (thread_idx : s.ThreadIndex) t :
  t = s.threads.get thread_idx →
  s.reservations = (s.other_reservations thread_idx) + t.reservation :=
  System.decompose_reservation'' s.threads thread_idx t

protected theorem decompose_reservation (s : System spec) { t } (t_def : t ∈ s.threads) :
  ∃ idx : s.ThreadIndex, s.threads.get idx = t ∧
  s.reservations = (s.other_reservations idx) + t.reservation :=by
  apply (list_index_exists s.threads t_def).elim
  intro thread_idx idx_correct
  exists thread_idx
  exact ⟨idx_correct, s.decompose_reservation' thread_idx t idx_correct.symm⟩

theorem single_reduce_elim {s s' : System spec} (r : s.reduces_single s') :
  ∀ t', t' ∈ s'.threads → ∃ (t : _) (state : spec.State), t ∈ s.threads ∧ (
  t = t' ∨ (
    t.block_until s.reservations ∧
    t.iterate s.state = Thread.IterationResult.Running state t')) :=by
  intro t' t'_def
  
  apply Exists.elim r ; intro thread_idx h
  cases block_until : Thread.block_until (List.get s.threads thread_idx) s.reservations
  next =>
    . exists t', s.state
      constructor
      . simp only [iterate, block_until, ite_false] at h
        rw [h]
        exact t'_def
      . exact Or.inl rfl
  have :=iterate_threads s thread_idx block_until
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
      . exact Or.inr ⟨block_until, rfl⟩
    . exists t' ; exists state
      exact ⟨h, Or.inl rfl⟩

end Mt.System