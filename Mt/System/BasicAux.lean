import Mt.Thread.Traced
import Mt.System.Basic
import Mt.Utils.List

namespace Mt.System.Traced

open Utils

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

def sum_reservations (l : List (Traced.TracedThread spec)) : spec.Reservation :=
  l.foldl (λ env_r thread => env_r + thread.reservation) spec.is_reservation.empty 

private def sum_reservations' (start) (l : List (Traced.TracedThread spec)) :=
  l.foldl (λ env_r thread => env_r + thread.reservation) start 

protected theorem sum_reservations.helper (head : Traced.TracedThread spec) (l) :
  sum_reservations (head :: l) = head.reservation + sum_reservations l :=by
  have : ∀ l : List (Traced.TracedThread spec),
    sum_reservations l = sum_reservations' IsReservation.empty l :=fun _ => rfl
  simp only [this] ; clear this
  simp only [add, IsReservation.empty_add]
  rw [assoc]
where
  add (r) (head : Traced.TracedThread spec) (tail)
    : sum_reservations' r (head::tail) = sum_reservations' (r + head.reservation) tail :=by
    simp only [sum_reservations', List.foldl]

  assoc (r : spec.Reservation) (l)
    : sum_reservations' r l = r + sum_reservations' IsReservation.empty l :=by
    revert r
    induction l
    . intro r
      show r = r + IsReservation.empty
      rw [IsReservation.toIsCommutative.comm, IsReservation.empty_add]
    . rename_i head tail IH
      intro r
      simp only [add]
      rw [IH, IsReservation.toIsAssociative.assoc, IsReservation.empty_add]
      rw [IH head.reservation]

protected theorem decompose_reservation (l : List (Traced.TracedThread spec)) (idx : Fin l.length) t :
  t = l.get idx →
  sum_reservations l = sum_reservations (l.eraseIdx idx.val) + t.reservation :=by
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
      simp only [this, List.get, List.eraseIdx, sum_reservations.helper]
      exact IsReservation.toIsCommutative.comm _ _
    . rename_i n
      have idx_ok : n + 1 < (thread :: threads).length :=calc
        n + 1 = idx.val :=h.symm
        _ < _ :=idx.isLt
      have : idx = Fin.mk (n + 1) idx_ok :=Fin.eq_of_val_eq h
      simp only [this, List.get, List.eraseIdx, sum_reservations.helper]
      clear this h idx
      rw [IsReservation.toIsAssociative.assoc]
      apply congrArg (thread.reservation + .)
      exact IH <| Fin.mk n (Nat.le_of_succ_le_succ idx_ok)
  
end Mt.System.Traced