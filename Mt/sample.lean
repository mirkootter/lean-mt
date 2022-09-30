import Mt.Reservation
import Mt.Task
import Mt.System

structure State where
  x : Nat
  y : Nat

structure Reservation where
  luft  : Nat
  min_x : Mt.LowerBound

-- [begin] this block will be provided by a `derive` handler in the future --
-----------------------------------------------------------------------------
instance : Add Reservation :=⟨fun ⟨luft, min_x⟩ ⟨luft', min_x'⟩ => ⟨luft + luft', min_x + min_x'⟩⟩

private theorem Reservation.add_rw : ∀ a b : Reservation, a + b = ⟨a.luft + b.luft, a.min_x + b.min_x⟩ :=
  by intros ; rfl

instance ReservationInstance : Mt.IsReservation Reservation where
  empty := ⟨Mt.IsReservation.empty, Mt.IsReservation.empty⟩
  assoc :=by intros ; simp only [Reservation.add_rw, Mt.IsReservation.toIsAssociative.assoc]
  comm :=by intros ; simp only [Reservation.add_rw, Mt.IsReservation.toIsCommutative.comm]
  empty_add :=by intros ; simp only [Reservation.add_rw, Mt.IsReservation.empty_add]

-----------------------------------------------------------------------------
-- [end] --------------------------------------------------------------------

def spec : Mt.Spec :={
  State
  Reservation
  validate := fun ⟨luft, min_x⟩ ⟨x, y⟩ => x ≥ y + luft ∧ x ≥ min_x
  reservations_can_be_dropped :=by
    simp only []
    intro r r' state h
    constructor
    . exact calc
        state.y + r.luft ≤ state.y + (r.luft + r'.luft) :=by simp_arith
        _                ≤ state.x                      :=h.left
    . sorry -- TODO
}

open Mt
open Mt.TaskM

def thread1 : TaskM spec Unit :=do
  -- increase x atomically; track luft
  atomic_read_modify λ r s => ⟨
    { r with luft :=r.luft + 1 },
    { s with x :=s.x + 1 }⟩
  
  -- increase y atomically; track luft
  atomic_read_modify λ r s => ⟨
    { r with luft :=r.luft - 1 },
    { s with y :=(s.y : Nat) + 1 }⟩

  let _ <- atomic_read λ r s => ⟨s.y, { r with min_x :=s.y }⟩
  let _ <- atomic_read λ r s => ⟨s.x, r⟩

  -- TODO: assert (px ≥ py)

theorem thread1_valid : thread1.valid_for_reservation' ReservationInstance.empty :=by
  rw [valid_for_reservation']
  apply valid_for_reservation_bind _ _ _ λ (r : spec.Reservation) _ => r.luft = 1
  . -- validate ++x
    apply valid_for_reservation_rm
    intro (s : State) (⟨luft, min_x⟩ : Reservation) initial_valid
    simp only [and_true, spec, IsReservation.empty, Nat.zero_add, Reservation.add_rw]
    simp only [spec, IsReservation.empty, Reservation.add_rw] at initial_valid
    constructor
    . sorry
    . sorry
  sorry