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
    intro ⟨env_luft, (env_min_x : Nat)⟩ ⟨luft, (min_x : Nat)⟩ ⟨x, y⟩
      (h : x ≥ y + (env_luft + luft) ∧ x ≥ Nat.max env_min_x min_x)

    show x ≥ y + env_luft ∧ x ≥ env_min_x

    cases h ; constructor
    . show x ≥ y + env_luft
      exact calc
        y + env_luft ≤ y + (env_luft + luft) :=by simp_arith
                   _ ≤ x                     :=by assumption
    . show x ≥ env_min_x
      rename x ≥ Nat.max env_min_x min_x => h
      exact (nat_max_le.mp h).left 
}

open Mt
open Mt.TaskM

def thread1 : TaskM spec Unit :=do
  -- increase x atomically; track luft
  atomic_read_modify λ r s => ⟨
    { r with luft := 1 },
    { s with x := s.x + 1 }⟩
  
  -- increase y atomically; track luft
  atomic_read_modify λ r s => ⟨
    { r with luft := 0 },
    { s with y := s.y + 1 }⟩

  let _ <- atomic_read λ _ ⟨_, y⟩ => ⟨y, Reservation.mk 0 y⟩
  let _ <- atomic_read λ _ ⟨x, _⟩ => ⟨x, ReservationInstance.empty⟩

  -- TODO: assert (px ≥ py)

theorem thread1_valid : thread1.valid_for_reservation' ReservationInstance.empty :=by
  rw [valid_for_reservation']
  apply valid_for_reservation_bind _ _ _ λ (r : spec.Reservation) _ => r.luft = 1
  . -- validate ++x
    ---------------
    apply valid_for_reservation_rm
    intro ⟨x, y⟩ ⟨env_luft, env_min_x⟩ initial_valid
    simp only [and_true]

    have : x ≥ y + env_luft ∧ x ≥ Nat.max env_min_x 0 :=initial_valid
    show x + 1 ≥ y + (env_luft + 1) ∧ x + 1 ≥ Nat.max env_min_x 0

    cases this ; constructor
    . show y + (env_luft + 1) ≤ x + 1
      calc
        _ = y + env_luft + 1 :=rfl
        _ ≤ x + 1            :=Nat.succ_le_succ (by assumption)
    . show Nat.max env_min_x 0 ≤ x + 1
      exact calc
        _ ≤ x     :=by assumption
        x ≤ x + 1 :=Nat.le_succ _
  
  intro ⟨luft, min_x⟩ ⟨⟩ luft_def
  apply valid_for_reservation_bind _ _ _ λ _ _ => True
  . -- validate ++y knowing luft = 1
    --------------------------------
    have luft_def : luft = 1 :=luft_def
    apply valid_for_reservation_rm
    intro ⟨x, y⟩ ⟨env_luft, env_min_x⟩ initial_valid
    simp only [and_true]
    rw [luft_def] at initial_valid

    have : x ≥ y + env_luft + 1 ∧ x ≥ env_min_x + min_x :=initial_valid
    show x ≥ y + 1 + env_luft ∧ x ≥ env_min_x + min_x

    cases this ; constructor <;> try assumption
    . show x ≥ y + 1 + env_luft
      rw [Nat.add_right_comm] ; assumption
  
  clear luft min_x luft_def
  intro ⟨luft, min_x⟩ ⟨⟩ ⟨⟩
  apply valid_for_reservation_bind (spec :=spec) _ _ _ λ ⟨_, min_x⟩ y => min_x = y
  . -- validate `let py = y` with `min_x := py`
    -------------------------------------------
    apply valid_for_reservation_read
    intro ⟨x, y⟩ ⟨env_luft, (env_min_x : Nat)⟩ initial_valid
    simp only [and_true]

    have : x ≥ y + (env_luft + luft) ∧ x ≥ Nat.max env_min_x min_x :=initial_valid
    show x ≥ y + env_luft ∧ x ≥ Nat.max env_min_x y

    cases this ; constructor
    . show y + env_luft ≤ x
      exact calc
        y + env_luft ≤ y + (env_luft + luft) :=by simp_arith
                   _ ≤ x                     :=by assumption
    . show Nat.max env_min_x y ≤ x
      apply nat_max_le.mpr ; constructor
      . show env_min_x ≤ x
        rename x ≥ Nat.max env_min_x min_x => h
        exact (nat_max_le.mp h).left
      . show y ≤ x
        exact calc
          y ≤ y + (env_luft + luft) :=by simp_arith
          _ ≤ x                     :=by assumption

  clear luft min_x
  intro ⟨luft, min_x⟩ (py : Nat) min_x_def
  apply valid_for_reservation_bind (spec :=spec) _ _ _ λ _ x => x ≥ py
  . -- validate `let px = x` knowing min_x = py
    -------------------------------------------
    have min_x_def : min_x = py :=min_x_def
    apply valid_for_reservation_read
    intro ⟨x, y⟩ ⟨env_luft, (env_min_x : Nat)⟩ initial_valid

    have : x ≥ y + (env_luft + luft) ∧ x ≥ Nat.max env_min_x min_x :=initial_valid
    show (x ≥ y + env_luft ∧ x ≥ Nat.max env_min_x 0) ∧ x ≥ py
    
    cases this ; constructor ; constructor
    . show y + env_luft ≤ x
      calc
        y + env_luft ≤ y + (env_luft + luft) :=by simp_arith
                   _ ≤ x                     :=by assumption
    . show x ≥ Nat.max env_min_x 0
      rw [nat_max_zero]
      rename x ≥ Nat.max env_min_x min_x => h
      exact (nat_max_le.mp h).left
    . show x ≥ py
      suffices x ≥ min_x by rw [<- min_x_def] ; assumption
      rename x ≥ Nat.max env_min_x min_x => h
      exact (nat_max_le.mp h).right
  
  clear luft min_x min_x_def
  intro ⟨luft, min_x⟩ (px : Nat) px_gt_py

  have : px ≥ py :=px_gt_py -- for the assertion

  exact valid_for_reservation_pure (spec :=spec) _ _ (λ _ _ => True) ⟨⟩