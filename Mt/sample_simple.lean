import Mt.Reservation
import Mt.Task
import Mt.System

structure State where
  x : Nat
  y : Nat

def spec : Mt.Spec :={
  State
  Reservation :=Nat
  validate := fun (luft : Nat) ⟨x, y⟩ => x ≥ y + luft
}

open Mt
open Mt.TaskM

def thread1 : TaskM spec Unit :=do
  -- increase x atomically; track luft
  atomic_read_modify λ _ s => ⟨(1 : Nat), { s with x := s.x + 1 }⟩
  
  -- increase y atomically; track luft
  atomic_read_modify λ _ s => ⟨(0 : Nat), { s with y := s.y + 1 }⟩

  atomic_assert fun ⟨x, y⟩ => x ≥ y

theorem thread1_valid : thread1.valid_for_reservation' (0 : Nat) :=by
  rw [valid_for_reservation']
  apply valid_for_reservation_bind (spec :=spec) _ _ _ (λ _ => true) λ (luft : Nat) _ => luft = 1
  . -- validate ++x
    ---------------
    apply valid_for_reservation_rm
    intro ⟨x, y⟩ (env_luft : Nat) initial_valid
    simp only [and_true]

    have : x ≥ y + env_luft :=initial_valid
    show x + 1 ≥ y + env_luft + 1

    exact Nat.succ_le_succ (by assumption)
  
  intro (luft : Nat) ⟨⟩ luft_def
  apply valid_for_reservation_bind (spec :=spec) _ _ _ (λ _ => true) λ (luft : Nat) _ => luft = 0
  . -- validate ++y knowing luft = 1
    --------------------------------
    apply valid_for_reservation_rm
    intro ⟨x, y⟩ (env_luft : Nat) initial_valid
    simp only [and_true]

    rw [luft_def] at initial_valid

    have : x ≥ y + env_luft + 1 :=initial_valid
    show x ≥ y + 1 + env_luft

    rw [Nat.add_right_comm] ; assumption
  
  clear luft luft_def
  intro (luft : Nat) ⟨⟩ luft_def
  apply valid_for_reservation_assert (spec :=spec) _ _ _ luft_def
  . -- validate `assert x ≥ y`
    ----------------------------
    intro ⟨x, y⟩ (env_luft : Nat) initial_valid _

    have : x ≥ y + (env_luft + luft) :=initial_valid
    show decide (x ≥ y) = true

    exact decide_eq_true <| calc
      y ≤ y + (env_luft + luft) :=by simp_arith
      _ ≤ x                     :=by assumption
