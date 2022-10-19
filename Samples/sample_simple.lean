import Mt.Reservation
import Mt.Thread

namespace SampleSimple

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

def thread1 : Thread spec :=mk_thread do
  -- increase x atomically
  atomic_read_modify λ s => { s with x := s.x + 1 }
  
  -- increase y atomically
  atomic_read_modify λ s => { s with y := s.y + 1 }

  atomic_assert fun ⟨x, y⟩ => x ≥ y

theorem thread1_valid : thread1.valid :=by
  rw [Thread.valid]
  apply valid_bind (spec :=spec) λ _ (luft : Nat) => luft = 1
  . -- validate ++x
    ---------------
    apply valid_rm
    intro (env_luft : Nat) ⟨x, y⟩ _ initial_valid
    exists (1 : Nat)
    simp only [and_true]

    have : x ≥ y + env_luft :=initial_valid
    show x + 1 ≥ y + env_luft + 1

    exact Nat.succ_le_succ (by assumption)
  
  intro (luft : Nat) ⟨⟩ luft_def
  apply valid_bind (spec :=spec) λ _ (luft : Nat) => luft = 0
  . -- validate ++y knowing luft = 1
    --------------------------------
    apply valid_rm
    intro (env_luft : Nat) ⟨x, y⟩ _ initial_valid
    exists (0 : Nat)
    simp only [and_true]

    rw [luft_def] at initial_valid

    have : x ≥ y + env_luft + 1 :=initial_valid
    show x ≥ y + 1 + env_luft

    rw [Nat.add_right_comm] ; assumption
  
  clear luft luft_def
  intro (luft : Nat) ⟨⟩ luft_def
  apply valid_assert (spec :=spec) luft_def
  . -- validate `assert x ≥ y`
    ----------------------------
    intro (env_luft : Nat) ⟨x, y⟩ _ initial_valid

    have : x ≥ y + (env_luft + luft) :=initial_valid
    show decide (x ≥ y) = true

    exact decide_eq_true <| calc
      y ≤ y + (env_luft + luft) :=by simp_arith
      _ ≤ x                     :=by assumption

end SampleSimple