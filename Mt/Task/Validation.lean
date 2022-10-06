import Mt.Reservation
import Mt.Task.Basic

namespace Mt.TaskM

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

def valid {T : Type} (p : TaskM spec T) (r : spec.Reservation)
  (assuming : spec.Reservation -> Bool)
  (motive : T -> spec.Reservation -> Prop)
  : Prop :=∀ env_r s,
    assuming (env_r + r) →
    spec.validate (env_r + r) s →
    match h : p.iterate r s with
    | IterationResult.Done r' s' t => spec.validate (env_r + r') s' ∧ motive t r'
    | IterationResult.Panic .. => False
    | IterationResult.Running r' s' block_until cont =>
        spec.validate (env_r + r') s' ∧
        cont.valid r' block_until motive
termination_by valid => p
decreasing_by simp_wf ; exact is_direct_cont.running h

theorem valid_pure {T : Type} {t : T} {r assuming motive}
  (is_valid : motive t r)
  : valid (spec :=spec) (pure t) r assuming motive :=by
  rw [valid]
  intro env_r s _ initial_valid
  rw [iterate_pure]
  exact ⟨initial_valid, is_valid⟩

theorem valid_bind {U V : Type}
  {mu : TaskM spec U}
  {f : U -> TaskM spec V}
  {r assuming motive}
  (motive_u : U -> spec.Reservation -> Prop)
  (mu_valid : mu.valid r assuming motive_u)
  (f_valid : ∀ r' u,
    motive_u u r' →
    (f u).valid r' (λ _ => true) motive)
  : valid (mu >>= f) r assuming motive :=by
  rw [valid]
  intro env_r s assuming_true initial_valid
  rw [iterate_bind]
  rw [valid] at mu_valid
  cases iteration : iterate mu r s
  all_goals (
    simp only []
    have mu_valid :=mu_valid env_r s assuming_true initial_valid
    rw [iteration] at mu_valid
    simp only [] at mu_valid
  )
  . exact ⟨mu_valid.left, f_valid _ _ mu_valid.right⟩
  . constructor
    . exact mu_valid.left
    . have :=is_direct_cont.running iteration
      exact valid_bind motive_u mu_valid.right f_valid
termination_by valid_bind => mu

end Mt.TaskM