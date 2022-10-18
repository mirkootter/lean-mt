import Mt.Reservation
import Mt.Task.Basic

namespace Mt.TaskM

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

def valid {T : Type} (p : TaskM spec T) (r : spec.Reservation)
  (assuming : spec.State -> Bool)
  (motive : T -> spec.Reservation -> Prop)
  : Prop :=∀ env_r s,
    assuming s →
    spec.validate (env_r + r) s → ∃ r' : spec.Reservation,
    match h : p.iterate s with
    | IterationResult.Done s' t => spec.validate (env_r + r') s' ∧ motive t r'
    | IterationResult.Panic .. => False
    | IterationResult.Running s' block_until cont =>
        spec.validate (env_r + r') s' ∧
        cont.valid r' block_until motive
termination_by valid => p
decreasing_by simp_wf ; exact is_direct_cont.running h

def valid' {T : Type} (p : TaskM spec T) (r : spec.Reservation)
  :=p.valid r (λ _ => true) (λ _ r => r = IsReservation.empty)

theorem valid_pure {T : Type} {t : T} {r assuming motive}
  (is_valid : motive t r)
  : valid (spec :=spec) (pure t) r assuming motive :=by
  rw [valid]
  intro env_r s _ initial_valid
  exists r

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
  cases iteration : iterate mu s
  all_goals (
    simp only []
    have mu_valid :=mu_valid env_r s assuming_true initial_valid
    rw [iteration] at mu_valid
    simp only [] at mu_valid
    cases mu_valid ; rename_i r' mu_valid
    exists r'
  )
  . exact ⟨mu_valid.left, f_valid _ _ mu_valid.right⟩
  . constructor
    . exact mu_valid.left
    . have :=is_direct_cont.running iteration
      exact valid_bind motive_u mu_valid.right f_valid
termination_by valid_bind => mu

theorem valid_rmr {T : Type}
  {f : spec.State -> T × spec.State}
  {r assuming motive}
  (f_valid : ∀ env_r s,
    assuming s →
    spec.validate (env_r + r) s → ∃ r' : spec.Reservation,
    match f s with
    | ⟨t, s'⟩ => spec.validate (env_r + r') s' ∧ motive t r'
  )
  : (atomic_read_modify_read f).valid r assuming motive :=by
  rw [valid]
  intro env_r s assuming_true initial_valid
  rw [iterate_rmr]
  exact f_valid env_r s assuming_true initial_valid

theorem valid_rm
  {f : spec.State -> spec.State}
  {r assuming motive}
  (f_valid : ∀ env_r s,
    assuming s →
    spec.validate (env_r + r) s → ∃ r' : spec.Reservation,
    match f s with
    | s' => spec.validate (env_r + r') s' ∧ motive ⟨⟩ r')
  : (atomic_read_modify f).valid r assuming motive :=valid_rmr f_valid

theorem valid_read
  {f : spec.State -> T}
  {r assuming motive}
  (f_valid : ∀ env_r s,
    assuming s →
    spec.validate (env_r + r) s → ∃ r' : spec.Reservation,
    match f s with
    | t => spec.validate (env_r + r') s ∧ motive t r')
  : (atomic_read f).valid r assuming motive :=valid_rmr f_valid

theorem valid_assert
  {cond : spec.State -> Bool}
  {r assuming motive}
  (motive_holds : motive ⟨⟩ r)
  (assertion_succeeds : ∀ env_r s,
    assuming s →
    spec.validate (env_r + r) s →
    cond s)
  : (atomic_assert cond).valid r assuming motive :=by
  rw [valid]
  intro env_r s assuming_true initial_valid
  rw [iterate_assert]
  have cond_true :=assertion_succeeds env_r s assuming_true initial_valid
  rw [cond_true]
  exists r

theorem valid_blocking_rmr
  {block_until : spec.State -> Bool}
  {f : spec.State -> T × spec.State}
  {r assuming motive}
  (f_valid : ∀ env_r s,
    block_until s →
    spec.validate (env_r + r) s → ∃ r' : spec.Reservation,
    match f s with
    | ⟨t, s'⟩ => spec.validate (env_r + r') s' ∧ motive t r'
  )
  : (atomic_blocking_rmr block_until f).valid r assuming motive :=by
  rw [valid]
  intro env_r s _ initial_valid
  simp only [iterate_blocking_rmr, initial_valid, true_and]
  
  exists r
  exact ⟨initial_valid, valid_rmr f_valid⟩

end Mt.TaskM