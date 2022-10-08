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

def valid' {T : Type} (p : TaskM spec T) (r : spec.Reservation)
  :=p.valid r (λ _ => true) (λ _ r => r = IsReservation.empty)

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

theorem valid_rmr {T : Type}
  {f : spec.Reservation -> spec.State -> T × spec.Reservation × spec.State}
  {r assuming motive}
  (f_valid : ∀ env_r s,
    assuming (env_r + r) →
    spec.validate (env_r + r) s →
    match f r s with
    | ⟨t, r', s'⟩ => spec.validate (env_r + r') s' ∧ motive t r'
  )
  : (atomic_read_modify_read f).valid r assuming motive :=by
  rw [valid]
  intro env_r s assuming_true initial_valid
  rw [iterate_rmr]
  exact f_valid env_r s assuming_true initial_valid

theorem valid_rm
  {f : spec.Reservation -> spec.State -> spec.Reservation × spec.State}
  {r assuming motive}
  (f_valid : ∀ env_r s,
    assuming (env_r + r) →
    spec.validate (env_r + r) s →
    match f r s with
    | ⟨r', s'⟩ => spec.validate (env_r + r') s' ∧ motive ⟨⟩ r')
  : (atomic_read_modify f).valid r assuming motive :=valid_rmr f_valid

theorem valid_read
  {f : spec.Reservation -> spec.State -> T × spec.Reservation}
  {r assuming motive}
  (f_valid : ∀ env_r s,
    assuming (env_r + r) →
    spec.validate (env_r + r) s →
    match f r s with
    | ⟨t, r'⟩ => spec.validate (env_r + r') s ∧ motive t r')
  : (atomic_read f).valid r assuming motive :=valid_rmr f_valid

theorem valid_assert
  {cond : spec.State -> Bool}
  {r assuming motive}
  (motive_holds : motive ⟨⟩ r)
  (assertion_succeeds : ∀ env_r s,
    assuming (env_r + r) →
    spec.validate (env_r + r) s →
    cond s)
  : (atomic_assert cond).valid r assuming motive :=by
  rw [valid]
  intro env_r s assuming_true initial_valid
  rw [iterate_assert]
  have cond_true :=assertion_succeeds env_r s assuming_true initial_valid
  rw [cond_true]
  simp only [ite_true]
  exact ⟨initial_valid, motive_holds⟩

theorem valid_blocking_rmr
  {block_until : spec.Reservation -> Bool}
  {f : spec.Reservation -> spec.State -> T × spec.Reservation × spec.State}
  {r assuming motive}
  (f_valid : ∀ env_r s,
    block_until (env_r + r) →
    spec.validate (env_r + r) s →
    match f r s with
    | ⟨t, r', s'⟩ => spec.validate (env_r + r') s' ∧ motive t r'
  )
  : (atomic_blocking_rmr block_until f).valid r assuming motive :=by
  rw [valid]
  intro env_r s _ initial_valid
  simp only [iterate_blocking_rmr, initial_valid, true_and]
  exact valid_rmr f_valid

end Mt.TaskM