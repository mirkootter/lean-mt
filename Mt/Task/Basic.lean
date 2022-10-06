import Mt.Reservation
import Mt.Task.Impl

namespace Mt

def TaskM (spec : Spec) (T : Type) : Type :=TaskM.impl.TaskM spec T

inductive TaskM.IterationResult (spec : Spec) (T : Type)
| Done : spec.Reservation -> spec.State -> T -> IterationResult spec T
| Panic : spec.Reservation -> spec.State -> String -> IterationResult spec T
| Running : spec.Reservation -> spec.State ->
    (spec.Reservation -> Bool) ->
    TaskM spec T -> IterationResult spec T

variable {spec : Spec}

def TaskM.IterationResult.reservation {T spec} : IterationResult spec T -> spec.Reservation
| Done r .. => r
| Panic r .. => r
| Running r .. => r

def TaskM.IterationResult.state {T spec} : IterationResult spec T -> spec.State
| Done _ s _ => s
| Panic _ s _ => s
| Running _ s .. => s

instance TaskM.instMonad : Monad (TaskM spec) where
  pure :=impl.TaskM.pure
  bind :=impl.TaskM.bind

theorem TaskM.bind_assoc {U V W : Type}
  (mu : TaskM spec U)
  (f : U -> TaskM spec V)
  (g : V -> TaskM spec W) :
  mu >>= (fun u => (f u) >>= g) = (mu >>= f) >>= g :=by
  simp only [Bind.bind]
  exact impl.TaskM.bind_assoc ..

def TaskM.atomic_read_modify_read {T : Type}
  (f : spec.Reservation -> spec.State -> T × spec.Reservation × spec.State)
  : TaskM spec T :=impl.TaskM.atomic_read_modify_read f

def TaskM.atomic_read_modify
  (f : spec.Reservation -> spec.State -> spec.Reservation × spec.State)
  : TaskM spec Unit :=
  atomic_read_modify_read λ r s => ⟨⟨⟩, f r s⟩

def TaskM.atomic_read {T : Type}
  (f : spec.Reservation -> spec.State -> T × spec.Reservation)
  : TaskM spec T :=
  atomic_read_modify_read λ r s => match f r s with
    | ⟨t, r'⟩ => ⟨t, r', s⟩

def TaskM.panic {T : Type} (msg : String) : TaskM spec T :=
  impl.TaskM.panic msg

def TaskM.atomic_assert
  (cond : spec.State -> Bool)
  : TaskM spec Unit :=impl.TaskM.atomic_assert cond

def TaskM.iterate {T : Type} : TaskM spec T ->
  spec.Reservation -> spec.State -> IterationResult spec T :=
  λ p r s => match p r s with
  | impl.IterationResult.Done r' s' t => IterationResult.Done r' s' t
  | impl.IterationResult.Panic r' s' msg => IterationResult.Panic r' s' msg
  | impl.IterationResult.Running r' s' block_until cont =>
      IterationResult.Running r' s' block_until cont

theorem TaskM.iterate_pure {T : Type} :
  ∀ (r : spec.Reservation) (s : spec.State) (t : T),
  iterate (pure t) r s = IterationResult.Done r s t :=by intros ; rfl

theorem TaskM.iterate_bind {U V : Type}
  (mu : TaskM spec U)
  (f : U -> TaskM spec V)
  : ∀ (r : spec.Reservation) (s : spec.State),
  iterate (mu >>= f) r s = match iterate mu r s with
    | IterationResult.Done r' s' u => IterationResult.Running r' s' (λ _ => true) (f u)
    | IterationResult.Panic r' s' msg => IterationResult.Panic r' s' msg
    | IterationResult.Running r' s' block_until cont =>
        IterationResult.Running r' s' block_until (cont >>= f) :=by
  intro r s
  simp only [Bind.bind, iterate, impl.TaskM.bind]
  cases mu r s <;> rfl

theorem TaskM.iterate_rmr {T : Type}
  (f : spec.Reservation -> spec.State -> T × spec.Reservation × spec.State)
  : ∀ r s,
  iterate (atomic_read_modify_read f) r s = match f r s with
    | ⟨t, r', s'⟩ => IterationResult.Done r' s' t :=by intros ; rfl

theorem TaskM.iterate_rm
  (f : spec.Reservation -> spec.State -> spec.Reservation × spec.State)
  : ∀ r s,
  iterate (atomic_read_modify f) r s = match f r s with
    | ⟨r', s'⟩ => IterationResult.Done r' s' ⟨⟩ :=by
  apply iterate_rmr

theorem TaskM.iterate_read
  (f : spec.Reservation -> spec.State -> T × spec.Reservation)
  : ∀ r s,
  iterate (atomic_read f) r s = match f r s with
    | ⟨t, r'⟩ => IterationResult.Done r' s t :=by
  apply iterate_rmr

theorem TaskM.iterate_panic {T : Type} (msg : String)
  : ∀ (r : spec.Reservation) (s : spec.State),
    iterate (panic (T :=T) msg) r s = IterationResult.Panic r s msg :=by
  intros ; rfl

theorem TaskM.iterate_assert
  (cond : spec.State -> Bool)
  : ∀ r s,
  iterate (atomic_assert cond) r s = if cond s then
    IterationResult.Done r s ⟨⟩
  else
    IterationResult.Panic r s "Assertion failed" :=by
  intro r s
  simp only [atomic_assert, impl.TaskM.atomic_assert, iterate]
  cases cond s <;> simp only [ite_false, ite_true]

inductive TaskM.is_direct_cont {T : Type} : TaskM spec T -> TaskM spec T -> Prop
| running
    {p cont : TaskM spec T}
    {r r' s s'}
    {block_until : spec.Reservation -> Bool}
    (iteration : p.iterate r s = IterationResult.Running r' s' block_until cont)
    : is_direct_cont cont p 

theorem TaskM.is_direct_cont_wf {T : Type} :
  WellFounded (@is_direct_cont spec T) :=by
  constructor ; intro (p : impl.TaskM spec T)

  induction p using WellFounded.induction
  . exact impl.TaskM.is_direct_cont.wf
  . clear p ; rename_i p IH
    constructor ; intro cont is_cont
    apply IH
    cases is_cont
    rename_i r r' s s' block_until iteration
    rw [iterate] at iteration
    cases h : p r s <;> rw [h] at iteration <;> try contradiction
    injection iteration
    rename_i cont'_def ; rw [cont'_def] at h
    exact ⟨h⟩

instance TaskM.instWf {T : Type} :
  WellFoundedRelation (TaskM spec T) where
  rel :=is_direct_cont
  wf  :=is_direct_cont_wf

end Mt