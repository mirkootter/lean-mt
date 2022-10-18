import Mt.Reservation
import Mt.Task.Impl

namespace Mt

def TaskM (spec : Spec) (T : Type) : Type :=TaskM.impl.TaskM spec T

inductive TaskM.IterationResult (spec : Spec) (T : Type)
| Done : spec.State -> T -> IterationResult spec T
| Panic : spec.State -> String -> IterationResult spec T
| Running : spec.State -> (spec.State -> Bool) -> TaskM spec T -> IterationResult spec T

variable {spec : Spec}

def TaskM.IterationResult.state {T spec} : IterationResult spec T -> spec.State
| Done s _ => s
| Panic s _ => s
| Running s .. => s

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
  (f : spec.State -> T × spec.State)
  : TaskM spec T :=impl.TaskM.atomic_read_modify_read f

def TaskM.atomic_read_modify
  (f : spec.State -> spec.State) : TaskM spec Unit :=
  atomic_read_modify_read λ s => ⟨⟨⟩, f s⟩

def TaskM.atomic_read {T : Type}
  (f : spec.State -> T)
  : TaskM spec T :=
  atomic_read_modify_read λ s => match f s with
    | t => ⟨t, s⟩

def TaskM.panic {T : Type} (msg : String) : TaskM spec T :=
  impl.TaskM.panic msg

def TaskM.atomic_assert
  (cond : spec.State -> Bool)
  : TaskM spec Unit :=impl.TaskM.atomic_assert cond

def TaskM.atomic_blocking_rmr
  (block_until : spec.State -> Bool)
  (f : spec.State -> T × spec.State)
  : TaskM spec T :=impl.TaskM.atomic_blocking_rmr block_until f

def TaskM.iterate {T : Type} : TaskM spec T ->
  spec.State -> IterationResult spec T :=
  λ p s => match p s with
  | impl.IterationResult.Done s' t => IterationResult.Done s' t
  | impl.IterationResult.Panic s' msg => IterationResult.Panic s' msg
  | impl.IterationResult.Running s' block_until cont =>
      IterationResult.Running s' block_until cont

theorem TaskM.iterate_pure {T : Type} :
  ∀ (s : spec.State) (t : T),
  iterate (pure t) s = IterationResult.Done s t :=by intros ; rfl

theorem TaskM.iterate_bind {U V : Type}
  (mu : TaskM spec U)
  (f : U -> TaskM spec V)
  : ∀ (s : spec.State),
  iterate (mu >>= f) s = match iterate mu s with
    | IterationResult.Done s' u => IterationResult.Running s' (λ _ => true) (f u)
    | IterationResult.Panic s' msg => IterationResult.Panic s' msg
    | IterationResult.Running s' block_until cont =>
        IterationResult.Running s' block_until (cont >>= f) :=by
  intro s
  simp only [Bind.bind, iterate, impl.TaskM.bind]
  cases mu s <;> rfl

theorem TaskM.iterate_rmr {T : Type}
  (f : spec.State -> T × spec.State)
  : ∀ s,
  iterate (atomic_read_modify_read f) s = match f s with
    | ⟨t, s'⟩ => IterationResult.Done s' t :=by intros ; rfl

theorem TaskM.iterate_rm
  (f : spec.State -> spec.State)
  : ∀ s,
  iterate (atomic_read_modify f) s = match f s with
    | s' => IterationResult.Done s' ⟨⟩ :=by
  apply iterate_rmr

theorem TaskM.iterate_read
  (f : spec.State -> T × spec.Reservation)
  : ∀ s,
  iterate (atomic_read f) s = match f s with
    | t => IterationResult.Done s t :=by
  apply iterate_rmr

theorem TaskM.iterate_panic {T : Type} (msg : String)
  : ∀ (s : spec.State),
    iterate (panic (T :=T) msg) s = IterationResult.Panic s msg :=by
  intros ; rfl

theorem TaskM.iterate_assert
  (cond : spec.State -> Bool)
  : ∀ s,
  iterate (atomic_assert cond) s = if cond s then
    IterationResult.Done s ⟨⟩
  else
    IterationResult.Panic s "Assertion failed" :=by
  intro s
  simp only [atomic_assert, impl.TaskM.atomic_assert, iterate]
  cases cond s <;> simp only [ite_false, ite_true]

theorem TaskM.iterate_blocking_rmr
  (block_until : spec.State -> Bool)
  (f : spec.State -> T × spec.State)
  : ∀ s,
  iterate (atomic_blocking_rmr block_until f) s = IterationResult.Running s
    block_until (atomic_read_modify_read f) :=by intros ; rfl

inductive TaskM.is_direct_cont {T : Type} : TaskM spec T -> TaskM spec T -> Prop
| running
    {p cont : TaskM spec T}
    {s s'}
    {block_until : spec.State -> Bool}
    (iteration : p.iterate s = IterationResult.Running s' block_until cont)
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
    rename_i s s' block_until iteration
    rw [iterate] at iteration
    cases h : p s <;> rw [h] at iteration <;> try contradiction
    injection iteration
    rename_i cont'_def ; rw [cont'_def] at h
    exact ⟨h⟩

instance TaskM.instWf {T : Type} :
  WellFoundedRelation (TaskM spec T) where
  rel :=is_direct_cont
  wf  :=is_direct_cont_wf

end Mt