import Mt.Reservation

namespace Mt

def TaskM (spec : Spec) (T : Type) : Type :=sorry

inductive TaskM.IterationResult (spec : Spec) (T : Type)
| Done : spec.Reservation -> spec.State -> T -> IterationResult spec T
| Panic : spec.Reservation -> spec.State -> String -> IterationResult spec T
| Running : spec.Reservation -> spec.State -> TaskM spec T -> IterationResult spec T

variable {spec : Spec}

instance TaskM.instMonad : Monad (TaskM spec) :=sorry

axiom TaskM.atomic_read_modify_read {T : Type}
  (f : spec.Reservation -> spec.State -> T × spec.Reservation × spec.State)
  : TaskM spec T

noncomputable def TaskM.atomic_read_modify
  (f : spec.Reservation -> spec.State -> spec.Reservation × spec.State)
  : TaskM spec Unit :=
  atomic_read_modify_read λ r s => ⟨⟨⟩, f r s⟩

noncomputable def TaskM.atomic_read {T : Type}
  (f : spec.Reservation -> spec.State -> T × spec.Reservation)
  : TaskM spec T :=
  atomic_read_modify_read λ r s => match f r s with
    | ⟨t, r'⟩ => ⟨t, r', s⟩

axiom TaskM.atomic_assert
  (cond : spec.Reservation -> spec.State -> Bool)
  : TaskM spec Unit

axiom TaskM.iterate {T : Type} : TaskM spec T ->
  spec.Reservation -> spec.State -> IterationResult spec T

axiom TaskM.iterate_pure {T : Type} :
  ∀ (r : spec.Reservation) (s : spec.State) (t : T),
  iterate (pure t) r s = IterationResult.Done r s t

axiom TaskM.iterate_bind {U V : Type}
  (mu : TaskM spec U)
  (f : U -> TaskM spec V)
  : ∀ (r : spec.Reservation) (s : spec.State),
  iterate (mu >>= f) r s = match iterate mu r s with
    | IterationResult.Done r' s' u => IterationResult.Running r' s' (f u)
    | IterationResult.Panic r' s' msg => IterationResult.Panic r' s' msg
    | IterationResult.Running r' s' cont => IterationResult.Running r' s' (cont >>= f)

axiom TaskM.iterate_rmr {T : Type}
  (f : spec.Reservation -> spec.State -> T × spec.Reservation × spec.State)
  : ∀ r s,
  iterate (atomic_read_modify_read f) r s = match f r s with
    | ⟨t, r', s'⟩ => IterationResult.Done r' s' t

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

axiom TaskM.iterate_assert
  (cond : spec.Reservation -> spec.State -> Bool)
  : ∀ r s,
  iterate (atomic_assert cond) r s = if cond r s then
    IterationResult.Done r s ⟨⟩
  else
    IterationResult.Panic r s "Assertion failed"

inductive TaskM.is_direct_cont {T : Type} : TaskM spec T -> TaskM spec T -> Prop
| running
    {p cont : TaskM spec T}
    {r r' s s'}
    (iteration : p.iterate r s = IterationResult.Running r' s' cont)
    : is_direct_cont cont p 

axiom TaskM.is_direct_cont_wf {T : Type} :
  WellFounded (@is_direct_cont spec T)

instance TaskM.instWf {T : Type} :
  WellFoundedRelation (TaskM spec T) where
  rel :=is_direct_cont
  wf  :=is_direct_cont_wf

end Mt