import Mt.Reservation

namespace Mt.TaskM.impl

inductive IterationResult (spec : Spec) (T : Type)
| Done : spec.Reservation -> spec.State -> T -> IterationResult spec T
| Panic : spec.Reservation -> spec.State -> String -> IterationResult spec T
| Running : spec.Reservation -> spec.State -> 
    (spec.Reservation -> Bool) ->
    (spec.Reservation -> spec.State -> IterationResult spec T) ->
    IterationResult spec T

def TaskM (spec : Spec) (T : Type) :=spec.Reservation -> spec.State -> IterationResult spec T

namespace TaskM

variable {spec : Spec}

def atomic_read_modify_read
  (f : spec.Reservation -> spec.State -> T × spec.Reservation × spec.State)
  : TaskM spec T
| r, s => match f r s with
  | ⟨t, r', s'⟩ => IterationResult.Done r' s' t

def panic {T : Type} (msg : String) : TaskM spec T
| r, s => IterationResult.Panic r s msg

def atomic_assert
  (cond : spec.State -> Bool)
  : TaskM spec Unit
| r, s => if cond s then
    IterationResult.Done r s ⟨⟩
  else
    IterationResult.Panic r s "Assertion failed"

def atomic_blocking_rmr
  (block_until : spec.Reservation -> Bool)
  (f : spec.Reservation -> spec.State -> T × spec.Reservation × spec.State)
  : TaskM spec T
| r, s => IterationResult.Running r s block_until (atomic_read_modify_read f)

inductive is_direct_cont {T : Type} : TaskM spec T -> TaskM spec T -> Prop
| running
    {p cont : TaskM spec T}
    {r r' s s'}
    {block_until : spec.Reservation -> Bool}
    (iteration : p r s = IterationResult.Running r' s' block_until cont)
    : is_direct_cont cont p

theorem is_direct_cont.wf {T : Type} : WellFounded (@is_direct_cont spec T) :=by
  constructor
  intro p
  constructor
  intro cont is_cont
  cases is_cont
  rename_i r r' s s' bu iteration
  exact helper (p r s) cont iteration

where
  helper (it : IterationResult spec T) (p : TaskM spec T) {r s block_until} :
    it = IterationResult.Running r s block_until p → Acc is_direct_cont p :=by
    revert p r s block_until
    induction it
    . intros ; contradiction
    . intros ; contradiction
    . intro p r s bu h
      rename_i r' s' bu' p' IH
      injection h ; rename_i h ; rw [h] at IH
      constructor
      intro cont is_cont ; cases is_cont ; rename_i h
      exact IH _ _ _ h

instance instWf {T : Type} : WellFoundedRelation (TaskM spec T) where
  rel :=is_direct_cont
  wf  :=is_direct_cont.wf

def pure {T : Type} (t : T) : TaskM spec T :=
  λ r s => IterationResult.Done r s t

def bind {U V : Type} (mu : TaskM spec U) (f : U -> TaskM spec V) : TaskM spec V :=
  λ r s => match h : mu r s with
    | IterationResult.Done r' s' u => IterationResult.Running r' s' (λ _ => true) (f u)
    | IterationResult.Panic r' s' msg => IterationResult.Panic r' s' msg
    | IterationResult.Running r' s' block_until cont =>
        have : is_direct_cont cont mu :=⟨h⟩
        IterationResult.Running r' s' block_until (bind cont f)
termination_by bind => mu

theorem bind_def {U V spec}
  {mu : TaskM spec U} {f : U -> TaskM spec V}
  {r s}
  : (bind mu f) r s = match mu r s with
    | IterationResult.Done r' s' u => IterationResult.Running r' s' (λ _ => true) (f u)
    | IterationResult.Panic r' s' msg => IterationResult.Panic r' s' msg
    | IterationResult.Running r' s' block_until cont =>
        IterationResult.Running r' s' block_until (bind cont f) :=by
  simp only [bind]
  cases mu r s <;> rfl

theorem bind_assoc {U V W : Type}
  (mu : TaskM spec U)
  (f : U -> TaskM spec V)
  (g : V -> TaskM spec W) :
  mu.bind (fun u => (f u).bind g) = (mu.bind f).bind g :=by
  apply funext ; intro reservation0
  apply funext ; intro s0
  simp only [bind_def]
  induction mu reservation0 s0 <;> try rfl
  rename_i r' s' block_until cont IH
  simp only []
  simp only [<- bind_def] at IH
  apply congrArg (IterationResult.Running _ _ _)
  apply funext ; intro r
  apply funext ; intro s
  exact IH ..

end TaskM

end Mt.TaskM.impl