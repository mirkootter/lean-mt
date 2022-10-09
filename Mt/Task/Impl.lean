import Mt.Reservation

namespace Mt.TaskM.impl

inductive IterationResult (spec : Spec) (T : Type)
| Done : spec.State -> T -> IterationResult spec T
| Panic : spec.State -> String -> IterationResult spec T
| Running : spec.State -> (spec.State -> Bool) ->
    (spec.State -> IterationResult spec T) ->
    IterationResult spec T

def TaskM (spec : Spec) (T : Type) :=spec.State -> IterationResult spec T

namespace TaskM

variable {spec : Spec}

def atomic_read_modify_read
  (f : spec.State -> T × spec.State)
  : TaskM spec T
| s => match f s with
  | ⟨t, s'⟩ => IterationResult.Done s' t

def panic {T : Type} (msg : String) : TaskM spec T
| s => IterationResult.Panic s msg

def atomic_assert
  (cond : spec.State -> Bool)
  : TaskM spec Unit
| s => if cond s then
    IterationResult.Done s ⟨⟩
  else
    IterationResult.Panic s "Assertion failed"

def atomic_blocking_rmr
  (block_until : spec.State -> Bool)
  (f : spec.State -> T × spec.State) : TaskM spec T
| s => IterationResult.Running s block_until (atomic_read_modify_read f)

inductive is_direct_cont {T : Type} : TaskM spec T -> TaskM spec T -> Prop
| running
    {p cont : TaskM spec T}
    {s s'}
    {block_until : spec.State -> Bool}
    (iteration : p s = IterationResult.Running s' block_until cont)
    : is_direct_cont cont p

theorem is_direct_cont.wf {T : Type} : WellFounded (@is_direct_cont spec T) :=by
  constructor
  intro p
  constructor
  intro cont is_cont
  cases is_cont
  rename_i s s' bu iteration
  exact helper (p s) cont iteration

where
  helper (it : IterationResult spec T) (p : TaskM spec T) {s block_until} :
    it = IterationResult.Running s block_until p → Acc is_direct_cont p :=by
    revert p s block_until
    induction it
    . intros ; contradiction
    . intros ; contradiction
    . intro p s bu h
      rename_i s' bu' p' IH
      injection h ; rename_i h ; rw [h] at IH
      constructor
      intro cont is_cont ; cases is_cont ; rename_i h
      exact IH _ _ h

instance instWf {T : Type} : WellFoundedRelation (TaskM spec T) where
  rel :=is_direct_cont
  wf  :=is_direct_cont.wf

def pure {T : Type} (t : T) : TaskM spec T :=
  λ s => IterationResult.Done s t

def bind {U V : Type} (mu : TaskM spec U) (f : U -> TaskM spec V) : TaskM spec V :=
  λ s => match h : mu s with
    | IterationResult.Done s' u => IterationResult.Running s' (λ _ => true) (f u)
    | IterationResult.Panic s' msg => IterationResult.Panic s' msg
    | IterationResult.Running s' block_until cont =>
        have : is_direct_cont cont mu :=⟨h⟩
        IterationResult.Running s' block_until (bind cont f)
termination_by bind => mu

theorem bind_def {U V spec}
  {mu : TaskM spec U} {f : U -> TaskM spec V}
  {s}
  : (bind mu f) s = match mu s with
    | IterationResult.Done s' u => IterationResult.Running s' (λ _ => true) (f u)
    | IterationResult.Panic s' msg => IterationResult.Panic s' msg
    | IterationResult.Running s' block_until cont =>
        IterationResult.Running s' block_until (bind cont f) :=by
  simp only [bind]
  cases mu s <;> rfl

theorem bind_assoc {U V W : Type}
  (mu : TaskM spec U)
  (f : U -> TaskM spec V)
  (g : V -> TaskM spec W) :
  mu.bind (fun u => (f u).bind g) = (mu.bind f).bind g :=by
  apply funext ; intro s0
  simp only [bind_def]
  induction mu s0 <;> try rfl
  rename_i s' block_until cont IH
  simp only []
  simp only [<- bind_def] at IH
  apply congrArg (IterationResult.Running _ _)
  apply funext ; intro s
  exact IH ..

end TaskM

end Mt.TaskM.impl