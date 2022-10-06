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

def atomic_assert
  (cond : spec.Reservation -> spec.State -> Bool)
  : TaskM spec Unit
| r, s =>if cond r s then
    IterationResult.Done r s ⟨⟩
  else
    IterationResult.Panic r s "Assertion failed"

inductive is_direct_cont {T : Type} : TaskM spec T -> TaskM spec T -> Prop
| running
    {p cont : TaskM spec T}
    {r r' s s'}
    {block_until : spec.Reservation -> Bool}
    (iteration : p r s = IterationResult.Running r' s' block_until cont)
    : is_direct_cont cont p

theorem is_direct_cont.wf {T : Type} : WellFounded (@is_direct_cont spec T) :=sorry

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
  rename_i cont IH 
  --simp only [bind_def]

  --simp only [Step.chain]
  simp only []
  conv =>
    lhs ; arg 4 ; intro reservation s
    simp only [bind_def]
    rw [IH reservation s]
    

end TaskM

end Mt.TaskM.impl