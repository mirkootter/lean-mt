import Mt.Reservation
import Mt.Task
import Mt.System

structure State where
  x : Nat
  y : Nat

def State.valid : State -> Prop
| ⟨x, y⟩ => x = y

abbrev Reservation :=Mt.Lock State

inductive validate : Reservation -> State -> Prop where
| unlocked {s : State} : s.valid → validate Mt.Lock.Unlocked s
| locked (s : State) : validate (Mt.Lock.Locked s) s

def spec : Mt.Spec :={
  State
  Reservation
  validate
}

open Mt
open Mt.TaskM

/-- read-modify operation assuming the mutex is owned -/
abbrev rm_locked (f : State -> State) : TaskM spec Unit :=
  atomic_read_modify λ _ s => match f s with
    | s' => ⟨Lock.Locked s', s'⟩ 

def thread1 : TaskM spec Unit :=do
  -- lock mutex
  atomic_blocking_rmr (λ r => r.is_unlocked) λ _ s => ⟨⟨⟩, Mt.Lock.Locked s, s⟩
  
  -- two atomic modifications, one after the other
  rm_locked λ s => {s with x :=s.x + 1}
  rm_locked λ s => {s with y :=s.y + 1}
  
  -- release mutex
  atomic_read_modify λ _ s => ⟨Mt.Lock.Unlocked, s⟩

def thread2 : TaskM spec Unit :=do
  -- lock mutex
  atomic_blocking_rmr (λ r => r.is_unlocked) λ _ s => ⟨⟨⟩, Mt.Lock.Locked s, s⟩
  
  -- two atomic reads, one after the other
  let px <- atomic_read λ r ⟨x, _⟩ => ⟨x, r⟩
  let py <- atomic_read λ r ⟨_, y⟩ => ⟨y, r⟩

  atomic_assert λ _ => px = py
  
  -- release mutex
  atomic_read_modify λ _ s => ⟨Mt.Lock.Unlocked, s⟩

theorem validate.elim_unlocked {r s} :
  validate r s → r.is_unlocked → s.valid :=by
  intro initial_valid unlocked
  cases initial_valid
  . assumption
  . contradiction

theorem validate.elim_locked {env_r : Reservation} {s s'} :
  validate (env_r + Lock.Locked s) s' →
  env_r = Lock.Unlocked ∧ s = s' :=by
  intro initial_valid
  cases env_r <;> cases initial_valid
  exact ⟨rfl, rfl⟩

theorem thread1_valid : thread1.valid' Mt.Lock.Unlocked :=by
  rw [valid']
  apply valid_bind (spec :=spec) λ ⟨⟩ r => r.is_locked_and_valid State.valid
  . -- verify mutex lock
    apply valid_blocking_rmr
    simp only [spec, Lock.add_unlocked]
    intro env_r s is_unlocked initial_valid
    have :=Lock.eq_of_is_unlocked is_unlocked
    simp only [spec, this, Lock.unlocked_add, Lock.is_locked_and_valid]
    exact ⟨validate.locked .., initial_valid.elim_unlocked is_unlocked⟩
  
  intro r ⟨⟩ is_locked_and_valid
  cases r <;> try contradiction
  rename_i s0
  let ⟨x0, y0⟩ :=s0 ; clear s0
  cases is_locked_and_valid
  apply valid_bind (spec :=spec) λ ⟨⟩ r' => r' = Lock.Locked ⟨x0 + 1, x0⟩
  . -- validate ++x
    apply valid_rm
    simp only [spec]
    intro env_r ⟨x, y⟩ ⟨⟩ initial_valid
    simp only [initial_valid.elim_locked, Lock.unlocked_add]
    injection initial_valid.elim_locked.right
    rename_i x0_def y0_def
    simp only [<- x0_def, <- y0_def]
    exact ⟨validate.locked _, ⟨⟩⟩
  
  intro r ⟨⟩ r_def
  rw [r_def] ; clear r_def r
  apply valid_bind (spec :=spec) λ ⟨⟩ r' => r' = Lock.Locked ⟨x0 + 1, x0 + 1⟩
  . -- validate ++y
    apply valid_rm
    simp only [spec]
    intro env_r ⟨x, y⟩ ⟨⟩ initial_valid
    simp only [initial_valid.elim_locked, Lock.unlocked_add]
    injection initial_valid.elim_locked.right
    rename_i x0_def y0_def
    simp only [<- x0_def, <- y0_def]
    exact ⟨validate.locked _, ⟨⟩⟩

  intro r ⟨⟩ r_def
  rw [r_def]; clear r_def r
  . -- validate mutex release
    apply valid_rm
    simp only [spec, Lock.add_unlocked]
    intro env_r ⟨x, y⟩ ⟨⟩ initial_valid
    injection initial_valid.elim_locked.right
    rename_i x_def y_def
    simp only [initial_valid.elim_locked]
    rw [x_def.symm, y_def.symm] ; clear x_def y_def
    exact ⟨validate.unlocked rfl, rfl⟩

theorem thread2_valid : thread2.valid' Mt.Lock.Unlocked :=by
  rw [valid']
  apply valid_bind (spec :=spec) λ ⟨⟩ r => r.is_locked_and_valid State.valid
  . -- verify mutex lock
    apply valid_blocking_rmr
    simp only [spec, Lock.add_unlocked]
    intro env_r s is_unlocked initial_valid
    have :=Lock.eq_of_is_unlocked is_unlocked
    simp only [spec, this, Lock.unlocked_add, Lock.is_locked_and_valid]
    exact ⟨validate.locked .., initial_valid.elim_unlocked is_unlocked⟩
  
  intro r ⟨⟩ is_locked_and_valid
  cases r <;> try contradiction
  rename_i s0
  let ⟨x0, y0⟩ :=s0 ; clear s0
  cases is_locked_and_valid
  
  apply valid_bind (spec :=spec) λ px r' => r' = Lock.Locked ⟨x0, x0⟩ ∧ px = x0
  . -- verify read of x; we should get x0
    apply valid_read
    simp only [spec]
    intro env_r ⟨x, y⟩ ⟨⟩ initial_valid
    simp only [initial_valid.elim_locked, Lock.unlocked_add]
    injection initial_valid.elim_locked.right
    rename_i x0_def y0_def
    simp only [<- x0_def, <- y0_def, and_true]
    exact validate.locked _

  intro r px is_locked_and_valid
  cases is_locked_and_valid ; rename_i r_def px_def
  cases r <;> try contradiction
  rename_i s0
  let ⟨x0, y0⟩ :=s0 ; clear s0
  cases r_def
  apply valid_bind (spec :=spec) λ py r' => r' = Lock.Locked ⟨x0, x0⟩ ∧ py = x0
  . -- verify read of x; we should get x0
    apply valid_read
    simp only [spec]
    intro env_r ⟨x, y⟩ ⟨⟩ initial_valid
    simp only [initial_valid.elim_locked, Lock.unlocked_add]
    injection initial_valid.elim_locked.right
    rename_i x0_def y0_def
    simp only [<- x0_def, <- y0_def, and_true]
    exact validate.locked _

  intro r py is_locked_and_valid
  cases is_locked_and_valid ; rename_i r_def py_def
  cases r <;> try contradiction
  rename_i s0
  let ⟨x0, y0⟩ :=s0 ; clear s0
  cases r_def
  apply valid_bind (spec :=spec) λ ⟨⟩ r' => r' = Lock.Locked ⟨x0, x0⟩
  . -- verify assertion
    apply valid_assert rfl
    intros
    rw [px_def, py_def]
    exact decide_eq_true rfl
  
  intro r ⟨⟩ r_def
  rw [r_def]; clear r_def r
  . -- validate mutex release
    apply valid_rm
    simp only [spec, Lock.add_unlocked]
    intro env_r ⟨x, y⟩ ⟨⟩ initial_valid
    injection initial_valid.elim_locked.right
    rename_i x_def y_def
    simp only [initial_valid.elim_locked]
    rw [x_def.symm, y_def.symm] ; clear x_def y_def
    exact ⟨validate.unlocked rfl, rfl⟩
