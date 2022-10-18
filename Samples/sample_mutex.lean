import Mt.Reservation
import Mt.Task

namespace SampleMutex

structure Data where
  x : Nat
  y : Nat

def Data.valid : Data -> Prop
| ⟨x, y⟩ => x = y

abbrev Reservation :=Mt.Lock Data

structure State where
  data : Data
  locked : Bool

inductive validate : Reservation -> State -> Prop where
| unlocked {data : Data} : data.valid → validate Mt.Lock.Unlocked ⟨data, false⟩
| locked (data : Data) : validate (Mt.Lock.Locked data) ⟨data, true⟩

def spec : Mt.Spec :={
  State
  Reservation
  validate
}

open Mt
open Mt.TaskM

def thread1 : TaskM spec Unit :=do
  -- lock mutex
  atomic_blocking_rmr (λ ⟨_, locked⟩ => locked = false) λ (s : State) => ⟨⟨⟩, {s with locked :=true}⟩
  
  -- two atomic modifications, one after the other
  atomic_read_modify λ s => {s with data :={s.data with x :=s.data.x + 1}}
  atomic_read_modify λ s => {s with data :={s.data with y :=s.data.y + 1}}
  
  -- release mutex
  atomic_read_modify λ s => {s with locked :=false}

def thread2 : TaskM spec Unit :=do
  -- lock mutex
  atomic_blocking_rmr (λ ⟨_, locked⟩ => locked = false) λ (s : State) => ⟨⟨⟩, {s with locked :=true}⟩
  
  -- two atomic reads, one after the other
  let px <- atomic_read λ s => s.data.x
  let py <- atomic_read λ s => s.data.y

  atomic_assert λ _ => px = py
  
  -- release mutex
  atomic_read_modify λ s => {s with locked :=false}

theorem validate.elim_unlocked' {r s} :
  validate r s → s.locked = false → r = Lock.Unlocked ∧ s.data.valid :=by
  intro is_valid is_unlocked
  cases is_valid
  . constructor
    . rfl
    . assumption
  . contradiction

theorem validate.elim_unlocked {r s} :
  validate r s → r.is_unlocked → ¬ s.locked ∧ s.data.valid :=by
  intro initial_valid unlocked
  cases initial_valid
  . constructor
    . intro h ; contradiction
    . assumption
  . contradiction

theorem validate.elim_locked {env_r : Reservation} {d s'} :
  validate (env_r + Lock.Locked d) s' →
  env_r = Lock.Unlocked ∧ d = s'.data ∧ s'.locked = true :=by
  intro initial_valid
  cases env_r <;> cases initial_valid
  constructor
  . rfl
  constructor <;> rfl

theorem thread1_valid : thread1.valid' Mt.Lock.Unlocked :=by
  rw [valid']
  apply valid_bind (spec :=spec) λ ⟨⟩ r => r.is_locked_and_valid Data.valid
  . -- verify mutex lock
    apply valid_blocking_rmr
    simp only [spec, Lock.add_unlocked]
    intro env_r s is_unlocked initial_valid
    exists Lock.Locked s.data

    have is_unlocked :=of_decide_eq_true is_unlocked
    have :=initial_valid.elim_unlocked' is_unlocked
    
    simp only [spec, this, Lock.is_locked_and_valid, and_true]
    exact validate.locked ..
  
  intro r ⟨⟩ is_locked_and_valid
  cases r <;> try contradiction
  rename_i data0
  let ⟨x0, y0⟩ :=data0 ; clear data0
  cases is_locked_and_valid
  apply valid_bind (spec :=spec) λ ⟨⟩ r' => r' = Lock.Locked ⟨x0 + 1, x0⟩
  . -- validate ++x
    apply valid_rm
    simp only [spec]
    intro env_r ⟨⟨x, y⟩, locked⟩ ⟨⟩ initial_valid
    exists Lock.Locked ⟨x0 + 1, x0⟩
    
    simp only [initial_valid.elim_locked, Lock.unlocked_add]
    injection initial_valid.elim_locked.right.left
    rename_i x0_def y0_def
    simp only [<- x0_def, <- y0_def]
    exact ⟨validate.locked _, ⟨⟩⟩
  
  intro r ⟨⟩ r_def
  rw [r_def] ; clear r_def r
  apply valid_bind (spec :=spec) λ ⟨⟩ r' => r' = Lock.Locked ⟨x0 + 1, x0 + 1⟩
  . -- validate ++y
    apply valid_rm
    simp only [spec]
    intro env_r ⟨⟨x, y⟩, locked⟩ ⟨⟩ initial_valid
    exists Lock.Locked ⟨x0 + 1, x0 + 1⟩
    simp only [initial_valid.elim_locked, Lock.unlocked_add]
    injection initial_valid.elim_locked.right.left
    rename_i x0_def y0_def
    simp only [<- x0_def, <- y0_def]
    exact ⟨validate.locked _, ⟨⟩⟩

  intro r ⟨⟩ r_def
  rw [r_def]; clear r_def r
  . -- validate mutex release
    apply valid_rm
    simp only [spec, Lock.add_unlocked]
    intro env_r ⟨⟨x, y⟩, locked ⟩ ⟨⟩ initial_valid
    exists Lock.Unlocked
    injection initial_valid.elim_locked.right.left
    rename_i x_def y_def
    simp only [initial_valid.elim_locked]
    rw [x_def.symm, y_def.symm] ; clear x_def y_def
    exact ⟨validate.unlocked rfl, rfl⟩

theorem thread2_valid : thread2.valid' Mt.Lock.Unlocked :=by
  rw [valid']
  apply valid_bind (spec :=spec) λ ⟨⟩ r => r.is_locked_and_valid Data.valid
  . -- verify mutex lock
    apply valid_blocking_rmr
    simp only [spec, Lock.add_unlocked]
    intro env_r s is_unlocked initial_valid
    exists Lock.Locked s.data

    have is_unlocked :=of_decide_eq_true is_unlocked
    have :=initial_valid.elim_unlocked' is_unlocked
    
    simp only [spec, this, Lock.is_locked_and_valid, and_true]
    exact validate.locked ..
  
  intro r ⟨⟩ is_locked_and_valid
  cases r <;> try contradiction
  rename_i data0
  let ⟨x0, y0⟩ :=data0 ; clear data0
  cases is_locked_and_valid
  
  apply valid_bind (spec :=spec) λ px r' => r' = Lock.Locked ⟨x0, x0⟩ ∧ px = x0
  . -- verify read of x; we should get x0
    apply valid_read
    simp only [spec]
    intro env_r ⟨⟨x, y⟩, locked⟩ ⟨⟩ initial_valid
    exists Lock.Locked ⟨x0, x0⟩
    simp only [initial_valid.elim_locked, Lock.unlocked_add]
    injection initial_valid.elim_locked.right.left
    rename_i x0_def y0_def
    simp only [<- x0_def, <- y0_def, and_true]
    exact validate.locked _

  intro r px is_locked_and_valid
  cases is_locked_and_valid ; rename_i r_def px_def
  cases r <;> try contradiction
  rename_i data0
  let ⟨x0, y0⟩ :=data0 ; clear data0
  cases r_def
  apply valid_bind (spec :=spec) λ py r' => r' = Lock.Locked ⟨x0, x0⟩ ∧ py = x0
  . -- verify read of x; we should get x0
    apply valid_read
    simp only [spec]
    intro env_r ⟨⟨x, y⟩, locked⟩ ⟨⟩ initial_valid
    exists Lock.Locked ⟨x0, x0⟩
    simp only [initial_valid.elim_locked, Lock.unlocked_add]
    injection initial_valid.elim_locked.right.left
    rename_i x0_def y0_def
    simp only [<- x0_def, <- y0_def, and_true]
    exact validate.locked _

  intro r py is_locked_and_valid
  cases is_locked_and_valid ; rename_i r_def py_def
  cases r <;> try contradiction
  rename_i data0
  let ⟨x0, y0⟩ :=data0 ; clear data0
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
    intro env_r ⟨⟨x, y⟩, locked⟩ ⟨⟩ initial_valid
    exists Lock.Unlocked
    injection initial_valid.elim_locked.right.left
    rename_i x_def y_def
    simp only [initial_valid.elim_locked]
    rw [x_def.symm, y_def.symm] ; clear x_def y_def
    exact ⟨validate.unlocked rfl, rfl⟩

end SampleMutex