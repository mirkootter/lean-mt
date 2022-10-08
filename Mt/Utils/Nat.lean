namespace Mt.Utils.Nat

theorem max_of_le {a b : Nat} : a ≤ b → a.max b = b :=by
  intro h ; simp only [Nat.max, h, ite_true]

theorem max_of_eq' {a b : Nat} : a = b → a.max b = b :=
  λ h => max_of_le (by rw [h] ; constructor)

theorem max_of_eq {a b : Nat} : a = b → a.max b = a :=by
  intro h ; rw [max_of_eq' h] ; exact h.symm

theorem max_of_gt {a b : Nat} : a > b → a.max b = a :=by
  intro h ; simp only [Nat.max, Nat.not_le_of_gt h, ite_false]

theorem max_of_ge {a b : Nat} : a ≥ b → a.max b = a :=by
  intro h
  cases Nat.eq_or_lt_of_le h <;> rename_i h
  . exact max_of_eq h.symm
  . exact max_of_gt h

theorem max_of_lt {a b : Nat} : a < b → a.max b = b :=max_of_le ∘ Nat.le_of_lt

theorem max_comm  : ∀ a b : Nat, a.max b = b.max a :=by
  intro a b
  cases Nat.lt_or_ge a b <;> rename_i h
  . rw [max_of_lt h, max_of_gt h]
  cases Nat.eq_or_lt_of_le h <;> (clear h ; rename_i h)
  . rw [max_of_eq h, max_of_eq' h.symm]
  . rw [max_of_lt h, max_of_gt h]

theorem max_assoc : ∀ a b c : Nat, (a.max b).max c = a.max (b.max c) :=by
  intros a b c
  cases Nat.lt_or_ge a b
  <;> cases Nat.lt_or_ge b c
  <;> rename_i ab bc
  . rw [max_of_lt ab, max_of_lt bc, max_of_lt (trans ab bc)]
  . rw [max_of_lt ab, max_of_ge bc, max_of_lt ab]
  . rw [max_of_ge ab, max_of_lt bc]
  . rw [max_of_ge ab, max_of_ge bc, max_of_ge ab]
    exact max_of_ge (trans bc ab : c ≤ a)

theorem zero_max  : ∀ a : Nat, ((0 : Nat).max a) = a :=by
  intro a
  simp only [Nat.max, Nat.zero_le, ite_true]

theorem max_zero  : ∀ a : Nat, (a.max 0) = a :=fun a => calc
  (a.max 0) = Nat.max 0 a :=max_comm ..
          _ = a           :=zero_max a

theorem max_le {a b c : Nat} : a.max b ≤ c ↔ a ≤ c ∧ b ≤ c :=by
  constructor <;> intro h
  <;> (cases Nat.lt_or_ge a b) <;> rename_i ab
  . rw [max_of_lt ab] at h
    exact ⟨Nat.le_of_lt (trans ab h), h⟩
  . rw [max_of_ge ab] at h
    exact ⟨h, trans ab h⟩
  . rw [max_of_lt ab]
    exact h.right
  . rw [max_of_ge ab]
    exact h.left

end Mt.Utils.Nat