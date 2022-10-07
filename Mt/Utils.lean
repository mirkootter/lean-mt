namespace Mt.Utils

theorem forall_ext {α : Type} {f g : α -> Prop}
  (h : ∀ a : α, f a = g a) : (∀ a : α, f a) = (∀ a : α, g a) :=by
  apply propext
  constructor <;> intro h' a
  . exact Eq.mp (h a) (h' a)
  . exact Eq.mpr (h a) (h' a)

theorem list_get_in {T : Type u} (l : List T) (idx : Fin l.length)
  : (l.get idx) ∈ l :=match l, idx with
  | a::_, ⟨0, _⟩ => List.Mem.head a _
  | _::as, ⟨n + 1, isLt⟩ => List.Mem.tail _ <| list_get_in as ⟨n, Nat.le_of_succ_le_succ isLt⟩

theorem list_get_of_set {T : Type u} (l : List T) (idx : Nat) (a : T)
  (isLt : idx < (l.set idx a).length)
  : (l.set idx a).get ⟨idx, isLt⟩ = a :=match l, idx with
  | _::_, 0 => rfl
  | _::xs, n + 1 => list_get_of_set xs n a <| Nat.lt_of_succ_lt_succ isLt

theorem list_erase_subset {T : Type u} {a : T} (l : List T) (idx : Nat) 
  : a ∈ (l.eraseIdx idx) → a ∈ l :=match l, idx with
  | [], _ => id
  | x::xs, 0 => fun h => List.Mem.tail _ h
  | x::xs, n+1 => by
    intro h ; cases h
    . exact List.Mem.head ..
    . exact List.Mem.tail x <| list_erase_subset xs n (by assumption)

theorem list_set_subset {T : Type u} {a : T} (l : List T) (idx : Nat) (new_value : T)
  : a ∈ (l.set idx new_value) → a = new_value ∨ a ∈ l :=match l, idx with
  | [], _ => Or.inr
  | x::xs, 0 => by
    intro h ; cases h
    . exact Or.inl rfl
    . exact Or.inr <| List.Mem.tail _ (by assumption)
  | x::xs, n+1 => by
    intro h ; cases h
    . exact Or.inr <| List.Mem.head ..
    . cases list_set_subset xs n new_value (by assumption)
      . exact Or.inl (by assumption)
      . exact Or.inr <| List.Mem.tail _ (by assumption)

theorem list_index_exists {T : Type u} {a : T} (l : List T)
  : a ∈ l → ∃ i : Fin l.length, l.get i = a :=fun a_in_l => match l, a_in_l with
    | x::xs, a_in_l => by
      cases a_in_l
      . exists ⟨0, by simp_arith⟩
      . apply (list_index_exists xs (by assumption)).elim
        intro i xs_get_i
        exists ⟨i.val + 1, by simp_arith only [List.length] ; exact i.isLt⟩

theorem erase_set {T : Type u} (l : List T) (idx : Nat) (new_value : T)
  : (l.set idx new_value).eraseIdx idx = l.eraseIdx idx :=match l, idx with
  | [], _ => rfl
  | _::_, 0 => rfl
  | x::xs, n+1 => congrArg (x :: .) <| erase_set xs n new_value


end Mt.Utils
