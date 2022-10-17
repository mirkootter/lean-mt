import Mt.Utils.Fin

namespace Mt.Utils.List

theorem get_in {T : Type u} (l : List T) (idx : Fin l.length)
  : (l.get idx) ∈ l :=match l, idx with
  | a::_, ⟨0, _⟩ => List.Mem.head a _
  | _::as, ⟨n + 1, isLt⟩ => List.Mem.tail _ <| get_in as ⟨n, Nat.le_of_succ_le_succ isLt⟩

theorem get_of_set {T : Type u} (l : List T) (idx : Nat) (a : T)
  (isLt : idx < (l.set idx a).length)
  : (l.set idx a).get ⟨idx, isLt⟩ = a :=match l, idx with
  | _::_, 0 => rfl
  | _::xs, n + 1 => get_of_set xs n a <| Nat.lt_of_succ_lt_succ isLt

theorem erase_subset {T : Type u} {a : T} (l : List T) (idx : Nat) 
  : a ∈ (l.eraseIdx idx) → a ∈ l :=match l, idx with
  | [], _ => id
  | x::xs, 0 => fun h => List.Mem.tail _ h
  | x::xs, n+1 => by
    intro h ; cases h
    . exact List.Mem.head ..
    . exact List.Mem.tail x <| erase_subset xs n (by assumption)

theorem set_subset {T : Type u} {a : T} (l : List T) (idx : Nat) (new_value : T)
  : a ∈ (l.set idx new_value) → a = new_value ∨ a ∈ l :=match l, idx with
  | [], _ => Or.inr
  | x::xs, 0 => by
    intro h ; cases h
    . exact Or.inl rfl
    . exact Or.inr <| List.Mem.tail _ (by assumption)
  | x::xs, n+1 => by
    intro h ; cases h
    . exact Or.inr <| List.Mem.head ..
    . cases set_subset xs n new_value (by assumption)
      . exact Or.inl (by assumption)
      . exact Or.inr <| List.Mem.tail _ (by assumption)

theorem index_exists {T : Type u} {a : T} (l : List T)
  : a ∈ l → ∃ i : Fin l.length, l.get i = a :=fun a_in_l => match l, a_in_l with
    | x::xs, a_in_l => by
      cases a_in_l
      . exists ⟨0, by simp_arith⟩
      . apply (index_exists xs (by assumption)).elim
        intro i xs_get_i
        exists ⟨i.val + 1, by simp_arith only [List.length] ; exact i.isLt⟩

theorem erase_set {T : Type u} (l : List T) (idx : Nat) (new_value : T)
  : (l.set idx new_value).eraseIdx idx = l.eraseIdx idx :=match l, idx with
  | [], _ => rfl
  | _::_, 0 => rfl
  | x::xs, n+1 => congrArg (x :: .) <| erase_set xs n new_value

theorem eq_of_in_map {U V : Type u} {f : U -> V} {l : List U} {v : V}
  : v ∈ (l.map f) → ∃ u, u ∈ l ∧ v = f u :=by
  intro v_in_map
  induction l
  . contradiction
  . rename_i head tail IH
    cases v_in_map
    . exact ⟨head, List.Mem.head .., rfl⟩
    . rename_i v_in_map_of_tail
      cases IH v_in_map_of_tail
      rename_i u u_hyp
      exact ⟨u, List.Mem.tail _ u_hyp.left, u_hyp.right⟩

theorem get_congr {T : Type u} {l l' : List T} (idx : Fin l.length)
  (eq : l = l')
  : l.get idx = l'.get (Fin.cast idx (congrArg _ eq)) :=Eq.rec
    (motive :=λ l' eq => l.get idx = l'.get (Fin.cast idx (congrArg _ eq)))
    rfl eq

theorem get_congr' {T : Type u} {l l' : List T}
  {i : Fin l.length}
  {j : Fin l'.length}
  (l_eq : l = l')
  (i_eq : i.val = j.val)
  : l.get i = l'.get j :=by
  have : j = Fin.cast i (congrArg _ l_eq) :=Fin.eq_of_val_eq i_eq.symm
  rw [this]
  exact get_congr _ l_eq

theorem get_of_map {U V : Type u} {f : U -> V} {l : List U}
  {idx : Fin (l.map f).length}
  : (l.map f).get idx = f (l.get (Fin.cast idx (List.length_map l f))) :=
  match l, idx with
  | head :: tail, ⟨0, isLt⟩ => rfl
  | head :: tail, ⟨n + 1, isLt⟩ => by
    simp only [List.map, List.get]
    rw [get_of_map]
    rfl

end Mt.Utils.List