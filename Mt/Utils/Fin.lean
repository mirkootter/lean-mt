namespace Mt.Utils.Fin

def cast {n m : Nat} (i : Fin n) (eq : n = m) : Fin m :=⟨i.val, calc
  i.val < n :=i.isLt
      n = m :=eq⟩

end Mt.Utils.Fin