def tp_dead_param (n : ℕ) (junk : ℕ) : ℕ := n + 1

def tn_used_both (n : ℕ) (m : ℕ) : ℕ := n + m

def tn_used_in_type (n : ℕ) (v : Fin n) : ℕ := v.val

abbrev tp_dead_abbrev (α : Type) (dead : Type) : Type := List α
