theorem dup_one {α : Type*} (s t : Set α) (h : s ⊆ t) : s ∩ t = s := by
  exact Set.inter_eq_self_of_subset_left h

theorem dup_two {α : Type*} (s t : Set α) (h : s ⊆ t) : s ∩ t = s := by
  simp [Set.inter_eq_self_of_subset_left, h]

theorem not_dup {α : Type*} (s t : Set α) (h : t ⊆ s) : s ∩ t = t := by
  exact Set.inter_eq_self_of_subset_right h

theorem named_arg_a {α : Type*} (s : Set α) : (id (α := α) '' s) = s := by
  simp

theorem named_arg_b {α : Type*} (s : Set α) (h : s.Nonempty) : (id (α := α) '' s) = s := by
  simp
