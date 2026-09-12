theorem tp_dup (m n : ℕ) (h₁ : 0 < m + n) (h₂ : 0 < m + n) : True := trivial

theorem tn_distinct (m n : ℕ) (h₁ : 0 < m) (h₂ : 0 < n) : True := trivial

theorem tn_group (a b : ℕ) (h : 0 < a + b) : True := trivial

theorem tn_instances {G : Type*} [Group G] [Group G] : True := trivial

theorem tp_implicit {α : Type*} {s : Set α} {t : Set α} (h : s = t) : True := trivial

theorem tp_implicit_prop {α : Type*} {s t : Set α} {h₁ : s ⊆ t} {h₂ : s ⊆ t} : True := trivial

theorem tn_data_same_type {α : Type*} {s : Set α} {t : Set α} (h : s = t) : True := trivial
