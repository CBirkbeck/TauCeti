theorem tp_unused (m : ℕ) (hdead : 0 < m) (hn : m ≠ 0) : m = m := by
  exact rfl

theorem tn_used (m : ℕ) (hm : 0 < m) : 0 < m := by
  exact hm

theorem tn_used_in_later_binder (n : ℕ) (hn : 0 < n) : True := by
  exact trivial

theorem tn_prefix_trap (m : ℕ) (h : 0 < m) : 0 < m := by
  have hm := h
  exact hm

theorem tn_ctx_omega (m : ℕ) (hquiet : 0 < m) : 0 ≤ m := by
  omega

theorem tn_subscript (m : ℕ) (h₀ : 0 < m) : 0 < m := by
  exact h₀

theorem tn_dot_field (m : ℕ) (hp : 0 < m) : 0 < m := by
  exact hp.lt_of_le' (le_refl 0) |>.trans_le (le_refl m) |>.trans_le (le_refl m)
