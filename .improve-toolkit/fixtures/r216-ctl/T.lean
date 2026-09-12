private lemma helper_only_used_by_dead (n : ℕ) : n = n := rfl

private lemma dead_consumer (n : ℕ) : n = n := helper_only_used_by_dead n

private lemma helper_also_used_by_live (n : ℕ) : n = n := rfl

private lemma dead_consumer_two (n : ℕ) : n = n := helper_also_used_by_live n

theorem live_user (n : ℕ) : n = n := helper_also_used_by_live n

private lemma plainly_live (n : ℕ) : n = n := rfl

theorem uses_plainly_live (n : ℕ) : n = n := plainly_live n
