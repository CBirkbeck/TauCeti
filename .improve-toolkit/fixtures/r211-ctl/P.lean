private lemma tp_dead (n : ℕ) : n = n := rfl

private lemma tn_used (n : ℕ) : n = n := rfl

theorem consumer (n : ℕ) : n = n := tn_used n

@[simp]
private lemma tn_attributed (n : ℕ) : n + 0 = n := rfl

private lemma tn_used_by_private (n : ℕ) : n = n := rfl

private lemma tn_chain (n : ℕ) : n = n := tn_used_by_private n

theorem consumer2 (n : ℕ) : n = n := tn_chain n

private lemma tn_transpose_user (V : Matrix ι ι R) : True := trivial

theorem uses_it (V : Matrix ι ι R) : True := tn_transpose_user Vᵀ

private theorem Foo.dotted_used (x : Foo) : True := trivial

theorem dot_consumer (f : Foo) : True := f.dotted_used

private theorem Foo.dotted_dead (x : Foo) : True := trivial

private lemma namespaced_used (n : ℕ) : n = n := rfl

theorem ns_consumer (W : Curve) (n : ℕ) : n = n := W.namespaced_used n
