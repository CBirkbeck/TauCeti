theorem letI_shape_a (P : Nat) (Q : Nat) (R : Nat) (hq : Q = R) :
    letI := P
    Nat.succ Q = Nat.succ R := by
  simp [hq]

theorem letI_shape_b (P : Nat) (Q : Nat) (R : Nat) (hq : Q = R) :
    letI := P
    Nat.pred Q = Nat.pred R := by
  simp [hq]
