theorem tp_dead_have (a b : Nat) : a + b = b + a := by
  have hdead : a = a := rfl
  exact Nat.add_comm a b

theorem tn_used_have (a b : Nat) : a + b = b + a := by
  have hlive : a = a := rfl
  rw [Nat.add_comm]
  exact hlive ▸ rfl

theorem tn_ctx_omega (a b : Nat) : a + b = b + a := by
  have hscan : a = a := rfl
  omega

theorem tn_rwa (a b : Nat) (hq : a = b) : a + b = b + a := by
  have hrwa_consumed : a = b := hq
  rwa [Nat.add_comm]

theorem tn_class_typed (P : Type) : P = P := by
  have hproj : Projective P := inferInstance
  rfl

theorem tp_dead_set (a b : Nat) : a + b = b + a := by
  set c := a + b with hcdead
  exact Nat.add_comm a b

theorem tn_used_set (a b : Nat) : a + b = b + a := by
  set c := a + b with hcused
  rw [hcused]
  exact Nat.add_comm a b

theorem tp_dead_let (a b : Nat) : a + b = b + a := by
  let cdeadlet : Nat := a + b
  exact Nat.add_comm a b

def tn_stmt_let (a : Nat) :
    let cmirror := a + 1
    cmirror = a + 1 := by
  let cmirror := a + 1
  rfl
