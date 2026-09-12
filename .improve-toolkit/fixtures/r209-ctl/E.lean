def ctl_interval (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹

def ctl_transpose (V : Matrix ι ι R) (η : ι → R) : Matrix ι ι R := (enlargeColumn Vᵀ η)ᵀ

def ctl_compl (f : X) (S : Set Y) : X := Set.indicator {A | IsPrimeTo A Sᶜ} f

def ctl_projection_still_rejected (g : G) (dead : ℕ) : G := g.symm.trans g
