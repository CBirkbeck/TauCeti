import TauCeti.Init

namespace TauCeti

/-- A PRE-EXISTING rooted declaration. `main` has carried this for many rounds; no PR under test
roots it, and `TauCeti.Submodule` living on elsewhere is not this PR's doing. -/
theorem _root_.Submodule.toAddSubgroup_submoduleOf : True := trivial

namespace LinearEquiv

variable (n : Nat)

theorem extendOfIsLattice : True := trivial

end LinearEquiv

end TauCeti
