module

public import Mathlib.LinearAlgebra.Basis.Defs

open Module

open scoped TensorProduct

namespace TauCeti

variable {K ι M : Type*}

/-- A block whose binder resolves ONLY through the file's `open Module`. -/
theorem tp_block_start (𝓑 : Basis ι K M) (t : TnRootType) : True := trivial

theorem tp_block_end (x : Other.tn_other_ns_decl) : True := trivial

end TauCeti
