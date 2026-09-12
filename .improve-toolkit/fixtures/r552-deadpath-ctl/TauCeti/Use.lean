/-
`TauCeti.Wrap` has been emptied: every declaration is rooted now.  The `open` below therefore
names a namespace that no longer exists, and the first reference is qualified with the WRAPPER's
name instead of the declaration's own.
-/
open TauCeti.Wrap
-- a PURE NAMESPACE token: `Wrap.Inner` is not a declaration, only a prefix of one,
-- and writing a namespace is entirely normal. It must not be reported.
open Wrap.Inner

namespace TauCeti

theorem _root_.Wrap.anchor : True := trivial

theorem _root_.Wrap.uses_overqualified : True := Wrap.tp_target

theorem _root_.Wrap.tn_correct : True := Wrap.Inner.tp_target

theorem _root_.Wrap.tn_mathlib : True := Wrap.Inner.mathlib_side

-- Declared `_root_.` inside another namespace in the fake Mathlib: a real name.
theorem _root_.Wrap.tn_rooted : True := Wrap.Inner.rooted_side

theorem _root_.Wrap.tn_namespace_token : True := by
  have : True := Wrap.Inner.tp_target
  trivial

end TauCeti
