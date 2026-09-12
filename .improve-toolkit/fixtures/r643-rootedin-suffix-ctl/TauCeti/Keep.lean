namespace TauCeti
namespace Wrap

/-- Rooted OUT of the surviving wrapper, two levels deep: full name `Wrap.Inner.tp_deep`. -/
theorem _root_.Wrap.Inner.tp_deep : True := trivial

/-- A PARTIALLY QUALIFIED reference carries part of the namespace but not enough to resolve.
Inside `TauCeti.Wrap`, Lean tries `TauCeti.Wrap.Inner.tp_deep`, then `TauCeti.Inner.tp_deep`, then
root `Inner.tp_deep` -- it never tries `Wrap.Inner.tp_deep`, so this is the r643 red build. -/
theorem tp_uses_partial : True := Inner.tp_deep

/-- The FULL name resolves at root and must not be reported. -/
theorem tp_uses_full : True := Wrap.Inner.tp_deep

end Wrap
end TauCeti
