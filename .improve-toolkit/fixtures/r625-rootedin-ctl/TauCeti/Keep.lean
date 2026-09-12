namespace TauCeti
namespace Wrap

/-- Rooted OUT of the surviving wrapper: full name `Wrap.tp_moved`. -/
theorem _root_.Wrap.tp_moved : True := trivial

/-- A bare reference to it cannot resolve: the wrapper opens `TauCeti.Wrap`, not `Wrap`. -/
theorem tp_uses_bare : True := tp_moved

/-- A QUALIFIED reference is fine and must not be reported. -/
theorem tp_uses_qualified : True := Wrap.tp_moved

/-- A same-named declaration in the enclosing stack shadows the rooted one (r625). -/
theorem tp_shadowed : True := trivial

/-- So a bare `tp_shadowed` resolves to `TauCeti.Wrap.tp_shadowed` and is not a breakage. -/
theorem tp_uses_shadowed : True := tp_shadowed

/-- An ATTRIBUTE is not a reference (r550/r626): `@[tp_moved]` above a declaration must not be read
as a bare use of the rooted `Wrap.tp_moved`. -/
@[tp_moved]
theorem tp_has_attribute : True := trivial

end Wrap
end TauCeti
