namespace TauCeti
namespace Wrap

/-- Flagged by the linter: the receiver is a Mathlib root namespace. -/
theorem tp_flagged : True := trivial

/-- NOT flagged: a private general helper that came along because the wrapper was retired. -/
private theorem tp_unflagged : True := trivial

end Wrap
end TauCeti
