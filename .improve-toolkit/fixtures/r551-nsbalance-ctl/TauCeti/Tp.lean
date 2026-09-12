/-
The #6056 shape: `namespace Wrap` became `section`, but the `end` that was renamed belonged to the
nested `section Inner`, and the wrapper's own `end Wrap` was left standing.
-/
public section

namespace TauCeti

section

section Inner

theorem tp_a : True := trivial

end

theorem tp_b : True := trivial

end Wrap

end TauCeti
