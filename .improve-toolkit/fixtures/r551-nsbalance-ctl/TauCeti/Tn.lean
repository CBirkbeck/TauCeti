/-
The SAME file done correctly, plus the two shapes that must not fire: `public section` opened
before the namespace and never closed (green `main` does this 4600 times), and `end A.B` closing a
compound namespace.
-/
public section

namespace TauCeti

namespace Tn.Compound

section Inner

theorem tn_a : True := trivial

end Inner

end Tn.Compound

end TauCeti
