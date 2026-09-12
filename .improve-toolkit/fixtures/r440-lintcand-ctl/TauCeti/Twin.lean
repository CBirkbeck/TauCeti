import TauCeti.Basic

/-!
The r439 trap: this file declares the SAME short name in two namespaces. A short-name regex
finds `tp_twinTarget` at the bottom -- the one that is NOT flagged.
-/

namespace TauCeti

/-- Flagged declaration, written DOTTED directly inside `namespace TauCeti`. -/
lemma Sheared.tp_twinTarget (M : Sheared) : True := trivial

namespace Bracketed

/-- Same short name, different namespace, NOT flagged. Its header is short, so if the screen
matches this one the reported width is far too small. -/
lemma tp_twinTarget : True := trivial

end Bracketed

end TauCeti
