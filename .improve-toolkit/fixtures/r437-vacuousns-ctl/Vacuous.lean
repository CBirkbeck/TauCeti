import TauCeti.Basic

namespace TauCeti

/-! A nested block whose declarations are ALL `_root_`-anchored and whose internal
reference is written in full -- the shape #5838 removed and merged green. -/
namespace Warped

theorem _root_.Warped.alphaOne : True := trivial

/-- Refers to its sibling **in full**, so the wrapper carries no resolution weight. -/
theorem _root_.Warped.betaTwo : True := Warped.alphaOne

end Warped

/-! LOAD-BEARING (r389, a red build): `deltaFour` names its sibling by SHORT name, which only
resolves because the enclosing `namespace Loadbear` supplies the prefix. Removing the block
would raise `unknown identifier gammaThree`. -/
namespace Loadbear

theorem _root_.Loadbear.gammaThree : True := trivial

theorem _root_.Loadbear.deltaFour : True := gammaThree

end Loadbear

/-! Declares into ITSELF, so the block is not vacuous. -/
namespace Ownkid

theorem epsilonFive : True := trivial

end Ownkid

/-! A docstring mention is NOT a reference: the first cut of the sibling check counted
comment and backtick text and dropped the historical control from 6 to 4. -/
namespace Docmask

theorem _root_.Docmask.zetaSix : True := trivial

/-- Mentions `zetaSix` only in prose; the body writes it in full. -/
theorem _root_.Docmask.etaSeven : True := Docmask.zetaSix

end Docmask

end TauCeti
