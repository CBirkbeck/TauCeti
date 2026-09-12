import TauCeti.Basic

namespace TauCeti

namespace Wrapped

/-- Header written BARE inside `namespace Wrapped`: rooting it costs `_root_.Wrapped.`,
which is 7 + 8 + 1 = 16 characters, not 7. -/
lemma tp_bareHeader : True := trivial

end Wrapped

end TauCeti
