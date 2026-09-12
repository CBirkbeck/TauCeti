namespace TauCeti

variable {X : Type*}

namespace Wrap

variable {Y : Type*}

section Inner

theorem tp_bare : True := trivial

end Inner

end Wrap

theorem Wrap.tp_dotted : True := trivial

namespace Wrap

theorem tp_second_block : True := trivial

end Wrap

end TauCeti
