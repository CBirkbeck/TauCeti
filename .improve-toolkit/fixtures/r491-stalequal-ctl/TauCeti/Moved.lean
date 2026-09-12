/-!
# The moved file

* `Foo.tp_dangler` : rooted by this PR, so `TauCeti.Foo.tp_dangler` no longer exists.
-/
namespace TauCeti

section

theorem _root_.Foo.tp_dangler : True := trivial

end

namespace Foo

theorem tn_unmoved_kin : True := trivial

theorem tp_danglerXtra : True := trivial

end Foo

end TauCeti
