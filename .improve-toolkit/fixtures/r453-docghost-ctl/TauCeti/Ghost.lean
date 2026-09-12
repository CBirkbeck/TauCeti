import TauCeti.Upstream

/-!
# Fixture for docghost

## Main declarations

* `tp_unreachableName`: declared only in `TauCeti/Downstream.lean`, which this file does NOT
  import — the #5579 defect this screen exists to find.
* `tn_reachableName`: declared in `TauCeti/Upstream.lean`, which this file DOES import, so it is
  advertised legitimately.
* `tn_staleName`: declared nowhere in the tree — a stale name, which is a DIFFERENT defect and
  must not be narrowed into the #5579 bucket.
* `tn_presentHere`: declared right below.
* `TauCeti.Wrapped.tn_qualifiedName`: advertised fully qualified, declared bare inside
  `namespace Wrapped`; leaf matching must resolve it.
* `tn_dottedDecl`: advertised bare, declared with a dotted header; leaf matching must resolve
  that direction too.
-/

namespace TauCeti

theorem tn_presentHere : True := trivial

theorem Something.tn_dottedDecl : True := trivial

namespace Wrapped

theorem tn_qualifiedName : True := trivial

end Wrapped

end TauCeti
