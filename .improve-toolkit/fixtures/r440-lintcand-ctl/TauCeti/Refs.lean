import TauCeti.Basic

namespace TauCeti

/-- Referenced only by DOT NOTATION and in prose -- neither forces a call-site edit. -/
lemma Guarded.tn_dotOnly (g : Guarded) : True := trivial

/-- Mentions `tn_dotOnly` in a docstring, which is prose, not a reference. -/
lemma useSiteOne (g : Guarded) : True := g.tn_dotOnly

/-- Referenced BARE, so rooting it would break this call site. -/
lemma Guarded.tn_bareUse (g : Guarded) : True := trivial

lemma useSiteTwo (g : Guarded) : True := tn_bareUse g

end TauCeti
