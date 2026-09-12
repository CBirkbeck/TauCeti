/-- A file this PR does NOT touch, short-spelling both names from inside `namespace TauCeti.*`. -/

namespace TauCeti.CoveringSpace

theorem uses : True := by
  have h1 := IsCoveringMap.fiberMap
  have h2 := Shadowed.keptElsewhere
  trivial

end TauCeti.CoveringSpace
