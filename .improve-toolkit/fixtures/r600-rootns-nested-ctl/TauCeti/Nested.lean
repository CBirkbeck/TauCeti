namespace TauCeti
namespace SheafOfModules

/-- A wrapper sits between `TauCeti` and the target: the full name is
`TauCeti.SheafOfModules.LocalGeneratorsData.IsInvertible`, so rooting must keep `SheafOfModules`. -/
structure LocalGeneratorsData.IsInvertible : Prop where
  dummy : True

def LocalGeneratorsData.ofIso : True := trivial

end SheafOfModules
end TauCeti
