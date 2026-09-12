/-
`map_injective` is declared in a TOP-LEVEL namespace, outside `namespace TauCeti`, so its old full
name carries no `TauCeti.` prefix to guess at. The control renames it and checks that the two
surviving references -- one prose, one code -- are still found.
-/
namespace HomotopyGroup

/-- `HomotopyGroup.map_injective` is named here in prose. -/
theorem map_injective : True := trivial

end HomotopyGroup

namespace TauCeti

theorem uses_it : True := HomotopyGroup.map_injective

end TauCeti

namespace TauCeti

namespace Rooted

/-- A genuine rooting: this becomes `_root_.Rooted.to_root`, i.e. `TauCeti.Rooted.to_root` ->
`Rooted.to_root`, which is the one declaration-set change a rooting PR is allowed to make. -/
theorem to_root : True := trivial

end Rooted

end TauCeti
