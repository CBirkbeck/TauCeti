namespace TauCeti

/-- A reference that lives in CODE and really does move namespace. -/
theorem uses_code : True := CodeOld.widget

/-- A reference that the mutation turns into PROSE. -/
theorem uses_prose : True := ProseOld.gadget

end TauCeti

namespace Extra

/-- A line the mutation REWRITES: every name on it is re-emitted into the diff, including one
that does not move. -/
theorem uses_survivor : True := Keep.widget

end Extra
