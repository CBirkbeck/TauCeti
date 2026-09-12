/-- A root-level declaration: the short form `Shadowed.keptElsewhere` still resolves here, so a
reference to it must NOT be reported once the `TauCeti.` copy goes away. -/

theorem Shadowed.keptElsewhere : True := trivial
