namespace TauCeti

/-- Flagged, and this PR roots it: `TauCeti.Wrap.tp_rooted` -> `Wrap.tp_rooted`. -/
theorem Wrap.tp_rooted : True := trivial

/-- NOT flagged. Review asked the PR to root LESS, so this one loses a namespace level instead:
`TauCeti.Wrap.tp_derooted` -> `TauCeti.tp_derooted`. -/
private theorem Wrap.tp_derooted : True := trivial

end TauCeti
