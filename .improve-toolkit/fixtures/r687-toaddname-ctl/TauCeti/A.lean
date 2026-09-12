namespace TauCeti

/-- Rooted by this PR, with an explicit to_additive target: ASK. -/
@[to_additive _root_.AddSubmonoid.continuousConstVAdd
/-- additive -/]
instance _root_.Submonoid.continuousConstSMul : True := trivial

/-- Rooted, but the attribute names no target: nothing to ask. -/
@[to_additive
  /-- additive -/]
instance _root_.Submonoid.tn_noTarget : True := trivial

/-- Rooted, attribute config only, no target name: nothing to ask. -/
@[to_additive (attr := simp)]
instance _root_.Submonoid.tn_attrOnly : True := trivial

/-- NOT rooted, explicit target: not this screen's business. -/
@[to_additive AddSubmonoid.tn_nestedTarget]
instance tn_nested : True := trivial

end TauCeti
