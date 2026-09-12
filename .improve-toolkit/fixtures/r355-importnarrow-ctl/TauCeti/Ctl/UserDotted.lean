public import TauCeti.Ctl.Mod
public import TauCeti.Ctl.Cover

-- Uses the module ONLY through a dotted name.  A dot-excluding use test reads this file
-- as unreferenced and wrongly reports it -- the r355 defect.
theorem tn_dotted_owndecl (n : Nat) : n = n := Ctl.ctlSoleLemma n
