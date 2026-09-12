/-
The OTHER file.  Everything here is already rooted under `Wrap`, exactly as a subtree PR
leaves it, and nothing in this file is a target -- so a screen that pairs one file's
declarations with that same file's uses can never see any of it.
-/
namespace TauCeti

theorem _root_.Wrap.tp_crossfile : True := trivial

theorem _root_.Wrap.Inner.tp_nested : True := trivial

theorem _root_.Wrap.tn_docmask_target : True := trivial

theorem _root_.Wrap.weyl.ext : True := trivial

theorem _root_.Wrap.tn_header_name : True := trivial

end TauCeti
