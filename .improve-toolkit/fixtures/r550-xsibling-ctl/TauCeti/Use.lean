/-
The changed file.  It declares into root `Wrap` while sitting in no `namespace Wrap`, which is
what "this PR removed the wrapper" looks like from HEAD alone -- no base tree required.
-/
namespace TauCeti

theorem _root_.Wrap.anchor : True := trivial

theorem _root_.Wrap.uses_crossfile : True := tp_crossfile

theorem _root_.Wrap.uses_nested : True := Inner.tp_nested

theorem _root_.Wrap.Sib.tp_samefile_nested : True := trivial

theorem _root_.Wrap.uses_samefile : True := Sib.tp_samefile_nested

-- r563: this header's OWN name matches a rooted `Wrap.tn_header_name` declared in
-- Decl.lean. A header is not a reference; rewriting it would move this declaration.
theorem tn_header_name : True := trivial

-- The same trap inside ONE file, which is what `siblingscan` sees: a rooted
-- `Wrap.tn_local_header` and a bare header of the same short name. Different
-- declarations; neither is a reference to the other.
theorem _root_.Wrap.tn_local_header : True := trivial

theorem tn_local_header : True := trivial

/-- Prose naming `tn_docmask_target` is a docstring, not a reference. -/
theorem _root_.Wrap.tn_prose : True := trivial

@[ext]
theorem _root_.Wrap.tn_attr : True := trivial

theorem _root_.Wrap.tn_tactic : True := by
  ext
  trivial

-- r661: a declaration written `_root_.TauCeti.X.y` is rooted INTO TauCeti, not out of it. It
-- lands exactly where the enclosing `namespace TauCeti` would put it, so no wrapper is lost and a
-- bare sibling reference still resolves. Reporting it flagged `origin/main`'s own code on #6188.
theorem _root_.TauCeti.Sig.tn_into_tauceti : True := trivial

theorem _root_.Wrap.uses_into_tauceti : True := Sig.tn_into_tauceti

end TauCeti
