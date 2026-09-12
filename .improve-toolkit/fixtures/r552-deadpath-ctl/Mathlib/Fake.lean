namespace Wrap.Inner
theorem mathlib_side : True := trivial
end Wrap.Inner

namespace Unrelated
-- `_root_.` ESCAPES the namespace stack: the full name is `Wrap.Inner.rooted_side`, NOT
-- `Unrelated.Wrap.Inner.rooted_side`. Mathlib declares thousands of names this way.
theorem _root_.Wrap.Inner.rooted_side : True := trivial
end Unrelated
