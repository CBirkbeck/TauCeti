namespace TauCeti

theorem _root_.Gone.anchor : True := trivial

-- PRE-EXISTING dead reference in CODE: `Gone.vanished_lemma` is not a declaration, and `main` has
-- carried this line for many rounds. No PR that merely opens this file wrote it.
theorem _root_.Gone.uses_dead : True := Gone.vanished_lemma

end TauCeti
