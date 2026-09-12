import TauCeti.Foo.TnImportMod

%example tp_outside
/-- Outside `TauCeti/`, in a SEPARATE lake project the sandboxed build never compiles. -/
theorem tp_outside {A : Type*} (φ : A) : True :=
  TauCeti.Foo.tp_dangler φ
%end
