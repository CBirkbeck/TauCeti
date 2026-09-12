/-!
# A header block whose prose must survive untouched

* [a link whose URL alone pushes this docstring bullet far past one hundred columns](https://example.invalid/aaaa/bbbb/cccc)
-/
theorem tp_split {K : Type*} [ClassOne K] [ClassTwo K] [AClassWithSeveralArguments K K K K K K K K K] : True := by
  rw [ContinuousLinearMap.index_def, ContinuousLinearMap.index_def, ContinuousLinearMap.toLinearMap_neg, LinearMap.index_neg]

theorem tn_unbreakable : True :=
  (ContinuousLinearMap.someVeryLongNameIndeed (ContinuousLinearMap.anotherExtremelyLongNameHere x y z))
