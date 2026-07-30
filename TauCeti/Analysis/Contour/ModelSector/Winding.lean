/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Circle

/-!
# Deprecated: the circular-arc winding values have moved

Every declaration that lived here — `indexIntegral_arc_interval`, `indexIntegral_arc`,
`windingNumber_circle`, `windingNumber_at_i` and `windingNumber_at_rho` — states a property of
`circleMap` rather than of the model sector, and now lives in
`TauCeti.Analysis.Contour.Winding.Number.Circle`. This module forwards to it so that
`import TauCeti.Analysis.Contour.ModelSector.Winding` keeps working; prefer importing the circle
module directly.

`TauCeti/Analysis/Contour/ModelSector/` retains the genuinely model-sector material:
`Corner.lean` (the two-ray corner) and `Closed.lean` (the assembled sector and its winding number).
-/
