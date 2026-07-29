/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Circle

/-!
# Deprecated: the circular-arc index integrals moved to `Winding/Number/Circle.lean`

The declarations that lived here — `indexIntegral_arc_interval`, `indexIntegral_arc`,
`windingNumber_at_i`, `windingNumber_at_rho`, `windingNumber_circle` — are generic `circleMap`
results rather than model-sector ones, so they now live in
`TauCeti.Analysis.Contour.Winding.Number.Circle`. This module re-exports them so existing imports
keep working; new code should import that module directly.

`TauCeti/Analysis/Contour/ModelSector/` retains the genuinely model-sector material:
`Corner.lean` (the two-ray corner) and `Closed.lean` (the assembled sector and its winding number).
-/

public section

end
