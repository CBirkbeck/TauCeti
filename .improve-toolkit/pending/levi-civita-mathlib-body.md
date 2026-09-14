Mathlib now has the Levi-Civita connection ([mathlib4#36845](https://github.com/leanprover-community/mathlib4/pull/36845), in the pinned Mathlib): the predicate `CovariantDerivative.IsLeviCivitaConnection`, the connection `CovariantDerivative.leviCivitaConnection` with `isLeviCivitaConnection_leviCivitaConnection`, and uniqueness `IsLeviCivitaConnection.uniqueness`. Tau Ceti carried a parallel development whose files cite that PR as the design they followed against an older pin. Following the no-compatibility rule, this PR moves Tau Ceti onto Mathlib's declarations and deletes the local copies.

## Deleted: superseded by Mathlib

| Tau Ceti (deleted) | Mathlib |
|---|---|
| `CovariantDerivative.IsLeviCivita` (fields `torsion_eq_zero`, `isMetricCompatible`) | `CovariantDerivative.IsLeviCivitaConnection` (fields `isMetricCompatible`, `torsion`) |
| `CovariantDerivative.IsLeviCivita.unique` | `CovariantDerivative.IsLeviCivitaConnection.uniqueness` |
| `CovariantDerivative.leviCivita` | `CovariantDerivative.leviCivitaConnection` |
| `CovariantDerivative.isLeviCivita_leviCivita` | `CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection` |
| `CovariantDerivative.exists_isLeviCivita` | `⟨_, isLeviCivitaConnection_leviCivitaConnection I⟩` |

`LeviCivita/Existence.lean` is deleted along with the construction. That covers `leviCivita`, its private helpers, `two_inner_leviCivita_apply`, and `TauCeti.Manifold.koszulHom` with `koszulHom_apply` and `koszulHom_apply_eq_extend`; the `koszulHom` lemmas existed only to build the connection.

## Kept: restated on Mathlib's predicate

Mathlib has no counterpart for these. Their content is unchanged; they move from `IsLeviCivita` to `IsLeviCivitaConnection`:

* `IsLeviCivitaConnection.sub_eq_mlieBracket` and `.mvfderiv_inner_eq`.
* `.two_inner_eq_koszul`, the Koszul formula in terms of `TauCeti.Manifold.koszul`. Mathlib's `IsLeviCivitaConnection.apply_eq` is the same identity with the expression written out.
* `.difference_eq_zero`, now proved from Mathlib's `uniqueness`.
* `isLeviCivitaConnection_iff`, the Koszul formula characterising Levi-Civita connections.
* `two_inner_leviCivitaConnection_eq_koszul`, the Koszul formula for Mathlib's connection. It was `two_inner_leviCivita_eq_koszul`, and it is the one input `LeviCivita/Regularity.lean` takes from the connection.

The Koszul-expression API (`TauCeti.Manifold.koszul` and its lemmas) is untouched.

## Renamed along with the connection

Mathlib does not yet have the smoothness results in `LeviCivita/Regularity.lean`. That file now refers to `leviCivitaConnection`, and its results are renamed to match:

* `contMDiffOn_leviCivitaConnection`
* `contMDiffCovariantDerivativeOn_leviCivitaConnection`
* `contMDiffOn_christoffelSymbol_leviCivitaConnection`
* `contMDiffOn_christoffelMap_leviCivitaConnection`
* `instContMDiffCovariantDerivativeLeviCivitaConnection`

The geodesic files `Geodesic/{Basic,ConstantSpeed,Reparametrization,Smoothness,Spray}.lean` now use `leviCivitaConnection I M`. `ConstantSpeed` takes metric compatibility from Mathlib's `isMetricCompatible_leviCivitaConnection`.

## Imports

`LeviCivita/Basic.lean` now imports `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita` instead of `…CovariantDerivative.Metric` and `…Torsion`, both of which that module re-exports. `Existence.lean` publicly imported `LeviCivita.Basic` and `Riemannian.Riesz`. Its two importers, `LeviCivita/Regularity.lean` and `Geodesic/Basic.lean`, now import both directly, so no downstream import closure shrinks.

## Notes for review

* The four moves `IsLeviCivita.X` → `IsLeviCivitaConnection.X` are deliberate. The receiver predicate is replaced, and each proof reads the same defining property from Mathlib's structure (`h.torsion`, `h.isMetricCompatible`).
* The two structures list their fields in opposite orders, so `isLeviCivitaConnection_iff` now builds the metric field first.

Roadmap: HopfRinow

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01Uud3dXqKRLcZcMgZYsDCmQ
