`TauCeti.Probability.contractable_of_exchangeable` and `TauCeti.Probability.Exchangeable.contractable`, both in `Probability/Exchangeability/Contractability.lean`, had identical signatures:

```lean
{μ : Measure Ω} {X : ℕ → Ω → α} (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    Contractable μ X
```

The second's entire proof was the first; its docstring called it the "dot-notation form of `contractable_of_exchangeable`". The repository keeps no duplicate theorem names, so this PR keeps one of them.

It keeps **`Exchangeable.contractable`**. That is the receiver form, usable as `hX.contractable hX_meas`, and it matches the neighbouring implications `MixedIID.exchangeable` and `MixedIIDWith.contractable`. The proof moves into it unchanged, together with the original docstring.

`contractable_of_exchangeable` is deleted, and its uses are repointed:

* `DeFinetti/BlockFactorization.lean` (`mixedIID_of_exchangeable`): now `hX.contractable fun i => (hX_meas i).aemeasurable`, and that file's module docstring;
* `Exchangeability/FullyExchangeable.lean` (`FullyExchangeable.measurePreserving_shift`): now `(hX.exchangeable hX_meas).contractable hX_meas`;
* `Examples/Probability/DeFinetti.lean`: now `example := @Exchangeable.contractable`;
* the module docstring of `Contractability.lean`.

`Exchangeability/Stationary.lean` already refers to `Exchangeable.contractable`. No statement changes.

Roadmap: none

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01Uud3dXqKRLcZcMgZYsDCmQ
