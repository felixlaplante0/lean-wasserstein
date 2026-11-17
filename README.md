# Lean Wasserstein Subadditivity

A Lean 4 formalization of the non-strict subadditivity inequality for the squared 2-Wasserstein distance:

$$
W_2\!\left(\sum_i\alpha_i S_i,\sum_i\alpha_i Z_i\right)^2
\leq \sum_i\alpha_i^2 W_2(S_i,Z_i)^2.
$$

The variables are centered and have finite second moments. Each family is independent within itself. No independence between the two families is required, and the coefficients can be arbitrary real numbers.

## Formal statements

[`WassersteinSubadditivity.lean`](WassersteinSubadditivity.lean) provides:

- `wasserstein_linear_combination`: the inequality for centered real probability laws with finite second moments.
- `wasserstein_linear_combination_randomVariables`: the inequality for measurable, centered, square-integrable random variables, with independence within each family.

Both statements allow any finite index type, including the empty type.

`linearLaw α μ` is the pushforward of the product of the laws `μ i` under the weighted sum. `w₂sq μ ν` is the real infimum of the quadratic transport costs over couplings, intended for probability laws in P₂(ℝ). The L² fields of `Coupling` ensure that each cost is integrable. `couplingOfMarginals` proves that every probability coupling of P₂ marginals satisfies these fields, so they do not restrict the admissible couplings. The formalization defines the squared distance directly. It does not develop a metric space structure on P₂.

## Proof

Take the product of couplings whose costs are arbitrarily close to their infima. The coordinate differences are centered and independent. Additivity of variance gives the quadratic cost of the weighted sum, and approximation of the infima gives the inequality. The proof does not require the existence of optimal couplings.

## Check the proof

The project uses **Lean 4.34.0** and **Mathlib v4.34.0**. Exact dependency revisions are pinned in `lake-manifest.json`.

With [Elan](https://github.com/leanprover/elan) installed:

```sh
git clone https://github.com/felixlaplante0/lean-wasserstein-subadditivity.git
cd lean-wasserstein-subadditivity
lake exe cache get
lake env lean WassersteinSubadditivity.lean
```

The final `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`, the usual Lean/Mathlib axioms. The proof uses no `sorry`, `admit`, or additional transport axioms.
