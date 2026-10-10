/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.PaperDefinitions
public import PseudoPrime.LLS.Extensions.QNeOneLogWeightedBounds

/-!
# General L-function estimates and Q-ne-one contradictions

The four general-function propositions state the generalized Lemma 2.5, reciprocal and
zero-mass formulas, and asymptotic bounds on L-values.
They are specifications, not assumptions or placeholder proofs. The generalized Lemma 2.5
has an explicit uniform remainder bound; the other asymptotic bounds are filter statements.
The remaining propositions describe the existing externally used Q-ne-one branch proofs.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- The logarithmic value formula for analytically admissible general L-functions under
individual RH. The conclusion includes summability of completed-zero mass and, for every
`x ≥ 2`, two real coefficients of absolute value at most one. They represent the zero and
gamma errors; the latter is bounded by `2 * degree / (x * (log x)²)` uniformly in the data.
Proof: Mellin inversion, centered Hadamard and digamma series give the shifted formula;
integrate in the real shift and evaluate the endpoint logarithmic derivative. Inverse-power
zero mass justifies integral exchange, and `Re κ ≥ 0` gives the gamma residue bound.
The public proof is `lls_propL1_general_proof`. Degree-one primitive Dirichlet data yields
Lemma 2.5, and the uniform cutoff range permits `x = (log C)²/(4d²)` in value estimates. -/
def lls_propL1_general : Prop :=
  ∀ f : GeneralLFunction,
    f.IsAdmissible →
      f.RiemannHypothesis →
      Summable f.zeroMassTerm ∧
        ∀ x : ℝ,
          2 ≤ x →
            ∃ θ₁ θ₂ : ℝ,
              |θ₁| ≤ 1 ∧
                |θ₂| ≤ 1 ∧
                Real.log ‖f.L 1‖ =
                  (f.logValueSum x).re + f.gammaLogDerivativeAtOne / Real.log x -
                      (1 / (2 * Real.log x) + θ₁ / (Real.sqrt x * (Real.log x) ^ 2)) * f.zeroMass +
                    2 * (f.degree : ℝ) * θ₂ / (x * (Real.log x) ^ 2)

/-- The smoothed reciprocal formula for admissible data under individual RH.
Its conclusion includes summable zero mass, a real coefficient bounded by one for every
`x ≥ 2`, and a remainder `O((log C + degree * log x)/x)` as `x → ∞` for the fixed function.
The zero-mass coefficient is `θ(x)/√x - 1/(2x)`; the coefficient and remainder are chosen in
the conclusion. Reciprocal Mellin inversion gives the arithmetic sum; the centered Hadamard
expansion bounds the zero contribution, and summable gamma residues give the fixed-function
remainder. The public theorem `lls_propL2_proof` proves this proposition. -/
def lls_propL2 : Prop :=
  ∀ f : GeneralLFunction,
    f.IsAdmissible →
      f.RiemannHypothesis →
      Summable f.zeroMassTerm ∧
        ∃ θ r : ℝ → ℝ,
          (∀ x : ℝ,
              2 ≤ x →
                |θ x| ≤ 1 ∧
                  -(logDeriv f.L 1).re =
                    (f.reciprocalWeightedSum x).re +
                      (θ x / Real.sqrt x - 1 / (2 * x)) * f.zeroMass +
                      r x) ∧
            Asymptotics.IsBigO Filter.atTop r
              (fun x : ℝ ↦ (Real.log f.analyticConductor + f.degree * Real.log x) / x)

/-- For admissible data under individual RH, zero mass is summable and equals
`log C - 2 * Re(reciprocalSum x) + r(x)` for every `x ≥ 2`, where the remainder is
`O(degree + log C/√x)` for the fixed function. This relates the zero mass to an arithmetic
sum for use in L-value bounds. The exact reciprocal formula bounds the smoothed arithmetic
sum, and Chebyshev's estimate controls removal of smoothing. The resulting bounded error
has the stated Big-O size because the degree is positive. `lls_sumzeros_proof` proves this
fixed-function statement; no uniform constant over L-functions is asserted. -/
def lls_sumzeros : Prop :=
  ∀ f : GeneralLFunction,
    f.IsAdmissible →
      f.RiemannHypothesis →
      Summable f.zeroMassTerm ∧
        ∃ r : ℝ → ℝ,
          (∀ x : ℝ,
              2 ≤ x →
                f.zeroMass = Real.log f.analyticConductor - 2 * (f.reciprocalSum x).re + r x) ∧
            Asymptotics.IsBigO Filter.atTop r
              (fun x : ℝ ↦ f.degree + Real.log f.analyticConductor / Real.sqrt x)

/-- Upper bounds on `‖L(1)‖` and its reciprocal, uniform over admissible RH functions
of each fixed positive degree as analytic conductor tends to infinity. The independent
real errors tend to zero and are `O(d²(log d)²/log log C)` on that family.
For degree one this Big-O scale vanishes, so the stated condition requires eventual zero
errors. No public proof is supplied. Proof sketch: combine the logarithmic and reciprocal
formulas, choose `x = (log C)²/(4d²)`, and bound the truncated Euler products on both sides. -/
def lls_generalL : Prop :=
  ∀ d : ℕ,
    0 < d →
      ∃ eUpper eReciprocal : GeneralLFunction.FixedDegreeFamily d → ℝ,
        Asymptotics.IsLittleO (GeneralLFunction.conductorFilter d) eUpper (fun _ ↦ (1 : ℝ)) ∧
          Asymptotics.IsLittleO (GeneralLFunction.conductorFilter d) eReciprocal (fun _ ↦ (1 : ℝ)) ∧
          Asymptotics.IsBigO (GeneralLFunction.conductorFilter d) eUpper
            (fun f ↦ (d : ℝ) ^ 2 * (Real.log d) ^ 2 / Real.log (Real.log f.val.analyticConductor)) ∧
          Asymptotics.IsBigO (GeneralLFunction.conductorFilter d) eReciprocal
            (fun f ↦ (d : ℝ) ^ 2 * (Real.log d) ^ 2 / Real.log (Real.log f.val.analyticConductor)) ∧
          ∀ᶠ f in GeneralLFunction.conductorFilter d,
            ‖f.val.L 1‖ ≤
                (2 * Real.exp Real.eulerMascheroniConstant) ^ d *
                  ((Real.log (Real.log f.val.analyticConductor)) ^ d -
                    ((d : ℝ) * Real.log d + d * (Real.log 2 - 1 / 2) + eUpper f) *
                      (Real.log (Real.log f.val.analyticConductor)) ^ (d - 1)) ∧
              1 / ‖f.val.L 1‖ ≤
                (12 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2) ^ d *
                  ((Real.log (Real.log f.val.analyticConductor)) ^ d -
                    ((d : ℝ) * Real.log d + d * (Real.log 2 - 1 / 2) + eReciprocal f) *
                      (Real.log (Real.log f.val.analyticConductor)) ^ (d - 1))

/-- The Q-ne-one contradiction for a nonprincipal character with nonzero modulus and conductor.
Assume its primitive character is even, GRH and both Riemann lower bounds, `y ≥ 12`,
`log conductor ≤ y + log 4`, and primitive character value `0` at two. Its value is one
on every odd prime in the specified power-dependent ranges up to `y²`.
The conclusion is `False`. The public proof uses the weighted-sum upper and lower bounds
for this branch and their numerical separation. No quadratic-character premise is required. -/
def lls_qNeOne_zero_branch : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (_hne : χ ≠ 1)
    (_heven : χ.primitiveCharacter.Even)
    (_hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (_hy : 12 ≤ y)
    (_hlogD : Real.log χ.conductor ≤ y + Real.log 4) (_hriemann : LLSRiemannWeightedLowerBound)
    (_hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (_hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (_h2 : χ.primitiveCharacter 2 = 0), False

/-- The Q-ne-one contradiction for a nonprincipal character with nonzero modulus and conductor.
Assume its primitive character is even, GRH and both Riemann lower bounds, `y ≥ 12`,
`log conductor ≤ y`, and primitive character value `-1` at two. Its value is one
on every odd prime in the specified power-dependent ranges up to `y²`.
The conclusion is `False`. The public proof uses the weighted-sum upper and lower bounds
for this branch and their numerical separation. No quadratic-character premise is required. -/
def lls_qNeOne_neg_one_branch : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (_hne : χ ≠ 1)
    (_heven : χ.primitiveCharacter.Even)
    (_hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (_hy : 12 ≤ y)
    (_hlogD : Real.log χ.conductor ≤ y) (_hriemann : LLSRiemannWeightedLowerBound)
    (_hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (_hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (_h2 : χ.primitiveCharacter 2 = -1), False

/-- The Q-ne-one contradiction for a nonprincipal character with nonzero modulus and conductor.
Assume its primitive character is even, GRH and both Riemann lower bounds, `y ≥ 12`,
`log conductor ≤ y`, and primitive character value `1` at two. Its value is one
on every odd prime in the specified power-dependent ranges up to `y²`.
The conclusion is `False`. The public proof uses the weighted-sum upper and lower bounds
for this branch and their numerical separation. No quadratic-character premise is required. -/
def lls_qNeOne_one_branch : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (_hne : χ ≠ 1)
    (_heven : χ.primitiveCharacter.Even)
    (_hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (_hy : 12 ≤ y)
    (_hlogD : Real.log χ.conductor ≤ y) (_hriemann : LLSRiemannWeightedLowerBound)
    (_hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (_hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (_h2 : χ.primitiveCharacter 2 = 1), False

end PseudoPrime.LLS.Extensions
