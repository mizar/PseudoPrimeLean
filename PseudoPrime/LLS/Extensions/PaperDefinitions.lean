/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperDefinitions
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import PseudoPrime.AnalyticNumberTheory.General.EntireOrder

/-!
# General L-function data, analytic hypotheses and arithmetic sums

The functions, coefficients and local parameters are data. `IsAdmissible` states the
arithmetic and analytic compatibility conditions, independently of the estimates to be proved.
Zeros of the completed function are weighted by their actual analytic multiplicity.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- Data for an L-function with degree, arithmetic conductor, complex gamma shifts,
local Euler roots, Dirichlet coefficients, ordinary continuation and completed continuation.
The structure alone imposes no analytic or arithmetic conditions. `IsAdmissible` requires
positive degree and conductor, normalization, root bounds, convergence, an entire completion
of order at most one, and a conjugate functional equation. The completed continuation is
supplied independently so that values at removable gamma singularities are represented. -/
structure GeneralLFunction where
  /-- The degree, also the number of gamma shifts and local roots at each prime. -/
  degree : ℕ
  /-- The arithmetic conductor before multiplication by archimedean factors. -/
  conductor : ℕ
  /-- Gamma shifts with nonnegative real parts under admissibility. -/
  shift : Fin degree → ℂ
  /-- Local Euler roots, indexed by a prime and the degree coordinate. -/
  root : ℕ → Fin degree → ℂ
  /-- Dirichlet-series coefficients, normalized to one at index one. -/
  coefficient : ℕ → ℂ
  /-- The continued ordinary L-function. -/
  L : ℂ → ℂ
  /-- The entire continuation of the completed function.
  Admissibility identifies it with the gamma product on `Re s > 0`, where no pole occurs. -/
  completed : ℂ → ℂ

namespace GeneralLFunction

/-- For data `f` and `s : ℂ`, the archimedean factor
`π^(-degree*s/2) * ∏ j, Γ((s + shift j)/2)`. It uses complex powers and a finite product;
its values at gamma poles follow Lean's total-function convention. Admissibility identifies
the completed function with the conductor factor times this factor times `L` on `Re s > 0`. -/
noncomputable def gammaFactor (f : GeneralLFunction) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-((f.degree : ℂ) * s) / 2) *
    ∏ j : Fin f.degree, Complex.Gamma ((s + f.shift j) / 2)

/-- For a natural index `p` and `s : ℂ`, the local factor
`∏ j, (1 - root p j / p^s)⁻¹`. The definition accepts any natural index; admissibility
uses it at primes to specify the Euler product in `Re s > 1`. -/
noncomputable def eulerFactor (f : GeneralLFunction) (p : ℕ) (s : ℂ) : ℂ :=
  ∏ j : Fin f.degree, (1 - f.root p j / (p : ℂ) ^ s)⁻¹

/-- Arithmetic and analytic compatibility conditions on general L-function data.
The degree and conductor are positive, the coefficient at one is one, gamma shifts have
nonnegative real parts, and local roots at primes have norm at most one. In `Re s > 1`,
the Dirichlet series is absolutely summable and equals `L`; the Euler factors are multipliable,
their principal logarithms are summable, and their product also equals `L`.
In `Re s > 0`, the completion agrees with the conductor and gamma product. It is entire,
has order at most one, and satisfies the conjugate functional equation with a unit root number.
These are the hypotheses used to derive explicit formulas and zero-mass estimates. -/
def IsAdmissible (f : GeneralLFunction) : Prop :=
  0 < f.degree ∧
    0 < f.conductor ∧
    f.coefficient 1 = 1 ∧
    (∀ j, 0 ≤ (f.shift j).re) ∧
    (∀ p : ℕ, p.Prime → ∀ j, ‖f.root p j‖ ≤ 1) ∧
    (∀ s : ℂ,
      1 < s.re →
        LSeriesSummable f.coefficient s ∧
          f.L s = LSeries f.coefficient s ∧
          Multipliable (fun p : Nat.Primes ↦ f.eulerFactor p s) ∧
          Summable (fun p : Nat.Primes ↦ Complex.log (f.eulerFactor p s)) ∧
          f.L s = ∏' p : Nat.Primes, f.eulerFactor p s) ∧
    (∀ s : ℂ, 0 < s.re → f.completed s = (f.conductor : ℂ) ^ (s / 2) * f.gammaFactor s * f.L s) ∧
    Differentiable ℂ f.completed ∧
    AnalyticNumberTheory.General.HasOrderAtMostOne f.completed ∧
    (∃ ε : ℂ,
      ‖ε‖ = 1 ∧ ∀ s : ℂ, f.completed s = ε * (starRingEnd ℂ) (f.completed (1 - (starRingEnd ℂ) s)))

/-- The real analytic conductor `q/π^d * ∏ j, ‖(1 + shift j)/2‖`.
The norms permit complex shifts. This normalization is used in the asymptotic value and
zero-mass statements and in the filter on families of fixed degree. -/
noncomputable def analyticConductor (f : GeneralLFunction) : ℝ :=
  (f.conductor : ℝ) / Real.pi ^ f.degree * ∏ j : Fin f.degree, ‖(1 + f.shift j) / 2‖

/-- The local logarithmic-derivative coefficient `a_f(p^k) = Σ_j α_j(p)^k`.
The exponent is positive in applications to prime powers. -/
noncomputable def primePowerCoefficient (f : GeneralLFunction) (p k : ℕ) : ℂ :=
  ∑ j : Fin f.degree, f.root p j ^ k

/-- The coefficient `a_f(n)` is zero outside prime powers.
At a prime power, `minFac` recovers its prime and `factorization` recovers its exponent. -/
noncomputable def mangoldtCoefficient (f : GeneralLFunction) (n : ℕ) : ℂ :=
  if IsPrimePow n then f.primePowerCoefficient n.minFac (n.factorization n.minFac) else 0

/-- The reciprocal sum `Σ_{n≤x} a_f(n) Λ(n)/n`, with positive natural indices.
It is the unweighted sum occurring in the zero-mass estimate. -/
noncomputable def reciprocalSum (f : GeneralLFunction) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
    f.mangoldtCoefficient n * (ArithmeticFunction.vonMangoldt n / (n : ℝ) : ℝ)

/-- The finite sum of `a_f(n) * Λ(n)/n * (1 - n/x)` over `0 < n ≤ floor x`.
The real weight is coerced to ℂ. This is the arithmetic term in the smoothed logarithmic-
derivative formula `lls_propL2`. -/
noncomputable def reciprocalWeightedSum (f : GeneralLFunction) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
    f.mangoldtCoefficient n * (ArithmeticFunction.vonMangoldt n / (n : ℝ) * (1 - (n : ℝ) / x) : ℝ)

/-- The logarithmic L-value sum has weight `Λ(n)/(n log n) log(x/n)/log x`.
The index one contributes zero under total division. -/
noncomputable def logValueSum (f : GeneralLFunction) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
    f.mangoldtCoefficient n *
      (ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n) * (Real.log (x / n) / Real.log x) :
        ℝ)

/-- The finite prime-power sum with weight `Λ(n)(1/(n log n)-1/(x log x))`.
Combining the generalized logarithmic and reciprocal formulas produces this sum. -/
noncomputable def truncatedValueSum (f : GeneralLFunction) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
    f.mangoldtCoefficient n *
      (ArithmeticFunction.vonMangoldt n * (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)) : ℝ)

/-- The subtype of complex points at which the completed function vanishes.
Multiplicity is not stored in the subtype; `zeroMassTerm` computes it using analytic order.
Under admissibility and RH, these zeros lie on `Re s = 1/2`. -/
abbrev Zero (f : GeneralLFunction) :=
  { ρ : ℂ // f.completed ρ = 0 }

/-- The contribution `analyticOrderNatAt completed ρ / ‖ρ‖²` of one completed zero.
It is real and nonnegative and uses the natural analytic order as its multiplicity.
`zeroMass` sums these terms; the convergence results establish their summability. -/
noncomputable def zeroMassTerm (f : GeneralLFunction) (ρ : f.Zero) : ℝ :=
  (analyticOrderNatAt f.completed ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2

/-- The real sum of `zeroMassTerm` over all completed zeros, including their multiplicities.
This totalized sum does not by itself assert convergence. Under admissibility and individual
RH, summability is proved and the mass controls completed-zero errors in explicit formulas. -/
noncomputable def zeroMass (f : GeneralLFunction) : ℝ :=
  ∑' ρ : f.Zero, f.zeroMassTerm ρ

/-- RH for this general L-function means every completed zero has real part one half.
It concerns this function alone and does not reuse Dirichlet-character GRH. -/
def RiemannHypothesis (f : GeneralLFunction) : Prop :=
  ∀ ρ : f.Zero, (ρ : ℂ).re = 1 / 2

/-- The real endpoint contribution
`log(q/π^d)/2 + (∑ j, Re(digamma((1 + shift j)/2)))/2`.
Here digamma is written as the logarithmic derivative of complex Gamma. Subtracting this
quantity from half the zero mass gives `Re(L'/L)(1)` for admissible RH data. -/
noncomputable def gammaLogDerivativeAtOne (f : GeneralLFunction) : ℝ :=
  Real.log ((f.conductor : ℝ) / Real.pi ^ f.degree) / 2 +
    (∑ j : Fin f.degree, (logDeriv Complex.Gamma ((1 + f.shift j) / 2)).re) / 2

/-- Admissible RH functions of a fixed degree, the uniform family in `generalL`.
No value estimate or explicit formula is included in the subtype conditions. -/
abbrev FixedDegreeFamily (d : ℕ) :=
  { f : GeneralLFunction // f.degree = d ∧ f.IsAdmissible ∧ f.RiemannHypothesis }

/-- The conductor tends to infinity through admissible RH functions of fixed degree.
Pulling back `atTop` expresses a threshold uniform over the whole family. -/
noncomputable def conductorFilter (d : ℕ) : Filter (FixedDegreeFamily d) :=
  Filter.comap (fun f : FixedDegreeFamily d ↦ f.val.analyticConductor) Filter.atTop

end GeneralLFunction

end PseudoPrime.LLS.Extensions
