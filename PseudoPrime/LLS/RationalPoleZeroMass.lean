/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalPoleMajorant
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PairedEulerDifferences

/-! # Actual zero-series bounds for the fourth-order rational-pole function -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The retained two-node Euler budget at sigma=1/2+alpha and tau=1/2+beta.
Inputs are a complex character and two finite Euler prefixes; the paired difference
is kept signed. This explicit expression bounds the actual zero-series norm in
rationalPole_four_zeroMass_le, independently of Mellin inversion. -/
noncomputable def rationalPoleFourEulerBudget {q : ℕ} (χ : DirichletCharacter ℂ q)
    (A B : Finset ℕ) : ℝ :=
  (poleFourUpperWeight - poleFourLowerWeight) *
      (Real.log q / 2 + (logDeriv χ.gammaFactor ((1 / 2 + poleFourAlpha : ℝ) : ℂ)).re -
        (logDeriv (1 : DirichletCharacter ℂ 1).LFunction ((1 / 2 + poleFourAlpha : ℝ) : ℂ)).re -
        ∑ m ∈ A,
          AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (1 / 2 + poleFourAlpha) m) +
    poleFourLowerWeight *
      ((logDeriv χ.gammaFactor ((1 / 2 + poleFourAlpha : ℝ) : ℂ)).re -
            (logDeriv χ.gammaFactor ((1 / 2 + poleFourBeta : ℝ) : ℂ)).re +
          (logDeriv (1 : DirichletCharacter ℂ 1).LFunction ((1 / 2 + poleFourBeta : ℝ) : ℂ)).re -
        (logDeriv (1 : DirichletCharacter ℂ 1).LFunction ((1 / 2 + poleFourAlpha : ℝ) : ℂ)).re -
        ((1 / 2 + poleFourBeta) - (1 / 2 + poleFourAlpha)) *
          ∑ m ∈ B,
            Real.log m *
              AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (1 / 2 + poleFourBeta)
                m)

/-- For primitive nonprincipal individual-RH data at q>=2, the actual completed-zero
series weighted by the fourth-order kernel norm is summable and bounded by the retained
Euler budget, for any shift c and finite prefixes A,B. Apply the whole-height two-node
majorant to the existing divisor-weighted Poisson API. Mellin admissibility is not assumed. -/
theorem rationalPole_four_zeroMass_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) (c : ℝ) (A B : Finset ℕ) :
    Summable
        (fun ρ : ℂ ↦
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖Analysis.rationalPoleFunction 2 (13 / 25) c (Complex.I * ρ.im)‖) ∧
      (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖Analysis.rationalPoleFunction 2 (13 / 25) c (Complex.I * ρ.im)‖) ≤
        rationalPoleFourEulerBudget χ A B := by
  apply
    AnalyticNumberTheory.DirichletLFunction.zeroMass_le_of_poissonDifferenceWeight_majorant hq hRH
      hp hne hinv (σ := 1 / 2 + poleFourAlpha) (τ := 1 / 2 + poleFourBeta)
      (by norm_num only [poleFourAlpha]) (by norm_num only [poleFourAlpha, poleFourBeta])
      poleFour_node_data.2.2.1 poleFour_node_data.2.2.2 A B
      (fun t ↦ ‖Analysis.rationalPoleFunction 2 (13 / 25) c (Complex.I * t)‖)
      (fun t ↦ norm_nonneg _)
  intro t
  simpa only [add_sub_cancel_left] using norm_poleFour_le_poisson c t

end PseudoPrime.LLS.PaperStatements
