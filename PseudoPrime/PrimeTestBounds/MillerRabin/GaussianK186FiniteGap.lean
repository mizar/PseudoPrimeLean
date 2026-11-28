/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleResidual
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteCells

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteEnvelope
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ForwardAbel

/-! # Two exponential-polynomial terms for the finite K186 residual -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The constant log coefficient in the finite K186 polynomial has a
short interval certificate. -/
theorem k186_log_two_pi_mem : Real.log (2 * Real.pi) ∈ Set.Icc (1 : ℝ) 2 := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  refine
    ⟨(Real.le_log_iff_exp_le hp).mpr (by linarith only [Real.exp_one_lt_d9, Real.pi_gt_three]),
      (Real.log_le_iff_le_exp hp).mpr ?_⟩
  have he := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2) 4
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    Nat.factorial] at he
  linarith only [he, Real.pi_lt_d4]

/-- The finite forward margin after substituting the tested input logarithm. -/
noncomputable def k186FiniteGap (x : ℝ) : ℝ :=
  let L := Real.exp (x / 2) / gaussianK186FarScale
  0.7216056623106 * Real.exp (x / 2) - 301 / 20000 * x ^ 2 - (x + 5) ^ 2 / 6000 -
    k186ForwardEndpoint (x + 5) -
    6 / 5 -
    (3 / 8 * L + k186FiniteEnvelope 78548 L x)

/-- The rate-nine-quarters polynomial consists of the conductor profile
and the first right Euler moment. -/
noncomputable def k186GapRateNine : Polynomial ℝ :=
  let B := HighGaussianKernel.k186.realProfile.comp (Polynomial.X + Polynomial.C 5)
  Polynomial.C (Real.exp (-55 / 4) * (2 / gaussianK186FarScale)) * B +
    Polynomial.C 4 * eulerMomentPoly k186MassPoly (9 / 4)

/-- The rate-eleven-quarters polynomial combines the fixed conductor
offset, signed reflection, forward endpoint and second right Euler moment. -/
noncomputable def k186GapRateEleven : Polynomial ℝ :=
  let B := HighGaussianKernel.k186.realProfile
  let P :=
    Polynomial.C (3 * Real.log (2 * Real.pi) - 7) * B + Polynomial.C 6 * k186ReflectedMoment +
      Polynomial.C 3 * middleMomentPoly B (13 / 4) 0
  Polynomial.C (Real.exp (-55 / 4)) * P.comp (Polynomial.X + Polynomial.C 5) +
    Polynomial.C (1 / 6) * k186EulerLatePoly

/-- Group the exact residual into the two fixed polynomial terms used for
endpoint and curvature certificates. This separates the cutoff from the coefficients. -/
theorem k186_finite_gap_grouped (x : ℝ) :
    k186FiniteGap x =
      (0.7216056623106 - 3 / (8 * gaussianK186FarScale)) * Real.exp (x / 2) +
          (94173 / 1250 - 3 / 100 - 3 / 16 - 6 / 5) -
        301 / 20000 * x ^ 2 -
        (x + 5) ^ 2 / 6000 -
        Real.exp (-(9 / 4 : ℝ) * x) * k186GapRateNine.eval x -
        Real.exp (-(11 / 4 : ℝ) * x) * k186GapRateEleven.eval x -
        Real.exp (-(x + 5) / 2) * 78548 := by
  have h₁ :
    Real.exp (-(11 / 4 : ℝ) * (5 + x)) = Real.exp (-55 / 4) * Real.exp (-(11 / 4 : ℝ) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₂ : Real.exp (-(11 / 4 : ℝ) * x) * Real.exp (x / 2) = Real.exp (-(9 / 4 : ℝ) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [k186FiniteGap, k186FiniteEnvelope, k186ForwardEndpoint, k186GapRateNine,
    k186GapRateEleven, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_X, gaussianK186FarScale]
  rw [show x + 5 = 5 + x by ring]
  rw [h₁, ← h₂]
  ring

/-- The finite comparison has two polynomial decays, the H30 exponential,
and a rate-zero term for the linear part of the shifted square. -/
noncomputable def k186GapRates : Fin 4 → ℝ :=
  ![9 / 4, 11 / 4, 1 / 2, 0]

/-- The fixed profiles in the order of `k186GapRates`. -/
noncomputable def k186GapProfiles : Fin 4 → Polynomial ℝ :=
  ![k186GapRateNine, k186GapRateEleven, Polynomial.C (78548 * Real.exp (-(5 / 2))),
    Polynomial.C (1 / 600) * Polynomial.X]

/-- The slope is the difference between the certified forward coefficient
and the central conductor contribution at the tested cutoff. -/
noncomputable def k186GapSlope : ℝ :=
  0.7216056623106 - 3 / (8 * gaussianK186FarScale)

/-- Reuse the common differentiable residual for the finite cell checks. -/
theorem k186_finite_gap_eq_residual :
    k186FiniteGap =
      gaussianMidResidual k186GapSlope (94173 / 1250 - 3 / 100 - 3 / 16 - 6 / 5 - 1 / 240)
        (4 * (301 / 20000 + 1 / 6000)) k186GapRates k186GapProfiles := by
  funext x
  rw [k186_finite_gap_grouped]
  have hE : Real.exp (-(x + 5) / 2) = Real.exp (-(1 / 2 : ℝ) * x) * Real.exp (-(5 / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hE]
  simp only [gaussianMidResidual, k186GapSlope, gaussianDecaySum, k186GapRates, k186GapProfiles,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, neg_zero, zero_mul, Real.exp_zero]
  ring

/-- A positive finite margin supplies the K186 budget used by the uniform
interval theorem and both primality criteria. -/
theorem k186_budget_of_positive_gap (h : ∀ x ∈ Set.Icc (30 : ℝ) 61, 0 < k186FiniteGap x) :
    K186FiniteBudget := by
  apply k186_budget_of_finite_check
  intro x hx
  exact sub_pos.mp (h x hx)

/-- The two endpoint inequalities and one signed curvature upper bound
per cell suffice for the remaining K186 comparison. -/
theorem k186_budget_of_gap_cells
    (hl : ∀ i : Fin 20, ((k186FiniteCell i).lowerLeft : ℝ) ≤ k186FiniteGap (k186FiniteCell i).left)
    (hr :
      ∀ i : Fin 20, ((k186FiniteCell i).lowerRight : ℝ) ≤ k186FiniteGap (k186FiniteCell i).right)
    (hc :
      ∀ i : Fin 20,
        ∀ x ∈ Set.Ioo ((k186FiniteCell i).left : ℝ) (k186FiniteCell i).right,
          gaussianMidResidualCurv k186GapSlope (4 * (301 / 20000 + 1 / 6000)) k186GapRates
              k186GapProfiles x ≤
            ((k186FiniteCell i).upperCurvature : ℝ)) :
    K186FiniteBudget := by
  apply k186_budget_of_positive_gap
  rw [k186_finite_gap_eq_residual] at hl hr ⊢
  intro x hx
  exact
    k186_finite_pos_of_cells
      (fun i ↦ gaussian_mid_cell_bounds (k186FiniteCell i) _ _ _ _ _ (hl i) (hr i) (hc i)) hx

end PseudoPrime.PrimeTestBounds.MillerRabin
