/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerPrefix570
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval

/-! # Centered Abel summation for the section 31 Euler weight -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The real-variable Euler weight at exponent 38/25. Its values at natural
indices enter the Mangoldt sum, and its derivative controls the Abel remainder. -/
noncomputable def eulerDensity570 (t : ℝ) : ℝ :=
  t ^ (-(38 / 25 : ℝ)) * (3 / 8 + 153 / 400 * Real.log t + 2601 / 20000 * Real.log t ^ 2)

/-- At every natural index the continuous-variable formula agrees with the
Dirichlet-series weight by the negative real power identity. -/
theorem eulerDensity570_nat (n : ℕ) : eulerDensity570 n = quarterEulerWeight570 n := by
  unfold eulerDensity570 quarterEulerWeight570
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  ring

/-- The derivative of the section 31 weight, written as a negative power times a
quadratic in the logarithm to permit termwise integration of its absolute value. -/
noncomputable def eulerSlope570 (t : ℝ) : ℝ :=
  -(t ^ (-(63 / 25 : ℝ))) * (3 / 16 + 3213 / 10000 * Real.log t + 49419 / 250000 * Real.log t ^ 2)

/-- At positive arguments the product and chain rules give the explicit Euler slope. -/
theorem eulerDensity570_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt eulerDensity570 (eulerSlope570 t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hd :=
    (Real.hasDerivAt_rpow_const (p := -(38 / 25 : ℝ)) (Or.inl ht.ne')).mul
      (((hasDerivAt_const t (3 / 8 : ℝ)).add (hl.const_mul (153 / 400))).add
        ((hl.pow 2).const_mul (2601 / 20000)))
  apply hd.congr_deriv
  have hp : t ^ (-(63 / 25 : ℝ)) = t ^ (-(38 / 25 : ℝ)) / t := by
    rw [show -(63 / 25 : ℝ) = -(38 / 25 : ℝ) - 1 by norm_num only, Real.rpow_sub ht, Real.rpow_one]
  unfold eulerSlope570
  rw [show -(38 / 25 : ℝ) - 1 = -(63 / 25 : ℝ) by norm_num only, hp]
  simp only [Pi.add_apply, Pi.pow_apply]
  ring

/-- On a positive finite interval the Euler sum minus its main integral equals
the centered boundary difference minus the integral of the psi error against
the explicit slope. This specializes centered Abel summation to the section 31 tail. -/
theorem euler570_abel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
        (∫ t : ℝ in a..b, eulerDensity570 t) =
      (Chebyshev.psi b - b) * eulerDensity570 b - (Chebyshev.psi a - a) * eulerDensity570 a -
        ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * eulerSlope570 t := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) := eulerDensity570_deriv (ha.trans_le ht.1)
  have hc : ContinuousOn eulerSlope570 (Set.Icc a b) := by
    intro t ht
    have hp := (ha.trans_le ht.1).ne'
    have hl := Real.continuousAt_log hp
    exact
      ((Real.continuousAt_rpow_const t _ (Or.inl hp)).neg.mul
          ((continuousAt_const.add (continuousAt_const.mul hl)).add
            (continuousAt_const.mul (hl.pow 2)))).continuousWithinAt
  have he : Set.EqOn (deriv eulerDensity570) eulerSlope570 (Set.Icc a b) := fun t ht ↦
    (hd t ht).deriv
  have hi : MeasureTheory.IntegrableOn (deriv eulerDensity570) (Set.Icc a b) :=
    (hc.congr he).integrableOn_Icc
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval ha.le hab
      (fun t ht ↦ (hd t ht).differentiableAt) hi
  simp only [eulerDensity570_nat] at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact congrArg ((Chebyshev.psi t - t) * ·) (he ht)

end PseudoPrime.PrimeTestBounds.MillerRabin
