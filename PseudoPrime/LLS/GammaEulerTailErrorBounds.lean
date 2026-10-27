/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PowerRiemannErrorIntegral
public import PseudoPrime.LLS.GammaEulerTailIdentity

/-! # Explicit RH error bounds for the actual signed Gamma Euler mass -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH, a finite signed power list gives an integrable common
Mangoldt-error density beyond cutoff at least one. Subtract the proved
logarithmic and linear common densities before estimating the error. -/
theorem integrableOn_powerList_error_density (hRH : RiemannHypothesis) (l : List (ℝ × ℝ))
    (hl : ∀ ab ∈ l, 1 < ab.1) {a : ℝ} (ha : 1 ≤ a) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) *
          (l.map (fun ab ↦ ab.2 * (ab.1 ^ 2 * t ^ (-ab.1 - 1)))).sum)
      (Set.Ioi a) := by
  have hs := integrableOn_powerList_density hRH l hl ha
  have ht := integrableOn_powerList_linear_density l hl (zero_lt_one.trans_le ha)
  apply (hs.sub ht).congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [Pi.sub_apply]
  ring

/-- Under RH, every finite signed power list has absolute error integral
at most the sum of coefficient magnitudes times the explicit scalar
budgets. Use justified integral addition and the triangle inequality;
absolute values apply only to the error, preserving the signed main terms. -/
theorem powerList_error_integral_abs_le (hRH : RiemannHypothesis) (l : List (ℝ × ℝ))
    (hl : ∀ ab ∈ l, 1 < ab.1) {a : ℝ} (ha : 1 ≤ a) :
    |∫ t in Set.Ioi a,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) *
            (l.map (fun ab ↦ ab.2 * (ab.1 ^ 2 * t ^ (-ab.1 - 1)))).sum| ≤
      (l.map (fun ab ↦ |ab.2| * powerRiemannErrorBudget ab.1 a)).sum := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil, mul_zero, MeasureTheory.integral_zero, abs_zero, le_refl]
  | cons ab l ih =>
    have hlt := fun ac hc ↦ hl ac (List.mem_cons_of_mem ab hc)
    have hs :=
      (powerRiemannError_density_integrable hRH (hl ab List.mem_cons_self) ha).const_mul ab.2
    have ht := integrableOn_powerList_error_density hRH l hlt ha
    have he (t : ℝ) :
      (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) *
          ((ab :: l).map (fun ac ↦ ac.2 * (ac.1 ^ 2 * t ^ (-ac.1 - 1)))).sum =
        ab.2 *
            ((AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) *
              (ab.1 ^ 2 * t ^ (-ab.1 - 1))) +
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) *
            (l.map (fun ac ↦ ac.2 * (ac.1 ^ 2 * t ^ (-ac.1 - 1)))).sum := by
      simp only [List.map_cons, List.sum_cons]
      ring
    simp only [he]
    rw [MeasureTheory.integral_add hs ht, MeasureTheory.integral_const_mul]
    simp only [List.map_cons, List.sum_cons]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    exact
      add_le_add
        (mul_le_mul_of_nonneg_left
          (powerRiemannError_integral_abs_le hRH (hl ab List.mem_cons_self) ha) (abs_nonneg ab.2))
        (ih hlt)

/-- The explicit finite RH error allowance for the actual Gamma Euler
variation beyond cutoff a. Sum the scalar integrated budgets with the
magnitudes of the fixed signed coefficients. The theorem applies for a at least one. -/
noncomputable def gammaEulerTailErrorBudget (a : ℝ) : ℝ :=
  (gammaRealPowerList.map (fun ab ↦ |ab.2| * powerRiemannErrorBudget ab.1 a)).sum

/-- The finite center for the actual common Euler mass at cutoff a.
Combine its retained integer prefix, signed Chebyshev and logarithmic
boundary terms, and explicit main integral. It uses only finite arithmetic
quantities and real elementary functions, and is enclosed by the error budget. -/
noncomputable def gammaEulerMassCenter (a : ℝ) : ℝ :=
  (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m) -
      Analysis.gammaResolventEulerWeight a * Chebyshev.psi a +
    gammaEulerLogSlope a * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a +
    gammaEulerTailMain a

/-- Under RH and cutoff at least one, the actual common Gamma Euler
error has magnitude at most its explicit finite allowance. Specialize
the signed-list error bound to the fixed rational resolvent certificate. -/
theorem gammaEulerTailError_abs_le_budget (hRH : RiemannHypothesis) {a : ℝ} (ha : 1 ≤ a) :
    |gammaEulerTailError a| ≤ gammaEulerTailErrorBudget a := by
  have h :=
    powerList_error_integral_abs_le hRH gammaRealPowerList gammaRealPowerList_exponents_gt_one ha
  simpa only [gammaEulerTailError, gammaEulerTailErrorBudget, gammaEulerVariation,
    gammaRealPowerList, List.map_map, Function.comp_def] using h

/-- Under RH and cutoff at least one, the actual total Euler mass equals
the finite center plus the signed error. Use the exact mass identity and
replace the derivative boundary by the proved explicit logarithmic slope. -/
theorem gammaEulerMass_eq_center_add_error (hRH : RiemannHypothesis) {a : ℝ} (ha : 1 ≤ a) :
    (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) =
      gammaEulerMassCenter a + gammaEulerTailError a := by
  have h := gammaEulerMass_eq_prefix_boundary_main_error hRH ha
  rw [← gammaEulerLogSlope_eq_mul_deriv (zero_lt_one.trans_le ha)] at h
  exact h

/-- Under RH and cutoff at least one, the actual common Euler mass lies
between its finite center minus and plus the explicit error allowance.
The exact identity and absolute-error bound remove the infinite numerical obligation. -/
theorem gammaEulerMass_bounds (hRH : RiemannHypothesis) {a : ℝ} (ha : 1 ≤ a) :
    gammaEulerMassCenter a - gammaEulerTailErrorBudget a ≤
        (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) ∧
      (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) ≤
        gammaEulerMassCenter a + gammaEulerTailErrorBudget a := by
  have hm := gammaEulerMass_eq_center_add_error hRH ha
  have he := abs_le.mp (gammaEulerTailError_abs_le_budget hRH ha)
  constructor <;> linarith only [hm, he.1, he.2]

/-- Finite upper bounds for the center and error allowance imply an
upper bound for the actual infinite Euler mass under RH. The cutoff is
at least one. This is the interface used by the scalar numerical certificates. -/
theorem gammaEulerMass_le_of_finite_bounds (hRH : RiemannHypothesis) {a c e : ℝ} (ha : 1 ≤ a)
    (hc : gammaEulerMassCenter a ≤ c) (he : gammaEulerTailErrorBudget a ≤ e) :
    (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) ≤ c + e := by
  exact (gammaEulerMass_bounds hRH ha).2.trans (add_le_add hc he)

end PseudoPrime.LLS
