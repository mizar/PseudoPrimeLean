/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PowerLogTailConvergence
public import PseudoPrime.Analysis.GammaSignedEulerSeries
public import PseudoPrime.Analysis.ListInfiniteSum

/-! # Signed finite combinations of power-weighted Euler tails -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH, a finite signed list of power variation densities is
integrable beyond a cutoff at least one. Each exponent is greater than
one; finite addition preserves convergence even for negative coefficients. -/
theorem integrableOn_powerList_density (hRH : RiemannHypothesis) (l : List (ℝ × ℝ))
    (hl : ∀ ab ∈ l, 1 < ab.1) {a : ℝ} (ha : 1 ≤ a) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t *
          (l.map (fun ab ↦ ab.2 * (ab.1 ^ 2 * t ^ (-ab.1 - 1)))).sum)
      (Set.Ioi a) := by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.sum_nil, mul_zero] using
      (MeasureTheory.integrableOn_zero :
        MeasureTheory.IntegrableOn (fun _ : ℝ ↦ (0 : ℝ)) (Set.Ioi a))
  | cons ab l
    ih =>
    have hs :=
      (integrableOn_power_logWeightedMangoldtSum hRH (hl ab List.mem_cons_self) ha).const_mul ab.2
    have ht := ih (fun ac hc ↦ hl ac (List.mem_cons_of_mem ab hc))
    apply (hs.add ht).congr
    apply Filter.Eventually.of_forall
    intro t
    dsimp only [Pi.add_apply]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- A finite signed list of power-weighted Mangoldt series is summable
when every exponent is greater than one. Combine the established scalar
series before taking its sum, retaining repeated nodes and coefficient signs. -/
theorem summable_powerList_weight (l : List (ℝ × ℝ)) (hl : ∀ ab ∈ l, 1 < ab.1) :
    Summable
      (fun m : ℕ ↦
        ArithmeticFunction.vonMangoldt m * (l.map (fun ab ↦ ab.2 * (m : ℝ) ^ (-ab.1))).sum) := by
  have hs :=
    Analysis.summable_list_sum l
      (fun ab m ↦ ab.2 * (ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-ab.1)))
      (fun ab hab ↦
        (AnalyticNumberTheory.Arithmetic.summable_powerMangoldtWeight (hl ab hab)).mul_left ab.2)
  apply hs.congr
  intro m
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  exact List.map_congr_left (fun ab hab ↦ by ring)

/-- Under RH, the total Euler weight of a finite signed power list minus
its prefix equals one improper logarithmic integral and the exact lower
Chebyshev and logarithmic boundary terms. Add the scalar tail identities
using proved summability and integrability, without coefficient absolute values. -/
theorem powerList_tail_eq_improper_log_integral (hRH : RiemannHypothesis) (l : List (ℝ × ℝ))
    (hl : ∀ ab ∈ l, 1 < ab.1) {a : ℝ} (ha : 1 ≤ a) :
    (∑' m : ℕ, ArithmeticFunction.vonMangoldt m * (l.map (fun ab ↦ ab.2 * (m : ℝ) ^ (-ab.1))).sum) -
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
          ArithmeticFunction.vonMangoldt m * (l.map (fun ab ↦ ab.2 * (m : ℝ) ^ (-ab.1))).sum) =
      (∫ t in Set.Ioi a,
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t *
            (l.map (fun ab ↦ ab.2 * (ab.1 ^ 2 * t ^ (-ab.1 - 1)))).sum) -
        (l.map (fun ab ↦ ab.2 * a ^ (-ab.1))).sum * Chebyshev.psi a -
        (l.map (fun ab ↦ ab.2 * ab.1 * a ^ (-ab.1))).sum *
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil, mul_zero, tsum_zero, Finset.sum_const_zero, sub_zero,
      MeasureTheory.integral_zero, zero_mul]
  | cons ab l ih =>
    have hlt := fun ac hc ↦ hl ac (List.mem_cons_of_mem ab hc)
    have he (m : ℕ) :
      ArithmeticFunction.vonMangoldt m * ((ab :: l).map (fun ac ↦ ac.2 * (m : ℝ) ^ (-ac.1))).sum =
        ab.2 * (ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-ab.1)) +
          ArithmeticFunction.vonMangoldt m * (l.map (fun ac ↦ ac.2 * (m : ℝ) ^ (-ac.1))).sum := by
      simp only [List.map_cons, List.sum_cons]
      ring
    have hi (t : ℝ) :
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t *
          ((ab :: l).map (fun ac ↦ ac.2 * (ac.1 ^ 2 * t ^ (-ac.1 - 1)))).sum =
        ab.2 *
            (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t *
              (ab.1 ^ 2 * t ^ (-ab.1 - 1))) +
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t *
            (l.map (fun ac ↦ ac.2 * (ac.1 ^ 2 * t ^ (-ac.1 - 1)))).sum := by
      simp only [List.map_cons, List.sum_cons]
      ring
    simp only [he, hi]
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [((AnalyticNumberTheory.Arithmetic.summable_powerMangoldtWeight
                (hl ab List.mem_cons_self)).mul_left
            ab.2).tsum_add
        (summable_powerList_weight l hlt),
      tsum_mul_left,
      MeasureTheory.integral_add
        ((integrableOn_power_logWeightedMangoldtSum hRH (hl ab List.mem_cons_self) ha).const_mul
          ab.2)
        (integrableOn_powerList_density hRH l hlt ha),
      MeasureTheory.integral_const_mul]
    have hs := powerMangoldtTail_eq_improper_log_integral hRH (hl ab List.mem_cons_self) ha
    have ht := ih hlt
    have hm := congrArg (fun z : ℝ ↦ ab.2 * z) hs
    nlinarith only [hm, ht]

/-- The signed logarithmic slope of the fixed common Euler weight.
Its explicit finite formula is minus the sum of b sigma t to the minus sigma.
At positive inputs it equals t times the actual derivative of the Euler weight. -/
noncomputable def gammaEulerLogSlope (t : ℝ) : ℝ :=
  -(Analysis.gammaResolventCoefficients.map
        (fun ab ↦ (ab.2 : ℝ) * ((1 / 2 : ℝ) + (ab.1 : ℝ)) * t ^ (-((1 / 2 : ℝ) + (ab.1 : ℝ))))).sum

/-- The signed variation density of the fixed common Euler weight.
Its finite formula sums b sigma squared t to the minus sigma minus one.
It is the derivative of the logarithmic slope at every positive input;
no individual coefficient or density is assumed to be nonnegative. -/
noncomputable def gammaEulerVariation (t : ℝ) : ℝ :=
  (Analysis.gammaResolventCoefficients.map
      (fun ab ↦
        (ab.2 : ℝ) * (((1 / 2 : ℝ) + (ab.1 : ℝ)) ^ 2 * t ^ (-((1 / 2 : ℝ) + (ab.1 : ℝ)) - 1)))).sum

/-- Every fixed resolvent exponent is greater than one. Cast the rational
scale certificate to the real exponent condition used for Euler-tail convergence. -/
theorem gammaResolvent_real_exponents_gt_one (ab : ℚ × ℚ)
    (hab : ab ∈ Analysis.gammaResolventCoefficients) : 1 < (1 / 2 : ℝ) + (ab.1 : ℝ) := by
  have h :=
    (Rat.cast_lt (K := ℝ)).mpr
      (List.forall_iff_forall_mem.mp Analysis.gammaResolvent_scales_gt_half ab hab)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  linarith only [h]

/-- Under RH and cutoff at least one, the actual common Gamma Euler total
minus its prefix equals the improper logarithmic integral minus its
Chebyshev boundary plus its signed logarithmic-slope boundary. Specialize
the finite signed-list theorem to the actual rational resolvent coefficients. -/
theorem gammaEulerTail_eq_improper_log_integral (hRH : RiemannHypothesis) {a : ℝ} (ha : 1 ≤ a) :
    (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m) =
      (∫ t in Set.Ioi a,
            AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * gammaEulerVariation t) -
          Analysis.gammaResolventEulerWeight a * Chebyshev.psi a +
        gammaEulerLogSlope a * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a := by
  let l :=
    Analysis.gammaResolventCoefficients.map (fun ab ↦ (((1 / 2 : ℝ) + (ab.1 : ℝ)), (ab.2 : ℝ)))
  have hl : ∀ ab ∈ l, 1 < ab.1 := by
    intro ac hac
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hac
    exact gammaResolvent_real_exponents_gt_one ab hab
  have ht := powerList_tail_eq_improper_log_integral hRH l hl ha
  dsimp only [l] at ht
  simp only [List.map_map, Function.comp_def] at ht
  simpa only [Analysis.gammaResolventMangoldtWeight, Analysis.gammaResolventEulerWeight,
    gammaEulerVariation, gammaEulerLogSlope, neg_mul, sub_eq_add_neg] using ht

/-- The derivative of a finite signed power-weight list is its finite
list of scalar derivatives at a positive input. Induction and the product
rule preserve signs and repeated nodes. This identifies the actual Euler slope. -/
theorem hasDerivAt_powerList_weight (l : List (ℝ × ℝ)) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t : ℝ ↦ (l.map (fun ab ↦ ab.2 * t ^ (-ab.1))).sum)
      (l.map (fun ab ↦ ab.2 * (-ab.1 * u ^ (-ab.1 - 1)))).sum u := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil] using (hasDerivAt_const u (0 : ℝ))
  | cons ab l ih =>
    simpa only [List.map_cons, List.sum_cons] using
      ((Analysis.powerWeight_derivative ab.1 hu).const_mul ab.2).fun_add ih

/-- The logarithmic slope of a finite signed power list has derivative
its signed variation density at positive inputs. Differentiate each term
and retain every coefficient before taking the finite sum. -/
theorem hasDerivAt_powerList_logSlope (l : List (ℝ × ℝ)) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t : ℝ ↦ -(l.map (fun ab ↦ ab.2 * ab.1 * t ^ (-ab.1))).sum)
      (l.map (fun ab ↦ ab.2 * (ab.1 ^ 2 * u ^ (-ab.1 - 1)))).sum u := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil, neg_zero] using (hasDerivAt_const u (0 : ℝ))
  | cons ab l
    ih =>
    have h := ((Analysis.powerWeight_derivative ab.1 hu).const_mul (ab.2 * ab.1)).neg
    have hs :
      HasDerivAt (fun t : ℝ ↦ -(ab.2 * ab.1 * t ^ (-ab.1))) (ab.2 * (ab.1 ^ 2 * u ^ (-ab.1 - 1)))
        u :=
      h.congr_deriv (by ring)
    simpa only [List.map_cons, List.sum_cons, neg_add] using hs.fun_add ih

/-- At a positive input the explicit Gamma logarithmic slope equals
the input times the actual derivative of the common Euler weight.
Differentiate the finite coefficient list and cancel the extra inverse power.
This aligns the certified tail boundary with the analytic partial-summation formula. -/
theorem gammaEulerLogSlope_eq_mul_deriv {u : ℝ} (hu : 0 < u) :
    gammaEulerLogSlope u = u * deriv Analysis.gammaResolventEulerWeight u := by
  have hd :=
    hasDerivAt_powerList_weight
      (Analysis.gammaResolventCoefficients.map (fun ab ↦ (((1 / 2 : ℝ) + (ab.1 : ℝ)), (ab.2 : ℝ))))
      hu
  have he :
    HasDerivAt Analysis.gammaResolventEulerWeight
      (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (ab.2 : ℝ) * (-((1 / 2 : ℝ) + (ab.1 : ℝ)) * u ^ (-((1 / 2 : ℝ) + (ab.1 : ℝ)) - 1)))).sum
      u := by
    change
      HasDerivAt
        (fun t ↦
          (Analysis.gammaResolventCoefficients.map
              (fun ab ↦ (ab.2 : ℝ) * t ^ (-((1 / 2 : ℝ) + (ab.1 : ℝ))))).sum)
        _ u
    simpa only [List.map_map, Function.comp_def] using hd
  rw [he.deriv, gammaEulerLogSlope, ← neg_one_mul, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  rw [Real.rpow_sub_one hu.ne' (-((1 / 2 : ℝ) + (ab.1 : ℝ)))]
  calc
    _ = -(ab.2 : ℝ) * ((1 / 2 : ℝ) + (ab.1 : ℝ)) * u ^ (-((1 / 2 : ℝ) + (ab.1 : ℝ))) := by ring
    _ = _ := by
      calc
        _ =
            u *
              ((ab.2 : ℝ) *
                (-((1 / 2 : ℝ) + (ab.1 : ℝ)) * (u ^ (-((1 / 2 : ℝ) + (ab.1 : ℝ))) / u))) :=
          by field_simp (discharger := exact hu.ne')
        _ = _ := rfl

/-- At a positive input the Gamma logarithmic slope has derivative the
fixed signed variation density. Specialize the signed finite-list derivative.
This identifies the density used in the improper Euler-tail integral. -/
theorem hasDerivAt_gammaEulerLogSlope {u : ℝ} (hu : 0 < u) :
    HasDerivAt gammaEulerLogSlope (gammaEulerVariation u) u := by
  have hd :=
    hasDerivAt_powerList_logSlope
      (Analysis.gammaResolventCoefficients.map (fun ab ↦ (((1 / 2 : ℝ) + (ab.1 : ℝ)), (ab.2 : ℝ))))
      hu
  change
    HasDerivAt
      (fun t ↦
        -(Analysis.gammaResolventCoefficients.map
              (fun ab ↦
                (ab.2 : ℝ) * ((1 / 2 : ℝ) + (ab.1 : ℝ)) * t ^ (-((1 / 2 : ℝ) + (ab.1 : ℝ))))).sum)
      _ u
  simpa only [gammaEulerVariation, List.map_map, Function.comp_def] using hd

/-- Under RH and cutoff at least one, the exact common Euler tail has
its lower logarithmic boundary expressed using the actual derivative of
the Euler weight. Substitute the proved logarithmic-slope identity. -/
theorem gammaEulerTail_eq_improper_log_integral_deriv (hRH : RiemannHypothesis) {a : ℝ}
    (ha : 1 ≤ a) :
    (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
        (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m) =
      (∫ t in Set.Ioi a,
            AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * gammaEulerVariation t) -
          Analysis.gammaResolventEulerWeight a * Chebyshev.psi a +
        (a * deriv Analysis.gammaResolventEulerWeight a) *
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a := by
  rw [gammaEulerTail_eq_improper_log_integral hRH ha,
    gammaEulerLogSlope_eq_mul_deriv (zero_lt_one.trans_le ha)]

/-- Under RH and cutoff at least one, the full common Euler mass equals
its retained prefix, both exact lower boundary terms and one improper
logarithmic integral. This is the double-partial-summation identity used
by the scalar numerical certificate, with all resolvent coefficients signed. -/
theorem gammaEulerMass_eq_prefix_boundary_integral (hRH : RiemannHypothesis) {a : ℝ} (ha : 1 ≤ a) :
    (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) =
      (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m) -
          Analysis.gammaResolventEulerWeight a * Chebyshev.psi a +
        (a * deriv Analysis.gammaResolventEulerWeight a) *
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a +
        (∫ t in Set.Ioi a,
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * gammaEulerVariation t) := by
  have ht := gammaEulerTail_eq_improper_log_integral_deriv hRH ha
  linarith only [ht]

/-- A signed finite list of linear power variation densities is integrable
beyond a positive cutoff when all exponents exceed one. Add the convergent
scalar densities without replacing signed coefficients by positive ones. -/
theorem integrableOn_powerList_linear_density (l : List (ℝ × ℝ)) (hl : ∀ ab ∈ l, 1 < ab.1) {a : ℝ}
    (ha : 0 < a) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦ t * (l.map (fun ab ↦ ab.2 * (ab.1 ^ 2 * t ^ (-ab.1 - 1)))).sum) (Set.Ioi a) := by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.sum_nil, mul_zero] using
      (MeasureTheory.integrableOn_zero :
        MeasureTheory.IntegrableOn (fun _ : ℝ ↦ (0 : ℝ)) (Set.Ioi a))
  | cons ab l
    ih =>
    have hs := (power_linear_density_integrable (hl ab List.mem_cons_self) ha).const_mul ab.2
    have ht := ih (fun ac hc ↦ hl ac (List.mem_cons_of_mem ab hc))
    apply (hs.add ht).congr
    apply Filter.Eventually.of_forall
    intro t
    dsimp only [Pi.add_apply]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- The linear main integral of a signed finite power list equals the
explicit sum of b sigma squared a to the one minus sigma over sigma minus
one. Justified finite integration preserves signs and repeated nodes. -/
theorem powerList_linear_density_integral_eq (l : List (ℝ × ℝ)) (hl : ∀ ab ∈ l, 1 < ab.1) {a : ℝ}
    (ha : 0 < a) :
    (∫ t in Set.Ioi a, t * (l.map (fun ab ↦ ab.2 * (ab.1 ^ 2 * t ^ (-ab.1 - 1)))).sum) =
      (l.map (fun ab ↦ ab.2 * (ab.1 ^ 2 * a ^ (1 - ab.1) / (ab.1 - 1)))).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, mul_zero, MeasureTheory.integral_zero]
  | cons ab l ih =>
    have hlt := fun ac hc ↦ hl ac (List.mem_cons_of_mem ab hc)
    have he (t : ℝ) :
      t * ((ab :: l).map (fun ac ↦ ac.2 * (ac.1 ^ 2 * t ^ (-ac.1 - 1)))).sum =
        ab.2 * (t * (ab.1 ^ 2 * t ^ (-ab.1 - 1))) +
          t * (l.map (fun ac ↦ ac.2 * (ac.1 ^ 2 * t ^ (-ac.1 - 1)))).sum := by
      simp only [List.map_cons, List.sum_cons]
      ring
    simp only [he]
    rw [MeasureTheory.integral_add
        ((power_linear_density_integrable (hl ab List.mem_cons_self) ha).const_mul ab.2)
        (integrableOn_powerList_linear_density l hlt ha),
      MeasureTheory.integral_const_mul, ih hlt,
      power_linear_density_integral_eq (hl ab List.mem_cons_self) ha]
    simp only [List.map_cons, List.sum_cons]

/-- The fixed rational resolvent certificate converted to real exponent
and signed coefficient pairs. The exponent is one half plus its rational
scale. This common list supplies all scalar convergence and main-term formulas. -/
noncomputable def gammaRealPowerList : List (ℝ × ℝ) :=
  Analysis.gammaResolventCoefficients.map (fun ab ↦ (((1 / 2 : ℝ) + (ab.1 : ℝ)), (ab.2 : ℝ)))

/-- Every exponent in the actual converted resolvent list exceeds one.
Use the rational certificate and the exact list-map membership. -/
theorem gammaRealPowerList_exponents_gt_one : ∀ ab ∈ gammaRealPowerList, 1 < ab.1 := by
  intro ac hac
  obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hac
  exact gammaResolvent_real_exponents_gt_one ab hab

/-- The explicit analytic main term beyond cutoff a for the signed Gamma
Euler variation. It sums b sigma squared a to the one minus sigma divided
by sigma minus one over the actual real resolvent nodes. Positive cutoffs
permit the main integral identity used in the numerical scalar certificate. -/
noncomputable def gammaEulerTailMain (a : ℝ) : ℝ :=
  (gammaRealPowerList.map (fun ab ↦ ab.2 * (ab.1 ^ 2 * a ^ (1 - ab.1) / (ab.1 - 1)))).sum

/-- The RH error integral for the common signed Gamma Euler variation
beyond cutoff a. Its integrand is the actual logarithmic Mangoldt error
A(t)-t times the combined variation density. It retains coefficient signs
until the subsequent quantitative absolute-error estimate. -/
noncomputable def gammaEulerTailError (a : ℝ) : ℝ :=
  ∫ t in Set.Ioi a,
    (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) * gammaEulerVariation t

/-- Under RH and cutoff at least one, the actual logarithmic Mangoldt sum
times the signed Gamma variation is integrable. Apply the common real
node-list convergence theorem with the certified exponents. -/
theorem integrableOn_gammaEulerVariation_logWeighted (hRH : RiemannHypothesis) {a : ℝ}
    (ha : 1 ≤ a) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * gammaEulerVariation t)
      (Set.Ioi a) := by
  have h :=
    integrableOn_powerList_density hRH gammaRealPowerList gammaRealPowerList_exponents_gt_one ha
  simpa only [gammaRealPowerList, gammaEulerVariation, List.map_map, Function.comp_def] using h

/-- Beyond a positive cutoff, the actual linear Gamma variation density
is integrable. The converted node-list exponents all exceed one. -/
theorem integrableOn_gammaEulerVariation_linear {a : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ t * gammaEulerVariation t) (Set.Ioi a) := by
  have h :=
    integrableOn_powerList_linear_density gammaRealPowerList gammaRealPowerList_exponents_gt_one ha
  simpa only [gammaRealPowerList, gammaEulerVariation, List.map_map, Function.comp_def] using h

/-- The actual signed linear Gamma variation integral equals its explicit
finite main term beyond a positive cutoff. Specialize the node-list formula. -/
theorem integral_gammaEulerVariation_linear_eq_main {a : ℝ} (ha : 0 < a) :
    (∫ t in Set.Ioi a, t * gammaEulerVariation t) = gammaEulerTailMain a := by
  have h :=
    powerList_linear_density_integral_eq gammaRealPowerList gammaRealPowerList_exponents_gt_one ha
  simpa only [gammaRealPowerList, gammaEulerVariation, gammaEulerTailMain, List.map_map,
    Function.comp_def] using h

/-- Under RH and cutoff at least one, the error integral equals the full
logarithmic integral minus the explicit main term. Both integrands are
proved integrable, so subtraction under the integral is justified. -/
theorem gammaEulerTailError_eq_integral_sub_main (hRH : RiemannHypothesis) {a : ℝ} (ha : 1 ≤ a) :
    gammaEulerTailError a =
      (∫ t in Set.Ioi a,
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * gammaEulerVariation t) -
        gammaEulerTailMain a := by
  simp only [gammaEulerTailError, sub_mul]
  rw [MeasureTheory.integral_sub (integrableOn_gammaEulerVariation_logWeighted hRH ha)
      (integrableOn_gammaEulerVariation_linear (zero_lt_one.trans_le ha)),
    integral_gammaEulerVariation_linear_eq_main (zero_lt_one.trans_le ha)]

/-- Under RH and cutoff at least one, the actual Euler mass equals its
finite prefix, exact lower boundary terms, explicit main term and one
signed error integral. This discharges the analytic mass identity before
finite numerical and quantitative error certification. -/
theorem gammaEulerMass_eq_prefix_boundary_main_error (hRH : RiemannHypothesis) {a : ℝ}
    (ha : 1 ≤ a) :
    (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) =
      (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m) -
          Analysis.gammaResolventEulerWeight a * Chebyshev.psi a +
        (a * deriv Analysis.gammaResolventEulerWeight a) *
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a +
        gammaEulerTailMain a +
        gammaEulerTailError a := by
  have h := gammaEulerMass_eq_prefix_boundary_integral hRH ha
  rw [gammaEulerTailError_eq_integral_sub_main hRH ha]
  linarith only [h]

end PseudoPrime.LLS
