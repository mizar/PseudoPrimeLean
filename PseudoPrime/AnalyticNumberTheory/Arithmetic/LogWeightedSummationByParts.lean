/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampLogKernel
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences

/-! # Double partial summation for the exponential ramp Mangoldt sum -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For positive scale x and u>=0, the clipped logarithmic atom at n/x is
log(xu/n) exactly when n is at most floor(xu), and zero otherwise. Compare the
real cutoff with its natural floor and cancel the scaling denominator.
This aligns continuous atoms with the project's finite arithmetic convention. -/
private theorem positiveLogRatio_nat {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) {n : ℕ} :
    Analysis.positiveLogRatio ((n : ℝ) / x) u =
      if n ≤ ⌊x * u⌋₊ then Real.log (x * u / n) else 0 := by
  have hxu : 0 ≤ x * u := mul_nonneg hx.le hu
  by_cases h : n ≤ ⌊x * u⌋₊
  · have hreal := (Nat.le_floor_iff hxu).mp h
    have hdiv : (n : ℝ) / x ≤ u := (div_le_iff₀ hx).mpr (by linarith only [hreal])
    rw [ite_eq_left h, Analysis.positiveLogRatio_eq_log hdiv, div_div_eq_mul_div]
    congr 2
    ring
  · have hreal : x * u ≤ (n : ℝ) := (le_of_not_ge (fun hb ↦ h ((Nat.le_floor_iff hxu).mpr hb)))
    have hdiv : u ≤ (n : ℝ) / x := (le_div_iff₀ hx).mpr (by linarith only [hreal])
    rw [ite_eq_right h, Analysis.positiveLogRatio_zero hdiv]

/-- For positive x and 0<=u<=y, express the logarithmically weighted sum at xu
as a finite combination of clipped logarithms on the common index set through floor(xy).
Pad with zero terms and apply the scaled atom identity.
This gives a fixed finite sum for interchanging summation and integration. -/
theorem logWeightedMangoldtSum_eq_clipped_scaled {x y u : ℝ} (hx : 0 < x) (hu : 0 ≤ u)
    (huy : u ≤ y) :
    logWeightedMangoldtSum (x * u) =
      ∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
        ArithmeticFunction.vonMangoldt n * Analysis.positiveLogRatio ((n : ℝ) / x) u := by
  rw [logWeightedMangoldtSum_eq_extended (mul_le_mul_of_nonneg_left huy hx.le)]
  apply Finset.sum_congr rfl
  intro n _
  rw [positiveLogRatio_nat hx hu, logWeightedMangoldtTerm]
  by_cases h : n ≤ ⌊x * u⌋₊
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h, mul_zero]

/-- The double-partial-summation functional of an arithmetic function A.
It consists of two smooth density integrals, the negative left jump, and the
positive right jump. The exact signed terms match the ramp derivative changes.
Applied to A(xu), it reconstructs the lower finite Mangoldt sum. -/
noncomputable def exponentialRampVariationFunctional (A : ℝ → ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..(247 / 100), A u * ((u - 1) * Real.exp (-u))) +
        (∫ u in (247 / 100 : ℝ)..(99 / 40),
          A u *
            (Real.exp (-u) * ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200)))) -
      A (247 / 100) * ((247 / 100) * Real.exp (-(247 / 100 : ℝ)) / (1 / 200)) +
    A (99 / 40) * ((99 / 40) * Real.exp (-(99 / 40 : ℝ)) / (1 / 200))

/-- A finite sum of continuous functions can be interchanged with the interval
integral against a continuous density. Establish integrability for each product.
This is the justified finite interchange in the ramp formula. -/
private theorem integral_finset_sum_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) {Q : ℝ → ℝ} (hQ : Continuous Q) (a b : ℝ) :
    (∫ u in a..b, (∑ i ∈ s, f i u) * Q u) = ∑ i ∈ s, ∫ u in a..b, f i u * Q u := by
  simp only [Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum (fun i hi ↦ ((hf i hi).mul hQ).intervalIntegrable a b)

/-- The ramp variation functional commutes with a real constant multiplier.
Move the constant outside both integrals and distribute the endpoint terms.
This transports the individual atom identities to Mangoldt coefficients. -/
private theorem rampFunctional_const_mul (c : ℝ) (A : ℝ → ℝ) :
    exponentialRampVariationFunctional (fun u ↦ c * A u) =
      c * exponentialRampVariationFunctional A := by
  simp only [exponentialRampVariationFunctional, mul_assoc, intervalIntegral.integral_const_mul]
  ring

/-- The ramp variation functional is additive over a finite family of continuous
functions. Interchange each finite sum and integral using product integrability,
and distribute the two jumps. This preserves every endpoint contribution. -/
private theorem rampFunctional_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    exponentialRampVariationFunctional (fun u ↦ ∑ i ∈ s, f i u) =
      ∑ i ∈ s, exponentialRampVariationFunctional (f i) := by
  rw [exponentialRampVariationFunctional,
    integral_finset_sum_mul s f hf (Q := fun u : ℝ ↦ (u - 1) * Real.exp (-u))
      ((continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)),
    integral_finset_sum_mul s f hf (Q := fun u : ℝ ↦
      Real.exp (-u) * ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200)))
      ((Real.continuous_exp.comp continuous_id.neg).mul
        (((continuous_id.sub continuous_const).mul
              ((continuous_const.sub continuous_id).div_const (1 / 200))).add
          ((continuous_const.mul continuous_id).sub continuous_const |>.div_const (1 / 200))))]
  simp only [exponentialRampVariationFunctional, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_mul]

/-- A finite weighted sum at positive atom locations equals the variation
functional of the corresponding clipped logarithmic sum. Use the actual atom
reconstruction and finite linearity. No abstract summation-by-parts premise remains. -/
theorem finite_sum_ramp_eq_logVariation {ι : Type*} (s : Finset ι) (c v : ι → ℝ)
    (hv : ∀ i ∈ s, 0 < v i) :
    (∑ i ∈ s, c i * Analysis.exponentialRampWeight (v i)) =
      exponentialRampVariationFunctional
        (fun u ↦ ∑ i ∈ s, c i * Analysis.positiveLogRatio (v i) u) := by
  rw [rampFunctional_finset_sum s (fun i u ↦ c i * Analysis.positiveLogRatio (v i) u)
      (fun i hi ↦ continuous_const.mul (Analysis.positiveLogRatio_continuous (hv i hi)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [rampFunctional_const_mul]
  exact congrArg (fun z : ℝ ↦ c i * z) (Analysis.exponentialRampLogKernel_eq_weight (hv i hi)).symm

/-- Functions agreeing on [0,99/40] have equal density integrals on every
subinterval of that cutoff. Apply pointwise interval-integral congruence.
This permits replacing the finite clipped sum by the actual arithmetic sum. -/
private theorem integral_mul_congr_on_cutoff {f g Q : ℝ → ℝ} {a b : ℝ}
    (h : Set.EqOn f g (Set.Icc 0 (99 / 40))) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 99 / 40) :
    (∫ u in a..b, f u * Q u) = ∫ u in a..b, g u * Q u := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hab] at hu
  exact congrArg (fun z : ℝ ↦ z * Q u) (h ⟨ha.trans hu.1, hu.2.trans hb⟩)

/-- The ramp variation functional depends only on values in [0,99/40].
Use integral congruence on both pieces and equality at both jumps.
This transports arithmetic identities on the supported interval. -/
theorem exponentialRampVariationFunctional_congr {f g : ℝ → ℝ}
    (h : Set.EqOn f g (Set.Icc 0 (99 / 40))) :
    exponentialRampVariationFunctional f = exponentialRampVariationFunctional g := by
  have hleft :=
    integral_mul_congr_on_cutoff (Q := fun u : ℝ ↦ (u - 1) * Real.exp (-u)) h le_rfl
      (by norm_num only : (0 : ℝ) ≤ 247 / 100) (by norm_num only)
  have hright :=
    integral_mul_congr_on_cutoff (Q := fun u : ℝ ↦
      Real.exp (-u) * ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200))) h
      (by norm_num only : (0 : ℝ) ≤ 247 / 100) (by norm_num only) le_rfl
  have ha : f (247 / 100) = g (247 / 100) := h ⟨by norm_num only, by norm_num only⟩
  have hb : f (99 / 40) = g (99 / 40) := h ⟨by norm_num only, le_rfl⟩
  rw [exponentialRampVariationFunctional, exponentialRampVariationFunctional, hleft, hright, ha, hb]

/-- The unnormalized finite lower Mangoldt sum with the actual ramp weight
at n/x and cutoff floor((99/40)x). Positive x gives the lower arithmetic sum
in the coefficient-0.8 no-witness comparison. -/
noncomputable def exponentialRampMangoldtSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x * (99 / 40)⌋₊,
    ArithmeticFunction.vonMangoldt n * Analysis.exponentialRampWeight ((n : ℝ) / x)

/-- For x>0, the actual finite ramp sum equals the variation functional of
A(xu), where A is the logarithmically weighted Mangoldt sum. Reconstruct each
positive atom, interchange the finite sum and integrals with proved integrability,
and use the common cutoff representation. Both derivative jumps are included. -/
theorem exponentialRampMangoldtSum_eq_logWeighted_variation {x : ℝ} (hx : 0 < x) :
    exponentialRampMangoldtSum x =
      exponentialRampVariationFunctional (fun u ↦ logWeightedMangoldtSum (x * u)) := by
  have he :=
    finite_sum_ramp_eq_logVariation (Finset.Ioc 0 ⌊x * (99 / 40)⌋₊)
      (fun n ↦ ArithmeticFunction.vonMangoldt n) (fun n ↦ (n : ℝ) / x)
      (fun n hn ↦ div_pos (Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1) hx)
  apply he.trans
  apply exponentialRampVariationFunctional_congr
  intro u hu
  exact (logWeightedMangoldtSum_eq_clipped_scaled hx hu.1 hu.2).symm

/-- The ramp variation functional evaluated on u equals the actual ramp mass.
Integrate the linear variation primitive on each smooth piece and cancel both
endpoint jumps. This separates the exact smoothed main term from the arithmetic error. -/
theorem exponentialRampVariationFunctional_id :
    exponentialRampVariationFunctional (fun u ↦ u) =
      ∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u := by
  have hfirst :=
    Analysis.linear_variation_integral (Q := fun u : ℝ ↦ (u - 1) * Real.exp (-u))
      (fun u _ ↦ Analysis.exponentialRamp_first_derivative u)
      (fun u _ ↦ Analysis.exponentialRamp_first_variation u)
      ((show Continuous (fun u : ℝ ↦ u * ((u - 1) * Real.exp (-u))) from
            continuous_id.mul
              ((continuous_id.sub continuous_const).mul
                (Real.continuous_exp.comp continuous_id.neg))).intervalIntegrable
        (0 : ℝ) (247 / 100))
      ((Real.continuous_exp.comp continuous_id.neg).intervalIntegrable (0 : ℝ) (247 / 100))
  have hsecond :=
    Analysis.linear_variation_integral (Q := fun u : ℝ ↦
      Real.exp (-u) * ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200)))
      (fun u _ ↦ Analysis.exponentialRamp_middle_derivative u)
      (fun u _ ↦ Analysis.exponentialRamp_middle_variation u)
      ((show
            Continuous
              (fun u : ℝ ↦
                u *
                  (Real.exp (-u) *
                    ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200))))
            from
            continuous_id.mul
              ((Real.continuous_exp.comp continuous_id.neg).mul
                (((continuous_id.sub continuous_const).mul
                      ((continuous_const.sub continuous_id).div_const (1 / 200))).add
                  ((continuous_const.mul continuous_id).sub continuous_const |>.div_const
                    (1 / 200))))).intervalIntegrable
        (247 / 100 : ℝ) (99 / 40))
      ((show Continuous (fun u : ℝ ↦ Real.exp (-u) * (99 / 40 - u) / (1 / 200)) from
            ((Real.continuous_exp.comp continuous_id.neg).mul
                  (continuous_const.sub continuous_id)).div_const
              (1 / 200)).intervalIntegrable
        (247 / 100 : ℝ) (99 / 40))
  rw [exponentialRampVariationFunctional, hfirst, hsecond,
    Analysis.exponentialRampWeight_integral_eq_branch_sum]
  ring

/-- For continuous f,g,Q, the integral of (f-g)Q is the difference of the two
product integrals. Supply both integrability proofs before splitting.
This is the subtraction step in the arithmetic main/error decomposition. -/
private theorem integral_sub_mul_eq (f g Q : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hQ : Continuous Q) (a b : ℝ) :
    (∫ u in a..b, (f u - g u) * Q u) = (∫ u in a..b, f u * Q u) - ∫ u in a..b, g u * Q u := by
  simp only [sub_mul]
  exact
    intervalIntegral.integral_sub (f := fun u ↦ f u * Q u) (g := fun u ↦ g u * Q u)
      ((hf.mul hQ).intervalIntegrable a b) ((hg.mul hQ).intervalIntegrable a b)

/-- For continuous f and g, the variation functional of f-g is the difference
of their functionals. Split the two integrable density products and collect the
signed endpoint terms. This supplies linear main-term separation. -/
private theorem rampFunctional_sub (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    exponentialRampVariationFunctional (fun u ↦ f u - g u) =
      exponentialRampVariationFunctional f - exponentialRampVariationFunctional g := by
  have hQ1 : Continuous (fun u : ℝ ↦ (u - 1) * Real.exp (-u)) :=
    (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have hQ2 :
    Continuous
      (fun u : ℝ ↦
        Real.exp (-u) * ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200))) :=
    (Real.continuous_exp.comp continuous_id.neg).mul
      (((continuous_id.sub continuous_const).mul
            ((continuous_const.sub continuous_id).div_const (1 / 200))).add
        ((continuous_const.mul continuous_id).sub continuous_const |>.div_const (1 / 200)))
  simp only [exponentialRampVariationFunctional]
  rw [integral_sub_mul_eq f g _ hf hg hQ1, integral_sub_mul_eq f g _ hf hg hQ2]
  ring

/-- For x>0, the finite ramp sum is x times the actual ramp mass plus the
variation functional of A(xu)-xu. Use a continuous finite clipped representation
on the supported interval and the evaluated linear functional.
This reduces the lower-sum error estimate to the sharp logarithmically weighted error. -/
theorem exponentialRampMangoldtSum_eq_main_add_error {x : ℝ} (hx : 0 < x) :
    exponentialRampMangoldtSum x =
      x * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) +
        exponentialRampVariationFunctional (fun u ↦ logWeightedMangoldtSum (x * u) - x * u) := by
  let F : ℝ → ℝ := fun u ↦
    ∑ n ∈ Finset.Ioc 0 ⌊x * (99 / 40)⌋₊,
      ArithmeticFunction.vonMangoldt n * Analysis.positiveLogRatio ((n : ℝ) / x) u
  have hF : Continuous F :=
    continuous_finsetSum _
      (fun n hn ↦
        continuous_const.mul
          (Analysis.positiveLogRatio_continuous
            (div_pos (Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1) hx)))
  have heq : Set.EqOn F (fun u ↦ logWeightedMangoldtSum (x * u)) (Set.Icc 0 (99 / 40)) := fun u hu ↦
    (logWeightedMangoldtSum_eq_clipped_scaled hx hu.1 hu.2).symm
  have hlinear :
    exponentialRampVariationFunctional (fun u ↦ x * u) =
      x * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) := by
    rw [rampFunctional_const_mul, exponentialRampVariationFunctional_id]
  have he :=
    exponentialRampVariationFunctional_congr
      (show
        Set.EqOn (fun u ↦ F u - x * u) (fun u ↦ logWeightedMangoldtSum (x * u) - x * u)
          (Set.Icc 0 (99 / 40))
        from fun u hu ↦ congrArg (fun z : ℝ ↦ z - x * u) (heq hu))
  rw [rampFunctional_sub F (fun u ↦ x * u) hF (continuous_const.mul continuous_id), hlinear] at he
  rw [exponentialRampMangoldtSum_eq_logWeighted_variation hx]
  linarith only [he, exponentialRampVariationFunctional_congr heq]

/-- For x>0, divide the exact ramp sum identity by sqrt(x). The main term is
the actual ramp mass times sqrt(x), and the normalized error is the variation
functional of A(xu)-xu divided by sqrt(x). Cancel x/sqrt(x) using sqrt(x)^2=x.
This is the finite double-partial-summation identity in the required normalization. -/
theorem exponentialRampMangoldtSum_normalized_eq_main_add_error {x : ℝ} (hx : 0 < x) :
    exponentialRampMangoldtSum x / Real.sqrt x =
      (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x +
        exponentialRampVariationFunctional (fun u ↦ logWeightedMangoldtSum (x * u) - x * u) /
          Real.sqrt x := by
  have he :=
    congrArg (fun z : ℝ ↦ z / Real.sqrt x) (exponentialRampMangoldtSum_eq_main_add_error hx)
  rw [add_div] at he
  have hc :
    x * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) / Real.sqrt x =
      (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x := by
    apply (div_eq_iff (Real.sqrt_pos.mpr hx).ne').mpr
    rw [mul_assoc, ← pow_two, Real.sq_sqrt hx.le, mul_comm]
  exact
    he.trans
      (congrArg
        (fun z : ℝ ↦
          z +
            exponentialRampVariationFunctional (fun u ↦ logWeightedMangoldtSum (x * u) - x * u) /
              Real.sqrt x)
        hc)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
