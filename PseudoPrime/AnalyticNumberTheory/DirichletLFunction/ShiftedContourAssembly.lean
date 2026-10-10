/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedContourLimits
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveScaledOrdinaryBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogLeftVertical

/-!
# Left-edge decay and assembly of shifted logarithmic Dirichlet contours.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For x>0, sigma>=0, and a<0, the shifted kernel at a-sigma+it is bounded in norm
by x^(-sigma) times the ordinary logarithmic kernel at a+it. Both evaluate L'/L at
the same point; the shifted denominator is larger. No zero hypothesis is required.
This transfers existing left-edge envelopes to real shifts. -/
theorem norm_shiftedLogContourKernel_left_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x σ a t : ℝ} (hx : 0 < x) (hσ : 0 ≤ σ) (ha : a < 0) :
    ‖shiftedLogContourKernel χ x σ (((a - σ : ℝ) : ℂ) + t * Complex.I)‖ ≤
      x ^ (-σ) * ‖dirichletLogContourKernel x χ ((a : ℂ) + t * Complex.I)‖ := by
  have hshift : (σ : ℂ) + (((a - σ : ℝ) : ℂ) + t * Complex.I) = (a : ℂ) + t * Complex.I := by
    rw [Complex.ofReal_sub]; ring
  have hnorm (b : ℝ) : ‖(b : ℂ) + t * Complex.I‖ ^ 2 = b ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, ← pow_two, ← pow_two]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self, add_zero, zero_add]
  have hden : ‖(a : ℂ) + t * Complex.I‖ ^ 2 ≤ ‖((a - σ : ℝ) : ℂ) + t * Complex.I‖ ^ 2 := by
    rw [hnorm a, hnorm (a - σ)]
    nlinarith only [hσ, ha.le, mul_nonneg hσ (neg_nonneg.mpr ha.le), sq_nonneg σ]
  have hapos : 0 < ‖(a : ℂ) + t * Complex.I‖ ^ 2 := by
    rw [hnorm a]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha.ne) (sq_nonneg t)
  have hre (b : ℝ) : ((b : ℂ) + t * Complex.I).re = b := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero]
  unfold shiftedLogContourKernel dirichletLogContourKernel
  rw [hshift]
  simp only [norm_div, norm_mul, norm_neg, norm_pow]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre (a - σ),
    hre a]
  have hnum :
    0 ≤
      (‖deriv χ.LFunction ((a : ℂ) + t * Complex.I)‖ / ‖χ.LFunction ((a : ℂ) + t * Complex.I)‖) *
        x ^ (a - σ) :=
    mul_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.rpow_nonneg hx.le _)
  calc
    _ ≤
        (‖deriv χ.LFunction ((a : ℂ) + t * Complex.I)‖ / ‖χ.LFunction ((a : ℂ) + t * Complex.I)‖) *
            x ^ (a - σ) /
          ‖(a : ℂ) + t * Complex.I‖ ^ 2 :=
      div_le_div_of_nonneg_left hnum hapos hden
    _ = _ := by
      rw [Real.rpow_sub hx, Real.rpow_neg hx.le]; ring

/-- For a nonnegative shift and A>=2, assume a nonnegative logarithmic-derivative
logarithmic envelope on Re z=-A-1/2. The shifted left integral is bounded by x^(-sigma)
times its existing integrable envelope mass. Integrate the transferred pointwise bound.
This provides quantitative control for the expanding-left-edge limit. -/
theorem norm_integral_shiftedLogContourKernel_left_of_bound {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x σ : ℝ} (hx : 0 < x) (hσ : 0 ≤ σ) {A : ℕ} (hA : 2 ≤ A) {D : ℝ}
    (hDnn : 0 ≤ D)
    (hLbound :
      ∀ t : ℝ,
        ‖logDeriv χ.LFunction (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
          D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2))) :
    ‖∫ t : ℝ, shiftedLogContourKernel χ x σ (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) + t * Complex.I)‖ ≤
      x ^ (-σ) *
        (D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1) *
          General.logQuadraticEnvelopeMass) := by
  have hapos : -(A : ℝ) - 1 / 2 < 0 := by linarith only [(Nat.cast_nonneg A : (0 : ℝ) ≤ (A : ℝ))]
  have hxnn := Real.rpow_nonneg hx.le (-σ)
  have hg :=
    (General.integrable_logQuadraticEnvelope.const_mul
          (D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1))).const_mul
      (x ^ (-σ))
  have hi :=
    MeasureTheory.norm_integral_le_of_norm_le hg
      (Filter.Eventually.of_forall fun t ↦
        (norm_shiftedLogContourKernel_left_le χ hx hσ hapos).trans
          (mul_le_mul_of_nonneg_left
            (norm_dirichletLogContourKernel_leftVertical_envelope_le hx hA hDnn hLbound t) hxnn))
  simpa only [MeasureTheory.integral_const_mul, General.logQuadraticEnvelopeMass] using hi

/-- For a primitive nonprincipal character with nonprincipal inverse, x>0, sigma>=0,
and A>=2, the shifted left-line kernel is continuous. The translated L-function argument
stays on Re z=-A-1/2, where functional-equation nonvanishing holds; the Mellin denominator
is nonzero. This supplies measurability without an RH hypothesis. -/
theorem continuous_shiftedLogContourKernel_left {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x σ : ℝ} (hx : 0 < x) (hσ : 0 ≤ σ) {A : ℕ}
    (hA : 2 ≤ A) :
    Continuous
      (fun t : ℝ ↦
        shiftedLogContourKernel χ x σ (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) + t * Complex.I)) := by
  have hline (b : ℝ) : Continuous (fun t : ℝ ↦ (b : ℂ) + t * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hF := χ.differentiable_LFunction hne
  have hc :=
    ((hF.deriv.continuous.comp (hline (-(A : ℝ) - 1 / 2))).neg).div
      (hF.continuous.comp (hline (-(A : ℝ) - 1 / 2)))
      (dirichletLFunction_ne_zero_leftVertical hp hne hinv A hA)
  have hs0 : ∀ t : ℝ, (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) + t * Complex.I) ^ 2 ≠ 0 := by
    intro t
    apply pow_ne_zero 2
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hr
    linarith only [hr, hσ, (Nat.cast_nonneg A : (0 : ℝ) ≤ (A : ℝ))]
  have hk :=
    (hc.mul
          ((hline (-(A : ℝ) - 1 / 2 - σ)).const_cpow
            (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')))).div
      ((hline (-(A : ℝ) - 1 / 2 - σ)).pow 2) hs0
  have hshift :
    ∀ t : ℝ,
      (σ : ℂ) + (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) + t * Complex.I) =
        ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + t * Complex.I := by
    intro t
    rw [Complex.ofReal_sub]
    ring
  change
    Continuous
      (fun t : ℝ ↦
        (-deriv χ.LFunction (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + t * Complex.I) /
              χ.LFunction (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + t * Complex.I)) *
            (x : ℂ) ^ (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) + t * Complex.I) /
          ((((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) + t * Complex.I) ^ 2)) at hk
  simpa only [shiftedLogContourKernel, hshift] using hk

/-- Under the preceding primitive-character assumptions, the shifted left kernel is
integrable. Its norm is dominated by x^(-sigma) times the integrable ordinary kernel norm,
and its proved continuity gives measurability. Thus left integrability is not an extra
premise of shifted rectangle assembly. -/
theorem integrable_shiftedLogContourKernel_left {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x σ : ℝ} (hx : 0 < x) (hσ : 0 ≤ σ) {A : ℕ}
    (hA : 2 ≤ A) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        shiftedLogContourKernel χ x σ (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) + t * Complex.I)) := by
  have hi :=
    (integrable_dirichletLogContourKernel_leftVertical hp hne hinv hx hA).norm.const_mul (x ^ (-σ))
  apply hi.mono' (continuous_shiftedLogContourKernel_left hp hne hinv hx hσ hA).aestronglyMeasurable
  filter_upwards with t
  exact
    norm_shiftedLogContourKernel_left_le χ hx hσ
      (by linarith only [(Nat.cast_nonneg A : (0 : ℝ) ≤ (A : ℝ))])

/-- For a primitive nonprincipal character with nonprincipal inverse, x>1 and sigma>=0,
the shifted whole-line left integral tends to zero as A tends to infinity. Combine the
uniform functional-equation logarithmic envelope with geometric decay against a quadratic
polynomial. No RH hypothesis is required; this removes the remaining left integral. -/
theorem tendsto_shiftedLogContourKernel_left_integral {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x σ : ℝ}
    (hx : 1 < x) (hσ : 0 ≤ σ) :
    Filter.Tendsto
      (fun A : ℕ ↦
        ∫ t : ℝ, shiftedLogContourKernel χ x σ (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) + t * Complex.I))
      Filter.atTop (nhds 0) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  obtain ⟨D, hDnn, hD⟩ :=
    exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le_general hp hne hinv
  let r : ℝ := x⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr hxpos.le
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hx
  let K : ℝ := x ^ (-σ) * D * x ^ (-(1 : ℝ) / 2) * General.logQuadraticEnvelopeMass * 26
  have hpoly : ∀ A : ℕ, ((A : ℝ) + 5) ^ 2 + 1 ≤ 26 * ((A : ℝ) + 1) ^ 2 := by
    intro A
    nlinarith only [(Nat.cast_nonneg A : (0 : ℝ) ≤ (A : ℝ)), sq_nonneg (A : ℝ)]
  have hpow : ∀ A : ℕ, x ^ (-(A : ℝ) - 1 / 2) = x ^ (-(1 : ℝ) / 2) * r ^ A := by
    intro A
    rw [show -(A : ℝ) - 1 / 2 = -(1 : ℝ) / 2 + -(A : ℝ) by ring, Real.rpow_add hxpos,
      Real.rpow_neg hxpos.le, Real.rpow_natCast, ← inv_pow]
  have hbound :
    ∀ A : ℕ,
      2 ≤ A →
        ‖∫ t : ℝ,
              shiftedLogContourKernel χ x σ (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) + t * Complex.I)‖ ≤
          K * (((A : ℝ) + 1) ^ 2 * r ^ A) := by
    intro A hA
    have hi := norm_integral_shiftedLogContourKernel_left_of_bound hxpos hσ hA hDnn (hD A hA)
    rw [hpow A] at hi
    calc
      _ ≤
          x ^ (-σ) *
            (D * (x ^ (-(1 : ℝ) / 2) * r ^ A) * (((A : ℝ) + 5) ^ 2 + 1) *
              General.logQuadraticEnvelopeMass) :=
        hi
      _ ≤
          x ^ (-σ) *
            (D * (x ^ (-(1 : ℝ) / 2) * r ^ A) * (26 * ((A : ℝ) + 1) ^ 2) *
              General.logQuadraticEnvelopeMass) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hpoly A)
              (mul_nonneg hDnn (mul_nonneg (Real.rpow_nonneg hxpos.le _) (pow_nonneg hr0 A))))
            General.logQuadraticEnvelopeMass_nonneg)
          (Real.rpow_nonneg hxpos.le _)
      _ = K * (((A : ℝ) + 1) ^ 2 * r ^ A) := by
        dsimp only [K]; ring
  apply squeeze_zero_norm'
  · filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact hbound A hA
  · have ht := (General.tendsto_add_one_pow_mul_pow_of_lt_one 2 hr0 hr1).const_mul K
    simpa only [mul_zero] using ht

/-- For primitive nonprincipal data, x>=1, sigma>=1, tau>0 and A>=2, assume nonzero heights
tending to infinity and vanishing logarithmic-derivative envelopes on both horizontal edges.
The normalized shifted boundary tends to the arithmetic logarithmic sum minus the left
integral. The general horizontal limit, proved vertical integrability, and Mellin inversion
remove all edge-integrability premises. Selecting heights and proving the envelopes remain
explicit analytic inputs, rather than a full-GRH assumption. -/
theorem tendsto_normalized_shiftedLogBoundary_of_envelopes {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x σ τ : ℝ}
    (hx : 1 ≤ x) (hσ : 1 ≤ σ) (hτ : 0 < τ) {A : ℕ} (hA : 2 ≤ A) (T ηp ηm : ℕ → ℝ)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) (hTne : ∀ k, T k ≠ 0)
    (hηp : Filter.Tendsto ηp Filter.atTop (nhds 0)) (hηm : Filter.Tendsto ηm Filter.atTop (nhds 0))
    (hpbound :
      ∀ k,
        ∀ u ∈ Set.Ioc (-(A : ℝ) - 1 / 2 - σ) τ,
          ‖logDeriv χ.LFunction ((σ : ℂ) + ((u : ℂ) + T k * Complex.I))‖ / (T k) ^ 2 ≤ ηp k)
    (hmbound :
      ∀ k,
        ∀ u ∈ Set.Ioc (-(A : ℝ) - 1 / 2 - σ) τ,
          ‖logDeriv χ.LFunction ((σ : ℂ) + ((u : ℂ) - T k * Complex.I))‖ / (T k) ^ 2 ≤ ηm k) :
    Filter.Tendsto
      (fun k ↦
        (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (shiftedLogContourKernel χ x σ)
            (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) - T k * Complex.I) ((τ : ℂ) + T k * Complex.I))
      Filter.atTop
      (nhds
        (General.logarithmicWeightedSum
            (General.shiftedLSeriesCoefficient
              (fun n ↦ χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)) σ)
            x -
          (2 * Real.pi : ℝ)⁻¹ •
            ∫ t : ℝ,
              shiftedLogContourKernel χ x σ
                (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) + t * Complex.I))) := by
  have hxpos := zero_lt_one.trans_le hx
  have hσ0 := zero_le_one.trans hσ
  have hab : -(A : ℝ) - 1 / 2 - σ ≤ τ := by
    linarith only [hσ, hτ, (Nat.cast_nonneg A : (0 : ℝ) ≤ (A : ℝ))]
  have htop :=
    General.tendsto_integral_shiftedLogarithmicKernel_horizontal (σ : ℂ) hx hab T ηp hTne hηp
      hpbound
  have hbottom :=
    General.tendsto_integral_shiftedLogarithmicKernel_horizontal (σ : ℂ) hx hab (fun k ↦ -T k) ηm
      (fun k ↦ neg_ne_zero.mpr (hTne k)) hηm
      (by simpa only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg, neg_sq] using hmbound)
  apply tendsto_normalized_shiftedLogBoundary χ hxpos hσ hτ T hT
  · simpa only [shiftedLogContourKernel, General.shiftedLogarithmicKernel, logDeriv_apply, neg_div,
      Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] using hbottom
  · simpa only [shiftedLogContourKernel, General.shiftedLogarithmicKernel, logDeriv_apply,
      neg_div] using htop
  · exact integrable_shiftedLogContourKernel_left hp hne hinv hxpos hσ0 hA

/-- Under the individual primitive non-principal character's RH, choose heights tending
to infinity so the normalized shifted rectangle boundary converges to its arithmetic sum
minus the left integral. For x>=1, sigma>=1, tau>0 and A>=2, a fixed strip containing the
rectangle supplies both horizontal envelopes. The already proved edge limits and Mellin
inversion identify the limit; no externally supplied envelope or full GRH is needed. -/
theorem exists_tendsto_normalized_shiftedLogBoundary_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x σ τ : ℝ} (hx : 1 ≤ x) (hσ : 1 ≤ σ) (hτ : 0 < τ) {A : ℕ}
    (hA : 2 ≤ A) :
    ∃ T : ℕ → ℝ,
      Filter.Tendsto T Filter.atTop Filter.atTop ∧
        (∀ k, 1 ≤ T k) ∧
        Filter.Tendsto
          (fun k ↦
            (-Complex.I / (2 * (Real.pi : ℂ))) *
              RectangleGeometry.rectangleBoundaryIntegral (shiftedLogContourKernel χ x σ)
                (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) - T k * Complex.I) ((τ : ℂ) + T k * Complex.I))
          Filter.atTop
          (nhds
            (General.logarithmicWeightedSum
                (General.shiftedLSeriesCoefficient
                  (fun n ↦ χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)) σ)
                x -
              (2 * Real.pi : ℝ)⁻¹ •
                ∫ t : ℝ,
                  shiftedLogContourKernel χ x σ
                    (((-(A : ℝ) - 1 / 2 - σ : ℝ) : ℂ) + t * Complex.I))) := by
  obtain ⟨B, hB⟩ := exists_nat_gt (max (A : ℝ) (σ + τ))
  have hAB : (A : ℝ) ≤ (B : ℝ) := (le_max_left _ _).trans hB.le
  have hright : σ + τ ≤ (B : ℝ) := (le_max_right _ _).trans hB.le
  obtain ⟨T, η, hT, hT1, hη, hb⟩ :=
    exists_fixedStrip_LLogDeriv_envelope_of_dirichletRH hN2 hRH hp hne hinv B
  refine ⟨T, hT, hT1, ?_⟩
  apply
    tendsto_normalized_shiftedLogBoundary_of_envelopes hp hne hinv hx hσ hτ hA T η η hT
      (fun k => ne_of_gt (zero_lt_one.trans_le (hT1 k))) hη hη
  · intro k u hu
    have hlo : -(B : ℝ) - 1 / 2 ≤ σ + u := by linarith only [hu.1, hAB]
    have hhi : σ + u ≤ (B : ℝ) + 3 / 2 := by linarith only [hu.2, hright]
    simpa only [Complex.ofReal_add, add_assoc] using (hb k (σ + u) hlo hhi).1
  · intro k u hu
    have hlo : -(B : ℝ) - 1 / 2 ≤ σ + u := by linarith only [hu.1, hAB]
    have hhi : σ + u ≤ (B : ℝ) + 3 / 2 := by linarith only [hu.2, hright]
    simpa only [Complex.ofReal_add, add_sub_assoc] using (hb k (σ + u) hlo hhi).2

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
