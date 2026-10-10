/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.CenteredResolventInversion
public import PseudoPrime.AnalyticNumberTheory.General.LogarithmicMellinInversion

/-!
# Mellin inversion for reciprocal centered resolvents

Pole-mass bounds justify summing the reciprocal smoothing residues of completed zeros.
The pole -1 coincides with a smoothing pole and is evaluated separately.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The indicator weight (t^(-α) - t)/(α(α+1)) on (0,1].
For a left-half-plane pole other than -1, its Mellin transform is the centered reciprocal
kernel. The totalized definition is used for the individual zero residues. -/
noncomputable def reciprocalResolventWeight (α : ℂ) (t : ℝ) : ℂ :=
  (α * (α + 1))⁻¹ *
    ((Set.Ioc (0 : ℝ) 1).indicator (fun u ↦ (u : ℂ) ^ (-α)) t -
      (Set.Ioc (0 : ℝ) 1).indicator (fun u ↦ (u : ℂ) ^ (1 : ℂ)) t)

/-- For Re α < 0, α ≠ -1 and Re s > 0, the reciprocal resolvent weight has
Mellin transform 1/(α(s+1)(s-α)). Subtract the two power transforms and simplify their
nonzero denominators. This supplies the scalar inversion formula. -/
theorem hasMellin_reciprocalResolventWeight {α s : ℂ} (hα : α.re < 0) (ha : α ≠ -1)
    (hs : 0 < s.re) : HasMellin (reciprocalResolventWeight α) s (1 / (α * (s + 1) * (s - α))) := by
  have hp :=
    hasMellin_cpow_Ioc (-α) (s := s)
      (by
        rw [Complex.neg_re]; linarith only [hα, hs])
  have ht :=
    hasMellin_cpow_Ioc (1 : ℂ) (s := s)
      (by
        rw [Complex.one_re]; linarith only [hs])
  have hh := hasMellin_const_smul (hasMellin_sub hp.1 ht.1).1 ((α * (α + 1))⁻¹)
  rw [(hasMellin_sub hp.1 ht.1).2, hp.2, ht.2] at hh
  have ha0 : α ≠ 0 := fun hz ↦ by
    rw [hz, Complex.zero_re] at hα; exact lt_irrefl _ hα
  have ha1 : α + 1 ≠ 0 := fun hz ↦ ha (eq_neg_of_add_eq_zero_left hz)
  have hs1 : s + 1 ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith only [he, hs]
  have hd : s - α ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.zero_re] at he
    linarith only [he, hs, hα]
  convert hh using 1
  · rfl
  · simp only [smul_eq_mul, ← sub_eq_add_neg]
    field_simp (disch := simp only [ha0, ha1, hs1, hd, ne_eq, not_false_eq_true])
    ring

/-- If Re z is nonnegative, adding one cannot decrease its norm.
Compare the squared norms. This bounds the factor z/(z+1) on positive vertical lines. -/
theorem norm_le_norm_add_one_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) : ‖z‖ ≤ ‖z + 1‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    add_zero]
  nlinarith only [hz]

/-- The centered reciprocal kernel x^z/(α(z+1)(z-α)), with z = τ+i y.
It is defined as the centered logarithmic resolvent times z/(z+1), so absolute-integral
bounds transfer from that kernel. Mellin inversion evaluates its zero residues. -/
noncomputable def reciprocalResolventKernel (α : ℂ) (x τ y : ℝ) : ℂ :=
  centeredResolventKernel α x τ y * (((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I + 1))

/-- For τ > 0, the reciprocal resolvent kernel has norm at most the centered
logarithmic resolvent, for all α,x,y. The factor z/(z+1) has norm at most one.
This transfers the pole-mass majorant to reciprocal smoothing. -/
theorem norm_reciprocalResolventKernel_le (α : ℂ) (x : ℝ) {τ : ℝ} (hτ : 0 < τ) (y : ℝ) :
    ‖reciprocalResolventKernel α x τ y‖ ≤ ‖centeredResolventKernel α x τ y‖ := by
  have he : ((τ : ℂ) + y * Complex.I).re = τ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hp : 0 < ‖(τ : ℂ) + y * Complex.I + 1‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hh := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re, he] at hh
    linarith only [hh, hτ]
  unfold reciprocalResolventKernel
  rw [norm_mul, norm_div]
  exact
    mul_le_of_le_one_right (norm_nonneg _)
      ((div_le_one hp).mpr
        (norm_le_norm_add_one_of_re_nonneg
          (by
            rw [he]; exact hτ.le)))

/-- For Re α < 0 and x,τ > 0, the reciprocal resolvent is vertically integrable.
Multiply the integrable centered logarithmic kernel by the continuous bounded factor
z/(z+1). This permits individual Mellin inversion and termwise integration. -/
theorem integrable_reciprocalResolventKernel {α : ℂ} (hα : α.re < 0) {τ x : ℝ} (hτ : 0 < τ)
    (hx : 0 < x) : MeasureTheory.Integrable (reciprocalResolventKernel α x τ) := by
  have he : ∀ y : ℝ, (τ : ℂ) + y * Complex.I + 1 ≠ 0 := by
    intro y hz
    have hh := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hh
    linarith only [hh, hτ]
  have hc : Continuous (fun y : ℝ ↦ ((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I + 1)) :=
    (continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)).div
      ((continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)).add continuous_const)
      he
  exact
    (integrable_centeredResolventKernel hα hτ hx).mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall
        (fun y ↦ by
          rw [norm_div]
          apply (div_le_one (norm_pos_iff.mpr (he y))).mpr
          apply norm_le_norm_add_one_of_re_nonneg
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
          exact hτ.le))

/-- For Re α < 0 and τ > 0, the reciprocal resolvent equals
x^z/(α(z+1)(z-α)). Nonvanishing vertical denominators justify cancellation of z.
This identifies the kernel with its computed Mellin transform. -/
theorem reciprocalResolventKernel_eq {α : ℂ} (hα : α.re < 0) {τ x : ℝ} (hτ : 0 < τ) (y : ℝ) :
    reciprocalResolventKernel α x τ y =
      (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
        (α * ((τ : ℂ) + y * Complex.I + 1) * ((τ : ℂ) + y * Complex.I - α)) := by
  have hz := ne_zero_add_mul_I_of_re_ne_zero hτ.ne' y
  have ha : α ≠ 0 := fun h ↦ by
    rw [h, Complex.zero_re] at hα; exact lt_irrefl _ hα
  have h1 : (τ : ℂ) + y * Complex.I + 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.one_re,
      Complex.zero_re] at he
    linarith only [he, hτ]
  have hd : (τ : ℂ) + y * Complex.I - α ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at he
    linarith only [he, hτ, hα]
  unfold reciprocalResolventKernel centeredResolventKernel
  field_simp (disch := simp only [hz, ha, h1, hd, ne_eq, not_false_eq_true])

/-- The reciprocal resolvent weight is continuous at every 0 < t < 1.
Both indicators are locally active and their power functions are continuous.
This supplies pointwise Mellin inversion at t = 1/x. -/
theorem continuousAt_reciprocalResolventWeight {α : ℂ} {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ContinuousAt (reciprocalResolventWeight α) t := by
  have he : ∀ᶠ u in nhds t, u ∈ Set.Ioc (0 : ℝ) 1 :=
    Filter.Eventually.mono (isOpen_Ioo.mem_nhds ⟨ht, ht1⟩) (fun _ hu ↦ ⟨hu.1, hu.2.le⟩)
  have hc : ContinuousAt (fun u : ℝ ↦ (α * (α + 1))⁻¹ * ((u : ℂ) ^ (-α) - (u : ℂ) ^ (1 : ℂ))) t :=
    continuousAt_const.mul
      ((Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
            (Complex.ofReal_mem_slitPlane.mpr ht)).sub
        (Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
          (Complex.ofReal_mem_slitPlane.mpr ht)))
  apply hc.congr_of_eventuallyEq
  filter_upwards [he] with u hu
  rw [reciprocalResolventWeight, Set.indicator_of_mem hu, Set.indicator_of_mem hu]

/-- For Re α < 0, α ≠ -1, τ > 0 and 0 < t < 1, Mellin inversion recovers
the reciprocal resolvent weight. Its transform, vertical integrability and continuity
verify all inversion hypotheses. This evaluates an individual centered pole. -/
theorem mellinInv_reciprocalResolventKernel_eq {α : ℂ} (hα : α.re < 0) (ha : α ≠ -1) {τ t : ℝ}
    (hτ : 0 < τ) (ht : 0 < t) (ht1 : t < 1) :
    mellinInv τ (fun s : ℂ ↦ 1 / (α * (s + 1) * (s - α))) t = reciprocalResolventWeight α t := by
  have hp : ∀ y : ℝ, 0 < ((τ : ℂ) + y * Complex.I).re := by
    intro y
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] using hτ
  have he := fun y ↦ (hasMellin_reciprocalResolventWeight hα ha (hp y)).2
  have hi : Complex.VerticalIntegrable (mellin (reciprocalResolventWeight α)) τ := by
    unfold Complex.VerticalIntegrable
    simp only [he]
    have hh := integrable_reciprocalResolventKernel hα hτ (show (0 : ℝ) < 1 from zero_lt_one)
    change MeasureTheory.Integrable (fun y ↦ reciprocalResolventKernel α 1 τ y) at hh
    simpa only [reciprocalResolventKernel_eq hα hτ, Complex.ofReal_one, Complex.one_cpow] using hh
  have hm :=
    mellinInv_mellin_eq τ (reciprocalResolventWeight α) ht
      (hasMellin_reciprocalResolventWeight hα ha (by simpa only [Complex.ofReal_re] using hτ)).1 hi
      (continuousAt_reciprocalResolventWeight ht ht1)
  rw [← hm]
  unfold mellinInv
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [he]

/-- For x > 1, the reciprocal resolvent weight at 1/x is
(x^α - 1/x)/(α(α+1)). Activate the indicators and invert the positive power base.
This converts Mellin inversion into the residue expression. -/
theorem reciprocalResolventWeight_inv {α : ℂ} {x : ℝ} (hx : 1 < x) :
    reciprocalResolventWeight α x⁻¹ = ((x : ℂ) ^ α - (x : ℂ)⁻¹) / (α * (α + 1)) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hi : x⁻¹ ∈ Set.Ioc (0 : ℝ) 1 := ⟨inv_pos.mpr hx0, ((inv_lt_one₀ hx0).mpr hx).le⟩
  rw [reciprocalResolventWeight, Set.indicator_of_mem hi, Set.indicator_of_mem hi, Complex.cpow_one,
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx0.le, Complex.cpow_neg, inv_inv,
    div_eq_mul_inv]
  exact mul_comm _ _

/-- For Re α < 0, α ≠ -1, τ > 0 and x > 1, the normalized vertical integral
of the reciprocal resolvent is (x^α - 1/x)/(α(α+1)). Apply Mellin inversion at 1/x.
This is the scalar contribution summed over completed zeros. -/
theorem integral_reciprocalResolventKernel_eq {α : ℂ} (hα : α.re < 0) (ha : α ≠ -1) {τ x : ℝ}
    (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ, reciprocalResolventKernel α x τ y) =
      ((x : ℂ) ^ α - (x : ℂ)⁻¹) / (α * (α + 1)) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hm :=
    mellinInv_reciprocalResolventKernel_eq hα ha hτ (inv_pos.mpr hx0) ((inv_lt_one₀ hx0).mpr hx)
  rw [reciprocalResolventWeight_inv hx] at hm
  rw [← hm]
  unfold mellinInv
  rw [one_div]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [reciprocalResolventKernel_eq hα hτ, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx0.le,
    Complex.cpow_neg, inv_inv, smul_eq_mul, div_eq_mul_inv, one_div]

/-- For left-half-plane poles with summable inverse-three-halves multiplicity
mass and x,τ > 0, the integrals of weighted reciprocal-kernel norms are summable.
Dominate each integral by the centered logarithmic-kernel integral.
This justifies exchanging the zero series and vertical integral. -/
theorem summable_integral_norm_reciprocalResolventKernel {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (α i).re < 0) {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x)
    (hm : Summable (fun i ↦ (m i : ℝ) / ‖α i‖ ^ (3 / 2 : ℝ))) :
    Summable (fun i ↦ ∫ y : ℝ, ‖(m i : ℂ) * reciprocalResolventKernel (α i) x τ y‖) := by
  apply
    Summable.of_nonneg_of_le (fun _ ↦ MeasureTheory.integral_nonneg (fun _ ↦ norm_nonneg _)) _
      (summable_integral_norm_centeredResolventKernel α m hα hτ hx hm)
  intro i
  apply
    MeasureTheory.integral_mono
      ((integrable_reciprocalResolventKernel (hα i) hτ hx).const_mul (m i : ℂ)).norm
      ((integrable_centeredResolventKernel (hα i) hτ hx).const_mul (m i : ℂ)).norm
  intro y
  change
    ‖(m i : ℂ) * reciprocalResolventKernel (α i) x τ y‖ ≤
      ‖(m i : ℂ) * centeredResolventKernel (α i) x τ y‖
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_reciprocalResolventKernel_le (α i) x hτ y) (norm_nonneg _)

/-- For a countable pole family with summable inverse-three-halves multiplicity
mass and x,τ > 0, vertical integration commutes with the reciprocal-resolvent series.
Absolute integral-norm summability gives the exchange; pull out each multiplicity.
This is the countable form of the completed-zero integration theorem. -/
theorem integral_tsum_reciprocalResolventKernel {ι : Type*} [Countable ι] (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (α i).re < 0) {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x)
    (hm : Summable (fun i ↦ (m i : ℝ) / ‖α i‖ ^ (3 / 2 : ℝ))) :
    (∫ y : ℝ, ∑' i, (m i : ℂ) * reciprocalResolventKernel (α i) x τ y) =
      ∑' i, (m i : ℂ) * (∫ y : ℝ, reciprocalResolventKernel (α i) x τ y) := by
  rw [←
    MeasureTheory.integral_tsum_of_summable_integral_norm
      (fun i ↦ (integrable_reciprocalResolventKernel (hα i) hτ hx).const_mul (m i : ℂ))
      (summable_integral_norm_reciprocalResolventKernel α m hα hτ hx hm)]
  exact tsum_congr (fun i ↦ MeasureTheory.integral_const_mul _ _)

/-- For any pole family with summable inverse-three-halves multiplicity mass
and x,τ > 0, vertical integration commutes with the reciprocal-resolvent series.
Restrict to the countable nonzero-multiplicity support and extend by zero.
No countability assumption on the ambient zero type is required. -/
theorem integral_tsum_reciprocalResolventKernel_of_mass {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (α i).re < 0) {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x)
    (hm : Summable (fun i ↦ (m i : ℝ) / ‖α i‖ ^ (3 / 2 : ℝ))) :
    (∫ y : ℝ, ∑' i, (m i : ℂ) * reciprocalResolventKernel (α i) x τ y) =
      ∑' i, (m i : ℂ) * (∫ y : ℝ, reciprocalResolventKernel (α i) x τ y) := by
  let S : Set ι := {i | m i ≠ 0}
  have hS : S.Countable :=
    hm.countable_support.mono
      (by
        intro i hi
        have ha : 0 < ‖α i‖ :=
          norm_pos_iff.mpr
            (fun hz ↦ by
              have he := hα i
              rw [hz, Complex.zero_re] at he
              exact lt_irrefl _ he)
        exact div_ne_zero (Nat.cast_ne_zero.mpr hi) (Real.rpow_pos_of_pos ha _).ne')
  let : Countable S := hS.to_subtype
  have hs (y : ℝ) :
    (∑' i : S, (m i : ℂ) * reciprocalResolventKernel (α i) x τ y) =
      ∑' i, (m i : ℂ) * reciprocalResolventKernel (α i) x τ y := by
    apply
      tsum_subtype_eq_of_support_subset (s := S) (f := fun i : ι ↦
        (m i : ℂ) * reciprocalResolventKernel (α i) x τ y)
    intro i hi
    by_contra hn
    have hz : m i = 0 := Classical.not_not.mp hn
    exact hi (by simp only [hz, Nat.cast_zero, zero_mul])
  calc
    _ = ∫ y : ℝ, ∑' i : S, (m i : ℂ) * reciprocalResolventKernel (α i) x τ y :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y ↦ (hs y).symm))
    _ = ∑' i : S, (m i : ℂ) * (∫ y : ℝ, reciprocalResolventKernel (α i) x τ y) :=
      integral_tsum_reciprocalResolventKernel (fun i : S ↦ α i) (fun i : S ↦ m i) (fun i ↦ hα i) hτ
        hx (hm.subtype S)
    _ = _ := by
      apply
        tsum_subtype_eq_of_support_subset (s := S) (f := fun i : ι ↦
          (m i : ℂ) * (∫ y : ℝ, reciprocalResolventKernel (α i) x τ y))
      intro i hi
      by_contra hn
      have hz : m i = 0 := Classical.not_not.mp hn
      exact hi (by simp only [hz, Nat.cast_zero, zero_mul])

/-- For left-half-plane poles distinct from -1, summable inverse-three-halves
multiplicity mass, τ > 0 and x > 1, the normalized reciprocal-resolvent integral equals
the multiplicity-weighted series (x^α - 1/x)/(α(α+1)). Exchange and evaluate each integral.
This supplies the completed-zero term of the general reciprocal formula. -/
theorem normalized_integral_tsum_reciprocalResolventKernel {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (α i).re < 0) (ha : ∀ i, α i ≠ -1) {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x)
    (hm : Summable (fun i ↦ (m i : ℝ) / ‖α i‖ ^ (3 / 2 : ℝ))) :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ, ∑' i, (m i : ℂ) * reciprocalResolventKernel (α i) x τ y) =
      ∑' i, (m i : ℂ) * (((x : ℂ) ^ (α i) - (x : ℂ)⁻¹) / (α i * (α i + 1))) := by
  rw [integral_tsum_reciprocalResolventKernel_of_mass α m hα hτ (zero_lt_one.trans hx) hm,
    Complex.real_smul, ← tsum_mul_left]
  apply tsum_congr
  intro i
  have he := integral_reciprocalResolventKernel_eq (hα i) (ha i) hτ hx
  rw [Complex.real_smul] at he
  rw [← mul_assoc, mul_comm _ (m i : ℂ), mul_assoc, he]

/-- For τ > 0 and x > 1, the reciprocal Mellin kernel x^z/(z(z+1)) is
integrable and its normalized integral is 1-1/x. Use the bounded power numerator and
invert the reciprocal smoothing weight. This evaluates the constant endpoint term. -/
theorem reciprocalMellin_integrable_and_integral {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x) :
    MeasureTheory.Integrable
        (fun y : ℝ ↦
          (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1))) ∧
      (2 * Real.pi)⁻¹ •
          (∫ y : ℝ,
            (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
              (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1))) =
        (1 - (x : ℂ)⁻¹) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have h1 : τ ≠ -1 := by linarith only [hτ]
  have hi :
    MeasureTheory.Integrable
      (fun y : ℝ ↦
        (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
          (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1))) := by
    have hc : Continuous (fun y : ℝ ↦ (x : ℂ) ^ ((τ : ℂ) + y * Complex.I)) :=
      continuous_const.cpow (continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I))
        (fun _ ↦ Complex.ofReal_mem_slitPlane.mpr hx0)
    have hh :=
      (verticalIntegrable_mellinReciprocalKernel hτ.ne' h1).bdd_mul hc.aestronglyMeasurable
        (Filter.Eventually.of_forall
          (fun y ↦ by
            rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
            simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
              Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
            exact le_refl (x ^ τ)))
    simpa only [div_eq_mul_inv] using hh
  have hm := mellinInv_mellinWeightOne_eq hτ (inv_pos.mpr hx0)
  have hmem : x⁻¹ ∈ Set.Ioc (0 : ℝ) 1 := ⟨inv_pos.mpr hx0, ((inv_lt_one₀ hx0).mpr hx).le⟩
  rw [mellinWeightOne, Set.indicator_of_mem hmem, Complex.ofReal_inv] at hm
  refine ⟨hi, ?_⟩
  rw [← hm]
  unfold mellinInv
  rw [one_div]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx0.le, Complex.cpow_neg, inv_inv,
    smul_eq_mul, div_eq_mul_inv, one_div]

/-- For left-half-plane poles with summable inverse-three-halves multiplicity mass
and x,τ > 0, the reciprocal-resolvent series is vertically integrable.
Pull the bounded multiplier z/(z+1) outside the already integrable centered series.
This permits splitting the completed logarithmic-derivative integral. -/
theorem integrable_tsum_reciprocalResolventKernel {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (α i).re < 0) {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x)
    (hm : Summable (fun i ↦ (m i : ℝ) / ‖α i‖ ^ (3 / 2 : ℝ))) :
    MeasureTheory.Integrable
      (fun y : ℝ ↦ ∑' i, (m i : ℂ) * reciprocalResolventKernel (α i) x τ y) := by
  have he : ∀ y : ℝ, (τ : ℂ) + y * Complex.I + 1 ≠ 0 := by
    intro y hz
    have hh := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hh
    linarith only [hh, hτ]
  have hc : Continuous (fun y : ℝ ↦ ((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I + 1)) :=
    (continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)).div
      ((continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)).add continuous_const)
      he
  have hi :=
    (integrable_tsum_centeredResolventKernel α m hα hτ hx hm).mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall
        (fun y ↦ by
          rw [norm_div]
          apply (div_le_one (norm_pos_iff.mpr (he y))).mpr
          apply norm_le_norm_add_one_of_re_nonneg
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
          exact hτ.le))
  convert hi using 1
  funext y
  simp only [reciprocalResolventKernel, ← mul_assoc, tsum_mul_right]

/-- For τ > 0 and x > 1, the reciprocal resolvent at the coincident pole -1
has normalized integral -log x/x. Shift the vertical parameter by one and apply
the logarithmic Mellin kernel evaluation. This handles the zero gamma shift that
cannot use the noncoincident residue formula. -/
theorem integral_reciprocalResolventKernel_neg_one {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ, reciprocalResolventKernel (-1) x τ y) =
      -(Real.log x : ℂ) / (x : ℂ) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hs : 0 < τ + 1 := by linarith only [hτ]
  obtain ⟨_, hI⟩ := logarithmicMellin_integrable_and_integral hs hx
  have he :
    reciprocalResolventKernel (-1) x τ =
      (fun y : ℝ ↦
        -(x : ℂ)⁻¹ *
          ((x : ℂ) ^ (((τ + 1 : ℝ) : ℂ) + y * Complex.I) /
            (((τ + 1 : ℝ) : ℂ) + y * Complex.I) ^ 2)) := by
    funext y
    rw [reciprocalResolventKernel_eq (by norm_num only [Complex.neg_re, Complex.one_re]) hτ]
    rw [show ((τ + 1 : ℝ) : ℂ) + y * Complex.I = ((τ : ℂ) + y * Complex.I) + 1 by
        rw [Complex.ofReal_add, Complex.ofReal_one]; ring,
      Complex.cpow_add ((τ : ℂ) + y * Complex.I) 1 (Complex.ofReal_ne_zero.mpr hx0.ne'),
      Complex.cpow_one]
    have hn : (τ : ℂ) + y * Complex.I + 1 ≠ 0 := by
      intro hz
      have hh := congrArg Complex.re hz
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.one_re, Complex.zero_re] at hh
      linarith only [hh, hτ]
    field_simp (disch :=
      simp only [Complex.ofReal_ne_zero.mpr hx0.ne', hn, sub_neg_eq_add, ne_eq, not_false_eq_true])
    ring
  rw [he, MeasureTheory.integral_const_mul, ← mul_smul_comm, hI]
  ring

end PseudoPrime.AnalyticNumberTheory.General
