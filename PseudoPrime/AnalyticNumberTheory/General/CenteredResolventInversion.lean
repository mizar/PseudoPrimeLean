/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.CenteredResolventIntegration
public import PseudoPrime.AnalyticNumberTheory.General.LogarithmicMellinInversion

/-!
# Mellin evaluation of centered pole series

The scalar inversion and power-mass interchange yield the complete centered residue sum.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For a left-half-plane pole, positive τ and x > 1, the normalized centered integral
is (x^α-1)/α². Split its kernel into the regularized resolvent and the logarithmic kernel;
Mellin inversion evaluates both pieces. This gives each completed-zero or gamma residue. -/
theorem integral_centeredResolventKernel_eq {α : ℂ} (hα : α.re < 0) {τ x : ℝ} (hτ : 0 < τ)
    (hx : 1 < x) :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ, centeredResolventKernel α x τ y) = ((x : ℂ) ^ α - 1) / α ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  let a : ℕ → ℂ := fun n ↦ if n = 1 then 1 else 0
  have ha : a 0 = 0 := by simp only [a, ite_eq_right Nat.zero_ne_one]
  have hg := integrable_logarithmicMellinTerm a ha hx0 hτ 1
  change MeasureTheory.Integrable (fun y ↦ logarithmicMellinTerm a x τ 1 y) at hg
  have hig := logarithmicMellinTerm_integral a hx0 hτ Nat.one_ne_zero
  simp only [logarithmicMellinTerm, a, ite_eq_left rfl, Nat.cast_one, Complex.one_cpow,
    one_mul] at hg hig
  have hm : mellinWeightTwo ((1 : ℝ) / x) = (Real.log x : ℂ) := by
    have hi : (1 : ℝ) / x ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨div_pos zero_lt_one hx0, (div_lt_one hx0).mpr hx |>.le⟩
    rw [mellinWeightTwo, Set.indicator_of_mem hi, one_div, Real.log_inv, Complex.ofReal_neg,
      neg_neg]
  rw [hm] at hig
  let H := fun y : ℝ ↦
    (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
      (((τ : ℂ) + y * Complex.I) ^ 2 * ((τ : ℂ) + y * Complex.I - α))
  let G := fun y : ℝ ↦ (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I) ^ 2
  have he : centeredResolventKernel α x τ = fun y ↦ H y + G y / α := by
    funext y
    have hnα : α ≠ 0 := fun h ↦ by
      rw [h, Complex.zero_re] at hα
      exact lt_irrefl _ hα
    have hnz := ne_zero_add_mul_I_of_re_ne_zero hτ.ne' y
    have hnd : (τ : ℂ) + y * Complex.I - α ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero,
        Complex.zero_re] at hh
      linarith only [hh, hτ, hα]
    unfold centeredResolventKernel H G
    field_simp [hnα, hnz, hnd]
    ring
  have hH : MeasureTheory.Integrable H := by
    have hi := (integrable_centeredResolventKernel hα hτ hx0).sub (hg.div_const α)
    rw [he] at hi
    convert hi using 1
    funext y
    dsimp only [Pi.sub_apply, G]
    ring
  rw [he, MeasureTheory.integral_add hH (hg.div_const α), smul_add, MeasureTheory.integral_div, ←
    smul_div_assoc, integral_resolventKernel_eq hα hτ hx]
  rw [← hig]
  have hnα : α ≠ 0 := fun h ↦ by
    rw [h, Complex.zero_re] at hα
    exact lt_irrefl _ hα
  field_simp [hnα]
  ring

/-- For left-half-plane poles, tau > 0, x > 0 and summable inverse-three-halves
multiplicity mass, exchange the centered-resolvent sum and vertical integral.
Restrict to the countable nonzero-multiplicity support, apply the summable integral-norm
majorant and interchange theorem, then extend by zero. No countability assumption
on the whole index type is needed for the completed-zero integral. -/
theorem integral_tsum_centeredResolventKernel_of_mass {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (α i).re < 0) {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x)
    (hm : Summable (fun i ↦ (m i : ℝ) / ‖α i‖ ^ (3 / 2 : ℝ))) :
    (∫ y : ℝ, ∑' i, (m i : ℂ) * centeredResolventKernel (α i) x τ y) =
      ∑' i, (m i : ℂ) * (∫ y : ℝ, centeredResolventKernel (α i) x τ y) := by
  let S : Set ι := {i | m i ≠ 0}
  have hS : S.Countable :=
    hm.countable_support.mono
      (by
        intro i hi
        have ha : 0 < ‖α i‖ :=
          norm_pos_iff.mpr
            (fun h ↦ by
              have he := hα i
              rw [h, Complex.zero_re] at he
              exact lt_irrefl _ he)
        exact div_ne_zero (Nat.cast_ne_zero.mpr hi) (Real.rpow_pos_of_pos ha _).ne')
  let : Countable S := hS.to_subtype
  have hs (y : ℝ) :
    (∑' i : S, (m i : ℂ) * centeredResolventKernel (α i) x τ y) =
      ∑' i, (m i : ℂ) * centeredResolventKernel (α i) x τ y := by
    apply
      tsum_subtype_eq_of_support_subset (s := S) (f := fun i : ι ↦
        (m i : ℂ) * centeredResolventKernel (α i) x τ y)
    intro i hi
    by_contra hn
    have hz : m i = 0 := Classical.not_not.mp hn
    exact hi (by simp only [hz, Nat.cast_zero, zero_mul])
  calc
    _ = ∫ y : ℝ, ∑' i : S, (m i : ℂ) * centeredResolventKernel (α i) x τ y :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y ↦ (hs y).symm))
    _ = ∑' i : S, (m i : ℂ) * (∫ y : ℝ, centeredResolventKernel (α i) x τ y) :=
      integral_tsum_centeredResolventKernel (fun i : S ↦ α i) (fun i : S ↦ m i) (fun i ↦ hα i) hτ hx
        (hm.subtype S)
    _ = _ := by
      apply
        tsum_subtype_eq_of_support_subset (s := S) (f := fun i : ι ↦
          (m i : ℂ) * (∫ y : ℝ, centeredResolventKernel (α i) x τ y))
      intro i hi
      by_contra hn
      have hz : m i = 0 := Classical.not_not.mp hn
      exact hi (by simp only [hz, Nat.cast_zero, zero_mul])

/-- For left-half-plane poles, tau > 0, x > 1 and summable inverse-three-halves
multiplicity mass, the normalized integral of the centered resolvent sum is the
multiplicity-weighted sum of (x^alpha-1)/alpha^2. Exchange the series and integral
and evaluate each pole by Mellin inversion. This gives the completed-zero contribution. -/
theorem normalized_integral_tsum_centeredResolventKernel {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (α i).re < 0) {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x)
    (hm : Summable (fun i ↦ (m i : ℝ) / ‖α i‖ ^ (3 / 2 : ℝ))) :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ, ∑' i, (m i : ℂ) * centeredResolventKernel (α i) x τ y) =
      ∑' i, (m i : ℂ) * (((x : ℂ) ^ (α i) - 1) / (α i) ^ 2) := by
  rw [integral_tsum_centeredResolventKernel_of_mass α m hα hτ (zero_lt_one.trans hx) hm,
    Complex.real_smul, ← tsum_mul_left]
  apply tsum_congr
  intro i
  have h := integral_centeredResolventKernel_eq (hα i) hτ hx
  rw [Complex.real_smul] at h
  rw [← mul_assoc, mul_comm _ (m i : ℂ), mul_assoc, h]

/-- For a left-half-plane pole and a positive vertical line, the centered kernel equals
the reciprocal difference times x^z/z². Nonvanishing denominators justify the algebra.
This matches the kernel with the logarithmic-derivative expansion. -/
theorem centeredResolventKernel_eq_difference {α : ℂ} (hα : α.re < 0) {τ x : ℝ} (hτ : 0 < τ)
    (y : ℝ) :
    centeredResolventKernel α x τ y =
      (1 / ((τ : ℂ) + y * Complex.I - α) + 1 / α) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
        ((τ : ℂ) + y * Complex.I) ^ 2 := by
  have ha : α ≠ 0 := fun h ↦ by
    rw [h, Complex.zero_re] at hα
    exact lt_irrefl _ hα
  have hz := ne_zero_add_mul_I_of_re_ne_zero hτ.ne' y
  have hd : (τ : ℂ) + y * Complex.I - α ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero,
      Complex.zero_re] at he
    linarith only [he, hτ, hα]
  unfold centeredResolventKernel
  field_simp [ha, hz, hd]
  ring

/-- A multiplicity-weighted centered-kernel sum equals the corresponding reciprocal
series times x^z/z². Apply the scalar identity and extract the common factors from the sum.
This connects the evaluated pole series to the vertical logarithmic derivative. -/
theorem tsum_centeredResolventKernel_eq_difference {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (α i).re < 0) {τ x : ℝ} (hτ : 0 < τ) (y : ℝ) :
    (∑' i, (m i : ℂ) * centeredResolventKernel (α i) x τ y) =
      (∑' i, (m i : ℂ) * (1 / ((τ : ℂ) + y * Complex.I - α i) + 1 / α i)) *
          (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
        ((τ : ℂ) + y * Complex.I) ^ 2 := by
  rw [← tsum_mul_right, ← tsum_div_const]
  apply tsum_congr
  intro i
  rw [centeredResolventKernel_eq_difference (hα i) hτ]
  ring

end PseudoPrime.AnalyticNumberTheory.General
