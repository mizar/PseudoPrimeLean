/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZeroTwoFrequency

/-! # Three-frequency phase inequality and shifted explicit formulas -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Completing two real squares gives the phase inequality with all three mixed
cosines for arbitrary signed coefficients and three angles. -/
theorem three_frequency_weighted_le (θ a b c p q s : ℝ) :
    p * (Real.cos a + Real.cos (θ - a)) + q * (Real.cos b + Real.cos (θ - b)) +
          s * (Real.cos c + Real.cos (θ - c)) -
        (p ^ 2 + q ^ 2 + s ^ 2) / 2 -
        p * q * Real.cos (a - b) -
        p * s * Real.cos (a - c) -
        q * s * Real.cos (b - c) ≤
      1 + Real.cos θ := by
  have hx := sq_nonneg (1 + Real.cos θ - p * Real.cos a - q * Real.cos b - s * Real.cos c)
  have hy := sq_nonneg (Real.sin θ - p * Real.sin a - q * Real.sin b - s * Real.sin c)
  simp only [Real.cos_sub]
  linear_combination
    hx / 2 + hy / 2 + Real.sin_sq_add_cos_sq θ / 2 + (p ^ 2 / 2) * Real.sin_sq_add_cos_sq a +
      (q ^ 2 / 2) * Real.sin_sq_add_cos_sq b +
      (s ^ 2 / 2) * Real.sin_sq_add_cos_sq c

/-- Summing the three-frequency phase inequality against nonnegative summable
weights preserves every mixed cosine term. -/
theorem three_frequency_weighted_tsum {ι : Type*} (w θ g : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (a b c p q s : ℝ) :
    let W := fun (f : ι → ℝ) ↦ ∑' i, w i * Real.cos (f i)
    let M := ∑' i, w i
    p * (W (fun i ↦ a * g i) + W (fun i ↦ θ i - a * g i)) +
          q * (W (fun i ↦ b * g i) + W (fun i ↦ θ i - b * g i)) +
          s * (W (fun i ↦ c * g i) + W (fun i ↦ θ i - c * g i)) -
        ((p ^ 2 + q ^ 2 + s ^ 2) / 2) * M -
        p * q * W (fun i ↦ (a - b) * g i) -
        p * s * W (fun i ↦ (a - c) * g i) -
        q * s * W (fun i ↦ (b - c) * g i) ≤
      M + W θ := by
  intro W M
  have hc (f : ι → ℝ) : Summable (fun i ↦ w i * Real.cos (f i)) := by
    apply hs.of_norm_bounded
    intro i
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i)]
    exact mul_le_of_le_one_right (hw i) (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  have h (f : ι → ℝ) := (hc f).hasSum
  have term (z t : ℝ) := ((h (fun i ↦ z * g i)).add (h (fun i ↦ θ i - z * g i))).mul_left t
  have cross (z t : ℝ) := (h (fun i ↦ z * g i)).mul_left t
  have hl :=
    ((((((term a p).add (term b q)).add (term c s)).sub
                  (hs.hasSum.mul_left ((p ^ 2 + q ^ 2 + s ^ 2) / 2))).sub
              (cross (a - b) (p * q))).sub
          (cross (a - c) (p * s))).sub
      (cross (b - c) (q * s))
  apply hasSum_le _ hl (hs.hasSum.add (h θ))
  intro i
  have hi :=
    mul_le_mul_of_nonneg_left
      (three_frequency_weighted_le (θ i) (a * g i) (b * g i) (c * g i) p q s) (hw i)
  rw [sub_mul a b, sub_mul a c, sub_mul b c]
  linarith only [hi]

/-- Under GRH the three-frequency phase inequality applies to the oscillating
zero series of a primitive nonprincipal character. -/
theorem quarter_zero_three_frequency {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (a b c p v s : ℝ) :
    let Z := quarterKernel570.oscillatingZeroTerm χ x
    let W := fun t : ℝ ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (t * ρ.im)
    let T := fun t : ℝ ↦ (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ (x * Real.exp (-t)) ρ).re
    p * (W a + T a) + v * (W b + T b) + s * (W c + T c) -
        ((p ^ 2 + v ^ 2 + s ^ 2) / 2) * quarterMass570 χ -
        p * v * W (a - b) -
        p * s * W (a - c) -
        v * s * W (b - c) ≤
      quarterMass570 χ + (∑' ρ : ℂ, Z ρ).re := by
  intro Z W T
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm quarterKernel570 hq hG hp hn hi hx
  have hm : (∑' ρ : ℂ, ‖Z ρ‖) = quarterMass570 χ := by
    apply tsum_congr
    intro ρ
    exact
      (LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm quarterKernel570 χ hx ρ).trans
        (kernel_zero_norm_570 hn ρ)
  have hr : (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (Z ρ).arg) = (∑' ρ : ℂ, Z ρ).re := by
    rw [Complex.re_tsum hs]
    exact tsum_congr (fun ρ ↦ Complex.norm_mul_cos_arg (Z ρ))
  have h :=
    three_frequency_weighted_tsum (fun ρ ↦ ‖Z ρ‖) (fun ρ ↦ (Z ρ).arg) Complex.im
      (fun ρ ↦ norm_nonneg (Z ρ)) hs.norm a b c p v s
  dsimp only at h
  rw [hm, hr, shifted_phase_eq_zero_sum hq hG hp hn hi hx a,
    shifted_phase_eq_zero_sum hq hG hp hn hi hx b,
    shifted_phase_eq_zero_sum hq hG hp hn hi hx c] at h
  exact h

/-- When the character is trivial at primes through the cutoff, apply the
explicit formula at each of the three shifted cutoffs and retain all mixed terms. -/
theorem three_frequency_contour_lower {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (a b c p v s : ℝ) (ha : 14 / 5 ≤ a) (hb : 14 / 5 ≤ b)
    (hc : 14 / 5 ≤ c) (hxa : 1 ≤ x * Real.exp (-a)) (hxb : 1 ≤ x * Real.exp (-b))
    (hxc : 1 ≤ x * Real.exp (-c)) (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ x → χ l = 1) :
    let Z := quarterKernel570.oscillatingZeroTerm χ x
    let W := fun t : ℝ ↦ ∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (t * ρ.im)
    let T := fun t : ℝ ↦
      let y := x * Real.exp (-t)
      contourNonEuler570 χ y - reflectedIntegral570 χ y -
        (∑' n : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) y n).re
    p * (W a + T a) + v * (W b + T b) + s * (W c + T c) -
        ((p ^ 2 + v ^ 2 + s ^ 2) / 2) * quarterMass570 χ -
        p * v * W (a - b) -
        p * s * W (a - c) -
        v * s * W (b - c) ≤
      quarterMass570 χ + (∑' ρ : ℂ, Z ρ).re := by
  intro Z W T
  have h := quarter_zero_three_frequency hq hG hp hn hi hx a b c p v s
  dsimp only at h
  rw [zero_re_eq_contour_sub_prime hq hG hp hn hi hxa,
    zero_re_eq_contour_sub_prime hq hG hp hn hi hxb,
    zero_re_eq_contour_sub_prime hq hG hp hn hi hxc, twoShift_forward_eq_principal χ hx ha hpass,
    twoShift_forward_eq_principal χ hx hb hpass, twoShift_forward_eq_principal χ hx hc hpass] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
