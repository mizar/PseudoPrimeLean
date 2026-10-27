/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapGammaBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedVariableGapBounds

/-! # Explicit pole-distance budgets for adjustable reciprocal left contours -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a positive gap, bound the kernel on its actual left contour by
(3+6/(e*h))/(1+t^2), where e=delta(h)/2. Compare the first-pole distance and
strip decay with the imaginary part. This retains explicit dependence on the gap. -/
theorem reciprocalGap_left_line_norm_le {h : ℝ} (hh : 0 < h) (t : ℝ) :
    let e := (reciprocalGapMellinKernel h hh).delta / 2
    ‖Analysis.reciprocalGapFunction h (((-1 / 2 - e : ℝ) : ℂ) + Complex.I * t)‖ ≤
      (3 + 6 / (e * h)) / (1 + t ^ 2) := by
  let e := (reciprocalGapMellinKernel h hh).delta / 2
  let s : ℂ := ((-1 / 2 - e : ℝ) : ℂ) + Complex.I * t
  have he : 0 < e := half_pos (reciprocalGapMellinKernel h hh).delta_pos
  have heh : e ≤ h / 8 := by
    have hm : (reciprocalGapMellinKernel h hh).delta ≤ h / 4 := min_le_left _ _
    dsimp only [e]
    linarith only [hm]
  have heu : e ≤ (1 / 16 : ℝ) := by
    have hm : (reciprocalGapMellinKernel h hh).delta ≤ (1 / 8 : ℝ) := min_le_right _ _
    dsimp only [e]
    linarith only [hm]
  have hr : s.re = -1 / 2 - e := by
    simp only [s, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hi : s.im = t := by
    simp only [s, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, one_mul, zero_mul, zero_add]
  have hs : s ∈ reciprocalGapRegion h := by
    change -1 / 2 - min (h / 2) (1 / 4) < s.re ∧ s.re < 3 / 4
    rw [hr]
    have hm : e < min (h / 2) (1 / 4) :=
      lt_min (by linarith only [heh, hh]) (by linarith only [heu])
    constructor <;> linarith only [hm, he]
  have hre : (s + 1 / 2).re = -e := by
    rw [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, hr]
    ring
  have hd := Complex.abs_re_le_norm (s + 1 / 2)
  rw [hre, abs_neg, abs_of_pos he] at hd
  have hk := reciprocalGap_strip_bound hh he hs hd
  have ht : t ^ 2 ≤ ‖s‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hi]
    nlinarith only [sq_nonneg s.re]
  have hB : 0 ≤ 3 + 6 / (e * h) :=
    add_nonneg (by norm_num only) (div_nonneg (by norm_num only) (mul_pos he hh).le)
  change ‖Analysis.reciprocalGapFunction h s‖ ≤ _
  exact
    hk.trans
      (div_le_div_of_nonneg_left hB (by linarith only [sq_nonneg t] : 0 < 1 + t ^ 2)
        (by linarith only [ht]))

/-- The fixed positive logarithmic moment (1/(2*pi)) times the real integral of
(log(4+abs(t))+1)/(1+t^2). Its integrability is already proved.
This universal real quantity factors out of the variable left-contour budget. -/
noncomputable def reciprocalLogMoment : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ, (Real.log (4 + |t|) + 1) / (1 + t ^ 2)

/-- For a primitive nonprincipal character with nonprincipal inverse and positive scale,
bound its left integral by the logarithmic moment times the explicit kernel factor,
log(q)+e^(-2)+e^(-1)+12 and x^(-1/2-e), where e=delta(h)/2 and q>=1.
Reflect the completed logarithmic derivative, apply the explicit gap bound and integrate
the common positive majorant. No GRH is required for this left-integral estimate. -/
theorem reciprocalGap_leftIntegral_norm_le {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q] (hq : 1 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) :
    let e := (reciprocalGapMellinKernel h hh).delta / 2
    ‖reciprocalGapLeftIntegral h hh χ x‖ ≤
      reciprocalLogMoment * (3 + 6 / (e * h)) * (Real.log q + e⁻¹ ^ 2 + e⁻¹ + 12) *
        x ^ (-1 / 2 - e) := by
  let K := reciprocalGapMellinKernel h hh
  let e := K.delta / 2
  let a := -1 / 2 - e
  let B := 3 + 6 / (e * h)
  let U := Real.log q + e⁻¹ ^ 2 + e⁻¹ + 12
  let H := fun t : ℝ ↦ (Real.log (4 + |t|) + 1) / (1 + t ^ 2)
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction ((((a : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
      (K.function ((a : ℂ) + Complex.I * t) * (x : ℂ) ^ ((a : ℂ) + Complex.I * t))
  have he : 0 < e := half_pos K.delta_pos
  have heu : e ≤ (1 / 16 : ℝ) := by
    have hm : K.delta ≤ (1 / 8 : ℝ) := min_le_right _ _
    dsimp only [e]
    linarith only [hm]
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hU : 12 ≤ U := by
    dsimp only [U]
    linarith only [hlog, sq_nonneg e⁻¹, inv_nonneg.mpr he.le]
  have hB : 0 ≤ B :=
    add_nonneg (by norm_num only) (div_nonneg (by norm_num only) (mul_pos he hh).le)
  have ha : -1 / 2 - K.delta < a := by
    dsimp only [a, e]; linarith only [K.delta_pos]
  have hal : a < -1 / 2 := by
    dsimp only [a]; linarith only [he]
  have ha2 : -3 / 2 ≤ a := by
    dsimp only [a]; linarith only [heu]
  have hiF : MeasureTheory.Integrable F :=
    MellinKernel.integrable_completed_left_line K hp hne hinv ha hal ha2 hx
  have hb (t : ℝ) : ‖F t‖ ≤ (B * U * x ^ a) * H t := by
    have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
    have hd :=
      AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_completed_left_strip_le_gap_log hp hne
        hinv he (by linarith only [heu] : e ≤ 1) t
    have hnlog : ‖Complex.log (q : ℂ)‖ = Real.log q := by
      rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    rw [hnlog] at hd
    have hs : (((a : ℝ) : ℂ) + Complex.I * t) + 1 / 2 = (-e : ℂ) + Complex.I * t := by
      dsimp only [a]
      simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
        Complex.ofReal_ofNat]
      ring
    have hd' :
      ‖logDeriv χ.completedLFunction ((((a : ℝ) : ℂ) + Complex.I * t) + 1 / 2)‖ ≤
        U * (Real.log (4 + |t|) + 1) := by
      rw [hs]
      dsimp only [U] at hU ⊢
      nlinarith only [hd, hU, hL]
    have hk := reciprocalGap_left_line_norm_le hh t
    change ‖K.function ((a : ℂ) + Complex.I * t)‖ ≤ B / (1 + t ^ 2) at hk
    dsimp only [F]
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    calc
      _ ≤ (U * (Real.log (4 + |t|) + 1)) * ((B / (1 + t ^ 2)) * x ^ a) :=
        mul_le_mul hd' (mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hx.le a))
          (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx.le a))
          (mul_nonneg (by linarith only [hU] : 0 ≤ U) (by linarith only [hL]))
      _ = _ := by
        dsimp only [H]; ring
  have hiH : MeasureTheory.Integrable (fun t : ℝ ↦ (B * U * x ^ a) * H t) :=
    Analysis.integrable_log_add_abs_div_one_add_sq.const_mul _
  have hi :=
    (MeasureTheory.norm_integral_le_integral_norm F).trans
      (MeasureTheory.integral_mono hiF.norm hiH hb)
  rw [MeasureTheory.integral_const_mul] at hi
  have hd : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos zero_lt_one (mul_pos (by norm_num only) Real.pi_pos))]
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t‖ ≤ _
  rw [norm_mul, hd]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((B * U * x ^ a) * ∫ t : ℝ, H t) :=
      mul_le_mul_of_nonneg_left hi
        (div_nonneg zero_le_one (mul_pos (by norm_num only) Real.pi_pos).le)
    _ = _ := by
      dsimp only [reciprocalLogMoment, B, U, a, e, K, H]; ring

/-- The explicit upper budget for the left integral at positive gap h, level q and scale x.
With e=delta(h)/2, it is the logarithmic moment times (3+6/(e*h)),
log(q)+e^(-2)+e^(-1)+12 and x^(-1/2-e).
It removes the character-dependent integral from the witness separation criterion. -/
noncomputable def reciprocalGapLeftBudget (h : ℝ) (hh : 0 < h) (q : ℕ) (x : ℝ) : ℝ :=
  let e := (reciprocalGapMellinKernel h hh).delta / 2
  reciprocalLogMoment * (3 + 6 / (e * h)) * (Real.log q + e⁻¹ ^ 2 + e⁻¹ + 12) * x ^ (-1 / 2 - e)

/-- Under primitive nonprincipal GRH data with nonprincipal inverse and level at least eight,
one common Gamma constant bounds the remainder after adding the explicit pole and left
budgets, uniformly in all positive gaps and scales at least one.
Combine the separated remainder estimate with the unconditional left-integral bound. -/
theorem exists_uniform_reciprocalGap_remainder_gap_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (h : ℝ) (hh : 0 < h) {q : ℕ} [NeZero q],
          8 ≤ q →
            ∀ {χ : DirichletCharacter ℂ q},
              χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                ∀ {x : ℝ},
                  1 ≤ x →
                    ‖reciprocalGapCompletedRemainder h hh χ x‖ ≤
                      ((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) +
                        reciprocalGapLeftBudget h hh q x +
                        C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_reciprocalGap_remainder_split_bound
  refine ⟨C, hC, ?_⟩
  intro h hh q _ hq χ hp hne hinv hGRH x hx
  have hL : ‖reciprocalGapLeftIntegral h hh χ x‖ ≤ reciprocalGapLeftBudget h hh q x :=
    reciprocalGap_leftIntegral_norm_le hh ((by norm_num only : 1 ≤ 8).trans hq) hp hne hinv
      (zero_lt_one.trans_le hx)
  have hR := hb h hh hq hp hne hGRH hx
  linarith only [hR, hL]

/-- For primitive nonprincipal GRH characters of level at least eight, the principal finite
sum exceeding the zero-prefix budget, explicit pole cost, explicit left budget and one
common Gamma constant gives a prime non-one witness below the scale.
Apply exact prime separation after bounding the remainder. All character-dependent contour
integrals have been removed, but universal constants still need numerical evaluation. -/
theorem exists_uniform_reciprocalGap_prime_gap_separation :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (h : ℝ) (hh : 0 < h) {q : ℕ} [NeZero q],
          8 ≤ q →
            ∀ {χ : DirichletCharacter ℂ q},
              AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ {c x : ℝ},
                  (1 / 2 : ℝ) < c →
                    c ^ 2 ≤ 1 / 4 + h / 2 →
                    1 ≤ x →
                    ∀ B : Finset ℕ,
                      (1 / c) *
                              (Real.log q / 2 +
                                  (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
                                  (∑' n : ℕ,
                                    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
                                ∑ n ∈ B,
                                  (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n /
                                    (n : ℝ) ^ (1 / 2 + c)) +
                            (((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) +
                              reciprocalGapLeftBudget h hh q x +
                              C) <
                          (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re →
                        ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_reciprocalGap_remainder_gap_bound
  refine ⟨C, hC, ?_⟩
  intro h hh q _ hq χ hGRH hp hne hinv c x hc hbound hx B hgap
  apply
    exists_prime_not_one_of_reciprocalGap_separation hh ((by norm_num only : 2 ≤ 8).trans hq) hGRH
      hp hne hinv hc hbound hx B
  have hr :=
    (Complex.re_le_norm (reciprocalGapCompletedRemainder h hh χ x)).trans
      (hb h hh hq hp hne hinv hGRH hx)
  exact (add_le_add (le_refl _) hr).trans_lt hgap

end PseudoPrime.LLS.PaperStatements
