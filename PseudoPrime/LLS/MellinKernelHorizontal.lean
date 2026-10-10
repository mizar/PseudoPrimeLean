/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelContour
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveHorizontalLogDerivBound

/-! # Horizontal edges for general Mellin kernels

Quadratic kernel decay combines with good-height bounds for the completed
logarithmic derivative to remove the horizontal edges of the contour.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- A single positive kernel constant controls horizontal integrals of
`F(s)K(s)x^s` on every interval in the admissible strip, for `x≥1` and height
of absolute value at least one. A bound `norm(F)≤ε t²` cancels quadratic
kernel decay. The resulting bound is `ε C x^b |b-a|`. -/
theorem exists_horizontal_integral_bound (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {a b x t ε : ℝ},
          a ≤ b →
            -1 / 2 - K.delta < a →
            b ≤ 1 / 2 + K.delta →
            1 ≤ x →
            1 ≤ |t| →
            0 ≤ ε →
            ∀ F : ℂ → ℂ,
              (∀ σ ∈ Set.uIoc a b, ‖F ((σ : ℂ) + t * Complex.I)‖ ≤ ε * t ^ 2) →
                ‖∫ σ in a..b,
                      F ((σ : ℂ) + t * Complex.I) * K.function ((σ : ℂ) + t * Complex.I) *
                        (x : ℂ) ^ ((σ : ℂ) + t * Complex.I)‖ ≤
                  ε * C * x ^ b * |b - a| := by
  obtain ⟨C, hC, hdec⟩ := K.decay 1 (by norm_num only)
  refine ⟨C, hC, ?_⟩
  intro a b x t ε hab ha hb hx ht hε F hF
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσ
  have hσ' : a < σ ∧ σ ≤ b := by simpa only [Set.uIoc_of_le hab, Set.mem_Ioc] using hσ
  have hr : ((σ : ℂ) + t * Complex.I).re = σ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hi : ((σ : ℂ) + t * Complex.I).im = t := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, zero_add, add_zero]
  have hs :=
    K.strip_subset
      (by
        rw [Set.mem_ofPred_eq, hr]
        exact ⟨ha.trans hσ'.1, hσ'.2.trans hb⟩)
  have hd : 1 ≤ ‖(σ : ℂ) + t * Complex.I + 1 / 2‖ :=
    ht.trans
      (by
        simpa only [Complex.add_im, hi, Complex.div_ofNat_im, Complex.one_im, zero_div,
          add_zero] using Complex.abs_im_le_norm ((σ : ℂ) + t * Complex.I + 1 / 2))
  have hsquare : t ^ 2 ≤ ‖(σ : ℂ) + t * Complex.I‖ ^ 2 := by
    have h := Complex.abs_im_le_norm ((σ : ℂ) + t * Complex.I)
    rw [hi] at h
    have hh := mul_self_le_mul_self (abs_nonneg t) h
    simpa only [← pow_two, sq_abs] using hh
  have htp : 0 < t ^ 2 := by nlinarith only [ht, sq_abs t]
  have hk :=
    (hdec _ hs hd).trans
      (div_le_div_of_nonneg_left hC.le htp
        (by linarith only [hsquare] : t ^ 2 ≤ 1 + ‖(σ : ℂ) + t * Complex.I‖ ^ 2))
  have hp : ‖(x : ℂ) ^ ((σ : ℂ) + t * Complex.I)‖ ≤ x ^ b := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx), hr]
    exact Real.rpow_le_rpow_of_exponent_le hx hσ'.2
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (ε * t ^ 2) * (C / t ^ 2) * x ^ b :=
      mul_le_mul (mul_le_mul (hF σ hσ) hk (norm_nonneg _) (by positivity)) hp (norm_nonneg _)
        (by positivity)
    _ = ε * C * (t ^ 2 / t ^ 2) * x ^ b := by ring
    _ = _ := by rw [div_self htp.ne', mul_one]

/-- If scaled horizontal bounds tend to zero and the heights have absolute
value at least one, the horizontal integrals tend to zero on each fixed
strip interval and at each fixed `x≥1`. Apply the kernel majorant and squeeze
the integral norms. This is the horizontal-edge limit interface. -/
theorem tendsto_horizontalIntegral_of_scaled_bound (K : MellinKernel) {a b x : ℝ} (hab : a ≤ b)
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) (hx : 1 ≤ x) (T ε : ℕ → ℝ)
    (ht : ∀ n, 1 ≤ |T n|) (hε : ∀ n, 0 ≤ ε n) (hlim : Filter.Tendsto ε Filter.atTop (nhds 0))
    (F : ℂ → ℂ) (hF : ∀ n, ∀ σ ∈ Set.uIoc a b, ‖F ((σ : ℂ) + T n * Complex.I)‖ ≤ ε n * (T n) ^ 2) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ σ in a..b,
          F ((σ : ℂ) + T n * Complex.I) * K.function ((σ : ℂ) + T n * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + T n * Complex.I))
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_horizontal_integral_bound K
  apply squeeze_zero_norm (a := fun n ↦ ε n * C * x ^ b * |b - a|)
  · intro n
    exact hbound hab ha hb hx (ht n) (hε n) F (hF n)
  · simpa only [zero_mul] using ((hlim.mul_const C).mul_const (x ^ b)).mul_const |b - a|

open AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive nonprincipal character and `x≥1`, GRH supplies good heights
along which both signed horizontal integrals of the completed logarithmic
derivative times `K(s)x^s` tend to zero. The interval must lie in the kernel
strip and in `[-5/2,3/2]`, so its shifted arguments satisfy `abs(Re)≤2`.
The centered good-height bound and the inverse-square constant term give a
vanishing majorant. This removes the horizontal edges in Lemma 6.1. -/
theorem tendsto_completed_horizontalIntegral (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b x : ℝ} (hab : a ≤ b)
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) (ha' : -5 / 2 ≤ a) (hb' : b ≤ 3 / 2)
    (hx : 1 ≤ x) (e : ℝ) (he : e = 1 ∨ e = -1) :
    let T := primitiveHorizontalHeightSeq hq hGRH hp hne hinv
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ σ in a..b,
          (logDeriv (DirichletCharacter.completedLFunction χ)
              (((σ : ℂ) + ((e * T n : ℝ) : ℂ) * Complex.I) + 1 / 2)) *
            K.function ((σ : ℂ) + ((e * T n : ℝ) : ℂ) * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + ((e * T n : ℝ) : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  let T := primitiveHorizontalHeightSeq hq hGRH hp hne hinv
  have ht (n : ℕ) : 1 ≤ T n :=
    (le_add_of_nonneg_left (Nat.cast_nonneg n)).trans
      (primitiveHorizontalHeightSeq_ge hq hGRH hp hne hinv n)
  apply
    tendsto_horizontalIntegral_of_scaled_bound K hab ha hb hx (fun n ↦ e * T n)
      (fun n ↦
        primitiveHorizontalStripEpsilon hq hGRH hp hne hinv n +
          ‖logDeriv (DirichletCharacter.completedLFunction χ) 0‖ / (T n) ^ 2)
      (F := fun s : ℂ ↦ logDeriv (DirichletCharacter.completedLFunction χ) (s + 1 / 2))
  · intro n
    rcases he with rfl | rfl
    · simpa only [one_mul, abs_of_nonneg (zero_le_one.trans (ht n))] using ht n
    · simpa only [neg_one_mul, abs_neg, abs_of_nonneg (zero_le_one.trans (ht n))] using ht n
  · intro n
    exact
      add_nonneg (primitiveHorizontalStripEpsilon_nonneg hq hGRH hp hne hinv n)
        (div_nonneg (norm_nonneg _) (sq_nonneg _))
  · have hTi :=
      tendsto_inv_atTop_zero.comp (tendsto_primitiveHorizontalHeightSeq_atTop hq hGRH hp hne hinv)
    have hB :
      Filter.Tendsto (fun n ↦ ‖logDeriv (DirichletCharacter.completedLFunction χ) 0‖ / (T n) ^ 2)
        Filter.atTop (nhds 0) := by
      simpa only [Function.comp_apply, div_eq_mul_inv, inv_pow,
        zero_pow (by norm_num only : (2 : ℕ) ≠ 0), mul_zero] using
        (hTi.pow 2).const_mul ‖logDeriv (DirichletCharacter.completedLFunction χ) 0‖
    simpa only [zero_add] using
      (tendsto_primitiveHorizontalStripEpsilon_atTop hq hGRH hp hne hinv).add hB
  · intro n σ hσ
    have hσ' : a < σ ∧ σ ≤ b := by simpa only [Set.uIoc_of_le hab, Set.mem_Ioc] using hσ
    have hσbound : |σ + 1 / 2| ≤ 2 :=
      abs_le.mpr ⟨by linarith only [ha', hσ'.1], by linarith only [hb', hσ'.2]⟩
    have hf := primitiveHorizontalHeightSeq_completedLogDeriv_bound hq hGRH hp hne hinv n hσbound
    have htsq : 0 < (T n) ^ 2 := sq_pos_of_pos (zero_lt_one.trans_le (ht n))
    have hcenter :
      ‖logDeriv (DirichletCharacter.completedLFunction χ)
              (((σ : ℂ) + ((e * T n : ℝ) : ℂ) * Complex.I) + 1 / 2) -
            logDeriv (DirichletCharacter.completedLFunction χ) 0‖ ≤
        primitiveHorizontalStripEpsilon hq hGRH hp hne hinv n * (e * T n) ^ 2 := by
      rcases he with rfl | rfl
      · have h := (div_le_iff₀ htsq).mp hf.1
        simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
          Complex.ofReal_ofNat, one_mul, add_assoc, add_comm, add_left_comm] using h
      · have h := (div_le_iff₀ htsq).mp hf.2
        simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
          Complex.ofReal_ofNat, neg_one_mul, one_mul, Complex.ofReal_neg, neg_mul, neg_sq,
          sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    have hsquare : (e * T n) ^ 2 = (T n) ^ 2 := by
      rcases he with rfl | rfl
      · rw [one_mul]
      · rw [neg_one_mul, neg_sq]
    rw [hsquare] at hcenter ⊢
    calc
      _ ≤ _ := norm_le_norm_sub_add _ (logDeriv (DirichletCharacter.completedLFunction χ) 0)
      _ ≤
          primitiveHorizontalStripEpsilon hq hGRH hp hne hinv n * (T n) ^ 2 +
            ‖logDeriv (DirichletCharacter.completedLFunction χ) 0‖ :=
        add_le_add hcenter (le_refl _)
      _ = _ := by rw [add_mul, div_mul_cancel₀ _ htsq.ne']

end PseudoPrime.LLS.PaperStatements.MellinKernel
