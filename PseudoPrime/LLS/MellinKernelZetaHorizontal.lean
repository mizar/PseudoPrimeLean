/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelHorizontal
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.HorizontalLogDerivBound
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.HeightSequence

/-! # Vanishing horizontal edges for the Riemann xi Mellin contour

Good zeta heights and the xi functional equation control both horizontal edges.
The Mellin kernel quadratic decay makes their boundary integrals vanish.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- For a Mellin kernel, a fixed interval in its strip and in `[-1,1]`, and
`x ≥ 1`, both signed horizontal ξ integrals tend to zero along zeta good heights.
The pole and gamma terms divided by the height squared vanish, as does the
squared-logarithmic zeta term. Apply the kernel horizontal majorant to this
vanishing bound. This removes the horizontal edges in the principal contour. -/
theorem tendsto_xi_horizontalIntegral (K : MellinKernel) {a b x : ℝ} (hab : a ≤ b)
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) (ha' : -1 ≤ a) (hb' : b ≤ 1) (hx : 1 ≤ x)
    (e : ℝ) (he : e = 1 ∨ e = -1) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ σ in a..b,
          logDeriv AnalyticNumberTheory.RiemannXi.riemannXi
              (((σ : ℂ) +
                  ((e * AnalyticNumberTheory.RiemannZeta.goodHeightSeq n : ℝ) : ℂ) * Complex.I) +
                1 / 2) *
            K.function
              ((σ : ℂ) +
                ((e * AnalyticNumberTheory.RiemannZeta.goodHeightSeq n : ℝ) : ℂ) * Complex.I) *
            (x : ℂ) ^
              ((σ : ℂ) +
                ((e * AnalyticNumberTheory.RiemannZeta.goodHeightSeq n : ℝ) : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    AnalyticNumberTheory.RiemannXi.exists_norm_logDeriv_signed_good_height_le
  let T := AnalyticNumberTheory.RiemannZeta.goodHeightSeq
  let D := AnalyticNumberTheory.RiemannZeta.qMinusOneZetaLogDerivConst
  have hT (n : ℕ) : 8 ≤ T n :=
    (le_add_of_nonneg_right (Nat.cast_nonneg n)).trans
      (AnalyticNumberTheory.RiemannZeta.goodHeightSeq_mem n).1
  have hpos (n : ℕ) : 0 < T n := by linarith only [hT n]
  have hi :=
    tendsto_inv_atTop_zero.comp AnalyticNumberTheory.RiemannZeta.tendsto_goodHeightSeq_atTop
  have hs := hi.pow 2
  have hl :=
    AnalyticNumberTheory.RiemannZeta.tendsto_log_add_two_sq_div_sq_atTop.comp
      AnalyticNumberTheory.RiemannZeta.tendsto_goodHeightSeq_atTop
  apply
    tendsto_horizontalIntegral_of_scaled_bound K hab ha hb hx (fun n => e * T n)
      (fun n =>
        (T n)⁻¹ ^ 2 + C * ((T n)⁻¹ + (T n)⁻¹ ^ 2) + D * (Real.log (T n + 2) ^ 2 / (T n) ^ 2))
      (F := fun s => logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s + 1 / 2))
  · intro n
    rcases he with rfl | rfl
    · rw [one_mul, abs_of_pos (hpos n)]
      linarith only [hT n]
    · rw [neg_one_mul, abs_neg, abs_of_pos (hpos n)]
      linarith only [hT n]
  · intro n
    exact
      add_nonneg
        (add_nonneg (sq_nonneg _)
          (mul_nonneg hC (add_nonneg (inv_nonneg.mpr (hpos n).le) (sq_nonneg _))))
        (mul_nonneg AnalyticNumberTheory.RiemannZeta.qMinusOneZetaLogDerivConst_nonneg
          (div_nonneg (sq_nonneg _) (sq_nonneg _)))
  · simpa only [Function.comp_apply, zero_pow (by norm_num only : (2 : ℕ) ≠ 0), zero_add,
      mul_zero] using (hs.add ((hi.add hs).const_mul C)).add (hl.const_mul D)
  · intro n σ hσ
    have hσ' : a < σ ∧ σ ≤ b := by simpa only [Set.uIoc_of_le hab, Set.mem_Ioc] using hσ
    have h :=
      hbound (8 + (n : ℝ)) (T n) (σ + 1 / 2) e (le_add_of_nonneg_right (Nat.cast_nonneg n))
        (AnalyticNumberTheory.RiemannZeta.goodHeightSeq_mem n)
        (AnalyticNumberTheory.RiemannZeta.goodHeightSeq_good n) (by linarith only [ha', hσ'.1])
        (by linarith only [hb', hσ'.2]) he
    have hsq : (e * T n) ^ 2 = (T n) ^ 2 := by
      rcases he with rfl | rfl
      · rw [one_mul]
      · rw [neg_one_mul, neg_sq]
    rw [hsq]
    have hi1 : (T n)⁻¹ * (T n) ^ 2 = T n := by
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (hpos n).ne', one_mul]
    have hi2 : (T n)⁻¹ ^ 2 * (T n) ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (hpos n).ne', one_pow]
    rw [add_mul, add_mul, mul_assoc, mul_assoc, add_mul, hi1, hi2,
      div_mul_cancel₀ _ (pow_ne_zero 2 (hpos n).ne')]
    simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      add_assoc, add_comm, add_left_comm] using h

end PseudoPrime.LLS.PaperStatements.MellinKernel
