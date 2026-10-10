/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.CompletedProductBounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import PseudoPrime.AnalyticNumberTheory.Gamma.UniformDigamma

/-!
# Archimedean factors with general complex parameters

Work with the parameter range Re(kappa)>-1 in the right half-plane.
The exact gamma-factor logarithmic derivative connects the local zero count
to individual digamma estimates without a Riemann hypothesis.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The product of d gamma factors Gamma((s+kappa_j)/2), for complex parameters
kappa_j. The parameter real parts are constrained separately by theorems.
This is the gamma-product component of the general L-function completion. -/
noncomputable def archimedeanGammaProduct {d : ℕ} (κ : Fin d → ℂ) (s : ℂ) : ℂ :=
  ∏ j : Fin d, Complex.Gamma ((s + κ j) / 2)

/-- If Re s>1 and Re kappa>-1, the gamma argument (s+kappa)/2 has positive
real part. Add the strict bounds and divide by two. This gives the original
general parameter range, without requiring kappa to be real or nonnegative. -/
theorem gammaArgument_re_pos {s κ : ℂ} (hs : 1 < s.re) (hκ : -1 < κ.re) : 0 < ((s + κ) / 2).re := by
  rw [Complex.div_ofNat_re, Complex.add_re]
  linarith only [hs, hκ]

/-- In the same right half-plane, the gamma argument is not any negative
natural number. Positive real part excludes every gamma pole. This supplies
the differentiability conditions for the gamma product. -/
theorem gammaArgument_ne_neg_nat {s κ : ℂ} (hs : 1 < s.re) (hκ : -1 < κ.re) (n : ℕ) :
    (s + κ) / 2 ≠ -(n : ℂ) := by
  intro h
  have hp := gammaArgument_re_pos hs hκ
  rw [h, Complex.neg_re, Complex.natCast_re] at hp
  exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg n))) hp

/-- For parameters with Re kappa_j>-1 and Re s>1, every gamma factor has
positive-real-part argument and is nonzero. Take the finite product.
This provides right-half-plane nonvanishing of the archimedean product. -/
theorem archimedeanGammaProduct_ne_zero {d : ℕ} {κ : Fin d → ℂ} {s : ℂ} (hs : 1 < s.re)
    (hκ : ∀ j, -1 < (κ j).re) : archimedeanGammaProduct κ s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact Complex.Gamma_ne_zero_of_re_pos (gammaArgument_re_pos hs (hκ j))

/-- With Re kappa_j>-1 and Re s>1, the archimedean gamma product is differentiable.
Exclude each gamma pole, compose with the affine argument, and differentiate
the finite product. This permits its logarithmic derivative to be used. -/
theorem differentiableAt_archimedeanGammaProduct {d : ℕ} {κ : Fin d → ℂ} {s : ℂ} (hs : 1 < s.re)
    (hκ : ∀ j, -1 < (κ j).re) : DifferentiableAt ℂ (archimedeanGammaProduct κ) s := by
  apply DifferentiableAt.fun_finsetProd
  intro j _
  exact
    (Complex.differentiableAt_Gamma _ (gammaArgument_ne_neg_nat hs (hκ j))).comp s
      (((hasDerivAt_id' s).add_const (κ j)).div_const 2).differentiableAt

/-- The logarithmic derivative of the gamma product is the sum of one half
the digamma values at (s+kappa_j)/2 in Re s>1. Use the nonvanishing factors,
the finite-product rule, and the affine gamma chain rule. This isolates
the individual archimedean contributions to the explicit formula. -/
theorem logDeriv_archimedeanGammaProduct {d : ℕ} {κ : Fin d → ℂ} {s : ℂ} (hs : 1 < s.re)
    (hκ : ∀ j, -1 < (κ j).re) :
    logDeriv (archimedeanGammaProduct κ) s =
      ∑ j : Fin d, (1 / 2 : ℂ) * Complex.digamma ((s + κ j) / 2) := by
  change logDeriv (fun z ↦ ∏ j : Fin d, Complex.Gamma ((z + κ j) / 2)) s = _
  rw [logDeriv_fun_prod (f := fun j z ↦ Complex.Gamma ((z + κ j) / 2)) (x := s)
      (fun j _ ↦ Complex.Gamma_ne_zero_of_re_pos (gammaArgument_re_pos hs (hκ j)))
      (fun j _ ↦
        (Complex.differentiableAt_Gamma _ (gammaArgument_ne_neg_nat hs (hκ j))).comp s
          (((hasDerivAt_id' s).add_const (κ j)).div_const 2).differentiableAt)]
  exact
    Finset.sum_congr rfl
      (fun j _ ↦
        (((hasDerivAt_id' s).add_const (κ j)).div_const 2).logDeriv_Gamma
          (gammaArgument_ne_neg_nat hs (hκ j)))

/-- For nonzero q and arbitrary complex slope b, the logarithmic derivative
of q^(b*s) equals b*log q. Differentiate the complex power and cancel its
nonzero value. This supplies the pi-power contribution of the gamma factor. -/
theorem logDeriv_affinePower {q : ℂ} (hq : q ≠ 0) (b s : ℂ) :
    logDeriv (fun z ↦ q ^ (b * z)) s = b * Complex.log q := by
  have hd := ((hasDerivAt_id' s).const_mul b).const_cpow (c := q) (Or.inl hq)
  have hp : q ^ (b * s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq)
  rw [logDeriv_apply, hd.deriv]
  calc
    _ = (q ^ (b * s) * (b * Complex.log q)) / q ^ (b * s) := by
      congr 1; ring
    _ = _ := mul_div_cancel_left₀ _ hp

/-- The degree-d archimedean factor pi^(-d*s/2) times the product of
Gamma((s+kappa_j)/2). Its parameters may be complex; nonvanishing and
regularity are stated separately. This matches the completion factor in
Section 5.1 of the reference. -/
noncomputable def archimedeanGammaFactor {d : ℕ} (κ : Fin d → ℂ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ ((-(d : ℂ) / 2) * s) * archimedeanGammaProduct κ s

/-- The real pi constant is nonzero after casting to the complex numbers.
Use positivity of real pi and injectivity of the real cast. This local
implementation fact permits differentiation of its exponential powers. -/
private theorem pi_complex_ne_zero : (Real.pi : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

/-- For Re s>1 and Re kappa_j>-1, the full archimedean factor is nonzero.
Combine the nonzero pi exponential with the gamma-product nonvanishing.
This removes an extra factor-nonvanishing premise from completion estimates. -/
theorem archimedeanGammaFactor_ne_zero {d : ℕ} {κ : Fin d → ℂ} {s : ℂ} (hs : 1 < s.re)
    (hκ : ∀ j, -1 < (κ j).re) : archimedeanGammaFactor κ s ≠ 0 := by
  exact
    mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl pi_complex_ne_zero))
      (archimedeanGammaProduct_ne_zero hs hκ)

/-- The full archimedean factor is differentiable in Re s>1 for parameters
with real part greater than minus one. Differentiate the pi exponential
and gamma product, then multiply. This supplies completion regularity. -/
theorem differentiableAt_archimedeanGammaFactor {d : ℕ} {κ : Fin d → ℂ} {s : ℂ} (hs : 1 < s.re)
    (hκ : ∀ j, -1 < (κ j).re) : DifferentiableAt ℂ (archimedeanGammaFactor κ) s := by
  exact
    ((((hasDerivAt_id' s).const_mul (-(d : ℂ) / 2)).const_cpow (c := (Real.pi : ℂ))
            (Or.inl pi_complex_ne_zero)).differentiableAt).mul
      (differentiableAt_archimedeanGammaProduct hs hκ)

/-- For the general complex parameter range, the gamma-factor logarithmic
derivative equals -d*log(pi)/2 plus half the digamma sum. The pi-power
product rule and the gamma-product formula give the identity. This is the
archimedean decomposition in the general logarithmic explicit formula. -/
theorem logDeriv_archimedeanGammaFactor {d : ℕ} {κ : Fin d → ℂ} {s : ℂ} (hs : 1 < s.re)
    (hκ : ∀ j, -1 < (κ j).re) :
    logDeriv (archimedeanGammaFactor κ) s =
      (-(d : ℂ) / 2) * Complex.log (Real.pi : ℂ) +
        ∑ j : Fin d, (1 / 2 : ℂ) * Complex.digamma ((s + κ j) / 2) := by
  have hp : (Real.pi : ℂ) ^ ((-(d : ℂ) / 2) * s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl pi_complex_ne_zero)
  have hd :=
    ((hasDerivAt_id' s).const_mul (-(d : ℂ) / 2)).const_cpow (c := (Real.pi : ℂ))
      (Or.inl pi_complex_ne_zero)
  change logDeriv (fun z ↦ (Real.pi : ℂ) ^ ((-(d : ℂ) / 2) * z) * archimedeanGammaProduct κ z) s = _
  rw [logDeriv_fun_mul (f := fun z ↦ (Real.pi : ℂ) ^ ((-(d : ℂ) / 2) * z)) (g :=
      archimedeanGammaProduct κ) s hp (archimedeanGammaProduct_ne_zero hs hκ) hd.differentiableAt
      (differentiableAt_archimedeanGammaProduct hs hκ),
    logDeriv_affinePower pi_complex_ne_zero, logDeriv_archimedeanGammaProduct hs hκ]

/-- In the right half-plane, the gamma-factor logarithmic derivative has norm
at most d*norm(log pi)/2 plus half the sum of digamma norms. Apply the triangle
inequality to the exact formula and finite sum. This reduces quantitative
archimedean bounds to individual digamma estimates. -/
theorem norm_logDeriv_archimedeanGammaFactor_le {d : ℕ} {κ : Fin d → ℂ} {s : ℂ} (hs : 1 < s.re)
    (hκ : ∀ j, -1 < (κ j).re) :
    ‖logDeriv (archimedeanGammaFactor κ) s‖ ≤
      (d : ℝ) / 2 * ‖Complex.log (Real.pi : ℂ)‖ +
        (1 / 2 : ℝ) * ∑ j : Fin d, ‖Complex.digamma ((s + κ j) / 2)‖ := by
  rw [logDeriv_archimedeanGammaFactor hs hκ]
  calc
    _ ≤
        ‖(-(d : ℂ) / 2) * Complex.log (Real.pi : ℂ)‖ +
          ‖∑ j : Fin d, (1 / 2 : ℂ) * Complex.digamma ((s + κ j) / 2)‖ :=
      norm_add_le _ _
    _ ≤
        ‖(-(d : ℂ) / 2) * Complex.log (Real.pi : ℂ)‖ +
          ∑ j : Fin d, ‖(1 / 2 : ℂ) * Complex.digamma ((s + κ j) / 2)‖ :=
      add_le_add le_rfl (norm_sum_le _ _)
    _ = _ := by
      simp only [norm_mul, norm_div, norm_neg, norm_natCast, norm_one, Complex.norm_ofNat]
      rw [Finset.mul_sum]

/-- For an entire order-one regularized completion satisfying the conjugate
functional equation and right-half-plane nonvanishing, bound the unit-height
zero count by endpoint order, log conductor, the individual gamma terms,
and the convergent arithmetic majorant. Use the original parameter range
Re kappa_j>-1 to prove gamma regularity and nonvanishing instead of assuming
them. The coefficient bound and logarithmic-derivative series identity remain
explicit inputs. This connects local zero counting to the general factors. -/
theorem localZeroCount_le_archimedeanTerms {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ} (hq : 1 ≤ q) (k : ℤ)
    (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n) (T : ℝ)
    (hL : L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdL : DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I)) :
    (∑' ρ : ℂ, localZeroMultiplicity F T ρ) ≤
      10 *
        (2 * |(k : ℝ)| + Real.log q / 2 +
          ((d : ℝ) / 2 * ‖Complex.log (Real.pi : ℂ)‖ +
            (1 / 2 : ℝ) *
              ∑ j : Fin d, ‖Complex.digamma ((((3 : ℝ) : ℂ) + T * Complex.I + κ j) / 2)‖) +
          (d : ℝ) * ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) := by
  have hs : 1 < ((((3 : ℝ) : ℂ) + T * Complex.I)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero]
    norm_num only
  have hc :=
    localZeroCount_le_completedProductBound hq k hreg hε hfe hright hF h0 horder ha T
      (archimedeanGammaFactor_ne_zero hs hκ) hL (differentiableAt_archimedeanGammaFactor hs hκ) hdL
      hlog
  have hg := norm_logDeriv_archimedeanGammaFactor_le hs hκ
  exact
    hc.trans
      (mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hg) le_rfl) (by norm_num only))

/-- For Re s=3 and Re kappa>-1, bound the half-shifted digamma value by
log(norm(s+kappa)+3)+pi plus the universal digamma-log error. Its argument
has real part at least one, so the uniform right-half-plane estimate applies.
This supplies the general gamma parameter estimate without a Riemann hypothesis. -/
theorem norm_digamma_half_shift_at_three_le_log {s κ : ℂ} (hs : s.re = 3) (hκ : -1 < κ.re) :
    ‖Complex.digamma ((s + κ) / 2)‖ ≤
      Real.log (‖s + κ‖ + 3) + Real.pi + Gamma.digammaLogErrorBound := by
  have ha : 1 ≤ ((s + κ) / 2).re := by
    rw [Complex.div_ofNat_re, Complex.add_re, hs]
    linarith only [hκ]
  have hn : 1 ≤ ‖(s + κ) / 2‖ := ha.trans (Complex.re_le_norm _)
  have hb := Gamma.norm_digamma_le_log_norm_add ((by norm_num only : (1 / 2 : ℝ) ≤ 1).trans ha) hn
  have hm : ‖(s + κ) / 2‖ ≤ ‖s + κ‖ + 3 := by
    rw [norm_div, Complex.norm_ofNat]
    linarith only [norm_nonneg (s + κ)]
  have hl := Real.log_le_log (zero_lt_one.trans_le hn) hm
  linarith only [hb, hl]

/-- At Re s=3 and with all Re kappa_j>-1, the gamma-factor logarithmic
derivative is bounded by a degree-proportional universal constant plus
half the sum of log(norm(s+kappa_j)+3). Sum the individual uniform digamma
bounds and combine them with the exact factor derivative. This gives the
archimedean logarithmic growth term used for local zero counting. -/
theorem norm_logDeriv_archimedeanGammaFactor_at_three_le {d : ℕ} {κ : Fin d → ℂ} {s : ℂ}
    (hs : s.re = 3) (hκ : ∀ j, -1 < (κ j).re) :
    ‖logDeriv (archimedeanGammaFactor κ) s‖ ≤
      (d : ℝ) / 2 * (‖Complex.log (Real.pi : ℂ)‖ + Real.pi + Gamma.digammaLogErrorBound) +
        (1 / 2 : ℝ) * ∑ j : Fin d, Real.log (‖s + κ j‖ + 3) := by
  have hright : 1 < s.re := by
    rw [hs]; norm_num only
  have he := norm_logDeriv_archimedeanGammaFactor_le hright hκ
  have hb :
    (∑ j : Fin d, ‖Complex.digamma ((s + κ j) / 2)‖) ≤
      ∑ j : Fin d, (Real.log (‖s + κ j‖ + 3) + Real.pi + Gamma.digammaLogErrorBound) := by
    exact Finset.sum_le_sum (fun j _ ↦ norm_digamma_half_shift_at_three_le_log hs (hκ j))
  have hm := mul_le_mul_of_nonneg_left hb (by norm_num only : (0 : ℝ) ≤ 1 / 2)
  have hsum :
    (∑ j : Fin d, (Real.log (‖s + κ j‖ + 3) + Real.pi + Gamma.digammaLogErrorBound)) =
      (∑ j : Fin d, Real.log (‖s + κ j‖ + 3)) +
        (d : ℝ) * (Real.pi + Gamma.digammaLogErrorBound) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  rw [hsum] at hm
  linarith only [he, hm]

end PseudoPrime.AnalyticNumberTheory.General
