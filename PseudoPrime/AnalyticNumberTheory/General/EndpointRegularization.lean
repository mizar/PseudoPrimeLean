/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.EntireHadamard
public import PseudoPrime.AnalyticNumberTheory.General.GenusConvergence
public import PseudoPrime.AnalyticNumberTheory.General.EntireOrder

/-!
# Endpoint regularization and logarithmic zero expansions

Remove integral orders at zero and one before applying the entire centered
Hadamard identity. The recovered logarithmic derivative keeps both endpoint
terms, including negative orders when the original function has endpoint zeros.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- At a point away from zero and one where L is differentiable and nonzero,
multiplication by (s(1-s))^r adds r/s+r/(s-1) to its logarithmic derivative.
The integer r allows poles and endpoint zeros to be treated with the same formula.
This is the endpoint correction used in the logarithmic explicit formula. -/
theorem logDeriv_endpointRegularization {L : ℂ → ℂ} {s : ℂ} (r : ℤ) (hs : s ≠ 0) (h1 : s ≠ 1)
    (hL : L s ≠ 0) (hd : DifferentiableAt ℂ L s) :
    logDeriv (fun z ↦ (z * (1 - z)) ^ r * L z) s =
      (r : ℂ) * (1 / s + 1 / (s - 1)) + logDeriv L s := by
  have hp : s * (1 - s) ≠ 0 := mul_ne_zero hs (sub_ne_zero.mpr h1.symm)
  have hb : DifferentiableAt ℂ (fun z : ℂ ↦ z * (1 - z)) s :=
    differentiableAt_id.mul ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id)
  rw [logDeriv_fun_mul (f := fun z : ℂ ↦ (z * (1 - z)) ^ r) (g := L) s (zpow_ne_zero r hp) hL
      (hb.zpow (Or.inl hp)) hd,
    logDeriv_fun_zpow hb]
  congr 1
  rw [logDeriv_fun_mul (f := fun z : ℂ ↦ z) (g := fun z ↦ 1 - z) s hs (sub_ne_zero.mpr h1.symm)
      differentiableAt_id ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id)]
  rw [logDeriv_id', logDeriv_apply, ((hasDerivAt_id' s).const_sub (1 : ℂ)).deriv]
  rw [show (1 - s : ℂ) = -(s - 1) from (neg_sub s 1).symm, neg_div_neg_eq]

/-- Away from zero and one, a regularization identity implies equality of
logarithmic derivatives. Restrict the pointwise identity to a neighborhood that
avoids both endpoints, then use locality of derivatives. No value of the
meromorphic function at its poles is prescribed; F has its own endpoint values. -/
theorem logDeriv_eq_of_endpointRegularization {L F : ℂ → ℂ} (r : ℤ)
    (hreg : ∀ z, z ≠ 0 → z ≠ 1 → F z = (z * (1 - z)) ^ r * L z) {s : ℂ} (hs : s ≠ 0) (h1 : s ≠ 1) :
    logDeriv F s = logDeriv (fun z ↦ (z * (1 - z)) ^ r * L z) s := by
  have he : F =ᶠ[nhds s] (fun z ↦ (z * (1 - z)) ^ r * L z) := by
    filter_upwards [eventually_ne_nhds hs, eventually_ne_nhds h1] with z hz0 hz1
    exact hreg z hz0 hz1
  simp only [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]

/-- Recover the negative logarithmic derivative of L from the centered derivative
of its endpoint regularization F. The assumed centered identity contributes Z;
the product rule supplies the two endpoint terms. This separates the elementary
endpoint calculation from the analytic zero expansion. -/
theorem neg_logDeriv_of_endpointRegularization {L F : ℂ → ℂ} (r : ℤ)
    (hreg : ∀ z, z ≠ 0 → z ≠ 1 → F z = (z * (1 - z)) ^ r * L z) {s : ℂ} (hs : s ≠ 0) (h1 : s ≠ 1)
    (hL : L s ≠ 0) (hd : DifferentiableAt ℂ L s) {Z : ℂ}
    (hgenus : logDeriv F s - logDeriv F 0 = Z) :
    -logDeriv L s = (r : ℂ) * (1 / s + 1 / (s - 1)) - logDeriv F 0 - Z := by
  have he := logDeriv_endpointRegularization r hs h1 hL hd
  rw [← logDeriv_eq_of_endpointRegularization r hreg hs h1] at he
  linear_combination he - hgenus

/-- An entire endpoint regularization F, nonzero at zero, with subquadratic
exponential growth gives an absolutely convergent genus-one series and the
logarithmic zero expansion of L away from its zeros and endpoints.
Apply the centered Hadamard identity and remove the integer endpoint factors.
No hypothesis on the real parts of the zeros or Riemann hypothesis is used.
This supplies the meromorphic endpoint correction in equation (5.24). -/
theorem neg_logDeriv_eq_genusSum_of_endpointRegularization {L F : ℂ → ℂ} (k : ℤ)
    (hreg : ∀ z, z ≠ 0 → z ≠ 1 → F z = (z * (1 - z)) ^ k * L z) (hF : Differentiable ℂ F)
    (h0 : F 0 ≠ 0) {C r : ℝ} (hC : 0 < C) (hr0 : 0 ≤ r) (hr2 : r < 2)
    (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r)) {s : ℂ} (hs : s ≠ 0) (h1 : s ≠ 1)
    (hL : L s ≠ 0) (hd : DifferentiableAt ℂ L s) :
    -logDeriv L s =
      (k : ℂ) * (1 / s + 1 / (s - 1)) - logDeriv F 0 -
        ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  have hFs : F s ≠ 0 := by
    rw [hreg s hs h1]
    exact mul_ne_zero (zpow_ne_zero k (mul_ne_zero hs (sub_ne_zero.mpr h1.symm))) hL
  exact
    neg_logDeriv_of_endpointRegularization k hreg hs h1 hL hd
      (PseudoPrime.AnalyticNumberTheory.General.centered_logDeriv_eq_genusSum hF h0 hC hr0 hr2 hg
        hFs (summable_genusTerms_of_entireGrowth hF h0 hC hr0 hr2 hg s))

/-- For the same entire endpoint regularization, subtract logarithmic derivatives
at two nonzero, nonunit points where L is differentiable and nonvanishing.
The centered constant and reciprocal-zero corrections cancel, leaving an
absolutely convergent resolvent difference and explicit endpoint corrections.
This is the constant-free form used before termwise contour integration. -/
theorem neg_logDeriv_sub_eq_resolventSum {L F : ℂ → ℂ} (k : ℤ)
    (hreg : ∀ z, z ≠ 0 → z ≠ 1 → F z = (z * (1 - z)) ^ k * L z) (hF : Differentiable ℂ F)
    (h0 : F 0 ≠ 0) {C r : ℝ} (hC : 0 < C) (hr0 : 0 ≤ r) (hr2 : r < 2)
    (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r)) {s t : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1)
    (hLs : L s ≠ 0) (hds : DifferentiableAt ℂ L s) (ht : t ≠ 0) (ht1 : t ≠ 1) (hLt : L t ≠ 0)
    (hdt : DifferentiableAt ℂ L t) :
    -logDeriv L s + logDeriv L t =
      (k : ℂ) * ((1 / s + 1 / (s - 1)) - (1 / t + 1 / (t - 1))) -
        ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ)) := by
  have hgs := summable_genusTerms_of_entireGrowth hF h0 hC hr0 hr2 hg s
  have hgt := summable_genusTerms_of_entireGrowth hF h0 hC hr0 hr2 hg t
  have he :
    (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ))) =
      (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) -
        (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (t - ρ) + 1 / ρ)) := by
    rw [← hgs.tsum_sub hgt]
    exact tsum_congr (fun ρ ↦ by ring)
  rw [he]
  have hss :=
    neg_logDeriv_eq_genusSum_of_endpointRegularization k hreg hF h0 hC hr0 hr2 hg hs hs1 hLs hds
  have htt :=
    neg_logDeriv_eq_genusSum_of_endpointRegularization k hreg hF h0 hC hr0 hr2 hg ht ht1 hLt hdt
  linear_combination hss - htt

/-- An entire endpoint regularization of order at most one has the logarithmic
zero expansion with integer endpoint terms. Its identity with (s(1-s))^k L(s)
is required only off the endpoints, allowing F to take the removable-extension
values there. A global growth bound of exponent 3/2 discharges both the
Hadamard growth and absolute-convergence requirements in equation (5.24). -/
theorem neg_logDeriv_eq_genusSum_of_orderAtMostOne {L F : ℂ → ℂ} (k : ℤ)
    (hreg : ∀ z, z ≠ 0 → z ≠ 1 → F z = (z * (1 - z)) ^ k * L z) (hF : Differentiable ℂ F)
    (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {s : ℂ} (hs : s ≠ 0) (h1 : s ≠ 1) (hL : L s ≠ 0)
    (hd : DifferentiableAt ℂ L s) :
    -logDeriv L s =
      (k : ℂ) * (1 / s + 1 / (s - 1)) - logDeriv F 0 -
        ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  obtain ⟨C, hC, hg⟩ :=
    exists_global_exponential_bound_of_orderAtMostOne hF.continuous horder (r := 3 / 2)
      (by norm_num only)
  exact
    neg_logDeriv_eq_genusSum_of_endpointRegularization k hreg hF h0 hC
      (by norm_num only : (0 : ℝ) ≤ 3 / 2) (by norm_num only : (3 / 2 : ℝ) < 2) hg hs h1 hL hd

end PseudoPrime.AnalyticNumberTheory.General
