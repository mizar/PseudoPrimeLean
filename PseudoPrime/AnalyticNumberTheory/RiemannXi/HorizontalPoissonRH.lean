/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CenteredHadamard

/-! # Xi logarithmic derivative as a positive horizontal zero sum -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- For a point on the critical line, the real genus term centered by half
the term at one is the Poisson kernel at an arbitrary complex point. The
two inverse-zero terms cancel because their norm squares agree. -/
theorem genus_re_centering (s ρ : ℂ) (k : ℕ) (hr : ρ.re = 1 / 2) :
    ((k : ℂ) * (1 / (s - ρ) + 1 / ρ)).re - (1 / 2 : ℝ) * ((k : ℂ) * (1 / (1 - ρ) + 1 / ρ)).re =
      (k : ℝ) * ((s.re - 1 / 2) / ((s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2)) := by
  have h0 : Complex.normSq ρ = 1 / 4 + ρ.im ^ 2 := by
    rw [Complex.normSq_apply, hr]
    ring
  have h1 : Complex.normSq (1 - ρ) = 1 / 4 + ρ.im ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      hr]
    ring
  have hs : Complex.normSq (s - ρ) = (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hr]
    ring
  simp only [one_div, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.add_re,
    Complex.inv_re, Complex.sub_re, Complex.one_re, hr, zero_mul, sub_zero, h0, h1, hs]
  ring

/-- Under RH, the centered real genus term equals the Poisson kernel for
every complex index. Away from zeros its multiplicity vanishes. -/
theorem genus_re_centering_all (hRH : RiemannHypothesis) (s ρ : ℂ) :
    ((analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)).re -
        (1 / 2 : ℝ) * ((analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (1 - ρ) + 1 / ρ)).re =
      (analyticOrderNatAt riemannXi ρ : ℝ) *
        ((s.re - 1 / 2) / ((s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2)) := by
  by_cases hz : riemannXi ρ = 0
  · exact genus_re_centering s ρ _ (xi_zero_re_eq_half_of_riemannHypothesis hRH hz)
  · have ho : analyticOrderNatAt riemannXi ρ = 0 := by
      rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz), ENat.toNat_zero]
    simp only [ho, Nat.cast_zero, zero_mul, Complex.zero_re, mul_zero, sub_zero]

/-- Under RH, the real logarithmic derivative of xi to the right of the
critical line is the convergent multiplicity-weighted Poisson zero sum.
Subtract half the genus expansion at one and use the functional equation to
cancel the remaining center constant. -/
theorem hasSum_logDeriv_poisson (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    HasSum
      (fun ρ : ℂ ↦
        (analyticOrderNatAt riemannXi ρ : ℝ) *
          ((s.re - 1 / 2) / ((s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2)))
      (logDeriv riemannXi s).re := by
  have h1 : (1 / 2 : ℝ) < (1 : ℂ).re := by norm_num only [Complex.one_re]
  have hS := Complex.hasSum_re (summable_genus_terms_of_riemannHypothesis hRH hs).hasSum
  have hO := Complex.hasSum_re (summable_genus_terms_of_riemannHypothesis hRH h1).hasSum
  rw [← centered_logDeriv_eq_genusSum_RH hRH hs] at hS
  rw [← centered_logDeriv_eq_genusSum_RH hRH h1] at hO
  have hh := hS.sub (hO.mul_left (1 / 2 : ℝ))
  have he :
    (logDeriv riemannXi s - logDeriv riemannXi 0).re -
        (1 / 2 : ℝ) * (logDeriv riemannXi 1 - logDeriv riemannXi 0).re =
      (logDeriv riemannXi s).re := by
    rw [logDeriv_riemannXi_one_eq_neg_zero]
    simp only [Complex.sub_re, Complex.neg_re]
    ring
  rw [he] at hh
  simpa only [genus_re_centering_all hRH] using hh

/-- Under RH, the real part of the xi logarithmic derivative is nonnegative
to the right of the critical line. Every term of its convergent Poisson sum
is nonnegative; no finite zero enumeration is used. -/
theorem logDeriv_re_nonneg (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    0 ≤ (logDeriv riemannXi s).re := by
  rw [← (hasSum_logDeriv_poisson hRH hs).tsum_eq]
  exact
    tsum_nonneg
      (fun ρ ↦
        mul_nonneg (Nat.cast_nonneg _)
          (div_nonneg (by linarith only [hs]) (add_nonneg (sq_nonneg _) (sq_nonneg _))))

/-- For positive ordered horizontal offsets, the offset times the Poisson
kernel is nondecreasing. Cross multiplication reduces the comparison to
the nonnegative product `(v² - u²) * w²`. -/
theorem mul_poisson_mono {u v w : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    u * (u / (u ^ 2 + w ^ 2)) ≤ v * (v / (v ^ 2 + w ^ 2)) := by
  have hv : 0 < v := hu.trans_le huv
  have hu2 : 0 < u ^ 2 + w ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hu) (sq_nonneg w)
  have hv2 : 0 < v ^ 2 + w ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hv) (sq_nonneg w)
  have huvs : u ^ 2 ≤ v ^ 2 := by nlinarith only [hu, huv, hv]
  have hm := mul_nonneg (sub_nonneg.mpr huvs) (sq_nonneg w)
  rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ hu2 hv2]
  nlinarith only [hm]

/-- Under RH, at any fixed height, the horizontal offset times the real xi
logarithmic derivative is nondecreasing for positive offsets. Compare the
convergent nonnegative Poisson series term by term. -/
theorem mul_logDeriv_re_mono (hRH : RiemannHypothesis) {u v : ℝ} (t : ℝ) (hu : 0 < u)
    (huv : u ≤ v) :
    u * (logDeriv riemannXi (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
      v * (logDeriv riemannXi (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
  have hv : 0 < v := hu.trans_le huv
  have hs (a : ℝ) (ha : 0 < a) :
    HasSum (fun ρ : ℂ ↦ (analyticOrderNatAt riemannXi ρ : ℝ) * (a / (a ^ 2 + (t - ρ.im) ^ 2)))
      (logDeriv riemannXi (((1 / 2 + a : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
    have h :=
      hasSum_logDeriv_poisson hRH
        (show (1 / 2 : ℝ) < (((1 / 2 + a : ℝ) : ℂ) + (t : ℂ) * Complex.I).re
          by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
          linarith only [ha])
    simpa only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul,
      zero_add, sub_zero, add_zero, add_sub_cancel_left] using h
  have huS := (hs u hu).mul_left u
  have hvS := (hs v hv).mul_left v
  rw [← huS.tsum_eq, ← hvS.tsum_eq]
  apply Summable.tsum_le_tsum _ huS.summable hvS.summable
  intro ρ
  have h :=
    mul_le_mul_of_nonneg_left (mul_poisson_mono (w := t - ρ.im) hu huv)
      (show (0 : ℝ) ≤ (analyticOrderNatAt riemannXi ρ : ℝ) from Nat.cast_nonneg _)
  nlinarith only [h]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
