/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.AnalyticConductor

/-!
# Quadratic height-weighted zero mass

Reflected resolvents control both nearby and distant zeros of a general
entire regularized completion, without a Riemann hypothesis.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- Every critical-strip location contributes at least 2/(9+(T-Im rho)^2)
to the reflected resolvent pair. The right Poisson fraction has this lower
bound and the left contribution is nonpositive. This controls distant zeros
as well as the unit height window. -/
theorem stripResolventPair_lower_global {T : ℝ} {ρ : ℂ} (hlo : 0 ≤ ρ.re) (hhi : ρ.re ≤ 1) :
    (2 : ℝ) / (9 + (T - ρ.im) ^ 2) ≤ stripResolventPair T ρ := by
  have hp : 0 < (3 - ρ.re) ^ 2 + (T - ρ.im) ^ 2 := by nlinarith only [hhi, sq_nonneg (T - ρ.im)]
  have hq : 0 < 9 + (T - ρ.im) ^ 2 := by nlinarith only [sq_nonneg (T - ρ.im)]
  have hl : (2 : ℝ) / (9 + (T - ρ.im) ^ 2) ≤ (1 / (((3 : ℝ) : ℂ) + T * Complex.I - ρ)).re := by
    rw [resolvent_re, div_le_div_iff₀ hq hp]
    nlinarith only [hlo, hhi, sq_nonneg ρ.re, mul_nonneg hlo (sq_nonneg (T - ρ.im))]
  have hn := strip_resolvent_re_nonpos (a := -2) (T := T) (by norm_num only) hlo
  rw [stripResolventPair, Complex.sub_re]
  linarith only [hl, hn]

/-- For an entire function of subquadratic growth with critical-strip zeros,
a conjugate functional equation, and nonzero values at zero and 3+iT,
the multiplicity-weighted reciprocal quadratic height profile is summable
and bounded by Re(logDeriv F(3+iT)). Compare each term with half the reflected
resolvent mass and use its exact sum. This supplies an absolute majorant
for distant-zero resolvent differences in the explicit formula. -/
theorem summable_poissonZeroMass_and_bound {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (hstrip : ∀ ρ, F ρ = 0 → 0 ≤ ρ.re ∧ ρ.re ≤ 1) {C r : ℝ} (hC : 0 < C) (hr0 : 0 ≤ r) (hr2 : r < 2)
    (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r)) (T : ℝ)
    (hs : F (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℝ) / (9 + (T - ρ.im) ^ 2)) ∧
      (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℝ) / (9 + (T - ρ.im) ^ 2)) ≤
        (logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)).re := by
  have hn : ∀ ρ : ℂ, 0 ≤ (analyticOrderNatAt F ρ : ℝ) / (9 + (T - ρ.im) ^ 2) := fun ρ ↦
    div_nonneg (Nat.cast_nonneg _) (by nlinarith only [sq_nonneg (T - ρ.im)])
  have hb :
    ∀ ρ : ℂ,
      (analyticOrderNatAt F ρ : ℝ) / (9 + (T - ρ.im) ^ 2) ≤
        (1 / 2 : ℝ) * ((analyticOrderNatAt F ρ : ℝ) * stripResolventPair T ρ) := by
    intro ρ
    by_cases hz : F ρ = 0
    · have hl :=
        mul_le_mul_of_nonneg_left
          (stripResolventPair_lower_global (T := T) (hstrip ρ hz).1 (hstrip ρ hz).2)
          (Nat.cast_nonneg (analyticOrderNatAt F ρ) : (0 : ℝ) ≤ _)
      rw [← mul_div_assoc, mul_comm _ (2 : ℝ), mul_div_assoc] at hl
      linarith only [hl]
    · have ho : analyticOrderNatAt F ρ = 0 := by
        rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz), ENat.toNat_zero]
      simp only [ho, Nat.cast_zero, zero_div, zero_mul, mul_zero, le_refl]
  have hm := (summable_stripResolventPair hF h0 hC hr0 hr2 hg T).mul_left (1 / 2 : ℝ)
  have hz := hm.of_nonneg_of_le hn hb
  refine ⟨hz, ?_⟩
  have hh := hz.tsum_le_tsum hb hm
  rw [tsum_mul_left, tsum_stripResolventPair_eq hε hfe hF h0 hC hr0 hr2 hg T hs] at hh
  nlinarith only [hh]

/-- Entire order-one completion data, its functional equation, and right
half-plane nonvanishing imply the summability and logarithmic derivative
bound for the quadratic height-weighted zero mass. Order one supplies the
subquadratic growth bound and the functional equation locates the zeros.
No Riemann hypothesis or separate convergence premise is required. -/
theorem poissonZeroMass_bound_of_orderAtMostOne {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (T : ℝ) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℝ) / (9 + (T - ρ.im) ^ 2)) ∧
      (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℝ) / (9 + (T - ρ.im) ^ 2)) ≤
        (logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)).re := by
  obtain ⟨C, hC, hg⟩ :=
    exists_global_exponential_bound_of_orderAtMostOne hF.continuous horder (r := 3 / 2)
      (by norm_num only)
  have hs : F (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0 := by
    apply hright
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero]
    norm_num only
  exact
    summable_poissonZeroMass_and_bound hε hfe hF h0
      (fun ρ hz ↦ zero_re_mem_Icc_of_functionalEquation hε hfe hright hz) hC
      (by norm_num only : (0 : ℝ) ≤ 3 / 2) (by norm_num only : (3 / 2 : ℝ) < 2) hg T hs

end PseudoPrime.AnalyticNumberTheory.General
