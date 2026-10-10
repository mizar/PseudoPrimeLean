/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMass
public import PseudoPrime.AnalyticNumberTheory.General.EntireHadamard
public import PseudoPrime.AnalyticNumberTheory.General.EntirePowerZeroMass
public import PseudoPrime.AnalyticNumberTheory.General.EntireOrder
public import PseudoPrime.AnalyticNumberTheory.General.ShiftedZeroBounds

/-!
# Centered Hadamard expansion and power mass of the Riemann xi function

The entire xi function supplies the zero contribution to shifted zeta formulas.
Its order-one envelope gives regularized power-mass convergence without RH.
Under RH, critical-line separation gives the shifted mass bounds and centered
logarithmic-derivative expansions used in Mellin inversion.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- For t >= 1, absorb the xi growth envelope's additive constant and shift by four
into a positive multiple of (t+3) log(t+3). Compare the shifted arguments and logarithms.
This puts the existing xi envelope into the standard order-at-most-one criterion. -/
private theorem xi_log_growth_le_standard_envelope {t : ℝ} (ht : 1 ≤ t) :
    xiOrderOneGrowthConstant + 2 * (t + 4) * Real.log (t + 4) ≤
      (|xiOrderOneGrowthConstant| + 9) * ((t + 3) * Real.log (t + 3)) := by
  have ht3 : 0 < t + 3 := by linarith only [ht]
  have hl :=
    Real.log_le_log (show (0 : ℝ) < 2 by norm_num only) (show (2 : ℝ) ≤ t + 3 by linarith only [ht])
  have h2 := Real.log_two_gt_d9
  norm_num only at h2
  have hl0 : 0 ≤ Real.log (t + 3) := by linarith only [hl, h2]
  have hP : 1 ≤ (t + 3) * Real.log (t + 3) := by
    have hm := mul_le_mul_of_nonneg_left hl ht3.le
    nlinarith only [hm, ht, h2]
  have hshift : t + 4 ≤ 2 * (t + 3) := by linarith only [ht]
  have hlog : Real.log (t + 4) ≤ 2 * Real.log (t + 3) := by
    have h := Real.log_le_log (show 0 < t + 4 by linarith only [ht]) hshift
    rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) ht3.ne'] at h
    linarith only [h, hl]
  have hm :=
    mul_le_mul hshift hlog (Real.log_nonneg (show 1 ≤ t + 4 by linarith only [ht]))
      (show 0 ≤ 2 * (t + 3) by linarith only [ht])
  have hC := (le_abs_self xiOrderOneGrowthConstant).trans (le_mul_of_one_le_right (abs_nonneg _) hP)
  nlinarith only [hm, hC, hP]

/-- The entire Riemann xi function has order at most one in the exponential-bound sense.
The existing global xi envelope is O(t log t) in its exponent; absorb its constants and
apply the general logarithmic growth criterion. This supplies arbitrary power-mass
convergence and the centered Hadamard expansion without assuming RH. -/
theorem hasOrderAtMostOne_riemannXi : General.HasOrderAtMostOne riemannXi := by
  apply
    General.hasOrderAtMostOne_of_exp_norm_mul_log_bound riemannXi
      (show 0 < |xiOrderOneGrowthConstant| + 9 by
        linarith only [abs_nonneg xiOrderOneGrowthConstant])
  intro s hs
  exact
    (norm_riemannXi_le_xiOrderOneBound s).trans
      ((xiOrderOneBound_le_exp_orderOne hs).trans
        (Real.exp_le_exp.mpr (xi_log_growth_le_standard_envelope hs)))

/-- For every real p > 1, the xi zero multiplicities divided by (1+norm rho)^p
form a summable family over all complex points. Nonzeros have multiplicity zero.
Apply the order-one growth bound with exponent (1+p)/2 and the general dyadic Jensen
estimate. This gives the three-halves majorant for shifted zero Mellin integration. -/
theorem summable_regularPowerZeroWeight_riemannXi {p : ℝ} (hp : 1 < p) :
    Summable (General.regularPowerZeroWeight riemannXi p) := by
  have h0 : riemannXi 0 ≠ 0 := by
    rw [riemannXi_zero]
    norm_num only
  obtain ⟨C, hC, hg⟩ :=
    General.exists_global_exponential_bound_of_orderAtMostOne differentiable_riemannXi.continuous
      hasOrderAtMostOne_riemannXi (show (1 : ℝ) < (1 + p) / 2 by linarith only [hp])
  exact
    General.summable_regularPowerZeroWeight differentiable_riemannXi h0 hC (by linarith only [hp])
      (zero_lt_one.trans hp) (by linarith only [hp]) hg

/-- A complex zero of the entire xi function, together with the proof that its value is zero.
The subtype records only the zero equation; analytic order supplies multiplicity
in sums. Under RH every such zero has real part one half.
The subtype indexes the centered resolvent and shifted residue sums. -/
abbrev Zero :=
  { ρ : ℂ // riemannXi ρ = 0 }

/-- Under RH, a xi zero stays at norm distance at least one half from every real sigma >= 1.
Its real part is one half, so the real part of the reflected difference bounds its norm.
This gives uniform pole separation for differentiating the centered zero series. -/
theorem norm_zero_sub_real_ge_half_of_riemannHypothesis (hRH : RiemannHypothesis) {σ : ℝ}
    (hσ : 1 ≤ σ) (ρ : Zero) : (1 / 2 : ℝ) ≤ ‖(ρ : ℂ) - (σ : ℂ)‖ := by
  have hh := Complex.re_le_norm ((σ : ℂ) - (ρ : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re,
    riemannXi_zero_re_eq_half_of_riemannHypothesis hRH ρ.property, norm_sub_rev] at hh
  linarith only [hh, hσ]

/-- Under RH, for sigma >= 1 and p > 1, the xi multiplicities divided by
norm(rho-sigma)^p form a summable series over xi zeros. Compare the shifted distance
with 1+norm rho using critical-line separation, then use the regularized power mass.
The cases p=3/2 and p=2 justify Mellin interchange and zero-series differentiation. -/
theorem summable_shifted_power_mass_of_riemannHypothesis (hRH : RiemannHypothesis) {σ : ℝ}
    (hσ : 1 ≤ σ) {p : ℝ} (hp : 1 < p) :
    Summable
      (fun ρ : Zero ↦ (riemannXiZeroMultiplicity (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - (σ : ℂ)‖ ^ p) := by
  have hs := (summable_regularPowerZeroWeight_riemannXi hp).subtype {z : ℂ | riemannXi z = 0}
  change Summable (fun ρ : Zero ↦ General.regularPowerZeroWeight riemannXi p (ρ : ℂ)) at hs
  have hδ := norm_zero_sub_real_ge_half_of_riemannHypothesis hRH hσ
  have hc : ∀ ρ : Zero, 1 + ‖(ρ : ℂ)‖ ≤ (3 + 2 * σ) * ‖(ρ : ℂ) - (σ : ℂ)‖ := by
    intro ρ
    have ht := norm_add_le ((ρ : ℂ) - (σ : ℂ)) (σ : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans hσ)] at ht
    have hm := mul_le_mul_of_nonneg_left (hδ ρ) (by linarith only [hσ] : 0 ≤ 2 * (1 + σ))
    nlinarith only [ht, hm]
  have hcp : ∀ ρ : Zero, (1 + ‖(ρ : ℂ)‖) ^ p ≤ (3 + 2 * σ) ^ p * ‖(ρ : ℂ) - (σ : ℂ)‖ ^ p := by
    intro ρ
    have h :=
      Real.rpow_le_rpow (by linarith only [norm_nonneg (ρ : ℂ)]) (hc ρ) (zero_lt_one.trans hp).le
    rwa [Real.mul_rpow (by linarith only [hσ]) (norm_nonneg _)] at h
  apply
    Summable.of_nonneg_of_le
      (fun ρ ↦ div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)) (fun ρ ↦ ?_)
      (hs.mul_left ((3 + 2 * σ) ^ p))
  change
    (riemannXiZeroMultiplicity (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) - (σ : ℂ)‖ ^ p ≤
      (3 + 2 * σ) ^ p * ((riemannXiZeroMultiplicity (ρ : ℂ) : ℝ) / (1 + ‖(ρ : ℂ)‖) ^ p)
  have hd := Real.rpow_pos_of_pos (by linarith only [hδ ρ]) p
  have he := Real.rpow_pos_of_pos (show 0 < 1 + ‖(ρ : ℂ)‖ by linarith only [norm_nonneg (ρ : ℂ)]) p
  rw [← mul_div_assoc, div_le_div_iff₀ hd he]
  convert
    mul_le_mul_of_nonneg_left (hcp ρ)
      (Nat.cast_nonneg (riemannXiZeroMultiplicity (ρ : ℂ)) : (0 : ℝ) ≤ _) using
    1
  ring

/-- Under RH, the inverse-square xi zero mass is summable on the zero subtype.
Restrict the existing all-point mass and identify the complex norm square.
This is the absolute majorant for the genus-one series. -/
theorem summable_inverse_square_mass_of_riemannHypothesis (hRH : RiemannHypothesis) :
    Summable (fun ρ : Zero ↦ (riemannXiZeroMultiplicity (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
  have h :=
    (summable_riemannXiZeroMultiplicityInvNormSq_of_riemannHypothesis hRH).subtype
      {z : ℂ | riemannXi z = 0}
  change
    Summable
      (fun ρ : Zero ↦
        if riemannXi (ρ : ℂ) = 0 then
          (riemannXiZeroMultiplicity (ρ : ℂ) : ℝ) / Complex.normSq (ρ : ℂ)
        else 0) at h
  exact h.congr (fun ρ ↦ by rw [ite_eq_left ρ.property, Complex.normSq_eq_norm_sq])

/-- Under RH and Re s > 1/2, the multiplicity-weighted xi genus-one series converges
absolutely. Bound each term by the inverse-square zero mass, then extend from
zeros to all complex points, where nonzero values have analytic order zero. -/
theorem summable_genus_terms_of_riemannHypothesis (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) := by
  have hsub :
    Summable
      (fun ρ : Zero ↦
        (analyticOrderNatAt riemannXi (ρ : ℂ) : ℂ) * (1 / (s - (ρ : ℂ)) + 1 / (ρ : ℂ))) := by
    apply
      Summable.of_norm_bounded
        ((summable_inverse_square_mass_of_riemannHypothesis hRH).mul_left
          (‖s‖ * (1 + ‖s‖ / (s.re - 1 / 2))))
    intro ρ
    rw [norm_mul, norm_natCast]
    have h :=
      mul_le_mul_of_nonneg_left
        (General.norm_genusTerm_le_inverseSquare
          (riemannXi_zero_re_eq_half_of_riemannHypothesis hRH ρ.property) hs)
        (Nat.cast_nonneg (analyticOrderNatAt riemannXi (ρ : ℂ)) : (0 : ℝ) ≤ _)
    exact
      h.trans_eq
        (by
          unfold riemannXiZeroMultiplicity; ring)
  apply
    (Subtype.val_injective.summable_iff (f := fun ρ : ℂ ↦
          (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) ?_).mp
      hsub
  intro ρ hρ
  have hn : riemannXi ρ ≠ 0 := fun hz ↦ hρ ⟨⟨ρ, hz⟩, rfl⟩
  have ho : analyticOrderNatAt riemannXi ρ = 0 := by
    rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hn), ENat.toNat_zero]
  rw [ho, Nat.cast_zero, zero_mul]

/-- Under RH and Re s > 1/2, the xi logarithmic derivative centered at zero equals
the genus-one zero sum. The order-one bound and absolute convergence discharge
the general entire Hadamard theorem; xi(0)=1/2 fixes the nonzero center. -/
theorem centered_logDeriv_eq_genusSum_of_riemannHypothesis (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    logDeriv riemannXi s - logDeriv riemannXi 0 =
      ∑' ρ : ℂ, (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (s - ρ) + 1 / ρ) := by
  have h0 : riemannXi 0 ≠ 0 := by
    rw [riemannXi_zero]; norm_num only
  have hne : riemannXi s ≠ 0 := fun hz ↦
    hs.ne' (riemannXi_zero_re_eq_half_of_riemannHypothesis hRH hz)
  obtain ⟨C, hC, hg⟩ :=
    General.exists_global_exponential_bound_of_orderAtMostOne differentiable_riemannXi.continuous
      hasOrderAtMostOne_riemannXi (show (1 : ℝ) < 3 / 2 by norm_num only)
  exact
    General.centered_logDeriv_eq_genusSum differentiable_riemannXi h0 hC
      (show (0 : ℝ) ≤ 3 / 2 by norm_num only) (show (3 / 2 : ℝ) < 2 by norm_num only) hg hne
      (summable_genus_terms_of_riemannHypothesis hRH hs)

/-- Under RH, subtracting xi logarithmic derivatives at two points with real part
above one half gives the difference of their zero resolvents. Subtract the two
convergent genus-one expansions to cancel the center and reciprocal-zero terms.
This identity supplies the centered resolvent for shifted Mellin inversion. -/
theorem logDeriv_sub_eq_zeroSeries_of_riemannHypothesis (hRH : RiemannHypothesis) {s t : ℂ}
    (hs : 1 / 2 < s.re) (ht : 1 / 2 < t.re) :
    logDeriv riemannXi s - logDeriv riemannXi t =
      ∑' ρ : ℂ, (analyticOrderNatAt riemannXi ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ)) := by
  have he :
    logDeriv riemannXi s - logDeriv riemannXi t =
      (logDeriv riemannXi s - logDeriv riemannXi 0) -
        (logDeriv riemannXi t - logDeriv riemannXi 0) := by
    ring
  rw [he, centered_logDeriv_eq_genusSum_of_riemannHypothesis hRH hs,
    centered_logDeriv_eq_genusSum_of_riemannHypothesis hRH ht, ←
    (summable_genus_terms_of_riemannHypothesis hRH hs).tsum_sub
      (summable_genus_terms_of_riemannHypothesis hRH ht)]
  exact tsum_congr (fun ρ ↦ by ring)

end PseudoPrime.AnalyticNumberTheory.RiemannXi
