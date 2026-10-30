/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CenteredHadamard
/-!
# Unconditional inverse-power masses and tails of xi zeros

Remove the regularized denominator using the nonzero value at the origin. The resulting
summable actual-zero weights provide inverse-square mass and quantitative radius tails.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi
/-- For a real exponent and a complex point, assign xi-zero multiplicity divided
by the norm to that exponent at zeros, and zero elsewhere. The indicator retains only
actual zeros. For exponent greater than one this is summable without RH and supplies
finite zero masses and quantitative high-radius tails. -/
noncomputable def inversePowerZeroWeight (p : ℝ) (ρ : ℂ) : ℝ :=
  if riemannXi ρ = 0 then (riemannXiZeroMultiplicity ρ : ℝ) / ‖ρ‖ ^ p else 0
/-- There is a positive radius separating every xi zero from the origin.
Xi is continuous and nonzero at zero, so a sufficiently small ball contains no zero.
This removes the artificial denominator regularization from the order-one power mass. -/
theorem exists_zero_norm_gap : ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℂ, riemannXi ρ = 0 → r ≤ ‖ρ‖ := by
  have hn : ∀ᶠ s : ℂ in nhds 0, riemannXi s ≠ 0 :=
    differentiable_riemannXi.continuous.continuousAt.eventually_ne
      (by rw [riemannXi_zero]; norm_num only)
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨r, hr, fun ρ hz ↦ ?_⟩
  by_contra h
  exact hb (by simpa only [dist_zero_right] using lt_of_not_ge h) hz
/-- For every real exponent and point, the inverse-power xi-zero weight is nonnegative.
Use nonnegative natural multiplicity and real powers. This permits summability comparison
and finite-sum bounds without any choice of zero enumeration. -/
theorem inversePowerZeroWeight_nonneg (p : ℝ) (ρ : ℂ) : 0 ≤ inversePowerZeroWeight p ρ := by
  dsimp only [inversePowerZeroWeight]
  split
  · exact div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  · exact le_rfl
/-- For a positive uniform zero-norm gap and nonnegative exponent, the unregularized
xi-zero weight is bounded by a constant times the regularized order-one weight.
Compare one plus the norm with the norm times one plus the inverse gap.
This transfers unconditional regularized power-mass summability. -/
theorem inversePowerZeroWeight_le_regular {r p : ℝ} (hr : 0 < r) (hp : 0 ≤ p)
    (hgap : ∀ ρ : ℂ, riemannXi ρ = 0 → r ≤ ‖ρ‖) (ρ : ℂ) :
    inversePowerZeroWeight p ρ ≤
      (1 + 1 / r) ^ p * General.regularPowerZeroWeight riemannXi p ρ := by
  dsimp only [inversePowerZeroWeight, General.regularPowerZeroWeight]
  split
  next hz =>
    have hn : 0 < ‖ρ‖ := hr.trans_le (hgap ρ hz)
    have hA : 0 < 1 + 1 / r := by positivity
    have hmul : 1 + ‖ρ‖ ≤ (1 + 1 / r) * ‖ρ‖ := by
      have hdiv := (one_le_div hr).mpr (hgap ρ hz)
      rw [show (1 + 1 / r) * ‖ρ‖ = ‖ρ‖ + ‖ρ‖ / r by ring]
      linarith only [hdiv]
    have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1 + ‖ρ‖) hmul hp
    rw [Real.mul_rpow hA.le hn.le] at hpow
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hn p)
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 + ‖ρ‖) p)).mpr
    have hm := mul_le_mul_of_nonneg_left hpow
      (Nat.cast_nonneg (riemannXiZeroMultiplicity ρ) : (0 : ℝ) ≤ _)
    dsimp only [riemannXiZeroMultiplicity] at hm ⊢
    nlinarith only [hm]
  next hz =>
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _))
/-- For every exponent greater than one, the actual xi-zero multiplicities divided
by the corresponding norm power form a summable family. Use the positive zero-norm gap
and the established order-one regularized mass. This theorem does not assume RH. -/
theorem summable_inversePowerZeroWeight {p : ℝ} (hp : 1 < p) :
    Summable (inversePowerZeroWeight p) := by
  obtain ⟨r, hr, hgap⟩ := exists_zero_norm_gap
  exact Summable.of_nonneg_of_le (inversePowerZeroWeight_nonneg p)
    (inversePowerZeroWeight_le_regular hr (zero_lt_one.trans hp).le hgap)
    ((summable_regularPowerZeroWeight_riemannXi hp).mul_left ((1 + 1 / r) ^ p))
/-- For a finite family of actual xi zeros whose zeta and xi multiplicities agree,
the inverse-norm-square zeta multiplicity sum is at most the full unconditional xi mass.
Rewrite the summands and apply summability. This bounds finite nontrivial zeta ledgers. -/
theorem sum_inverse_square_le_mass (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, RiemannZeta.riemannZetaZeroMultiplicity ρ = riemannXiZeroMultiplicity ρ)
    (hxi : ∀ ρ ∈ S, riemannXi ρ = 0) :
    (∑ ρ ∈ S, (RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ) ≤
      ∑' ρ : ℂ, inversePowerZeroWeight 2 ρ := by
  have heq : (∑ ρ ∈ S, (RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) /
      Complex.normSq ρ) = ∑ ρ ∈ S, inversePowerZeroWeight 2 ρ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [inversePowerZeroWeight, ite_eq_left (hxi ρ hρ), hz ρ hρ,
      Real.rpow_two, Complex.normSq_eq_norm_sq]
  rw [heq]
  exact (summable_inversePowerZeroWeight (by norm_num only : (1 : ℝ) < 2)).sum_le_tsum S
    (fun ρ _ ↦ inversePowerZeroWeight_nonneg 2 ρ)
/-- For exponent at most two, positive cutoff T and a point of norm at least T,
the inverse-square xi weight is at most T to the exponent minus two times its power weight.
Compare the complementary denominator powers. This supplies the high-zero tail decay. -/
theorem inverse_square_le_power_tail {p T : ℝ} (hp : p ≤ 2) (hT : 0 < T)
    {ρ : ℂ} (ht : T ≤ ‖ρ‖) :
    inversePowerZeroWeight 2 ρ ≤ T ^ (p - 2) * inversePowerZeroWeight p ρ := by
  have hn : 0 < ‖ρ‖ := hT.trans_le ht
  have hpow : T ^ (2 - p) ≤ ‖ρ‖ ^ (2 - p) :=
    Real.rpow_le_rpow hT.le ht (sub_nonneg.mpr hp)
  have he : T ^ (p - 2) = (T ^ (2 - p))⁻¹ := by
    rw [show p - 2 = -(2 - p) by ring, Real.rpow_neg hT.le]
  rw [inversePowerZeroWeight, inversePowerZeroWeight, he]
  split
  next hz =>
    rw [← div_eq_inv_mul, div_div]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
      (mul_pos (Real.rpow_pos_of_pos hn p) (Real.rpow_pos_of_pos hT (2 - p)))
    have hm := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hn.le p)
    rw [← Real.rpow_add hn, show p + (2 - p) = 2 by ring] at hm
    exact hm
  next hz => rw [mul_zero]
/-- For exponent strictly between one and two inclusive and a positive radius cutoff,
the finite inverse-square xi mass outside the cutoff is bounded by the cutoff to the
exponent minus two times the full power mass. Sum the pointwise comparison and use
unconditional summability. Exponent three halves gives an inverse-square-root tail. -/
theorem sum_inverse_square_tail_le {p T : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hT : 0 < T) (S : Finset ℂ) (ht : ∀ ρ ∈ S, T ≤ ‖ρ‖) :
    (∑ ρ ∈ S, inversePowerZeroWeight 2 ρ) ≤
      T ^ (p - 2) * ∑' ρ : ℂ, inversePowerZeroWeight p ρ := by
  have hs := Finset.sum_le_sum fun ρ hρ ↦ inverse_square_le_power_tail hp2 hT (ht ρ hρ)
  rw [← Finset.mul_sum] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left
    ((summable_inversePowerZeroWeight hp).sum_le_tsum S
      (fun ρ _ ↦ inversePowerZeroWeight_nonneg p ρ))
    (Real.rpow_nonneg hT.le _))
end PseudoPrime.AnalyticNumberTheory.RiemannXi
