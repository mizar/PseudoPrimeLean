/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaActualRamifiedBudget
public import PseudoPrime.Analysis.GammaLargePrimeCosts

/-! # Finite support of the variable ramified dual excess -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Variable dual parameter 5/(4 sqrt x), used at positive scales. Its
order is x^(-1/2), so the term mu log n remains bounded at the prescribed
quadratic scale. This parameter replaces an endpoint-only constant choice. -/
noncomputable def gammaRamifiedDualParameter (x : ℝ) : ℝ :=
  5 / (4 * Real.sqrt x)

/-- For p>1, the signed full Euler cost is bounded by the positive
coefficient mass divided by p-1. Compare all positive-power series with
the reciprocal geometric series and normalize its denominator. This
controls the large-prime dual excess without discarding a tail error. -/
theorem gamma_prime_euler_cost_le_positive_reciprocal {p : ℝ} (hp : 1 < p) :
    gammaPrimeEulerCost p ≤ (79977719 / 25000000 : ℝ) / (p - 1) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hs :=
    (summable_gamma_euler_positive_powers hp (zero_lt_one : (0 : ℝ) < 1)).mul_left
      (79977719 / 25000000 : ℝ)
  have hle :=
    (summable_gammaResolventEulerWeight_powers hp).tsum_le_tsum
      (fun k ↦ by
        simpa only [Real.rpow_neg_one] using
          gamma_euler_weight_le_positive_reciprocal (one_le_pow₀ hp.le : (1 : ℝ) ≤ p ^ (k + 1)))
      hs
  rw [tsum_gammaResolventEulerWeight_powers_eq_cost hp, tsum_mul_left,
    tsum_gamma_euler_positive_powers hp (zero_lt_one : (0 : ℝ) < 1)] at hle
  have hr : p ^ (-1 : ℝ) / (1 - p ^ (-1 : ℝ)) = 1 / (p - 1) := by
    have he : 1 - p⁻¹ = p⁻¹ * (p - 1) := by rw [mul_sub, inv_mul_cancel₀ hp0, mul_one]
    rw [Real.rpow_neg_one, he, mul_comm p⁻¹ (p - 1)]
    simpa only [one_mul] using mul_div_mul_right (1 : ℝ) (p - 1) (inv_ne_zero hp0)
  rw [hr] at hle
  simpa only [mul_one_div] using hle

/-- If the second positive power lies beyond the cutoff, the natural-floor
ramp count is at most one. Logarithmic monotonicity gives a quotient below
two, and the floor then has only the values zero or one. This controls the
ramp contribution of the large-prime dual excess. -/
theorem gamma_ramp_count_le_one_of_square_above {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x)
    (hcut : (99 / 40 : ℝ) * x < (p : ℝ) ^ 2) : gammaRampPowerCount p x ≤ 1 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlp := Real.log_pos hpR
  have hcut0 : (1 : ℝ) ≤ (99 / 40 : ℝ) * x := by nlinarith only [hx]
  have hlog := Real.log_lt_log (zero_lt_one.trans_le hcut0) hcut
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hquot := (div_lt_iff₀ hlp).mpr hlog
  have hfloor := (Nat.floor_lt (div_nonneg (Real.log_nonneg hcut0) hlp.le)).mpr hquot
  dsimp only [gammaRampPowerCount]
  exact_mod_cast (Nat.le_of_lt_succ hfloor : ⌊Real.log ((99 / 40 : ℝ) * x) / Real.log p⌋₊ ≤ 1)

/-- For x>=1 and p>1+4 B_+ sqrt x, the combined ramified allowance is
strictly below 5/(4 sqrt x). The same threshold places p^2 beyond the
cutoff. The reciprocal Euler bound contributes less than 1/(4 sqrt x)
and the actual ramp count contributes at most 1/sqrt x. -/
theorem gamma_ramified_cost_lt_variable_dual {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x)
    (hpbig : 1 + (79977719 / 6250000 : ℝ) * Real.sqrt x < p) :
    gammaRamifiedCombinedCost p x < gammaRamifiedDualParameter x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ht0 := Real.sqrt_pos.mpr hx0
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hpp : (79977719 / 6250000 : ℝ) * Real.sqrt x < p := by linarith only [hpbig]
  have hs := (sq_lt_sq₀ (mul_nonneg (by norm_num only) ht0.le) (zero_lt_one.trans hpR).le).mpr hpp
  have hcut : (99 / 40 : ℝ) * x < (p : ℝ) ^ 2 := by nlinarith only [hs, Real.sq_sqrt hx0.le, hx]
  have he := gamma_prime_euler_cost_le_positive_reciprocal hpR
  have hr := gamma_ramp_count_le_one_of_square_above hp hx hcut
  have hd : (79977719 / 25000000 : ℝ) / ((p : ℝ) - 1) < 1 / (4 * Real.sqrt x) := by
    apply (div_lt_div_iff₀ (sub_pos.mpr hpR) (mul_pos (by norm_num only) ht0)).mpr
    nlinarith only [hpbig]
  have hbound := add_lt_add_of_lt_of_le (he.trans_lt hd) (div_le_div_of_nonneg_right hr ht0.le)
  have heq : (1 : ℝ) / (4 * Real.sqrt x) + 1 / Real.sqrt x = 5 / (4 * Real.sqrt x) := by
    rw [← div_div (1 : ℝ) 4 (Real.sqrt x), ← add_div]
    norm_num only
    rw [div_div]
  simpa only [gammaRamifiedCombinedCost, gammaRamifiedDualParameter, heq] using hbound

/-- Beyond 1+4 B_+ sqrt x, the positive part of the variable dual excess
is exactly zero. The strict combined-cost bound makes the subtraction
negative. This justifies replacing the infinite prime tail by a finite
sum in numerical certificates at any positive scale x>=1. -/
theorem gamma_ramified_variable_dual_excess_eq_zero {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x)
    (hpbig : 1 + (79977719 / 6250000 : ℝ) * Real.sqrt x < p) :
    max (gammaRamifiedCombinedCost p x - gammaRamifiedDualParameter x) 0 = 0 := by
  exact max_eq_right (sub_nonpos.mpr (gamma_ramified_cost_lt_variable_dual hp hx hpbig).le)

/-- The variable dual parameter is nonnegative at every real scale.
The square root and its factor four are nonnegative, and the numerator
is positive. This supplies the sign premise of the common dual budget. -/
theorem gamma_ramified_dual_parameter_nonneg (x : ℝ) : 0 ≤ gammaRamifiedDualParameter x := by
  exact
    div_nonneg (by norm_num only : (0 : ℝ) ≤ 5)
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (Real.sqrt_nonneg x))

/-- Finite set of odd primes at most 1+4 B_+ sqrt x. The natural floor
and prime filter make the set finite at every scale. All odd-prime
positive dual excess outside this set is zero by the proved tail bound. -/
noncomputable def gammaRamifiedDualPrimeSet (x : ℝ) : Finset ℕ :=
  (Finset.Icc 3 ⌊1 + (79977719 / 6250000 : ℝ) * Real.sqrt x⌋₊).filter Nat.Prime

/-- At x>=1, the weighted positive dual excess over any finite set of
odd primes is bounded by the finite scale-dependent prime set. Every
term outside it vanishes exactly; the remaining terms are nonnegative.
This gives a finite numerical target independent of the input factors. -/
theorem gamma_ramified_variable_excess_le_finite (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime ∧ 3 ≤ p)
    {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ R, Real.log p * max (gammaRamifiedCombinedCost p x - gammaRamifiedDualParameter x) 0) ≤
      ∑ p ∈ gammaRamifiedDualPrimeSet x,
        Real.log p * max (gammaRamifiedCombinedCost p x - gammaRamifiedDualParameter x) 0 := by
  let F : ℕ → ℝ := fun p ↦
    Real.log p * max (gammaRamifiedCombinedCost p x - gammaRamifiedDualParameter x) 0
  have hz (p : ℕ) (hp : p ∈ R) (hnot : p ∉ gammaRamifiedDualPrimeSet x) : F p = 0 := by
    have hpdata := hR p hp
    have hfloor : ⌊1 + (79977719 / 6250000 : ℝ) * Real.sqrt x⌋₊ < p := by
      apply lt_of_not_ge
      intro hle
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpdata.2, hle⟩, hpdata.1⟩)
    have hpbig :=
      (Nat.floor_lt
            (by nlinarith only [Real.sqrt_nonneg x] :
              (0 : ℝ) ≤ 1 + (79977719 / 6250000 : ℝ) * Real.sqrt x)).mp
        hfloor
    dsimp only [F]
    rw [gamma_ramified_variable_dual_excess_eq_zero hpdata.1.one_lt hx hpbig, mul_zero]
  have he : (∑ p ∈ R ∩ gammaRamifiedDualPrimeSet x, F p) = ∑ p ∈ R, F p :=
    Finset.sum_subset Finset.inter_subset_left
      (fun p hp hnot ↦ hz p hp (fun hq ↦ hnot (Finset.mem_inter.mpr ⟨hp, hq⟩)))
  change (∑ p ∈ R, F p) ≤ ∑ p ∈ gammaRamifiedDualPrimeSet x, F p
  rw [← he]
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
  intro p hp hnot
  exact
    mul_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
      (le_max_right _ _)

/-- For an odd input at x>=1, all selected zero-valued local losses
obey one variable dual budget plus a finite odd-prime excess sum.
The arithmetic log n budget is used once, and the support theorem
removes dependence of the numerical excess bound on the input factors. -/
theorem gamma_actual_odd_ramified_cost_le_finite_dual {n f : ℕ} (hn : Odd n) (R : Finset ℕ)
    (hR : R ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ R, χ p = 0)
    (K : ℕ → Finset ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ R, gammaActualPrimeLocalCost χ p (K p) x) ≤
      gammaRamifiedDualParameter x * Real.log n +
        ∑ p ∈ gammaRamifiedDualPrimeSet x,
          Real.log p * max (gammaRamifiedCombinedCost p x - gammaRamifiedDualParameter x) 0 := by
  have hr :=
    gamma_actual_ramified_joint_cost_le_input_dual_cap hn.pos R hR χ hχ K (zero_lt_one.trans_le hx)
      (gamma_ramified_dual_parameter_nonneg x)
  have hprime (p : ℕ) (hp : p ∈ R) : p.Prime ∧ 3 ≤ p := by
    have h := Nat.prime_of_mem_primeFactors (hR hp)
    have hpne : p ≠ 2 := by
      intro he
      exact hn.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors (hR hp))
    exact ⟨h, Nat.succ_le_iff.mpr (lt_of_le_of_ne h.two_le (Ne.symm hpne))⟩
  exact hr.trans (add_le_add le_rfl (gamma_ramified_variable_excess_le_finite R hprime hx))

/-- An odd prime outside the finite dual prime set exceeds its real
cutoff. Membership would otherwise follow from the natural-floor bound.
This identifies the strict tail condition for both signed and count costs. -/
theorem gamma_odd_prime_gt_dual_cutoff_of_not_mem {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (x : ℝ)
    (hnot : p ∉ gammaRamifiedDualPrimeSet x) : 1 + (79977719 / 6250000 : ℝ) * Real.sqrt x < p := by
  have hfloor : ⌊1 + (79977719 / 6250000 : ℝ) * Real.sqrt x⌋₊ < p := by
    apply lt_of_not_ge
    intro hle
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, hle⟩, hp⟩)
  exact
    (Nat.floor_lt
          (by nlinarith only [Real.sqrt_nonneg x] :
            (0 : ℝ) ≤ 1 + (79977719 / 6250000 : ℝ) * Real.sqrt x)).mp
      hfloor

/-- The signed ramified dual excess vanishes beyond the same finite
cutoff as the coarse count allowance. Compare the signed cost with the
count cost only in the tail. No precision is lost in the finite sum. -/
theorem gamma_ramified_signed_variable_excess_eq_zero {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x)
    (hpbig : 1 + (79977719 / 6250000 : ℝ) * Real.sqrt x < p) :
    max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedDualParameter x) 0 = 0 := by
  exact
    max_eq_right
      (sub_nonpos.mpr
        ((gamma_ramified_signed_cost_le_combined hp (zero_lt_one.trans_le hx)).trans
          (gamma_ramified_cost_lt_variable_dual hp hx hpbig).le))

/-- A weighted finite sum supported in Q is at most the sum over Q when
all Q terms are nonnegative. Intersect the input set with Q and remove
the zero terms outside Q. This supplies the exact finite-support transfer
without assuming that every input prime itself lies below the cutoff. -/
theorem gamma_supported_sum_le_finite (R Q : Finset ℕ) (F : ℕ → ℝ)
    (hzero : ∀ p ∈ R, p ∉ Q → F p = 0) (hpos : ∀ p ∈ Q, 0 ≤ F p) :
    (∑ p ∈ R, F p) ≤ ∑ p ∈ Q, F p := by
  have he : (∑ p ∈ R ∩ Q, F p) = ∑ p ∈ R, F p :=
    Finset.sum_subset Finset.inter_subset_left
      (fun p hp hnot ↦ hzero p hp (fun hq ↦ hnot (Finset.mem_inter.mpr ⟨hp, hq⟩)))
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun p hp hnot ↦ hpos p hp)

/-- The signed positive dual excess of any finite set of odd primes is
bounded by the finite scale-dependent prime sum. The actual signed
combined cost remains in every retained term; the tail vanishes exactly.
This is the finite quantity to certify numerically for the refined bound. -/
theorem gamma_ramified_signed_variable_excess_le_finite (R : Finset ℕ)
    (hR : ∀ p ∈ R, p.Prime ∧ 3 ≤ p) {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ R,
        Real.log p * max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedDualParameter x) 0) ≤
      ∑ p ∈ gammaRamifiedDualPrimeSet x,
        Real.log p *
          max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedDualParameter x) 0 := by
  apply gamma_supported_sum_le_finite
  · intro p hp hnot
    rw [gamma_ramified_signed_variable_excess_eq_zero (hR p hp).1.one_lt hx
        (gamma_odd_prime_gt_dual_cutoff_of_not_mem (hR p hp).1 (hR p hp).2 x hnot),
      mul_zero]
  · intro p hp
    exact
      mul_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
        (le_max_right _ _)

/-- For an odd input, actual selected ramified losses are bounded by
the variable log n budget and the finite signed prime excess. The tail
is removed exactly and the finite ramp contributions retain their signs.
This gives the precise factor-independent numerical interface at x>=1. -/
theorem gamma_actual_odd_ramified_signed_cost_le_finite_dual {n f : ℕ} (hn : Odd n) (R : Finset ℕ)
    (hR : R ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ R, χ p = 0)
    (K : ℕ → Finset ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ R, gammaActualPrimeLocalCost χ p (K p) x) ≤
      gammaRamifiedDualParameter x * Real.log n +
        ∑ p ∈ gammaRamifiedDualPrimeSet x,
          Real.log p *
            max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedDualParameter x) 0 := by
  have hr :=
    gamma_actual_ramified_signed_cost_le_input_dual_cap hn.pos R hR χ hχ K x
      (gamma_ramified_dual_parameter_nonneg x)
  have hprime (p : ℕ) (hp : p ∈ R) : p.Prime ∧ 3 ≤ p := by
    have h := Nat.prime_of_mem_primeFactors (hR hp)
    have hpne : p ≠ 2 := by
      intro he
      exact hn.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors (hR hp))
    exact ⟨h, Nat.succ_le_iff.mpr (lt_of_le_of_ne h.two_le (Ne.symm hpne))⟩
  exact hr.trans (add_le_add le_rfl (gamma_ramified_signed_variable_excess_le_finite R hprime hx))

end PseudoPrime.Analysis
