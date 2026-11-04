/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighPrimeCount
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighLog

/-! # Prime supply at large square radii -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, square radii at least `5000` have a Chebyshev lower bound of `99 / 100`.
Apply the relative-width bound at `1 / 200` and compare its error with the quadratic margin.
This provides the prime supply needed by the improved Miller–Rabin counting bounds. -/
theorem high_square_psi_lower_99 (hRH : RiemannHypothesis) {b : ℝ} (hb : 5000 ≤ b) :
    (99 / 100 : ℝ) * b ^ 2 ≤ Chebyshev.psi (b ^ 2) := by
  have hb0 : 0 ≤ b := by linarith only [hb]
  have hs : Real.sqrt (b ^ 2) = b := Real.sqrt_sq_eq_abs b |>.trans (abs_of_nonneg hb0)
  have hpsi :=
    LLS.psi_lower_relative_log_shift hRH (h := (1 / 200 : ℝ)) (by norm_num only) (by norm_num only)
      (sq_nonneg b)
  rw [hs] at hpsi
  have hprod : 0 ≤ (b - 5000) * ((b + 5000) / 200 - 20) := by
    apply mul_nonneg
    · linarith only [hb]
    · linarith only [hb]
  linarith only [hpsi, hprod]

/-- Under RH, a count with logarithmic cost at most `99 / 100` of the square radius is bounded
by the number of primes at that radius for `b ≥ 5000`. Combine the Chebyshev lower bound with
the unconditional psi-to-prime-count inequality. -/
theorem high_square_prime_count_99 (hRH : RiemannHypothesis) {b M : ℕ} (hb : 5000 ≤ b)
    (hM : (M : ℝ) * Real.log (b ^ 2 : ℕ) ≤ (99 / 100 : ℝ) * (b : ℝ) ^ 2) :
    M ≤ (b ^ 2).primeCounting := by
  have hB : 1 < b ^ 2 := by
    have hb2 : 2 ≤ b := by linarith only [hb]
    nlinarith only [hb2]
  have hpsi := high_square_psi_lower_99 hRH (b := (b : ℝ)) (Nat.cast_le.mpr hb)
  norm_num only [Nat.cast_ofNat] at hpsi
  rw [← Nat.cast_pow] at hpsi hM
  have hl := hM.trans (hpsi.trans (Chebyshev.psi_le_primeCounting_mul_log (b ^ 2)))
  have hp : 0 < Real.log (b ^ 2 : ℕ) := Real.log_pos (Nat.one_lt_cast.mpr hB)
  exact Nat.cast_le.mp ((mul_le_mul_iff_left₀ hp).mp hl)

/-- Under RH, the floor of `99 * b ^ 2 / (100 * log (b ^ 2))` bounds from below the number of
primes up to `b ^ 2` for `b ≥ 5000`. The logarithm is positive and the floor is at most its
argument, so the preceding prime-count bound applies to this counting parameter. -/
theorem high_square_floor_prime_count_99 (hRH : RiemannHypothesis) {b : ℕ} (hb : 5000 ≤ b) :
    ⌊((99 / 100 : ℝ) * (b : ℝ) ^ 2) / Real.log (b ^ 2 : ℕ)⌋₊ ≤ (b ^ 2).primeCounting := by
  have hB : 1 < b ^ 2 := by
    have hb2 : 2 ≤ b := by linarith only [hb]
    nlinarith only [hb2]
  have hu : 0 < Real.log (b ^ 2 : ℕ) := Real.log_pos (Nat.one_lt_cast.mpr hB)
  apply high_square_prime_count_99 hRH hb
  have hx : 0 ≤ ((99 / 100 : ℝ) * (b : ℝ) ^ 2) / Real.log (b ^ 2 : ℕ) :=
    div_nonneg (mul_nonneg (by norm_num only) (sq_nonneg _)) hu.le
  have hf := Nat.floor_le hx
  have hm := mul_le_mul_of_nonneg_right hf hu.le
  rw [div_mul_cancel₀ _ hu.ne'] at hm
  exact hm

/-- If `L ≥ 70000` and `α ≥ 647 / 1000`, the selected floor radius `⌊α * L⌋₊` is at least
`5000`. Compare the product with its lower endpoint and use the natural-floor order criterion.
This verifies the size hypothesis for the improved prime supply. -/
theorem high_floor_radius_ge_5000 {L α : ℝ} (hL : 70000 ≤ L) (hα : (647 / 1000 : ℝ) ≤ α) :
    5000 ≤ ⌊α * L⌋₊ := by
  have hα0 : 0 ≤ α := by linarith only [hα]
  have hL0 : 0 ≤ L := by linarith only [hL]
  apply (Nat.le_floor_iff (mul_nonneg hα0 hL0)).mpr
  norm_num only [Nat.cast_ofNat]
  have hprod : 0 ≤ (α - 647 / 1000) * (L - 70000) :=
    mul_nonneg (by linarith only [hα]) (by linarith only [hL])
  nlinarith only [hL, hα, hprod]

/-- Under RH, the `99 / 100` prime-count parameter is bounded by the number of primes up to the
square of the selected radius when `L ≥ 70000` and `α ≥ 647 / 1000`. The radius lower bound
allows the uniform square-radius estimate to be used by the improved counting construction. -/
theorem high_floor_radius_prime_count_99 (hRH : RiemannHypothesis) {L α : ℝ} (hL : 70000 ≤ L)
    (hα : (647 / 1000 : ℝ) ≤ α) :
    ⌊((99 / 100 : ℝ) * (⌊α * L⌋₊ : ℝ) ^ 2) / Real.log ((⌊α * L⌋₊ : ℕ) ^ 2)⌋₊ ≤
      ((⌊α * L⌋₊ : ℕ) ^ 2).primeCounting := by
  simpa only [Nat.cast_pow] using
    high_square_floor_prime_count_99 hRH (high_floor_radius_ge_5000 hL hα)

/-- At `L ≥ 70000`, the floor and ceiling estimates for the `99 / 100` prime supply imply that
the paired binomial base exceeds `197 * b / 100`. The bounds on `α`, `u`, and the floor radius
absorb rounding losses. This is the scalar ratio needed for the improved product count. -/
theorem high_paired_ratio_99 {L α b u : ℝ} {M k : ℕ} (hL : 70000 ≤ L) (hα : (647 / 1000 : ℝ) ≤ α)
    (hb : α * L - 1 ≤ b) (hu0 : 0 < u) (hu : u ≤ L / 2000) (hkM : k ≤ M)
    (hM : ((99 / 100 : ℝ) * b ^ 2) / u < (M : ℝ) + 1) (hk : (k : ℝ) < α * L / u) :
    (197 / 100 : ℝ) * b < 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1) := by
  have hαL : (647 / 1000 : ℝ) * L ≤ α * L := mul_le_mul_of_nonneg_right hα (by linarith only [hL])
  have hb0 : 0 < b := by linarith only [hL, hαL, hb]
  have hpart : (197 / 100 : ℝ) * (α * L + u) < (99 / 50 : ℝ) * b - 4 := by
    linarith only [hL, hαL, hb, hu]
  have hmul := mul_lt_mul_of_pos_left hpart hb0
  have hbound : 2 * (α * L) ≤ 4 * b := by linarith only [hL, hαL, hb]
  have hbase : (197 / 100 : ℝ) * b * (α * L + u) < 2 * ((99 / 100 : ℝ) * b ^ 2 - α * L) := by
    nlinarith only [hmul, hbound]
  have hmk : ((M + 1 - k : ℕ) : ℝ) = (M : ℝ) + 1 - k := by
    rw [Nat.cast_sub (hkM.trans (Nat.le_succ M)), Nat.cast_succ]
  have hN : ((99 / 100 : ℝ) * b ^ 2 - α * L) < ((M + 1 - k : ℕ) : ℝ) * u := by
    have hm := (div_lt_iff₀ hu0).mp hM
    have hkk := (lt_div_iff₀ hu0).mp hk
    nlinarith only [hm, hkk, hmk]
  have hK : ((k : ℝ) + 1) * u < α * L + u := by
    have hkk := (lt_div_iff₀ hu0).mp hk
    linarith only [hkk]
  have hleft := mul_lt_mul_of_pos_left hK (mul_pos (by norm_num only : (0 : ℝ) < 197 / 100) hb0)
  have hright := mul_lt_mul_of_pos_left hN (show (0 : ℝ) < 2 by norm_num only)
  have hden : 0 < (k : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) (by norm_num only)
  apply (lt_div_iff₀ hden).2
  have hv : (197 / 100 : ℝ) * b * ((k : ℝ) + 1) * u < (2 * ((M + 1 - k : ℕ) : ℝ)) * u := by
    nlinarith only [hleft, hbase, hright]
  exact lt_of_mul_lt_mul_right hv hu0.le

/-- The logarithm of `197 / 100` exceeds `339 / 500`. A rational interval certificate supplies
the constant used in the paired-prime counting budget without numerical approximation. -/
theorem log_paired_base_197 : (339 / 500 : ℝ) ≤ Real.log (197 / 100 : ℝ) := by
  have hc : Analysis.rationalLogIntervalCheck (197 / 100) 1 12 (339 / 500) 1 = true := by
    decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- The `99 / 100` supply ratio yields a paired binomial count greater than `exp T` whenever the
corresponding logarithmic budget exceeds `T`. The comparison retains the rounding hypotheses
and feeds the existing prime-product counting interface. -/
theorem exp_lt_choose_of_supply_99 {L α b u T : ℝ} {M k : ℕ} (hL : 70000 ≤ L)
    (hα : (647 / 1000 : ℝ) ≤ α) (hb : α * L - 1 ≤ b) (hu0 : 0 < u) (hu : u ≤ L / 2000) (hkM : k ≤ M)
    (hM : ((99 / 100 : ℝ) * b ^ 2) / u < (M : ℝ) + 1) (hk : (k : ℝ) < α * L / u)
    (hlog : u = 2 * Real.log b) (hbudget : T < (k : ℝ) * (u / 2 + 339 / 500)) :
    Real.exp T < (Nat.choose M k : ℝ) := by
  have hαL : (647 / 1000 : ℝ) * L ≤ α * L := mul_le_mul_of_nonneg_right hα (by linarith only [hL])
  have hb0 : 0 < b := by linarith only [hL, hαL, hb]
  have hratio := high_paired_ratio_99 hL hα hb hu0 hu hkM hM hk
  have hpos : 0 < (197 / 100 : ℝ) * b := mul_pos (by norm_num only) hb0
  have hR := hpos.trans hratio
  have hlogR := Real.log_lt_log hpos hratio
  rw [Real.log_mul (by norm_num only : (197 / 100 : ℝ) ≠ 0) hb0.ne'] at hlogR
  have hbound : u / 2 + (339 / 500 : ℝ) ≤ Real.log (2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1)) := by
    linarith only [hlog, hlogR, log_paired_base_197]
  apply exp_lt_choose_of_paired_budget M k hR
  exact hbudget.trans_le (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg k))

/-- A positive logarithmic scale `u` gives the paired-count budget when `α ≤ 2 / 3`, the scalar
gap is at least `1 / 100` at an upper scale `U`, and the quadratic error is at most `L / 100`.
The ceiling-minus-one lower bound on `k` then absorbs the rounding loss. -/
theorem paired_budget_of_gap {L α u U : ℝ} {k : ℕ} (hL : 0 < L) (hu : 0 < u) (huU : u ≤ U)
    (hα : α ≤ 2 / 3) (hgap : (3 / 2 * α - 1) * U + (339 / 500) * α ≥ 1 / 100)
    (hm : u ^ 2 + (339 / 250) * u ≤ L / 100) (hk : α * L / u - 1 ≤ (k : ℝ)) :
    (1 - α) * L < (k : ℝ) * (u / 2 + 339 / 500) := by
  have hbase : 0 ≤ u / 2 + (339 / 500 : ℝ) := by linarith only [hu]
  have hgapU : 0 ≤ (1 - (3 / 2 : ℝ) * α) * (U - u) :=
    mul_nonneg (by linarith only [hα]) (by linarith only [huU])
  have hgap' : (1 / 100 : ℝ) ≤ ((3 / 2 : ℝ) * α - 1) * u + (339 / 500) * α := by
    nlinarith only [hgap, hgapU]
  have hgapL := mul_le_mul_of_nonneg_left hgap' hL.le
  have hsmall : (u / 2 + (339 / 500 : ℝ)) * u ≤ L / 200 := by nlinarith only [hm]
  have hbudget' : (1 - α) * L * u < (α * L - u) * (u / 2 + 339 / 500) := by
    nlinarith only [hgapL, hsmall, hL]
  have hk' : α * L - u ≤ (k : ℝ) * u := by
    have hh := (sub_le_iff_le_add).mp hk
    have hh' := (div_le_iff₀ hu).mp hh
    nlinarith only [hh']
  have hmulk := mul_le_mul_of_nonneg_right hk' hbase
  have hc : (1 - α) * L * u < ((k : ℝ) * (u / 2 + 339 / 500)) * u := by
    nlinarith only [hbudget', hmulk]
  exact lt_of_mul_lt_mul_right hc hu.le

/-- The `99 / 100` supply, rounding bounds, and scalar gap make the paired-prime count exceed
the exponential cofactor budget. Combining the ratio estimate and logarithmic gap reduces the
large-cofactor witness construction to its radius and scalar hypotheses. -/
theorem high_paired_count_of_gap {L α b u U : ℝ} {M k : ℕ} (hL : 70000 ≤ L)
    (hα : (647 / 1000 : ℝ) ≤ α) (hα2 : α ≤ 2 / 3) (hb : α * L - 1 ≤ b) (hu0 : 0 < u)
    (hu : u ≤ L / 2000) (huU : u ≤ U) (hkM : k ≤ M)
    (hM : ((99 / 100 : ℝ) * b ^ 2) / u < (M : ℝ) + 1) (hklo : α * L / u - 1 ≤ (k : ℝ))
    (hkhi : (k : ℝ) < α * L / u) (hlog : u = 2 * Real.log b)
    (hgap : (3 / 2 * α - 1) * U + (339 / 500) * α ≥ 1 / 100)
    (hm : u ^ 2 + (339 / 250) * u ≤ L / 100) : Real.exp ((1 - α) * L) < (Nat.choose M k : ℝ) := by
  apply exp_lt_choose_of_supply_99 hL hα hb hu0 hu hkM hM hkhi hlog
  exact paired_budget_of_gap (by linarith only [hL]) hu0 huU hα2 hgap hm hklo

end PseudoPrime.PrimeTestBounds.MillerRabin
