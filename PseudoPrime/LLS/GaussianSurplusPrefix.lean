/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianSurplusData
public import PseudoPrime.Analysis.GaussianSignedEulerSeries

/-! # Actual finite Gaussian-minus-Gamma surplus -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The checked natural endpoints enclose every actual node power at a positive index.
Cast the denominator-200 grid identity and apply the integer interval soundness theorem. -/
theorem gaussianSurplus_ratio_sound {m : ℕ} (hm : 0 < m) (hc : gaussianSurplusNatCheck m = true)
    (ab : ℚ × ℚ) (hab : ab ∈ gaussianSurplusCoefficients) :
    ((gaussianSurplusRatios m ab.1).1 : ℝ) ≤ (m : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ∧
      (m : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ ((gaussianSurplusRatios m ab.1).2 : ℝ) := by
  have hnodes := of_decide_eq_true hc
  obtain ⟨hl, hu⟩ := List.forall_iff_forall_mem.mp hnodes ab hab
  have he := List.forall_iff_forall_mem.mp gaussianSurplus_exponents ab hab
  have heR := congrArg (fun q : ℚ ↦ (q : ℝ)) he
  norm_num only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] at heR
  have hexp : -(Analysis.finiteEulerExponent 200 ab.1 : ℝ) / 200 = -(1 / 2 + (ab.1 : ℝ)) := by
    linarith only [heR]
  have hb := gaussianSurplus_nat_interval hm hl hu
  simpa only [gaussianSurplusRatios, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, hexp] using hb

/-- The aggregated Mangoldt surplus is exactly Gaussian weight minus 17/20 Gamma weight.
The identity holds for every natural index, including zero. -/
theorem gaussianSurplus_mangoldt_eq (n : ℕ) :
    Analysis.finiteSignedMangoldtWeight gaussianSurplusCoefficients n =
      Analysis.gaussianResolventMangoldtWeight n - (17 / 20 : ℝ) *
        Analysis.gammaResolventMangoldtWeight n := by
  rw [Analysis.finiteSignedMangoldtWeight, gaussianSurplus_euler_eq,
    Analysis.gaussianResolventMangoldtWeight,
    Analysis.gammaResolventMangoldtWeight]
  ring

/-- The exact surplus is nonnegative at every input. Positive inputs use the existing
Gaussian/Gamma Euler comparison, and the zero input has zero Mangoldt weight. -/
theorem gaussianSurplus_nonneg (n : ℕ) :
    0 ≤ Analysis.finiteSignedMangoldtWeight gaussianSurplusCoefficients n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Analysis.finiteSignedMangoldtWeight, ArithmeticFunction.map_zero, zero_mul]
  · rw [Analysis.finiteSignedMangoldtWeight, gaussianSurplus_euler_eq]
    exact
      mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))
        (Analysis.gaussianGamma_weight_difference_nonneg (Nat.one_le_cast.mpr hn))

/-- A checked existing seed row yields its actual Mangoldt surplus lower bound.
Only the power intervals are new: the logarithm certificate and prime-power identity are reused. -/
theorem gaussianSurplus_row_lower (r : Analysis.GammaFiniteEulerRow) (hp : r.prime.Prime)
    (hc : r.check = true) (hpow : gaussianSurplusNatCheck r.index = true)
    (hlo : 0 ≤ Analysis.finiteSignedEulerLower gaussianSurplusCoefficients (gaussianSurplusRatios
      r.index)) :
    ((r.logLower *
            Analysis.finiteSignedEulerLower gaussianSurplusCoefficients (gaussianSurplusRatios
              r.index) :
          ℚ) :
        ℝ) ≤
      Analysis.finiteSignedMangoldtWeight gaussianSurplusCoefficients r.index := by
  have he :=
    (Analysis.finiteSigned_euler_interval_bounds gaussianSurplusCoefficients (gaussianSurplusRatios
      r.index)
        (gaussianSurplus_ratio_sound (pow_pos hp.pos _) hpow)).1
  have hlog := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2
  have hl := (Analysis.rationalLogIntervalCheck_sound hlog).1
  norm_num only [Rat.cast_natCast] at hl
  have hh := (Rat.cast_nonneg (K := ℝ)).mpr hlo
  have hw := mul_le_mul hl he hh (Real.log_natCast_nonneg r.prime)
  simpa only [Analysis.GammaFiniteEulerRow.index, Analysis.finiteSignedMangoldtWeight,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Rat.cast_mul] using hw

/-- The existing 35 distinct seed rows contribute at least 0.73 to the actual finite surplus.
The unselected terms are nonnegative, so complete prime-power enumeration is unnecessary. -/
theorem gaussianSurplus_prefix100 :
    (73 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 100, Analysis.finiteSignedMangoldtWeight gaussianSurplusCoefficients n :=
        by
  have h :=
    Analysis.nonnegative_weight_prefix_le_of_rows (Analysis.finiteSignedMangoldtWeight
      gaussianSurplusCoefficients)
      gaussianSurplus_nonneg Analysis.smallSeedRows Analysis.GammaFiniteEulerRow.index
      (fun r ↦
        r.logLower *
          Analysis.finiteSignedEulerLower gaussianSurplusCoefficients (gaussianSurplusRatios
            r.index))
      Analysis.small_seed_distinct (fun r hr ↦ List.forall_iff_forall_mem.mp
        Analysis.small_seed_members r hr)
      (fun r hr ↦
        gaussianSurplus_row_lower r (List.forall_iff_forall_mem.mp Analysis.small_seed_primes r hr)
          (List.forall_iff_forall_mem.mp Analysis.small_seed_rows_check r hr)
          (List.forall_iff_forall_mem.mp gaussianSurplus_all_checks r hr)
          (List.forall_iff_forall_mem.mp gaussianSurplus_rational_checks.1 r hr))
  have hs := (Rat.cast_le (K := ℝ)).mpr gaussianSurplus_rational_checks.2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hs
  exact hs.trans h

/-- Every actual finite prefix beyond 100 retains the entire certified surplus.
Enlarge the positive interval and use nonnegativity for the additional terms. -/
theorem gaussianSurplus_prefix {b : ℝ} (hb : 100 ≤ b) :
    (73 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.finiteSignedMangoldtWeight gaussianSurplusCoefficients n :=
        by
  have hB : 100 ≤ ⌊b⌋₊ := (Nat.le_floor_iff (by linarith only [hb] : (0 : ℝ) ≤ b)).mpr hb
  have hsub : Finset.Ioc 0 100 ⊆ Finset.Ioc 0 ⌊b⌋₊ := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans hB⟩
  exact
    gaussianSurplus_prefix100.trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ ↦ gaussianSurplus_nonneg n))

end PseudoPrime.LLS
