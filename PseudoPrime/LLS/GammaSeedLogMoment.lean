/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPrefixFine

/-! # Checked seed logarithmic moments and transported actual prefixes -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The rational logarithmic moment of one existing prime-power row.
The positive exponent is exponent plus one, matching the represented index. -/
def seedRowLogMoment (r : Analysis.GammaFiniteEulerRow) : ℚ :=
  ((r.exponent + 1 : ℕ) : ℚ) * r.logLower ^ 2

/-- For a prime row with a valid logarithm check and nonnegative lower endpoint,
its rational logarithmic moment is below the actual Mangoldt logarithmic moment.
Square the certified logarithm inequality and evaluate Mangoldt at the positive prime power. -/
theorem seed_row_log_moment (r : Analysis.GammaFiniteEulerRow) (hp : r.prime.Prime)
    (hc : r.check = true) (hlo : 0 ≤ r.logLower) :
    (seedRowLogMoment r : ℝ) ≤ ArithmeticFunction.vonMangoldt r.index * Real.log (r.index : ℝ) := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hlog := (Analysis.rationalLogIntervalCheck_sound (Bool.and_eq_true_iff.mp hh.1).2).1
  norm_num only [Rat.cast_natCast] at hlog
  have hl0 : (0 : ℝ) ≤ (r.logLower : ℝ) := (Rat.cast_nonneg (K := ℝ)).mpr hlo
  have hs := (sq_le_sq₀ hl0 (hl0.trans hlog)).mpr hlog
  have hm :=
    mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (r.exponent + 1) : (0 : ℝ) ≤ (r.exponent + 1 : ℕ))
  rw [Analysis.GammaFiniteEulerRow.index,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
  norm_num only [seedRowLogMoment, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow]
  nlinarith only [hm]

/-- The existing 35 rows have exact rational logarithmic moment 342.3144832843.
Kernel arithmetic also checks all logarithm lower endpoints are nonnegative. -/
theorem seed_log_moment_check :
    (Analysis.smallSeedRows.map seedRowLogMoment).sum = (3423144832843 / 10000000000 : ℚ) ∧
      Analysis.smallSeedRows.Forall (fun r ↦ 0 ≤ r.logLower) := by
  decide +kernel

/-- The existing distinct seed rows bound the actual full logarithmic moment below.
Embed their indices into the positive interval and retain nonnegativity of every omitted term.
Exhaustive coverage of the prime powers is not required. -/
theorem seed_log_moment_lower :
    (3423144832843 / 10000000000 : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 100, ArithmeticFunction.vonMangoldt m * Real.log (m : ℝ) := by
  have hl :=
    List.sum_le_sum
      (fun (r : Analysis.GammaFiniteEulerRow) hr ↦
        seed_row_log_moment r (List.forall_iff_forall_mem.mp Analysis.small_seed_primes r hr)
          (List.forall_iff_forall_mem.mp Analysis.small_seed_rows_check r hr)
          (List.forall_iff_forall_mem.mp seed_log_moment_check.2 r hr))
  have hs :
    (Analysis.smallSeedRows.map Analysis.GammaFiniteEulerRow.index).toFinset ⊆
      Finset.Ioc 0 100 := by
    intro m hm
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    exact Finset.mem_Ioc.mpr (List.forall_iff_forall_mem.mp Analysis.small_seed_members r hr)
  have ht :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (f := fun m ↦
      ArithmeticFunction.vonMangoldt m * Real.log (m : ℝ))
      (fun m hm _ ↦
        mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := m))
          (Real.log_nonneg
            (by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_Ioc.mp hm).1 : (1 : ℝ) ≤ m)))
  rw [List.sum_toFinset _ Analysis.small_seed_distinct, List.map_map] at ht
  have hcast :
    (((Analysis.smallSeedRows.map seedRowLogMoment).sum : ℚ) : ℝ) =
      (3423144832843 / 10000000000 : ℝ) := by
    rw [seed_log_moment_check.1]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [← hcast]
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def]
  exact hl.trans ht

/-- At a positive cutoff, the smoothed Mangoldt sum equals log times psi minus
the actual logarithmic moment. Expand log of a quotient over the positive finite interval. -/
theorem smoothed_eq_log_psi_sub {x : ℝ} (hx : 0 < x) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x =
      Real.log x * Chebyshev.psi x -
        ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt m * Real.log (m : ℝ) := by
  rw [AnalyticNumberTheory.Arithmetic.psi_eq_positive_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hm).1
  rw [AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm, Real.log_div hx.ne' hm0.ne']
  ring

/-- The existing twenty-term rational logarithm checker bounds log 100 above.
This single finer logarithm cap controls the seed smoothed sum without RH. -/
theorem seed_log100_upper : Real.log (100 : ℝ) ≤ 4605171 / 1000000 := by
  have hc :
    Analysis.rationalLogIntervalCheck 100 7 20 (4605170 / 1000000) (4605171 / 1000000) = true := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using (Analysis.rationalLogIntervalCheck_sound hc).2

/-- The actual smoothed sum at 100 is at most 90.784, without RH.
Combine the checked logarithm cap, existing actual psi cap and actual moment lower bound. -/
theorem seed_moment_smoothed_upper :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 100 ≤ (11348 / 125 : ℝ) := by
  have hp :=
    mul_le_mul seed_log100_upper fine_seed_psi (Chebyshev.psi_nonneg 100)
      (by norm_num only : (0 : ℝ) ≤ 4605171 / 1000000)
  rw [smoothed_eq_log_psi_sub (by norm_num only : (0 : ℝ) < 100)]
  norm_num only [Nat.floor_ofNat]
  linarith only [hp, seed_log_moment_lower]

/-- The actual Euler boundary at 100 is at least 9.25833, without RH.
Keep the signed weight, slope and main-tail products with the moment-derived smoothed cap. -/
theorem moment_seed_boundary : (925833 / 100000 : ℝ) ≤ gammaEulerBoundaryTail 100 := by
  have h :=
    gamma_euler_boundary_tail_lower fine_seed_weight (by norm_num only) fine_seed_psi
      fine_seed_slope (by norm_num only)
      (gamma_logWeightedMangoldtSum_nonneg (by norm_num only : (0 : ℝ) < 100))
      seed_moment_smoothed_upper fine_seed_main
  linarith only [h]

/-- Under RH, any certified seed boundary lower bound transports the existing seed
to an actual target prefix. The target boundary and error remain explicit inputs. -/
theorem prefix_at_seed_boundary (hRH : RiemannHypothesis) {A b B E : ℝ}
    (hA : A ≤ gammaEulerBoundaryTail 100) (hb : 1 ≤ b) (hB : gammaEulerBoundaryTail b ≤ B)
    (hE : gammaEulerTailErrorBudget b ≤ E) :
    15877 / 5000 + A - B - (93 / 1250 + E) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  exact
    gamma_euler_prefix_lower_of_transport_bounds hRH (by norm_num only) hb recovered_seed_prefix hA
      hB (add_le_add recovered_seed_error hE)

/-- Under RH, the moment-derived seed boundary transports the improved seed credit.
Apply the parameterized transport theorem while retaining the existing target inputs. -/
theorem moment_prefix_at (hRH : RiemannHypothesis) {b B E : ℝ} (hb : 1 ≤ b)
    (hB : gammaEulerBoundaryTail b ≤ B) (hE : gammaEulerTailErrorBudget b ≤ E) :
    15877 / 5000 + 925833 / 100000 - B - (93 / 1250 + E) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  exact prefix_at_seed_boundary hRH moment_seed_boundary hb hB hE

/-- Under RH, every actual Gamma prefix beyond this cutoff has the displayed credit.
Use the moment-derived seed boundary, unchanged target certificate and prefix monotonicity. -/
theorem gamma_prefix1000_moment (hRH : RiemannHypothesis) {b : ℝ} (hb : 1000 ≤ b) :
    (42501 / 10000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    moment_prefix_at hRH (by norm_num only : (1 : ℝ) ≤ 1000) (recovered_boundary1000 hRH)
      recovered_error1000
  have hm :=
    recovered_prefix_mono (c := 42501 / 10000) hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [h])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hm
  exact hm

/-- Under RH, every actual Gamma prefix beyond this cutoff has the displayed credit.
Use the moment-derived seed boundary, unchanged target certificate and prefix monotonicity. -/
theorem gamma_prefix35000_moment (hRH : RiemannHypothesis) {b : ℝ} (hb : 35000 ≤ b) :
    (28301 / 5000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    moment_prefix_at hRH (by norm_num only : (1 : ℝ) ≤ 35000) (fine_boundary35000 hRH)
      checkpoint35000_error_upper
  have hm :=
    recovered_prefix_mono (c := 28301 / 5000) hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [h])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hm
  exact hm

/-- Under RH, every actual Gamma prefix beyond this cutoff has the displayed credit.
Use the moment-derived seed boundary, unchanged target certificate and prefix monotonicity. -/
theorem gamma_prefix50000_moment (hRH : RiemannHypothesis) {b : ℝ} (hb : 50000 ≤ b) :
    (57827 / 10000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    moment_prefix_at hRH (by norm_num only : (1 : ℝ) ≤ 50000) (fine_boundary50000 hRH)
      gamma_tail_error_budget_le
  have hm :=
    recovered_prefix_mono (c := 57827 / 10000) hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [h])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hm
  exact hm

/-- Under RH, every actual Gaussian prefix beyond this cutoff has the displayed credit.
Transfer the actual Gamma prefix through the pointwise kernel factor 17/20. -/
theorem gaussian_prefix1000_moment (hRH : RiemannHypothesis) {b : ℝ} (hb : 1000 ≤ b) :
    (722517 / 200000 : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight m := by
  have h := recovered_gaussian_prefix (gamma_prefix1000_moment hRH hb)
  linarith only [h]

/-- Under RH, every actual Gaussian prefix beyond this cutoff has the displayed credit.
Transfer the actual Gamma prefix through the pointwise kernel factor 17/20. -/
theorem gaussian_prefix35000_moment (hRH : RiemannHypothesis) {b : ℝ} (hb : 35000 ≤ b) :
    (481117 / 100000 : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight m := by
  have h := recovered_gaussian_prefix (gamma_prefix35000_moment hRH hb)
  linarith only [h]

/-- Under RH, every actual Gaussian prefix beyond this cutoff has the displayed credit.
Transfer the actual Gamma prefix through the pointwise kernel factor 17/20. -/
theorem gaussian_prefix50000_moment (hRH : RiemannHypothesis) {b : ℝ} (hb : 50000 ≤ b) :
    (983059 / 200000 : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight m := by
  have h := recovered_gaussian_prefix (gamma_prefix50000_moment hRH hb)
  linarith only [h]

end PseudoPrime.LLS
