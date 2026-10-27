/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalTheorem11S1Subgroup
public import PseudoPrime.LLS.RationalProfileContracts
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorParitySplitBounds

/-! # Parity-improved rational Part 1 profile from 3000 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L ≥ 8, twice the squared logarithmic ratio is at most 271/250.
Use its monotonicity and the certified logarithm of eight.
This absorbs the exceptional-prime contribution into a rational constant. -/
theorem twice_log_sq_div_le_of_ge_eight {L : ℝ} (hL : 8 ≤ L) :
    2 * Real.log L ^ 2 / L ≤ 271 / 250 := by
  have h := strictAntiOn_logSquareRatio.antitoneOn (le_refl (8 : ℝ)) hL hL
  change Real.log L ^ 2 / L ≤ Real.log (8 : ℝ) ^ 2 / 8 at h
  have h8 : Real.log (8 : ℝ) ≤ 52 / 25 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have h80 : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num only)
  have hs := (sq_le_sq₀ h80 (by norm_num only : (0 : ℝ) ≤ 52 / 25)).mpr h8
  norm_num only at hs
  rw [show 2 * Real.log L ^ 2 / L = 2 * (Real.log L ^ 2 / L) by ring]
  linarith only [h, hs]

/-- For L > 0, log L/L^(3/10) ≤ 1227/1000. Apply a logarithmic tangent
at 1359/500 and the certified exponential lower bound at one.
This controls the small-prime contribution for the split exponent 7/10. -/
theorem log_div_rpow_three_tenths_le {L : ℝ} (hL : 0 < L) :
    Real.log L / L ^ (3 / 10 : ℝ) ≤ 1227 / 1000 := by
  have hu0 := Real.rpow_pos_of_pos hL (3 / 10 : ℝ)
  have ht := Real.log_le_sub_one_of_pos (div_pos hu0 (by norm_num only : (0 : ℝ) < 1359 / 500))
  rw [Real.log_div hu0.ne' (by norm_num only : (1359 / 500 : ℝ) ≠ 0), Real.log_rpow hL] at ht
  have ha : Real.log (1359 / 500 : ℝ) < 1 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num only : (0 : ℝ) < 1359 / 500)).mpr
    exact (by norm_num only : (1359 / 500 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
  rw [div_le_iff₀ hu0]
  linarith only [ht, ha, hu0]

end PseudoPrime.Analysis

namespace PseudoPrime.LLS

/-- For q ≥ 3000, the rational Part 1 radius is at most
log q+(42589/7000)log log q+77/25. Split the support at (log q)^(7/10),
use the parity saving and absorb the exceptional prime by the squared-log ratio.
This improves the universal rational profile while retaining the actual pointwise radius. -/
theorem rationalRadiusRoot_le_parity_shift {q : ℕ} [NeZero q] (hq : 3000 ≤ q) :
    rationalRadiusRoot q ≤ Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25 := by
  let L := Real.log q
  let z := Real.log L
  let u := L ^ (3 / 10 : ℝ)
  have hL8 := Analysis.eight_lt_log_level hq
  have hL : 1 < L := by linarith only [hL8]
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hz0 : 0 < z := Real.log_pos hL
  have hu0 := Real.rpow_pos_of_pos hL0 (3 / 10 : ℝ)
  have hratio := Analysis.log_div_rpow_three_tenths_le hL0
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_half_log_power (NeZero.ne q) hL
      (by norm_num only : (0 : ℝ) < 7 / 10)
  have hpow : L ^ (7 / 10 : ℝ) = L / u := by
    apply (eq_div_iff hu0.ne').mpr
    rw [← Real.rpow_add hL0]
    norm_num only [Real.rpow_one]
  have hcan : L / ((7 / 10 : ℝ) * z) = (10 / 7 : ℝ) * L / z := by
    rw [div_mul_eq_div_div]
    ring
  change (q.primeFactors.card : ℝ) ≤ L ^ (7 / 10 : ℝ) / 2 + 1 + L / ((7 / 10 : ℝ) * z) at hcard
  rw [hpow, hcan] at hcard
  have hm := mul_le_mul_of_nonneg_right hcard (div_nonneg hz0.le hL0.le)
  have he : (L / u / 2 + 1 + (10 / 7 : ℝ) * L / z) * (z / L) = z / u / 2 + z / L + 10 / 7 := by
    calc
      _ = (z / u / 2) * (L / L) + z / L + (10 / 7 : ℝ) * ((L / z) * z / L) := by ring
      _ = z / u / 2 + z / L + 10 / 7 := by
        rw [div_self hL0.ne', div_mul_cancel₀ _ hz0.ne', div_self hL0.ne', mul_one, mul_one]
  rw [he] at hm
  have hstep : (q.primeFactors.card : ℝ) * (z / L) ≤ (1227 / 1000 : ℝ) / 2 + z / L + 10 / 7 := by
    linarith only [hm, hratio]
  have hw := mul_le_mul_of_nonneg_left hstep (show 0 ≤ 2 * z by linarith only [hz0])
  have hwe :
    2 * z * ((q.primeFactors.card : ℝ) * (z / L)) = 2 * (q.primeFactors.card : ℝ) * z ^ 2 / L := by
    ring
  rw [hwe] at hw
  rw [show 2 * z * ((1227 / 1000 : ℝ) / 2 + z / L + 10 / 7) = (28589 / 7000 : ℝ) * z + 2 * z ^ 2 / L
      by ring] at hw
  have hA : 0 ≤ refinedAuxiliaryTerm q := le_max_left _ _
  have hB : rationalCorrectionTerm q ≤ (42589 / 7000 : ℝ) * z + 77 / 25 := by
    unfold rationalCorrectionTerm
    apply max_le (by linarith only [hz0])
    change
      2 * z + 499 / 250 + 2 * (q.primeFactors.card : ℝ) * z ^ 2 / L - 2 * refinedAuxiliaryTerm q ≤
        (42589 / 7000 : ℝ) * z + 77 / 25
    have hsmall := Analysis.twice_log_sq_div_le_of_ge_eight hL8.le
    change 2 * z ^ 2 / L ≤ 271 / 250 at hsmall
    linarith only [hw, hA, hsmall]
  unfold rationalRadiusRoot
  linarith only [hB]

/-- Under GRH, a nonprincipal character at q ≥ 3000 has a coprime non-one
prime through (log q+(42589/7000)log log q+77/25)².
Compare the nonnegative rational-radius roots and transfer the pointwise witness.
This is the general-character interface for the sharper profile. -/
theorem exists_prime_character_ne_one_le_parityProfile3000 {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 3000 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        χ p ≠ 1 ∧
        (p : ℝ) ≤ (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25) ^ 2 := by
  have hq0 : q ≠ 0 := Nat.ne_zero_of_lt ((by decide : (0 : ℕ) < 3000).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  obtain ⟨p, hp, hd, hv, hb⟩ := exists_prime_character_ne_one_le_rationalRadius χ hq hne hGRH
  have hR := rationalRadiusRoot_le_parity_shift hq
  have hR0 : 0 ≤ rationalRadiusRoot q := by
    unfold rationalRadiusRoot
    have hL := Analysis.eight_lt_log_level hq
    have hB : 0 ≤ rationalCorrectionTerm q := le_max_left _ _
    linarith only [hL, hB]
  exact ⟨p, hp, hd, hv, hb.trans ((sq_le_sq₀ hR0 (hR0.trans hR)).mpr hR)⟩

/-- Under GRH, q ≥ 3000 and H proper, a coprime outside prime lies through
the parity-improved profile. Bound the rational-radius root and transfer its subgroup witness.
This retains the uniform subgroup and starting-value scope. -/
theorem exists_prime_outside_subgroup_le_parityProfile3000 {q : ℕ} (hq : 3000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25) ^ 2 := by
  have hq0 : q ≠ 0 := Nat.ne_zero_of_lt ((by decide : (0 : ℕ) < 3000).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_subgroup_le_rationalRadius hq H hH hGRH
  have hR := rationalRadiusRoot_le_parity_shift hq
  have hR0 : 0 ≤ rationalRadiusRoot q := by
    unfold rationalRadiusRoot
    have hL := Analysis.eight_lt_log_level hq
    have hB : 0 ≤ rationalCorrectionTerm q := le_max_left _ _
    linarith only [hL, hB]
  exact ⟨p, hp, hb.trans ((sq_le_sq₀ hR0 (hR0.trans hR)).mpr hR)⟩

/-- Under GRH, q ≥ 3000 and H proper, the least coprime outside prime lies
through the parity-improved profile. Minimize the unbounded outside-prime predicate.
Minimality holds among all eligible primes, with the same formula and starting value. -/
theorem exists_least_prime_outside_subgroup_le_parityProfile3000 {q : ℕ} (hq : 3000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25) ^ 2 ∧
        ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  classical
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_subgroup_le_parityProfile3000 hq H hH hGRH
  have hex : ∃ r, PrimeOutsideSubgroup q H r := ⟨p, hp⟩
  exact
    ⟨Nat.find hex, Nat.find_spec hex, (Nat.cast_le.mpr (Nat.find_min' hex hp)).trans hb, fun _ hr ↦
      Nat.find_min' hex hr⟩

/-- The rational tuple (1,42589/7000,77/25) starts at 3000.
The common profile structure stores its positive leading coefficient and own entrance.
This is the current uniform-unit-subgroup candidate. -/
def parityPart1Profile : Analysis.RationalLogarithmicProfile :=
  ⟨1, 42589 / 7000, 77 / 25, by norm_num only, 3000⟩

/-- Under GRH, the parity profile gives a coprime outside prime for every
proper subgroup from 3000. Apply the sharper subgroup theorem and normalize the rational casts.
This attaches a witness proof to the coefficient-and-start pair. -/
theorem parityPart1Profile_bound : UniformSubgroupProfileBound parityPart1Profile := by
  intro q H hH hGRH hq
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_subgroup_le_parityProfile3000 hq H hH hGRH
  refine ⟨p, hp, ?_⟩
  simpa only [Analysis.RationalLogarithmicProfile.cutoff, Analysis.logarithmicShiftCutoff,
    Analysis.logarithmicShiftRoot, parityPart1Profile, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one,
    one_mul] using hb

/-- For 3000 ≤ n ≤ m, the parity profile cutoff is nondecreasing.
Apply logarithm monotonicity and the positive-root shifted cutoff comparison.
This preserves the pointwise formula for finite-range envelopes. -/
theorem parityPart1Profile_cutoff_le {n m : ℕ} (hn : 3000 ≤ n) (horder : n ≤ m) :
    parityPart1Profile.cutoff n ≤ parityPart1Profile.cutoff m := by
  have hL := Analysis.eight_lt_log_level hn
  have hL0 : 0 < Real.log n := by linarith only [hL]
  have hz := Real.log_nonneg (show 1 ≤ Real.log n by linarith only [hL])
  have hlog :=
    Real.log_le_log (Nat.cast_pos.mpr ((by decide : (0 : ℕ) < 3000).trans_le hn))
      (Nat.cast_le.mpr horder)
  have hb : -Real.log n ≤ ((42589 / 7000 : ℚ) : ℝ) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    linarith only [hL]
  have hroot : 0 ≤ Analysis.logarithmicShiftRoot (Real.log n) (42589 / 7000) (77 / 25) := by
    norm_num only [Analysis.logarithmicShiftRoot, Rat.cast_div, Rat.cast_ofNat]
    linarith only [hL, hz]
  exact Analysis.logarithmicShiftCutoff_le_of_le (by norm_num only : (0 : ℚ) < 1) hL0 hlog hb hroot

/-- Under GRH, for 3000 ≤ q ≤ B and H proper, an outside prime lies through
the parity profile at B. Transfer the pointwise witness by monotonicity.
The envelope uses the same coefficient triple and starting value. -/
theorem exists_prime_outside_le_parityPart1Profile_envelope {q B : ℕ} (hq : 3000 ≤ q) (hqB : q ≤ B)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ parityPart1Profile.cutoff B := by
  obtain ⟨p, hp, hb⟩ := parityPart1Profile_bound q H hH hGRH hq
  exact ⟨p, hp, hb.trans (parityPart1Profile_cutoff_le hq hqB)⟩

end PseudoPrime.LLS

namespace PseudoPrime.Analysis

/-- For L ≥ 8, the new parity profile square is strictly below the former
Part 1 profile square. The logarithm of L exceeds two, so the decrease in its coefficient
outweighs the increased constant. This removes the former tuple on its whole eligible domain. -/
theorem parity_shift_sq_lt_original {L : ℝ} (hL : 8 ≤ L) :
    (L + (42589 / 7000 : ℝ) * Real.log L + 77 / 25) ^ 2 <
      (L + (1791 / 250 : ℝ) * Real.log L + 499 / 250) ^ 2 := by
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 8) hL
  have h8 : (2 : ℝ) < Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hroot :
    L + (42589 / 7000 : ℝ) * Real.log L + 77 / 25 <
      L + (1791 / 250 : ℝ) * Real.log L + 499 / 250 := by
    linarith only [hlog, h8]
  apply
    (sq_lt_sq₀
        (show 0 ≤ L + (42589 / 7000 : ℝ) * Real.log L + 77 / 25 by linarith only [hL, hlog, h8])
        (show 0 ≤ L + (1791 / 250 : ℝ) * Real.log L + 499 / 250 by
          linarith only [hL, hlog, h8])).mpr
  exact hroot

end PseudoPrime.Analysis
