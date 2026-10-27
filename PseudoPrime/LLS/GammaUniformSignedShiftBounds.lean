/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformScaleBounds
public import PseudoPrime.LLS.GammaUniformLocalBudgetParameters

/-! # Smaller Gamma cutoffs with a negative constant correction

An independent nonunit-loss budget applies to any scale and cutoff satisfying
the root and logarithmic bounds. The choice T=log q-2 gives a strictly smaller
coefficient-four-fifths cutoff from log q ≥ 46330.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For nonzero q with log q > 1, x > 0 and X ≥ 1, suppose log X ≤ 2 log log q,
sqrt x ≥ a log q with a > 0, and log log q/(log q)^(1/3) ≤ beta.
Twice the normalized nonunit loss is at most (4/a)(beta+3/2).
Use the split-prime estimate and cancel the logarithmic and root factors.
This local budget permits scales independent of log q. -/
theorem gamma_commonFactor_budget_of_scale_ratio_sqrt {q : ℕ} [NeZero q] {x X a beta : ℝ}
    (ha : 0 < a) (hL : 1 < Real.log q) (hx0 : 0 < x) (hcut : 1 ≤ X)
    (hcutlog : Real.log X ≤ 2 * Real.log (Real.log q)) (hroot : a * Real.log q ≤ Real.sqrt x)
    (hlog : Real.log (Real.log q) / (Real.log q) ^ (1 / 3 : ℝ) ≤ beta) :
    2 * (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x X q / Real.sqrt x) ≤
      (4 / a) * (beta + 3 / 2) := by
  let L := Real.log q
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hs0 := Real.sqrt_pos.mpr hx0
  have hu0 := Real.rpow_pos_of_pos hL0 (1 / 3 : ℝ)
  have hlog0 := Real.log_pos hL
  have hp : L ^ (2 / 3 : ℝ) = L / L ^ (1 / 3 : ℝ) := by
    apply (eq_div_iff hu0.ne').mpr
    rw [← Real.rpow_add hL0]
    norm_num only [Real.rpow_one]
  have hc := hcutlog
  have hF0 : 0 ≤ L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L :=
    add_nonneg (Real.rpow_pos_of_pos hL0 _).le (div_nonneg (by linarith only [hL0]) hlog0.le)
  have hnum :=
    (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum_le_log_two_thirds (NeZero.ne q) hx0
          hcut hL).trans
      (mul_le_mul_of_nonneg_left hc hF0)
  have he :
    (L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L) * (2 * Real.log L) =
      2 * L * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) := by
    rw [hp]
    have hbcan : ((3 / 2 : ℝ) * L / Real.log L) * (2 * Real.log L) = 3 * L := by
      calc
        _ = 2 * ((3 / 2 : ℝ) * L / Real.log L * Real.log L) := by ring
        _ = 2 * ((3 / 2 : ℝ) * L) := by rw [div_mul_cancel₀ _ hlog0.ne']
        _ = 3 * L := by ring
    rw [add_mul, hbcan]
    ring
  change
    AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x X q ≤
      (L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L) * (2 * Real.log L) at hnum
  rw [he] at hnum
  have hB0 : 0 ≤ Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2 :=
    add_nonneg (div_nonneg hlog0.le hu0.le) (by norm_num only)
  have hr : L / Real.sqrt x ≤ 1 / a := by
    apply (div_le_div_iff₀ hs0 ha).mpr
    nlinarith only [hroot]
  have hm := mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hB0)
  have ht :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by norm_num only : (0 : ℝ) ≤ 2))
      (Real.sqrt_nonneg x)
  calc
    _ = 2 * AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x X q / Real.sqrt x := by
      ring
    _ ≤ 2 * (2 * L * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2)) / Real.sqrt x := ht
    _ = 4 * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) * (L / Real.sqrt x) := by ring
    _ ≤ 4 * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) * (1 / a) := hm
    _ = (4 / a) * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) := by ring
    _ ≤ (4 / a) * (beta + 3 / 2) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hlog (3 / 2 : ℝ))
        (div_nonneg (by norm_num only : (0 : ℝ) ≤ 4) ha.le)

/-- For log q ≥ 44739, twice the normalized nonunit loss at T=log q-2 and
x=(32/99)T² is at most 170560/13419. Bound the cutoff by (log q)² and
the scale root below by (567/1000)log q, then apply the general local budget.
This controls the actual local loss for the negative constant correction. -/
theorem gamma_commonFactor_budget_log_minus_two {q : ℕ} [NeZero q] (hL : 44739 ≤ Real.log q) :
    let T := Real.log q - 2;
    let x := (32 / 99 : ℝ) * T ^ 2;
    2 *
        (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((4 / 5 : ℝ) * T ^ 2) q /
          Real.sqrt x) ≤
      (4 / (567 / 1000 : ℝ)) * (1071 / 3550 + 3 / 2) := by
  let L := Real.log q
  let T := L - 2
  let x := (32 / 99 : ℝ) * T ^ 2
  have hT0 : 0 < T := by
    dsimp only [T, L]; linarith only [hL]
  have hx0 : 0 < x := mul_pos (by norm_num only) (sq_pos_of_pos hT0)
  have hcut : 1 ≤ (4 / 5 : ℝ) * T ^ 2 := by
    dsimp only [T, L]
    nlinarith only [hL, sq_nonneg (Real.log q - 44739)]
  have hc : (4 / 5 : ℝ) * T ^ 2 ≤ L ^ 2 := by
    have he : T ≤ L := by
      dsimp only [T]; linarith only
    have ht :=
      (sq_le_sq₀ hT0.le
            (show 0 ≤ L by
              dsimp only [L]; linarith only [hL])).mpr
        he
    nlinarith only [ht, sq_nonneg T]
  have hlog := Real.log_le_log (zero_lt_one.trans_le hcut) hc
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hs := uniform_ramp_scale_sqrt_lower_71_div_125 hT0.le
  have hroot : (567 / 1000 : ℝ) * L ≤ Real.sqrt x := by
    change (71 / 125 : ℝ) * (L - 2) ≤ Real.sqrt x at hs
    have hlarge : 44739 ≤ L := hL
    linarith only [hs, hlarge]
  exact
    gamma_commonFactor_budget_of_scale_ratio_sqrt (by norm_num only)
      (show 1 < Real.log q by linarith only [hL]) hx0 hcut hlog hroot
      (log_div_cuberoot_le_of_ge_44739 hL)

end PseudoPrime.Analysis

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, nonzero q, log q ≥ 46330 and H proper, a prime coprime to q
outside H exists through (4/5)(log q-2)². Apply the independent-scale witness
theorem and the certified local-loss allowance with a strict rational margin.
This improves the pointwise upper bound on the entire stated half-line. -/
theorem exists_prime_outside_le_gamma_four_fifths_log_minus_two {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 46330 ≤ Real.log q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q - 2) ^ 2 := by
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have ht := Real.log_le_sub_one_of_pos hqpos
  have hq : 20000 ≤ q := by exact_mod_cast (show (20000 : ℝ) ≤ q by linarith only [ht, hL])
  apply
    exists_prime_outside_le_gamma_four_fifths_scale hq H hH hGRH
      (show 35000 ≤ Real.log q - 2 by linarith only [hL])
      (show Real.log q ≤ Real.log q - 2 + 2 by linarith only)
  have hlocal :=
    Analysis.gamma_commonFactor_budget_log_minus_two (show 44739 ≤ Real.log q by linarith only [hL])
  dsimp only at hlocal
  linarith only [hlocal, hL]

end PseudoPrime.LLS.PaperStatements
