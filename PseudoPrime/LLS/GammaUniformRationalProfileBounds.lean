/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSignedWitnessBounds

/-! # A rational coefficient-0.796 shifted profile

The rational triple (199/250,0,117) has the same decimal entrance 10^15188
as the positive coefficient-0.8 profile. The proof controls the ambient-scale
excess as well as the actual nonunit loss, uniformly over every proper subgroup.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For L > 0, relative scale reduction at most r ≥ 0, ramp scale at least one
and root at least aL with a > 0, the explicit scale excess is at most (131/30)r/a.
Bound the negative-power coefficient by the reciprocal root and bound the positive part.
This controls the contour cost of decreasing the leading rational coefficient. -/
theorem gammaScaleExcess_le_of_relative_scale {L T r a : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (ha : 0 < a)
    (hscale : (1 - r) * L ≤ T) (hx : 1 ≤ (32 / 99 : ℝ) * T ^ 2)
    (hroot : a * L ≤ Real.sqrt ((32 / 99 : ℝ) * T ^ 2)) :
    gammaScaleExcess L T ≤ ((131 / 30 : ℝ) / a) * r := by
  let x := (32 / 99 : ℝ) * T ^ 2
  let D := max 0 (L - T - 2)
  have hs0 := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  have hD0 : 0 ≤ D := le_max_left _ _
  have hD : D ≤ r * L := by
    apply max_le (mul_nonneg hr hL.le)
    linarith only [hscale]
  have hrpow : x ^ (-9 / 16 : ℝ) ≤ 1 / Real.sqrt x := by
    have h := Real.rpow_le_rpow_of_exponent_le hx (by norm_num only : (-9 / 16 : ℝ) ≤ -(1 / 2 : ℝ))
    rw [Real.rpow_neg (zero_lt_one.trans_le hx).le, ← Real.sqrt_eq_rpow, ← one_div] at h
    exact h
  have hcoef :
    (7 / 6 : ℝ) / Real.sqrt x + (16 / 5 : ℝ) * x ^ (-9 / 16 : ℝ) ≤
      (131 / 30 : ℝ) / Real.sqrt x := by
    have h := mul_le_mul_of_nonneg_left hrpow (by norm_num only : (0 : ℝ) ≤ 16 / 5)
    calc
      _ ≤ (7 / 6 : ℝ) / Real.sqrt x + (16 / 5 : ℝ) * (1 / Real.sqrt x) := add_le_add_right h _
      _ = _ := by ring
  have hratio : L / Real.sqrt x ≤ 1 / a := by
    apply (div_le_div_iff₀ hs0 ha).mpr
    nlinarith only [hroot]
  have hstep :=
    mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 131 / 30) hr)
  change ((7 / 6 : ℝ) / Real.sqrt x + (16 / 5 : ℝ) * x ^ (-9 / 16 : ℝ)) * D ≤ _
  calc
    _ ≤ ((131 / 30 : ℝ) / Real.sqrt x) * D := mul_le_mul_of_nonneg_right hcoef hD0
    _ ≤ ((131 / 30 : ℝ) / Real.sqrt x) * (r * L) :=
      mul_le_mul_of_nonneg_left hD (div_nonneg (by norm_num only) hs0.le)
    _ = (131 / 30 : ℝ) * r * (L / Real.sqrt x) := by ring
    _ ≤ (131 / 30 : ℝ) * r * (1 / a) := hstep
    _ = _ := by ring

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, nonzero q, log q ≥ 34971 and H proper, a coprime outside prime
exists through (199/250)(log q+117)². Rescale the common ramp by sqrt(199/200),
certify its rational lower bound, local allowance and relative scale-excess budget.
This lowers coefficient 0.8 while retaining the smaller logarithmic entrance. -/
theorem exists_prime_outside_le_gamma_199_div_250_plus_117_log {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 34971 ≤ Real.log q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log q + 117) ^ 2 := by
  let L := Real.log q
  let T := Real.sqrt (199 / 200 : ℝ) * (L + 117)
  let x := (32 / 99 : ℝ) * T ^ 2
  have hL0 : 0 < L := by
    dsimp only [L]; linarith only [hL]
  have hsqrt : (124687 / 125000 : ℝ) ≤ Real.sqrt (199 / 200 : ℝ) := by
    apply (Real.le_sqrt (by norm_num only) (by norm_num only)).mpr
    norm_num only
  have hTlower : (124687 / 125000 : ℝ) * (L + 117) ≤ T :=
    mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ L + 117 by linarith only [hL0])
  have hT : 35000 ≤ T := by linarith only [hTlower, hL]
  have hxlarge := Analysis.common_nonOne_ramp_scale_large hT
  have hx : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ (17 / 5) ^ 16).trans hxlarge
  have hT0 : 0 < T := by linarith only [hT]
  have he : (4 / 5 : ℝ) * T ^ 2 = (199 / 250 : ℝ) * (L + 117) ^ 2 := by
    dsimp only [T]
    rw [mul_pow, Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 199 / 200)]
    ring
  have hcut : 1 ≤ (4 / 5 : ℝ) * T ^ 2 := by nlinarith only [hT, sq_nonneg (T - 35000)]
  have hcutupper : (4 / 5 : ℝ) * T ^ 2 ≤ L ^ 2 := by
    rw [he]
    nlinarith only [hL, sq_nonneg (L - 34971)]
  have hcutlog := Real.log_le_log (zero_lt_one.trans_le hcut) hcutupper
  rw [Real.log_pow] at hcutlog
  norm_num only [Nat.cast_ofNat] at hcutlog
  have hs := Analysis.uniform_ramp_scale_sqrt_lower_71_div_125 hT0.le
  have hroot : (283 / 500 : ℝ) * L ≤ Real.sqrt x := by
    change (71 / 125 : ℝ) * T ≤ Real.sqrt x at hs
    linarith only [hs, hTlower, hL0]
  have hlocal :=
    Analysis.gamma_commonFactor_budget_of_scale_ratio_sqrt (by norm_num only : (0 : ℝ) < 283 / 500)
      (show 1 < Real.log q by linarith only [hL]) (zero_lt_one.trans_le hx) hcut hcutlog hroot
      (Analysis.log_div_cuberoot_le_one_third_of_ge_32768
        (show 32768 ≤ Real.log q by linarith only [hL]))
  norm_num only at hlocal
  have hexcess :=
    gammaScaleExcess_le_of_relative_scale hL0 (by norm_num only : (0 : ℝ) ≤ 313 / 125000)
      (by norm_num only : (0 : ℝ) < 283 / 500)
      (show (1 - (313 / 125000 : ℝ)) * L ≤ T by linarith only [hTlower]) hx hroot
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have ht := Real.log_le_sub_one_of_pos hqpos
  have hq : 20000 ≤ q := by exact_mod_cast (show (20000 : ℝ) ≤ q by linarith only [ht, hL])
  have hbudget :
    (11783423 / 25000000 : ℝ) * Real.log q + gammaScaleExcess L T + 40159 / 900 +
        2 *
          (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((4 / 5 : ℝ) * T ^ 2) q /
            Real.sqrt x) <
      (11783423 / 25000000 + 1 / 795 : ℝ) * T := by
    linarith only [hlocal, hexcess, hTlower, hL]
  obtain ⟨p, hp, hd, hout, hb⟩ :=
    exists_prime_outside_le_gamma_four_fifths_signed_scale hq H hH hGRH hT hbudget
  exact ⟨p, hp, hd, hout, he ▸ hb⟩

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, q ≥ 10^15188 and H proper, a coprime outside prime exists
through (199/250)(log q+117)². Convert the decimal threshold to log q > 34971.
This is the uniform decimal entrance for the coefficient-0.796 profile. -/
theorem exists_prime_outside_le_gamma_199_div_250_plus_117_15188 {q : ℕ} (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hq : 10 ^ 15188 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log q + 117) ^ 2 := by
  have hq0 : q ≠ 0 :=
    Nat.ne_zero_of_lt ((pow_pos (by norm_num only : (0 : ℕ) < 10) 15188).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  apply exists_prime_outside_le_gamma_199_div_250_plus_117_log H hH hGRH
  exact
    (Analysis.log_nat_gt_of_decimal_lower (by norm_num only : 0 < 15188) hq
        (by norm_num only : (34971 : ℝ) < (15188 : ℝ) * (115129 / 50000))).le

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH, q ≥ 10^15188 and χ nonprincipal, a coprime prime with χ(p) ≠ 1
exists through (199/250)(log q+117)². Apply the uniform subgroup cutoff to the unit kernel.
This is the general-character version with the same expression and starting value. -/
theorem exists_prime_character_ne_one_le_gamma_199_div_250_plus_117_15188 {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 15188 ≤ q) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log q + 117) ^ 2 := by
  exact
    exists_prime_character_ne_one_of_uniform_subgroup_cutoff χ hne
      (fun H hH ↦
        PaperStatements.exists_prime_outside_le_gamma_199_div_250_plus_117_15188 H hH hGRH hq)

/-- Under GRH, q ≥ 10^15188 and H proper, the least coprime outside prime is
at most (199/250)(log q+117)². Minimize the bounded outside-prime witness.
Minimality is among all eligible primes and retains the same starting value. -/
theorem exists_least_prime_outside_le_gamma_199_div_250_plus_117_15188 {q : ℕ}
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 15188 ≤ q) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log q + 117) ^ 2 ∧
        ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  exact
    exists_least_prime_outside_of_subgroup_cutoff H
      (PaperStatements.exists_prime_outside_le_gamma_199_div_250_plus_117_15188 H hH hGRH hq)

end PseudoPrime.LLS
