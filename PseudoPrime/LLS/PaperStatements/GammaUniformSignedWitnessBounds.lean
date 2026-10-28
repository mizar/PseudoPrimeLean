/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSignedProfiles
public import PseudoPrime.LLS.GammaUniformTightStart
public import PseudoPrime.Analysis.LogarithmicShiftBounds
public import PseudoPrime.Analysis.GammaUniformSignedWitnessBounds

/-! # Decimal and character interfaces for rational signed Gamma profiles

The concrete rational triples (4/5,0,29), (4/5,0,-2) and (4/5,-1,0)
have decimal entrances 15188, 20121 and 22097. General characters and least
outside primes use the same cutoffs. A rational-parameter interface retains
the actual analytic budget for further coefficient optimization.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, q ≥ 10^15188 and H proper, a coprime prime outside H exists
through (4/5)(log q+29)². Convert the exact decimal entrance to log q > 34971.
This is the decimal proper-subgroup interface for the signed profile. -/
theorem exists_prime_outside_le_gamma_four_fifths_plus_twentyNine_15188 {q : ℕ}
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 15188 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q + 29) ^ 2 := by
  have hq0 : q ≠ 0 :=
    Nat.ne_zero_of_lt ((pow_pos (by norm_num only : (0 : ℕ) < 10) 15188).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  apply exists_prime_outside_le_gamma_four_fifths_log_plus_twentyNine H hH hGRH
  exact
    (Analysis.log_nat_gt_of_decimal_lower (by norm_num only : 0 < 15188) hq
        (by norm_num only : (34971 : ℝ) < (15188 : ℝ) * (115129 / 50000))).le

/-- Under GRH, q ≥ 10^20121 and H proper, a coprime prime outside H exists
through (4/5)(log q-2)². Convert the exact decimal entrance to log q > 46330.
This is the decimal proper-subgroup interface for the signed profile. -/
theorem exists_prime_outside_le_gamma_four_fifths_minus_two_20121 {q : ℕ} (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hq : 10 ^ 20121 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q - 2) ^ 2 := by
  have hq0 : q ≠ 0 :=
    Nat.ne_zero_of_lt ((pow_pos (by norm_num only : (0 : ℕ) < 10) 20121).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  apply exists_prime_outside_le_gamma_four_fifths_log_minus_two H hH hGRH
  exact
    (Analysis.log_nat_gt_of_decimal_lower (by norm_num only : 0 < 20121) hq
        (by norm_num only : (46330 : ℝ) < (20121 : ℝ) * (115129 / 50000))).le

/-- Under GRH, q ≥ 10^22097 and H proper, a coprime prime outside H exists
through (4/5)(log q-log log q)². Convert the exact decimal entrance to log q > 50880.
This is the decimal proper-subgroup interface for the signed profile. -/
theorem exists_prime_outside_le_gamma_four_fifths_minus_loglog_22097 {q : ℕ}
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 22097 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        ¬residueInSubgroup q H p ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q - Real.log (Real.log q)) ^ 2 := by
  have hq0 : q ≠ 0 :=
    Nat.ne_zero_of_lt ((pow_pos (by norm_num only : (0 : ℕ) < 10) 22097).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  apply exists_prime_outside_le_gamma_four_fifths_log_minus_loglog H hH hGRH
  exact
    (Analysis.log_nat_gt_of_decimal_lower (by norm_num only : 0 < 22097) hq
        (by norm_num only : (50880 : ℝ) < (22097 : ℝ) * (115129 / 50000))).le

end PseudoPrime.LLS.PaperStatements
