/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformWitnessBounds
public import PseudoPrime.Analysis.QuadraticGammaDecimalRefinement
public import PseudoPrime.Analysis.GammaUniformReducedStart

/-! # A smaller uniform Gamma starting value

The same analytic budgets close from log q ≥ 45731. The certified decimal
logarithm then gives q ≥ 10^19861 for subgroup, character and least-prime witnesses.
Existing wrappers at 10^20000 remain available.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, q ≠ 0, log q ≥ 45731 and H proper, there is a unit prime
outside H through (4/5)(log q)^2. The same local allowance is valid from 42875,
and the fixed error closes at 45731. Apply the uniform ramp contradiction.
This strengthens the logarithmic starting value without changing the kernel. -/
theorem exists_prime_outside_le_gamma_four_fifths_log_45731 {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 45731 ≤ Real.log q) :
    ∃ p : ℕ,
      p.Prime ∧ ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 := by
  classical
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have ht := Real.log_le_sub_one_of_pos hq0
  have hq : 20000 ≤ q := by exact_mod_cast (show (20000 : ℝ) ≤ q by linarith only [ht, hL])
  by_contra hn
  have hsmall (p : ℕ) (hp : p.Prime) (hd : ¬p ∣ q) (hb : (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2) :
    residueInSubgroup q H p := by
    by_contra hout
    exact hn ⟨p, hp, hd, hout, hb⟩
  have hc :=
    gamma_ramp_subgroup_comparison_uniform hq H hH hGRH
      ((by norm_num only : (35000 : ℝ) ≤ 45731).trans hL) hsmall
  have hD :=
    Analysis.gamma_commonFactor_budget_of_log_ge_42875
      ((by norm_num only : (42875 : ℝ) ≤ 45731).trans hL)
  have he := Analysis.gamma_uniform_error_budget_of_ge_45731 hL
  have hm := Analysis.nonOne_main_term_gap (show 0 < Real.log q by linarith only [hL])
  linarith only [hc, hD, he, hm]

/-- Under GRH, q ≥ 10^19861 and H any proper subgroup of the units,
there is a prime coprime to q outside H at most (4/5)(log q)^2.
Convert the decimal threshold to log q > 45731 and apply the reduced log entrance.
The bound is uniform in the index and has no factorization-type premise. -/
theorem exists_prime_outside_le_gamma_four_fifths_19861 {q : ℕ} (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hq : 10 ^ 19861 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧ ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 := by
  have hq0 : q ≠ 0 :=
    Nat.ne_zero_of_lt ((pow_pos (by norm_num only : (0 : ℕ) < 10) 19861).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  exact
    exists_prime_outside_le_gamma_four_fifths_log_45731 H hH hGRH
      (Analysis.log_nat_gt_45731_of_decimal_19861 hq).le

end PseudoPrime.LLS.PaperStatements
