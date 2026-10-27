/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSubgroupComparison
public import PseudoPrime.LLS.GammaUniformSubgroupNumerics

/-! # Uniform coefficient four-fifths for primes outside proper subgroups

Under GRH, every proper subgroup of the unit group at a sufficiently large
level has an outside prime through (4/5)(log q)^2. The starting value is
independent of the subgroup index and of the factorization type of the level.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, q ≠ 0, log q ≥ 46000 and H a proper subgroup of the units,
there is a prime p coprime to q outside H with p ≤ (4/5)(log q)^2.
Contradict the uniform ramp comparison using the certified local and scalar budgets.
This is the logarithmic entrance for the improved LLS Theorem 1.1 bound. -/
theorem exists_prime_outside_le_gamma_four_fifths_log {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 46000 ≤ Real.log q) :
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
      ((by norm_num only : (35000 : ℝ) ≤ 46000).trans hL) hsmall
  have hD := Analysis.gamma_commonFactor_budget_of_log_ge hL
  have he := Analysis.gamma_uniform_error_budget hL
  have hm := Analysis.nonOne_main_term_gap (show 0 < Real.log q by linarith only [hL])
  linarith only [hc, hD, he, hm]

/-- Under GRH, q ≥ 10^20000 and H any proper subgroup of the units,
there is a prime p coprime to q outside H with p ≤ (4/5)(log q)^2.
Convert the decimal start to log q > 46000 and apply the logarithmic theorem.
The start is uniform in the index; no parity, squarefree or small-factor premise remains. -/
theorem exists_prime_outside_le_gamma_four_fifths {q : ℕ} (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 20000 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧ ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 := by
  have hq0 : q ≠ 0 :=
    Nat.ne_zero_of_lt ((pow_pos (by norm_num only : (0 : ℕ) < 10) 20000).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  exact
    exists_prime_outside_le_gamma_four_fifths_log H hH hGRH
      (Analysis.log_nat_gt_46000_of_decimal hq).le

end PseudoPrime.LLS.PaperStatements
