/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformReducedStart
public import PseudoPrime.LLS.GammaUniformLocalBudgetParameters
public import PseudoPrime.Analysis.GammaUniformTightStart

/-! # Tighter uniform coefficient-four-fifths starting value

Refined rational square-root and logarithmic-ratio certificates lower the common
logarithmic start to 45561. The decimal logarithm gives 10^19787 for subgroup,
general-character and least-prime witnesses, with the same analytic kernel.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, nonzero q, log q ≥ 35000 and H proper, a strict budget for the
actual normalized nonunit loss gives a unit prime outside H through (4/5)(log q)^2.
Contradict the uniform ramp comparison and the main-term gap.
This internal interface keeps the witness proof independent of the local-budget parameters. -/
private theorem exists_prime_outside_of_uniform_gamma_local_budget {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 35000 ≤ Real.log q)
    (hbudget :
      (40159 / 900 : ℝ) +
          2 *
            (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum
                ((32 / 99 : ℝ) * (Real.log q) ^ 2) ((4 / 5 : ℝ) * (Real.log q) ^ 2) q /
              Real.sqrt ((32 / 99 : ℝ) * (Real.log q) ^ 2)) <
        Real.log q / 795) :
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
  have hc := gamma_ramp_subgroup_comparison_uniform hq H hH hGRH hL hsmall
  have he :
    (99 / 40 : ℝ) * ((32 / 99 : ℝ) * (Real.log q) ^ 2) = (4 / 5 : ℝ) * (Real.log q) ^ 2 := by ring
  dsimp only at hc
  rw [he] at hc
  have hm := Analysis.nonOne_main_term_gap (show 0 < Real.log q by linarith only [hL])
  linarith only [hc, hbudget, hm]

/-- Under GRH, nonzero q, log q ≥ 45561 and H proper, a unit prime outside H
exists through (4/5)(log q)^2. Apply the parameterized local allowance 63960/5041
and the rational strict error budget to the common contradiction interface.
No additional arithmetic or analytic premise remains in this log entrance. -/
theorem exists_prime_outside_le_gamma_four_fifths_log_45561 {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 45561 ≤ Real.log q) :
    ∃ p : ℕ,
      p.Prime ∧ ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 := by
  apply
    exists_prime_outside_of_uniform_gamma_local_budget H hH hGRH
      ((by norm_num only : (35000 : ℝ) ≤ 45561).trans hL)
  have hD :=
    Analysis.gamma_commonFactor_budget_of_log_ge_44739
      ((by norm_num only : (44739 : ℝ) ≤ 45561).trans hL)
  have hE := Analysis.gamma_uniform_error_budget_of_ge_45561 hL
  have he :
    (99 / 40 : ℝ) * ((32 / 99 : ℝ) * (Real.log q) ^ 2) = (4 / 5 : ℝ) * (Real.log q) ^ 2 := by ring
  dsimp only at hD
  rw [he] at hD
  linarith only [hD, hE]

/-- Under GRH, q ≥ 10^19787 and H any proper subgroup of the units,
there is a prime coprime to q outside H at most (4/5)(log q)^2.
Convert the decimal threshold to log q > 45561 and apply the tighter log entrance.
The starting value is uniform in the index and in the level's factorization type. -/
theorem exists_prime_outside_le_gamma_four_fifths_19787 {q : ℕ} (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hq : 10 ^ 19787 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧ ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 := by
  have hq0 : q ≠ 0 :=
    Nat.ne_zero_of_lt ((pow_pos (by norm_num only : (0 : ℕ) < 10) 19787).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  exact
    exists_prime_outside_le_gamma_four_fifths_log_45561 H hH hGRH
      (Analysis.log_nat_gt_45561_of_decimal_19787 hq).le

end PseudoPrime.LLS.PaperStatements
