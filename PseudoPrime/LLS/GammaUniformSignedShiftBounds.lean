/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformScaleBounds
public import PseudoPrime.LLS.GammaUniformLocalBudgetParameters
public import PseudoPrime.Analysis.GammaUniformSignedShiftBounds

/-! # Smaller Gamma cutoffs with a negative constant correction

An independent nonunit-loss budget applies to any scale and cutoff satisfying
the root and logarithmic bounds. The choice T=log q-2 gives a strictly smaller
coefficient-four-fifths cutoff from log q ≥ 46330.
-/

@[expose] public section

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
