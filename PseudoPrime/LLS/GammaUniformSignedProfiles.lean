/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSignedShiftBounds
public import PseudoPrime.LLS.GammaUniformScaleExcessBounds
public import PseudoPrime.Analysis.GammaUniformSignedProfiles

/-! # Concrete signed logarithmic corrections for coefficient four fifths

A positive constant correction lowers the logarithmic entrance to 34971.
A negative log-log correction gives a smaller pointwise cutoff from 50880.
Both proofs bound the actual nonunit loss on the entire stated half-line.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, nonzero q, log q ≥ 34971 and H proper, a prime coprime to q
outside H exists through (4/5)(log q+29)². Apply the independent-scale witness
with the certified local allowance. This retains coefficient 0.8 at a smaller entrance. -/
theorem exists_prime_outside_le_gamma_four_fifths_log_plus_twentyNine {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 34971 ≤ Real.log q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q + 29) ^ 2 := by
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have ht := Real.log_le_sub_one_of_pos hqpos
  have hq : 20000 ≤ q := by exact_mod_cast (show (20000 : ℝ) ≤ q by linarith only [ht, hL])
  apply
    exists_prime_outside_le_gamma_four_fifths_scale hq H hH hGRH
      (show 35000 ≤ Real.log q + 29 by linarith only [hL])
      (show Real.log q ≤ Real.log q + 29 + 2 by linarith only)
  have hlocal := Analysis.gamma_commonFactor_budget_log_plus_twentyNine hL
  dsimp only at hlocal
  linarith only [hlocal, hL]

/-- Under GRH, nonzero q, log q ≥ 50880 and H proper, a prime coprime to q
outside H exists through (4/5)(log q-log log q)². Use the signed-scale witness,
actual local allowance, scale excess and affine logarithm majorant.
This gives a strictly smaller upper bound on the entire stated half-line. -/
theorem exists_prime_outside_le_gamma_four_fifths_log_minus_loglog {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 50880 ≤ Real.log q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        ¬residueInSubgroup q H p ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q - Real.log (Real.log q)) ^ 2 := by
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have ht := Real.log_le_sub_one_of_pos hqpos
  have hq : 20000 ≤ q := by exact_mod_cast (show (20000 : ℝ) ≤ q by linarith only [ht, hL])
  obtain ⟨hT, hlocal, hexcess⟩ :=
    Analysis.gamma_log_minus_loglog_scale_bounds (show 44739 ≤ Real.log q by linarith only [hL])
  apply exists_prime_outside_le_gamma_four_fifths_signed_scale hq H hH hGRH hT
  have hlog := Analysis.log_le_linear_tenThousand (show 0 < Real.log q by linarith only [hL])
  linarith only [hlocal, hexcess, hlog, hL]

end PseudoPrime.LLS.PaperStatements
