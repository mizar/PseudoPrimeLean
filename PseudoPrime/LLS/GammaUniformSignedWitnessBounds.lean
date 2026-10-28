/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSignedProfiles
public import PseudoPrime.LLS.GammaUniformTightStart
public import PseudoPrime.Analysis.LogarithmicShiftBounds
public import PseudoPrime.LLS.GammaUniformSignedWitnessBounds2

/-! # Decimal and character interfaces for rational signed Gamma profiles

The concrete rational triples (4/5,0,29), (4/5,0,-2) and (4/5,-1,0)
have decimal entrances 15188, 20121 and 22097. General characters and least
outside primes use the same cutoffs. A rational-parameter interface retains
the actual analytic budget for further coefficient optimization.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH and q ≥ 20000, rational a > 0 and signed rational b,c give
a coprime outside prime through a(log q+b log log q+c)² whenever the displayed
scale entrance and strict error budget hold. Rescale the common Gamma scale.
This research interface separates rational coefficient selection from the actual analytic budget. -/
theorem exists_prime_outside_le_rational_logarithmic_shift {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {a b c : ℚ} (ha : 0 < a)
    (hT :
      35000 ≤ Real.sqrt ((5 / 4 : ℝ) * (a : ℝ)) * Analysis.logarithmicShiftRoot (Real.log q) b c)
    (hbudget :
      let T := Real.sqrt ((5 / 4 : ℝ) * (a : ℝ)) * Analysis.logarithmicShiftRoot (Real.log q) b c;
      (11783423 / 25000000 : ℝ) * Real.log q + gammaScaleExcess (Real.log q) T + 40159 / 900 +
          2 *
            (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum ((32 / 99 : ℝ) * T ^ 2)
                ((4 / 5 : ℝ) * T ^ 2) q /
              Real.sqrt ((32 / 99 : ℝ) * T ^ 2)) <
        (11783423 / 25000000 + 1 / 795 : ℝ) * T) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        ¬residueInSubgroup q H p ∧
        (p : ℝ) ≤ Analysis.logarithmicShiftCutoff (Real.log q) a b c := by
  let T := Real.sqrt ((5 / 4 : ℝ) * (a : ℝ)) * Analysis.logarithmicShiftRoot (Real.log q) b c
  have haR : (0 : ℝ) ≤ (5 / 4 : ℝ) * (a : ℝ) :=
    mul_nonneg (by norm_num only) (by exact_mod_cast ha.le)
  have he : (4 / 5 : ℝ) * T ^ 2 = Analysis.logarithmicShiftCutoff (Real.log q) a b c := by
    dsimp only [T, Analysis.logarithmicShiftCutoff]
    rw [mul_pow, Real.sq_sqrt haR]
    ring
  obtain ⟨p, hp, hd, hout, hb⟩ :=
    exists_prime_outside_le_gamma_four_fifths_signed_scale hq H hH hGRH hT hbudget
  exact ⟨p, hp, hd, hout, he ▸ hb⟩

end PseudoPrime.LLS.PaperStatements
