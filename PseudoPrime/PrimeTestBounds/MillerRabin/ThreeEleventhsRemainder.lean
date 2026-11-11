/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsThetaInputs
public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundThetaMainPart

/-! # Three-elevenths bound from a signed Gamma remainder -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the Euler-normalized Riemann–von Mangoldt identity and the
signed imaginary Stirling-remainder bounds imply the least-prime `3/11`
witness bound for every odd composite. The elementary Gamma main part and
the Backlund zero-count argument are handled internally. -/
theorem three_eleven_least_of_gamma_remainder {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hV : EulerRiemannVonMangoldt)
    (hR :
      ∀ t : ℝ,
        2 * Real.pi * Real.exp 1 ≤ t →
          -(1 / (4 * t)) ≤ backlundGammaRemainder t ∧ backlundGammaRemainder t ≤ 0) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  apply three_eleven_least_of_theta hn ho hc hGRH hV
  intro t ht
  have hbase : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  exact backlundTheta_error_of_signed_remainder (hbase.trans_le ht) (hR t ht).1 (hR t ht).2

end PseudoPrime.PrimeTestBounds.MillerRabin
