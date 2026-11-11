/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsRemainder
public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundGammaIntegral

/-! # Three-elevenths bound from the Gamma-remainder integral -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The imaginary Gamma-logarithm remainder equals the negative integral of
the positive Euler–Maclaurin kernel at the required heights. This proposition
specifies the remaining Gamma integral identity; it does not assert a proof. -/
def BacklundGammaRemainderIdentity : Prop :=
  ∀ t : ℝ,
    2 * Real.pi * Real.exp 1 ≤ t →
      backlundGammaRemainder t =
        -(∫ x in Set.Ioi (0 : ℝ), backlundGammaWeight x * backlundGammaKernel (1 / 4) (t / 2) x)

/-- The Gamma-remainder integral identity supplies the signed remainder
bound needed by the zero-count argument. The integrability, positivity and
explicit `1/(4t)` integral bound are proved independently. -/
theorem gamma_remainder_bounds_of_integral (hI : BacklundGammaRemainderIdentity) :
    ∀ t : ℝ,
      2 * Real.pi * Real.exp 1 ≤ t →
        -(1 / (4 * t)) ≤ backlundGammaRemainder t ∧ backlundGammaRemainder t ≤ 0 := by
  intro t ht
  have hbase : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  have h := backlundGammaWeight_integral_height (hbase.trans_le ht)
  rw [hI t ht]
  constructor <;> linarith only [h.2.1, h.2.2]

/-- Under GRH, the Euler-normalized Riemann–von Mangoldt identity and the
Gamma-remainder integral identity imply the least-prime `3/11` witness
bound for every odd composite. The integral bound, Backlund phase estimate,
coarse zero count and classification are discharged internally. -/
theorem three_eleven_least_of_gamma_integral {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hV : EulerRiemannVonMangoldt)
    (hI : BacklundGammaRemainderIdentity) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact
    three_eleven_least_of_gamma_remainder hn ho hc hGRH hV (gamma_remainder_bounds_of_integral hI)

end PseudoPrime.PrimeTestBounds.MillerRabin
