/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.AffineLogarithmicTailBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianWitnessBounds
public import PseudoPrime.Analysis.PrimeTestBoundsMillerRabinAffineLogarithmicWitnessBounds

/-! # Analytic tails of two squared affine-logarithmic Miller--Rabin fits -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite n ≥ 10^97826087 has a prime strong Miller--Rabin
witness through the a = 9/10 squared affine-logarithmic fit. Transfer the established
Gaussian witness using its logarithmic threshold and the fitting-root comparison.
This proves only the large-input tail, not the gap above the finite fitting domain. -/
theorem exists_prime_witness_le_mrFit_nineTenths {n : ℕ} (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 97826087 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          Analysis.affineLogarithmicRoot (Real.log n) (9 / 10) (-110659 / 20000)
              (6178681 / 1000000) ^
            2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_gaussian hnOdd hnComposite hGRH hn
  have hL : 1000 ≤ Real.log n :=
    (by norm_num only : (1000 : ℝ) ≤ 225000000).trans (Analysis.gaussianMR_log_cutoff hn)
  exact ⟨p, hp, hb.trans (Analysis.gaussian_square_le_mrFit_nineTenths hL), hf⟩

/-- Under GRH, an odd composite n ≥ 10^97826087 has a prime strong Miller--Rabin
witness through the a = 1 squared affine-logarithmic fit. Use the same Gaussian
witness and the second root comparison. The small-to-large interval remains separate. -/
theorem exists_prime_witness_le_mrFit_one {n : ℕ} (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 97826087 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          Analysis.affineLogarithmicRoot (Real.log n) 1 (-96439 / 15625) (1681239 / 250000) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_gaussian hnOdd hnComposite hGRH hn
  have hL : 1000 ≤ Real.log n :=
    (by norm_num only : (1000 : ℝ) ≤ 225000000).trans (Analysis.gaussianMR_log_cutoff hn)
  exact ⟨p, hp, hb.trans (Analysis.gaussian_square_le_mrFit_one hL), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
