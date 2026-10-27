/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.AffineLogarithmicTailBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianWitnessBounds

/-! # Analytic tails of two squared affine-logarithmic Miller--Rabin fits -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The logarithm of 1000 is at most seven. Compare with 1024 = 2^10
and use the certified upper bound on log two. This checks a convenient
starting logarithmic level for the Miller--Rabin fitting-root comparisons. -/
theorem mrFit_log_thousand_le_seven : Real.log (1000 : ℝ) ≤ 7 := by
  have h :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 1000) (by norm_num only : (1000 : ℝ) ≤ 1024)
  rw [show (1024 : ℝ) = 2 ^ 10 by norm_num only, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

/-- At L = 1000, the a = 9/10 fitting root dominates (4/5)L.
Its log coefficient is negative, so the upper logarithm bound gives a lower root bound.
This checks the initial inequality for analytic continuation. -/
theorem mrFit_nineTenths_at_thousand :
    (4 / 5 : ℝ) * 1000 ≤
      affineLogarithmicRoot 1000 (9 / 10) (-110659 / 20000) (6178681 / 1000000) := by
  have h := mrFit_log_thousand_le_seven
  norm_num only [affineLogarithmicRoot, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  linarith only [h]

/-- For L ≥ 1000, the a = 9/10 fitting square dominates the Gaussian square.
Apply the general continuation criterion with comparison slope 4/5.
This permits transfer of the established coefficient 16/25 witness bound. -/
theorem gaussian_square_le_mrFit_nineTenths {L : ℝ} (hL : 1000 ≤ L) :
    (16 / 25 : ℝ) * L ^ 2 ≤
      affineLogarithmicRoot L (9 / 10) (-110659 / 20000) (6178681 / 1000000) ^ 2 := by
  have h :=
    affineLogarithmicSquare_ge_linear_square_on_tail (r := 4 / 5) (a := 9 / 10) (b :=
      -110659 / 20000) (c := 6178681 / 1000000) (by norm_num only) (by norm_num only)
      (by norm_num only : (0 : ℝ) < 1000) hL
      (by norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg])
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using mrFit_nineTenths_at_thousand)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
  exact h

/-- At L = 1000, the a = 1 fitting root dominates (4/5)L.
Use the same upper logarithm bound with its negative logarithmic coefficient.
This is the second fitting root's initial continuation certificate. -/
theorem mrFit_one_at_thousand :
    (4 / 5 : ℝ) * 1000 ≤ affineLogarithmicRoot 1000 1 (-96439 / 15625) (1681239 / 250000) := by
  have h := mrFit_log_thousand_le_seven
  norm_num only [affineLogarithmicRoot, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  linarith only [h]

/-- For L ≥ 1000, the a = 1 fitting square dominates the Gaussian square.
Apply the continuation criterion with comparison slope 4/5 and the checked initial root.
This transfers the Gaussian witness to the second fitted formula. -/
theorem gaussian_square_le_mrFit_one {L : ℝ} (hL : 1000 ≤ L) :
    (16 / 25 : ℝ) * L ^ 2 ≤ affineLogarithmicRoot L 1 (-96439 / 15625) (1681239 / 250000) ^ 2 := by
  have h :=
    affineLogarithmicSquare_ge_linear_square_on_tail (r := 4 / 5) (a := 1) (b := -96439 / 15625)
      (c := 1681239 / 250000) (by norm_num only) (by norm_num only)
      (by norm_num only : (0 : ℝ) < 1000) hL
      (by norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg])
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using mrFit_one_at_thousand)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
  exact h

end PseudoPrime.Analysis

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
