/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.AffineLogarithmicTailBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaWitnessBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaMaximumBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaNonOneProfileBounds

/-! # Analytic tails of squared affine-logarithmic quadratic witness fits -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The logarithm of 10000 is at most ten. Compare with 16384 = 2^14
and use the upper bound on log two. This supplies the initial logarithmic
estimate for the four quadratic fitting-root continuation certificates. -/
theorem qFit_log_ten_thousand_le_ten : Real.log (10000 : ℝ) ≤ 10 := by
  have h :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 10000) (by norm_num only : (10000 : ℝ) ≤ 16384)
  rw [show (16384 : ℝ) = 2 ^ 14 by norm_num only, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

/-- With rational a ≥ 1789/2000, the continuation guards at L = 10000
make the fitting square dominate (4/5)L² for every L ≥ 10000.
The rational comparison slope has square above 4/5, so no irrational coefficient is needed. -/
theorem quadratic_gamma_square_le_affine_root {L : ℝ} {a b c : ℚ} (ha : 1789 / 2000 ≤ a)
    (hL : 10000 ≤ L) (hb : -((a - 1789 / 2000 : ℚ) : ℝ) * 10000 ≤ (b : ℝ))
    (hbase : (1789 / 2000 : ℝ) * 10000 ≤ affineLogarithmicRoot 10000 a b c) :
    (4 / 5 : ℝ) * L ^ 2 ≤ affineLogarithmicRoot L a b c ^ 2 := by
  have hs :=
    affineLogarithmicSquare_ge_linear_square_on_tail (r := 1789 / 2000) (by norm_num only) ha
      (by norm_num only : (0 : ℝ) < 10000) hL hb
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hbase)
  have hc : (4 / 5 : ℝ) ≤ ((1789 / 2000 : ℚ) : ℝ) ^ 2 := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg L)).trans hs

/-- At L = 10000, this quadratic fitting root dominates (1789/2000)L.
The negative log coefficient permits use of the upper logarithm bound.
This verifies the initial guard for its analytic upper interval. -/
theorem qFit_negNineTenths_at_ten_thousand :
    (1789 / 2000 : ℝ) * 10000 ≤
      affineLogarithmicRoot 10000 (9 / 10) (-166161 / 50000) (6168143 / 1000000) := by
  have h := qFit_log_ten_thousand_le_ten
  norm_num only [affineLogarithmicRoot, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  linarith only [h]

/-- For L ≥ 10000, this fitted square dominates the established Gamma bound.
Apply the rational-slope continuation criterion with its verified initial guard.
This is the numerical transfer used by the corresponding actual witness theorem. -/
theorem gamma_square_le_qFit_negNineTenths {L : ℝ} (hL : 10000 ≤ L) :
    (4 / 5 : ℝ) * L ^ 2 ≤
      affineLogarithmicRoot L (9 / 10) (-166161 / 50000) (6168143 / 1000000) ^ 2 := by
  exact
    quadratic_gamma_square_le_affine_root (by norm_num only) hL
      (by norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg])
      qFit_negNineTenths_at_ten_thousand

/-- At L = 10000, this quadratic fitting root dominates (1789/2000)L.
The negative log coefficient permits use of the upper logarithm bound.
This verifies the initial guard for its analytic upper interval. -/
theorem qFit_negOne_at_ten_thousand :
    (1789 / 2000 : ℝ) * 10000 ≤
      affineLogarithmicRoot 10000 1 (-991489 / 250000) (6720131 / 1000000) := by
  have h := qFit_log_ten_thousand_le_ten
  norm_num only [affineLogarithmicRoot, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  linarith only [h]

/-- For L ≥ 10000, this fitted square dominates the established Gamma bound.
Apply the rational-slope continuation criterion with its verified initial guard.
This is the numerical transfer used by the corresponding actual witness theorem. -/
theorem gamma_square_le_qFit_negOne {L : ℝ} (hL : 10000 ≤ L) :
    (4 / 5 : ℝ) * L ^ 2 ≤ affineLogarithmicRoot L 1 (-991489 / 250000) (6720131 / 1000000) ^ 2 := by
  exact
    quadratic_gamma_square_le_affine_root (by norm_num only) hL
      (by norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg])
      qFit_negOne_at_ten_thousand

/-- At L = 10000, this quadratic fitting root dominates (1789/2000)L.
The negative log coefficient permits use of the upper logarithm bound.
This verifies the initial guard for its analytic upper interval. -/
theorem qFit_nonOneNineTenths_at_ten_thousand :
    (1789 / 2000 : ℝ) * 10000 ≤
      affineLogarithmicRoot 10000 (9 / 10) (-1439941 / 500000) (908039 / 250000) := by
  have h := qFit_log_ten_thousand_le_ten
  norm_num only [affineLogarithmicRoot, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  linarith only [h]

/-- For L ≥ 10000, this fitted square dominates the established Gamma bound.
Apply the rational-slope continuation criterion with its verified initial guard.
This is the numerical transfer used by the corresponding actual witness theorem. -/
theorem gamma_square_le_qFit_nonOneNineTenths {L : ℝ} (hL : 10000 ≤ L) :
    (4 / 5 : ℝ) * L ^ 2 ≤
      affineLogarithmicRoot L (9 / 10) (-1439941 / 500000) (908039 / 250000) ^ 2 := by
  exact
    quadratic_gamma_square_le_affine_root (by norm_num only) hL
      (by norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg])
      qFit_nonOneNineTenths_at_ten_thousand

/-- At L = 10000, this quadratic fitting root dominates (1789/2000)L.
The negative log coefficient permits use of the upper logarithm bound.
This verifies the initial guard for its analytic upper interval. -/
theorem qFit_nonOneOne_at_ten_thousand :
    (1789 / 2000 : ℝ) * 10000 ≤
      affineLogarithmicRoot 10000 1 (-1720413 / 500000) (1005597 / 250000) := by
  have h := qFit_log_ten_thousand_le_ten
  norm_num only [affineLogarithmicRoot, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg]
  linarith only [h]

/-- For L ≥ 10000, this fitted square dominates the established Gamma bound.
Apply the rational-slope continuation criterion with its verified initial guard.
This is the numerical transfer used by the corresponding actual witness theorem. -/
theorem gamma_square_le_qFit_nonOneOne {L : ℝ} (hL : 10000 ≤ L) :
    (4 / 5 : ℝ) * L ^ 2 ≤ affineLogarithmicRoot L 1 (-1720413 / 500000) (1005597 / 250000) ^ 2 := by
  exact
    quadratic_gamma_square_le_affine_root (by norm_num only) hL
      (by norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg])
      qFit_nonOneOne_at_ten_thousand

end PseudoPrime.Analysis

namespace PseudoPrime.PseudoSquare

/-- Under GRH, an odd nonsquare n ≥ 10^19978 has an odd prime
negative Jacobi witness bounded by this squared affine-logarithmic fit.
Transfer the actual Gamma witness using the decimal logarithm certificate.
This proves its upper interval; the gap above the finite fitting domain remains separate. -/
theorem exists_prime_neg_one_witness_le_qFit_negNineTenths
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 19978 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤
          Analysis.affineLogarithmicRoot (Real.log n) (9 / 10) (-166161 / 50000)
              (6168143 / 1000000) ^
            2 ∧
        jacobiSym n p = -1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_neg_one_witness_le_gamma_19978 hGRH hn hns hN
  have hL : 10000 ≤ Real.log n :=
    (by norm_num only : (10000 : ℝ) ≤ 46000).trans
      (Analysis.log_nat_gt_46000_of_decimal_19978 hN).le
  exact ⟨p, hp, ho, hb.trans (Analysis.gamma_square_le_qFit_negNineTenths hL), hv⟩

/-- Under GRH, an odd nonsquare n ≥ 10^19978 has an odd prime
negative Jacobi witness bounded by this squared affine-logarithmic fit.
Transfer the actual Gamma witness using the decimal logarithm certificate.
This proves its upper interval; the gap above the finite fitting domain remains separate. -/
theorem exists_prime_neg_one_witness_le_qFit_negOne
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 19978 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤
          Analysis.affineLogarithmicRoot (Real.log n) 1 (-991489 / 250000) (6720131 / 1000000) ^ 2 ∧
        jacobiSym n p = -1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_neg_one_witness_le_gamma_19978 hGRH hn hns hN
  have hL : 10000 ≤ Real.log n :=
    (by norm_num only : (10000 : ℝ) ≤ 46000).trans
      (Analysis.log_nat_gt_46000_of_decimal_19978 hN).le
  exact ⟨p, hp, ho, hb.trans (Analysis.gamma_square_le_qFit_negOne hL), hv⟩

/-- Under GRH, an odd nonsquare n ≥ 10^15639 has an odd prime
non-one Jacobi witness bounded by this squared affine-logarithmic fit.
Transfer the actual Gamma witness using the decimal logarithm certificate.
This proves its upper interval; the gap above the finite fitting domain remains separate. -/
theorem exists_prime_ne_one_witness_le_qFit_nonOneNineTenths
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 15639 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤
          Analysis.affineLogarithmicRoot (Real.log n) (9 / 10) (-1439941 / 500000)
              (908039 / 250000) ^
            2 ∧
        jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_ne_one_witness_le_gamma_15639 hGRH hn hns hN
  have hL : 10000 ≤ Real.log n :=
    (by norm_num only : (10000 : ℝ) ≤ 36010).trans (log_nat_gt_36010_of_decimal_15639 hN).le
  exact ⟨p, hp, ho, hb.trans (Analysis.gamma_square_le_qFit_nonOneNineTenths hL), hv⟩

/-- Under GRH, an odd nonsquare n ≥ 10^15639 has an odd prime
non-one Jacobi witness bounded by this squared affine-logarithmic fit.
Transfer the actual Gamma witness using the decimal logarithm certificate.
This proves its upper interval; the gap above the finite fitting domain remains separate. -/
theorem exists_prime_ne_one_witness_le_qFit_nonOneOne
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 15639 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤
          Analysis.affineLogarithmicRoot (Real.log n) 1 (-1720413 / 500000) (1005597 / 250000) ^ 2 ∧
        jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_ne_one_witness_le_gamma_15639 hGRH hn hns hN
  have hL : 10000 ≤ Real.log n :=
    (by norm_num only : (10000 : ℝ) ≤ 36010).trans (log_nat_gt_36010_of_decimal_15639 hN).le
  exact ⟨p, hp, ho, hb.trans (Analysis.gamma_square_le_qFit_nonOneOne hL), hv⟩

/-- Under the same GRH, odd nonsquare and decimal-start assumptions,
the least odd-prime negative witness satisfies the fitted square bound.
Minimize the proved prime witness; no larger starting value is introduced. -/
theorem primeNegOneWitness_cast_le_qFit_negNineTenths
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 19978 ≤ n)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      Analysis.affineLogarithmicRoot (Real.log n) (9 / 10) (-166161 / 50000) (6168143 / 1000000) ^
        2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_neg_one_witness_le_qFit_negNineTenths hGRH hn hns hN
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH for B ≥ 10^19978, the finite negative witness maximum
satisfies the same fitted formula as the pointwise bound. Transfer the established
Gamma finite maximum, which already includes every smaller admissible input.
This introduces neither a weaker formula nor an extra starting-value restriction. -/
theorem QNegOne_le_qFit_negNineTenths {B : ℕ} (hB : 10 ^ 19978 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤
      Analysis.affineLogarithmicRoot (Real.log B) (9 / 10) (-166161 / 50000) (6168143 / 1000000) ^
        2 := by
  have hb := (gamma_formula_explicit_19978 hB hGRH).2
  have hL : 10000 ≤ Real.log B :=
    (by norm_num only : (10000 : ℝ) ≤ 46000).trans
      (Analysis.log_nat_gt_46000_of_decimal_19978 hB).le
  exact hb.trans (Analysis.gamma_square_le_qFit_negNineTenths hL)

/-- Under the same GRH, odd nonsquare and decimal-start assumptions,
the least odd-prime negative witness satisfies the fitted square bound.
Minimize the proved prime witness; no larger starting value is introduced. -/
theorem primeNegOneWitness_cast_le_qFit_negOne
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 19978 ≤ n)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      Analysis.affineLogarithmicRoot (Real.log n) 1 (-991489 / 250000) (6720131 / 1000000) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_neg_one_witness_le_qFit_negOne hGRH hn hns hN
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH for B ≥ 10^19978, the finite negative witness maximum
satisfies the same fitted formula as the pointwise bound. Transfer the established
Gamma finite maximum, which already includes every smaller admissible input.
This introduces neither a weaker formula nor an extra starting-value restriction. -/
theorem QNegOne_le_qFit_negOne {B : ℕ} (hB : 10 ^ 19978 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤
      Analysis.affineLogarithmicRoot (Real.log B) 1 (-991489 / 250000) (6720131 / 1000000) ^ 2 := by
  have hb := (gamma_formula_explicit_19978 hB hGRH).2
  have hL : 10000 ≤ Real.log B :=
    (by norm_num only : (10000 : ℝ) ≤ 46000).trans
      (Analysis.log_nat_gt_46000_of_decimal_19978 hB).le
  exact hb.trans (Analysis.gamma_square_le_qFit_negOne hL)

/-- Under the same GRH, odd nonsquare and decimal-start assumptions,
the least odd-prime non-one witness satisfies the fitted square bound.
Minimize the proved prime witness; no larger starting value is introduced. -/
theorem primeNeOneWitness_cast_le_qFit_nonOneNineTenths
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 15639 ≤ n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      Analysis.affineLogarithmicRoot (Real.log n) (9 / 10) (-1439941 / 500000) (908039 / 250000) ^
        2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_ne_one_witness_le_qFit_nonOneNineTenths hGRH hn hns hN
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH for B ≥ 10^15639, the finite non-one witness maximum
satisfies the same fitted formula as the pointwise bound. Transfer the established
Gamma finite maximum, which already includes every smaller admissible input.
This introduces neither a weaker formula nor an extra starting-value restriction. -/
theorem QNeOne_le_qFit_nonOneNineTenths {B : ℕ} (hB : 10 ^ 15639 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤
      Analysis.affineLogarithmicRoot (Real.log B) (9 / 10) (-1439941 / 500000) (908039 / 250000) ^
        2 := by
  have hb := QNeOne_le_gamma_15639 hB hGRH
  have hL : 10000 ≤ Real.log B :=
    (by norm_num only : (10000 : ℝ) ≤ 36010).trans (log_nat_gt_36010_of_decimal_15639 hB).le
  exact hb.trans (Analysis.gamma_square_le_qFit_nonOneNineTenths hL)

/-- Under the same GRH, odd nonsquare and decimal-start assumptions,
the least odd-prime non-one witness satisfies the fitted square bound.
Minimize the proved prime witness; no larger starting value is introduced. -/
theorem primeNeOneWitness_cast_le_qFit_nonOneOne
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 15639 ≤ n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      Analysis.affineLogarithmicRoot (Real.log n) 1 (-1720413 / 500000) (1005597 / 250000) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_ne_one_witness_le_qFit_nonOneOne hGRH hn hns hN
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH for B ≥ 10^15639, the finite non-one witness maximum
satisfies the same fitted formula as the pointwise bound. Transfer the established
Gamma finite maximum, which already includes every smaller admissible input.
This introduces neither a weaker formula nor an extra starting-value restriction. -/
theorem QNeOne_le_qFit_nonOneOne {B : ℕ} (hB : 10 ^ 15639 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤
      Analysis.affineLogarithmicRoot (Real.log B) 1 (-1720413 / 500000) (1005597 / 250000) ^ 2 := by
  have hb := QNeOne_le_gamma_15639 hB hGRH
  have hL : 10000 ≤ Real.log B :=
    (by norm_num only : (10000 : ℝ) ≤ 36010).trans (log_nat_gt_36010_of_decimal_15639 hB).le
  exact hb.trans (Analysis.gamma_square_le_qFit_nonOneOne hL)

end PseudoPrime.PseudoSquare
