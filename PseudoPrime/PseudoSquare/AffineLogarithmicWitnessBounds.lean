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
public import PseudoPrime.Analysis.AffineLogarithmicWitnessBounds

/-! # Analytic tails of squared affine-logarithmic quadratic witness fits -/

@[expose] public section

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
