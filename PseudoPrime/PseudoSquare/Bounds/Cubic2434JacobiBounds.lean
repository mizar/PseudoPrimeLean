/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

public import PseudoPrime.PseudoSquare.Bounds.RationalCubicNegativeSupportBounds
public import PseudoPrime.LLS.Cubic2434LinearBounds
public import PseudoPrime.PseudoSquare.Bounds.RefinedConductorRadicalWitnessBounds

/-! # Improved cubic bounds with the exact squarefree-part logarithm -/

@[expose] public section

namespace PseudoPrime.PseudoSquare
/-- For the canonical positive decomposition n=s^2 d, log(s)=(log(n)-log(d))/2.
Prove s is nonzero from n>0, then take logarithms of the exact product.
This retains the squarefree logarithm in the exclusion budget. -/
theorem squareFactor_log_decomposition {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    Real.log bridge.squareFactor = (Real.log n - Real.log bridge.squarefreePart) / 2 := by
  have hs : bridge.squareFactor ≠ 0 := by
    intro hz
    have he := bridge.squarefreePart_sq_mul
    rw [hz, zero_pow (by norm_num only : 2 ≠ 0), zero_mul] at he
    exact hn.pos.ne' he.symm
  have he : (n : ℝ) = (bridge.squareFactor : ℝ) ^ 2 * bridge.squarefreePart := by
    exact_mod_cast bridge.squarefreePart_sq_mul.symm
  have hl := congrArg Real.log he
  rw [Real.log_mul (pow_ne_zero _ (Nat.cast_ne_zero.mpr hs))
    (Nat.cast_ne_zero.mpr bridge.squarefreePart_pos.ne'),Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl]
/-- The negative-support prime cost is at most (log(n)-log(d))/2.
Bound it by all distinct prime logarithms of s, then by log(s), and apply the
exact decomposition identity. No GRH or asymptotic assumption is used. -/
theorem negativeSquareFactorCost_le_log_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor ≤
      (Real.log n - Real.log bridge.squarefreePart) / 2 := by
  have hs : bridge.squareFactor ≠ 0 := by
    intro hz
    have he := bridge.squarefreePart_sq_mul
    rw [hz, zero_pow (by norm_num only : 2 ≠ 0), zero_mul] at he
    exact hn.pos.ne' he.symm
  have h := (negativeSquareFactorCost_le_full bridge.squarefreePart bridge.squareFactor).trans
    (AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log hs)
  rw [squareFactor_log_decomposition bridge] at h
  exact h
/-- The positive squarefree part has logarithm at most log(n).
Use the exact decomposition and nonnegativity of log(s).
This checks nonnegativity of the improved root's remaining budget. -/
theorem squarefree_log_le_input_log {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    Real.log bridge.squarefreePart ≤ Real.log n := by
  have hl := squareFactor_log_decomposition bridge
  linarith only [hl,Real.log_natCast_nonneg bridge.squareFactor]

/-- The affine conductor term (10/13)log(4d)+2434/75 for canonical data.
Its input is the actual squarefree part, and it is positive.
The single-cutoff and direct quadratic conditions reuse this term. -/
noncomputable def cubic2434Base {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) : ℝ :=
  (10 / 13 : ℝ) * Real.log (4 * bridge.squarefreePart : ℕ) + 2434 / 75
/-- The improved squared root envelope at G=log(4d), d=log(d), L=log(n).
The canonical decomposition supplies d<=L. Its variable exclusion budget is
(4/3)(L-log(d)), retaining the squarefree-part saving. -/
noncomputable def cubic2434RootBound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) : ℝ :=
  LLS.PaperStatements.cubic2434RootEnvelope (Real.log (4 * bridge.squarefreePart : ℕ))
    (Real.log bridge.squarefreePart) (Real.log n)
/-- The displayed improved linear and square-root envelope for canonical data.
It uses the same positive affine term and L-log(d) as the exact root bound.
For fixed d the leading coefficient is 4/3; it is not uniform in d. -/
noncomputable def cubic2434LinearBound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) : ℝ :=
  LLS.PaperStatements.cubic2434LinearEnvelope (Real.log (4 * bridge.squarefreePart : ℕ))
    (Real.log bridge.squarefreePart) (Real.log n)
/-- The actual negative-support squared radius is below the improved root bound.
Apply the exact logarithmic budget to the scalar radius comparison.
This connects the existing analytic witness theorem to the new public envelope. -/
theorem cubic2434_support_le_root {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    (LLS.PaperStatements.cubicSquareFactorRadius2434
      (Real.log (4 * bridge.squarefreePart : ℕ))
      (negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^ 2 ≤
        cubic2434RootBound bridge := by
  exact LLS.PaperStatements.cubic2434_radius_le_root (Real.log_natCast_nonneg _)
    (negativeSquareFactorCost_le_log_budget bridge)
/-- The exact root is at most the displayed envelope, which is strictly below
the previous constant-35 envelope throughout the canonical domain.
Apply the scalar comparisons with nonnegative logarithms and d<=L. -/
theorem cubic2434_envelope_chain {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    cubic2434RootBound bridge ≤ cubic2434LinearBound bridge ∧
      cubic2434LinearBound bridge < LLS.PaperStatements.cubicSquareFactorLinearEnvelope
        (Real.log (4 * bridge.squarefreePart : ℕ)) (Real.log n) := by
  exact ⟨LLS.PaperStatements.cubic2434_root_le_linear (Real.log_natCast_nonneg _)
    (squarefree_log_le_input_log bridge),
    LLS.PaperStatements.cubic2434_linear_lt_old (Real.log_natCast_nonneg _)
      (Real.log_natCast_nonneg _)⟩
/-- The improved root bound is at least 27 for every canonical decomposition.
Its scalar lower bound is (4868/75)^2, so rational arithmetic absorbs all
small exceptional Selfridge stopping magnitudes. -/
theorem cubic2434_root_ge_twenty_seven {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    27 ≤ cubic2434RootBound bridge := by
  have h := LLS.PaperStatements.cubic2434_root_ge (Real.log_natCast_nonneg
    (4 * bridge.squarefreePart)) (squarefree_log_le_input_log bridge)
  change (4868 / 75 : ℝ) ^ 2 ≤ cubic2434RootBound bridge at h
  linarith only [h]
/-- Under GRH, an actual odd coprime negative Jacobi prime satisfies the new root bound.
Compose the existing improved negative-support prime theorem with the exact budget.
All canonical odd nonsquare inputs are covered without a conductor threshold. -/
theorem exists_prime_neg_one_le_cubic2434_root {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 ∧
      (p : ℝ) ≤ cubic2434RootBound bridge := by
  obtain ⟨p,hp,ho,hc,hj,hb⟩ := exists_prime_neg_one_le_cubic2434_negative_support bridge hg
  exact ⟨p,hp,ho,hc,hj,hb.trans (cubic2434_support_le_root bridge)⟩
/-- Under GRH, the least negative odd-prime witness obeys the new root bound.
Compose the established negative-support least-witness estimate with its budget
comparison. The witness nonemptiness proof is supplied explicitly. -/
theorem primeNegOneWitness_le_cubic2434_root {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ cubic2434RootBound bridge := by
  exact (primeNegOneWitness_le_cubic2434_negative_support bridge hg hw).trans
    (cubic2434_support_le_root bridge)
/-- Under GRH, the least non-one odd-prime witness obeys the new root bound.
Compose its existing negative-support estimate with the exact budget comparison.
The negative and non-one least witnesses remain separate definitions. -/
theorem primeNeOneWitness_le_cubic2434_root {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ cubic2434RootBound bridge := by
  exact (primeNeOneWitness_le_cubic2434_negative_support bridge hg hw).trans
    (cubic2434_support_le_root bridge)
/-- The stated direct quadratic condition bounds the actual root by (4/3+delta)log(n).
Positivity follows from d>1 and d<=n. Apply the scalar criterion, retaining log(d).
No estimate through the displayed envelope is used. -/
theorem cubic2434_root_direct_cutoff {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {δ : ℝ} (hδ : 0 < δ)
    (hc : δ * Real.log n + (4 / 3 : ℝ) * Real.log bridge.squarefreePart ≥
      2 * cubic2434Base bridge * Real.sqrt ((4 / 3 + δ) * Real.log n)) :
    cubic2434RootBound bridge ≤ (4 / 3 + δ) * Real.log n := by
  have hd := Real.log_pos (Nat.one_lt_cast.mpr bridge.squarefreePart_gt_one)
  exact LLS.PaperStatements.cubic2434_root_le_coefficient (Real.log_natCast_nonneg _)
    (squarefree_log_le_input_log bridge) (hd.trans_le (squarefree_log_le_input_log bridge)) hδ hc
/-- For delta>0, the single affine-conductor cutoff bounds the actual root
by (4/3+delta)log(n). Apply the scalar direct-root absorption theorem.
This makes the fixed-squarefree-part coefficient effective. -/
theorem cubic2434_root_single_cutoff {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {δ : ℝ} (hδ : 0 < δ)
    (hc : 4 * (4 / 3 + δ) * (cubic2434Base bridge) ^ 2 / δ ^ 2 ≤ Real.log n) :
    cubic2434RootBound bridge ≤ (4 / 3 + δ) * Real.log n := by
  have hd := Real.log_pos (Nat.one_lt_cast.mpr bridge.squarefreePart_gt_one)
  exact LLS.PaperStatements.cubic2434_single_cutoff (Real.log_natCast_nonneg _)
    (Real.log_natCast_nonneg _) (squarefree_log_le_input_log bridge)
    (hd.trans_le (squarefree_log_le_input_log bridge)) hδ hc
/-- Under GRH, the least witness is bounded by the displayed improved envelope.
Compose its exact root bound with the root-to-envelope comparison.
This preserves the squarefree-part logarithm and the constant 2434/75. -/
theorem primeNegOneWitness_le_cubic2434_linear {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ cubic2434LinearBound bridge := by
  exact (primeNegOneWitness_le_cubic2434_root bridge hg hw).trans
    (cubic2434_envelope_chain bridge).1
/-- Under GRH and the single explicit cutoff for delta>0, the least witness
is at most (4/3+delta)log(n). Compose the exact root witness bound with direct
quadratic absorption; no coarse linear-envelope estimate is inserted. -/
theorem primeNegOneWitness_le_cubic2434_coefficient {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (hc : 4 * (4 / 3 + δ) * (cubic2434Base bridge) ^ 2 / δ ^ 2 ≤ Real.log n) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (4 / 3 + δ) * Real.log n := by
  exact (primeNegOneWitness_le_cubic2434_root bridge hg hw).trans
    (cubic2434_root_single_cutoff bridge hδ hc)
/-- Under GRH, the least witness is bounded by the displayed improved envelope.
Compose its exact root bound with the root-to-envelope comparison.
This preserves the squarefree-part logarithm and the constant 2434/75. -/
theorem primeNeOneWitness_le_cubic2434_linear {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ cubic2434LinearBound bridge := by
  exact (primeNeOneWitness_le_cubic2434_root bridge hg hw).trans
    (cubic2434_envelope_chain bridge).1
/-- Under GRH and the single explicit cutoff for delta>0, the least witness
is at most (4/3+delta)log(n). Compose the exact root witness bound with direct
quadratic absorption; no coarse linear-envelope estimate is inserted. -/
theorem primeNeOneWitness_le_cubic2434_coefficient {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (hc : 4 * (4 / 3 + δ) * (cubic2434Base bridge) ^ 2 / δ ^ 2 ≤ Real.log n) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (4 / 3 + δ) * Real.log n := by
  exact (primeNeOneWitness_le_cubic2434_root bridge hg hw).trans
    (cubic2434_root_single_cutoff bridge hδ hc)
end PseudoPrime.PseudoSquare
