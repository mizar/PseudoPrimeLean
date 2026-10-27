/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimitiveSquarefreeCharacter
public import PseudoPrime.PseudoSquare.Bounds.CubicSquareFactorJacobiBounds

/-! # Cubic witnesses charging only negative primes of the square factor -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Sum log p over prime divisors p of s at which the Jacobi symbol (d/p) is
minus one. Applications use odd s, so all denominator primes are odd. This
is the portion of the square factor that can hide a negative prime witness. -/
noncomputable def negativeSquareFactorCost (d s : ℕ) : ℝ :=
  ∑ p ∈ s.primeFactors with jacobiSym d p = -1, Real.log p

/-- The negative-prime cost is nonnegative because every prime logarithm is
nonnegative. This supplies the sign condition for the cubic square-factor radius. -/
theorem negativeSquareFactorCost_nonneg (d s : ℕ) : 0 ≤ negativeSquareFactorCost d s := by
  exact Finset.sum_nonneg fun p _ ↦ Real.log_natCast_nonneg p

/-- The negative-prime cost is at most the full prime logarithm sum of s.
Compare the filtered support with all prime factors using nonnegative logarithms.
This compares the refined radius with the previously proved square-factor bound. -/
theorem negativeSquareFactorCost_le_full (d s : ℕ) :
    negativeSquareFactorCost d s ≤ ∑ p ∈ s.primeFactors, Real.log p := by
  exact
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ ↦ Real.log_natCast_nonneg p)

/-- At an odd prime away from the squarefree part, the primitive logarithmic
defect is exactly twice log p for a negative Jacobi value and zero otherwise.
Use squarefree primitive transfer and the two possible nonzero Jacobi values.
This removes positively valued square-factor primes from the exclusion cost. -/
theorem primitiveQuadratic_defect_log_eq_negative {n p : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (hp : p.Prime) (ho : Odd p)
    (hd : ¬p ∣ bridge.squarefreePart) :
    (1 - (NumberTheory.primitiveQuadraticCharacter n hn p).re) * Real.log p =
      if jacobiSym bridge.squarefreePart p = -1 then 2 * Real.log p else 0 := by
  have he := NumberTheory.primitiveQuadraticCharacter_apply_squarefree_odd_prime bridge hp ho hd
  simp only [Int.cast_natCast] at he
  have hj :=
    jacobiSym.eq_one_or_neg_one
      (show (bridge.squarefreePart : ℤ).gcd p = 1
        by
        rw [Int.gcd_natCast_natCast]
        exact (hp.coprime_iff_not_dvd.mpr hd).symm.gcd_eq_one)
  rw [he]
  rcases hj with hj | hj <;> rw [hj] <;>
    norm_num only [Int.cast_one, Int.cast_neg, Complex.one_re, Complex.neg_re, ite_true, ite_false,
      zero_mul]

/-- The defect sum over prime divisors of the square factor absent from d is
at most twice the negative-prime logarithm cost. Evaluate each unramified odd
prime by the squarefree Jacobi symbol and enlarge the nonnegative filtered sum.
The set difference avoids charging ramified primes already counted in d. -/
theorem primitiveQuadratic_square_factor_sdiff_le_negative {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    (∑ p ∈ bridge.squareFactor.primeFactors \ bridge.squarefreePart.primeFactors,
        (1 - (NumberTheory.primitiveQuadraticCharacter n hn p).re) * Real.log p) ≤
      2 * negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor := by
  classical
    calc
    _ =
        ∑ p ∈ bridge.squareFactor.primeFactors \ bridge.squarefreePart.primeFactors,
          if jacobiSym bridge.squarefreePart p = -1 then 2 * Real.log p else 0 :=
      by
      apply Finset.sum_congr rfl
      intro p hp
      have hm := Finset.mem_sdiff.mp hp
      have hprime := Nat.prime_of_mem_primeFactors hm.1
      have hodd := Odd.of_dvd_nat bridge.squareFactor_odd (Nat.dvd_of_mem_primeFactors hm.1)
      have hd : ¬p ∣ bridge.squarefreePart := fun h ↦
        hm.2 (Nat.mem_primeFactors.mpr ⟨hprime, h, bridge.squarefreePart_pos.ne'⟩)
      exact primitiveQuadratic_defect_log_eq_negative bridge hprime hodd hd
    _ ≤
        ∑ p ∈ bridge.squareFactor.primeFactors,
          if jacobiSym bridge.squarefreePart p = -1 then 2 * Real.log p else 0 :=
      by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      intro p _ _
      exact ite_nonneg (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg p)) le_rfl
    _ = _ := by
      rw [← Finset.sum_filter]
      exact (Finset.mul_sum _ _ _).symm

open AnalyticNumberTheory.Arithmetic in
/-- For n=s²d, the primitive exclusion cost at 2n is at most log(4d)+2E_-(s).
Split the product support exactly to avoid shared ramified primes, then bound
only the negative square-factor primes and the contribution at two. This is
the arithmetic input required for the refined cubic witness radius. -/
theorem primitiveQuadraticExclusionCost_le_negative_square_factor {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    characterExclusionCost (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) ≤
      Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) +
        2 * negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor := by
  let χ := NumberTheory.primitiveQuadraticCharacter n hn
  have hd := bridge.squarefreePart_pos.ne'
  have hs := bridge.squareFactor_odd.pos.ne'
  have hp := characterExclusionCost_mul_le χ (by decide : 2 ≠ 0) hn.pos.ne'
  have he := characterExclusionCost_mul_eq_add_sdiff χ hd (pow_ne_zero 2 hs)
  rw [Nat.primeFactors_pow bridge.squareFactor (by decide : 2 ≠ 0)] at he
  rw [mul_comm bridge.squarefreePart, bridge.squarefreePart_sq_mul] at he
  have hdC :=
    characterExclusionCost_le_log_of_zero χ hd
      (fun p hp ↦ primitiveQuadraticCharacter_zero_on_squarefreePart bridge hp)
  have hsc := primitiveQuadratic_square_factor_sdiff_le_negative bridge
  have ht := characterExclusionCost_le_twice χ 2
  rw [Nat.prime_two.primeFactors, Finset.sum_singleton] at ht
  norm_num only [Nat.cast_ofNat] at ht
  have hl :
    Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) =
      2 * Real.log 2 + Real.log bridge.squarefreePart := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hd)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  change characterExclusionCost χ (2 * n) ≤ _
  change
    (∑ p ∈ bridge.squareFactor.primeFactors \ bridge.squarefreePart.primeFactors,
        (1 - (χ p).re) * Real.log p) ≤
      _ at hsc
  linarith only [hp, he, hdC, hsc, ht, hl]

/-- Under GRH for n=s²d, there is an odd coprime negative prime below the cubic
square-factor radius with only E_-(s) charged. Supply the proved negative-support
cost to the generic absorbed-radius extraction. No extra arithmetic hypothesis
remains; positively valued square-factor primes do not contribute. -/
theorem exists_prime_neg_one_le_cubic_negative_support {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          (LLS.PaperStatements.cubicSquareFactorRadius
              (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
              (negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^
            2 := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hdvd : bridge.squarefreePart ∣ n :=
    ⟨bridge.squareFactor ^ 2, by simpa only [mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  have hf :=
    Nat.le_of_dvd (Nat.mul_pos (by decide : 0 < 4) bridge.squarefreePart_pos)
      (NumberTheory.complexQuadraticCharacter_conductor_dvd_four_mul_squarefreePart bridge hdvd)
  have hlog :=
    Real.log_le_log
      (Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero))
      (Nat.cast_le.mpr hf)
  exact
    exists_prime_neg_one_le_cubic_square_factor_of_envelopes (hns := hns) hGRH hlog
      (negativeSquareFactorCost_nonneg _ _)
      (primitiveQuadraticExclusionCost_le_negative_square_factor bridge)

/-- Under GRH, leastness transfers the negative-support cubic radius to the
least negative odd-prime witness of n=s²d. The support cost is the explicit
Jacobi filter on the square factor, with no remaining analytic cost hypothesis. -/
theorem primeNegOneWitness_le_cubic_negative_support {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (LLS.PaperStatements.cubicSquareFactorRadius (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
          (negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^
        2 := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_cubic_negative_support bridge hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- The same negative-support radius bounds the least non-one odd-prime
witness under GRH. Use the constructed negative value as a non-one value;
this does not identify the two least witnesses. -/
theorem primeNeOneWitness_le_cubic_negative_support {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      (LLS.PaperStatements.cubicSquareFactorRadius (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
          (negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^
        2 := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_cubic_negative_support bridge hGRH
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

/-- For nonnegative G, the negative-support squared radius never exceeds the
full square-factor radius for the same d,s. Compare the filtered logarithmic
costs and apply the generic monotonicity of nonnegative root radii. -/
theorem cubicNegativeSupportRadius_sq_le_full (d s : ℕ) {G : ℝ} (hG : 0 ≤ G) :
    (LLS.PaperStatements.cubicSquareFactorRadius G (negativeSquareFactorCost d s)) ^ 2 ≤
      (LLS.PaperStatements.cubicSquareFactorRadius G (∑ p ∈ s.primeFactors, Real.log p)) ^ 2 := by
  dsimp only [LLS.PaperStatements.cubicSquareFactorRadius]
  apply LLS.PaperStatements.root_radius_sq_mono (by linarith only [hG]) le_rfl
  exact mul_le_mul_of_nonneg_left (negativeSquareFactorCost_le_full d s) (by norm_num only)

/-- Under GRH, a positive target X bounds the least negative odd-prime witness
when 2B sqrt(X)+(8/3)E_-(s) is at most X. Apply the generic quadratic radius
criterion with the proved negative-support cost. This strengthens the full
square-factor criterion without changing the target interface. -/
theorem primeNegOneWitness_le_of_cubic_negative_support_target {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) {X : ℝ} (hX : 0 < X)
    (hquad :
      2 * ((10 / 13 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 35) * Real.sqrt X +
          (8 / 3 : ℝ) * negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor ≤
        X) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ X := by
  have hG := Real.log_natCast_nonneg (4 * bridge.squarefreePart)
  have hE := negativeSquareFactorCost_nonneg bridge.squarefreePart bridge.squareFactor
  have hq :
    2 * ((10 / 13 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 35) * Real.sqrt X +
        (8 / 3 : ℝ) * negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor ≤
      (Real.sqrt X) ^ 2 := by
    rw [Real.sq_sqrt hX.le]
    exact hquad
  have hr :=
    LLS.PaperStatements.cubicSquareFactorRadius_le_of_quadratic hG hE (Real.sqrt_pos.mpr hX) hq
  have hn := (LLS.PaperStatements.cubicSquareFactorRadius_data hG hE).1
  have hs := pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 70).trans hn) hr 2
  exact
    (primeNegOneWitness_le_cubic_negative_support bridge hGRH hw).trans
      (hs.trans_eq (Real.sq_sqrt hX.le))

/-- For any real epsilon, GRH and the coupled negative-support inequality at
L^(1-epsilon/2) give the least negative witness at most L^(2-epsilon), L=log n.
Positivity of L follows from the squarefree decomposition. Rewrite the square
root of the target power and use the generic positive-target theorem. -/
theorem primeNegOneWitness_le_log_rpow_of_cubic_negative_support {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) (ε : ℝ)
    (hquad :
      2 * ((10 / 13 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 35) *
            (Real.log n) ^ (1 - ε / 2) +
          (8 / 3 : ℝ) * negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor ≤
        (Real.log n) ^ (2 - ε)) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (Real.log n) ^ (2 - ε) := by
  have hdvd : bridge.squarefreePart ∣ n :=
    ⟨bridge.squareFactor ^ 2, by simpa only [mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  have hn1 := bridge.squarefreePart_gt_one.trans_le (Nat.le_of_dvd hn.pos hdvd)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  have he : Real.sqrt ((Real.log n) ^ (2 - ε)) = (Real.log n) ^ (1 - ε / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le]
    congr 1
    ring
  apply
    primeNegOneWitness_le_of_cubic_negative_support_target bridge hGRH hw
      (Real.rpow_pos_of_pos hL (2 - ε))
  rw [he]
  exact hquad

end PseudoPrime.PseudoSquare
