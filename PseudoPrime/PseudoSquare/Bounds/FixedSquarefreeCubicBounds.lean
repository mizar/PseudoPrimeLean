/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TruncatedExclusionSupport
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.RamifiedExclusion
public import PseudoPrime.PseudoSquare.Bounds.TruncatedCubicJacobiBounds

/-! # Cubic bounds independent of large square-factor primes -/

public section

namespace PseudoPrime.PseudoSquare

/-- In an odd nonsquare decomposition n=s²d, suppose every prime dividing
s with negative Jacobi value for d exceeds X. The primitive localized cost
at 2n is then at most the full cost at 2d. Classify primes outside 2d and
use the nonzero quadratic character values. This removes the size of s. -/
theorem primitiveQuadratic_truncated_cost_le_fixed_support {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {X : ℝ}
    (hlarge :
      ∀ p : ℕ, p.Prime → p ∣ bridge.squareFactor → jacobiSym bridge.squarefreePart p = -1 → X < p) :
    LLS.PaperStatements.truncatedCharacterExclusionCost
        (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) X ≤
      AnalyticNumberTheory.Arithmetic.characterExclusionCost
        (NumberTheory.primitiveQuadraticCharacter n hn) (2 * bridge.squarefreePart) := by
  apply
    LLS.PaperStatements.truncatedCharacterExclusionCost_le_of_prime_coverage _
      (mul_ne_zero (by norm_num only : (2 : ℕ) ≠ 0) bridge.squarefreePart_pos.ne')
  intro p hp hM hx
  by_cases hpd : p ∣ 2 * bridge.squarefreePart
  · exact Or.inl hpd
  · right
    have hpnot2 : ¬p ∣ 2 := fun h ↦ hpd (h.trans (dvd_mul_right 2 bridge.squarefreePart))
    have hpn := (hp.dvd_mul.mp hM).resolve_left hpnot2
    have hd : ¬p ∣ bridge.squarefreePart := fun h ↦
      hpd (h.trans (dvd_mul_left bridge.squarefreePart 2))
    rw [← bridge.squarefreePart_sq_mul] at hpn
    have hs := hp.dvd_of_dvd_pow ((hp.dvd_mul.mp hpn).resolve_right hd)
    have ho : Odd p := Odd.of_dvd_nat bridge.squareFactor_odd hs
    have hj :=
      jacobiSym.eq_one_or_neg_one
        (show (bridge.squarefreePart : ℤ).gcd p = 1
          by
          rw [Int.gcd_natCast_natCast]
          exact (hp.coprime_iff_not_dvd.mpr hd).symm.gcd_eq_one)
    have hjone : jacobiSym bridge.squarefreePart p = 1 :=
      hj.resolve_right (fun hv ↦ (not_lt_of_ge hx) (hlarge p hp hs hv))
    have he := NumberTheory.primitiveQuadraticCharacter_apply_squarefree_odd_prime bridge hp ho hd
    simpa only [Int.cast_natCast, hjone, Int.cast_one] using he

/-- With no negative square-factor prime at most X, the localized primitive
cost is at most log(4d). Combine prime coverage with vanishing on ramified
primes and the generic cost of excluding two. This is the fixed-family
arithmetic input to the cubic radius theorem. -/
theorem primitiveQuadratic_truncated_cost_le_log_squarefree {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {X : ℝ}
    (hlarge :
      ∀ p : ℕ, p.Prime → p ∣ bridge.squareFactor → jacobiSym bridge.squarefreePart p = -1 → X < p) :
    LLS.PaperStatements.truncatedCharacterExclusionCost
        (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) X ≤
      Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) := by
  exact
    (primitiveQuadratic_truncated_cost_le_fixed_support bridge hlarge).trans
      (AnalyticNumberTheory.Arithmetic.characterExclusionCost_two_mul_le_log_four_mul _
        bridge.squarefreePart_pos.ne'
        (fun p hp ↦ primitiveQuadraticCharacter_zero_on_squarefreePart bridge hp))

/-- The squared tight cubic radius with both conductor and cost envelopes
equal to log(4d). For positive odd squarefree d greater than one, this is a
constant independent of the added square factor. Subsequent theorems use it
when every negative prime divisor of that factor lies above this value. -/
noncomputable def fixedSquarefreeCubicBound (d : ℕ) : ℝ :=
  (LLS.PaperStatements.tightCubicExclusionRadius (Real.log ((4 * d : ℕ) : ℝ))
      (Real.log ((4 * d : ℕ) : ℝ))) ^
    2

/-- Under GRH, n=s²d has a coprime odd negative Jacobi prime at most the
fixed bound for d if every negative prime divisor of s exceeds that bound.
Discharge the conductor envelope arithmetically and the cost envelope by
localized prime coverage. This is the witness existence statement for the family. -/
theorem exists_prime_neg_one_le_fixed_squarefree_cubic_bound {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlarge :
      ∀ p : ℕ,
        p.Prime →
          p ∣ bridge.squareFactor →
          jacobiSym bridge.squarefreePart p = -1 →
          fixedSquarefreeCubicBound bridge.squarefreePart < p) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧ (p : ℝ) ≤ fixedSquarefreeCubicBound bridge.squarefreePart := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hdvd : bridge.squarefreePart ∣ n :=
    ⟨bridge.squareFactor ^ 2, by simpa only [mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  have hf :=
    Nat.le_of_dvd (Nat.mul_pos (by norm_num only : 0 < 4) bridge.squarefreePart_pos)
      (NumberTheory.complexQuadraticCharacter_conductor_dvd_four_mul_squarefreePart bridge hdvd)
  have hlog :=
    Real.log_le_log
      (Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero))
      (Nat.cast_le.mpr hf)
  exact
    exists_prime_neg_one_le_of_truncated_cubic_radius (hns := hns) hGRH hlog
      (primitiveQuadratic_truncated_cost_le_log_squarefree bridge hlarge)
      (le_refl (fixedSquarefreeCubicBound bridge.squarefreePart))

/-- The fixed squared radius is at least 27 for every natural d. The cubic
radius is at least 63/2 because both logarithmic envelopes are nonnegative.
This discharges the small-prime exception in both Selfridge transfers. -/
theorem twenty_seven_le_fixedSquarefreeCubicBound (d : ℕ) : 27 ≤ fixedSquarefreeCubicBound d := by
  have h :=
    (LLS.PaperStatements.tightCubicExclusionRadius_data (Real.log_natCast_nonneg (4 * d))
        (Real.log_natCast_nonneg (4 * d))).1
  unfold fixedSquarefreeCubicBound
  nlinarith only [h]

end PseudoPrime.PseudoSquare
