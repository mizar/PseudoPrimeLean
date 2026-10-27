/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReflectedSplitConductorBounds
public import PseudoPrime.PseudoSquare.Bounds.TwoPoleConductorPrefixNegOneBounds

/-! # Uniform negative Jacobi witnesses from the certified reflected conductor gap -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The certified negative-witness separation gap for all odd nonsquares at most B.
The ambient character level is 4B. Subtract the uniform prime-factor count budget
5/2+(3/8)log(4B), retain the anchor-128 saving and charge the prime-two allowance.
A positive gap at an admissible scale yields both pointwise and finite-maximum bounds. -/
noncomputable def anchor128NegativeGap (B : ℕ) (x b h : ℝ) : ℝ :=
  (133 / 160 : ℝ) * Real.sqrt x - LLS.variableRampPrincipalErrorNumerator x h / Real.sqrt x -
        LLS.reflectedSplitUpper (4 * B) (112 / 25) x +
      ((3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ)) -
    (1 / 5 : ℝ) * Real.log 2 -
    (5 / 2 + (3 / 8 : ℝ) * Real.log (4 * B : ℕ)) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x

/-- For an odd nonsquare n at most B under GRH, a positive anchor gap at an admissible
scale and width yields an odd prime with Jacobi symbol minus one below (99/40)x.
Use the even quadratic character of level 4n and the common factor-count bound at 4B.
The conclusion excludes zero and covers every admissible input, including small n. -/
theorem exists_odd_prime_neg_one_of_anchor128_gap {n B : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b h : ℝ}
    (hx : 25 ≤ x) (hh : 0 < h) (hhx : h ≤ x) (hb : 128 ≤ b) (hcut : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < anchor128NegativeGap B x b h) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_five_halves_add_three_eighths_log
      (Nat.mul_pos (by norm_num only : 0 < 4) hn.pos) (Nat.mul_le_mul_left 4 hnB)
  have hlog : 0 ≤ Real.log ((99 / 40 : ℝ) * x) := Real.log_nonneg (by linarith only [hx])
  have hcost :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hlog) (Real.sqrt_nonneg x)
  have hC :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      (NumberTheory.complexQuadraticCharacter n hn).primitiveCharacter
      ((NumberTheory.primitiveCharacter_even_iff _).mpr
        (NumberTheory.complexQuadraticCharacter_isEven n hn))
  have hsep :
    (5 / 2 + (3 / 8 : ℝ) * Real.log (4 * B : ℕ)) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
      (133 / 160 : ℝ) * Real.sqrt x - LLS.variableRampPrincipalErrorNumerator x h / Real.sqrt x -
            LLS.reflectedSplitUpper (4 * B) (112 / 25) x +
          ((3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ)) -
        (1 / 5 : ℝ) * Real.log 2 := by
    dsimp only [anchor128NegativeGap] at hgap
    linarith only [hgap]
  obtain ⟨p, hp, hd, hpbound, hv⟩ :=
    LLS.exists_prime_neg_one_of_anchor128_mass133 (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns)
      (Nat.mul_le_mul_left 4 hnB) hGRH hx hh hhx hb hcut hC (hcost.trans_lt hsep)
  have hw :=
    NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd
      (by
        rw [hv]; norm_num only)
  exact ⟨p, hp, hw.2.1, hpbound, hw.2.2⟩

/-- Under the common anchor-gap assumptions, the least negative odd-prime Jacobi
witness for any admissible input n at most B is at most (99/40)x.
Apply the constructed witness and leastness. This is the finite-maximum interface. -/
theorem primeNegOneWitness_cast_le_of_anchor128_gap {n B : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b h : ℝ}
    (hx : 25 ≤ x) (hh : 0 < h) (hhx : h ≤ x) (hb : 128 ≤ b) (hcut : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < anchor128NegativeGap B x b h)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hbound, hv⟩ :=
    exists_odd_prime_neg_one_of_anchor128_gap hn hns hnB hGRH hx hh hhx hb hcut hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hbound

/-- Under GRH, a positive common anchor gap at an admissible scale and width bounds
QNegOne(B) by (99/40)x. Apply the least-witness estimate to each admissible input.
No finite input enumeration or additional prime-prefix certificate is assumed. -/
theorem QNegOne_le_of_anchor128_gap {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b h : ℝ} (hx : 25 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) (hb : 128 ≤ b) (hcut : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < anchor128NegativeGap B x b h) : (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  apply
    QNegOne_cast_le_of_forall
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (by linarith only [hx] : 0 ≤ x))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_of_anchor128_gap ha.odd ha.not_isSquare ha.le hGRH hx hh hhx hb hcut
      hgap (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

end PseudoPrime.PseudoSquare
