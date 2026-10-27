/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.QuarterLogPrimeFactorBounds
public import PseudoPrime.PseudoSquare.Bounds.PrincipalLowerBounds

/-! # Negative Jacobi witnesses with the quarter-logarithm local budget -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The certified principal lower cap minus the reflected upper bound and the local
cost (13/2+(1/4)log(4B))log((99/40)x)/sqrt x. This keeps the earlier conductor allocation
and prefix saving one while reducing the logarithmic factor-count coefficient. -/
noncomputable def quarterPrincipalNegOneGap (B : ℕ) (x P : ℝ) : ℝ :=
  LLS.principalLowerGap (4 * B) (87 / 25) x P -
    (13 / 2 + (1 / 4 : ℝ) * Real.log (4 * B : ℕ)) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x

/-- For odd nonsquare n at most B under GRH, a certified principal lower cap and positive
quarter-budget gap give an odd prime negative Jacobi witness below (99/40)x.
Apply the conductor comparison with the unconditional quarter-logarithm factor count.
This is the pointwise consumer for improved principal profiles. -/
theorem exists_odd_prime_neg_one_of_quarterPrincipalLower_gap {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x P : ℝ} (hx : 25 ≤ x)
    (hP :
      P ≤
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re)
    (hgap : 0 < quarterPrincipalNegOneGap B x P) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hC :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      (NumberTheory.complexQuadraticCharacter n hn).primitiveCharacter
      ((NumberTheory.primitiveCharacter_even_iff _).mpr
        (NumberTheory.complexQuadraticCharacter_isEven n hn))
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_thirteen_halves_add_quarter_log
      (Nat.mul_pos (by norm_num only : 0 < 4) hn.pos) (Nat.mul_le_mul_left 4 hnB)
  have hc :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcard
        (Real.log_nonneg (by linarith only [hx] : 1 ≤ (99 / 40 : ℝ) * x)))
      (Real.sqrt_nonneg x)
  have hs : 5 ≤ Real.sqrt x := by
    nlinarith only [hx, Real.sqrt_nonneg x, Real.sq_sqrt (by linarith only [hx] : 0 ≤ x)]
  have hg :
    (13 / 2 + (1 / 4 : ℝ) * Real.log (4 * B : ℕ)) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
      LLS.principalLowerGap (4 * B) (112 / 25 - 1) x P := by
    dsimp only [quarterPrincipalNegOneGap] at hgap
    norm_num only
    linarith only [hgap]
  have hY : ∀ k ∈ Finset.Ioc 0 ⌊(13 : ℝ)⌋₊, (k : ℝ) ≤ (99 / 40 : ℝ) * x := by
    intro k hk
    have hk13 : k ≤ 13 := by
      norm_num only [Nat.floor_ofNat] at hk
      exact (Finset.mem_Ioc.mp hk).2
    exact (Nat.cast_le.mpr hk13).trans (by linarith only [hx])
  have hSaving :
    (1 : ℝ) ≤ LLS.twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊(13 : ℝ)⌋₊) - (1 / 5 : ℝ) * Real.log 2 := by
    norm_num only [Nat.floor_ofNat]
    exact LLS.twoPoleEulerPrefixMass_thirteen_saving_one
  obtain ⟨p, hp, hd, hb, hv⟩ :=
    LLS.exists_prime_neg_one_of_principalLower_conductor_prefix
      (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns)
      (Nat.mul_le_mul_left 4 hnB) hGRH (by linarith only [hx]) hP (Y := 13) (by norm_num only) (a :=
      3 / 10) (d := (1 / 5 : ℝ) * Real.log 2) (by norm_num only)
      (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg 2)) (by linarith only [hs])
      (fun p hp ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_upper_three_tenths hp)
      hY hC (g := 1) hSaving (hc.trans_lt hg)
  have hw :=
    NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd
      (by
        rw [hv]; norm_num only)
  exact ⟨p, hp, hw.2.1, hb, hw.2.2⟩

/-- Under the quarter-budget gap assumptions, the least odd-prime negative witness
is at most (99/40)x. Apply leastness to the pointwise witness. This supplies the finite maximum. -/
theorem primeNegOneWitness_cast_le_of_quarterPrincipalLower_gap {n B : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x P : ℝ} (hx : 25 ≤ x)
    (hP :
      P ≤
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re)
    (hgap : 0 < quarterPrincipalNegOneGap B x P)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_neg_one_of_quarterPrincipalLower_gap hn hns hnB hGRH hx hP hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH, scale at least 25 and a positive quarter-budget gap for a certified
principal cap, QNegOne(B) is at most (99/40)x. Apply leastness uniformly to all
admissible inputs. No lower bound on the individual input is imposed. -/
theorem QNegOne_le_of_quarterPrincipalLower_gap {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x P : ℝ} (hx : 25 ≤ x)
    (hP :
      P ≤
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re)
    (hgap : 0 < quarterPrincipalNegOneGap B x P) : (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  apply
    QNegOne_cast_le_of_forall
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (by linarith only [hx] : 0 ≤ x))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_of_quarterPrincipalLower_gap ha.odd ha.not_isSquare ha.le hGRH hx hP
      hgap (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- Under GRH, an admissible width and positive quarter-budget gap for the clipped
principal profile bound QNegOne(B) by (99/40)x. Insert the proved principal lower cap.
This connects the reduced local cost to the actual corrected analytic profile. -/
theorem QNegOne_le_of_quarterClippedShift_gap {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x h : ℝ} (hx : 25 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x)
    (hgap : 0 < quarterPrincipalNegOneGap B x (LLS.clippedShiftPrincipalLower x h)) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  exact
    QNegOne_le_of_quarterPrincipalLower_gap hGRH hx
      (LLS.clippedShiftPrincipalLower_le_actual hGRH.riemann (by linarith only [hx]) hh hhx) hgap

/-- At scale at least 25 and log(4B) above 32, the quarter-budget gap is strictly
larger than the old gap for every principal cap P. Multiply the strict coefficient
comparison by the positive logarithmic cost. This certifies a uniform improvement
of the witness criterion, without claiming a new closed half-line cutoff. -/
theorem quarterPrincipalNegOneGap_gt_old {B : ℕ} {x P : ℝ} (hx : 25 ≤ x)
    (hL : 32 < Real.log (4 * B : ℕ)) :
    principalNegOneGap B x P < quarterPrincipalNegOneGap B x P := by
  have hcoeff := AnalyticNumberTheory.Arithmetic.quarter_factor_budget_lt_old hL
  have hx0 : 0 < x := by linarith only [hx]
  have hlog : 0 < Real.log ((99 / 40 : ℝ) * x) :=
    Real.log_pos (by linarith only [hx] : 1 < (99 / 40 : ℝ) * x)
  have hc := div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hcoeff hlog) (Real.sqrt_pos.mpr hx0)
  dsimp only [principalNegOneGap, quarterPrincipalNegOneGap]
  linarith only [hc]

end PseudoPrime.PseudoSquare
