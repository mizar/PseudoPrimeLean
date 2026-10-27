/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrincipalLowerWitnessBounds
public import PseudoPrime.LLS.ClippedLogShiftPrincipalBounds
public import PseudoPrime.LLS.TwoPolePrimePowerPrefixSavings
public import PseudoPrime.PseudoSquare.Bounds.TwoPolePrefixBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorLogDeficitBounds

/-! # Jacobi witness maxima from certified principal lower caps -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The odd non-one gap for all nonsquare odd inputs at most B, parameterized by
a certified principal lower cap P. Subtract the even Gamma cost after saving 7/8 and
the prime-two allowance. Its positivity is used in the common-ambient witness theorem. -/
noncomputable def principalNeOneGap (B : ℕ) (x P : ℝ) : ℝ :=
  LLS.principalLowerGap (4 * B) (112 / 25 - 7 / 8) x P -
    (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x

/-- Under GRH, odd nonsquare n at most B and x at least three, a certified principal
lower cap with positive non-one gap gives an odd prime non-one Jacobi witness below (99/40)x.
Apply the generic character consumer and quadratic reciprocity; zero values remain allowed. -/
theorem exists_odd_prime_ne_one_of_principalLower_gap {n B : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x P : ℝ}
    (hx : 3 ≤ x)
    (hP :
      P ≤
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re)
    (hgap : 0 < principalNeOneGap B x P) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p ≠ 1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hC :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      (NumberTheory.complexQuadraticCharacter n hn).primitiveCharacter
      ((NumberTheory.primitiveCharacter_even_iff _).mpr
        (NumberTheory.complexQuadraticCharacter_isEven n hn))
  have hs : ∀ m ∈ ({3,5} : Finset ℕ), (m : ℝ) ≤ (99 / 40 : ℝ) * x := by
    intro m hm
    have hn5 : m ≤ 5 := (by decide +kernel : ∀ k ∈ ({3,5} : Finset ℕ), k ≤ 5) m hm
    exact (Nat.cast_le.mpr hn5).trans (by linarith only [hx])
  have hg :
    (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x <
      LLS.principalLowerGap (4 * B) (112 / 25 - 7 / 8) x P := by
    dsimp only [principalNeOneGap] at hgap
    linarith only [hgap]
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    LLS.exists_odd_prime_ne_one_of_principalLower_prefix
      (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns)
      (show 2 ∣ 4 * n from ⟨2 * n, by ring⟩) (Nat.mul_le_mul_left 4 hnB) hGRH
      (by linarith only [hx]) hP hC ({3,5} : Finset ℕ) hs
      (by decide +kernel : ∀ k ∈ ({3,5} : Finset ℕ), Odd k)
      AnalyticNumberTheory.Arithmetic.pairedEuler_prefix_35_saving hg
  refine ⟨p, hp, ho, hb, ?_⟩
  intro hj
  let : NeZero p := ⟨hp.ne_zero⟩
  have hgcd : (n : ℤ).gcd p = 1 := by
    by_contra hc
    have hz := jacobiSym.eq_zero_iff_not_coprime.mpr hc
    rw [hj] at hz
    exact one_ne_zero hz
  have hc : Nat.Coprime n p := by exact_mod_cast hgcd
  apply hv
  rw [NumberTheory.complexQuadraticCharacter_apply_odd_prime n hn hp ho hc.symm, hj]
  exact Int.cast_one

/-- The negative gap for all nonsquare odd inputs at most B, parameterized by
a certified principal lower cap P. Retain the saving one through thirteen and subtract
the affine factor-count ramp cost. This keeps zero exclusion in the negative branch. -/
noncomputable def principalNegOneGap (B : ℕ) (x P : ℝ) : ℝ :=
  LLS.principalLowerGap (4 * B) (87 / 25) x P -
    (5 / 2 + (3 / 8 : ℝ) * Real.log (4 * B : ℕ)) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x

/-- Under GRH, odd nonsquare n at most B and x at least 25, a certified principal
lower cap with positive negative gap gives an odd prime negative Jacobi witness below
(99/40)x. Retain the conductor allocation and prefix through thirteen, excluding zero. -/
theorem exists_odd_prime_neg_one_of_principalLower_gap {n B : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x P : ℝ}
    (hx : 25 ≤ x)
    (hP :
      P ≤
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re)
    (hgap : 0 < principalNegOneGap B x P) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hC :=
    AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant_le_signed_of_even
      (NumberTheory.complexQuadraticCharacter n hn).primitiveCharacter
      ((NumberTheory.primitiveCharacter_even_iff _).mpr
        (NumberTheory.complexQuadraticCharacter_isEven n hn))
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_five_halves_add_three_eighths_log
      (Nat.mul_pos (by norm_num only : 0 < 4) hn.pos) (Nat.mul_le_mul_left 4 hnB)
  have hc :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcard
        (Real.log_nonneg (by linarith only [hx] : 1 ≤ (99 / 40 : ℝ) * x)))
      (Real.sqrt_nonneg x)
  have hs : 5 ≤ Real.sqrt x := by
    nlinarith only [hx, Real.sqrt_nonneg x, Real.sq_sqrt (by linarith only [hx] : 0 ≤ x)]
  have hg :
    (5 / 2 + (3 / 8 : ℝ) * Real.log (4 * B : ℕ)) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
      LLS.principalLowerGap (4 * B) (112 / 25 - 1) x P := by
    dsimp only [principalNegOneGap] at hgap
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

/-- Under the common principal-cap gap assumptions, the least odd-prime non-one
Jacobi witness for n at most B is at most (99/40)x. Apply leastness to the constructed
witness. This is the finite-maximum interface for arbitrary certified principal caps. -/
theorem primeNeOneWitness_cast_le_of_principalLower_gap {n B : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x P : ℝ}
    (hx : 3 ≤ x)
    (hP :
      P ≤
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re)
    (hgap : 0 < principalNeOneGap B x P) (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_ne_one_of_principalLower_gap hn hns hnB hGRH hx hP hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH, a certified principal lower cap with positive common non-one
gap bounds QNeOne(B) by (99/40)x. Apply the least-witness estimate to all admissible
inputs, including small n. The principal cap is an argument, independent of kernel choice. -/
theorem QNeOne_le_of_principalLower_gap {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x P : ℝ} (hx : 3 ≤ x)
    (hP :
      P ≤
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re)
    (hgap : 0 < principalNeOneGap B x P) : (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  apply
    QNeOne_cast_le_of_forall
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (by linarith only [hx] : 0 ≤ x))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNeOneWitness_cast_le_of_principalLower_gap ha.odd ha.not_isSquare ha.le hGRH hx hP hgap
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare))

/-- Under the common principal-cap gap assumptions, the least odd-prime negative
Jacobi witness for n at most B is at most (99/40)x. Apply leastness to the constructed
witness. This is the finite-maximum interface for arbitrary certified principal caps. -/
theorem primeNegOneWitness_cast_le_of_principalLower_gap {n B : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hnB : n ≤ B) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x P : ℝ}
    (hx : 25 ≤ x)
    (hP :
      P ≤
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re)
    (hgap : 0 < principalNegOneGap B x P) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_neg_one_of_principalLower_gap hn hns hnB hGRH hx hP hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH, a certified principal lower cap with positive common negative
gap bounds QNegOne(B) by (99/40)x. Apply the least-witness estimate to all admissible
inputs, including small n. The principal cap is an argument, independent of kernel choice. -/
theorem QNegOne_le_of_principalLower_gap {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x P : ℝ} (hx : 25 ≤ x)
    (hP :
      P ≤
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re)
    (hgap : 0 < principalNegOneGap B x P) : (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  apply
    QNegOne_cast_le_of_forall
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (by linarith only [hx] : 0 ≤ x))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_of_principalLower_gap ha.odd ha.not_isSquare ha.le hGRH hx hP hgap
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- Under GRH, a positive gap using the full clipped-corrected principal cap
bounds QNeOne(B) by (99/40)x at an admissible scale and width. Supply the proved
principal lower bound to the generic finite-maximum theorem. No independent
principal-bound assumption remains in this corrected-profile consumer. -/
theorem QNeOne_le_of_clippedShift_gap {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x h : ℝ} (hx : 3 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x)
    (hgap : 0 < principalNeOneGap B x (LLS.clippedShiftPrincipalLower x h)) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  exact
    QNeOne_le_of_principalLower_gap hGRH hx
      (LLS.clippedShiftPrincipalLower_le_actual hGRH.riemann (by linarith only [hx]) hh hhx) hgap

/-- Under GRH, a positive gap using the full clipped-corrected principal cap
bounds QNegOne(B) by (99/40)x at an admissible scale and width. Supply the proved
principal lower bound to the generic finite-maximum theorem. No independent
principal-bound assumption remains in this corrected-profile consumer. -/
theorem QNegOne_le_of_clippedShift_gap {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x h : ℝ} (hx : 25 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x)
    (hgap : 0 < principalNegOneGap B x (LLS.clippedShiftPrincipalLower x h)) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  exact
    QNegOne_le_of_principalLower_gap hGRH hx
      (LLS.clippedShiftPrincipalLower_le_actual hGRH.riemann (by linarith only [hx]) hh hhx) hgap

end PseudoPrime.PseudoSquare
