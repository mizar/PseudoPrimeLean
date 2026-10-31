/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GammaSignedVariableScaleBounds
public import PseudoPrime.LLS.GammaNoNegativeRampSupport
public import PseudoPrime.Analysis.GammaResolventGridCertificate
public import PseudoPrime.LLS.PaperStatements.GammaResolventCharacterComparison

/-! # Sharp character comparisons retaining the actual resolvent zero mass -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The remaining numerical budget at logarithmic input L and integer-prefix
cutoff b. It combines the even Gamma factor, full Euler weight, twice the
prefix gain, ambient conductor, shared local dual, pole and sharp left costs.
Its input is only the scale and prefix, with no unknown factorization data.
This is the quantity to certify over the analytic interval. -/
noncomputable def gammaRefinedArithmeticBudget (L b : ℝ) : ℝ :=
  let x := Analysis.gammaRefinedScale L
  (AnalyticNumberTheory.Gamma.gammaResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
      2 * (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) +
    (11783423 / 25000000 : ℝ) * (L + Real.log 4) +
    (3 / 4 : ℝ) +
    gammaRefinedSignedDualBudget L +
    ((7 / 6 : ℝ) * (L + Real.log 4) + 4) / Real.sqrt x +
    x ^ (-9 / 16 : ℝ) * ((3 / 2) * (L + Real.log 4 + 28) + 1)

/-- The actual primitive Jacobi modulus of an odd nonsquare input is at
least three. Its odd squarefree part is larger than one and divides the
positive fundamental discriminant. This discharges the analytic conductor gate. -/
theorem gamma_jacobi_modulus_ge_three {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    3 ≤ (NumberTheory.complexQuadraticCharacter n hn).conductor := by
  have hd : 3 ≤ bridge.squarefreePart :=
    Nat.succ_le_of_lt
      (lt_of_le_of_ne (Nat.succ_le_of_lt bridge.squarefreePart_gt_one)
        (fun he ↦ bridge.squarefreePart_odd.not_two_dvd_nat (he ▸ dvd_refl 2)))
  have hf : 0 < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (gamma_jacobi_modulus_eq_discriminant bridge).symm ▸ bridge.discriminant_pos
  exact hd.trans (Nat.le_of_dvd hf (gamma_jacobi_modulus_squarefree_data bridge).1)

/-- For odd nonsquare n≥10^100 under GRH, absence of negative odd-prime
Jacobi witnesses through the prescribed cutoff forces a comparison of the
actual principal and ramp sums with the signed Gamma factor, full Euler
weight, integer prefix gain, finite local dual budget, pole and sharp left cost.
Only the remaining quantitative numerical inequality is needed for contradiction. -/
theorem gamma_jacobi_no_negative_refined_arithmetic_comparison {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlarge : 10 ^ 100 ≤ n) {b : ℝ}
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n))
    (hno :
      ∀ p : ℕ,
        p.Prime →
          Odd p →
          (p : ℝ) ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n) → jacobiSym n p ≠ -1) :
    let x := Analysis.gammaRefinedScale (Real.log n)
    2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re ≤
      (AnalyticNumberTheory.Gamma.gammaResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) * (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
          2 * (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) +
        (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) +
        (3 / 4 : ℝ) +
        gammaRefinedSignedDualBudget (Real.log n) +
        ((7 / 6 : ℝ) * Real.log (4 * (n : ℝ)) + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log (4 * (n : ℝ)) + 28) + 1) := by
  dsimp only
  have hx : 2 ≤ Analysis.gammaRefinedScale (Real.log n) :=
    le_trans (by norm_num only : (2 : ℝ) ≤ 20000)
      (Analysis.gamma_refined_scale_ge_twenty_thousand
        (Analysis.gamma_refined_log_range_of_decimal hlarge))
  have hx0 : 0 < Analysis.gammaRefinedScale (Real.log n) :=
    lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  have hm := gamma_jacobi_modulus_ge_three bridge
  have hmq :=
    Nat.le_of_dvd (mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos)
      (DirichletCharacter.conductor_dvd_level (NumberTheory.complexQuadraticCharacter n hn))
  have hq : 20000 ≤ 4 * n :=
    le_trans (by norm_num only : (20000 : ℕ) ≤ 4 * 10 ^ 100) (Nat.mul_le_mul_left 4 hlarge)
  have hinv : bridge.character⁻¹ ≠ 1 := by
    rw [bridge.character_quadratic.inv]
    exact bridge.character_ne_one
  have hc :=
    PaperStatements.gamma_primitive_sum_re_le_resolvent_sharp hq hm hmq hGRH
      bridge.character_primitive bridge.character_ne_one hinv hx
  have hz :=
    gamma_jacobi_no_negative_zeroMass_add_ramp_le_prefix_dual bridge
      (hGRH _ bridge.character bridge.character_primitive) hb
      (fun p hp hodd hpb ↦ hno p hp hodd (hpb.trans hbX)) hlarge
  have ha := gamma_jacobi_no_negative_ramp_comparison bridge hx0 hno
  have hgf : bridge.character.gammaFactor = Complex.Gammaℝ :=
    funext (fun z ↦ bridge.character_even.gammaFactor_def z)
  rw [hgf] at hz
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hc
  have hf0 : (0 : ℝ) < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num only : (0 : ℕ) < 3) hm)
  have hfq : ((NumberTheory.complexQuadraticCharacter n hn).conductor : ℝ) ≤ 4 * n := by
    exact_mod_cast hmq
  have hl := Real.log_le_log hf0 hfq
  have hleft :=
    mul_le_mul_of_nonneg_left
      (add_le_add_right
        (mul_le_mul_of_nonneg_left (add_le_add_right hl 28) (by norm_num only : (0 : ℝ) ≤ 3 / 2)) 1)
      (Real.rpow_pos_of_pos hx0 (-9 / 16 : ℝ)).le
  linarith only [hc, hz, ha, hleft]

/-- A strict numerical gap over the factorization-independent budget forces
an odd-prime negative Jacobi witness below the prescribed cutoff, for odd
nonsquare n≥10^100 under GRH. Negating witness existence supplies exactly
the no-negative hypothesis of the complete smoothed arithmetic comparison.
The gap remains an explicit numerical requirement, not an assumed certificate. -/
theorem exists_odd_prime_negative_of_refined_arithmetic_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlarge : 10 ^ 100 ≤ n) {b : ℝ}
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n))
    (hgap :
      gammaRefinedArithmeticBudget (Real.log n) b <
        2 *
            (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum
                (Analysis.gammaRefinedScale (Real.log n)) /
              Real.sqrt (Analysis.gammaRefinedScale (Real.log n))) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                (Analysis.gammaRefinedScale (Real.log n)) k).re) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n) ∧ jacobiSym n p = -1 := by
  by_contra hnot
  have hno :
    ∀ p : ℕ,
      p.Prime →
        Odd p →
        (p : ℝ) ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n) → jacobiSym n p ≠ -1 :=
    fun p hp hodd hcut hj ↦ hnot ⟨p, hp, hodd, hcut, hj⟩
  have h := gamma_jacobi_no_negative_refined_arithmetic_comparison bridge hGRH hlarge hb hbX hno
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn.pos).ne'
  have hlog : Real.log (4 * (n : ℝ)) = Real.log n + Real.log 4 := by
    rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) hn0, add_comm]
  apply (not_le_of_gt hgap)
  simpa only [gammaRefinedArithmeticBudget, hlog] using h

end PseudoPrime.LLS
