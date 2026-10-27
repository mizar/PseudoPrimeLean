/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaPairedEulerIdentity
public import PseudoPrime.LLS.GammaResolventCharacterComparison

/-! # Conductor budgets retaining the nonnegative paired Euler tail -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For the actual primitive Jacobi character under individual RH, n≥10^100
and ambient-unit prime triviality through b≥1, keep the unretained paired
Euler mass together with the zero mass and ambient ramp. The exact paired
prefix identity and the joint conductor budget give the same finite dual
upper bound while retaining the additional nonnegative prime-power gain. -/
theorem gamma_jacobi_zeroMass_add_ramp_pairedTail_le_dual {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis bridge.character) {b : ℝ}
    (hb : 1 ≤ b)
    (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p (4 * n) → bridge.character p = 1)
    (hlarge : 10 ^ 100 ≤ n) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor bridge.character.completedLFunction Set.univ ρ : ℝ) *
            Analysis.gammaResolventMajorant ρ.im) +
        (∑ p ∈ (4 * n).primeFactors,
          Real.log p *
            ((∑' k : ℕ,
                Analysis.exponentialRampLocalCorrection (bridge.character p)
                  ((p : ℝ) ^ (k + 1) / Analysis.gammaRefinedScale (Real.log n)) (k + 1)) /
              Real.sqrt (Analysis.gammaRefinedScale (Real.log n)))) +
        Analysis.gammaPairedEulerTail bridge.character (Finset.Ioc 0 ⌊b⌋₊) ≤
      (Analysis.gammaResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) *
                    (logDeriv bridge.character.gammaFactor
                        (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
          2 * (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) +
        (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) +
        (3 / 4 : ℝ) +
        gammaRefinedSignedDualBudget (Real.log n) := by
  have hq := le_trans (by norm_num only : (2 : ℕ) ≤ 3) (gamma_jacobi_modulus_ge_three bridge)
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_zeroMass_add_pairedTail_eq_prefix hq hRH
      bridge.character_primitive bridge.character_ne_one
      (by
        rw [bridge.character_quadratic.inv]; exact bridge.character_ne_one)
      (Finset.Ioc 0 ⌊b⌋₊)
  have hl := gamma_jacobi_integer_prefix_local_budget bridge hb hone hlarge
  dsimp only [gammaRefinedSignedDualBudget]
  linarith only [hz, hl]

/-- For odd nonsquare n≥10^100 under GRH and no negative Jacobi odd-prime
witness through the prescribed cutoff, the complete arithmetic comparison
retains the nonnegative paired tail on the left. The same numerical budget
is sufficient, and a certified tail lower bound can improve its gap. -/
theorem gamma_jacobi_no_negative_arithmetic_add_pairedTail_le_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlarge : 10 ^ 100 ≤ n) {b : ℝ}
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n))
    (hno :
      ∀ p : ℕ,
        p.Prime →
          Odd p →
          (p : ℝ) ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n) → jacobiSym n p ≠ -1) :
    2 *
            (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum
                (Analysis.gammaRefinedScale (Real.log n)) /
              Real.sqrt (Analysis.gammaRefinedScale (Real.log n))) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                (Analysis.gammaRefinedScale (Real.log n)) k).re +
        Analysis.gammaPairedEulerTail bridge.character (Finset.Ioc 0 ⌊b⌋₊) ≤
      gammaRefinedArithmeticBudget (Real.log n) b := by
  dsimp only [gammaRefinedArithmeticBudget]
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
    gamma_jacobi_zeroMass_add_ramp_pairedTail_le_dual bridge
      (hGRH _ bridge.character bridge.character_primitive) hb
      (gamma_jacobi_no_negative_prefix_prime_one bridge
        (fun p hp hodd hpb ↦ hno p hp hodd (hpb.trans hbX)))
      hlarge
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
  have hlog : Real.log (4 * (n : ℝ)) = Real.log n + Real.log 4 := by
    rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_pos.mpr hn.pos).ne', add_comm]
  rw [hlog] at hc hz hleft
  linarith only [hc, hz, ha, hleft]

/-- Any selected square inputs outside the prefix improve the complete
Jacobi arithmetic comparison by their common weight. The gain depends only
on the selected finite set and remains valid at ramified primes. This is
an input-independent refinement available to the numerical gap certificate. -/
theorem gamma_jacobi_no_negative_arithmetic_add_square_gain_le_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlarge : 10 ^ 100 ≤ n) {b : ℝ}
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n))
    (hno :
      ∀ p : ℕ,
        p.Prime →
          Odd p →
          (p : ℝ) ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n) → jacobiSym n p ≠ -1)
    (C : Finset ℕ) (hC : ∀ m ∈ C, IsSquare m) (hBC : Disjoint (Finset.Ioc 0 ⌊b⌋₊) C) :
    2 *
            (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum
                (Analysis.gammaRefinedScale (Real.log n)) /
              Real.sqrt (Analysis.gammaRefinedScale (Real.log n))) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                (Analysis.gammaRefinedScale (Real.log n)) k).re +
        (∑ m ∈ C, Analysis.gammaResolventMangoldtWeight m) ≤
      gammaRefinedArithmeticBudget (Real.log n) b := by
  have ht :=
    Analysis.gammaPairedEulerTail_ge_square_sum bridge.character bridge.character_quadratic
      (Finset.Ioc 0 ⌊b⌋₊) C hBC hC
  have ha :=
    gamma_jacobi_no_negative_arithmetic_add_pairedTail_le_budget bridge hGRH hlarge hb hbX hno
  exact (add_le_add_right ht _).trans ha

/-- A strict gap including selected square-power gains forces an odd-prime
negative Jacobi witness through the prescribed cutoff. The numerical
premise depends only on n, b and the selected finite square set, and can be
weaker than the gap obtained by discarding the nonnegative paired tail. -/
theorem exists_odd_prime_negative_of_refined_square_gain_gap {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlarge : 10 ^ 100 ≤ n) {b : ℝ}
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n)) (C : Finset ℕ)
    (hC : ∀ m ∈ C, IsSquare m) (hBC : Disjoint (Finset.Ioc 0 ⌊b⌋₊) C)
    (hgap :
      gammaRefinedArithmeticBudget (Real.log n) b <
        2 *
              (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum
                  (Analysis.gammaRefinedScale (Real.log n)) /
                Real.sqrt (Analysis.gammaRefinedScale (Real.log n))) -
            (∑' k : ℕ,
                PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                  (Analysis.gammaRefinedScale (Real.log n)) k).re +
          (∑ m ∈ C, Analysis.gammaResolventMangoldtWeight m)) :
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
  exact
    (not_le_of_gt hgap)
      (gamma_jacobi_no_negative_arithmetic_add_square_gain_le_budget bridge hGRH hlarge hb hbX hno C
        hC hBC)

end PseudoPrime.LLS
