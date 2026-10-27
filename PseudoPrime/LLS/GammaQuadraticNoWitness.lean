/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaQuadraticArithmetic
public import PseudoPrime.LLS.GammaSmoothedPrincipalBounds
public import PseudoPrime.LLS.GammaExponentialPrincipalBounds
public import PseudoPrime.LLS.GammaSmoothedNonprincipalBounds
public import PseudoPrime.LLS.MellinKernelBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedSummationByParts
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison

/-! # Smoothed quadratic no-witness comparison

The actual ramp finite sum and two Gamma series retain the signed local correction.
The fixed-scale analytic budgets rule out prime triviality at logarithm 46000.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- If eligible primes up to X have character value one, then a unit prime power
up to X has primitive character value one. Its prime base lies below X and is a level unit.
Use multiplicativity and exact primitive agreement on original-level units. -/
theorem primitive_prime_power_one_of_prime_trivial {q n : ℕ} (χ : DirichletCharacter ℂ q) {X : ℝ}
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → χ p = 1) (hpow : IsPrimePow n)
    (hcop : Nat.Coprime n q) (hcut : (n : ℝ) ≤ X) : χ.primitiveCharacter n = 1 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
  have hc := (Nat.coprime_pow_left_iff hk _ _).mp hcop
  have hpR : (p : ℝ) ≤ X := by
    have hnat := Nat.le_self_pow hk.ne' p
    have hr : (p : ℝ) ≤ (p ^ k : ℕ) := by exact_mod_cast hnat
    exact hr.trans hcut
  have hpval := hsmall p hp (hp.coprime_iff_not_dvd.mp hc) hpR
  have hnval : χ (p ^ k : ℕ) = 1 := by simp only [Nat.cast_pow, map_pow, hpval, one_pow]
  have he := AnalyticNumberTheory.Arithmetic.apply_eq_primitiveCharacter_or_zero χ (n := p ^ k)
  rw [ite_eq_left hcop, hnval] at he
  exact he.symm

/-- Under the quadratic no-witness condition, each signed ramp discrepancy is
bounded by its nonunit Mangoldt correction. Unit prime powers inside the cutoff have value one;
outside it the discrepancy is nonpositive, and Mangoldt vanishes off prime powers. -/
theorem signed_local_term_le_Mangoldt_correction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.sqrt x *
        Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter n) ((n : ℝ) / x) 1 ≤
      gammaSignedMangoldtCorrection χ x n := by
  by_cases hcop : Nat.Coprime n q
  · rw [gammaSignedMangoldtCorrection_unit χ x hcop]
    by_cases hpow : IsPrimePow n
    · have hlocal :
        Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter n) ((n : ℝ) / x) 1 ≤ 0 := by
        by_cases hcut : (n : ℝ) ≤ (99 / 40 : ℝ) * x
        · have he := primitive_prime_power_one_of_prime_trivial χ hsmall hpow hcop hcut
          rw [he]
          exact Analysis.exponentialRampLocalCorrection_one _ _
        · have hu : 99 / 40 ≤ (n : ℝ) / x := by
            apply (le_div_iff₀ hx).mpr
            exact (lt_of_not_ge hcut).le
          exact
            Analysis.exponentialRampLocalCorrection_tail_nonpos
              ((NumberTheory.isQuadratic_primitiveCharacter χ hquad) n) hu 1
      exact
        mul_nonpos_of_nonneg_of_nonpos
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg x)) hlocal
    · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
      rw [hz, zero_div, zero_mul]
  · rw [gammaSignedMangoldtCorrection, ite_eq_right hcop]

/-- The normalized ramp term is Mangoldt(n)W(n/x)/sqrt(x).
Its finite cutoff support connects the actual ramp finite sum with a whole-series comparison. -/
noncomputable def normalizedRampMangoldtTerm (x : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Analysis.exponentialRampWeight ((n : ℝ) / x) / Real.sqrt x

/-- At positive scale, the normalized ramp term vanishes outside the positive cutoff indices.
Index zero has zero Mangoldt value, and indices above the cutoff have zero ramp weight. -/
theorem normalizedRampMangoldtTerm_support {x : ℝ} (hx : 0 < x) (n : ℕ)
    (hn : n ∉ Finset.Ioc 0 ⌊x * (99 / 40 : ℝ)⌋₊) : normalizedRampMangoldtTerm x n = 0 := by
  by_cases hn0 : n = 0
  · have hz : ArithmeticFunction.vonMangoldt 0 = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero
    simp only [normalizedRampMangoldtTerm, hn0, hz, zero_mul, zero_div]
  · have hnot : ¬n ≤ ⌊x * (99 / 40 : ℝ)⌋₊ := fun h ↦
      hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, h⟩)
    have hnn : ((⌊x * (99 / 40 : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ n := by
      exact_mod_cast Nat.succ_le_of_lt (lt_of_not_ge hnot)
    have hfloor := Nat.lt_floor_add_one (x * (99 / 40 : ℝ))
    have hu : 99 / 40 ≤ (n : ℝ) / x := by
      apply (le_div_iff₀ hx).mpr
      norm_num only [Nat.cast_add, Nat.cast_one] at hnn
      linarith only [hnn, hfloor]
    rw [normalizedRampMangoldtTerm, Analysis.exponentialRampWeight_eq_zero hu, mul_zero, zero_div]

/-- The normalized ramp series equals the actual finite ramp Mangoldt sum divided by sqrt(x).
Use its exact finite support and extract the common denominator. -/
theorem normalizedRampMangoldtTerm_tsum {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, normalizedRampMangoldtTerm x n) =
      AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x := by
  rw [tsum_eq_sum (normalizedRampMangoldtTerm_support hx)]
  dsimp only [normalizedRampMangoldtTerm,
    AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum]
  exact (Finset.sum_div _ _ _).symm

/-- Under the no-witness condition, twice the normalized ramp term is bounded
by the principal and primitive Gamma summands plus the signed Mangoldt correction.
Combine the exact summand identity with the unit/nonunit discrepancy bound. -/
theorem gamma_pair_summand_le_of_prime_trivial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) (n : ℕ) :
    2 * normalizedRampMangoldtTerm x n ≤
      (PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re +
        (PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        gammaSignedMangoldtCorrection χ x n := by
  have h := signed_local_term_le_Mangoldt_correction χ hquad hx hsmall n
  have he := PaperStatements.gamma_pair_summand_add_signed_term χ hquad hx n
  dsimp only [normalizedRampMangoldtTerm]
  linarith only [h, he]

/-- For a quadratic character at nonzero level and positive scale, triviality on
eligible primes through (99/40)x implies twice the actual normalized ramp finite sum
is at most the two full Gamma series plus the signed local correction.
Absolute summability and exact correction reindexing justify the whole-series comparison. -/
theorem gamma_ramp_no_witness_comparison {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) :
    2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) ≤
      (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re +
        (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        gammaQuadraticLocalCorrection χ x := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hA : Summable (fun n : ℕ ↦ 2 * normalizedRampMangoldtTerm x n) :=
    (summable_of_ne_finset_zero (normalizedRampMangoldtTerm_support hx)).mul_left 2
  have hP :=
    PaperStatements.MellinKernel.summable_summand PaperStatements.gammaMellinKernel
      (1 : DirichletCharacter ℂ 1) hx
  have hC :=
    PaperStatements.MellinKernel.summable_summand PaperStatements.gammaMellinKernel
      χ.primitiveCharacter hx
  have hE := summable_gammaSignedMangoldtCorrection χ hquad hx
  have hrhs := (Complex.reCLM.summable hP).add (Complex.reCLM.summable hC) |>.add hE
  have h := Summable.tsum_le_tsum (gamma_pair_summand_le_of_prime_trivial χ hquad hx hsmall) hA hrhs
  erw [tsum_mul_left, normalizedRampMangoldtTerm_tsum hx,
    Summable.tsum_add ((Complex.reCLM.summable hP).add (Complex.reCLM.summable hC)) hE,
    Summable.tsum_add (Complex.reCLM.summable hP) (Complex.reCLM.summable hC), ←
    Complex.reCLM.map_tsum hP, ← Complex.reCLM.map_tsum hC,
    tsum_gammaSignedMangoldtCorrection_eq_localCorrection χ hquad hx] at h
  exact h

/-- Under GRH, for odd n with log(n)≥46000 and original level 4n≥20000,
a nonprincipal quadratic character cannot be trivial on all eligible primes through
(99/40)(32/99)log(n)². Combine the actual no-witness comparison with the principal,
nonprincipal and signed local budgets; the total 4987/90 contradicts the main-term margin. -/
theorem gamma_ramp_prime_trivial_false {n : ℕ} (hn : Odd n) (χ : DirichletCharacter ℂ (4 * n))
    (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hq : 20000 ≤ 4 * n) (hL : 46000 ≤ Real.log n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ¬(∀ p : ℕ,
        p.Prime →
          ¬p ∣ 4 * n → (p : ℝ) ≤ (99 / 40 : ℝ) * ((32 / 99 : ℝ) * (Real.log n) ^ 2) → χ p = 1) := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  intro hsmall
  have hx := zero_lt_one.trans_le (Analysis.ramp_scale_ge_one hL)
  have hlogq : Real.log (4 * n : ℕ) ≤ Real.log n + 2 := by
    rw [log_original_quadratic_level (Odd.pos hn)]
    linarith only [log_four_le_two]
  have hQ := gamma_ramp_no_witness_comparison χ hquad hx hsmall
  have hlo := gamma_ramp_sum_lower_seven hGRH.riemann hL
  have hP := PaperStatements.gamma_level_one_sum_upper_one_fifth hGRH.riemann hL
  have hC :=
    PaperStatements.gamma_primitiveCharacter_sum_re_le_smoothed_at_ramp_scale hq χ hne hGRH hL hlogq
  have hE := gammaQuadraticLocalCorrection_absorbed_at_ramp_scale hn χ hquad hL
  apply Analysis.gamma_ramp_inequality_false_of_log_ge hL
  nlinarith only [hQ, hlo, hP, hC, hE]

end PseudoPrime.LLS
