/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaQuadraticNoWitness
public import PseudoPrime.LLS.GammaVariableScaleBounds

/-! # Odd non-one witnesses and the prime-two Gamma correction

Absence of an odd non-one witness removes all positive odd level-prime defects.
The remaining signed prime-two series supplies the improved local budget.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- If all odd primes through X have character value one, every odd prime dividing
the level lies above X. Nonzero character value forces level coprimality, contradicting
divisibility. This removes odd level primes from the non-one correction. -/
theorem gamma_level_prime_above_cutoff_of_odd_trivial {q p : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {X : ℝ} (hsmall : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ X → χ p = 1)
    (hp : p ∈ q.primeFactors) (h2 : p ≠ 2) : X < (p : ℝ) := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  by_contra hnot
  have hval := hsmall p hprime (hprime.odd_of_ne_two h2) (le_of_not_gt hnot)
  have hnonzero : χ p ≠ 0 := by
    rw [hval]
    exact one_ne_zero
  have hc := (ZMod.isUnit_iff_coprime p q).mp (MulChar.apply_ne_zero_iff.mp hnonzero)
  exact (hprime.coprime_iff_not_dvd.mp hc) (Nat.mem_primeFactors.mp hp).2.1

/-- For a quadratic primitive source, positive scale and a base above the ramp cutoff,
every positive power has nonpositive signed correction. Sum the tail inequalities.
This retains the signed tail instead of charging a level-prime defect. -/
theorem gamma_prime_power_tail_series_nonpos {q p : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x) (hcut : (99 / 40 : ℝ) * x < p) :
    (∑' k : ℕ,
        Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter p) ((p : ℝ) ^ (k + 1) / x)
          (k + 1)) ≤
      0 := by
  apply tsum_nonpos
  intro k
  have hpw : (p : ℝ) ≤ (p : ℝ) ^ (k + 1) := by exact_mod_cast Nat.le_self_pow (Nat.succ_ne_zero k) p
  apply
    Analysis.exponentialRampLocalCorrection_tail_nonpos
      ((NumberTheory.isQuadratic_primitiveCharacter χ hquad) p)
  apply (le_div_iff₀ hx).mpr
  exact hcut.le.trans hpw

/-- For an even nonzero level and a quadratic character trivial on odd primes through
the cutoff, the full signed local correction is at most the prime-two correction.
Odd level primes lie above the cutoff and contribute nonpositive series.
This eliminates the square-factor cost in the non-one witness comparison. -/
theorem gammaQuadraticLocalCorrection_le_two_of_odd_trivial {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (h2 : 2 ∣ q) {x : ℝ} (hx : 0 < x)
    (hsmall : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) :
    gammaQuadraticLocalCorrection χ x ≤
      Real.log 2 *
          (∑' k : ℕ,
            Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter 2) ((2 : ℝ) ^ (k + 1) / x)
              (k + 1)) /
        Real.sqrt x := by
  have hmem : 2 ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, NeZero.ne q⟩
  have hsum :=
    Finset.sum_le_sum (s := q.primeFactors) (f := fun p : ℕ ↦
      Real.log p *
        (∑' k : ℕ,
          Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter p) ((p : ℝ) ^ (k + 1) / x)
            (k + 1)))
      (g := fun p : ℕ ↦
      if p = 2 then
        Real.log p *
          (∑' k : ℕ,
            Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter p) ((p : ℝ) ^ (k + 1) / x)
              (k + 1))
      else 0)
  have hpoint :
    ∀ p ∈ q.primeFactors,
      Real.log p *
          (∑' k : ℕ,
            Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter p) ((p : ℝ) ^ (k + 1) / x)
              (k + 1)) ≤
        if p = 2 then
          Real.log p *
            (∑' k : ℕ,
              Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter p)
                ((p : ℝ) ^ (k + 1) / x) (k + 1))
        else 0 := by
    intro p hp
    by_cases hp2 : p = 2
    · rw [ite_eq_left hp2]
    · rw [ite_eq_right hp2]
      exact
        mul_nonpos_of_nonneg_of_nonpos
          (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
          (gamma_prime_power_tail_series_nonpos χ hquad hx
            (gamma_level_prime_above_cutoff_of_odd_trivial χ hsmall hp hp2))
  have hs := hsum hpoint
  simp only [Finset.sum_ite_eq', ite_eq_left hmem] at hs
  exact div_le_div_of_nonneg_right hs (Real.sqrt_nonneg x)

/-- At even nonzero level and positive scale, absence of odd non-one prime witnesses
bounds twice the actual normalized ramp sum by the principal and primitive Gamma sums
and the signed prime-two correction. Combine the full-series comparison with odd-tail removal.
The actual primitive conductor and both series are retained. -/
theorem gamma_ramp_no_odd_ne_one_comparison {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (h2 : 2 ∣ q) {x : ℝ} (hx : 0 < x)
    (hsmall : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) :
    2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) ≤
      (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re +
        (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        Real.log 2 *
            (∑' k : ℕ,
              Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter 2)
                ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x := by
  have helig : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1 := by
    intro p hp hpd hcut
    have hp2 : p ≠ 2 := fun he ↦ hpd (he.symm ▸ h2)
    exact hsmall p hp (hp.odd_of_ne_two hp2) hcut
  exact
    (gamma_ramp_no_witness_comparison χ hquad hx helig).trans
      (add_le_add_right (gammaQuadraticLocalCorrection_le_two_of_odd_trivial χ hquad h2 hx hsmall)
        _)

/-- Under the same odd-prime triviality condition with cutoff at least one,
replace the prime-two series by (log(cutoff)+log(2))/sqrt(x).
Use the signed prime-power bound and allow the negative-value parity endpoint.
This supplies a level-prime-count-free input for coefficient-preserving threshold reduction. -/
theorem gamma_ramp_no_odd_ne_one_comparison_log_budget {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (h2 : 2 ∣ q) {x : ℝ} (hx : 0 < x)
    (hcut : 1 ≤ (99 / 40 : ℝ) * x)
    (hsmall : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) :
    2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) ≤
      (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re +
        (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x := by
  have hprim := NumberTheory.isQuadratic_primitiveCharacter χ hquad
  have htwo :=
    Analysis.exponentialRamp_prime_power_log_correction_le (hprim 2) Nat.prime_two.one_lt hx hcut
  have hlog : 0 ≤ Real.log (2 : ℕ) := Real.log_nonneg (by norm_num only [Nat.cast_ofNat])
  have hite : (if χ.primitiveCharacter 2 = -1 then Real.log (2 : ℕ) else 0) ≤ Real.log 2 := by
    split_ifs with he
    · exact le_refl _
    · exact hlog
  have hbound := htwo.trans (add_le_add_right hite _)
  exact
    (gamma_ramp_no_odd_ne_one_comparison χ hquad h2 hx hsmall).trans
      (add_le_add_right (div_le_div_of_nonneg_right hbound (Real.sqrt_nonneg x)) _)

/-- For an even nonzero level, quadratic character and cutoff at least one,
 a strict gap between the actual normalized ramp sum and the two Gamma series plus
 the prime-two logarithmic budget yields an odd prime with character value different from one.
 Negating existence gives odd-prime triviality, contradicted by the whole-series comparison.
 This is the witness interface for later GRH and explicit threshold budgets. -/
theorem exists_odd_prime_ne_one_of_gamma_ramp_gap {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (h2 : 2 ∣ q) {x : ℝ} (hx : 0 < x) (hcut : 1 ≤ (99 / 40 : ℝ) * x)
    (hgap :
      (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re +
          (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re +
          (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
  classical
  by_contra hnone
  have hsmall : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1 := by
    intro p hp hodd hpX
    by_contra hval
    exact hnone ⟨p, hp, hodd, hpX, hval⟩
  exact
    (not_le_of_gt hgap) (gamma_ramp_no_odd_ne_one_comparison_log_budget χ hquad h2 hx hcut hsmall)

/-- For a nonprincipal quadratic character at even level q≥20000 under GRH and x≥1,
 an explicit variable-scale budget below the actual ramp lower sum yields an odd non-one prime.
 Substitute the primitive Gamma upper estimate into the strict-gap witness interface.
 Only the principal series and actual ramp lower sum remain to be bounded numerically. -/
theorem exists_odd_prime_ne_one_of_gamma_variable_budget {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (hcut : 1 ≤ (99 / 40 : ℝ) * x)
    (hgap :
      (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re +
          ((11783423 / 25000000 : ℝ) * Real.log χ.conductor + 24 + 64 / 9 +
            ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
            x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log χ.conductor + 283) + 5 / 3)) +
          (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
  have hnp := PaperStatements.gamma_primitiveCharacter_sum_re_le_variable_scale hq χ hne hGRH hx
  apply exists_odd_prime_ne_one_of_gamma_ramp_gap χ hquad h2 (zero_lt_one.trans_le hx) hcut
  linarith only [hnp, hgap]

end PseudoPrime.LLS
