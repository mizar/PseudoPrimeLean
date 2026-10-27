/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampUnramifiedSupport
public import PseudoPrime.LLS.GammaIntegerPrefixConductorBounds
public import PseudoPrime.LLS.GammaQuadraticNoWitness

/-! # Actual Jacobi ramp corrections outside the ambient prime factors -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For a positive scale and no negative odd-prime witness through 99x/40,
the actual primitive Jacobi character has a convergent nonpositive ramp series
at every prime coprime to 4n. Transfer the witness assumption at small primes
and retain the signed tail at larger primes. This is the support reduction
needed when comparing the full principal and character smoothed sums. -/
theorem gamma_jacobi_no_negative_unramified_ramp {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {x : ℝ} (hx : 0 < x)
    (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1) {p : ℕ}
    (hp : p.Prime) (hcop : Nat.Coprime p (4 * n)) :
    Summable
        (fun k : ℕ ↦
          Analysis.exponentialRampLocalCorrection (bridge.character p) ((p : ℝ) ^ (k + 1) / x)
            (k + 1)) ∧
      (∑' k : ℕ,
          Analysis.exponentialRampLocalCorrection (bridge.character p) ((p : ℝ) ^ (k + 1) / x)
            (k + 1)) ≤
        0 := by
  exact
    Analysis.exponentialRamp_unramified_series_nonpos hp hx (bridge.character_quadratic p)
      (fun hcut ↦ gamma_jacobi_no_negative_prefix_prime_one bridge hno p hp hcut hcop)

/-- For any finite prime set containing all ambient factors, its full local
ramp sum is bounded by the ambient factor sum. Primes outside 4n contribute
nonpositively, including their signed tails. No large-input hypothesis or RH
is needed for this arithmetic support reduction. -/
theorem gamma_jacobi_no_negative_finite_ramp_le_ambient {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {x : ℝ} (hx : 0 < x)
    (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (hsub : (4 * n).primeFactors ⊆ s) :
    (∑ p ∈ s,
        Real.log p *
          ((∑' k : ℕ,
              Analysis.exponentialRampLocalCorrection (bridge.character p) ((p : ℝ) ^ (k + 1) / x)
                (k + 1)) /
            Real.sqrt x)) ≤
      ∑ p ∈ (4 * n).primeFactors,
        Real.log p *
          ((∑' k : ℕ,
              Analysis.exponentialRampLocalCorrection (bridge.character p) ((p : ℝ) ^ (k + 1) / x)
                (k + 1)) /
            Real.sqrt x) := by
  apply Finset.sum_le_sum_of_subset_of_nonpos hsub
  intro p hps hpa
  have hp := hs p hps
  have hcop : Nat.Coprime p (4 * n) :=
    hp.coprime_iff_not_dvd.mpr
      (fun hd ↦
        hpa
          (Nat.mem_primeFactors.mpr
            ⟨hp, hd, (mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos).ne'⟩))
  exact
    mul_nonpos_of_nonneg_of_nonpos (Real.log_natCast_nonneg p)
      (div_nonpos_of_nonpos_of_nonneg
        (gamma_jacobi_no_negative_unramified_ramp bridge hx hno hp hcop).2 (Real.sqrt_nonneg x))

/-- At positive scale, absence of a negative Jacobi odd-prime witness through
99x/40 bounds twice the normalized ramp sum by the two full Gamma sums and
the actual ambient 4n local correction. Use original-level unit agreement
to apply the existing absolutely convergent arithmetic comparison. -/
theorem gamma_jacobi_no_negative_ramp_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {x : ℝ} (hx : 0 < x)
    (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1) :
    2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) ≤
      (∑' m : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x m).re +
        (∑' m : ℕ, PaperStatements.gammaMellinKernel.summand bridge.character x m).re +
        ∑ p ∈ (4 * n).primeFactors,
          Real.log p *
            ((∑' k : ℕ,
                Analysis.exponentialRampLocalCorrection (bridge.character p) ((p : ℝ) ^ (k + 1) / x)
                  (k + 1)) /
              Real.sqrt x) := by
  let χ := NumberTheory.complexQuadraticCharacter n hn
  let : NeZero (4 * n) := ⟨(mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos).ne'⟩
  have hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ 4 * n → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1 := by
    intro p hp hpd hcut
    have hc := hp.coprime_iff_not_dvd.mpr hpd
    have he := AnalyticNumberTheory.Arithmetic.apply_eq_primitiveCharacter_or_zero χ (n := p)
    rw [ite_eq_left hc] at he
    have hv := gamma_jacobi_no_negative_prefix_prime_one bridge hno p hp hcut hc
    rw [bridge.character_eq] at hv
    exact he.trans hv
  have h :=
    gamma_ramp_no_witness_comparison χ (NumberTheory.complexQuadraticCharacter_isQuadratic n hn) hx
      hsmall
  rw [bridge.character_eq]
  simpa only [χ, NumberTheory.primitiveQuadraticCharacter, gammaQuadraticLocalCorrection,
    Finset.sum_div, mul_div_assoc] using h

end PseudoPrime.LLS
