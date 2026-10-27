/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampLocalSeries
public import PseudoPrime.NumberTheory.DirichletCharacter
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

/-! # Signed quadratic local corrections and conductor absorption

Negative primitive values have support in the conductor quotient.
Absorb their endpoint loss before replacing the conductor by the original level.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- A prime dividing the original level whose primitive value is minus one divides
the level-to-conductor quotient. Nonzero primitive value implies conductor coprimality.
This preserves the exact support of the extra odd-power endpoint loss. -/
theorem negative_primitive_prime_mem_quotientFactors {q p : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : p ∈ q.primeFactors) (hneg : χ.primitiveCharacter p = -1) :
    p ∈ (q / χ.conductor).primeFactors := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hnzero : χ.primitiveCharacter p ≠ 0 := by
    rw [hneg]
    norm_num only
  have hu : IsUnit (p : ZMod χ.conductor) := MulChar.apply_ne_zero_iff.mp hnzero
  have hcop := (ZMod.isUnit_iff_coprime p χ.conductor).mp hu
  have hnd := hpprime.coprime_iff_not_dvd.mp hcop
  have hdiv := (Nat.mem_primeFactors.mp hp).2.1
  rw [← AnalyticNumberTheory.DirichletLFunction.conductor_mul_quotient χ] at hdiv
  have hquot := (hpprime.dvd_mul.mp hdiv).resolve_left hnd
  exact
    Nat.mem_primeFactors.mpr
      ⟨hpprime, hquot, (AnalyticNumberTheory.DirichletLFunction.quotient_pos χ).ne'⟩

/-- The log weight of level primes with negative primitive value is at most
log(q/conductor). Embed their finite support into the quotient prime factors.
This supplies the conductor deficit in the signed local correction. -/
theorem sum_log_negative_primitive_primes_le_log_quotient {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ p ∈ q.primeFactors, if χ.primitiveCharacter p = -1 then Real.log p else 0) ≤
      Real.log (q / χ.conductor : ℕ) := by
  have hsub :
    q.primeFactors.filter (fun p : ℕ ↦ χ.primitiveCharacter p = -1) ⊆
      (q / χ.conductor).primeFactors := by
    intro p hp
    exact
      negative_primitive_prime_mem_quotientFactors χ (Finset.mem_filter.mp hp).1
        (Finset.mem_filter.mp hp).2
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ p ∈ (q / χ.conductor).primeFactors, Real.log p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      apply Real.log_nonneg
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    _ ≤ _ :=
      AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log
        (AnalyticNumberTheory.DirichletLFunction.quotient_pos χ).ne'

/-- The signed quadratic local correction sums log-weighted prime-power terms over
all prime factors of the original level, normalized by sqrt(x).
The primitive values determine the alternating powers; prime two and square-part primes remain. -/
noncomputable def gammaQuadraticLocalCorrection {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℝ :=
  (∑ p ∈ q.primeFactors,
      Real.log p *
        (∑' k : ℕ,
          Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter p) ((p : ℝ) ^ (k + 1) / x)
            (k + 1))) /
    Real.sqrt x

/-- For a quadratic character, positive scale and X=(99/40)x≥1, the actual local
series is at most (omega(q)log(X)+log(q/conductor))/sqrt(x).
Combine per-prime signed bounds and the exact negative-prime support estimate. -/
theorem gammaQuadraticLocalCorrection_le_count_log_quotient {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x)
    (hcut : 1 ≤ (99 / 40 : ℝ) * x) :
    gammaQuadraticLocalCorrection χ x ≤
      ((q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) + Real.log (q / χ.conductor : ℕ)) /
        Real.sqrt x := by
  have hprim := NumberTheory.isQuadratic_primitiveCharacter χ hquad
  have hsum :
    (∑ p ∈ q.primeFactors,
        Real.log p *
          (∑' k : ℕ,
            Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter p) ((p : ℝ) ^ (k + 1) / x)
              (k + 1))) ≤
      ∑ p ∈ q.primeFactors,
        (Real.log ((99 / 40 : ℝ) * x) + if χ.primitiveCharacter p = -1 then Real.log p else 0) := by
    apply Finset.sum_le_sum
    intro p hp
    exact
      Analysis.exponentialRamp_prime_power_log_correction_le (hprim p)
        (Nat.prime_of_mem_primeFactors hp).one_lt hx hcut
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  have hbudget :=
    add_le_add (le_refl ((q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x)))
      (sum_log_negative_primitive_primes_le_log_quotient χ)
  exact div_le_div_of_nonneg_right (hsum.trans hbudget) (Real.sqrt_nonneg x)

/-- When M sqrt(x)≥1, combine Mlog(conductor) with the signed local correction
before rounding to Mlog(q). The quotient logarithm is nonnegative and absorbed.
Only omega(q)log(X)/sqrt(x) remains; the original level's prime support is unchanged. -/
theorem gammaQuadraticLocalCorrection_absorb_conductor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) {x M : ℝ} (hx : 0 < x)
    (hcut : 1 ≤ (99 / 40 : ℝ) * x) (hM : 1 ≤ M * Real.sqrt x) :
    M * Real.log χ.conductor + gammaQuadraticLocalCorrection χ x ≤
      M * Real.log q + (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x := by
  have hs := Real.sqrt_pos.mpr hx
  have hquot0 : 0 ≤ Real.log (q / χ.conductor : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (AnalyticNumberTheory.DirichletLFunction.quotient_pos χ))
  have hmul := mul_le_mul_of_nonneg_left hM hquot0
  have hcost :
    Real.log (q / χ.conductor : ℕ) / Real.sqrt x ≤ M * Real.log (q / χ.conductor : ℕ) := by
    rw [div_le_iff₀ hs]
    nlinarith only [hmul]
  have he := gammaQuadraticLocalCorrection_le_count_log_quotient χ hquad hx hcut
  rw [add_div] at he
  calc
    _ ≤
        M * Real.log χ.conductor +
          ((q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x +
            Real.log (q / χ.conductor : ℕ) / Real.sqrt x) :=
      add_le_add (le_refl _) he
    _ ≤
        M * Real.log χ.conductor +
          ((q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x +
            M * Real.log (q / χ.conductor : ℕ)) :=
      add_le_add (le_refl _) (add_le_add (le_refl _) hcost)
    _ = _ := by
      rw [AnalyticNumberTheory.DirichletLFunction.log_level_eq_log_conductor_add_log_quotient χ]
      ring

end PseudoPrime.LLS
