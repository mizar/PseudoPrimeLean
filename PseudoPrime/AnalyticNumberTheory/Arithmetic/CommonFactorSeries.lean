/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt

/-!
# Reciprocal Mangoldt series on integers sharing a prime factor

The support is parametrized by a prime divisor and a positive exponent.
The resulting geometric series gives the infinite-sum identity in LLS Lemma 3.1.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The reciprocal Mangoldt term restricted to positive integers not coprime to `m`.
This is the unrestricted series compared with the finite weighted sum in LLS Lemma 3.1. -/
noncomputable def commonFactorReciprocalTerm (m n : ℕ) : ℝ :=
  if 0 < n ∧ ¬Nat.Coprime n m then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0

/-- A prime divisor paired with a natural index represents its positive power.
Using exponent `k + 1` removes the zero exponent from the series parametrization. -/
def commonFactorPrimePowerIndex (m : ℕ) (z : m.primeFactors × ℕ) : ℕ :=
  (z.1 : ℕ) ^ (z.2 + 1)

/-- For `p > 1`, the geometric ratio has positive denominator and sums to `1/(p-1)`.
Cross multiplication identifies the constant used in the reciprocal prime-power series. -/
private theorem inv_div_one_sub_inv {p : ℝ} (hp : 1 < p) : p⁻¹ / (1 - p⁻¹) = 1 / (p - 1) := by
  rw [div_eq_div_iff (ne_of_gt (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp))) (sub_ne_zero.mpr hp.ne')]
  rw [mul_sub, inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans hp)), mul_one, one_mul]

/-- The prime-power reciprocal summand is a scalar multiple of a geometric summand.
The identity supplies the pointwise conversion used by the `HasSum` proof. -/
private theorem log_div_pow_succ (p : ℝ) (k : ℕ) :
    Real.log p / p ^ (k + 1) = (Real.log p / p) * p⁻¹ ^ k := by
  rw [pow_succ, inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  ring

/-- For prime `p`, the reciprocal series on its positive powers has sum `log p/(p-1)`.
The proof multiplies the geometric series of ratio `1/p` by `log p/p`.
This gives both summability and the exact prime contribution to LLS Lemma 3.1. -/
theorem hasSum_log_div_prime_pow {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ ↦ Real.log p / (p : ℝ) ^ (k + 1)) (Real.log p / (p - 1)) := by
  have hpcast : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
  have hgeo :=
    (hasSum_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p))
          (inv_lt_one_of_one_lt₀ hpcast)).mul_left
      (Real.log p / p)
  have he := congrArg (fun z : ℝ ↦ Real.log p * z) (inv_div_one_sub_inv hpcast)
  have hd : Real.log p / (p - 1) = (Real.log p / p) * (1 - (p : ℝ)⁻¹)⁻¹ := by
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using he.symm
  simpa only [log_div_pow_succ, hd] using hgeo

/-- Unique prime-power representations make the support parametrization injective.
The positive exponent lets `Nat.Prime.pow_inj` recover both coordinates. -/
theorem commonFactorPrimePowerIndex_injective (m : ℕ) :
    Function.Injective (commonFactorPrimePowerIndex m) := fun a b hab ↦
  Prod.ext
    (Subtype.ext
      ((Nat.Prime.pow_inj (Nat.prime_of_mem_primeFactors a.1.property)
          (Nat.prime_of_mem_primeFactors b.1.property) hab).1))
    ((Nat.Prime.pow_inj (Nat.prime_of_mem_primeFactors a.1.property)
        (Nat.prime_of_mem_primeFactors b.1.property) hab).2)

/-- On a positive power of a prime divisor, the restricted term is `log p/p^(k+1)`.
Primality evaluates the Mangoldt function and identifies failure of coprimality.
This is the summand conversion for the geometric-series reindexing. -/
theorem commonFactorReciprocalTerm_prime_power (m : ℕ) (z : m.primeFactors × ℕ) :
    commonFactorReciprocalTerm m (commonFactorPrimePowerIndex m z) =
      Real.log (z.1 : ℕ) / ((z.1 : ℕ) : ℝ) ^ (z.2 + 1) := by
  have hp := Nat.mem_primeFactors.mp z.1.property
  have hc : ¬Nat.Coprime ((z.1 : ℕ) ^ (z.2 + 1)) m := fun h ↦
    (hp.1.coprime_iff_not_dvd.mp ((Nat.coprime_pow_left_iff (Nat.succ_pos z.2) _ _).mp h)) hp.2.1
  rw [commonFactorPrimePowerIndex, commonFactorReciprocalTerm,
    ite_eq_left ⟨Nat.pow_pos hp.1.pos, hc⟩,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero z.2),
    ArithmeticFunction.vonMangoldt_apply_prime hp.1, Nat.cast_pow]

/-- A nonzero restricted summand has a positive index sharing a factor with `m`.
The conditional definition gives the support conditions used by reindexing. -/
private theorem commonFactorReciprocalTerm_conditions {m n : ℕ}
    (hn : commonFactorReciprocalTerm m n ≠ 0) : 0 < n ∧ ¬Nat.Coprime n m := by
  exact of_not_not fun h ↦ hn (by rw [commonFactorReciprocalTerm, ite_eq_right h])

/-- A nonzero restricted summand must be a prime power, since Mangoldt vanishes elsewhere.
This identifies the arithmetic part of the unrestricted series support. -/
private theorem commonFactorReciprocalTerm_isPrimePow {m n : ℕ}
    (hn : commonFactorReciprocalTerm m n ≠ 0) : IsPrimePow n := by
  exact
    of_not_not fun h ↦
      hn
        (by
          rw [commonFactorReciprocalTerm, ite_eq_left (commonFactorReciprocalTerm_conditions hn),
            ArithmeticFunction.vonMangoldt_apply, ite_eq_right h, zero_div])

/-- For nonzero `m`, every nonzero summand is indexed by a prime divisor and positive power.
Prime-power support and failure of coprimality identify the required prime divisor.
Together with injectivity this permits reindexing the entire infinite series. -/
theorem commonFactorReciprocalTerm_support {m : ℕ} (hm : m ≠ 0) :
    Function.support (commonFactorReciprocalTerm m) ⊆
      Set.range (commonFactorPrimePowerIndex m) := by
  intro n hn
  obtain ⟨p, k, hp, hk, he⟩ := (isPrimePow_nat_iff n).mp (commonFactorReciprocalTerm_isPrimePow hn)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hd : p ∣ m :=
    of_not_not fun h ↦
      (commonFactorReciprocalTerm_conditions hn).2 (he ▸ (hp.coprime_iff_not_dvd.mpr h).pow_left k)
  refine ⟨(⟨p, Nat.mem_primeFactors.mpr ⟨hp, hd, hm⟩⟩, j), ?_⟩
  exact (congrArg (fun r : ℕ ↦ p ^ r) hj).symm.trans he

/-- The geometric contributions are summable over prime divisors and positive exponents.
Each prime slice is summable; the outer index is finite and every term is nonnegative.
This justifies exchanging the prime and exponent sums. -/
theorem summable_commonFactorPrimePowerSeries (m : ℕ) :
    Summable (fun z : m.primeFactors × ℕ ↦ Real.log (z.1 : ℕ) / ((z.1 : ℕ) : ℝ) ^ (z.2 + 1)) := by
  apply
    (summable_prod_of_nonneg
        (fun z ↦
          div_nonneg
            (Real.log_nonneg
              (Nat.one_le_cast.mpr (Nat.prime_of_mem_primeFactors z.1.property).one_le))
            (pow_nonneg (Nat.cast_nonneg _) _))).mpr
  exact
    ⟨fun p ↦ (hasSum_log_div_prime_pow (Nat.prime_of_mem_primeFactors p.property)).summable,
      (hasSum_fintype _).summable⟩

/-- The sum of the geometric prime-power contributions is the prime-factor logarithmic sum.
Summability permits iterated summation, and each inner sum has its exact geometric value.
This is the evaluation step in the unrestricted Mangoldt identity. -/
theorem tsum_commonFactorPrimePowerSeries (m : ℕ) :
    (∑' z : m.primeFactors × ℕ, Real.log (z.1 : ℕ) / ((z.1 : ℕ) : ℝ) ^ (z.2 + 1)) =
      primeFactorLogSum m := by
  rw [(summable_commonFactorPrimePowerSeries m).tsum_prod]
  calc
    _ = ∑' p : m.primeFactors, Real.log (p : ℕ) / ((p : ℕ) - 1 : ℝ) :=
      tsum_congr fun p ↦
        (hasSum_log_div_prime_pow (Nat.prime_of_mem_primeFactors p.property)).tsum_eq
    _ = primeFactorLogSum m := by
      rw [tsum_fintype, Finset.sum_coe_sort m.primeFactors (fun p : ℕ ↦ Real.log p / ((p : ℝ) - 1)),
        primeFactorLogSum]

/-- For nonzero `m`, the unrestricted reciprocal common-factor series is summable.
The injective prime-power parametrization covers its support and reduces it to finitely
many convergent geometric series. This rules out the nonsummable default value of `tsum`. -/
theorem summable_commonFactorReciprocalTerm {m : ℕ} (hm : m ≠ 0) :
    Summable (commonFactorReciprocalTerm m) := by
  apply
    ((commonFactorPrimePowerIndex_injective m).summable_iff
        (fun n hn ↦ not_not.mp (fun he ↦ hn (commonFactorReciprocalTerm_support hm he)))).mp
  exact
    (summable_commonFactorPrimePowerSeries m).congr fun z ↦
      (commonFactorReciprocalTerm_prime_power m z).symm

/-- For nonzero `m`, summing `Λ(n)/n` over positive integers not coprime to `m`
gives `Σ_{p ∣ m} log p/(p-1)`. Unique prime-power support reindexes the series,
and its geometric evaluation gives the equality required by LLS Lemma 3.1. -/
theorem tsum_commonFactorReciprocalTerm {m : ℕ} (hm : m ≠ 0) :
    (∑' n : ℕ, commonFactorReciprocalTerm m n) = primeFactorLogSum m := by
  have hr :=
    (commonFactorPrimePowerIndex_injective m).tsum_eq (commonFactorReciprocalTerm_support hm)
  rw [← hr]
  simp only [commonFactorReciprocalTerm_prime_power]
  exact tsum_commonFactorPrimePowerSeries m

end PseudoPrime.AnalyticNumberTheory.Arithmetic
