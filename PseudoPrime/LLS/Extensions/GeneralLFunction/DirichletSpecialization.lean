/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.PaperStatements
public import PseudoPrime.LLS.Extensions.ArithmeticCoefficients
public import PseudoPrime.LLS.DirichletExplicitFormula
public import PseudoPrime.AnalyticNumberTheory.General.AnalyticMultiplicity
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Arithmetic specialization of general L-function data to Dirichlet characters

Degree-one data, finite sums, gamma endpoints and completed-zero multiplicities are compared.
The identities transfer arithmetic sums, RH and zero mass without requiring general admissibility.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- Degree-one data associated with a complex Dirichlet character of nonzero modulus.
The conductor is the modulus, the gamma shift records parity, and the local root and
Dirichlet coefficient are the character value. Analytic admissibility is a separate proposition.
The completion uses mathlib's continued completed L-function; the odd normalization factor
converts `Gammaℝ(s+1)` to `π^(-s/2) Gamma((s+1)/2)`.
This data identifies the extension's arithmetic sums with the original paper's sums. -/
noncomputable def ofDirichletCharacter {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    GeneralLFunction where
  degree := 1
  conductor := q
  shift := fun _ ↦ if χ (-1) = 1 then 0 else 1
  root := fun p _ ↦ χ p
  coefficient := fun n ↦ χ n
  L := χ.LFunction
  completed := fun s ↦
    (q : ℂ) ^ (s / 2) * (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ)) * χ.completedLFunction s

/-- The degree-one local root-power sum equals the character value on `p^k`.
Evaluate the singleton sum and use character multiplicativity. -/
theorem ofDirichletCharacter_primePowerCoefficient {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (p k : ℕ) : (ofDirichletCharacter χ).primePowerCoefficient p k = χ (p ^ k) := by
  change (∑ _j : Fin 1, (χ p) ^ k) = χ (p ^ k)
  rw [Fin.sum_univ_one, map_pow]

/-- The extension's local root estimate bounds the degree-one prime-power coefficient by one.
Dirichlet character values have norm at most one, including nonunits. -/
theorem ofDirichletCharacter_primePower_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (p k : ℕ) : ‖(ofDirichletCharacter χ).primePowerCoefficient p k‖ ≤ 1 := by
  simpa only [ofDirichletCharacter, Nat.cast_one] using
    norm_primePowerCoefficient_le (ofDirichletCharacter χ) (p := p) (fun _ ↦ χ.norm_le_one _) k

/-- Multiplication by Mangoldt identifies the general degree-one coefficient with the character.
On prime powers use the local coefficient formula; elsewhere Mangoldt is zero.
This equality transfers every Mangoldt-weighted arithmetic sum. -/
theorem ofDirichletCharacter_weighted_coefficient {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (n : ℕ) :
    (ofDirichletCharacter χ).mangoldtCoefficient n * (ArithmeticFunction.vonMangoldt n : ℂ) =
      χ n * (ArithmeticFunction.vonMangoldt n : ℂ) := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := hn
    rw [mangoldtCoefficient_prime_pow _ hp.nat_prime (Nat.ne_of_gt hk),
      ofDirichletCharacter_primePowerCoefficient, Nat.cast_pow]
  · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
    rw [hz, Complex.ofReal_zero, mul_zero, mul_zero]

/-- The extension's degree-one logarithmic L-value sum equals the original character sum.
Transfer its Mangoldt-weighted coefficient termwise, with no analytic assumptions. -/
theorem ofDirichletCharacter_logValueSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    (ofDirichletCharacter χ).logValueSum x = PaperStatements.characterLogLValueSum χ x := by
  unfold logValueSum PaperStatements.characterLogLValueSum
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.ofReal_mul, Complex.ofReal_div, ← mul_assoc, ← mul_div_assoc,
    ofDirichletCharacter_weighted_coefficient]
  ring

/-- The extension's degree-one smoothed reciprocal sum equals the original character sum.
Transfer the Mangoldt factor termwise; the remaining real weight is unchanged. -/
theorem ofDirichletCharacter_reciprocalWeightedSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x : ℝ) :
    (ofDirichletCharacter χ).reciprocalWeightedSum x =
      AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ := by
  unfold reciprocalWeightedSum AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
    AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedTerm
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.ofReal_mul, Complex.ofReal_div, ← mul_assoc, ← mul_div_assoc,
    ofDirichletCharacter_weighted_coefficient]
  ring

/-- The extension's degree-one truncated L-value sum equals the character comparison sum
used in Lemma 5.1 and Theorem 1.5. Transfer the weighted coefficient termwise. -/
theorem ofDirichletCharacter_truncatedValueSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x : ℝ) :
    (ofDirichletCharacter χ).truncatedValueSum x =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        χ n *
          (ArithmeticFunction.vonMangoldt n * (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)) :
            ℝ) := by
  unfold truncatedValueSum
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.ofReal_mul, ← mul_assoc, ofDirichletCharacter_weighted_coefficient, mul_assoc]

/-- Every canonical degree-one Mangoldt coefficient has norm at most one.
Prime powers use the extension's root bound; other indices have zero coefficient. -/
theorem ofDirichletCharacter_mangoldtCoefficient_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖(ofDirichletCharacter χ).mangoldtCoefficient n‖ ≤ 1 := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := hn
    rw [mangoldtCoefficient_prime_pow _ hp.nat_prime (Nat.ne_of_gt hk)]
    exact ofDirichletCharacter_primePower_norm_le χ p k
  · rw [mangoldtCoefficient, ite_eq_right hn, norm_zero]
    exact zero_le_one

end PseudoPrime.LLS.Extensions.GeneralLFunction
