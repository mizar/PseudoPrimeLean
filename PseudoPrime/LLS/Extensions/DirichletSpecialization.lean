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

namespace PseudoPrime.LLS.PaperStatements

/-- For `x ≥ 1` and a positive integer below its cutoff, the logarithmic L-value weight
is nonnegative. The logarithms of the index and `x/n` are nonnegative.
Total division also covers the endpoints with zero logarithm. -/
private theorem logValueWeight_nonneg {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊) :
    0 ≤
      ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n) *
        (Real.log (x / n) / Real.log x) := by
  have h := Finset.mem_Ioc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h.1
  have hnx : (n : ℝ) ≤ x :=
    (by exact_mod_cast h.2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le (zero_le_one.trans hx))
  have hl : 0 ≤ Real.log (x / n) := Real.log_nonneg ((one_le_div₀ hn0).mpr hnx)
  exact
    mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (mul_nonneg hn0.le (Real.log_natCast_nonneg n)))
      (div_nonneg hl (Real.log_nonneg hx))

/-- For any complex Dirichlet character and `x ≥ 1`, the norm of its logarithmic L-value
sum is at most the unsigned sum. Apply the extension's finite coefficient estimate to
degree-one data and use weight nonnegativity. This supplies the arithmetic upper comparison
for Theorem 1.5 without primitivity or GRH. -/
theorem norm_characterLogLValueSum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 1 ≤ x) : ‖characterLogLValueSum χ x‖ ≤ logLValueSum x := by
  let w : ℕ → ℝ := fun n ↦
    ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n) * (Real.log (x / n) / Real.log x)
  have h :=
    Extensions.GeneralLFunction.norm_finiteWeightedSum_le_of_bound
      (Extensions.GeneralLFunction.ofDirichletCharacter χ)
      (Extensions.GeneralLFunction.ofDirichletCharacter_mangoldtCoefficient_norm_le χ)
      (Finset.Ioc 0 ⌊x⌋₊) w
  have hs : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, |w n|) = logLValueSum x := by
    apply Finset.sum_congr rfl
    intro n hn
    exact abs_of_nonneg (logValueWeight_nonneg hx hn)
  change
    ‖(Extensions.GeneralLFunction.ofDirichletCharacter χ).logValueSum x‖ ≤
      1 * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, |w n| at h
  simpa only [Extensions.GeneralLFunction.ofDirichletCharacter_logValueSum, one_mul, hs] using h

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- The real digamma value at one half is the even-character endpoint constant.
Take real parts of the complex special value and convert the logarithm of two.
This supplies the gamma term in the degree-one logarithmic formula. -/
private theorem digamma_one_half_re :
    (Complex.digamma (1 / 2)).re = -2 * Real.log 2 - Real.eulerMascheroniConstant := by
  rw [Complex.digamma_one_half]
  simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.re_ofNat, Complex.im_ofNat, neg_zero, zero_mul, sub_zero]
  rw [show (Complex.log (2 : ℂ)).re = Real.log 2 from Complex.log_ofReal_re 2]

/-- The gamma endpoint of degree-one character data equals the parity constant in Lemma 2.5.
The singleton gamma sum reduces to digamma at one half or one; no RH or primitivity is needed.
This identifies the deterministic term of the generalized logarithmic formula. -/
theorem ofDirichletCharacter_gammaLogDerivativeAtOne {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (ofDirichletCharacter χ).gammaLogDerivativeAtOne =
      Real.log ((q : ℝ) / Real.pi) / 2 +
        (if χ (-1) = 1 then -2 * Real.log 2 - Real.eulerMascheroniConstant
          else -Real.eulerMascheroniConstant) /
          2 := by
  change
    Real.log ((q : ℝ) / Real.pi ^ 1) / 2 +
        (∑ _j : Fin 1, (Complex.digamma ((1 + if χ (-1) = 1 then 0 else 1) / 2)).re) / 2 =
      _
  rw [Fin.sum_univ_one, pow_one]
  split_ifs with h
  · rw [add_zero, digamma_one_half_re]
  · norm_num only [Complex.digamma_one, Complex.neg_re, Complex.ofReal_re]

/-- The conductor and parity normalization never vanish, for any nonzero modulus.
Nonzero complex powers and positivity of the square root of pi prove the claim.
Consequently normalization preserves the completed-zero set. -/
private theorem completionScale_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (q : ℂ) ^ (s / 2) * (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ)) ≠ 0 := by
  apply mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q))))
  split_ifs with h
  · exact one_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))

/-- The normalized completion vanishes exactly at the character's completed zeros.
Cancel the nonzero conductor and parity factor. This transports RH and reindexes zero mass. -/
theorem ofDirichletCharacter_completed_eq_zero_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) : (ofDirichletCharacter χ).completed s = 0 ↔ χ.completedLFunction s = 0 := by
  change
    ((q : ℂ) ^ (s / 2) * (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ))) *
          χ.completedLFunction s =
        0 ↔
      _
  rw [mul_eq_zero]
  exact or_iff_right (completionScale_ne_zero χ s)

/-- Individual RH of a primitive nontrivial character gives RH of its degree-one data.
Normalization preserves zeros, and reflection excludes trivial completed zeros.
This uses the precise hypothesis of Lemma 2.5 rather than global Dirichlet GRH. -/
theorem ofDirichletCharacter_riemannHypothesis {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) :
    (ofDirichletCharacter χ).RiemannHypothesis := by
  intro ρ
  exact
    AnalyticNumberTheory.DirichletLFunction.completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp
      (inv_ne_one.mpr hne) ((ofDirichletCharacter_completed_eq_zero_iff χ ρ).mp ρ.property)

/-- The normalization factor is entire, since its complex-power base is nonzero.
Differentiate the exponent and multiply by the constant parity factor.
Analyticity of this unit is needed to compare completed-zero multiplicities. -/
private theorem differentiable_completionScale {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ
      (fun z : ℂ ↦ (q : ℂ) ^ (z / 2) * (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ))) := by
  exact
    ((differentiable_id.div_const 2).const_cpow
          (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))).mul_const
      _

/-- For a nontrivial character, normalization preserves analytic multiplicity at every point.
Its factor is an analytic unit of order zero, so additivity of order gives the equality.
This identifies the actual multiplicities used in the generalized zero mass. -/
theorem ofDirichletCharacter_analyticOrderNatAt_completed {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) :
    analyticOrderNatAt (ofDirichletCharacter χ).completed s =
      analyticOrderNatAt χ.completedLFunction s := by
  change
    analyticOrderNatAt
        ((fun z : ℂ ↦ (q : ℂ) ^ (z / 2) * (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ))) *
          χ.completedLFunction)
        s =
      _
  have ho :
    analyticOrderAt
        (fun z : ℂ ↦ (q : ℂ) ^ (z / 2) * (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ))) s =
      0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (completionScale_ne_zero χ s))
  unfold analyticOrderNatAt
  rw [analyticOrderAt_mul ((differentiable_completionScale χ).analyticAt s)
      ((DirichletCharacter.differentiable_completedLFunction hne).analyticAt s),
    ho, zero_add]

/-- For a nontrivial character, the normalized zero mass is the original completed-zero sum.
Reindex by the unchanged zero set and use equality of analytic multiplicities.
This is the subtype form of the mass needed to specialize the generalized formula. -/
theorem ofDirichletCharacter_zeroMass_eq_subtype_tsum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
    (ofDirichletCharacter χ).zeroMass =
      ∑' ρ : { z : ℂ // χ.completedLFunction z = 0 },
        (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2 := by
  let e : (ofDirichletCharacter χ).Zero ≃ { z : ℂ // χ.completedLFunction z = 0 } :=
    Equiv.subtypeEquivProp (funext fun z ↦ propext (ofDirichletCharacter_completed_eq_zero_iff χ z))
  rw [← e.tsum_eq (fun ρ ↦ (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2)]
  apply tsum_congr
  intro ρ
  change
    (analyticOrderNatAt (ofDirichletCharacter χ).completed (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2 =
      (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2
  rw [ofDirichletCharacter_analyticOrderNatAt_completed χ hne]

/-- The normalized mass equals the divisor-weighted mass of the character's completed function.
Extend the zero-subtype sum by zero, convert analytic order to divisor multiplicity,
and identify squared norm with `Complex.normSq`. This connects the general mass to `primitiveBRe`.
Only nontriviality is needed; the equality does not assume RH or convergence. -/
theorem ofDirichletCharacter_zeroMass_eq_divisor_tsum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
    (ofDirichletCharacter χ).zeroMass =
      ∑' z : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ z : ℝ) / Complex.normSq z := by
  rw [ofDirichletCharacter_zeroMass_eq_subtype_tsum χ hne]
  exact
    AnalyticNumberTheory.General.tsum_zeroMultiplicity_eq_divisor
      (DirichletCharacter.differentiable_completedLFunction hne)

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive nonprincipal character of modulus at least two under its individual RH,
the degree-one zero mass equals `2 * |primitiveBRe χ|`. Convert the normalized mass to the
completed function's divisor sum and apply the single-character mass identity.
This supplies the zero-mass substitution in Lemma 2.5 without RH for other characters. -/
theorem ofDirichletCharacter_zeroMass_eq_two_mul_abs_BRe_of_dirichletRH {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) :
    (ofDirichletCharacter χ).zeroMass =
      2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| := by
  rw [ofDirichletCharacter_zeroMass_eq_divisor_tsum χ hne]
  exact tsum_divisor_inv_normSq_eq_two_mul_abs_BRe_of_dirichletRH hq hRH hp hne (inv_ne_one.mpr hne)

/-- Under GRH, the degree-one mass is twice the absolute real Hadamard constant.
The modulus is at least two and the character is primitive and nontrivial.
Use the divisor-mass identity after normalization. This supplies the mass term for Theorem 1.5. -/
theorem ofDirichletCharacter_zeroMass_eq_two_mul_abs_BRe {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (ofDirichletCharacter χ).zeroMass =
      2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| := by
  exact ofDirichletCharacter_zeroMass_eq_two_mul_abs_BRe_of_dirichletRH χ hq hp hne (hGRH q χ hp)

end PseudoPrime.LLS.Extensions.GeneralLFunction

namespace PseudoPrime.LLS.PaperStatements

/-- For `x ≥ 1`, the real part of the character logarithmic L-value sum is at most
its unsigned counterpart. The extension's degree-one norm comparison supplies the bound.
This is the arithmetic upper-bound input to Theorem 1.5. -/
theorem characterLogLValueSum_re_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 1 ≤ x) : (characterLogLValueSum χ x).re ≤ logLValueSum x := by
  exact (Complex.re_le_norm _).trans (norm_characterLogLValueSum_le χ hx)

/-- For a primitive character of modulus at least three under individual RH and `x ≥ 2`,
the general logarithmic formula gives the parity-dependent formula of Lemma 2.5.
The general formula, admissibility of the degree-one data, and its mass identity are
explicit premises. Transport RH, substitute the arithmetic sum, gamma endpoint and mass,
and rearrange the two bounded errors. This is the specialization interface used by the
mass-free and admissibility-free versions. -/
theorem characterLogLValue_formula_of_general (hformula : Extensions.lls_propL1_general) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ)
    (hf : (Extensions.GeneralLFunction.ofDirichletCharacter χ).IsAdmissible)
    (hMass :
      (Extensions.GeneralLFunction.ofDirichletCharacter χ).zeroMass =
        2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ|)
    {x : ℝ} (hx : 2 ≤ x) :
    ∃ θ₁ θ₂ : ℝ,
      |θ₁| ≤ 1 ∧
        |θ₂| ≤ 1 ∧
        Real.log ‖χ.LFunction 1‖ =
          (characterLogLValueSum χ x).re +
                (1 / Real.log x) *
                  (Real.log ((q : ℝ) / Real.pi) / 2 +
                    (if χ (-1) = 1 then -2 * Real.log 2 - Real.eulerMascheroniConstant
                      else -Real.eulerMascheroniConstant) /
                      2) -
              (1 / Real.log x + 2 * θ₁ / (Real.sqrt x * (Real.log x) ^ 2)) *
                |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
            2 * θ₂ / (x * (Real.log x) ^ 2) := by
  have hne := primitiveCharacter_ne_one_of_three_le hq hp
  have hRHf := Extensions.GeneralLFunction.ofDirichletCharacter_riemannHypothesis χ hp hne hRH
  obtain ⟨θ₁, θ₂, hθ₁, hθ₂, he⟩ :=
    (hformula (Extensions.GeneralLFunction.ofDirichletCharacter χ) hf hRHf).2 x hx
  rw [Extensions.GeneralLFunction.ofDirichletCharacter_logValueSum,
    Extensions.GeneralLFunction.ofDirichletCharacter_gammaLogDerivativeAtOne, hMass] at he
  simp only [Extensions.GeneralLFunction.ofDirichletCharacter, Nat.cast_one, mul_one] at he
  refine ⟨θ₁, θ₂, hθ₁, hθ₂, ?_⟩
  convert he using 1
  ring

/-- For a primitive character of modulus at least three under individual RH and `x ≥ 2`,
assume the general logarithmic formula and admissibility of its degree-one data.
Identify zero mass as twice the absolute real Hadamard constant using this character's RH,
then apply the specialization formula. The mass identity is derived rather than assumed;
the remaining premises are the formula and admissibility. -/
theorem characterLogLValue_formula_of_general_of_admissible
    (hformula : Extensions.lls_propL1_general) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ)
    (hf : (Extensions.GeneralLFunction.ofDirichletCharacter χ).IsAdmissible) {x : ℝ} (hx : 2 ≤ x) :
    ∃ θ₁ θ₂ : ℝ,
      |θ₁| ≤ 1 ∧
        |θ₂| ≤ 1 ∧
        Real.log ‖χ.LFunction 1‖ =
          (characterLogLValueSum χ x).re +
                (1 / Real.log x) *
                  (Real.log ((q : ℝ) / Real.pi) / 2 +
                    (if χ (-1) = 1 then -2 * Real.log 2 - Real.eulerMascheroniConstant
                      else -Real.eulerMascheroniConstant) /
                      2) -
              (1 / Real.log x + 2 * θ₁ / (Real.sqrt x * (Real.log x) ^ 2)) *
                |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
            2 * θ₂ / (x * (Real.log x) ^ 2) := by
  have hne := primitiveCharacter_ne_one_of_three_le hq hp
  have hMass :=
    Extensions.GeneralLFunction.ofDirichletCharacter_zeroMass_eq_two_mul_abs_BRe_of_dirichletRH χ
      (Nat.le_trans (by norm_num only : 2 ≤ 3) hq) hp hne hRH
  exact characterLogLValue_formula_of_general hformula χ hq hp hRH hf hMass hx

/-- The general logarithmic formula implies Lemma 2.5 when degree-one primitive
character data at modulus at least three is assumed admissible. Introduce the parameters
of the numbered statement and use the mass-free specialization under individual RH.
This packages the implication with the admissibility premise explicit. -/
theorem lls_lemma25_of_general (hformula : Extensions.lls_propL1_general)
    (hadmissible :
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        3 ≤ q → χ.IsPrimitive → (Extensions.GeneralLFunction.ofDirichletCharacter χ).IsAdmissible) :
    lls_lemma25 := by
  intro q _ χ hq hp hRH x hx
  exact
    characterLogLValue_formula_of_general_of_admissible hformula χ hq hp hRH (hadmissible q χ hq hp)
      hx

end PseudoPrime.LLS.PaperStatements
