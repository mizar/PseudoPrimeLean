/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements
public import PseudoPrime.LLS.LogLValueIntegral
public import PseudoPrime.LLS.LValueNumerics
public import PseudoPrime.LLS.ClassNumberBounds
public import PseudoPrime.NumberTheory.QuadraticDiscriminantSplitting
public import PseudoPrime.LLS.MellinKernelBounds
public import PseudoPrime.LLS.MellinKernelZeros
public import PseudoPrime.LLS.MellinKernelCharacterBounds
public import PseudoPrime.LLS.TheoreticalPrimeBounds
public import PseudoPrime.LLS.CosetCoarseBounds
public import PseudoPrime.LLS.PrimePowerComparison
public import PseudoPrime.LLS.PrimePowerEvenComparison
public import PseudoPrime.LLS.PrimePowerFiniteComparison
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CommonFactorSeries
public import PseudoPrime.LLS.Corollary11
public import PseudoPrime.LLS.Corollary12
public import PseudoPrime.LLS.DirichletExplicitFormula
public import PseudoPrime.LLS.RiemannExplicitFormula
public import PseudoPrime.LLS.Theorem11S1GRH
public import PseudoPrime.LLS.Theorem11S2
public import PseudoPrime.LLS.Extensions.DirichletAdmissibility
public import PseudoPrime.LLS.Extensions.PaperProofs

/-!
# Public proofs of the numbered LLS paper statements

Only proofs with exactly the premises and conclusions of `PaperStatements.lean`
are exported here. Derived inequalities and conditional analytic interfaces remain
in their implementation modules. For Theorem 1.3, only the restriction to indices
at least seven is exported; the full statement remains without a public proof.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Theorem 1.1 follows from GRH: combine the existing general-character proof
of Part 1 with the small-prime-exclusion proof of Part 2. No additional analytic
assumptions are imposed. This is the public proof of the complete numbered statement. -/
theorem lls_theorem11_proof : lls_theorem11 := fun hGRH ↦
  ⟨llsTheorem11S1_of_grh hGRH, llsTheorem11S2_of_grh hGRH⟩

/-- Corollary 1.1 follows from the strict GRH character bound for large prime levels
and kernel-checked nonsquare certificates for smaller levels. Natural well-ordering
preserves the strict bound for the least positive quadratic nonresidue. -/
theorem lls_corollary11_proof : lls_corollary11 := fun hGRH q hp h5 ↦
  if hq : q < 3000 then exists_least_positive_nonsquare_lt_log_sq_small hp h5 hq
  else
    exists_least_positive_nonsquare_lt
      (exists_positive_nonsquare_lt_log_sq_large hp (Nat.le_of_not_gt hq) hGRH)

/-- Under GRH, the least prime outside a proper subgroup satisfies Theorem 1.2
for sufficiently large moduli. Specialize the uniform kernel comparison to the
gamma kernel, use the certified mass and parameter choices, and contradict any
least prime beyond the resulting cutoff. -/
theorem lls_theorem12_proof : lls_theorem12 := by exact theorem12

/-- Under GRH, Theorem 1.3 holds uniformly for each fixed index at least seven.
Use the triangular kernel for indices at least twenty-eight and the gamma-kernel
comparison for indices seven through twenty-seven, as combined in the index bound. -/
theorem lls_theorem13_of_index_ge_seven_proof : lls_theorem13_of_index_ge_seven := by
  intro hGRH h hh ε hε
  exact triangular_asymptotic_prime_bound_of_index_ge_seven hGRH h hh ε hε

/-- Under GRH, the least prime in every proper coset satisfies Theorem 1.4 for
moduli at least twenty thousand. The character comparison gives a coarse bound
when the cutoff contains no prime; the complete radius comparison then contradicts
a least prime above both the exceptional cutoff and the paper's squared radius. -/
theorem lls_theorem14_proof : lls_theorem14 := by exact theorem14

/-- Under GRH, Corollary 1.2 bounds the least prime in every unit residue
by `(φ(q) log q)²` for `q > 3`. Combine the checked finite routes and shared
analytic intervals with the uniform large-modulus estimate.
This exports the original numbered statement with no extra premises. -/
theorem lls_corollary12_proof : lls_corollary12 := by
  intro hGRH q _ hq a
  exact exists_least_prime_in_residue_le_totient_log_sq (Nat.succ_le_of_lt hq) a hGRH

/-- Under GRH, Theorem 1.5 gives both explicit bounds for every primitive
character modulo q ≥ 10^10. Combine the logarithmic upper and lower estimates
at the paper's cutoff with the certified exponential conversions. The constants
and factors agree with the original statement, without further analytic premises. -/
theorem lls_theorem15_proof : lls_theorem15 := by
  intro hGRH q _ χ hq hp
  exact ⟨lValue_upper_bound χ hq hp hGRH, lValue_reciprocal_bound χ hq hp hGRH⟩

/-- Under GRH, Corollary 1.3 gives the stated upper and lower class-number bounds
for every imaginary quadratic field of discriminant `-q` with `q ≥ 10^10`.
Construct a primitive character modulo q whose values agree with the splitting of
every rational prime, then derive ideal counts, Dedekind factorization and the
class-number formula.
The explicit L-value bounds give the paper's constants without further premises. -/
theorem lls_corollary13_proof : lls_corollary13 := by
  apply lls_corollary13_of_prime_splitting
  intro q _ K _ _ _ hdeg hd
  obtain ⟨χ, hprim, _hquad, _hodd, hlocal⟩ :=
    NumberTheory.exists_primitive_character_splitting_of_discr q K hdeg hd
  exact ⟨χ, hprim, hlocal⟩

/-- Under RH and `x > 1`, the logarithmically weighted Mangoldt sum has the formula
of Lemma 2.1, including its full trivial-zero correction series and a real error coefficient
of absolute value at most one. Bound the nontrivial-zero and xi endpoint errors, convert
the norm bound to a real coefficient, and substitute the exact trivial-zero series.
This proves the numbered statement with its original hypotheses. -/
theorem lls_lemma21_proof : lls_lemma21 := by
  intro hRH x hx
  obtain ⟨θ, hθ, he⟩ := exists_theta_mul_of_abs_le (abs_logWeightedMangoldtSum_error_le hRH hx)
  refine ⟨θ, hθ, ?_⟩
  rw [logTrivialZeroSeries_paper_eq hx]
  nlinarith only [he]

/-- Under GRH, for a primitive character of modulus at least three and `x > 1`,
the character's logarithmically weighted sum satisfies both clauses of Lemma 2.2.
Use the complex contour formula with the exact parity correction, then take real parts
to obtain the second clause. The complex and real error coefficients are chosen separately. -/
theorem lls_lemma22_proof : lls_lemma22 := by
  intro hGRH q _ χ hq hp x hx
  have hc := characterLogWeightedSum_complex_formula hq hp hGRH hx
  exact ⟨hc, characterLogWeightedSum_real_of_complex hq hp hGRH x hc⟩

/-- Under GRH, for a primitive character of modulus at least three and `x > 1`,
prove the complex reciprocal formula and the zero-mass identity of Lemma 2.3.
The contour formula and functional equation give the complex clause; taking real parts
and using positivity of the inverse factor gives the real clause, with a bounded error
coefficient in each. This preserves both conclusions of the numbered statement. -/
theorem lls_lemma23_proof : lls_lemma23 := by
  intro hGRH q _ χ hq hp x hx
  have hc := characterReciprocalWeightedSum_complex_formula hq hp hGRH hx
  exact ⟨hc, characterReciprocalWeightedSum_real_of_complex hq hp hGRH hx hc⟩

/-- Under RH and `x > 1`, the smoothed reciprocal Mangoldt sum satisfies Lemma 2.4
with a real error coefficient of absolute value at most one. Use the exact trivial-zero
series limit and the nontrivial-zero norm bound, then normalize the real error.
This proves the numbered formula without adding an endpoint or convergence premise. -/
theorem lls_lemma24_proof : lls_lemma24 := by
  intro hRH x hx
  obtain ⟨θ, hθ, he⟩ :=
    exists_theta_mul_of_abs_le (abs_reciprocalWeightedMangoldtSum_error_le hRH hx)
  rw [riemannReciprocalTrivialZeroSeries_eq_paper] at he
  refine ⟨θ, hθ, ?_⟩
  simp only [div_eq_mul_inv] at he ⊢
  nlinarith only [he]

/-- For a primitive character of level at least three, its individual Riemann
hypothesis implies the complete formula of Lemma 2.5 for every x ≥ 2.
Specialize the proved general L-function formula to the admissible degree-one data;
identify its arithmetic sum, zero mass and parity-dependent gamma endpoint.
The two bounded real errors retain the constants of the numbered statement. -/
theorem lls_lemma25_proof : lls_lemma25 := by
  exact lls_lemma25_of_general_formula Extensions.lls_propL1_general_proof

/-- Under RH, Lemma 2.6 holds for every x ≥ exp 1: the logarithmic Mangoldt sum
equals log log x+gamma-1+gamma/log x plus the stated zero and gamma errors.
Evaluate the combined zeta main integral and normalize the integrated residues separately
to obtain real coefficients of absolute value at most one. The signed zero constant
and both error denominators agree with the numbered statement. -/
theorem lls_lemma26_proof : lls_lemma26 := by
  intro hRH x hx
  apply logLValueSum_eq_main_with_bounded_errors hRH
  exact (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hx

/-- Lemma 3.1 holds for `m ≥ 3` and `x ≥ 2` without RH or GRH.
Finite prime-power estimates give the logarithmic and reciprocal bounds.
The unrestricted reciprocal series is summable and equals the prime-factor sum
by unique prime-power reindexing and exact geometric summation. -/
theorem lls_lemma31_proof : lls_lemma31 := by
  intro m x hm hx
  have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hm)
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  have he := AnalyticNumberTheory.Arithmetic.tsum_commonFactorReciprocalTerm hm0
  refine ⟨?_, ?_, he⟩
  · nlinarith only [AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum_le hm0 hx0]
  · change
      AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum x m ≤
        ∑' n : ℕ, AnalyticNumberTheory.Arithmetic.commonFactorReciprocalTerm m n
    rw [he]
    exact AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum_le hm0 hx0

/-- For any complex Dirichlet character of nonzero modulus and real `x ≥ 100`,
the alternating prime-power sum is at most the real character-weighted sum of Lemma 5.1.
For primes at least three, the first term dominates the even losses. At two, the first five
terms and an even-tail bound give the comparison. Zero character values use the nonpositive
alternating sum. Reindex Mangoldt support by prime powers to combine the comparisons;
no RH or primitivity assumption is used. -/
theorem lls_lemma51_proof : lls_lemma51 := by
  intro q _ χ x hx
  exact character_primePower_comparison_lower χ hx

/-- Under GRH, every admissible Mellin kernel satisfies the principal and nonprincipal
smoothed character estimates of Lemma 6.1, uniformly in modulus and scale. Apply the
principal contour bound and the primitive-character formula with its level correction;
the sharp ambient zero-mass bound supplies the nonprincipal coefficient. -/
theorem lls_lemma61_proof : lls_lemma61 := by exact MellinKernel.lemma61

/-- Under GRH, every admissible Mellin kernel satisfies Proposition 6.1 uniformly
in the modulus, subgroup, and positive cutoff. Combine the sharp finite principal
upper bound with the weighted Mangoldt integral limit; absorb the uniform errors
at large scales and use the growing modulus to cover bounded scales. -/
theorem lls_proposition61_proof : lls_proposition61 := by exact MellinKernel.proposition61

end PseudoPrime.LLS.PaperStatements
