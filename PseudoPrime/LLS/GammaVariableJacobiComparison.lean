/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeCharacterComparison

/-! # Variable-scale signed Jacobi comparison without a decimal input gate -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal data with 3 ≤ m ≤ q, q ≥ 20000, GRH and x ≥ 2,
bound the actual arithmetic sum by the resolvent zero mass, pole allowance,
exact nonpositive conductor integral and conductor-free remainder.
Combine the signed completed formula with the absolutely convergent zero majorant.
This retains the negative conductor gain for the Jacobi comparison. -/
theorem gamma_primitive_sum_re_le_resolvent_signed_conductor {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            Analysis.gammaResolventMajorant ρ.im) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        Analysis.gammaNegativeConductorTerm (Real.log m) x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hr := re_gamma_primitive_remainder_le_signed_conductor hq hm hmq hp hne hinv hGRH hx
  have hz :=
    norm_gamma_oscillatingZeroSum_le_resolvent (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm)
      (hGRH m χ hp) hp hne hinv (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx)
  have hn := Complex.re_le_norm (-(∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hn
  simp only [Complex.add_re] at hr
  linarith only [hr, hz, hn]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- The exact finite ambient correction at positive scale x for the primitive Jacobi
character of an odd nonsquare input. Sum the signed local ramp series over prime
factors of 4n, including two. No asymptotic input gate is imposed by this definition.
The correction is used in the variable-scale no-negative arithmetic comparison. -/
noncomputable def gammaJacobiAmbientRamp {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (x : ℝ) : ℝ :=
  ∑ p ∈ (4 * n).primeFactors,
    Real.log p *
      ((∑' k : ℕ,
          Analysis.exponentialRampLocalCorrection (bridge.character p) ((p : ℝ) ^ (k + 1) / x)
            (k + 1)) /
        Real.sqrt x)

/-- The variable-scale arithmetic upper budget for an actual primitive Jacobi character.
Inputs are its arithmetic bridge, ambient pole modulus q, scale x and any finite prefix B.
Retain signed Gamma and Euler terms, exact prefix loss and ambient ramp correction,
the signed conductor integral, and the pole and 43 x^(-9/16) costs. The comparison
theorem supplies its hypotheses; this definition imposes no lower bound on the input. -/
noncomputable def gammaJacobiActualBudget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (q : ℕ) (x : ℝ) (B : Finset ℕ) :
    ℝ :=
  (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (Analysis.gammaResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
      2 * (∑ k ∈ B, Analysis.gammaResolventMangoldtWeight k) +
    (∑ k ∈ B, (1 - (bridge.character k).re) * Analysis.gammaResolventMangoldtWeight k) +
    gammaJacobiAmbientRamp bridge x +
    ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
    Analysis.gammaNegativeConductorTerm
      (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor) x +
    43 * x ^ (-9 / 16 : ℝ)

/-- For every odd nonsquare input, GRH and x ≥ 2, absence of negative odd-prime
witnesses through 99x/40 bounds the actual ramp-minus-principal quantity by the
exact variable-scale budget. The only ambient restriction is q ≥ max(20000,m),
where m is the actual primitive conductor. Apply signed zero-prefix and completed
arithmetic comparisons and retain the finite ambient correction without a large-input
local envelope. This is the small-start numerical-gap interface. -/
theorem gamma_jacobi_no_negative_actual_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x : ℝ} (hx : 2 ≤ x)
    (B : Finset ℕ)
    (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1) :
    2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re ≤
      gammaJacobiActualBudget bridge q x B := by
  have hm := gamma_jacobi_modulus_ge_three bridge
  have hinv : bridge.character⁻¹ ≠ 1 := by
    rw [bridge.character_quadratic.inv]
    exact bridge.character_ne_one
  have hc :=
    PaperStatements.gamma_primitive_sum_re_le_resolvent_signed_conductor hq hm hmq hGRH
      bridge.character_primitive bridge.character_ne_one hinv hx
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_zeroMass_le_signed_prefix
      (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm)
      (hGRH _ bridge.character bridge.character_primitive) bridge.character_primitive
      bridge.character_ne_one hinv B
  have ha :=
    gamma_jacobi_no_negative_ramp_comparison bridge
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx) hno
  have hgf : bridge.character.gammaFactor = Complex.Gammaℝ :=
    funext (fun z ↦ bridge.character_even.gammaFactor_def z)
  rw [hgf] at hz
  dsimp only [gammaJacobiActualBudget, gammaJacobiAmbientRamp]
  linarith only [hc, hz, ha]

/-- With GRH and an ambient pole modulus at least 20000 and the actual conductor,
a strict gap between the exact budget and ramp-minus-principal quantity gives
a negative odd-prime Jacobi witness through 99x/40, at any scale x ≥ 2.
Negating existence supplies the preceding comparison hypothesis. No decimal
input bound or finite-input certificate is used. -/
theorem exists_odd_prime_negative_of_actual_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x : ℝ} (hx : 2 ≤ x)
    (B : Finset ℕ)
    (hgap :
      gammaJacobiActualBudget bridge q x B <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  by_contra hnot
  have hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1 :=
    fun p hp hodd hcut hj ↦ hnot ⟨p, hp, hodd, hcut, hj⟩
  exact (not_le_of_gt hgap) (gamma_jacobi_no_negative_actual_comparison bridge hGRH hq hmq hx B hno)

/-- For every odd nonsquare input and GRH, take the ambient modulus to be
max(20000,m), where m is the actual conductor. At x ≥ 2, a strict actual-budget
gap implies a negative odd-prime Jacobi witness through 99x/40.
The ambient inequalities follow from max; the input has no extra lower bound.
This supplies a uniform interface for small analytic starting points. -/
theorem exists_odd_prime_negative_of_canonical_actual_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 2 ≤ x)
    (B : Finset ℕ)
    (hgap :
      gammaJacobiActualBudget bridge
          (max 20000 (NumberTheory.complexQuadraticCharacter n hn).conductor) x B <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  exact
    exists_odd_prime_negative_of_actual_gap bridge hGRH (le_max_left _ _) (le_max_right _ _) hx B
      hgap

/-- Under GRH, if the canonical actual-budget gap holds at x=(32/99)(log n)^2
and x ≥ 2, an odd-prime Jacobi witness with value minus one is at most
(4/5)(log n)^2 and strictly below (log n)^2. Substitute the common scale and
use its positivity. The scalar gap remains explicit, with no claimed starting point. -/
theorem exists_odd_prime_negative_log_sq_of_actual_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hx : 2 ≤ (32 / 99 : ℝ) * (Real.log n) ^ 2) (B : Finset ℕ)
    (hgap :
      gammaJacobiActualBudget bridge
          (max 20000 (NumberTheory.complexQuadraticCharacter n hn).conductor)
          ((32 / 99 : ℝ) * (Real.log n) ^ 2) B <
        2 *
            (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum
                ((32 / 99 : ℝ) * (Real.log n) ^ 2) /
              Real.sqrt ((32 / 99 : ℝ) * (Real.log n) ^ 2)) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                ((32 / 99 : ℝ) * (Real.log n) ^ 2) k).re) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧ (p : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨p, hp, hodd, hbound, hj⟩ :=
    exists_odd_prime_negative_of_canonical_actual_gap bridge hGRH hx B hgap
  refine ⟨p, hp, hodd, hj, ?_, ?_⟩
  · nlinarith only [hbound]
  · nlinarith only [hbound, hx]

/-- At arbitrary scale, a finite integer prefix and the exact ambient ramp
combine into prime-local costs whenever no negative Jacobi odd-prime witness
occurs up to the prefix endpoint b ≥ 1. Transfer to unit-prime character value one
and use the existing full-power prefix identity. No RH or input-size gate is needed.
This is the local-cost interface for the actual variable-scale budget. -/
theorem gamma_jacobi_prefix_add_ambient_ramp_eq_local_cost {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {b : ℝ} (hb : 1 ≤ b)
    (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ b → jacobiSym n p ≠ -1) (x : ℝ) :
    (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊,
          (1 - (bridge.character k).re) * Analysis.gammaResolventMangoldtWeight k) +
        gammaJacobiAmbientRamp bridge x =
      ∑ p ∈ (4 * n).primeFactors,
        Analysis.gammaActualPrimeLocalCost bridge.character p
          (AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b p) x := by
  exact
    AnalyticNumberTheory.DirichletLFunction.gamma_character_prefix_add_ambient_ramp_eq_local_cost
      bridge.character (mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos) hb
      (gamma_jacobi_no_negative_prefix_prime_one bridge hno) x

/-- For an odd nonsquare input under GRH, x ≥ 2 and prefix 1 ≤ b ≤ 99x/40,
an upper bound U on the actual ambient prime-local costs gives the no-negative
arithmetic comparison below. Retain the exact conductor and signed integral.
Group the full positive-power prefix before applying U, so no large-input local
envelope is required. The bound U is the explicit remaining local certification task. -/
theorem gamma_jacobi_no_negative_local_upper_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b U : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * x)
    (hU :
      (∑ p ∈ (4 * n).primeFactors,
          Analysis.gammaActualPrimeLocalCost bridge.character p
            (AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b p) x) ≤
        U)
    (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1) :
    2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
            (Analysis.gammaResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) * (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
        U +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        Analysis.gammaNegativeConductorTerm
          (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor) x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hc :=
    gamma_jacobi_no_negative_actual_comparison bridge hGRH hq hmq hx (Finset.Ioc 0 ⌊b⌋₊) hno
  have he :=
    gamma_jacobi_prefix_add_ambient_ramp_eq_local_cost bridge hb
      (fun p hp hodd hpb ↦ hno p hp hodd (hpb.trans hbX)) x
  dsimp only [gammaJacobiActualBudget] at hc
  linarith only [hc, he, hU]

/-- With the preceding local-cost cap and an arbitrary-scale strict numerical
gap, a negative odd-prime Jacobi witness occurs below 99x/40.
Use contradiction and the local upper comparison, keeping the prefix and conductor
gains. The cap and gap are hypotheses, not asserted numerical certificates. -/
theorem exists_odd_prime_negative_of_local_upper_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b U : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * x)
    (hU :
      (∑ p ∈ (4 * n).primeFactors,
          Analysis.gammaActualPrimeLocalCost bridge.character p
            (AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b p) x) ≤
        U)
    (hgap :
      (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
              (Analysis.gammaResolventCoefficients.map
                  (fun ab ↦
                    (ab.2 : ℝ) *
                      (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
              (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
            2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
          U +
          ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
          Analysis.gammaNegativeConductorTerm
            (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor) x +
          43 * x ^ (-9 / 16 : ℝ) <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  by_contra hnot
  have hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1 :=
    fun p hp hodd hcut hj ↦ hnot ⟨p, hp, hodd, hcut, hj⟩
  exact
    (not_le_of_gt hgap)
      (gamma_jacobi_no_negative_local_upper_comparison bridge hGRH hq hmq hx hb hbX hU hno)

end PseudoPrime.LLS
