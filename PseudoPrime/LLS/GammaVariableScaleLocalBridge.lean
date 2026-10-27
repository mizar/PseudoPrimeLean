/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaVariableScaleLocalBounds
public import PseudoPrime.LLS.GammaVariableJacobiComparison
public import PseudoPrime.LLS.GammaSmallScaleLocalBridge
public import PseudoPrime.LLS.GammaQuadraticPolynomialSeparation

/-! # Scale-dependent factorization-independent Jacobi witness budgets -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: an odd nonsquare Jacobi bridge, selected minus-one factors and x>=1.
Claim: conductor, square and dyadic costs fit the variable mass times log(4n)
plus the dyadic allowance. Proof: separate odd and even conductor branches.
Role: retain scale dependence without a fixed local entrance. -/
theorem gamma_jacobi_square_dyadic_variable_scale {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hχ : ∀ p ∈ S, bridge.character p = -1) (K : ℕ → Finset ℕ)
    (K2 : Finset ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 x ≤
      Analysis.gammaVariableSquareMass x * Real.log (4 * (n : ℝ)) +
        Analysis.gammaVariableDyadicAllowance x := by
  have hd := gamma_jacobi_modulus_squarefree_data bridge
  have hf : 0 < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (gamma_jacobi_modulus_eq_discriminant bridge).symm ▸ bridge.discriminant_pos
  have hdecomp : n = bridge.squarefreePart * bridge.squareFactor ^ 2 := by
    simpa only [Nat.mul_comm] using bridge.squarefreePart_sq_mul.symm
  rcases gamma_jacobi_actual_dyadic_branch bridge with ⟨hfd, htwo⟩ | heven
  · have hnf :
      n = (NumberTheory.complexQuadraticCharacter n hn).conductor * bridge.squareFactor ^ 2 := by
      rw [hfd]
      exact hdecomp
    have hs :=
      Analysis.gamma_actual_odd_square_absorbed_variable hnf hn hf bridge.squareFactor_odd.pos S hS
        bridge.character hχ K hx
    have ht :
      Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 x -
          Analysis.gammaVariableSquareMass x * Real.log 4 ≤
        Analysis.gammaVariableDyadicAllowance x := by
      rcases htwo with h2 | h2
      · have hc :=
          Analysis.gamma_actual_one_prime_cost_nonpos bridge.character Nat.prime_two
            (by simpa only [Nat.cast_ofNat] using h2) K2 (by linarith only [hx])
        have hm := Analysis.gamma_variable_square_mass_ge x
        have hl : 0 ≤ Analysis.gammaVariableSquareMass x * Real.log 4 :=
          mul_nonneg (by linarith only [hm]) (Real.log_nonneg (by norm_num only))
        linarith only [hc, hl, Analysis.gamma_variable_dyadic_nonneg hx]
      · have hc := Analysis.gamma_actual_dyadic_minus_one_cost_variable bridge.character h2 K2 hx
        have hm :=
          mul_le_mul_of_nonneg_right (Analysis.gamma_variable_square_mass_ge x)
            (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 4))
        dsimp only [Analysis.gammaVariableDyadicAllowance]
        linarith only [hc, hm]
    have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn.pos).ne'
    rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) hn0]
    linarith only [hs, ht]
  · have hs :=
      Analysis.gamma_actual_square_absorbed_variable hdecomp hn bridge.squarefreePart_pos
        bridge.squareFactor_odd.pos hf hd.1 hd.2 S hS bridge.character hχ K hx
    have ht :=
      Analysis.gamma_actual_dyadic_zero_cost_variable bridge.character
        (Analysis.gamma_even_modulus_character_two_zero bridge.character heven) K2 hx
    linarith only [hs, ht]

/-- Input: the Jacobi bridge, selected minus-one and zero factors, and x>=1.
Claim: the combined local cost fits the scale-dependent square/dyadic and signed
ramified budgets. Proof: add the existing finite ramified dual estimate.
Role: handle both nonpositive character values in one comparison. -/
theorem gamma_jacobi_joint_local_variable_scale {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (S R : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hR : R ⊆ n.primeFactors) (hSχ : ∀ p ∈ S, bridge.character p = -1)
    (hRχ : ∀ p ∈ R, bridge.character p = 0) (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {x : ℝ}
    (hx : 1 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 x +
        (∑ p ∈ R, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) ≤
      Analysis.gammaVariableSquareMass x * Real.log (4 * (n : ℝ)) +
        Analysis.gammaVariableDyadicAllowance x +
        Analysis.gammaRamifiedDualParameter x * Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedDualPrimeSet x,
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
              0 := by
  have hs := gamma_jacobi_square_dyadic_variable_scale bridge S hS hSχ K K2 hx
  have hr :=
    Analysis.gamma_actual_odd_ramified_signed_cost_le_finite_dual hn R hR bridge.character hRχ K
      (by linarith only [hx])
  linarith only [hs, hr]

/-- Input: an odd nonsquare Jacobi bridge, arbitrary power prefixes and x>=1.
Claim: every ambient local cost fits a factorization-independent budget.
Proof: classify the quadratic values and discard only the nonpositive one branch.
Role: remove unknown input factorization from the scalar witness criterion. -/
theorem gamma_jacobi_all_local_variable_scale {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (K : ℕ → Finset ℕ) {x : ℝ}
    (hx : 1 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ (4 * n).primeFactors,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) ≤
      Analysis.gammaVariableSquareMass x * Real.log (4 * (n : ℝ)) +
        Analysis.gammaVariableDyadicAllowance x +
        Analysis.gammaRamifiedDualParameter x * Real.log n +
        ∑ p ∈ Analysis.gammaRamifiedDualPrimeSet x,
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
              0 := by
  let S := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = -1)
  let R := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = 0)
  have hj :=
    gamma_jacobi_joint_local_variable_scale bridge S R (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) (fun p hp ↦ (Finset.mem_filter.mp hp).2)
      (fun p hp ↦ (Finset.mem_filter.mp hp).2) K (K 2) hx
  have hc :=
    gamma_actual_quadratic_local_sum_le_classified hn bridge.character bridge.character_quadratic K
      (by linarith only [hx])
  change
    (∑ p ∈ n.primeFactors, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) ≤
      (∑ p ∈ S, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) +
        ∑ p ∈ R, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x at hc
  rw [gamma_ambient_four_factor_sum_eq hn]
  linarith only [hj, hc]

/-- Input: the input n, an ambient pole modulus q, scale x and prefix endpoint b.
Definition: the variable local budget plus the signed Gamma, Euler and pole costs.
Output: an upper bound for ramp minus principal when the comparison premises hold.
Role: expose a factorization-independent criterion valid from scale two. -/
noncomputable def gammaVariableScaleArithmeticBudget (n q : ℕ) (x b : ℝ) : ℝ :=
  Analysis.gammaVariableSquareMass x * Real.log (4 * (n : ℝ)) +
        Analysis.gammaVariableDyadicAllowance x +
        Analysis.gammaRamifiedDualParameter x * Real.log n +
        (∑ p ∈ Analysis.gammaRamifiedDualPrimeSet x,
          Real.log p *
            max
              (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x)
              0) +
        (Analysis.gammaResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
      2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
    ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
    43 * x ^ (-9 / 16 : ℝ)

/-- Input: GRH, an odd nonsquare Jacobi bridge, admissible ambient modulus,
x>=2 and prefix, and absence of negative odd-prime witnesses.
Claim: ramp minus principal is at most the variable arithmetic budget.
Proof: combine the actual comparison, exact prefix identity and all-local bound.
Role: replace the old scale-4096 gate by an explicit scale-dependent budget. -/
theorem gamma_jacobi_no_negative_variable_scale_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * x)
    (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1) :
    2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re ≤
      gammaVariableScaleArithmeticBudget n q x b := by
  have hc :=
    gamma_jacobi_no_negative_actual_comparison bridge hGRH hq hmq
      (by linarith only [hx] : (2 : ℝ) ≤ x) (Finset.Ioc 0 ⌊b⌋₊) hno
  have he :=
    gamma_jacobi_prefix_add_ambient_ramp_eq_local_cost bridge hb
      (fun p hp hodd hpb ↦ hno p hp hodd (hpb.trans hbX)) x
  have hu :=
    gamma_jacobi_all_local_variable_scale bridge
      (AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b) (by linarith only [hx])
  have hC :=
    Analysis.gammaNegativeConductorTerm_nonpos
      (Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor)
      (by linarith only [hx] : (0 : ℝ) < x)
  dsimp only [gammaJacobiActualBudget] at hc
  dsimp only [gammaVariableScaleArithmeticBudget]
  linarith only [hc, he, hu, hC]

/-- Input: GRH, an odd nonsquare Jacobi bridge, ambient modulus and admissible
scale x>=2 and prefix. A strict arithmetic gap implies a negative odd-prime
Jacobi witness through 99x/40. Proof: contradict the no-negative comparison.
Role: connect the variable local costs to an actual witness; the gap remains to certify. -/
theorem exists_odd_prime_negative_of_variable_scale_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      gammaVariableScaleArithmeticBudget n q x b <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  by_contra hnot
  have hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ (99 / 40 : ℝ) * x → jacobiSym n p ≠ -1 :=
    fun p hp hodd hcut hj ↦ hnot ⟨p, hp, hodd, hcut, hj⟩
  exact
    (not_le_of_gt hgap)
      (gamma_jacobi_no_negative_variable_scale_comparison bridge hGRH hq hmq hx hb hbX hno)

/-- Input: x>=4096. Claim: the variable arithmetic budget saves at least
149/10000 against the previous fixed budget. Proof: the square mass agrees
and the dyadic allowance is smaller. Role: quantify the retained local gain. -/
theorem gamma_variable_scale_budget_gain {n q : ℕ} {x b : ℝ} (hx : 4096 ≤ x) :
    gammaVariableScaleArithmeticBudget n q x b + 149 / 10000 ≤
      gammaSmallScaleArithmeticBudget n q x b := by
  have he := Analysis.gamma_variable_square_mass_eq_of_large_scale hx
  have hd := Analysis.gamma_variable_dyadic_allowance_gain hx
  dsimp only [gammaVariableScaleArithmeticBudget, gammaSmallScaleArithmeticBudget]
  rw [he]
  linarith only [hd]

/-- Input: 0<n<=N and arbitrary real scale. Claim: the factorization-independent budget
is monotone in the input bound. Proof: both logarithmic coefficients are nonnegative.
Role: use one arithmetic gap uniformly for a full finite witness maximum. -/
theorem gamma_variable_scale_budget_mono {n N q : ℕ} (hn : 0 < n) (hnN : n ≤ N) {x b : ℝ} :
    gammaVariableScaleArithmeticBudget n q x b ≤ gammaVariableScaleArithmeticBudget N q x b := by
  have hl := Real.log_le_log (Nat.cast_pos.mpr hn : (0 : ℝ) < n) (Nat.cast_le.mpr hnN)
  have h4 : Real.log (4 * (n : ℝ)) ≤ Real.log (4 * (N : ℝ)) :=
    Real.log_le_log (mul_pos (by norm_num only) (Nat.cast_pos.mpr hn))
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hnN) (by norm_num only))
  have hm := Analysis.gamma_variable_square_mass_ge x
  have h4m :=
    mul_le_mul_of_nonneg_left h4 (show 0 ≤ Analysis.gammaVariableSquareMass x by linarith only [hm])
  have hdm := mul_le_mul_of_nonneg_left hl (Analysis.gamma_ramified_dual_parameter_nonneg x)
  dsimp only [gammaVariableScaleArithmeticBudget]
  linarith only [h4m, hdm]

/-- Input: an odd nonsquare n, log n<=L and x>=1. Claim: its actual
joint prefix budget is at most the variable scalar budget.
Proof: enlarge the logarithmic terms in the all-local comparison.
Role: feed scale-dependent local costs to the shared polynomial criterion. -/
theorem gamma_joint_prefix_le_variable_scale_budget {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    {L b x : ℝ} (hlog : Real.log n ≤ L) (hx : 1 ≤ x) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      Analysis.gammaVariableSquareMass x * (L + 7 / 5) + Analysis.gammaVariableDyadicAllowance x +
          gammaScaleSignedDualBudget L x -
        2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) := by
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns
  let K := AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b
  have hl := gamma_jacobi_all_local_variable_scale bridge K hx
  have he : bridge.character = (NumberTheory.complexQuadraticCharacter n hn).primitiveCharacter :=
    bridge.character_eq
  have hm := mul_le_mul_of_nonneg_left hlog (Analysis.gamma_ramified_dual_parameter_nonneg x)
  have hlog4 : Real.log (4 * (n : ℝ)) ≤ L + 7 / 5 := by
    rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_pos.mpr hn.pos).ne']
    linarith only [hlog, Analysis.log_four_le_seven_fifths]
  have hmass := Analysis.gamma_variable_square_mass_ge x
  have hlead :=
    mul_le_mul_of_nonneg_left hlog4
      (show 0 ≤ Analysis.gammaVariableSquareMass x by linarith only [hmass])
  rw [gammaJointPrefixLocalBudget, ← he]
  dsimp only [gammaScaleSignedDualBudget]
  linarith only [hl, hm, hlead]

/-- Input: odd nonsquare n, log n<=L, x>=1 and effective prefix credit
after the variable square, dyadic and ramified costs. Claim: the actual
joint budget has the standard kernel coefficient minus twice the credit.
Proof: absorb the excess variable mass in the prefix requirement.
Role: retain the existing paired polynomial without imposing scale 4096. -/
theorem gamma_joint_prefix_le_of_variable_scale_credit {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    {L b x C D : ℝ} (hlog : Real.log n ≤ L) (hx : 1 ≤ x)
    (hcredit :
      C +
          ((Analysis.gammaVariableSquareMass x - 11783423 / 25000000) * (L + 7 / 5) +
              Analysis.gammaVariableDyadicAllowance x +
              D) /
            2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : gammaScaleSignedDualBudget L x ≤ D) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) - 2 * C := by
  have hj := gamma_joint_prefix_le_variable_scale_budget (b := b) hn hns hlog hx
  linarith only [hj, hcredit, hdual]

/-- Input: GRH-independent quadratic arithmetic data, the displayed logarithmic
and scale conditions, variable effective credit and the shared polynomial.
Claim: the actual common-cost separation is positive.
Proof: combine the variable budget with the existing paired comparison.
Role: remove the fixed local scale gate from the polynomial witness interface. -/
theorem gamma_common_margin_pos_of_variable_scale_polynomial {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L b x C D : ℝ} (hlog : Real.log n ≤ L) (hx : 1 ≤ x)
    (hlogQ : Real.log Q ≤ L + 7 / 5)
    (hcredit :
      C +
          ((Analysis.gammaVariableSquareMass x - 11783423 / 25000000) * (L + 7 / 5) +
              Analysis.gammaVariableDyadicAllowance x +
              D) /
            2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : gammaScaleSignedDualBudget L x ≤ D)
    (hpoly : GammaPairedPolynomialCondition (L + 7 / 5) x C) :
    0 <
      gammaJointPrefixSeparationWithCommonCap Q (NumberTheory.complexQuadraticCharacter n hn) b x
        (541 / 50) (gammaSignedVariationPrincipalCap x) := by
  obtain ⟨R, u, hroot, hlogu, hcoef, hp⟩ := hpoly
  exact
    gamma_joint_prefix_common_margin_pos_of_polynomial (NumberTheory.complexQuadraticCharacter n hn)
      hx hroot hlogu hlogQ
      (gamma_joint_prefix_le_of_variable_scale_credit hn hns hlog hx hcredit hdual) hcoef hp

/-- Input: effective credit C<=123901/10000. Claim: the current paired
polynomial cannot certify L=45 and x=800. Proof: bound the root and logarithm
below using exact arithmetic and the existing log-two and log-three bounds.
Role: distinguish a local scale-gate removal from a feasible low-entrance bound. -/
theorem gamma_paired_polynomial_obstruction_45_800 {C : ℝ} (hC : C ≤ (123901 / 10000 : ℝ)) :
    ¬GammaPairedPolynomialCondition (232 / 5) 800 C := by
  rintro ⟨R, u, hroot, hlog, hcoef, hp⟩
  have hs : (28 : ℝ) ≤ Real.sqrt 800 := by
    have hsq := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 800)
    nlinarith only [hsq, Real.sqrt_nonneg (800 : ℝ)]
  have hlog0 : (15 / 2 : ℝ) ≤ Real.log ((101 / 40 : ℝ) * 800) := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 1944)
        (by norm_num only : (1944 : ℝ) ≤ (101 / 40 : ℝ) * 800)
    have he : (1944 : ℝ) = 2 ^ 3 * 3 ^ 5 := by norm_num only
    rw [he, Real.log_mul (by norm_num only : (2 : ℝ) ^ 3 ≠ 0) (by norm_num only : (3 : ℝ) ^ 5 ≠ 0),
      Real.log_pow, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h, Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hR : (28 : ℝ) ≤ R := hs.trans hroot
  have hu := hlog0.trans hlog
  have hcm := mul_le_mul_of_nonneg_left hR hcoef
  nlinarith only [hp, hcm, hu, hC]

/-- Input: RH and the variable-cost credit and dual conditions at L=45,x=800.
Claim: the current paired polynomial cannot hold for any prefix.
Proof: nonnegative local costs bound the effective credit by the full Euler mass,
which is too small for the preceding obstruction.
Role: show that a larger prefix alone cannot solve this low-scale comparison. -/
theorem gamma_no_variable_scale_polynomial_45_800 (hRH : RiemannHypothesis) {b C D : ℝ}
    (hcredit :
      C +
          ((Analysis.gammaVariableSquareMass 800 - 11783423 / 25000000) * (45 + 7 / 5) +
              Analysis.gammaVariableDyadicAllowance 800 +
              D) /
            2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : gammaScaleSignedDualBudget 45 800 ≤ D) :
    ¬GammaPairedPolynomialCondition (45 + 7 / 5) 800 C := by
  have hd0 : 0 ≤ gammaScaleSignedDualBudget 45 800 := by
    apply add_nonneg
    · exact mul_nonneg (Analysis.gamma_ramified_dual_parameter_nonneg _) (by norm_num only)
    · exact Finset.sum_nonneg (fun p _ ↦ mul_nonneg (Real.log_natCast_nonneg p) (le_max_right _ _))
  have hextra :
    0 ≤
      (Analysis.gammaVariableSquareMass 800 - 11783423 / 25000000) * (45 + 7 / 5) +
        Analysis.gammaVariableDyadicAllowance 800 +
        D :=
    add_nonneg
      (add_nonneg
        (mul_nonneg (sub_nonneg.mpr (Analysis.gamma_variable_square_mass_ge _)) (by norm_num only))
        (Analysis.gamma_variable_dyadic_nonneg (by norm_num only)))
      (hd0.trans hdual)
  have hP :=
    Summable.sum_le_tsum (Finset.Ioc 0 ⌊b⌋₊)
      (fun k _ ↦ Analysis.gammaResolventMangoldtWeight_nonneg k)
      Analysis.summable_gammaResolventMangoldtWeight
  have he := gamma_principal_euler_lt_precise hRH
  have hC : C ≤ (123901 / 10000 : ℝ) := by linarith only [hcredit, hextra, hP, he]
  rw [show (45 + 7 / 5 : ℝ) = 232 / 5 by norm_num only]
  exact gamma_paired_polynomial_obstruction_45_800 hC

end PseudoPrime.LLS
