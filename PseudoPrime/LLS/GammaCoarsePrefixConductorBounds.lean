/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaCertifiedArithmeticBudget
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaRamifiedPrefixCap

/-! # Actual Jacobi conductor comparison using the finite prefix cap -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For the actual primitive Jacobi character of an odd nonsquare input,
the square and dyadic costs spend the conductor gap once. Ramified Euler
costs share one integer prefix cap, and each input prime spends at most
log((99/40)x)/sqrt x on its ramp. The finite prime count replaces the local dual
in the coarse tail route while all minus-one losses are still accounted for. -/
theorem gamma_jacobi_all_local_cost_le_prefix_cap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {b : ℝ} (hb : 0 ≤ b)
    (hlarge : 10 ^ 100 ≤ n) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ n.primeFactors,
          Analysis.gammaActualPrimeLocalCost bridge.character p
            (AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b p)
            (Analysis.gammaRefinedScale (Real.log n))) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2
          (AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b 2)
          (Analysis.gammaRefinedScale (Real.log n)) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) +
        (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) +
        (n.primeFactors.card : ℝ) *
          (Real.log ((99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n)) /
            Real.sqrt (Analysis.gammaRefinedScale (Real.log n))) := by
  let K := AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b
  let S := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = -1)
  let R := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = 0)
  have hL := Analysis.gamma_refined_log_range_of_decimal hlarge
  have hx : 1 ≤ Analysis.gammaRefinedScale (Real.log n) :=
    le_trans (by norm_num only : (1 : ℝ) ≤ 20000)
      (Analysis.gamma_refined_scale_ge_twenty_thousand hL)
  have hs :=
    gamma_jacobi_refined_input_square_dyadic_cost_le bridge S (Finset.filter_subset _ _)
      (fun p hp ↦ (Finset.mem_filter.mp hp).2) K (K 2) hlarge
  have hr :=
    AnalyticNumberTheory.DirichletLFunction.gamma_selected_ramified_local_cost_le_prefix_cap
      bridge.character hb hx R
      (fun p hp ↦
        ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩)
  have hc :=
    gamma_actual_quadratic_local_sum_le_classified hn bridge.character bridge.character_quadratic K
      (zero_lt_one.trans_le hx)
  change
    (∑ p ∈ n.primeFactors,
        Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
          (Analysis.gammaRefinedScale (Real.log n))) ≤
      (∑ p ∈ S,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale (Real.log n))) +
        ∑ p ∈ R,
          Analysis.gammaActualPrimeLocalCost bridge.character p (K p)
            (Analysis.gammaRefinedScale (Real.log n)) at hc
  have hcard : (R.card : ℝ) ≤ (n.primeFactors.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  have hcut : (1 : ℝ) ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n) := by
    nlinarith only [hx]
  have hbnd :=
    mul_le_mul_of_nonneg_right hcard
      (div_nonneg (Real.log_nonneg hcut)
        (Real.sqrt_nonneg (Analysis.gammaRefinedScale (Real.log n))))
  linarith only [hs, hr, hc, hbnd]

/-- With ambient unit primes equal to one up to the retained cutoff,
the original integer character deficit and ambient ramp obey the coarse
prefix-cap conductor budget. The exact prime-power reindexing and dyadic
split preserve the actual character values after primitivization. -/
theorem gamma_jacobi_integer_prefix_local_budget_cap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {b : ℝ} (hb : 1 ≤ b)
    (hone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p (4 * n) → bridge.character p = 1)
    (hlarge : 10 ^ 100 ≤ n) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        ((∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
            (1 - (bridge.character m).re) * Analysis.gammaResolventMangoldtWeight m) +
          ∑ p ∈ (4 * n).primeFactors,
            Real.log p *
              ((∑' k : ℕ,
                  Analysis.exponentialRampLocalCorrection (bridge.character p)
                    ((p : ℝ) ^ (k + 1) / Analysis.gammaRefinedScale (Real.log n)) (k + 1)) /
                Real.sqrt (Analysis.gammaRefinedScale (Real.log n)))) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) +
        (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) +
        (n.primeFactors.card : ℝ) *
          (Real.log ((99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n)) /
            Real.sqrt (Analysis.gammaRefinedScale (Real.log n))) := by
  let K := AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b
  have he :=
    AnalyticNumberTheory.DirichletLFunction.gamma_character_prefix_add_ambient_ramp_eq_local_cost
      bridge.character (Nat.mul_pos (by norm_num only) hn.pos) hb hone
      (Analysis.gammaRefinedScale (Real.log n))
  rw [he, gamma_ambient_four_factor_sum_eq hn]
  simpa only [add_assoc] using
    gamma_jacobi_all_local_cost_le_prefix_cap bridge (zero_le_one.trans hb) hlarge

/-- Under individual RH and no negative Jacobi prime witness through b,
the primitive zero mass and actual ambient ramp have a coarse upper bound
with one retained prefix gain. The even Gamma correction is certified,
and square-part, ramified, and dyadic costs are all included. This is
the analytic contract used before the remaining scalar tail certificates. -/
theorem gamma_jacobi_no_negative_zeroMass_add_ramp_le_prefix_cap {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis bridge.character) {b : ℝ}
    (hb : 1 ≤ b) (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ b → jacobiSym n p ≠ -1)
    (hlarge : 10 ^ 100 ≤ n) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor bridge.character.completedLFunction Set.univ ρ : ℝ) *
            Analysis.gammaResolventMajorant ρ.im) +
        (∑ p ∈ (4 * n).primeFactors,
          Real.log p *
            ((∑' k : ℕ,
                Analysis.exponentialRampLocalCorrection (bridge.character p)
                  ((p : ℝ) ^ (k + 1) / Analysis.gammaRefinedScale (Real.log n)) (k + 1)) /
              Real.sqrt (Analysis.gammaRefinedScale (Real.log n)))) ≤
      (-159 / 100 : ℝ) + (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
          (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) +
        (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) +
        (3 / 4 : ℝ) +
        (n.primeFactors.card : ℝ) *
          (Real.log ((99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n)) /
            Real.sqrt (Analysis.gammaRefinedScale (Real.log n))) := by
  have hf : 0 < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (gamma_jacobi_modulus_eq_discriminant bridge).symm ▸ bridge.discriminant_pos
  let : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor := ⟨hf.ne'⟩
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_zeroMass_le_signed_prefix
      (le_trans (by norm_num only : (2 : ℕ) ≤ 3) (gamma_jacobi_modulus_ge_three bridge)) hRH
      bridge.character_primitive bridge.character_ne_one
      (by
        rw [bridge.character_quadratic.inv]; exact bridge.character_ne_one)
      (Finset.Ioc 0 ⌊b⌋₊)
  have hl :=
    gamma_jacobi_integer_prefix_local_budget_cap bridge hb
      (gamma_jacobi_no_negative_prefix_prime_one bridge hno) hlarge
  have hgf : bridge.character.gammaFactor = Complex.Gammaℝ :=
    funext (fun z ↦ bridge.character_even.gammaFactor_def z)
  rw [hgf] at hz
  have hΓ := AnalyticNumberTheory.Gamma.gammaResolvent_even_correction_le
  linarith only [hz, hl, hΓ]

/-- The coarse scalar budget at log scale L, prefix b and prime-count bound w.
Its single prefix gain comes from the shared ramified cap; the prime-count
ramp allowance replaces the precise local dual. The Gamma correction is
already certified. Use alongside the sharper dual budget, retaining both routes. -/
noncomputable def gammaCoarseArithmeticBudget (L b w : ℝ) : ℝ :=
  let x := Analysis.gammaRefinedScale L
  (-159 / 100 : ℝ) + (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
      (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) +
    (11783423 / 25000000 : ℝ) * (L + Real.log 4) +
    (3 / 4 : ℝ) +
    w * (Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x) +
    ((7 / 6 : ℝ) * (L + Real.log 4) + 4) / Real.sqrt x +
    x ^ (-9 / 16 : ℝ) * ((3 / 2) * (L + Real.log 4 + 28) + 1)

/-- Under GRH, absence of negative Jacobi witnesses through the refined
cutoff forces the actual principal/ramp comparison against the coarse
prefix-cap scalar budget. The primitive, ambient, square and dyadic losses
are discharged; only scalar certification and prime-count bounds remain. -/
theorem gamma_jacobi_no_negative_coarse_arithmetic_comparison {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlarge : 10 ^ 100 ≤ n) {b : ℝ}
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n))
    (hno :
      ∀ p : ℕ,
        p.Prime →
          Odd p →
          (p : ℝ) ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n) → jacobiSym n p ≠ -1) :
    let x := Analysis.gammaRefinedScale (Real.log n)
    2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re ≤
      gammaCoarseArithmeticBudget (Real.log n) b n.primeFactors.card := by
  dsimp only [gammaCoarseArithmeticBudget]
  have hx : 2 ≤ Analysis.gammaRefinedScale (Real.log n) :=
    le_trans (by norm_num only : (2 : ℝ) ≤ 20000)
      (Analysis.gamma_refined_scale_ge_twenty_thousand
        (Analysis.gamma_refined_log_range_of_decimal hlarge))
  have hx0 : 0 < Analysis.gammaRefinedScale (Real.log n) :=
    lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  have hm := gamma_jacobi_modulus_ge_three bridge
  have hmq :=
    Nat.le_of_dvd (mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos)
      (DirichletCharacter.conductor_dvd_level (NumberTheory.complexQuadraticCharacter n hn))
  have hq : 20000 ≤ 4 * n :=
    le_trans (by norm_num only : (20000 : ℕ) ≤ 4 * 10 ^ 100) (Nat.mul_le_mul_left 4 hlarge)
  have hinv : bridge.character⁻¹ ≠ 1 := by
    rw [bridge.character_quadratic.inv]
    exact bridge.character_ne_one
  have hc :=
    PaperStatements.gamma_primitive_sum_re_le_resolvent_sharp hq hm hmq hGRH
      bridge.character_primitive bridge.character_ne_one hinv hx
  have hz :=
    gamma_jacobi_no_negative_zeroMass_add_ramp_le_prefix_cap bridge
      (hGRH _ bridge.character bridge.character_primitive) hb
      (fun p hp hodd hpb ↦ hno p hp hodd (hpb.trans hbX)) hlarge
  have ha := gamma_jacobi_no_negative_ramp_comparison bridge hx0 hno
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hc
  have hf0 : (0 : ℝ) < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num only : (0 : ℕ) < 3) hm)
  have hfq : ((NumberTheory.complexQuadraticCharacter n hn).conductor : ℝ) ≤ 4 * n := by
    exact_mod_cast hmq
  have hl := Real.log_le_log hf0 hfq
  have hleft :=
    mul_le_mul_of_nonneg_left
      (add_le_add_right
        (mul_le_mul_of_nonneg_left (add_le_add_right hl 28) (by norm_num only : (0 : ℝ) ≤ 3 / 2)) 1)
      (Real.rpow_pos_of_pos hx0 (-9 / 16 : ℝ)).le
  have hlog : Real.log (4 * (n : ℝ)) = Real.log n + Real.log 4 := by
    rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hn.pos.ne'), add_comm]
  rw [hlog] at hc hz hleft
  linarith only [hc, hz, ha, hleft]

/-- At a refined scale at least one, increasing the allowed distinct-prime
count increases the coarse budget. The prime-count multiplier has a
nonnegative logarithm and square root denominator. This permits a proved
analytic prime-count bound to replace the unknown input factorization. -/
theorem gammaCoarseArithmeticBudget_mono_count {L b w v : ℝ} (hx : 1 ≤ Analysis.gammaRefinedScale L)
    (hw : w ≤ v) : gammaCoarseArithmeticBudget L b w ≤ gammaCoarseArithmeticBudget L b v := by
  have hcut : (1 : ℝ) ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale L := by nlinarith only [hx]
  have hm :=
    mul_le_mul_of_nonneg_right hw
      (div_nonneg (Real.log_nonneg hcut) (Real.sqrt_nonneg (Analysis.gammaRefinedScale L)))
  dsimp only [gammaCoarseArithmeticBudget]
  linarith only [hm]

/-- A strict gap over the coarse prefix-cap budget with an upper bound w
for the number of distinct input prime factors forces an odd-prime negative
Jacobi witness under GRH. Both the conductor losses and fixed Gamma
correction are proved; the gap is the remaining numerical tail obligation. -/
theorem exists_odd_prime_negative_of_coarse_arithmetic_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlarge : 10 ^ 100 ≤ n) {b w : ℝ}
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n))
    (hw : (n.primeFactors.card : ℝ) ≤ w)
    (hgap :
      gammaCoarseArithmeticBudget (Real.log n) b w <
        2 *
            (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum
                (Analysis.gammaRefinedScale (Real.log n)) /
              Real.sqrt (Analysis.gammaRefinedScale (Real.log n))) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                (Analysis.gammaRefinedScale (Real.log n)) k).re) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n) ∧ jacobiSym n p = -1 := by
  by_contra hnot
  have hno :
    ∀ p : ℕ,
      p.Prime →
        Odd p →
        (p : ℝ) ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n) → jacobiSym n p ≠ -1 :=
    fun p hp hodd hcut hj ↦ hnot ⟨p, hp, hodd, hcut, hj⟩
  have ha := gamma_jacobi_no_negative_coarse_arithmetic_comparison bridge hGRH hlarge hb hbX hno
  have hx : 1 ≤ Analysis.gammaRefinedScale (Real.log n) :=
    le_trans (by norm_num only : (1 : ℝ) ≤ 20000)
      (Analysis.gamma_refined_scale_ge_twenty_thousand
        (Analysis.gamma_refined_log_range_of_decimal hlarge))
  exact (not_le_of_gt hgap) (ha.trans (gammaCoarseArithmeticBudget_mono_count hx hw))

end PseudoPrime.LLS
