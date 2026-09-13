/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
import PseudoPrime.LLS.Theorem11S1

/-!
# The analytic and finite-sum interfaces for LLS Lemma 2.1

This file separates the Riemann explicit-formula estimate from the finite character-sum
decomposition used in Section 3.1.  The analytic proposition is the precise lower-bound direction
consumed later; it does not expose the paper's auxiliary `θ` parameter.
-/

namespace PseudoPrime.LLS

namespace LLSLemma21Internal

/-- Under the Part 1 no-small-prime hypothesis, for `0 < n ≤ ⌊x⌋₊` and a positive cutoff `x`
within the search radius, the character summand is its real weight on coprime inputs and zero
on the remaining inputs. -/
theorem characterWeightedTerm_re_eq_ite {q n : ℕ} [NeZero q] (x : ℝ) (χ : DirichletCharacter ℂ q)
    (hx : 0 < x) (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊) (hsmall : llsTheorem11S1NoSmallPrime χ)
    (hlimit : x ≤ (llsTheorem11S1RadiusRoot q) ^ 2) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedTerm x χ n).re =
      if Nat.Coprime n q then
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n
      else 0 := by
  by_cases hcop : Nat.Coprime n q
  · rw [ite_eq_left hcop]
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · rw [AnalyticNumberTheory.Arithmetic.characterLogWeightedTerm,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm, hΛ, zero_mul]
      change ((0 : ℂ) * χ (n : ZMod q)).re = 0
      rw [zero_mul, Complex.zero_re]
    · obtain ⟨p, k, hp, hk, rfl⟩ :=
        (isPrimePow_nat_iff (n := n)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
      have hpdiv : p ∣ p ^ k := dvd_pow_self p hk.ne'
      have hpcop : Nat.Coprime p q := hcop.of_dvd_left hpdiv
      have hpbound : (p : ℝ) ≤ x := by
        have hpowFloor := (Finset.mem_Ioc.mp hn).2
        have hpPow : p ≤ p ^ k := Nat.le_pow hk
        exact
          (show (p : ℝ) ≤ (p ^ k : ℕ) by exact_mod_cast hpPow).trans
            ((Nat.le_floor_iff hx.le).mp hpowFloor)
      have hpvalue : χ p = 1 := hsmall p hp (hp.coprime_iff_not_dvd.mp hpcop) (hpbound.trans hlimit)
      rw [AnalyticNumberTheory.Arithmetic.characterLogWeightedTerm]
      simp only [Nat.cast_pow, map_pow, hpvalue, one_pow, mul_one, Complex.ofReal_re]
  · rw [ite_eq_right hcop]
    have hχzero : χ n = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ (n : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hcop)
    rw [AnalyticNumberTheory.Arithmetic.characterLogWeightedTerm, hχzero, mul_zero,
      Complex.zero_re]

end LLSLemma21Internal

/--
The lower-bound direction of LLS Lemma 2.1 needed in Part 1.

The input is `x > 1`.  The omitted positive trivial-zero series is discarded, and the RH zero
contribution is bounded below by `-2 |B| (sqrt x + 1)`.
-/
def LLSRiemannWeightedLowerBound : Prop :=
  ∀ x : ℝ,
    1 < x →
      x - Real.log (2 * Real.pi) * Real.log x - 1 -
          2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt x + 1) ≤
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x

/--
The finite decomposition used before applying Lemma 2.1 and the weighted estimate.

For a Part 1 counterexample, every contributing prime coprime to `q` has character value `1`.
Thus the real part of the character sum is the Riemann sum minus the terms not coprime to `q`.
-/
def LLSPart1CharacterWeightedDecomposition : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q →
      χ ≠ 1 →
      llsTheorem11S1NoSmallPrime χ →
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
            ((llsTheorem11S1RadiusRoot q) ^ 2) χ).re =
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum
            ((llsTheorem11S1RadiusRoot q) ^ 2) -
          AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum
            ((llsTheorem11S1RadiusRoot q) ^ 2) q

/-- The Part 1 finite character decomposition follows from prime-power support. -/
theorem llsPart1CharacterWeightedDecomposition : LLSPart1CharacterWeightedDecomposition := by
  intro q _ χ hq _ hsmall
  have hx : 0 < (llsTheorem11S1RadiusRoot q) ^ 2 := by
    have hlog : (8 : ℝ) < Real.log q := by
      apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
      rw [show (8 : ℝ) = (8 : ℕ) * 1 by norm_num only, Real.exp_nat_mul]
      exact
        (show Real.exp 1 ^ 8 < (3000 : ℝ) by
              calc
                Real.exp 1 ^ 8 < (2.7182818286 : ℝ) ^ 8 := by
                  gcongr
                  exact Real.exp_one_lt_d9
                _ < 3000 := by norm_num only).trans_le
          (by exact_mod_cast hq)
    rw [llsTheorem11S1RadiusRoot]
    nlinarith only [llsCorrectionTerm_nonneg q, hlog,
      sq_nonneg (Real.log (q : ℝ) + llsCorrectionTerm q)]
  rw [AnalyticNumberTheory.Arithmetic.characterLogWeightedSum,
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum,
    AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum]
  simp only [Complex.re_sum]
  trans
    ∑ n ∈ Finset.Ioc 0 ⌊(llsTheorem11S1RadiusRoot q) ^ 2⌋₊,
      if Nat.Coprime n q then
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm
          ((llsTheorem11S1RadiusRoot q) ^ 2) n
      else 0
  · apply Finset.sum_congr rfl
    intro n hn
    exact LLSLemma21Internal.characterWeightedTerm_re_eq_ite _ χ hx hn hsmall le_rfl
  have hpartition :=
    Finset.sum_filter_add_sum_filter_not (s := Finset.Ioc 0 ⌊(llsTheorem11S1RadiusRoot q) ^ 2⌋₊)
      (f :=
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm
        ((llsTheorem11S1RadiusRoot q) ^ 2))
      (p := fun n ↦ Nat.Coprime n q)
  rw [← Finset.sum_filter]
  linarith only [hpartition]

/-- Lemmas 2.1 and 3.1 give the unsimplified Part 1 lower bound. -/
theorem llsPart1WeightedRawLower (h21 : LLSRiemannWeightedLowerBound)
    (hdecompose : LLSPart1CharacterWeightedDecomposition) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) (hχ : χ ≠ 1)
    (hsmall : llsTheorem11S1NoSmallPrime χ) :
    (llsTheorem11S1RadiusRoot q) ^ 2 -
        Real.log (2 * Real.pi) * Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) -
        1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass *
          (llsTheorem11S1RadiusRoot q + 1) -
        (1 / 2 : ℝ) * q.primeFactors.card * (Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) ^ 2 ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
          ((llsTheorem11S1RadiusRoot q) ^ 2) χ).re := by
  have hy : 1 < llsTheorem11S1RadiusRoot q := by
    exact
      (show (1 : ℝ) < 8 by norm_num only).trans
        (by
          exact
            (Real.lt_log_iff_exp_lt (by positivity)).mpr
                ((show Real.exp 8 < (3000 : ℝ)
                      by
                      rw [show (8 : ℝ) = (8 : ℕ) * 1 by norm_num only, Real.exp_nat_mul]
                      calc
                        Real.exp 1 ^ 8 < (2.7182818286 : ℝ) ^ 8 := by
                          gcongr
                          exact Real.exp_one_lt_d9
                        _ < 3000 := by norm_num only).trans_le
                  (by exact_mod_cast hq)) |>.trans_le
              (le_add_of_nonneg_right (llsCorrectionTerm_nonneg q)))
  have hx : 1 < (llsTheorem11S1RadiusRoot q) ^ 2 := by nlinarith
  have hriemann := h21 ((llsTheorem11S1RadiusRoot q) ^ 2) hx
  have hcommon :=
    AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum_le (NeZero.ne q)
      (zero_lt_one.trans hx)
  have hsqrt : Real.sqrt ((llsTheorem11S1RadiusRoot q) ^ 2) = llsTheorem11S1RadiusRoot q := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (zero_lt_one.trans hy)]
  rw [hsqrt] at hriemann
  rw [hdecompose q χ hq hχ hsmall]
  linarith only [hriemann, hcommon]

/-- Lemma 2.1 alone now supplies the raw Part 1 lower bound. -/
theorem llsPart1WeightedRawLower_of_riemann (h21 : LLSRiemannWeightedLowerBound) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) (hχ : χ ≠ 1)
    (hsmall : llsTheorem11S1NoSmallPrime χ) :
    (llsTheorem11S1RadiusRoot q) ^ 2 -
        Real.log (2 * Real.pi) * Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) -
        1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass *
          (llsTheorem11S1RadiusRoot q + 1) -
        (1 / 2 : ℝ) * q.primeFactors.card * (Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) ^ 2 ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
          ((llsTheorem11S1RadiusRoot q) ^ 2) χ).re :=
  llsPart1WeightedRawLower h21 llsPart1CharacterWeightedDecomposition χ hq hχ hsmall

end PseudoPrime.LLS
