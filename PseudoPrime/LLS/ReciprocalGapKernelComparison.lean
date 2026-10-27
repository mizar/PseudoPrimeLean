/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapKernelArithmetic

/-! # Uniform remainder bounds and witness separation for adjustable reciprocal kernels -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For each positive fixed gap there is a positive remainder constant uniform in all
primitive nonprincipal GRH characters of level at least eight and scales at least one.
The norm is at most C(1+log(q)/sqrt(x)). Apply the general kernel remainder estimate.
This proves uniformity in the arithmetic variables; the dependence on h is not explicit. -/
theorem exists_norm_reciprocalGapCompletedRemainder_le {h : ℝ} (hh : 0 < h) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q],
          8 ≤ q →
            ∀ {χ : DirichletCharacter ℂ q},
              AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ {x : ℝ},
                  1 ≤ x →
                    ‖reciprocalGapCompletedRemainder h hh χ x‖ ≤
                      C * (1 + Real.log q / Real.sqrt x) := by
  obtain ⟨C, hC, hb⟩ :=
    MellinKernel.exists_norm_summand_add_oscillatingZeroSum_le (reciprocalGapMellinKernel h hh)
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hGRH hp hne hinv x hx
  have hs := hb hq hGRH hp hne hinv hx
  rw [reciprocalGapMellinKernel_tsum_eq_finite hh χ (zero_lt_one.trans_le hx)] at hs
  change
    ‖reciprocalGapCharacterSum h χ x +
          (∑' ρ : ℂ, (reciprocalGapMellinKernel h hh).oscillatingZeroTerm χ x ρ)‖ ≤
      _ at hs
  rw [reciprocalGapCharacterSum_eq_zeroSum_add_remainder hh ((by norm_num only : 2 ≤ 8).trans hq)
      hGRH hp hne hinv hx] at hs
  simpa only [neg_add_cancel_comm] using hs

/-- For a fixed positive gap, bound the finite character sum uniformly by the positive-prefix
zero budget and C(1+log(q)/sqrt(x)), at levels at least eight under primitive GRH data.
Use the exact arithmetic comparison and the norm estimate for the remainder.
This removes contour integrals as extra hypotheses while retaining a kernel-dependent constant. -/
theorem exists_reciprocalGapCharacterSum_re_le_positive_prefix {h : ℝ} (hh : 0 < h) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q],
          8 ≤ q →
            ∀ {χ : DirichletCharacter ℂ q},
              AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ {c x : ℝ},
                  (1 / 2 : ℝ) < c →
                    c ^ 2 ≤ 1 / 4 + h / 2 →
                    1 ≤ x →
                    ∀ B : Finset ℕ,
                      (reciprocalGapCharacterSum h χ x).re ≤
                        (1 / c) *
                            (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
                                (∑' n : ℕ,
                                  ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
                              ∑ n ∈ B,
                                (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n /
                                  (n : ℝ) ^ (1 / 2 + c)) +
                          C * (1 + Real.log q / Real.sqrt x) := by
  obtain ⟨C, hC, hR⟩ := exists_norm_reciprocalGapCompletedRemainder_le hh
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hGRH hp hne hinv c x hc hbound hx B
  have hu :=
    reciprocalGapCharacterSum_re_le_positive_prefix hh ((by norm_num only : 2 ≤ 8).trans hq) hGRH hp
      hne hinv hc hbound hx B
  have hr :=
    (Complex.re_le_norm (reciprocalGapCompletedRemainder h hh χ x)).trans
      (hR hq hGRH hp hne hinv hx)
  exact hu.trans (add_le_add_right hr _)

/-- If a character takes value one at every prime up to a nonnegative scale, its finite gap sum
equals the level-one principal sum. Zero Mangoldt terms vanish and prime powers inherit
value one from their prime. This is the witness-nonexistence side of the comparison. -/
theorem reciprocalGapCharacterSum_eq_principal_of_prime_one {h x : ℝ} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hx : 0 ≤ x) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1) :
    reciprocalGapCharacterSum h χ x =
      reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x := by
  unfold reciprocalGapCharacterSum
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp only [hΛ, zero_div, Complex.ofReal_zero, zero_mul]
  · obtain ⟨p, r, hp, hr, rfl⟩ :=
      (isPrimePow_nat_iff (n := n)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hpx : (p : ℝ) ≤ x :=
      (show (p : ℝ) ≤ (p ^ r : ℕ) by exact_mod_cast Nat.le_pow hr).trans
        ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx))
    simp only [Nat.cast_pow, map_pow, hsmall p hp hpx, one_pow,
      MulChar.one_apply (isUnit_of_subsingleton ((p : ℕ) : ZMod 1))]

/-- For a positive gap and primitive nonprincipal GRH data, a strict separation between the
principal finite sum and the prefix budget plus exact remainder yields a non-one prime
witness at most the scale. Contradict equality with the principal sum under nonexistence.
This criterion still requires a quantitative separation; it asserts no numerical cutoff. -/
theorem exists_prime_not_one_of_reciprocalGap_separation {h c : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ}
    (hx : 1 ≤ x) (B : Finset ℕ)
    (hgap :
      (1 / c) *
            (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
                (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
              ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) +
          (reciprocalGapCompletedRemainder h hh χ x).re <
        (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  classical
  by_contra hn
  have hs : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1 := by
    intro p hp hpx
    by_contra hχ
    exact hn ⟨p, hp, hpx, hχ⟩
  have hu := reciprocalGapCharacterSum_re_le_positive_prefix hh hq hGRH hp hne hinv hc hbound hx B
  rw [reciprocalGapCharacterSum_eq_principal_of_prime_one χ (zero_le_one.trans hx) hs] at hu
  exact (not_lt_of_ge hu) hgap

/-- For a positive gap and scale, the first-pole residue has norm equal to the completed
endpoint logarithmic derivative divided by h sqrt(x), for nonprincipal characters.
Evaluate the regularization at the pole and simplify the inverse square-root power.
This records the exact inverse-gap cost needed for finite-scale optimization. -/
theorem reciprocalGap_poleResidue_norm {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
          (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)‖ =
      ‖logDeriv χ.completedLFunction 0‖ / (h * Real.sqrt x) := by
  simp only [MellinKernel.weightedResidue, ite_true]
  rw [AnalyticNumberTheory.DirichletLFunction.logDeriv_shifted_completed hne]
  have he : (-1 / 2 : ℂ) + 1 / 2 = 0 := by ring
  rw [he, norm_mul, norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  norm_num only [Complex.div_ofNat_re, Complex.neg_re, Complex.one_re]
  change
    ‖logDeriv χ.completedLFunction 0‖ *
        (‖1 / ((-(1 / 2) : ℂ) + ((1 / 2 + h : ℝ) : ℂ))‖ * x ^ (-(1 / 2) : ℝ)) =
      _
  have hs : (-(1 / 2) : ℂ) + ((1 / 2 + h : ℝ) : ℂ) = (h : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [hs, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hpow : x ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt x := by
    rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hpow]
  ring

/-- Under primitive nonprincipal GRH data at level at least eight and positive scale,
the first-pole residue is bounded by ((7/6) log(q)+4)/(h sqrt(x)).
Combine the exact residue norm with the completed endpoint estimate.
This makes the pole part of the gap-dependent remainder explicit. -/
theorem reciprocalGap_poleResidue_norm_le {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q] (hq : 8 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    ‖MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
          (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)‖ ≤
      ((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) := by
  rw [reciprocalGap_poleResidue_norm hh hne hx]
  exact
    div_le_div_of_nonneg_right (norm_completedLogDeriv_zero_le_affine_log hq hp hne hGRH)
      (mul_nonneg hh.le (Real.sqrt_nonneg x))

end PseudoPrime.LLS.PaperStatements
