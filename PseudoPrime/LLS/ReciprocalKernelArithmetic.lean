/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalKernel
public import PseudoPrime.LLS.MellinKernelExplicitFormula

/-! # Finite reciprocal arithmetic sums and their completed explicit formula -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: a character, a positive scale and any natural index.
Claim: the kernel term equals Lambda(n) chi(n) max(1-n/x,0)/sqrt(x).
Proof: the compact inverse profile cancels the summand square root.
Role: give the exact arithmetic weight without numerical Mellin evaluation. -/
theorem reciprocalMellinKernel_summand {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (n : ℕ) :
    reciprocalMellinKernel.summand χ x n =
      (ArithmeticFunction.vonMangoldt n / Real.sqrt x : ℝ) * χ n *
        (max (1 - (n : ℝ) / x) 0 : ℝ) := by
  by_cases hn : n = 0
  · simp only [MellinKernel.summand, hn, ite_eq_left, ArithmeticFunction.map_zero, zero_div,
      Complex.ofReal_zero, zero_mul]
  · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [MellinKernel.summand, ite_eq_right hn, reciprocalMellinKernel_transform (div_pos hn0 hx),
      Complex.ofReal_mul, Real.sqrt_div hn0.le x, Complex.ofReal_div]
    have hs : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hn0).ne'
    have hxS : (Real.sqrt x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
    simp only [Complex.ofReal_div]
    field_simp [hs, hxS]

/-- Input: a character, positive scale and an index outside the positive floor interval.
Claim: the reciprocal summand vanishes.
Proof: index zero is excluded by definition; larger indices have zero profile.
Role: replace the infinite arithmetic series by an exact finite sum. -/
theorem reciprocalMellinKernel_summand_support {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) {n : ℕ} (hn : n ∉ Finset.Ioc 0 ⌊x⌋₊) :
    reciprocalMellinKernel.summand χ x n = 0 := by
  by_cases hn0 : n = 0
  · simp only [MellinKernel.summand, hn0, ite_eq_left]
  · have hnot : ¬n ≤ ⌊x⌋₊ := fun h ↦ hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, h⟩)
    have hnx : x < (n : ℝ) := (Nat.lt_of_floor_lt (lt_of_not_ge hnot))
    have hu : 1 ≤ (n : ℝ) / x := (le_div_iff₀ hx).mpr (by simpa only [one_mul] using hnx.le)
    rw [reciprocalMellinKernel_summand χ hx, max_eq_right (sub_nonpos.mpr hu), Complex.ofReal_zero,
      mul_zero]

/-- Input: a character and a positive scale.
Claim: the whole reciprocal series is its finite linearly smoothed Mangoldt sum through floor(x).
Proof: finite support and the exact summand formula.
Role: connect finite arithmetic evaluation to the general contour machinery. -/
theorem reciprocalMellinKernel_tsum_eq_finite {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    (∑' n : ℕ, reciprocalMellinKernel.summand χ x n) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt x : ℝ) * χ n * (1 - (n : ℝ) / x : ℝ) := by
  rw [tsum_eq_sum (fun n hn ↦ reciprocalMellinKernel_summand_support χ hx hn)]
  apply Finset.sum_congr rfl
  intro n hn
  have hnx : (n : ℝ) ≤ x := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx.le)
  rw [reciprocalMellinKernel_summand χ hx, max_eq_left (sub_nonneg.mpr ((div_le_one hx).mpr hnx))]

/-- Input: GRH, primitive nonprincipal character with nonprincipal inverse, q >= 2 and x >= 1.
Claim: the finite weighted sum equals the pole residue minus zeros plus the two contour integrals.
Proof: instantiate the completed kernel formula at lines -9/16 and 9/16.
Role: remove all kernel admissibility and inversion premises from the rational explicit formula. -/
theorem reciprocalMellinKernel_finite_sum_eq_completed_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    let W := fun s : ℂ ↦ reciprocalMellinFunction s * (x : ℂ) ^ s
    let F := fun s : ℂ ↦ -logDeriv χ.completedLFunction (s + 1 / 2) * W s
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt x : ℝ) * χ n * (1 - (n : ℝ) / x : ℝ)) =
      MellinKernel.weightedResidue reciprocalMellinKernel
            (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
          (∑' ρ : ℂ, reciprocalMellinKernel.oscillatingZeroTerm χ x ρ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
              W (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  rw [← reciprocalMellinKernel_tsum_eq_finite χ (zero_lt_one.trans_le hx)]
  exact
    MellinKernel.tsum_summand_eq_completed_residue_formula reciprocalMellinKernel hq hGRH hp hne
      hinv (by norm_num only) (by norm_num only [reciprocalMellinKernel])
      (by norm_num only [reciprocalMellinKernel]) (by norm_num only) (by norm_num only) hx
      (by norm_num only) (by norm_num only)

end PseudoPrime.LLS.PaperStatements
