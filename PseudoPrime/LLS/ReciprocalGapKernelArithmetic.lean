/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapKernel
public import PseudoPrime.LLS.MellinKernelExplicitFormula
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TwoPoleZeroBounds

/-! # Finite arithmetic and contour identities for adjustable reciprocal kernels -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive gap and input, the admissible kernel transform is the compact power weight.
Use inverse Mellin inversion on the central line. This identifies the arithmetic profile. -/
theorem reciprocalGapMellinKernel_transform {h u : ℝ} (hh : 0 < h) (hu : 0 < u) :
    (reciprocalGapMellinKernel h hh).transform u =
      AnalyticNumberTheory.General.twoPoleMellinWeight (1 / 2) h u := by
  exact inverseMellin_reciprocalGap hh (by norm_num only) hu

/-- For positive scale and gap, express the kernel summand using a clamped real weight.
Cancel square roots after the transform identity. This gives its arithmetic normalization. -/
theorem reciprocalGapMellinKernel_summand {h : ℝ} (hh : 0 < h) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (reciprocalGapMellinKernel h hh).summand χ x n =
      (ArithmeticFunction.vonMangoldt n / Real.sqrt x : ℝ) * χ n *
        (max (1 - ((n : ℝ) / x) ^ h) 0 / h : ℝ) := by
  by_cases hn : n = 0
  · simp only [MellinKernel.summand, hn, ite_eq_left, ArithmeticFunction.map_zero, zero_div,
      Complex.ofReal_zero, zero_mul]
  · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [MellinKernel.summand, ite_eq_right hn,
      reciprocalGapMellinKernel_transform hh (div_pos hn0 hx),
      AnalyticNumberTheory.General.twoPoleMellinWeight_eq_clamped hh (div_pos hn0 hx), ←
      Real.sqrt_eq_rpow, Real.sqrt_div hn0.le x]
    have hs : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hn0).ne'
    have hxS : (Real.sqrt x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
    simp only [Complex.ofReal_div, Complex.ofReal_mul]
    field_simp [hs, hxS, Complex.ofReal_ne_zero.mpr hh.ne']

/-- Outside the positive integers at most the scale, the kernel summand vanishes.
The clamped power weight is zero above one. This supplies finite support. -/
theorem reciprocalGapMellinKernel_summand_support {h : ℝ} (hh : 0 < h) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ∉ Finset.Ioc 0 ⌊x⌋₊) :
    (reciprocalGapMellinKernel h hh).summand χ x n = 0 := by
  by_cases hn0 : n = 0
  · simp only [MellinKernel.summand, hn0, ite_eq_left]
  · have hnot : ¬n ≤ ⌊x⌋₊ := fun h ↦ hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, h⟩)
    have hnx : x < (n : ℝ) := Nat.lt_of_floor_lt (lt_of_not_ge hnot)
    have hu : 1 ≤ (n : ℝ) / x := (le_div_iff₀ hx).mpr (by simpa only [one_mul] using hnx.le)
    rw [reciprocalGapMellinKernel_summand hh χ hx,
      max_eq_right (sub_nonpos.mpr (Real.one_le_rpow hu hh.le)), zero_div, Complex.ofReal_zero,
      mul_zero]

/-- For positive scale and gap, the kernel series equals the finite power-weighted sum.
Use finite support and remove the clamp on the support. This connects contour and arithmetic. -/
theorem reciprocalGapMellinKernel_tsum_eq_finite {h : ℝ} (hh : 0 < h) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, (reciprocalGapMellinKernel h hh).summand χ x n) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt x : ℝ) * χ n *
          ((1 - ((n : ℝ) / x) ^ h) / h : ℝ) := by
  rw [tsum_eq_sum (fun n hn ↦ reciprocalGapMellinKernel_summand_support hh χ hx hn)]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnx : (n : ℝ) ≤ x := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx.le)
  rw [reciprocalGapMellinKernel_summand hh χ hx,
    max_eq_left
      (sub_nonneg.mpr (Real.rpow_le_one (div_nonneg hn0 hx.le) ((div_le_one hx).mpr hnx) hh.le))]

/-- The finite character sum with gap h and scale x has weight
Lambda(n)/sqrt(x) times (1-(n/x)^h)/h, for positive n at most floor(x).
For positive h and x this is the arithmetic side of the adjustable reciprocal kernel. -/
noncomputable def reciprocalGapCharacterSum {q : ℕ} (h : ℝ) (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
    (ArithmeticFunction.vonMangoldt n / Real.sqrt x : ℝ) * χ n * ((1 - ((n : ℝ) / x) ^ h) / h : ℝ)

/-- The completed contour remainder retains the first-pole residue and both vertical integrals.
For h positive the lines are displaced by half the admissible kernel margin.
This exact remainder isolates the quantitative estimate still needed for witness bounds. -/
noncomputable def reciprocalGapCompletedRemainder {q : ℕ} [NeZero q] (h : ℝ) (hh : 0 < h)
    (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  let K := reciprocalGapMellinKernel h hh
  let δ := K.delta
  let W := fun s : ℂ ↦ K.function s * (x : ℂ) ^ s
  let F := fun s : ℂ ↦ -logDeriv χ.completedLFunction (s + 1 / 2) * W s
  MellinKernel.weightedResidue K (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) +
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F (((-1 / 2 - δ / 2 : ℝ) : ℂ) + Complex.I * t)) +
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv χ.gammaFactor ((((1 / 2 + δ / 2 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          W (((1 / 2 + δ / 2 : ℝ) : ℂ) + Complex.I * t))

/-- Under GRH for a primitive nonprincipal character, the finite sum is minus the zero sum
plus the completed contour remainder, at scales at least one.
Apply the admissible kernel contour formula on its interior lines and collect terms. -/
theorem reciprocalGapCharacterSum_eq_zeroSum_add_remainder {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    reciprocalGapCharacterSum h χ x =
      -(∑' ρ : ℂ, (reciprocalGapMellinKernel h hh).oscillatingZeroTerm χ x ρ) +
        reciprocalGapCompletedRemainder h hh χ x := by
  let K := reciprocalGapMellinKernel h hh
  have hd := K.delta_pos
  have hu : K.delta ≤ (1 / 8 : ℝ) := min_le_right _ _
  have hf :=
    MellinKernel.tsum_summand_eq_completed_residue_formula K hq hGRH hp hne hinv (a :=
      -1 / 2 - K.delta / 2) (b := 1 / 2 + K.delta / 2) (by linarith only [hd])
      (by linarith only [hd]) (by linarith only [hd]) (by linarith only [hu])
      (by linarith only [hu]) hx (by linarith only [hd]) (by linarith only [hd])
  unfold reciprocalGapCharacterSum
  rw [← reciprocalGapMellinKernel_tsum_eq_finite hh χ (zero_lt_one.trans_le hx)]
  dsimp only [reciprocalGapCompletedRemainder]
  rw [hf]
  ring

/-- Identify each admissible-kernel zero term with the two-pole resolvent term.
Unfold both definitions, preserving multiplicity and the unit phase.
This connects the exact contour identity to the quantitative zero bounds. -/
theorem reciprocalGapMellinKernel_zeroTerm_eq {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) (ρ : ℂ) :
    (reciprocalGapMellinKernel h hh).oscillatingZeroTerm χ x ρ =
      AnalyticNumberTheory.DirichletLFunction.twoPoleCompletedZeroTerm χ (1 / 2) (1 / 2 + h)
        (fun z ↦ (x : ℂ) ^ (Complex.I * z.im)) ρ := by
  unfold MellinKernel.oscillatingZeroTerm MellinKernel.kernelZeroTerm
    AnalyticNumberTheory.DirichletLFunction.twoPoleCompletedZeroTerm
  simp only [Complex.ofReal_intCast]
  rfl

/-- Under GRH and the positive-gap width bound, bound the finite sum by a zero budget
with a nonnegative Euler prefix subtracted, plus the exact remainder.
Use the oscillating zero-sum estimate and the real-part bound by the norm.
The remainder is retained explicitly; no quantitative witness cutoff is asserted. -/
theorem reciprocalGapCharacterSum_re_le_positive_prefix {h c : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ}
    (hx : 1 ≤ x) (B : Finset ℕ) :
    (reciprocalGapCharacterSum h χ x).re ≤
      (1 / c) *
          (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
              (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
            ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) +
        (reciprocalGapCompletedRemainder h hh χ x).re := by
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.twoPole_oscillating_zeroSum_bound hq (hGRH q χ hp) hp
      hne hinv hc (show c ^ 2 ≤ (1 / 2 : ℝ) * (1 / 2 + h) by nlinarith only [hbound])
      (zero_lt_one.trans_le hx) B
  have he :
    (∑' ρ : ℂ, (reciprocalGapMellinKernel h hh).oscillatingZeroTerm χ x ρ) =
      ∑' ρ : ℂ,
        AnalyticNumberTheory.DirichletLFunction.twoPoleCompletedZeroTerm χ (1 / 2) (1 / 2 + h)
          (fun z ↦ (x : ℂ) ^ (Complex.I * z.im)) ρ :=
    tsum_congr (fun ρ ↦ reciprocalGapMellinKernel_zeroTerm_eq hh χ x ρ)
  rw [← he] at hz
  have hr :=
    Complex.re_le_norm (-(∑' ρ : ℂ, (reciprocalGapMellinKernel h hh).oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hr
  rw [reciprocalGapCharacterSum_eq_zeroSum_add_remainder hh hq hGRH hp hne hinv hx, Complex.add_re,
    Complex.neg_re]
  linarith only [hz.2, hr]

end PseudoPrime.LLS.PaperStatements
