/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineTail663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterForward656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxiliary656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineCore663

/-! # Forward comparison for the six section 137 frequencies -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed sum of shifted contour remainders minus the shifted
level-one forward sums, at the six section 137 frequencies. -/
noncomputable def quarterShiftedForward663 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (r : ℝ) :
    ℝ :=
  let x := fun i : Fin 6 ↦ r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ))
  ∑ i,
    (quarterCoeff663 i : ℝ) *
      ((contourRemainder656 χ (x i)).re -
        (∑' n, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (x i) n).re)

/-- Under GRH and prime agreement, the finite Gram inequality bounds the
main forward sum with the signed shifted remainders of section 137. -/
theorem quarter_single_forward_663 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {r : ℝ} (hr : 328 ≤ r) (hpass : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ r ^ 2 → χ p = 1) :
    (∑' n, quarterKernel656.summand χ (r ^ 2) n).re + quarterShiftedForward663 χ r ≤
      quarterCosineContour656 χ 0 + (contourRemainder656 χ (r ^ 2)).re +
        quarterAuxMix663 (fun t ↦ quarterCosineContour656 χ |(t : ℝ)|) := by
  have hX : (1 : ℝ) ≤ r ^ 2 :=
    (by norm_num only : (1 : ℝ) ≤ 328 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr 2)
  have hx := zero_lt_one.trans_le hX
  let Z := quarterKernel656.oscillatingZeroTerm χ (r ^ 2)
  have hZ :=
    LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm quarterKernel656 hq hG hp hn
      (inv_ne_one.mpr hn) hx
  have h :=
    finite_frequency_weighted_le (fun ρ ↦ ‖Z ρ‖) (fun ρ ↦ (Z ρ).arg) Complex.im
      (fun ρ ↦ norm_nonneg (Z ρ)) hZ.norm (fun i ↦ (quarterFreq663 i : ℝ))
      (fun i ↦ (quarterCoeff663 i : ℝ))
  dsimp only at h
  have hf : ∀ i, (21 / 8 : ℚ) ≤ quarterFreq663 i := by decide +kernel
  have hfR (i : Fin 6) : (21 / 8 : ℝ) ≤ (quarterFreq663 i : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr (hf i)
  have hB (i : Fin 6) :=
    quarter_cosine_contour_656 hq hG hp hn hx ((by norm_num only : (0 : ℝ) ≤ 21 / 8).trans (hfR i))
  have hm := quarter_cosine_contour_656 hq hG hp hn hx (le_refl (0 : ℝ))
  simp only [zero_mul, Real.cos_zero, mul_one] at hm
  have ht (i : Fin 6) :
    (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos ((Z ρ).arg - (quarterFreq663 i : ℝ) * ρ.im)) =
      (contourRemainder656 χ (r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ)))).re -
        (∑' n,
            quarterKernel656.summand (1 : DirichletCharacter ℂ 1)
              (r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ))) n).re := by
    dsimp only [Z]
    rw [shifted_phase_eq hq hG hp hn (inv_ne_one.mpr hn) hx,
      zero_re_eq_contour hq hG hp hn (quarter_aux_scale_ge_one_663 hr i),
      quarter_shifted_forward_656 χ hx (hfR i) hpass]
  have hz : (∑' ρ : ℂ, ‖Z ρ‖ * Real.cos (Z ρ).arg) = (∑' ρ : ℂ, Z ρ).re := by
    rw [Complex.re_tsum hZ]
    exact tsum_congr (fun ρ ↦ Complex.norm_mul_cos_arg (Z ρ))
  rw [hz] at h
  simp only [ht, Z, hB, quarter_cosine_abs_contour_656 hq hG hp hn hx, hm,
    zero_re_eq_contour hq hG hp hn hX, mul_add, Finset.sum_add_distrib] at h
  unfold quarterShiftedForward663 quarterAuxMix663
  simp only [Rat.cast_sub, abs_of_nonneg ((by norm_num only : (0 : ℝ) ≤ 21 / 8).trans (hfR _))]
  linarith only [h]

/-- Summing the three Gram inequalities leaves one signed Euler tail and
the certified six-frequency residue gain. -/
theorem quarter_scaled_forward_663 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ} (hr : 328 ≤ r)
    (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    (∑' n, quarterKernel656.summand a (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand b (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand c (r ^ 2) n).re +
        (quarterShiftedForward663 a r + quarterShiftedForward663 b r +
          quarterShiftedForward663 c r) +
        3.64052193 ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
          (contourRemainder656 c (r ^ 2)).re) +
        quarterAuxMix663 quarterConductorProfile663 * t +
        ∑' n : { n : ℕ // ⌊r ^ 2⌋₊ < n },
          (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ)) *
            (quarterProfile663 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val)) := by
  have h := quarter_scaled_cosine_cap_663 ha hb hc hG.riemann hr hL hpa hpb hpc
  have hmix (f g k : ℚ → ℝ) :
    quarterAuxMix663 (fun t ↦ f t + g t + k t) =
      quarterAuxMix663 f + quarterAuxMix663 g + quarterAuxMix663 k := by
    simpa only [one_mul] using mix_linear f g k 1 1 1
  rw [hmix] at h
  linarith only [h, quarter_single_forward_663 hp hG ha.1 ha.2.1 hr hpa,
    quarter_single_forward_663 hq hG hb.1 hb.2.1 hr hpb,
    quarter_single_forward_663 hk hG hc.1 hc.2.1 hr hpc]

/-- Specialize the independent conductor radius to the quarter-square radius. -/
theorem quarter_three_forward_663 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : 328 ≤ r)
    (hL : Real.log p + Real.log q + Real.log k = 4 * r)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    (∑' n, quarterKernel656.summand a (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand b (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand c (r ^ 2) n).re +
        (quarterShiftedForward663 a r + quarterShiftedForward663 b r +
          quarterShiftedForward663 c r) +
        3.64052193 ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
          (contourRemainder656 c (r ^ 2)).re) +
        quarterAuxMix663 quarterConductorProfile663 * r +
        ∑' n : { n : ℕ // ⌊r ^ 2⌋₊ < n },
          (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ)) *
            (quarterProfile663 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val)) := by
  exact quarter_scaled_forward_663 ha hb hc hp hq hk hG hr hL hpa hpb hpc

end PseudoPrime.PrimeTestBounds.MillerRabin
