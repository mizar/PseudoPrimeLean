/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Conductor
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainXi656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaMass656
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterPrimeTriviality

import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ConductorTail

/-! # Shifted contour comparison with the K197 coefficients -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The forward contour remainder mixed with the K197 coefficients. -/
noncomputable def gaussianShiftedForward197 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (r : ℝ) : ℝ :=
  let x := fun i : Fin 6 ↦ r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ))
  ∑ i,
    (gaussianCoeff197 i : ℝ) *
      ((contourRemainder656 χ (x i)).re -
        (∑' n, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (x i) n).re)

/-- The positive half-point coefficient in the shifted K197 comparison. -/
@[expose]
noncomputable def gaussianHalfCoeff197 : ℝ :=
  (3 * (11 / 10) ^ 5 / (8 / 5) ^ 6) *
    ∑ i, (gaussianCoeff197 i : ℝ) * Real.exp (-(quarterShift663 i : ℝ) / 2)

private theorem gaussian_half_pole_sum_197 {r : ℝ} (hr : 0 < r) :
    3 *
        (∑ i,
          (gaussianCoeff197 i : ℝ) *
            (quarterKernel656.function (1 / 2) *
                ((r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ)).re) =
      gaussianHalfCoeff197 * r := by
  have hs (i : Fin 6) : 21 / 8 + (quarterShift663 i : ℝ) = quarterFreq663 i := by
    simp only [quarterShift663, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
    ring
  have hh (i : Fin 6) := quarter_shifted_half_pole_656 hr (quarterShift663 i : ℝ)
  dsimp only at hh
  simp only [hs] at hh
  unfold gaussianHalfCoeff197
  simp only [hh, mul_assoc, mul_left_comm (gaussianCoeff197 _ : ℝ), ← Finset.mul_sum]
  ring

/-- The signed zeta zero contribution at the six shifted scales. -/
noncomputable def gaussianXiMix197 (r : ℝ) : ℝ :=
  ∑ i,
    (gaussianCoeff197 i : ℝ) *
      (∑' ρ,
          quarterKernel656.zetaOscillatingZeroTerm (r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ)))
            ρ).re

/-- Under RH, expand the six shifted remainders at radius `r` and total
log conductor `4 * r / scale`. Only the conductor term is divided by the scale. -/
theorem gaussian_scaled_shift_mix_197 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r scale : ℝ}
    (hr : 328 ≤ r) (hL : Real.log p + Real.log q + Real.log s = 4 * r / scale) :
    (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r =
      gaussianTheta197 r / scale + gaussianNegPole197 / r + 3 * gaussianXiMix197 r +
        ∑ i,
          (gaussianCoeff197 i : ℝ) *
            quarterAuxReflection656 (fun n ↦ 3 - ((a n).re + (b n).re + (c n).re)) r
              (quarterShift663 i : ℝ) := by
  let x := fun i ↦ r ^ 2 * Real.exp (-((quarterFreq663 i : ℝ)))
  let P := fun (t : ℝ) (i : Fin 6) ↦ (quarterKernel656.function (t : ℂ) * (x i : ℂ) ^ (t : ℂ)).re
  let Z := fun i ↦ (∑' ρ, quarterKernel656.zetaOscillatingZeroTerm (x i) ρ).re
  let T := fun i ↦
    quarterAuxReflection656 (fun n ↦ 3 - ((a n).re + (b n).re + (c n).re)) r (quarterShift663 i : ℝ)
  let A := fun i ↦ (4 * r * (quarterKernel656.transform (x i)⁻¹).re) / scale - 3 * P (-1 / 2) i
  let S := fun (i : Fin 6) ↦
    (∑' n, quarterKernel656.summand (1 : DirichletCharacter ℂ 1) (x i) n).re
  have hr₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr
  have hx (i : Fin 6) : 1 ≤ x i := quarter_aux_scale_ge_one_663 hr i
  have hs (i : Fin 6) :
    (contourRemainder656 a (x i)).re - S i + P (1 / 2) i +
        ((contourRemainder656 b (x i)).re - S i + P (1 / 2) i) +
        ((contourRemainder656 c (x i)).re - S i + P (1 / 2) i) =
      A i + 3 * Z i + T i := by
    have he : 21 / 8 + (quarterShift663 i : ℝ) = (quarterFreq663 i : ℝ) := by
      simp only [quarterShift663, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
      ring
    have h :=
      quarter_shifted_forward_diff_656 ha hb hc hRH hr₀ (h := (quarterShift663 i : ℝ))
        (by simpa only [he, x] using hx i)
    simp only [he] at h
    have hp :
      (quarterKernel656.transform (x i)⁻¹).re =
        Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (x i)⁻¹ := by
      rw [quarterKernel656,
        LLS.PaperStatements.rationalPole_transform _ _ _ _
          (inv_pos.mpr (zero_lt_one.trans_le (hx i))),
        Complex.ofReal_re]
    simp only [hL, Complex.sub_re] at h
    dsimp only [A, P, Z, S, T, x] at h hp ⊢
    rw [hp]
    linear_combination h
  have hA :
    (∑ i, (gaussianCoeff197 i : ℝ) * A i) =
      gaussianTheta197 r / scale + gaussianNegPole197 / r := by
    have ht := gaussian_theta_sum_197 hr
    have hp := gaussian_neg_pole_sum_197 hr₀
    dsimp only [A, P, x]
    simp only [mul_sub, Finset.sum_sub_distrib, ← mul_div_assoc,
      mul_left_comm (gaussianCoeff197 _ : ℝ) 3, ← Finset.mul_sum]
    rw [← Finset.sum_div, ht]
    linarith only [hp]
  rw [← hA]
  rw [← gaussian_half_pole_sum_197 hr₀]
  unfold gaussianShiftedForward197 gaussianXiMix197
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hp : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [← hp]
  change
    (gaussianCoeff197 i : ℝ) * ((contourRemainder656 a (x i)).re - S i) +
        (gaussianCoeff197 i : ℝ) * ((contourRemainder656 b (x i)).re - S i) +
        (gaussianCoeff197 i : ℝ) * ((contourRemainder656 c (x i)).re - S i) +
        3 * ((gaussianCoeff197 i : ℝ) * P (1 / 2) i) =
      (gaussianCoeff197 i : ℝ) * A i + 3 * ((gaussianCoeff197 i : ℝ) * Z i) +
        (gaussianCoeff197 i : ℝ) * T i
  linear_combination (gaussianCoeff197 i : ℝ) * hs i

/-- The six shifted zero terms for three characters cost at most
nine millionths, by the common principal-kernel zero bound. -/
theorem gaussian_xi_cap_197 (hRH : RiemannHypothesis) {r : ℝ} (hr : 328 ≤ r) :
    |3 * gaussianXiMix197 r| ≤ 0.000009 := by
  let f := fun i : Fin 6 ↦
    (∑' ρ,
        quarterKernel656.zetaOscillatingZeroTerm (r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ))) ρ).re
  have hc : ∀ i : Fin 6, |gaussianCoeff197 i| ≤ 1 := by decide +kernel
  have hf (i : Fin 6) := quarter_main_zero_abs_656 hRH (quarter_aux_scale_ge_one_663 hr i)
  have h :=
    sum_six_error (fun i ↦ (gaussianCoeff197 i : ℝ) * f i) (fun _ ↦ 0)
      (fun i ↦ by
        simp only [sub_zero, abs_mul]
        have hi : |(gaussianCoeff197 i : ℝ)| ≤ 1 := by exact_mod_cast hc i
        have he := mul_le_mul hi (hf i) (abs_nonneg _) (by norm_num only : (0 : ℝ) ≤ 1)
        norm_num only at he ⊢
        exact he)
  simp only [Finset.sum_const_zero, sub_zero] at h
  rw [abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3)]
  unfold gaussianXiMix197
  linarith only [h]

/-- Prime agreement and the trace bound give the early K197 shifted
contour lower bound, with the positive half-point term left on the left. -/
private theorem shift_forward_of_refl {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r s B E : ℝ}
    (hr : 328 ≤ r) (hL : Real.log p + Real.log q + Real.log k = 4 * r / s)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (hcost : B ≤ gaussianTheta197 r / s + gaussianNegPole197 / r)
    (hrefl :
      ∀ α : ℕ → ℝ,
        (∀ n, 0 ≤ α n ∧ α n ≤ 4) →
          (∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) →
          -E ≤
            ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ)) :
    B - E - 0.000009 ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
  let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
  have hd (n : ℕ) : 0 ≤ d n ∧ d n ≤ 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  have hprefix (n : ℕ) (hn : (n : ℝ) ≤ r ^ 2) (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0) :
    d n = 0 := by
    simp only [d,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero a hpa hn hΛ,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero b hpb hn hΛ,
      AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero c hpc hn hΛ,
      Complex.one_re]
    norm_num only
  have he := gaussian_scaled_shift_mix_197 ha hb hc hRH hr hL
  have hbnd := hrefl d hd hprefix
  have hz := (abs_le.mp (gaussian_xi_cap_197 hRH hr)).1
  dsimp only [d] at hbnd
  linarith only [he, hbnd, hz, hcost]

/-- Prime agreement and the trace bound give the early K197 shifted
contour lower bound, with the positive half-point term left on the left. -/
private theorem shift_forward_lower {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r s B : ℝ}
    (hr : r ∈ Set.Icc 332.15 336.9) (hL : Real.log p + Real.log q + Real.log k = 4 * r / s)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (hcost : B ≤ gaussianTheta197 r / s + gaussianNegPole197 / r) :
    B - 0.000059 ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
  have hr' : (328 : ℝ) ≤ r := (by norm_num only : (328 : ℝ) ≤ 332.15).trans hr.1
  have h :=
    shift_forward_of_refl ha hb hc hRH hr' hL ht hpa hpb hpc hcost
      (gaussian_joint_early_lower_197 hRH hr)
  linarith only [h]

/-- Prime agreement and the trace bound give the early K197 shifted
contour lower bound, with the positive half-point term left on the left. -/
theorem gaussian_shift_forward_early_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r s : ℝ}
    (hr : r ∈ Set.Icc 332.15 334) (hs : 1 ≤ s)
    (hL : Real.log p + Real.log q + Real.log k = 4 * r / s)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    (-2.908059 : ℝ) ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
  have h :=
    shift_forward_lower ha hb hc hRH ⟨hr.1, hr.2.trans (by norm_num only)⟩ hL ht hpa hpb hpc
      (gaussian_shift_early_lower_197 hr hs)
  linarith only [h]

/-- Prime agreement and the trace bound give the early K197 shifted
contour lower bound, with the positive half-point term left on the left. -/
theorem gaussian_shift_forward_first_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 332.249 332.5)
    (hL : Real.log p + Real.log q + Real.log k = 4 * r / (500186760939 / 500000000000))
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    (-2.895059 : ℝ) ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
  have hwide : r ∈ Set.Icc 332.15 336.9 :=
    ⟨(by norm_num only : (332.15 : ℝ) ≤ 332.249).trans hr.1, hr.2.trans (by norm_num only)⟩
  have h :=
    shift_forward_lower ha hb hc hRH hwide hL ht hpa hpb hpc (gaussian_shift_first_lower_197 hr)
  linarith only [h]

/-- Prime agreement and the trace bound give the K197 shifted
contour lower bound, with the positive half-point term left on the left. -/
theorem gaussian_shift_forward_from3338_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r s : ℝ}
    (hr : r ∈ Set.Icc 333.8 336.9) (hs : 1 ≤ s)
    (hL : Real.log p + Real.log q + Real.log k = 4 * r / s)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    (-2.887559 : ℝ) ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
  have h :=
    shift_forward_lower ha hb hc hRH ⟨(by norm_num only : (332.15 : ℝ) ≤ 333.8).trans hr.1, hr.2⟩ hL
      ht hpa hpb hpc (gaussian_shift_from3338_197 ⟨hr.1, hr.2.trans (by norm_num only)⟩ hs)
  linarith only [h]

private theorem mid_shift_cost {r s : ℝ} (hr : r ∈ Set.Icc 336.8 342.9) (hs : 1 ≤ s) :
    (-2.8736 : ℝ) ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 336.8).trans_le hr.1
  have hθ := gaussian_theta_from3368_197 hr.1
  have hθ' : (-2.934 : ℝ) ≤ gaussianTheta197 r / s :=
    (le_div_iff₀ (zero_lt_one.trans_le hs)).mpr
      ((by linarith only [hs] : (-2.934 : ℝ) * s ≤ -2.934).trans hθ)
  have hn : (0.0604 : ℝ) ≤ gaussianNegPole197 / r :=
    (le_div_iff₀ hp).mpr (by linarith only [hr.2, gaussian_neg_pole_lower_197])
  linarith only [hθ', hn]

/-- On radii through 342.9, combine the K197 conductor, half-point, and
reflected estimates into one lower bound for the three shifted contours. -/
theorem gaussian_shift_forward_mid_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r s : ℝ}
    (hr : r ∈ Set.Icc 336.8 342.9) (hs : 1 ≤ s)
    (hL : Real.log p + Real.log q + Real.log k = 4 * r / s)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    (-2.873664 : ℝ) ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
  have hr' : (328 : ℝ) ≤ r := (by norm_num only : (328 : ℝ) ≤ 336.8).trans hr.1
  have hrw : r ∈ Set.Icc 332.15 342.9 :=
    ⟨(by norm_num only : (332.15 : ℝ) ≤ 336.8).trans hr.1, hr.2⟩
  have h :=
    shift_forward_of_refl ha hb hc hRH hr' hL ht hpa hpb hpc (mid_shift_cost hr hs)
      (gaussian_joint_mid_lower_197 hRH hrw)
  linarith only [h]

private theorem shift_cost_from338 {r s : ℝ} (hr : r ∈ Set.Icc 338 342.9) (hs : 1.001 ≤ s) :
    (-2.8657 : ℝ) ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 338).trans_le hr.1
  have hθ := gaussian_theta_from338_197 hr.1
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.001).trans_le hs
  have hθ' : (-2.9261 : ℝ) ≤ gaussianTheta197 r / s :=
    (le_div_iff₀ hs₀).mpr ((by linarith only [hs] : (-2.9261 : ℝ) * s ≤ -2.929).trans hθ)
  have hn : (0.0604 : ℝ) ≤ gaussianNegPole197 / r :=
    (le_div_iff₀ hp).mpr (by linarith only [hr.2, gaussian_neg_pole_lower_197])
  linarith only [hθ', hn]

/-- From radius 338 through 342.9, a scale of at least 1.001 gives a
lower bound for the three shifted contours including their half-point term. -/
theorem gaussian_shift_forward_from338_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r s : ℝ}
    (hr : r ∈ Set.Icc 338 342.9) (hs : 1.001 ≤ s)
    (hL : Real.log p + Real.log q + Real.log k = 4 * r / s)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    (-2.865764 : ℝ) ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
  have hr' : (328 : ℝ) ≤ r := (by norm_num only : (328 : ℝ) ≤ 338).trans hr.1
  have hrw : r ∈ Set.Icc 332.15 342.9 := ⟨(by norm_num only : (332.15 : ℝ) ≤ 338).trans hr.1, hr.2⟩
  have h :=
    shift_forward_of_refl ha hb hc hRH hr' hL ht hpa hpb hpc (shift_cost_from338 hr hs)
      (gaussian_joint_mid_lower_197 hRH hrw)
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
