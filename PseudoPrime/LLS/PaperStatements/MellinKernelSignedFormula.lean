/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.MellinKernelExplicitFormula
import Mathlib.Tactic.Ring

/-! # Exact explicit formula for signed finite sums of Mellin kernels -/

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- The arithmetic summands of a finite combination of admissible kernels
are summable and their sum is the corresponding combination of series.
The coefficients may have either sign. -/
public theorem tsum_kernel_finset_sum {ι : Type*} (s : Finset ι) (K : ι → MellinKernel) (c : ι → ℂ)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, ∑ i ∈ s, c i * (K i).summand χ x n) =
      ∑ i ∈ s, c i * ∑' n : ℕ, (K i).summand χ x n := by
  rw [Summable.tsum_finsetSum (fun i _ ↦ ((K i).summable_summand χ hx).mul_left (c i))]
  apply Finset.sum_congr rfl
  intro i _
  exact ((K i).summable_summand χ hx).tsum_mul_left (c i)

/-- Regroup the absolutely convergent oscillating zero series by zero.
This preserves cancellation between the signed kernel components. -/
public theorem tsum_signed_oscillating_zero {ι : Type*} (s : Finset ι) (K : ι → MellinKernel)
    (c : ι → ℂ) {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    (∑' ρ : ℂ, ∑ i ∈ s, c i * (K i).oscillatingZeroTerm χ x ρ) =
      ∑ i ∈ s, c i * ∑' ρ : ℂ, (K i).oscillatingZeroTerm χ x ρ := by
  have hs (i : ι) := (K i).summable_oscillatingZeroTerm hq hGRH hp hne hinv hx
  rw [Summable.tsum_finsetSum (fun i _ ↦ (hs i).mul_left (c i))]
  apply Finset.sum_congr rfl
  intro i _
  exact (hs i).tsum_mul_left (c i)

/-- For primitive nonprincipal characters under GRH, apply the exact
residue formula to a signed finite sum on two common admissible lines.
The combined arithmetic series is evaluated with the original kernels. -/
public theorem tsum_signed_kernel_residue {ι : Type*} (s : Finset ι) (K : ι → MellinKernel)
    (c : ι → ℂ) {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b x : ℝ} (hab : a < b)
    (ha : ∀ i ∈ s, -1 / 2 - (K i).delta < a) (hb : ∀ i ∈ s, b ≤ 1 / 2 + (K i).delta)
    (ha' : -3 / 2 ≤ a) (hb' : b ≤ 3 / 2) (hx : 1 ≤ x) (haleft : a < -1 / 2) (hbright : 1 / 2 < b) :
    let W := fun i (z : ℂ) ↦ (K i).function z * (x : ℂ) ^ z
    let F := fun i (z : ℂ) ↦ -logDeriv χ.completedLFunction (z + 1 / 2) * W i z
    (∑' n : ℕ, ∑ i ∈ s, c i * (K i).summand χ x n) =
      ∑ i ∈ s,
        c i *
          (weightedResidue (K i) (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
              (∑' ρ : ℂ, (K i).oscillatingZeroTerm χ x ρ) +
            ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F i ((a : ℂ) + Complex.I * t)) +
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              (∫ t : ℝ,
                logDeriv (DirichletCharacter.gammaFactor χ) (((b : ℂ) + Complex.I * t) + 1 / 2) *
                  W i ((b : ℂ) + Complex.I * t))) := by
  intro W F
  rw [tsum_kernel_finset_sum s K c χ (zero_lt_one.trans_le hx)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tsum_summand_eq_completed_residue_formula (K i) hq hGRH hp hne hinv hab (ha i hi) (hb i hi)
      ha' hb' hx haleft hbright]

/-- Group the signed explicit formula into a residue sum, a zero series
and two contour integrals, keeping the cancellation inside each sum. -/
public theorem tsum_signed_kernel_contours {ι : Type*} (s : Finset ι) (K : ι → MellinKernel)
    (c : ι → ℂ) {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b x : ℝ} (hab : a < b)
    (ha : ∀ i ∈ s, -1 / 2 - (K i).delta < a) (hb : ∀ i ∈ s, b ≤ 1 / 2 + (K i).delta)
    (ha' : -3 / 2 ≤ a) (hb' : b ≤ 3 / 2) (hx : 1 ≤ x) (haleft : a < -1 / 2) (hbright : 1 / 2 < b) :
    let W := fun i (z : ℂ) ↦ (K i).function z * (x : ℂ) ^ z
    let F := fun i (t : ℝ) ↦
      -logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2) *
        W i ((a : ℂ) + Complex.I * t)
    let G := fun i (t : ℝ) ↦
      logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) * W i ((b : ℂ) + Complex.I * t)
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (∑' n : ℕ, ∑ i ∈ s, c i * (K i).summand χ x n) =
      (∑ i ∈ s,
            c i * weightedResidue (K i) (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)) -
          (∑' ρ : ℂ, ∑ i ∈ s, c i * (K i).oscillatingZeroTerm χ x ρ) +
        d * (∫ t : ℝ, ∑ i ∈ s, c i * F i t) +
        d * (∫ t : ℝ, ∑ i ∈ s, c i * G i t) := by
  intro W F G d
  have hx0 := zero_lt_one.trans_le hx
  have hf (i : ι) (hi : i ∈ s) : MeasureTheory.Integrable (fun t ↦ c i * F i t) :=
    (integrable_completed_left_line (K i) hp hne hinv (ha i hi) haleft ha' hx0).const_mul _
  have hg (i : ι) (hi : i ∈ s) : MeasureTheory.Integrable (fun t ↦ c i * G i t) := by
    have hi' :=
      integrable_gammaFactor_power_line (K i) χ (by linarith only [hbright]) (hb i hi) hb' hx0
    simpa only [G, W, ← mul_assoc] using hi'.const_mul (c i)
  have h := tsum_signed_kernel_residue s K c hq hGRH hp hne hinv hab ha hb ha' hb' hx haleft hbright
  rw [tsum_signed_oscillating_zero s K c hq hGRH hp hne hinv hx0,
    MeasureTheory.integral_finsetSum s hf, MeasureTheory.integral_finsetSum s hg]
  simp only [MeasureTheory.integral_const_mul, Finset.mul_sum]
  dsimp only [d]
  rw [h]
  simp only [F, G, W, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_left_comm (c _)]

end PseudoPrime.LLS.PaperStatements.MellinKernel
