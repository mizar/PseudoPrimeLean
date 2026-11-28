/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianFirstWitness
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSixPoleAbelBound
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTrivial656

/-! # K137 Gaussian witnesses on the second and third compressed cells -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Bound the linear contribution using the cell's right endpoint,
the nonpositive slope, and the auxiliary coefficient bounds. -/
private theorem k137_linear_lower {s L B : ℝ} (hs : 1 ≤ s) (hL : 0 ≤ L) (hU : L ≤ B)
    (hcoef : (0.71780481 + 0.006702) * (s - 1) + 0.71780481 - 3 / 4 + 0.0002205111 ≤ 0)
    (hend :
      -10.537 ≤ ((0.71780481 + 0.006702) * (s - 1) + 0.71780481 - 3 / 4 + 0.0002205111) * B / 2) :
    -10.537 ≤
      (0.71780481 - quarterAuxHalfCoeff663) * (s * L / 2) -
        (3 / 4 + quarterAuxMix663 quarterConductorProfile663) * (L / 2) := by
  have h := mul_le_mul_of_nonpos_left hU hcoef
  have hδ :=
    mul_le_mul_of_nonneg_right quarter_aux_delta_lower_663.le
      (div_nonneg hL (by norm_num only : (0 : ℝ) ≤ 2))
  have hH :=
    mul_le_mul_of_nonneg_right quarter_aux_half_upper_663
      (mul_nonneg (sub_nonneg.mpr hs) (div_nonneg hL (by norm_num only : (0 : ℝ) ≤ 2)))
  linarith only [h, hδ, hH, hend]

/-- Combine the six-pole principal bound with the Gamma term and the
signed Chebyshev boundary charge. -/
private theorem gaussian_principal_gamma_lower (hRH : RiemannHypothesis) {y B G C : ℝ}
    (hy : 331 ≤ y)
    (hγ :
      (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (y ^ 2)).re ≤
        -2.16 * quarterWeight656 (y ^ 2) 1 - G)
    (hb : (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ B)
    (hlog : C ≤ 4 * quarterWeight656 (y ^ 2) (y ^ 2) * Real.log (2 * Real.pi)) :
    let x := y ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * y + 3 * G - 0.026012 - B - 0.001 + C <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro x W
  have hx : 1 ≤ x := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 331).trans hy)
  have hw : 0 ≤ quarterWeight656 x 1 := by
    have hlog := Real.log_nonneg hx
    unfold quarterWeight656
    simp only [Real.sqrt_one, one_div, inv_one, one_mul, Real.log_inv, sub_neg_eq_add]
    positivity
  have hcoeff : (100 / 31 - 1.7875 + 3 * Real.log (2 * Real.pi) - 6.48 : ℝ) ≤ 0.6 := by
    linarith only [Analysis.log_two_mul_pi_lt]
  have hend :=
    (mul_le_mul_of_nonneg_right hcoeff hw).trans
      (mul_le_mul_of_nonneg_left (gaussian_six_pole_endpoint_weight hy)
        (by norm_num only : (0 : ℝ) ≤ 0.6))
  have hmain := gaussian_six_pole_principal_mass hRH hy
  dsimp only [x, W] at hx hlog hend hmain hγ ⊢
  ring_nf at hb hlog hend hmain hγ ⊢
  linarith only [hb, hlog, hend, hmain, hγ]

/-- Combine the six-pole principal bound with the Gamma term and the
signed Chebyshev boundary charge shared by the two later cells. -/
private theorem k137_principal_lower (hRH : RiemannHypothesis) {y : ℝ}
    (hy : y ∈ Set.Icc (663 / 2) (1329 / 4))
    (hb : (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.074) :
    let x := y ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * y + 0.07155 - 0.026012 - 0.074 - 0.001 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro x W
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hy.1)
      (quarter_gamma_gaussian_first hy) hb
      (mul_nonneg
        (mul_nonneg (by norm_num only)
          (cutoff_weight_bound (one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 663 / 2).trans hy.1))).1)
        (by linarith only [Analysis.log_two_mul_pi_gt]))
  dsimp only [x, W] at h ⊢
  linarith only [h]

private theorem k197_log_credit {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 334) :
    0.00205 ≤ 4 * quarterWeight656 (r ^ 2) (r ^ 2) * Real.log (2 * Real.pi) := by
  have hp := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  rw [quarter_cutoff_weight_656 (sq_pos_of_pos hp), Real.sqrt_sq hp.le]
  have hlog : (1.837 : ℝ) ≤ Real.log (2 * Real.pi) := by linarith only [Analysis.log_two_mul_pi_gt]
  have hW : (0.09319731 : ℝ) ≤ (quarterKernel656.transform 1).re := by
    linarith only [quarter_unit_weight_656.1]
  have hw :=
    (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 0.09319731) hp hr.2).trans
      (div_le_div_of_nonneg_right hW hp.le)
  have h :=
    mul_le_mul hw hlog (by norm_num only : (0 : ℝ) ≤ 1.837)
      ((by norm_num only : (0 : ℝ) ≤ 0.09319731 / 334).trans hw)
  linarith only [h]

/-- Combine the principal sum and Gamma term on the first K197 cell
using its signed Chebyshev boundary bound. -/
theorem gaussian_k197_first_principal (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (2657 / 4) (2659 / 4)) :
    let y := (500186760939 / 500000000000 : ℝ) * L / 2
    let x := y ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * y - 0.063502 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro y x W
  have hy : y ∈ Set.Icc (663 / 2) (665 / 2) :=
    ⟨by
      dsimp only [y]; linarith only [hL.1], by
      dsimp only [y]; linarith only [hL.2]⟩
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hy.1)
      (quarter_gamma_k197_first hy) (gaussian_k197_first_boundary_le hL)
      (k197_log_credit ⟨hy.1, hy.2.trans (by norm_num only)⟩)
  change
    _ <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re at h
  linarith only [h]

/-- Prime triviality of all three characters contradicts the comparison
after inserting the linear, principal, reflection, and prime-power bounds. -/
private theorem k137_later_pair_false {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L s : ℝ}
    (hs : s ∈ Set.Icc 1 (1001 / 1000)) (hL : L ∈ Set.Icc (1327 / 2) (2657 / 4))
    (hlev : Real.log p + Real.log q + Real.log r = 2 * L)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hlin :
      -10.537 ≤
        (0.71780481 - quarterAuxHalfCoeff663) * (s * L / 2) -
          (3 / 4 + quarterAuxMix663 quarterConductorProfile663) * (L / 2)) :
    let y := s * L / 2
    y ∈ Set.Icc (663 / 2) (1329 / 4) →
      (-4 * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2)) ≤ 0.074 →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → a l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → b l = 1) →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → c l = 1) → False := by
  intro y hy hB hpa hpb hpc
  let R := (quarterKernel656.transform (y ^ 2)⁻¹).re
  let d := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
  have hy₁ : (328 : ℝ) ≤ y := (by norm_num only : (328 : ℝ) ≤ 663 / 2).trans hy.1
  have hy₃ : y ∈ Set.Icc 328 333 := ⟨hy₁, hy.2.trans (by norm_num only)⟩
  have hs₀ := zero_lt_one.trans_le hs.1
  have hscale : y / s = L / 2 := by
    apply (div_eq_iff hs₀.ne').mpr
    dsimp only [y]
    ring
  have hlev' : Real.log p + Real.log q + Real.log r = 4 * (y / s) := by
    rw [hscale]
    linarith only [hlev]
  have ⟨hsupp, hgain⟩ := k137_later_power_data hs hL
  have hupper :=
    quarter_scaled_comparison_upper ha hb hc hp hq hr hG hy₃ hlev' ht hpa hpb hpc fixedPowers663
      (fun n hn ↦ (hsupp n hn).1) (fun n hn ↦ (hsupp n hn).2) (fun _ hn ↦ fixed_power_base_663 hn)
  have hallow :
    (14.54795483 : ℝ) ≤
      if y ≤ 663 / 2 then 14.55079583 else if y ≤ 332 then 14.54846283 else 14.54795483 := by
    split
    · norm_num only
    · split <;> norm_num only
  have hd (n : ℕ) : 0 ≤ d n ∧ d n ≤ 4 :=
    ⟨sub_nonneg.mpr (ht n).2, by
      dsimp only [d]; linarith only [(ht n).1]⟩
  have hprefix := gaussian_k137_deficit_prefix a b c hy.1 hpa hpb hpc
  have hshift :=
    quarter_scaled_shift_mix_663 ha hb hc hG.riemann hy₁ (by simpa only [mul_div_assoc] using hlev')
  have htheta := gaussian_k137_shift_lower (scale := s) hy hs.1
  have href := gaussian_k137_reflect_lower hG.riemann d hd hprefix hy
  have hxi := (abs_le.mp (quarter_shift_xi_cap_663 hG.riemann hy₁)).1
  have hm := gaussian_k137_main_reflect a b c hG.riemann hy ht hpa hpb hpc
  have hx : 1 ≤ y ^ 2 := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 328).trans hy₁)
  have hE : 0 ≤ quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (y ^ 2) := by
    have h := quarter_main_euler_hasSum_656 (1 : DirichletCharacter ℂ 1) (zero_lt_one.trans_le hx)
    have hχ (n : ℕ) : ((1 : DirichletCharacter ℂ 1) n).re = 1 := by
      simp only [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re]
    simp only [hχ, one_mul, quarter_main_euler_weight_656 hx] at h
    rw [← h.tsum_eq]
    exact
      tsum_nonneg
        (fun n ↦ by
          have hz :=
            add_nonneg (add_nonneg (by norm_num only : (0 : ℝ) ≤ 21 / 8) (Real.log_nonneg hx))
              (Real.log_natCast_nonneg n)
          positivity)
  have hmain := k137_principal_lower hG.riemann hy hB
  have hcond := quarter_main_conductor_box_663 hy₁
  rw [ite_eq_left ((by norm_num only : (1319 / 4 : ℝ) ≤ 663 / 2).trans hy.1)] at hcond
  change 4 * y * R ≤ _ at hcond
  have htR : 4 * (y / s) * R ≤ 1.654812 := by
    rw [show 4 * (y / s) * R = (4 * y * R) / s by ring]
    apply (div_le_iff₀ hs₀).mpr
    linarith only [hcond, hs.1]
  rw [hscale] at htR
  dsimp only at hupper hmain hgain
  rw [hscale] at hupper
  dsimp only [d, R, y] at *
  ring_nf at hupper hshift hlin hmain htR hgain hm htheta href hxi hallow hE
  linarith only [hupper, hshift, hlin, hmain, hallow, htheta, href, hxi, hm, htR, hgain, hE]

/-- Transfer the pair-character contradiction to a rejecting prime below
the target Gaussian cutoff for an odd uniform Korselt triple. -/
private theorem k137_later_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {s : ℝ}
    (hs : s ∈ Set.Icc 1 (1001 / 1000)) (hL : Real.log n ∈ Set.Icc (1327 / 2) (2657 / 4))
    (hlin :
      -10.537 ≤
        (0.71780481 - quarterAuxHalfCoeff663) * (s * Real.log n / 2) -
          (3 / 4 + quarterAuxMix663 quarterConductorProfile663) * (Real.log n / 2)) :
    let y := s * Real.log n / 2
    y ∈ Set.Icc (663 / 2) (1329 / 4) →
      (-4 * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2)) ≤ 0.074 →
      y ^ 2 ≤ gaussianWitnessCutoff (Real.log n) →
      ∃ l : ℕ,
        l.Prime ∧
          (l : ℝ) ≤ gaussianWitnessCutoff (Real.log n) ∧
          ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  intro y hy hB hcut
  obtain ⟨l, hl, hb, hf⟩ :=
    uniform_witness_of_pair_false hn ho hu (X := y ^ 2)
      (by
        intro p q r _ _ _ a b c ha hb hc hp hq hr hlev ht hsmall
        exact
          k137_later_pair_false ha hb hc hp hq hr hGRH hs hL hlev ht hlin hy hB
            (fun l hl hX ↦ (hsmall l hl hX).1) (fun l hl hX ↦ (hsmall l hl hX).2.1)
            (fun l hl hX ↦ (hsmall l hl hX).2.2))
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Use the second compressed scale and its signed boundary to obtain a
Gaussian witness on the closed logarithmic interval from 1327/2 to 664. -/
private theorem k137_second_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (1327 / 2) 664) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ gaussianWitnessCutoff (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    k137_later_witness hn ho hu hGRH (s := 1000328278743 / 1000000000000)
      ⟨by norm_num only, by norm_num only⟩ ⟨hL.1, hL.2.trans (by norm_num only)⟩
      (k137_linear_lower (by norm_num only) (Real.log_natCast_nonneg n) hL.2 (by norm_num only)
        (by norm_num only))
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact (gaussian_second_boundary_le hL).trans (by norm_num only)
  · exact gaussianCutoff_k137_cell3 hL.1

/-- Use the third compressed scale and its signed boundary to obtain a
Gaussian witness on the closed logarithmic interval from 664 to 2657/4. -/
private theorem k137_third_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 664 (2657 / 4)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ gaussianWitnessCutoff (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    k137_later_witness hn ho hu hGRH (s := 125044806547 / 125000000000)
      ⟨by norm_num only, by norm_num only⟩
      ⟨(by norm_num only : (1327 / 2 : ℝ) ≤ 664).trans hL.1, hL.2⟩
      (k137_linear_lower (by norm_num only) (Real.log_natCast_nonneg n) hL.2 (by norm_num only)
        (by norm_num only))
  · exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact gaussian_third_boundary_le hL
  · exact gaussianCutoff_k137_cell6 hL.1

/-- Under GRH, the three compressed K137 cells cover the whole interval
from log 663 to log 2657/4 for odd uniform Korselt triples. -/
theorem gaussian_k137_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc 663 (2657 / 4)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ gaussianWitnessCutoff (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases h₁ : Real.log n ≤ 1327 / 2
  · exact gaussian_first_witness hn ho hu hGRH ⟨hL.1, h₁⟩
  by_cases h₂ : Real.log n ≤ 664
  · exact k137_second_witness hn ho hu hGRH ⟨le_of_not_ge h₁, h₂⟩
  exact k137_third_witness hn ho hu hGRH ⟨le_of_not_ge h₂, hL.2⟩

/-- Combine the principal sum and Gamma term on the second K197 cell
using its signed Chebyshev boundary bound. -/
theorem gaussian_k197_second_principal (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (2659 / 4) (2661 / 4)) :
    let y := (12505045329 / 12500000000 : ℝ) * L / 2
    let x := y ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * y - 0.042952 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro y x W
  have hy : y ∈ Set.Icc (663 / 2) 334 :=
    ⟨by
      dsimp only [y]; linarith only [hL.1], by
      dsimp only [y]; linarith only [hL.2]⟩
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hy.1)
      (quarter_gamma_k197_next hy) (gaussian_k197_cell2_boundary_le hL) (k197_log_credit hy)
  change
    _ <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re at h
  linarith only [h]

/-- Combine the principal sum and Gamma term on the third K197 cell
using its signed Chebyshev boundary bound. -/
theorem gaussian_k197_third_principal (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (2661 / 4) (2665 / 4)) :
    let y := (1000433684769 / 1000000000000 : ℝ) * L / 2
    let x := y ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * y - 0.030952 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro y x W
  have hy : y ∈ Set.Icc (663 / 2) 334 :=
    ⟨by
      dsimp only [y]; linarith only [hL.1], by
      dsimp only [y]; linarith only [hL.2]⟩
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hy.1)
      (quarter_gamma_k197_next hy) (gaussian_k197_cell3_boundary_le hL) (k197_log_credit hy)
  change
    _ <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re at h
  linarith only [h]

/-- Combine the principal sum and Gamma term on the fourth K197 cell
using its signed Chebyshev boundary bound. -/
theorem gaussian_k197_fourth_principal (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (2665 / 4) (2669 / 4)) :
    let y := (500246832053 / 500000000000 : ℝ) * L / 2
    let x := y ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * y - 0.039952 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro y x W
  have hy : y ∈ Set.Icc (663 / 2) 334 :=
    ⟨by
      dsimp only [y]; linarith only [hL.1], by
      dsimp only [y]; linarith only [hL.2]⟩
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hy.1)
      (quarter_gamma_k197_next hy) (gaussian_k197_cell4_boundary_le hL) (k197_log_credit hy)
  change
    _ <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re at h
  linarith only [h]

private theorem k197_wide_log_credit {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 336.9) :
    0.00203 ≤ 4 * quarterWeight656 (r ^ 2) (r ^ 2) * Real.log (2 * Real.pi) := by
  have hp := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  rw [quarter_cutoff_weight_656 (sq_pos_of_pos hp), Real.sqrt_sq hp.le]
  have hlog : (1.837 : ℝ) ≤ Real.log (2 * Real.pi) := by linarith only [Analysis.log_two_mul_pi_gt]
  have hW : (0.09319731 : ℝ) ≤ (quarterKernel656.transform 1).re := by
    linarith only [quarter_unit_weight_656.1]
  have hw :=
    (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 0.09319731) hp hr.2).trans
      (div_le_div_of_nonneg_right hW hp.le)
  have h :=
    mul_le_mul hw hlog (by norm_num only : (0 : ℝ) ≤ 1.837)
      ((by norm_num only : (0 : ℝ) ≤ 0.09319731 / 336.9).trans hw)
  linarith only [h]

/-- On the early K197 radii through 336.9, any certified signed boundary
cost gives a principal-sum lower bound including the Gamma term. -/
theorem gaussian_k197_wide_principal (hRH : RiemannHypothesis) {r B : ℝ}
    (hr : r ∈ Set.Icc (663 / 2) 336.9)
    (hb : -4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * r + 0.045488 - B <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro x W
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hr.1)
      (quarter_gamma_k197_wide hr) hb (k197_wide_log_credit hr)
  dsimp only [x, W] at h ⊢
  linarith only [h]

private theorem k197_mid_log_credit {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 342.9) :
    0.00199 ≤ 4 * quarterWeight656 (r ^ 2) (r ^ 2) * Real.log (2 * Real.pi) := by
  have hp := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  rw [quarter_cutoff_weight_656 (sq_pos_of_pos hp), Real.sqrt_sq hp.le]
  have hlog : (1.837 : ℝ) ≤ Real.log (2 * Real.pi) := by linarith only [Analysis.log_two_mul_pi_gt]
  have hW : (0.09319731 : ℝ) ≤ (quarterKernel656.transform 1).re := by
    linarith only [quarter_unit_weight_656.1]
  have hw :=
    (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 0.09319731) hp hr.2).trans
      (div_le_div_of_nonneg_right hW hp.le)
  have h :=
    mul_le_mul hw hlog (by norm_num only : (0 : ℝ) ≤ 1.837)
      ((by norm_num only : (0 : ℝ) ≤ 0.09319731 / 342.9).trans hw)
  linarith only [h]

/-- On the middle K197 radii through 342.9, any certified signed boundary
cost gives a principal-sum lower bound including the Gamma term. -/
theorem gaussian_k197_mid_principal (hRH : RiemannHypothesis) {r B : ℝ}
    (hr : r ∈ Set.Icc (663 / 2) 342.9)
    (hb : -4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * r + 0.044128 - B <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro x W
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hr.1)
      (quarter_gamma_k197_mid hr) hb (k197_mid_log_credit hr)
  dsimp only [x, W] at h ⊢
  linarith only [h]

private theorem k197_log_credit_to34610 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 346.1) :
    0.00197 ≤ 4 * quarterWeight656 (r ^ 2) (r ^ 2) * Real.log (2 * Real.pi) := by
  have hp := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  rw [quarter_cutoff_weight_656 (sq_pos_of_pos hp), Real.sqrt_sq hp.le]
  have hlog : (1.837 : ℝ) ≤ Real.log (2 * Real.pi) := by linarith only [Analysis.log_two_mul_pi_gt]
  have hW : (0.09319731 : ℝ) ≤ (quarterKernel656.transform 1).re := by
    linarith only [quarter_unit_weight_656.1]
  have hw :=
    (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 0.09319731) hp hr.2).trans
      (div_le_div_of_nonneg_right hW hp.le)
  have h :=
    mul_le_mul hw hlog (by norm_num only : (0 : ℝ) ≤ 1.837)
      ((by norm_num only : (0 : ℝ) ≤ 0.09319731 / 346.1).trans hw)
  linarith only [h]

/-- On the middle K197 radii through 346.1, any certified signed boundary
cost gives a principal-sum lower bound including the Gamma term. -/
theorem gaussian_k197_principal_to34610 (hRH : RiemannHypothesis) {r B : ℝ}
    (hr : r ∈ Set.Icc (663 / 2) 346.1)
    (hb : -4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * r + 0.043358 - B <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro x W
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hr.1)
      (quarter_gamma_k197_to34610 hr) hb (k197_log_credit_to34610 hr)
  dsimp only [x, W] at h ⊢
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
