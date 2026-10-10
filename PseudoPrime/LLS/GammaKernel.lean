/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaKernelIdentities

/-! # The admissible gamma Mellin kernel

The shifted gamma function satisfies every kernel condition of Section 6.3.
Recurrence and compact real-gamma bounds give uniform strip decay.
Mellin inversion supplies the real nonnegative transform.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- On the positive compact interval `[1/2,4]`, real gamma has a positive
uniform upper bound. Continuity and compactness provide the bound.
It controls the shifted recurrence numerators in the kernel strip. -/
private theorem gamma_real_compact_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Set.Icc (1 / 2 : ℝ) 4, Real.Gamma x ≤ B := by
  have hc : ContinuousOn Real.Gamma (Set.Icc (1 / 2 : ℝ) 4) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono
      (by
        intro x hx
        exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hx.1)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨|B| + 1, by linarith only [abs_nonneg B], ?_⟩
  intro x hx
  have hb := hB x hx
  rw [Real.norm_eq_abs] at hb
  exact (le_abs_self _).trans (hb.trans (by linarith only [le_abs_self B]))

/-- A positive lower bound for the distance excludes the gamma pole.
A vanishing shifted argument would contradict the strictly positive distance. -/
private theorem gamma_ne_pole {s : ℂ} {η : ℝ} (hη : 0 < η) (hd : η ≤ ‖s + 1 / 2‖) :
    s + 1 / 2 ≠ 0 := by
  intro he
  rw [he, norm_zero] at hd
  exact (not_le_of_gt hη) hd

/-- In the fixed strip, the shifted gamma norm times its pole distance
is bounded uniformly. One recurrence moves to a positive real half-plane,
where Euler's integral and the compact real-gamma bound apply. -/
private theorem gamma_norm_mul_distance_le {B η : ℝ} (hη : 0 < η)
    (hB : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 4, Real.Gamma x ≤ B) {s : ℂ} (hs : -3 / 4 < s.re ∧ s.re < 3 / 4)
    (hd : η ≤ ‖s + 1 / 2‖) : ‖Complex.Gamma (s + 1 / 2)‖ * η ≤ B := by
  have hr : (s + 1 / 2 + 1).re = s.re + 3 / 2 := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    ring
  have hp : 0 < (s + 1 / 2 + 1).re := by
    rw [hr]; linarith only [hs.1]
  have hn := Analysis.norm_Gamma_le_realGamma hp
  rw [Complex.Gamma_add_one _ (gamma_ne_pole hη hd), norm_mul, hr] at hn
  have hb := hB (s.re + 3 / 2) ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
  have hm := mul_le_mul_of_nonneg_right hd (norm_nonneg (Complex.Gamma (s + 1 / 2)))
  calc
    _ = η * ‖Complex.Gamma (s + 1 / 2)‖ := mul_comm _ _
    _ ≤ _ := hm
    _ ≤ _ := hn
    _ ≤ _ := hb

/-- Away from its pole, shifted gamma has uniform quadratic decay in the
fixed strip. Bound small heights by one recurrence and large heights by two.
This establishes the decay condition for the gamma Mellin kernel. -/
private theorem gamma_strip_decay {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ s : ℂ,
          (-3 / 4 < s.re ∧ s.re < 3 / 4) →
            η ≤ ‖s + 1 / 2‖ → ‖Complex.Gamma (s + 1 / 2)‖ ≤ C / (1 + ‖s‖ ^ 2) := by
  obtain ⟨B, hBpos, hB⟩ := gamma_real_compact_bound
  have hbdiv : 0 < B / η := div_pos hBpos hη
  refine ⟨3 * (B / η) + 3 * B, by linarith only [hbdiv, hBpos], ?_⟩
  intro s hs hd
  have hsr : s.re ^ 2 ≤ 1 := by
    have hm :=
      mul_nonneg (by linarith only [hs.1] : 0 ≤ s.re + 1) (by linarith only [hs.2] : 0 ≤ 1 - s.re)
    nlinarith only [hm]
  have hsq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hn := norm_nonneg (Complex.Gamma (s + 1 / 2))
  apply (le_div_iff₀ (by linarith only [sq_nonneg ‖s‖] : 0 < 1 + ‖s‖ ^ 2)).mpr
  by_cases ht : s.im ^ 2 ≤ 1
  · have hb := (le_div_iff₀ hη).mpr (gamma_norm_mul_distance_le hη hB hs hd)
    have hs3 : 1 + ‖s‖ ^ 2 ≤ 3 := by
      rw [hsq]; linarith only [hsr, ht]
    have hm := mul_le_mul_of_nonneg_left hs3 hn
    nlinarith only [hm, hb, hBpos]
  · have htp : 0 < s.im ^ 2 := by linarith only [lt_of_not_ge ht]
    have him : (s + 1 / 2).im = s.im := by
      simp only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, zero_div, add_zero]
    have hr : (s + 1 / 2).re = s.re + 1 / 2 := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    have hb :=
      Analysis.norm_Gamma_le_im_sq (s := s + 1 / 2)
        (by
          rw [hr]; linarith only [hs.1])
        (by
          rw [him]; exact sq_pos_iff.mp htp)
    rw [hr, him] at hb
    have hg := hB (s.re + 1 / 2 + 2) ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
    have hmul := ((le_div_iff₀ htp).mp hb).trans hg
    have hs3 : 1 + ‖s‖ ^ 2 ≤ 3 * s.im ^ 2 := by
      rw [hsq]
      linarith only [hsr, lt_of_not_ge ht]
    have hm := mul_le_mul_of_nonneg_left hs3 hn
    nlinarith only [hm, hmul, hbdiv]

/-- The shifted gamma function is differentiable in the fixed strip away
from its pole. Comparing real parts excludes all other nonpositive integer poles.
This supplies holomorphy of the gamma kernel. -/
private theorem gamma_shift_differentiable {s : ℂ} (hs : -3 / 4 < s.re) (hz : s + 1 / 2 ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ ↦ Complex.Gamma (z + 1 / 2)) s := by
  apply (Complex.differentiableAt_Gamma _ ?_).comp s (differentiableAt_id.add_const _)
  intro m he
  by_cases hm : m = 0
  · subst m
    simp only [Nat.cast_zero, neg_zero] at he
    exact hz he
  · have hr := congrArg Complex.re he
    simp only [id_eq, Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at hr
    have hn : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hm)
    linarith only [hr, hn, hs]

/-- Multiplication by the shifted argument regularizes the gamma pole.
The recurrence identifies the extension with gamma on a positive half-plane,
where its complex derivative exists. -/
private theorem gamma_regularized_differentiable {s : ℂ} (hs : -3 / 4 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ ↦ Complex.Gamma (z + 1 / 2 + 1)) s := by
  have hr : 0 < (s + 1 / 2 + 1).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith only [hs]
  exact
    (Complex.hasDerivAt_Gamma_of_re_pos hr).differentiableAt.comp s
      ((differentiableAt_id.add_const _).add_const _)

/-- Away from `s=-1/2`, the shifted argument is nonzero.
An additive cancellation proves the condition needed for gamma recurrence. -/
private theorem gamma_shift_ne_zero {s : ℂ} (hs : s ≠ -1 / 2) : s + 1 / 2 ≠ 0 := by
  intro he
  apply hs
  calc
    s = -(1 / 2 : ℂ) := eq_neg_of_add_eq_zero_left he
    _ = -1 / 2 := by ring

/-- The admissible Section 6.3 kernel `Gamma(s+1/2)`, with strip width `1/8`.
The only pole in the chosen region is regularized by gamma recurrence.
Uniform quadratic decay, absolute convergence, and line-independent inversion
are proved rather than assumed. Its positive real transform is `sqrt(u) exp(-u)`.
This kernel is used in the small-index specialization of Proposition 6.1. -/
noncomputable def gammaMellinKernel : MellinKernel where
  function s := Complex.Gamma (s + 1 / 2)
  delta := 1 / 8
  delta_pos := by norm_num only
  region := {s : ℂ | -3 / 4 < s.re ∧ s.re < 3 / 4}
  region_open :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  strip_subset := by
    intro s hs
    exact ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
  holomorphic := by
    intro s hs
    have hz : s ≠ -1 / 2 := by simpa only [Set.mem_singleton_iff] using hs.2
    exact (gamma_shift_differentiable hs.1.1 (gamma_shift_ne_zero hz)).differentiableWithinAt
  regularized s := Complex.Gamma (s + 1 / 2 + 1)
  regularized_holomorphic := by
    intro s hs
    exact (gamma_regularized_differentiable hs.1).differentiableWithinAt
  regularized_eq := by
    intro s _ hs
    exact Complex.Gamma_add_one _ (gamma_shift_ne_zero hs)
  decay := by
    intro η hη
    obtain ⟨C, hC, hbound⟩ := gamma_strip_decay hη
    exact ⟨C, hC, fun s hs hd ↦ hbound s hs hd⟩
  mellin_integrable := fun c u hc _ hu ↦ integrable_inverseMellin_gamma hc hu
  mellin_eq := by
    intro c u hc _ hu
    rw [inverseMellin_gamma hc hu, inverseMellin_gamma (by norm_num only) hu]
  mellin_nonneg := by
    intro u hu
    rw [inverseMellin_gamma (by norm_num only) hu, Complex.ofReal_re]
    exact mul_nonneg (Real.sqrt_nonneg u) (Real.exp_pos (-u)).le
  mellin_nonzero := by
    refine ⟨1, by norm_num only, ?_⟩
    rw [inverseMellin_gamma (by norm_num only) (by norm_num only), Complex.ofReal_re, Real.sqrt_one,
      one_mul]
    exact (Real.exp_pos _).ne'
  mellin_real := by
    intro u hu
    rw [inverseMellin_gamma (by norm_num only) hu, Complex.ofReal_im]

end PseudoPrime.LLS.PaperStatements
