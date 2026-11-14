/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount100RH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountGoodPhaseRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundEulerLog
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Height-100 zero count from a normalized phase bound -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, nonvanishing of zeta at `1/2 + 100i` excludes all zeros of
nonnegative real part at height 100. RH puts any such zero on the critical
line, where its real and imaginary parts determine the same point. -/
theorem good_height_100_of_center_ne (hRH : RiemannHypothesis)
    (hcenter : riemannZeta (((1 / 2 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) ≠ 0) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ 100 := by
  intro ρ hz hre him
  have hxi := RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz hre
  have hreal := RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
  have heq : ρ = (((1 / 2 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext
    · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero] using hreal
    · simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero] using him
  exact hcenter (heq ▸ hz)

/-- Under RH, central nonvanishing and a continuous Euler-normalized zeta
phase bounded above by `π/2` at `1/2` imply that the two-sided zero count
through height 100 is at most 58. The phase is identified with the count
argument at the good height, and the finite count is rounded down. -/
theorem count_100_le_58_of_phase (hRH : RiemannHypothesis)
    (hcenter : riemannZeta (((1 / 2 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) ≠ 0) (φ : ℝ → ℝ)
    (hc : ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)))
    (hp :
      ∀ x : ℝ,
        x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
          riemannZeta ((x : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) =
            (‖riemannZeta ((x : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I))
    (hn : φ (3 / 2) = (backlundZetaLog (((3 / 2 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).im)
    (hφ : φ (1 / 2) ≤ Real.pi / 2) : zeroCount 100 ≤ 58 := by
  have hgood := good_height_100_of_center_ne hRH hcenter
  have he := count_arg_eq_euler_phase hRH (show (100 : ℝ) ≤ 100 by norm_num only) hgood φ hc hp hn
  apply count_100_le_58_of_arg hRH
  nlinarith only [he, hφ, Real.pi_pos]

/-- A continuous phase with positive cosine cannot cross `π/2`. -/
private theorem phase_lt_of_cos_pos {a b : ℝ} (hab : a ≤ b) (φ : ℝ → ℝ)
    (hc : ContinuousOn φ (Set.Icc a b)) (hcos : ∀ x ∈ Set.Icc a b, 0 < Real.cos (φ x))
    (hb : φ b < Real.pi / 2) : φ a < Real.pi / 2 := by
  by_contra ha
  have hge : Real.pi / 2 ≤ φ a := le_of_not_gt ha
  have hm : Real.pi / 2 ∈ Set.Icc (φ b) (φ a) := ⟨hb.le, hge⟩
  obtain ⟨x, hx, he⟩ := intermediate_value_Icc' hab hc hm
  have hz := hcos x hx
  rw [he, Real.cos_pi_div_two] at hz
  exact (lt_irrefl 0) hz

/-- The Euler normalization at `3/2 + 100i` lies below `π/2`. -/
private theorem phase_endpoint_lt (φ : ℝ → ℝ)
    (hn : φ (3 / 2) = (backlundZetaLog (((3 / 2 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).im) :
    φ (3 / 2) < Real.pi / 2 := by
  have hlog :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck (14 / 5) 2 64 1 (11 / 10) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hn' : |φ (3 / 2)| ≤ Real.log (14 / 5) := by
    rw [hn]
    apply (Complex.abs_im_le_norm _).trans
    apply norm_backlundZetaLog_le_const
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact le_rfl
  have hb := (abs_le.mp hn').2
  linarith only [hb, hlog.2, Real.pi_gt_three]

/-- A polar representation of a complex number with positive real part has positive cosine. -/
private theorem phase_cos_pos (φ : ℝ → ℝ)
    (hp :
      ∀ x : ℝ,
        x ∈ Set.Icc (1 / 2) (3 / 2) →
          riemannZeta ((x : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) =
            (‖riemannZeta ((x : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I))
    (hpos :
      ∀ x : ℝ,
        x ∈ Set.Icc (1 / 2) (3 / 2) →
          0 < (riemannZeta ((x : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re) :
    ∀ x : ℝ, x ∈ Set.Icc (1 / 2) (3 / 2) → 0 < Real.cos (φ x) := by
  intro x hx
  have hr := congrArg Complex.re (hp x hx)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_mul, sub_zero, Real.exp_zero,
    one_mul] at hr
  have h := hpos x hx
  rw [hr] at h
  have hz : riemannZeta ((x : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro hz
    have hh := hpos x hx
    rw [hz, Complex.zero_re] at hh
    exact (lt_irrefl 0) hh
  exact (mul_pos_iff_of_pos_left (norm_pos_iff.mpr hz)).mp h

/-- Under RH, positivity of the real part of zeta on the horizontal segment from
`1/2 + 100i` to `3/2 + 100i` gives the two-sided zero count `N(100) ≤ 58`.
The Euler-normalized phase cannot cross `π/2`, so the count formula rounds down. -/
theorem count_100_le_58_of_positive_line (hRH : RiemannHypothesis)
    (hpos :
      ∀ x : ℝ,
        x ∈ Set.Icc (1 / 2) (3 / 2) →
          0 < (riemannZeta ((x : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re) :
    zeroCount 100 ≤ 58 := by
  have hcenter : riemannZeta (((1 / 2 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    intro hz
    have hh := hpos (1 / 2) ⟨le_rfl, by norm_num only⟩
    rw [hz, Complex.zero_re] at hh
    exact (lt_irrefl 0) hh
  have hgood := good_height_100_of_center_ne hRH hcenter
  obtain ⟨φ, hc, hp, hn, _⟩ :=
    exists_euler_phase_of_count hRH (show (100 : ℝ) ≤ 100 by norm_num only) hgood
  have hsubset : Set.Icc (1 / 2 : ℝ) (3 / 2) ⊆ Set.Icc (-(1 / 2)) (3 / 2) :=
    Set.Icc_subset_Icc (by norm_num only) le_rfl
  have hcos := phase_cos_pos φ (fun x hx => hp x (hsubset hx)) hpos
  have hφ :=
    phase_lt_of_cos_pos (show (1 / 2 : ℝ) ≤ 3 / 2 by norm_num only) φ (hc.mono hsubset) hcos
      (phase_endpoint_lt φ hn)
  exact count_100_le_58_of_phase hRH hcenter φ hc hp hn hφ.le

/-- A derivative bound of 128 and lower bounds of 1 on the 129 grid points
`1/2 + k/128` imply positivity on the whole segment. The floor of the scaled
distance gives a grid point less than one mesh width to the left. -/
private theorem positive_of_grid (f : ℝ → ℝ)
    (hd : ∀ t ∈ Set.Icc (1 / 2) (3 / 2), DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Set.Icc (1 / 2) (3 / 2), ‖deriv f t‖ ≤ 128)
    (hg : ∀ k : ℕ, k ≤ 128 → 1 ≤ f (1 / 2 + (k : ℝ) / 128)) :
    ∀ t ∈ Set.Icc (1 / 2) (3 / 2), 0 < f t := by
  intro t ht
  let k := Nat.floor (128 * (t - 1 / 2))
  have hn : 0 ≤ 128 * (t - 1 / 2) := by nlinarith only [ht.1]
  have hk := Nat.floor_le hn
  have hk' := Nat.lt_floor_add_one (128 * (t - 1 / 2))
  change (k : ℝ) ≤ 128 * (t - 1 / 2) at hk
  change 128 * (t - 1 / 2) < (k : ℝ) + 1 at hk'
  have hkn : k ≤ 128 := by
    apply (Nat.cast_le (α := ℝ)).mp
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hk, ht.2]
  have hleft : 1 / 2 + (k : ℝ) / 128 ≤ t := by nlinarith only [hk]
  have hright : t - (1 / 2 + (k : ℝ) / 128) < 1 / 128 := by nlinarith only [hk']
  have hkmem : 1 / 2 + (k : ℝ) / 128 ∈ Set.Icc (1 / 2) (3 / 2) := by
    constructor
    · have hknonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      nlinarith only [hknonneg]
    · exact le_trans hleft ht.2
  have hmv :=
    Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc (1 / 2 : ℝ) (3 / 2)) hkmem ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hleft)] at hmv
  have hv := (abs_le.mp hmv).1
  have hgk := hg k hkn
  nlinarith only [hv, hgk, hright]

/-- The real part of zeta on the horizontal line at height 100 is differentiable.
The line avoids the pole at one, and real and imaginary projections are linear. -/
private theorem zeta_line_differentiable (t : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => (riemannZeta ((y : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re)
      t := by
  have hs : ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    norm_num only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, Complex.one_im] at hi
  have hz := (differentiableAt_riemannZeta hs).real_of_complex
  have hi : DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) t :=
    Complex.ofRealCLM.differentiable.differentiableAt.add_const _
  exact Complex.reCLM.differentiable.differentiableAt.comp t (hz.comp t hi)

/-- Under RH, lower bounds of 1 for the real part of zeta at the 129 grid points
`1/2 + k/128 + 100i`, together with a derivative bound of 128 on the intervening
segment, imply `N(100) ≤ 58`. The mean value bound supplies the positive line. -/
theorem count_100_le_58_of_grid (hRH : RiemannHypothesis)
    (hb :
      ∀ t ∈ Set.Icc (1 / 2) (3 / 2),
        ‖deriv (fun y : ℝ => (riemannZeta ((y : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re) t‖ ≤ 128)
    (hg :
      ∀ k : ℕ,
        k ≤ 128 →
          1 ≤ (riemannZeta (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re) :
    zeroCount 100 ≤ 58 := by
  apply count_100_le_58_of_positive_line hRH
  exact positive_of_grid _ (fun t _ => zeta_line_differentiable t) hb hg

/-- Along the line at height 100, the real derivative of the real part is the real
part of the complex derivative. This follows by composing with the line map. -/
private theorem zeta_line_deriv (t : ℝ) :
    deriv (fun y : ℝ => (riemannZeta ((y : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re) t =
      (deriv riemannZeta ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re := by
  have hs : ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    norm_num only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, Complex.one_im] at hi
  have hz := (differentiableAt_riemannZeta hs).hasDerivAt
  have hc := hz.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).add_const (((100 : ℝ) : ℂ) * Complex.I))
  have hr := hc.real_of_complex
  simpa only [mul_one, Function.comp_apply, id_eq] using hr.deriv

/-- Under RH, the 129 grid lower bounds and a bound of 128 for the norm of the
complex zeta derivative on the intervening segment imply `N(100) ≤ 58`.
The real derivative needed for interpolation is bounded by the complex norm. -/
theorem count_100_le_58_of_grid_complex (hRH : RiemannHypothesis)
    (hb :
      ∀ t : ℝ,
        t ∈ Set.Icc (1 / 2) (3 / 2) →
          ‖deriv riemannZeta ((t : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)‖ ≤ 128)
    (hg :
      ∀ k : ℕ,
        k ≤ 128 →
          1 ≤ (riemannZeta (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)).re) :
    zeroCount 100 ≤ 58 := by
  apply count_100_le_58_of_grid hRH
  · intro t ht
    rw [zeta_line_deriv, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hb t ht)
  · exact hg

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
