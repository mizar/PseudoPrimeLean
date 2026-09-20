/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.Growth
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorGrowth
import PseudoPrime.AnalyticNumberTheory.Gamma.GrowthElementary

/-!
# Variable-radius Borel–Carathéodory bounds for digamma

The fixed-radius estimate `norm_digamma_shift_add_mul_I_le` in `RiemannZeta.Growth`
gives a linear bound in the imaginary part. Here a radius proportional to the imaginary part,
combined with a shift whose cost is bounded by `n / |Im z|`, gives a logarithmic bound.
The local logarithm and Gamma norm estimates are reused from `RiemannZeta.Growth`.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: `c : ℂ`, `R U : ℝ` with `R > 0`, the open ball `ball c R` lies in `Re > 0`,
`log ‖Γ c‖ < U`, and `log ‖Γ w‖ ≤ U` for every `w ∈ ball c R`.
Conclusion: `‖digamma c‖ ≤ 4 * (U - log ‖Γ c‖) / R`.
Content: `PseudoPrime.AnalyticNumberTheory.RiemannZeta.`
  `exists_hasDerivAt_digamma_re_eq_log_norm_Gamma` gives a local primitive `g` of `digamma`
  with `Re (g w) = log ‖Γ w‖`; `Complex.borelCaratheodory_zero` (mathlib, general Schwarz-lemma
  Borel–Carathéodory) applied to `h z := g (c + z) - g c` on `ball 0 R` (bounded above by
  `M := U - Re (g c)` in real part, `h 0 = 0`) gives `‖h z‖ ≤ 2 M ‖z‖ / (R - ‖z‖)`;
  evaluated on the Cauchy sphere `sphere c (R/2)` this is `≤ 2M`; Cauchy's estimate
  (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`, order `1`, radius `R/2`) then gives
  `‖deriv f c‖ = ‖digamma c‖ ≤ 1! · 2M / (R/2) = 4M/R`.
Role: the left-vertical step backbone — letting `R` grow with `|Im s|`
  (rather than staying fixed at `1/2`) is what turns the resulting digamma bound from
  `O(|Im s|)` (as in `PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_digamma_shift_add_mul_I_le`)
  into `O(log |Im s|)`, which the left-edge argument's left-vertical integral needs to be
  absolutely convergent.
-/
theorem norm_digamma_le_of_logGamma_ball_bound {c : ℂ} {R U : ℝ} (hR : 0 < R)
    (hball : ∀ w ∈ Metric.ball c R, 0 < w.re) (hMpos : Real.log ‖Complex.Gamma c‖ < U)
    (hupper : ∀ w ∈ Metric.ball c R, Real.log ‖Complex.Gamma w‖ ≤ U) :
    ‖Complex.digamma c‖ ≤ 4 * (U - Real.log ‖Complex.Gamma c‖) / R := by
  obtain ⟨g, hg', hgRe⟩ := RiemannZeta.exists_hasDerivAt_digamma_re_eq_log_norm_Gamma hR hball
  have hccenter : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  set M : ℝ := U - (g c).re with hM_def
  have hMpos' : 0 < M := by
    rw [hM_def, hgRe c hccenter]; linarith only [hMpos]
  set h : ℂ → ℂ := fun z => g (c + z) - g c with hh_def
  have hgc_shift_diffOn : DifferentiableOn ℂ h (Metric.ball (0 : ℂ) R) := by
    intro z hz
    have hcz_mem : c + z ∈ Metric.ball c R := by
      simpa only [Metric.mem_ball, dist_self_add_left, dist_zero_right] using hz
    have : DifferentiableAt ℂ (fun z => g (c + z)) z :=
      ((hg' (c + z) hcz_mem).differentiableAt).comp z ((differentiableAt_id).const_add c)
    exact (this.sub_const (g c)).differentiableWithinAt
  have hh0 : h 0 = 0 := by simp only [hh_def, add_zero, sub_self]
  have hh_bound : ∀ z ∈ Metric.ball (0 : ℂ) R, (h z).re ≤ M := by
    intro z hz
    have hcz_mem : c + z ∈ Metric.ball c R := by
      simpa only [Metric.mem_ball, dist_self_add_left, dist_zero_right] using hz
    have hzupper := hupper (c + z) hcz_mem
    simp only [hh_def, Complex.sub_re]
    rw [hgRe (c + z) hcz_mem]
    linarith only [hM_def, hzupper]
  have hBC : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖h z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) := by
    intro z hz
    exact
      Complex.borelCaratheodory_zero hMpos' hgc_shift_diffOn (fun w hw => hh_bound w hw) hR hz hh0
  set f : ℂ → ℂ := fun w => g w - g c with hf_def
  have hfh : ∀ w : ℂ, f w = h (w - c) := by
    intro w; simp only [hf_def, hh_def, add_sub_cancel]
  have hR2 : (0 : ℝ) < R / 2 := by linarith only [hR]
  have hf_diffOn : DifferentiableOn ℂ f (Metric.ball c (R / 2)) := by
    intro w hw
    have hw' : w ∈ Metric.ball c R := by
      have := Metric.mem_ball.mp hw
      exact Metric.mem_ball.mpr (by linarith only [this, hR])
    exact ((hg' w hw').differentiableAt.sub_const (g c)).differentiableWithinAt
  have hf_diffContOnCl : DiffContOnCl ℂ f (Metric.ball c (R / 2)) := by
    constructor
    · exact hf_diffOn
    · have hDiffCl : DifferentiableOn ℂ f (closure (Metric.ball c (R / 2))) := by
        intro w hw
        have hw' : w ∈ Metric.ball c R := by
          have hw2 := Metric.closure_ball_subset_closedBall hw
          have := Metric.mem_closedBall.mp hw2
          exact Metric.mem_ball.mpr (by linarith only [this, hR])
        exact ((hg' w hw').differentiableAt.sub_const (g c)).differentiableWithinAt
      exact hDiffCl.continuousOn
  have hsphere_bound : ∀ w ∈ Metric.sphere c (R / 2), ‖f w‖ ≤ 2 * M := by
    intro w hw
    have hw_norm : ‖w - c‖ = R / 2 := by
      have := Metric.mem_sphere.mp hw
      rwa [Complex.dist_eq] at this
    have hw_mem : w - c ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right, hw_norm]; linarith only [hR]
    have hbc := hBC (w - c) hw_mem
    rw [hw_norm] at hbc
    rw [hfh w]
    calc
      ‖h (w - c)‖ ≤ 2 * M * (R / 2) / (R - R / 2) := hbc
      _ = 2 * M := by
        rw [show R - R / 2 = R / 2 from by ring, mul_div_assoc, div_self (ne_of_gt hR2), mul_one]
  have hcauchy :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := f) (c := c) (R := R / 2) (C :=
      2 * M) 1 hR2 hf_diffContOnCl hsphere_bound
  simp only [iteratedDeriv_one] at hcauchy
  have hderivf : deriv f c = Complex.digamma c := by
    have hderivg : deriv g c = Complex.digamma c := (hg' c hccenter).deriv
    have heq : deriv f c = deriv g c := by
      simp only [hf_def]; rw [deriv_sub_const]
    rw [heq, hderivg]
  rw [hderivf] at hcauchy
  have hfactorial : (Nat.factorial 1 : ℝ) * (2 * M) / (R / 2) ^ 1 = 4 * M / R := by
    simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one]
    field_simp
    ring
  rw [hfactorial] at hcauchy
  have hMeq : M = U - Real.log ‖Complex.Gamma c‖ := by rw [hM_def, hgRe c hccenter]
  rwa [hMeq] at hcauchy

/-! ### the left-vertical step: a sharp (`O(1)`-per-unit-shift) digamma shift bound -/

/--
Input/assumptions: `z : ℂ` with `z.im ≠ 0`, `n : ℕ`.
Conclusion: `‖digamma (z + n) - digamma z‖ ≤ n / |z.im|`.
Content: induction on `n` via `digamma_apply_add_one`; each step contributes a correction term
`(z + k)⁻¹` with `‖(z + k)⁻¹‖ ≤ 1 / |z.im|` (since `‖z + k‖ ≥ |(z + k).im| = |z.im|`), so the
triangle inequality accumulates `n` terms of size `1 / |z.im|` each — unlike
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_digamma_le_shift_nat_add`'s `2 * m`
(which bounds each correction term by the *constant* `2`,
requiring `|z.im| ≥ 1/2`), this scales the *shift itself* by `1/|z.im|`, giving an `O(1)` bound
when `n ≍ |z.im|`.
Role: the left-vertical step ingredient — combined with a variable radius `R ≍ |t|`
(`norm_digamma_le_of_logGamma_ball_bound`) and a shift `n ≍ |t|` that pushes `Re (z + n) ≍ |t|`
into the region where `log Γ` is polynomially bounded, this keeps the shift cost `O(1)` instead of
`O(|t|)`, which is what turns the final digamma bound sublinear.
-/
theorem norm_digamma_sub_shift_nat_le {z : ℂ} (n : ℕ) (hz : z.im ≠ 0) :
    ‖Complex.digamma (z + n) - Complex.digamma z‖ ≤ n / |z.im| := by
  have hzabs_pos : (0 : ℝ) < |z.im| := abs_pos.mpr hz
  induction n with
  | zero => simp only [CharP.cast_eq_zero, add_zero, sub_self, norm_zero, zero_div, Std.le_refl]
  | succ n
    ih =>
    have hzn_im : (z + (n : ℂ)).im = z.im := by
      simp only [Complex.add_im, Complex.natCast_im, add_zero]
    have hzm : ∀ m : ℕ, z ≠ -(m : ℂ) := ne_neg_nat_of_im_ne_zero hz
    have hzn_ne : ∀ m : ℕ, z + (n : ℂ) ≠ -(m : ℂ) := by
      intro m h
      apply hzm (m + n)
      push_cast
      linear_combination h
    have hrec :
      Complex.digamma (z + (n : ℂ) + 1) = Complex.digamma (z + (n : ℂ)) + (z + (n : ℂ))⁻¹ :=
      Complex.digamma_apply_add_one (z + (n : ℂ)) hzn_ne
    have heq : z + ((n : ℕ) + 1 : ℕ) = z + (n : ℂ) + 1 := by
      push_cast; ring
    have hnorm_ge : |z.im| ≤ ‖z + (n : ℂ)‖ := by
      have h := Complex.abs_im_le_norm (z + (n : ℂ))
      rwa [hzn_im] at h
    have hinv_le : ‖(z + (n : ℂ))⁻¹‖ ≤ 1 / |z.im| := by
      rw [norm_inv, inv_eq_one_div]
      exact div_le_div_of_nonneg_left (by norm_num only) hzabs_pos hnorm_ge
    have hrearrange :
      (Complex.digamma (z + (n : ℂ)) + (z + (n : ℂ))⁻¹) - Complex.digamma z =
        (Complex.digamma (z + (n : ℂ)) - Complex.digamma z) + (z + (n : ℂ))⁻¹ := by
      ring
    calc
      ‖Complex.digamma (z + ((n : ℕ) + 1 : ℕ)) - Complex.digamma z‖ =
          ‖(Complex.digamma (z + (n : ℂ)) - Complex.digamma z) + (z + (n : ℂ))⁻¹‖ :=
        by rw [heq, hrec, hrearrange]
      _ ≤ ‖Complex.digamma (z + (n : ℂ)) - Complex.digamma z‖ + ‖(z + (n : ℂ))⁻¹‖ := norm_add_le _ _
      _ ≤ (n : ℝ) / |z.im| + 1 / |z.im| := by linarith [ih, hinv_le]
      _ = ((n : ℕ) + 1 : ℕ) / |z.im| := by
        push_cast; ring

/-! ### the left-vertical step: a real-part-separated digamma shift bound (covers `Im z = 0`) -/

/--
Input/assumptions: `z : ℂ`, `n : ℕ`, `δ > 0`; for every `k < n`, `z + k` avoids every nonpositive
integer pole (`hpole`) and has `|Re (z + k)| ≥ δ` (`hsep`).
Conclusion: `‖digamma (z + n) - digamma z‖ ≤ n / δ`.
Content: the real-part analogue of `norm_digamma_sub_shift_nat_le` — same induction via
`digamma_apply_add_one`, but bounding `‖(z + k)⁻¹‖ ≤ 1/δ` via `Complex.abs_re_le_norm` instead of
`Complex.abs_im_le_norm`. Unlike the imaginary-part version (whose single hypothesis `z.im ≠ 0`
automatically rules out every pole for every shift), pole-avoidance here isn't implied by the real
part separation alone, so it is a separate explicit hypothesis. Proved by strengthening to `∀ j ≤
n` on a fresh induction variable `j`, since `hpole`/`hsep` already mention the fixed `n`.
Role: the left-vertical step shift ingredient that (unlike `norm_digamma_sub_shift_nat_le`)
covers `Im z = 0`, needed for the left-vertical line's `t = 0` point.
-/
theorem norm_digamma_sub_shift_nat_le_of_re_sep {z : ℂ} (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hpole : ∀ k < n, ∀ m : ℕ, z + (k : ℂ) ≠ -(m : ℂ)) (hsep : ∀ k < n, δ ≤ |(z + (k : ℂ)).re|) :
    ‖Complex.digamma (z + n) - Complex.digamma z‖ ≤ n / δ := by
  have main : ∀ j : ℕ, j ≤ n → ‖Complex.digamma (z + j) - Complex.digamma z‖ ≤ j / δ := by
    intro j
    induction j with
    | zero =>
      intro _; simp only [CharP.cast_eq_zero, add_zero, sub_self, norm_zero, zero_div, Std.le_refl]
    | succ j ih =>
      intro hjn
      have ihbound := ih (by omega)
      have hzj_ne : ∀ m : ℕ, z + (j : ℂ) ≠ -(m : ℂ) := hpole j (by omega)
      have hrec :
        Complex.digamma (z + (j : ℂ) + 1) = Complex.digamma (z + (j : ℂ)) + (z + (j : ℂ))⁻¹ :=
        Complex.digamma_apply_add_one (z + (j : ℂ)) hzj_ne
      have heq : z + ((j : ℕ) + 1 : ℕ) = z + (j : ℂ) + 1 := by
        push_cast; ring
      have hre_sep_j : δ ≤ |(z + (j : ℂ)).re| := hsep j (by omega)
      have hnorm_ge : δ ≤ ‖z + (j : ℂ)‖ := le_trans hre_sep_j (Complex.abs_re_le_norm _)
      have hinv_le : ‖(z + (j : ℂ))⁻¹‖ ≤ 1 / δ := by
        rw [norm_inv, inv_eq_one_div]
        exact div_le_div_of_nonneg_left (by norm_num only) hδ hnorm_ge
      have hrearrange :
        (Complex.digamma (z + (j : ℂ)) + (z + (j : ℂ))⁻¹) - Complex.digamma z =
          (Complex.digamma (z + (j : ℂ)) - Complex.digamma z) + (z + (j : ℂ))⁻¹ := by
        ring
      calc
        ‖Complex.digamma (z + ((j : ℕ) + 1 : ℕ)) - Complex.digamma z‖ =
            ‖(Complex.digamma (z + (j : ℂ)) - Complex.digamma z) + (z + (j : ℂ))⁻¹‖ :=
          by rw [heq, hrec, hrearrange]
        _ ≤ ‖Complex.digamma (z + (j : ℂ)) - Complex.digamma z‖ + ‖(z + (j : ℂ))⁻¹‖ :=
          norm_add_le _ _
        _ ≤ (j : ℝ) / δ + 1 / δ := by linarith [ihbound, hinv_le]
        _ = ((j : ℕ) + 1 : ℕ) / δ := by
          push_cast; ring
  exact main n le_rfl

/-- Absorb the large-imaginary-part constants with only real inequalities in context. -/
private theorem largeIm_absorb {M L L₂ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hLL : L ≤ L₂) :
    (67 + 32 * M + 80 * Real.pi + 64 * L) + 2 ≤
      (69 + 80 * Real.pi + 32 * M + 64 + 10) * (1 + L₂) := by
  nlinarith only [hM, hL, hLL, Real.pi_pos]

/-- The ball estimate's rational bound, separated from complex geometry. -/
private theorem largeIm_ball_algebra {T V C : ℝ} (hT : 12 ≤ T)
    (hV : V ≤ 2 * T + 2 * T * Real.log T) :
    32 * (V + 1 + C + 5 * Real.pi * T / 2) / T ≤
      67 + 32 * max C 0 + 80 * Real.pi + 64 * Real.log T := by
  have hkey : 0 ≤ 32 * max C 0 * T - 32 * C := by
    have hm : 0 ≤ max C 0 := le_max_right _ _
    nlinarith only [le_max_left C 0,
      mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ T by linarith only [hT]) hm]
  rw [div_le_iff₀ (by linarith only [hT] : 0 < T)]
  nlinarith only [hV, hkey, hT, Real.pi_pos]

/-! ### the left-vertical step: `O(log |t|)` digamma bound for large `|t|`, fixed real part -/

/--
Input/assumptions: none (existence statement).
Conclusion: there is `C ≥ 0`, independent of `a`, such that for every `a t : ℝ` with
`4 * (|a| + 3) ≤ |t|`, `‖digamma (a + t i)‖ ≤ C * (1 + log (|t| + 2))`.
Content: shifts `z := a + t i` by `m := ⌈|a| + |t|⌉₊` to `c := z + m` (`c.re ≍ |t|`), applies
`norm_digamma_le_of_logGamma_ball_bound` on `ball c (|t|/8)` — the upper bound `U` on `log ‖Γ‖`
over the ball comes from `PseudoPrime.AnalyticNumberTheory.Gamma.log_Gamma_le_of_one_le`
at the ball's rightmost point `X ≍ |t|`
(`PseudoPrime.AnalyticNumberTheory.RiemannZeta.Real.Gamma_le_max_of_mem_Icc'` plus
`Real.Gamma_strictMonoOn_Ici` to see `Γ 1 ≤ Γ X`), and the
center lower bound from `PseudoPrime.AnalyticNumberTheory.RiemannZeta.`
`exists_neg_log_norm_Gamma_one_add_add_mul_I_le_uniform` — giving
`‖digamma c‖ = O(log |t|)`; then undoes the shift via `norm_digamma_sub_shift_nat_le`
(`≤ m / |t| = O(1)` since `m ≍ |a| + |t|` and the hypothesis `|t| ≥ 4(|a| + 3)` keeps `|a|` from
dominating). The witness `C` never mentions `a`, so it is pulled outside the `∀ a` — this matters
because the eventual `A → ∞` limit needs a single constant, not an opaque per-`A` one.
Role: the left-vertical step large-`|t|` half of the left-vertical digamma bound
(paired with a small-`|t|` finite bound handling `A`-dependence explicitly).
-/
theorem exists_C_forall_norm_digamma_large_im_le :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ a t : ℝ,
          4 * (|a| + 3) ≤ |t| →
            ‖Complex.digamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 + Real.log (|t| + 2)) := by
  obtain ⟨C₁, hC₁⟩ := RiemannZeta.exists_neg_log_norm_Gamma_one_add_add_mul_I_le_uniform
  set C : ℝ := 69 + 80 * Real.pi + 32 * max C₁ 0 + 64 + 10 with hC_def
  have hCnonneg : 0 ≤ C := by
    have h1 : (0 : ℝ) ≤ max C₁ 0 := le_max_right _ _
    nlinarith only [Real.pi_pos, h1]
  refine ⟨C, hCnonneg, fun a t h4B3 => ?_⟩
  set B : ℝ := |a| with hB_def
  have hBnn : 0 ≤ B := abs_nonneg a
  have htabs_pos : (0 : ℝ) < |t| := by linarith only [h4B3, hBnn]
  have ht12 : (12 : ℝ) ≤ |t| := by linarith only [h4B3, hBnn]
  set z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I with hz_def
  set m : ℕ := ⌈B + |t|⌉₊ with hm_def
  have hm_ge : B + |t| ≤ (m : ℝ) := Nat.le_ceil _
  have hm_lt : (m : ℝ) < B + |t| + 1 := Nat.ceil_lt_add_one (by linarith only [hBnn, htabs_pos])
  set c : ℂ := z + (m : ℂ) with hc_def
  have hcre : c.re = a + m := by
    simp only [hc_def, hz_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.natCast_re]
  have hcim : c.im = t := by
    simp only [hc_def, hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.natCast_im]
  have ha_ge : -B ≤ a := neg_abs_le a
  have ha_le : a ≤ B := le_abs_self a
  have hcre_ge : |t| ≤ c.re := by
    rw [hcre]; linarith only [hm_ge, ha_ge]
  have hcre_le : c.re ≤ 2 * B + |t| + 1 := by
    rw [hcre]; linarith only [hm_lt, ha_le]
  set R : ℝ := |t| / 8 with hR_def
  have hR_pos : 0 < R := by
    rw [hR_def]; linarith only [htabs_pos]
  have hball_re_lower : ∀ w ∈ Metric.ball c R, 7 * |t| / 8 < w.re := by
    intro w hw
    have hd : ‖w - c‖ < R := by simpa only [Metric.mem_ball, Complex.dist_eq] using hw
    have h1 := Complex.abs_re_le_norm (w - c)
    rw [Complex.sub_re] at h1
    have h2 : |w.re - c.re| < R := lt_of_le_of_lt h1 hd
    have h3 := (abs_lt.mp h2).1
    rw [hR_def] at h3
    linarith only [h3, hcre_ge]
  have hball : ∀ w ∈ Metric.ball c R, 0 < w.re := fun w hw => by
    have := hball_re_lower w hw; linarith only [this, htabs_pos]
  have hball_re1 : ∀ w ∈ Metric.ball c R, 1 ≤ w.re := fun w hw => by
    have := hball_re_lower w hw; linarith only [this, ht12]
  set X : ℝ := 2 * B + 2 + (9 / 8) * |t| with hX_def
  have hX1 : (1 : ℝ) ≤ X := by
    rw [hX_def]; linarith only [hBnn, htabs_pos]
  have hX2 : (2 : ℝ) ≤ X := by
    rw [hX_def]; linarith only [hBnn, htabs_pos]
  have hXub : X ≤ 2 * |t| := by
    rw [hX_def]; nlinarith only [h4B3, hBnn]
  have hupper1 : ∀ w ∈ Metric.ball c R, w.re ≤ X := by
    intro w hw
    have hd : ‖w - c‖ < R := by simpa only [Metric.mem_ball, Complex.dist_eq] using hw
    have h1 := Complex.abs_re_le_norm (w - c)
    rw [Complex.sub_re] at h1
    have h2 : |w.re - c.re| < R := lt_of_le_of_lt h1 hd
    have h3 := (abs_lt.mp h2).2
    rw [hR_def] at h3
    rw [hX_def]; linarith only [h3, hcre_le]
  have hΓX_ge1 : (1 : ℝ) ≤ Real.Gamma X := by
    rw [← Real.Gamma_two]
    exact Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hX2) hX2
  have hupper_logGamma : ∀ w ∈ Metric.ball c R, Real.log ‖Complex.Gamma w‖ ≤ X * Real.log X := by
    intro w hw
    have hwre_pos := hball w hw
    have hwre_le := hupper1 w hw
    have hwre_ge1 := hball_re1 w hw
    have h1 : Real.Gamma w.re ≤ max (Real.Gamma 1) (Real.Gamma X) :=
      RiemannZeta.Real.Gamma_le_max_of_mem_Icc' (by norm_num only) hX1 ⟨hwre_ge1, hwre_le⟩
    have hmax_eq : max (Real.Gamma 1) (Real.Gamma X) = Real.Gamma X := by
      rw [Real.Gamma_one]; exact max_eq_right hΓX_ge1
    rw [hmax_eq] at h1
    calc
      Real.log ‖Complex.Gamma w‖ ≤ Real.log (Real.Gamma w.re) :=
        Real.log_le_log (norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hwre_pos))
          (RiemannZeta.norm_Gamma_le_Gamma_re hwre_pos)
      _ ≤ Real.log (Real.Gamma X) :=
        Real.log_le_log (Real.Gamma_pos_of_pos (by linarith only [hwre_pos])) h1
      _ ≤ X * Real.log X := Gamma.log_Gamma_le_of_one_le hX1
  set U : ℝ := X * Real.log X + 1 with hU_def
  have hccenter : c ∈ Metric.ball c R := Metric.mem_ball_self hR_pos
  have hMpos : Real.log ‖Complex.Gamma c‖ < U := by
    have := hupper_logGamma c hccenter; rw [hU_def]; linarith only [this]
  have hupper : ∀ w ∈ Metric.ball c R, Real.log ‖Complex.Gamma w‖ ≤ U := fun w hw => by
    have := hupper_logGamma w hw; rw [hU_def]; linarith only [this]
  have hdigamma_c := norm_digamma_le_of_logGamma_ball_bound hR_pos hball hMpos hupper
  set r : ℝ := c.re - 1 with hr_def
  have hr0 : 0 ≤ r := by
    rw [hr_def]; linarith only [hcre_ge, ht12]
  have hcform : c = (1 : ℂ) + (r : ℂ) + (t : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [hr_def, Complex.ofReal_sub, Complex.ofReal_one, add_sub_cancel, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
        mul_one, sub_self, add_zero]
    · simp only [← hcim, Complex.add_im, Complex.one_im, Complex.ofReal_im, add_zero,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, zero_add]
  have hneg_log_le := hC₁ r t hr0
  rw [← hcform] at hneg_log_le
  have hlogΓc_ge : -(C₁ + 5 * Real.pi * |t| / 2) ≤ Real.log ‖Complex.Gamma c‖ := by
    linarith only [hneg_log_le]
  have hUmc : U - Real.log ‖Complex.Gamma c‖ ≤ X * Real.log X + 1 + C₁ + 5 * Real.pi * |t| / 2 := by
    rw [hU_def]; linarith only [hlogΓc_ge]
  have hXlogX_le : X * Real.log X ≤ (2 * |t|) * Real.log (2 * |t|) :=
    Gamma.mul_log_mono_of_one_le hX1 hXub
  have h2t_ge1 : (1 : ℝ) ≤ 2 * |t| := by linarith only [ht12]
  have hlog2t : Real.log (2 * |t|) = Real.log 2 + Real.log |t| := by
    rw [Real.log_mul (by norm_num only) (by linarith only [htabs_pos])]
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num only); linarith only [this]
  have hlogt_nonneg : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith only [ht12])
  have hXlogXfinal : X * Real.log X ≤ 2 * |t| + 2 * |t| * Real.log |t| := by
    calc
      X * Real.log X ≤ (2 * |t|) * Real.log (2 * |t|) := hXlogX_le
      _ = (2 * |t|) * (Real.log 2 + Real.log |t|) := by rw [hlog2t]
      _ ≤ (2 * |t|) * (1 + Real.log |t|) := by
        apply
          mul_le_mul_of_nonneg_left (by linarith only [hlog2_le1]) (by linarith only [htabs_pos])
      _ = 2 * |t| + 2 * |t| * Real.log |t| := by ring
  have hReq :
    (4 : ℝ) * (U - Real.log ‖Complex.Gamma c‖) / R =
      32 * (U - Real.log ‖Complex.Gamma c‖) / |t| := by
    rw [hR_def]; field_simp; ring
  rw [hReq] at hdigamma_c
  have hC1nn : C₁ ≤ max C₁ 0 := le_max_left _ _
  have hfinal_c : ‖Complex.digamma c‖ ≤ 67 + 32 * max C₁ 0 + 80 * Real.pi + 64 * Real.log |t| := by
    have hstep :
      32 * (U - Real.log ‖Complex.Gamma c‖) / |t| ≤
        32 * (X * Real.log X + 1 + C₁ + 5 * Real.pi * |t| / 2) / |t| := by
      apply div_le_div_of_nonneg_right _ (le_of_lt htabs_pos)
      linarith only [hUmc]
    have hstep2 := largeIm_ball_algebra ht12 hXlogXfinal (C := C₁)
    calc
      ‖Complex.digamma c‖ ≤ 32 * (U - Real.log ‖Complex.Gamma c‖) / |t| := hdigamma_c
      _ ≤ 32 * (X * Real.log X + 1 + C₁ + 5 * Real.pi * |t| / 2) / |t| := hstep
      _ ≤ 67 + 32 * max C₁ 0 + 80 * Real.pi + 64 * Real.log |t| := hstep2
  have hzim : z.im = t := by
    simp only [hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hzim_ne : z.im ≠ 0 := by
    rw [hzim]; exact abs_pos.mp htabs_pos
  have hshift : ‖Complex.digamma c - Complex.digamma z‖ ≤ (m : ℝ) / |t| := by
    have hb := norm_digamma_sub_shift_nat_le m hzim_ne
    rw [hzim] at hb
    rwa [hc_def]
  have hshift_le : (m : ℝ) / |t| ≤ 2 := by
    rw [div_le_iff₀ htabs_pos]
    nlinarith only [hm_lt.le, h4B3, hBnn]
  have htri :
    ‖Complex.digamma z‖ ≤ ‖Complex.digamma c‖ + ‖Complex.digamma c - Complex.digamma z‖ := by
    have heq : Complex.digamma z = Complex.digamma c - (Complex.digamma c - Complex.digamma z) := by
      ring
    calc
      ‖Complex.digamma z‖ = ‖Complex.digamma c - (Complex.digamma c - Complex.digamma z)‖ := by
        rw [← heq]
      _ ≤ ‖Complex.digamma c‖ + ‖Complex.digamma c - Complex.digamma z‖ := norm_sub_le _ _
  have hlogt2_ge : Real.log |t| ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by linarith only [htabs_pos]) (by linarith only [])
  have hMnn : (0 : ℝ) ≤ max C₁ 0 := le_max_right _ _
  calc
    ‖Complex.digamma z‖ ≤ ‖Complex.digamma c‖ + ‖Complex.digamma c - Complex.digamma z‖ := htri
    _ ≤ (67 + 32 * max C₁ 0 + 80 * Real.pi + 64 * Real.log |t|) + 2 := by
      linarith only [hfinal_c, hshift, hshift_le]
    _ ≤ C * (1 + Real.log (|t| + 2)) := by
      rw [hC_def]
      exact largeIm_absorb hMnn hlogt_nonneg hlogt2_ge

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
