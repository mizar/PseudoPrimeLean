/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorLogDeriv
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.Growth

/-!
# Central-strip growth of the gamma-factor log-derivative

Growth estimates for `Complex.digamma` and `DirichletCharacter.gammaFactor` on the central strip
`-1 ≤ Re z ≤ 3/2`, kept separate from the exact log-derivative identities in `GammaFactorLogDeriv`.
Both parities' digamma argument (`s/2` even, `(s+1)/2` odd) lands in this strip once
`|Re s| ≤ 2`, so a single central digamma bound theorem covers both.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- A point off the real axis is never a nonpositive integer. -/
theorem ne_neg_nat_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) (m : ℕ) : w ≠ -(m : ℂ) := by
  intro hm
  apply hw
  have h1 : w.im = (-(m : ℂ)).im := congrArg Complex.im hm
  simpa only [Complex.neg_im, Complex.natCast_im, neg_zero] using h1

/--
Input/assumptions: `z : ℂ` with `1/2 ≤ |z.im|`.
Conclusion: `‖digamma z‖ ≤ ‖digamma (z + 2)‖ + 4`.
Content: two applications of `digamma_apply_add_one` give
`digamma z = digamma (z + 2) - z⁻¹ - (z + 1)⁻¹`; since `|z|, |z + 1| ≥ |z.im| ≥ 1/2`,
`‖z⁻¹‖, ‖(z + 1)⁻¹‖ ≤ 2`, so the triangle inequality gives the `+ 4` slack.
Role: isolates the "undo a shift by 2" step so it is shared by both parities' central-strip bound.
-/
theorem norm_digamma_le_shift_two_add_four {z : ℂ} (hz : (1 : ℝ) / 2 ≤ |z.im|) :
    ‖Complex.digamma z‖ ≤ ‖Complex.digamma (z + 2)‖ + 4 := by
  have hzim_ne : z.im ≠ 0 := abs_pos.mp (by linarith)
  have hz1im_ne : (z + 1).im ≠ 0 := by
    simpa only [Complex.add_im, Complex.one_im, add_zero, ne_eq] using hzim_ne
  have hzm : ∀ m : ℕ, z ≠ -(m : ℂ) := ne_neg_nat_of_im_ne_zero hzim_ne
  have hz1m : ∀ m : ℕ, z + 1 ≠ -(m : ℂ) := ne_neg_nat_of_im_ne_zero hz1im_ne
  have hrec1 : Complex.digamma (z + 1) = Complex.digamma z + z⁻¹ :=
    Complex.digamma_apply_add_one z hzm
  have hrec2 : Complex.digamma (z + 1 + 1) = Complex.digamma (z + 1) + (z + 1)⁻¹ :=
    Complex.digamma_apply_add_one (z + 1) hz1m
  have hz2eq : z + 1 + 1 = z + 2 := by ring
  rw [hz2eq] at hrec2
  have hz_eq : Complex.digamma z = Complex.digamma (z + 2) - z⁻¹ - (z + 1)⁻¹ := by
    rw [hrec2, hrec1]; ring
  have hznorm : (1 : ℝ) / 2 ≤ ‖z‖ := hz.trans (Complex.abs_im_le_norm z)
  have hz1norm : (1 : ℝ) / 2 ≤ ‖z + 1‖ := by
    have h1 : |(z + 1).im| ≤ ‖z + 1‖ := Complex.abs_im_le_norm (z + 1)
    have h2 : (z + 1).im = z.im := by simp only [Complex.add_im, Complex.one_im, add_zero]
    rw [h2] at h1
    linarith
  have hzinv_le : ‖z⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    calc
      ‖z‖⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ := inv_anti₀ (by norm_num only) hznorm
      _ = 2 := by norm_num only
  have hz1inv_le : ‖(z + 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    calc
      ‖z + 1‖⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ := inv_anti₀ (by norm_num only) hz1norm
      _ = 2 := by norm_num only
  rw [hz_eq]
  calc
    ‖Complex.digamma (z + 2) - z⁻¹ - (z + 1)⁻¹‖ ≤ ‖Complex.digamma (z + 2) - z⁻¹‖ + ‖(z + 1)⁻¹‖ :=
      norm_sub_le _ _
    _ ≤ (‖Complex.digamma (z + 2)‖ + ‖z⁻¹‖) + ‖(z + 1)⁻¹‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ‖Complex.digamma (z + 2)‖ + 4 := by
      calc
        (‖Complex.digamma (z + 2)‖ + ‖z⁻¹‖) + ‖(z + 1)⁻¹‖ ≤ (‖Complex.digamma (z + 2)‖ + 2) + 2 :=
          add_le_add (add_le_add (le_refl _) hzinv_le) hz1inv_le
        _ = ‖Complex.digamma (z + 2)‖ + 4 := by ring

/--
Input/assumptions: none (existence statement).
Conclusion: there is a fixed `C ≥ 0` such that `‖digamma z‖ ≤ C * (|z.im| + 1)` for every `z` with
`-1 ≤ z.re ≤ 3/2` and `|z.im| ≥ 1/2`.
Content: shifts to `z + 2` (real part in `[1, 7/2]`, matching
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_digamma_shift_add_mul_I_le`'s
`1 + r` shape with `r := z.re + 1 ∈ [0, 5/2]`), bounds the two real `Gamma` values there by a fixed
constant `M_Γ := max Γ(1/2) Γ(4)` (both `r + 1/2, r + 3/2 ∈ [1/2, 4]`, via
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.Real.Gamma_le_max_of_mem_Icc'`) and the
`-log‖Γ(1+r+it)‖` term by
`RiemannZeta.exists_neg_log_norm_Gamma_one_add_add_mul_I_le_uniform`'s
`O(t)` bound, then undoes the shift via
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_digamma_le_shift_two_add_four`.
Role: the pointwise central-strip ingredient, applied at `z := s/2` or `z := (s+1)/2` to bound
`logDeriv (gammaFactor χ)` on the horizontal strip.
-/
theorem exists_norm_digamma_central_strip_le :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ z : ℂ,
          -1 ≤ z.re →
            z.re ≤ 3 / 2 → (1 : ℝ) / 2 ≤ |z.im| → ‖Complex.digamma z‖ ≤ C * (|z.im| + 1) := by
  obtain ⟨C₁, hC₁⟩ := RiemannZeta.exists_neg_log_norm_Gamma_one_add_add_mul_I_le_uniform
  set MΓ := max (Real.Gamma (1 / 2)) (Real.Gamma 4) with hMΓ_def
  have hMΓpos : 0 < MΓ := lt_max_of_lt_left (Real.Gamma_pos_of_pos (by norm_num only))
  set C : ℝ := 8 * Real.log (MΓ + 1) + 8 * max C₁ 0 + 4 + 20 * Real.pi with hC_def
  have hC₁_le : C₁ ≤ max C₁ 0 := le_max_left _ _
  have hCnonneg : 0 ≤ C := by
    have hlogMΓ1_nonneg : 0 ≤ Real.log (MΓ + 1) := Real.log_nonneg (by linarith)
    have hmax_nonneg : (0 : ℝ) ≤ max C₁ 0 := le_max_right _ _
    linarith only [Real.pi_pos, hlogMΓ1_nonneg, hmax_nonneg]
  refine ⟨C, hCnonneg, fun z hzre1 hzre2 hzim => ?_⟩
  set t' := z.im with ht'_def
  have ht'pos : (0 : ℝ) < |t'| := by linarith
  set r := z.re + 1 with hr_def
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hzr : (1 + r : ℝ) + (t' : ℂ) * Complex.I = z + 2 := by
    apply Complex.ext
    · simp only [hr_def, Complex.ofReal_add, Complex.ofReal_one, Complex.add_re, Complex.one_re,
        Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
        mul_one, sub_self, add_zero, Complex.re_ofNat]
      ring
    · simp only [Complex.ofReal_add, Complex.ofReal_one, ht'_def, Complex.add_im, Complex.one_im,
        Complex.ofReal_im, add_zero, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.I_re, mul_zero, zero_add, Complex.im_ofNat]
  have hshift := RiemannZeta.norm_digamma_shift_add_mul_I_le r hr0 t'
  have hr12 : r + 1 / 2 ∈ Set.Icc (1 / 2 : ℝ) 4 := ⟨by linarith, by linarith⟩
  have hr32 : r + 3 / 2 ∈ Set.Icc (1 / 2 : ℝ) 4 := ⟨by linarith, by linarith⟩
  have hΓ12 : Real.Gamma (r + 1 / 2) ≤ MΓ :=
    RiemannZeta.Real.Gamma_le_max_of_mem_Icc' (by norm_num only) (by norm_num only) hr12
  have hΓ32 : Real.Gamma (r + 3 / 2) ≤ MΓ :=
    RiemannZeta.Real.Gamma_le_max_of_mem_Icc' (by norm_num only) (by norm_num only) hr32
  have hlog_le :
    Real.log (max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) + 1) ≤ Real.log (MΓ + 1) := by
    apply Real.log_le_log (by positivity)
    linarith [max_le hΓ12 hΓ32]
  have hcast : (1 + r : ℝ) + (t' : ℂ) * Complex.I = 1 + (r : ℂ) + (t' : ℂ) * Complex.I := by
    push_cast; ring
  have hneg_log_le := hC₁ r t' hr0
  rw [← hcast] at hneg_log_le
  have hdigamma_shift_le' :
    ‖Complex.digamma ((1 + r : ℝ) + (t' : ℂ) * Complex.I)‖ ≤
      8 * Real.log (MΓ + 1) + 8 * C₁ + 20 * Real.pi * |t'| := by
    have h1 :
      (8 : ℝ) *
          (Real.log (max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) + 1) -
            Real.log ‖Complex.Gamma ((1 + r : ℝ) + (t' : ℂ) * Complex.I)‖) ≤
        8 * Real.log (MΓ + 1) + 8 * C₁ + 20 * Real.pi * |t'| := by
      linarith only [hlog_le, hneg_log_le]
    exact hshift.trans h1
  have hdigamma_shift_le :
    ‖Complex.digamma (z + 2)‖ ≤ 8 * Real.log (MΓ + 1) + 8 * C₁ + 20 * Real.pi * |t'| := by
    rw [← hzr]; exact hdigamma_shift_le'
  have hshift4 : ‖Complex.digamma z‖ ≤ ‖Complex.digamma (z + 2)‖ + 4 :=
    norm_digamma_le_shift_two_add_four hzim
  have hlogMΓ1_nonneg : 0 ≤ Real.log (MΓ + 1) := Real.log_nonneg (by linarith)
  have hmax_nonneg : (0 : ℝ) ≤ max C₁ 0 := le_max_right _ _
  have hprod_nonneg : (0 : ℝ) ≤ (8 * Real.log (MΓ + 1) + 8 * max C₁ 0 + 4 + 20 * Real.pi) * |t'| :=
    mul_nonneg (by linarith [Real.pi_pos]) (le_of_lt ht'pos)
  calc
    ‖Complex.digamma z‖ ≤ ‖Complex.digamma (z + 2)‖ + 4 := hshift4
    _ ≤ (8 * Real.log (MΓ + 1) + 8 * C₁ + 20 * Real.pi * |t'|) + 4 := by linarith
    _ ≤ C * (|t'| + 1) := by
      rw [hC_def]
      nlinarith only [hC₁_le, hlogMΓ1_nonneg, hmax_nonneg, hprod_nonneg, Real.pi_pos]

/--
Input/assumptions: `χ : DirichletCharacter ℂ N` (any modulus, either parity).
Conclusion: there is a fixed `C ≥ 0`, independent of `χ`'s modulus (depending only on parity, and
`max`-ed over both), such that for every `σ T : ℝ` with `|σ| ≤ 2` and `1 ≤ |T|`,
`‖logDeriv (gammaFactor χ) (σ + T * I)‖ ≤ C * (|T| + 1)`.
Content: splits on `χ.even_or_odd`, rewrites `logDeriv (gammaFactor χ) s` via
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.logDeriv_gammaFactor_eq_of_even`/`_odd` as
`-log π / 2 + digamma z / 2` with `z := s / 2`
(even) or `z := (s + 1) / 2` (odd); in both cases `z.re ∈ [-1, 3 / 2]` from `|σ| ≤ 2` and
`z.im = T / 2`, so `|z.im| ≥ 1 / 2` from `|T| ≥ 1`. Bounds `digamma z` via
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.exists_norm_digamma_central_strip_le` and
combines with the constant `log π` term.
Role: the character-level central-strip gamma-factor bound feeding the ordinary
`L'/L` height-sequence envelope, combined with
`exists_primitiveHorizontalHeightSeq_completedLogDeriv_small`.
-/
theorem exists_norm_logDeriv_gammaFactor_horizontal_le :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (σ T : ℝ),
          |σ| ≤ 2 →
            1 ≤ |T| →
            ‖logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
              C * (|T| + 1) := by
  obtain ⟨C₀, hC₀nonneg, hC₀⟩ := exists_norm_digamma_central_strip_le
  set C : ℝ := |Real.log Real.pi| / 2 + C₀ / 2 with hC_def
  have hCnonneg : 0 ≤ C := by
    have h1 : (0 : ℝ) ≤ |Real.log Real.pi| := abs_nonneg _
    rw [hC_def]; linarith
  refine ⟨C, hCnonneg, fun χ σ T hσ hT => ?_⟩
  set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I with hs_def
  have hsim : s.im = T := by
    simp only [hs_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hsim_ne : s.im ≠ 0 := by
    rw [hsim]; intro h; rw [h] at hT; norm_num only at hT
  have hlogpi_norm : ‖(-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)‖ = |Real.log Real.pi| / 2 := by
    have h1 : (-(Complex.log (Real.pi : ℂ)) / 2 : ℂ) = ((-(Real.log Real.pi) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_log Real.pi_pos.le]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_div]
    rw [abs_neg]
    norm_num only
  have hmain :
    ∀ a b : ℝ,
      -1 ≤ a →
        a ≤ 3 / 2 →
        b = T / 2 →
        ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((a : ℂ) + (b : ℂ) * Complex.I) / 2 :
              ℂ)‖ ≤
          C * (|T| + 1) := by
    intro a b ha1 ha2 hb
    set z : ℂ := (a : ℂ) + (b : ℂ) * Complex.I with hz_def
    have hzre : z.re = a := by
      simp only [hz_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    have hzim : z.im = b := by
      simp only [hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    have hzim_abs : (1 : ℝ) / 2 ≤ |z.im| := by
      rw [hzim, hb, abs_div]
      have h2 : |(2 : ℝ)| = 2 := by norm_num only
      rw [h2]; linarith [hT]
    have hdb :=
      hC₀ z
        (by
          rw [hzre]; exact ha1)
        (by
          rw [hzre]; exact ha2)
        hzim_abs
    rw [hzim, hb] at hdb
    have habs2 : |T / 2| = |T| / 2 := by
      rw [abs_div]; norm_num only
    rw [habs2] at hdb
    calc
      ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma z / 2 : ℂ)‖ ≤
          ‖(-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)‖ + ‖(Complex.digamma z / 2 : ℂ)‖ :=
        norm_add_le _ _
      _ = |Real.log Real.pi| / 2 + ‖Complex.digamma z‖ / 2 := by
        rw [hlogpi_norm, norm_div, Complex.norm_two]
      _ ≤ |Real.log Real.pi| / 2 + C₀ * (|T| / 2 + 1) / 2 := by gcongr
      _ ≤ C * (|T| + 1) := by
        rw [hC_def]
        nlinarith [hC₀nonneg, abs_nonneg T,
          mul_nonneg (abs_nonneg (Real.log Real.pi)) (abs_nonneg T),
          mul_nonneg hC₀nonneg (abs_nonneg T)]
  rcases χ.even_or_odd with heven | hodd
  · have hform : s / 2 = ((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hs_def]; push_cast; ring
    rw [logDeriv_gammaFactor_eq_of_even heven hsim_ne, hform]
    exact hmain (σ / 2) (T / 2) (by linarith [abs_le.mp hσ]) (by linarith [abs_le.mp hσ]) rfl
  · have hform : (s + 1) / 2 = (((σ + 1) / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hs_def]; push_cast; ring
    rw [logDeriv_gammaFactor_eq_of_odd hodd hsim_ne, hform]
    exact hmain ((σ + 1) / 2) (T / 2) (by linarith [abs_le.mp hσ]) (by linarith [abs_le.mp hσ]) rfl

/-! ### A digamma bound on an arbitrary strip pushed into `Re ≥ 1` by a fixed shift -/

/--
Input/assumptions: `z : ℂ` with `1/2 ≤ |z.im|`.
Conclusion: `‖digamma z‖ ≤ ‖digamma (z + 1)‖ + 2`.
Content: `digamma_apply_add_one` gives `digamma z = digamma (z + 1) - z⁻¹`; `‖z‖ ≥ |z.im| ≥ 1/2`
gives `‖z⁻¹‖ ≤ 2` via `inv_anti₀`; the triangle inequality gives the `+ 2` slack.
Role: the single-step building block for
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_digamma_le_shift_nat_add`'s iterated
shift.
-/
theorem norm_digamma_le_shift_one_add_two {z : ℂ} (hz : (1 : ℝ) / 2 ≤ |z.im|) :
    ‖Complex.digamma z‖ ≤ ‖Complex.digamma (z + 1)‖ + 2 := by
  have hzim_ne : z.im ≠ 0 := abs_pos.mp (by linarith)
  have hzm : ∀ m : ℕ, z ≠ -(m : ℂ) := ne_neg_nat_of_im_ne_zero hzim_ne
  have hrec : Complex.digamma (z + 1) = Complex.digamma z + z⁻¹ :=
    Complex.digamma_apply_add_one z hzm
  have hz_eq : Complex.digamma z = Complex.digamma (z + 1) - z⁻¹ := by
    rw [hrec]; ring
  have hznorm : (1 : ℝ) / 2 ≤ ‖z‖ := hz.trans (Complex.abs_im_le_norm z)
  have hzinv_le : ‖z⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    calc
      ‖z‖⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ := inv_anti₀ (by norm_num only) hznorm
      _ = 2 := by norm_num only
  rw [hz_eq]
  calc
    ‖Complex.digamma (z + 1) - z⁻¹‖ ≤ ‖Complex.digamma (z + 1)‖ + ‖z⁻¹‖ := norm_sub_le _ _
    _ ≤ ‖Complex.digamma (z + 1)‖ + 2 := by linarith

/--
Input/assumptions: `z : ℂ` with `1/2 ≤ |z.im|`, `m : ℕ`.
Conclusion: `‖digamma z‖ ≤ ‖digamma (z + m)‖ + 2 * m`.
Content: induction on `m` via
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_digamma_le_shift_one_add_two`, using that
`(z + k).im = z.im`
for every `k : ℕ` so the hypothesis `1/2 ≤ |z.im|` transfers unchanged at each step.
Role: generalizes
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_digamma_le_shift_two_add_four` (the fixed
`m = 2` case, up to the constant)
to an arbitrary shift, needed to push a fixed-`A` far-left strip into `Re ≥ 1`.
-/
theorem norm_digamma_le_shift_nat_add {z : ℂ} (hz : (1 : ℝ) / 2 ≤ |z.im|) (m : ℕ) :
    ‖Complex.digamma z‖ ≤ ‖Complex.digamma (z + m)‖ + 2 * m := by
  induction m with
  | zero => simp only [Nat.cast_zero, add_zero, mul_zero, le_refl]
  | succ m
    ih =>
    have hzm_im : (z + (m : ℂ)).im = z.im := by
      simp only [Complex.add_im, Complex.natCast_im, add_zero]
    have hzm_bound : (1 : ℝ) / 2 ≤ |(z + (m : ℂ)).im| := by
      rw [hzm_im]; exact hz
    have hstep := norm_digamma_le_shift_one_add_two hzm_bound
    have heq : z + ((m : ℕ) + 1 : ℕ) = (z + (m : ℂ)) + 1 := by
      push_cast; ring
    calc
      ‖Complex.digamma z‖ ≤ ‖Complex.digamma (z + (m : ℂ))‖ + 2 * m := ih
      _ ≤ (‖Complex.digamma ((z + (m : ℂ)) + 1)‖ + 2) + 2 * m := by linarith [hstep]
      _ = ‖Complex.digamma (z + ((m : ℕ) + 1 : ℕ))‖ + 2 * ((m : ℕ) + 1 : ℕ) := by
        rw [← heq]; push_cast; ring

/--
Input/assumptions: `a b : ℝ` with `a ≤ b`, `m : ℕ` with `1 ≤ a + m`.
Conclusion: there is a fixed `C ≥ 0` such that `‖digamma z‖ ≤ C * (|z.im| + 1)` for every `z` with
`a ≤ z.re ≤ b` and `1/2 ≤ |z.im|`.
Content: generalizes
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.exists_norm_digamma_central_strip_le` (the
case `a = -1, b = 3/2, m = 2`) to
an arbitrary strip pushed into `Re ≥ 1` by a shift `m`: shifts to `z + m` (real part in
`[a + m, b + m] ⊆ [1, ∞)`), bounds the two real `Gamma` values there by
`M_Γ := max Γ(1/2) Γ(b - 1 + m + 3/2)` (via
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.Real.Gamma_le_max_of_mem_Icc'`, using
`r := z.re + m - 1 ∈ [0, b - 1 + m]`) and the `-log‖Γ(1 + r + it)‖` term by
`RiemannZeta.exists_neg_log_norm_Gamma_one_add_add_mul_I_le_uniform`'s
`O(t)` bound, then undoes the shift via
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_digamma_le_shift_nat_add`.
Role: the pointwise digamma ingredient on a fixed but arbitrary strip, feeding the
fixed-`A` gamma factor bound.
-/
theorem exists_norm_digamma_strip_le (a b : ℝ) (hab : a ≤ b) (m : ℕ) (hm : 1 ≤ a + m) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ z : ℂ,
          a ≤ z.re → z.re ≤ b → (1 : ℝ) / 2 ≤ |z.im| → ‖Complex.digamma z‖ ≤ C * (|z.im| + 1) := by
  have hbm : (1 : ℝ) ≤ b + m := le_trans hm (by linarith)
  obtain ⟨C₁, hC₁⟩ := RiemannZeta.exists_neg_log_norm_Gamma_one_add_add_mul_I_le_uniform
  set MΓ := max (Real.Gamma (1 / 2)) (Real.Gamma (b - 1 + m + 3 / 2)) with hMΓ_def
  have hMΓpos : 0 < MΓ := lt_max_of_lt_left (Real.Gamma_pos_of_pos (by norm_num only))
  set C : ℝ := 8 * Real.log (MΓ + 1) + 8 * max C₁ 0 + (4 + 2 * m) + 20 * Real.pi with hC_def
  have hC₁_le : C₁ ≤ max C₁ 0 := le_max_left _ _
  have hCnonneg : 0 ≤ C := by
    have hlogMΓ1_nonneg : 0 ≤ Real.log (MΓ + 1) := Real.log_nonneg (by linarith)
    have hmax_nonneg : (0 : ℝ) ≤ max C₁ 0 := le_max_right _ _
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith only [Real.pi_pos, hlogMΓ1_nonneg, hmax_nonneg, hmnn]
  refine ⟨C, hCnonneg, fun z hzre1 hzre2 hzim => ?_⟩
  set t' := z.im with ht'_def
  have ht'pos : (0 : ℝ) < |t'| := by linarith
  set r := z.re + m - 1 with hr_def
  have hr0 : (0 : ℝ) ≤ r := by
    rw [hr_def]; linarith
  have hrmax : r ≤ b - 1 + m := by
    rw [hr_def]; linarith
  have hzr : (1 + r : ℝ) + (t' : ℂ) * Complex.I = z + m := by
    apply Complex.ext
    · simp only [hr_def, add_sub_cancel, Complex.ofReal_add, Complex.ofReal_natCast, Complex.add_re,
        Complex.ofReal_re, Complex.natCast_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    · simp only [Complex.ofReal_add, Complex.ofReal_one, ht'_def, Complex.add_im, Complex.one_im,
        Complex.ofReal_im, add_zero, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.I_re, mul_zero, zero_add, Complex.natCast_im]
  have hshift := RiemannZeta.norm_digamma_shift_add_mul_I_le r hr0 t'
  have hr12 : r + 1 / 2 ∈ Set.Icc (1 / 2 : ℝ) (b - 1 + m + 3 / 2) := ⟨by linarith, by linarith⟩
  have hr32 : r + 3 / 2 ∈ Set.Icc (1 / 2 : ℝ) (b - 1 + m + 3 / 2) := ⟨by linarith, by linarith⟩
  have hΓ12 : Real.Gamma (r + 1 / 2) ≤ MΓ :=
    RiemannZeta.Real.Gamma_le_max_of_mem_Icc' (by norm_num only) (by linarith) hr12
  have hΓ32 : Real.Gamma (r + 3 / 2) ≤ MΓ :=
    RiemannZeta.Real.Gamma_le_max_of_mem_Icc' (by norm_num only) (by linarith) hr32
  have hlog_le :
    Real.log (max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) + 1) ≤ Real.log (MΓ + 1) := by
    apply Real.log_le_log (by positivity)
    linarith [max_le hΓ12 hΓ32]
  have hcast : (1 + r : ℝ) + (t' : ℂ) * Complex.I = 1 + (r : ℂ) + (t' : ℂ) * Complex.I := by
    push_cast; ring
  have hneg_log_le := hC₁ r t' hr0
  rw [← hcast] at hneg_log_le
  have hdigamma_shift_le' :
    ‖Complex.digamma ((1 + r : ℝ) + (t' : ℂ) * Complex.I)‖ ≤
      8 * Real.log (MΓ + 1) + 8 * C₁ + 20 * Real.pi * |t'| := by
    have h1 :
      (8 : ℝ) *
          (Real.log (max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) + 1) -
            Real.log ‖Complex.Gamma ((1 + r : ℝ) + (t' : ℂ) * Complex.I)‖) ≤
        8 * Real.log (MΓ + 1) + 8 * C₁ + 20 * Real.pi * |t'| := by
      linarith only [hlog_le, hneg_log_le]
    exact hshift.trans h1
  have hdigamma_shift_le :
    ‖Complex.digamma (z + m)‖ ≤ 8 * Real.log (MΓ + 1) + 8 * C₁ + 20 * Real.pi * |t'| := by
    rw [← hzr]; exact hdigamma_shift_le'
  have hshiftm : ‖Complex.digamma z‖ ≤ ‖Complex.digamma (z + m)‖ + 2 * m :=
    norm_digamma_le_shift_nat_add hzim m
  have hlogMΓ1_nonneg : 0 ≤ Real.log (MΓ + 1) := Real.log_nonneg (by linarith)
  have hmax_nonneg : (0 : ℝ) ≤ max C₁ 0 := le_max_right _ _
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hprod_nonneg :
    (0 : ℝ) ≤ (8 * Real.log (MΓ + 1) + 8 * max C₁ 0 + (4 + 2 * m) + 20 * Real.pi) * |t'| :=
    mul_nonneg (by linarith only [Real.pi_pos, hlogMΓ1_nonneg, hmax_nonneg, hmnn]) (le_of_lt ht'pos)
  calc
    ‖Complex.digamma z‖ ≤ ‖Complex.digamma (z + m)‖ + 2 * m := hshiftm
    _ ≤ (8 * Real.log (MΓ + 1) + 8 * C₁ + 20 * Real.pi * |t'|) + 2 * m := by linarith
    _ ≤ C * (|t'| + 1) := by
      rw [hC_def]
      nlinarith only [hC₁_le, hlogMΓ1_nonneg, hmax_nonneg, hprod_nonneg, Real.pi_pos, hmnn]

/-! ### A fixed-`A` strip bound on the gamma factor's log-derivative -/

/--
Input/assumptions: `A : ℕ`.
Conclusion: there is a fixed `C ≥ 0` (depending on `A`) such that for every character `χ` (any
modulus, either parity) and every `σ T : ℝ` with `-A - 1/2 ≤ σ ≤ A + 3/2` and `1 ≤ |T|`,
`‖logDeriv (gammaFactor χ) (σ + T i)‖ ≤ C * (|T| + 1)`.
Content: generalizes
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.exists_norm_logDeriv_gammaFactor_horizontal_le`
(the `A = 2`-ish central-strip
case) via `PseudoPrime.AnalyticNumberTheory.DirichletLFunction.exists_norm_digamma_strip_le` on the
strip `[-A - 1, A + 2]` (shift `m := A + 2`, chosen
so `a + m = 1`), which contains both parities' digamma argument range `σ/2` / `(σ + 1)/2` for
`σ ∈ [-A - 1/2, A + 3/2]`.
Role: the fixed-strip gamma ingredient, applied at both `s` and `1 - s` in the far-left
`L'/L` reflection bound.
-/
theorem exists_norm_logDeriv_gammaFactor_fixed_strip_le (A : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (σ T : ℝ),
          -(A : ℝ) - 1 / 2 ≤ σ →
            σ ≤ (A : ℝ) + 3 / 2 →
            1 ≤ |T| →
            ‖logDeriv (DirichletCharacter.gammaFactor χ) ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
              C * (|T| + 1) := by
  obtain ⟨C₀, hC₀nonneg, hC₀⟩ :=
    exists_norm_digamma_strip_le (-(A : ℝ) - 1) ((A : ℝ) + 2) (by linarith) (A + 2)
      (by
        push_cast; linarith)
  set C : ℝ := |Real.log Real.pi| / 2 + C₀ / 2 with hC_def
  have hCnonneg : 0 ≤ C := by
    have h1 : (0 : ℝ) ≤ |Real.log Real.pi| := abs_nonneg _
    rw [hC_def]; linarith
  refine ⟨C, hCnonneg, fun χ σ T hσ1 hσ2 hT => ?_⟩
  set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I with hs_def
  have hsim : s.im = T := by
    simp only [hs_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hsim_ne : s.im ≠ 0 := by
    rw [hsim]; intro h; rw [h] at hT; norm_num only at hT
  have hlogpi_norm : ‖(-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)‖ = |Real.log Real.pi| / 2 := by
    have h1 : (-(Complex.log (Real.pi : ℂ)) / 2 : ℂ) = ((-(Real.log Real.pi) / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_log Real.pi_pos.le]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_div]
    rw [abs_neg]
    norm_num only
  have hmain :
    ∀ a b : ℝ,
      -(A : ℝ) - 1 ≤ a →
        a ≤ (A : ℝ) + 2 →
        b = T / 2 →
        ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma ((a : ℂ) + (b : ℂ) * Complex.I) / 2 :
              ℂ)‖ ≤
          C * (|T| + 1) := by
    intro a b ha1 ha2 hb
    set z : ℂ := (a : ℂ) + (b : ℂ) * Complex.I with hz_def
    have hzre : z.re = a := by
      simp only [hz_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    have hzim : z.im = b := by
      simp only [hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    have hzim_abs : (1 : ℝ) / 2 ≤ |z.im| := by
      rw [hzim, hb, abs_div]
      have h2 : |(2 : ℝ)| = 2 := by norm_num only
      rw [h2]; linarith [hT]
    have hdb :=
      hC₀ z
        (by
          rw [hzre]; exact ha1)
        (by
          rw [hzre]; exact ha2)
        hzim_abs
    rw [hzim, hb] at hdb
    have habs2 : |T / 2| = |T| / 2 := by
      rw [abs_div]; norm_num only
    rw [habs2] at hdb
    calc
      ‖(-(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma z / 2 : ℂ)‖ ≤
          ‖(-(Complex.log (Real.pi : ℂ)) / 2 : ℂ)‖ + ‖(Complex.digamma z / 2 : ℂ)‖ :=
        norm_add_le _ _
      _ = |Real.log Real.pi| / 2 + ‖Complex.digamma z‖ / 2 := by
        rw [hlogpi_norm, norm_div, Complex.norm_two]
      _ ≤ |Real.log Real.pi| / 2 + C₀ * (|T| / 2 + 1) / 2 := by gcongr
      _ ≤ C * (|T| + 1) := by
        rw [hC_def]
        nlinarith [hC₀nonneg, abs_nonneg T,
          mul_nonneg (abs_nonneg (Real.log Real.pi)) (abs_nonneg T),
          mul_nonneg hC₀nonneg (abs_nonneg T)]
  rcases χ.even_or_odd with heven | hodd
  · have hform : s / 2 = ((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hs_def]; push_cast; ring
    rw [logDeriv_gammaFactor_eq_of_even heven hsim_ne, hform]
    exact hmain (σ / 2) (T / 2) (by linarith) (by linarith) rfl
  · have hform : (s + 1) / 2 = (((σ + 1) / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hs_def]; push_cast; ring
    rw [logDeriv_gammaFactor_eq_of_odd hodd hsim_ne, hform]
    exact hmain ((σ + 1) / 2) (T / 2) (by linarith) (by linarith) rfl

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
