/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.Growth
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BasicBounds

/-!
# Zeta growth and zero-free-region prerequisites

The functional equation gives left-half-plane growth and excludes nontrivial
zeros there. Pole cancellation constructs the entire function `(s-1)ζ(s)`
with value one at the pole. Auxiliary exponential envelopes and Mellin bounds
provide additional strip-growth estimates. The logarithmic local zero count
itself is established separately in `PseudoPrime.AnalyticNumberTheory.RiemannZeta.Jensen`.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The `|ζ|` growth bound on the left half-plane (companion to `norm_digamma...` on the
`ζ'/ζ` side), via the functional equation and the elementary bounds on `Γ`, `cos`, and the
Dirichlet series — no logarithmic derivative, hence no Borel-Carathéodory / branch-cut
subtlety is needed here. -/
theorem norm_riemannZeta_one_sub_le {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta (1 - s)‖ ≤
      2 * (2 * Real.pi) ^ (-s.re) * Real.Gamma s.re * (2 * Real.cosh (Real.pi * s.im / 2)) *
        ∑' n : ℕ, (n : ℝ) ^ (-s.re) := by
  obtain ⟨hs1, hs2⟩ := side_conditions_of_one_lt_re hs
  rw [riemannZeta_one_sub hs1 hs2, norm_mul, norm_mul, norm_mul, norm_mul]
  have h2pipos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2 : ‖(2 : ℂ)‖ = 2 := Complex.norm_two
  have hcpow : ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ = (2 * Real.pi) ^ (-s.re) := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos h2pipos]
    congr 1
  have hgamma := norm_Gamma_le_Gamma_re (by linarith : (0 : ℝ) < s.re)
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ ≤ 2 * Real.cosh (Real.pi * s.im / 2) := by
    have := norm_cos_le_two_mul_cosh_im ((Real.pi : ℂ) * s / 2)
    convert this using 2
    simp only [Complex.div_ofNat_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero]
  have hzeta := norm_riemannZeta_le hs
  rw [h2, hcpow]
  gcongr

/-- For `Re w < 0`, zeta is nonzero away from the negative even integers.
In the functional equation with `s=1-w`, the factors `2`, `(2π)^(-s)`,
`Γ(s)`, and `ζ(s)` are nonzero. Only `cos(πs/2)` can vanish, forcing
`w=-2(n+1)`. Thus nontrivial zeros cannot lie left of the critical strip. -/
theorem riemannZeta_ne_zero_of_re_neg {w : ℂ} (hw : w.re < 0) (hnt : ∀ n : ℕ, w ≠ -2 * (n + 1)) :
    riemannZeta w ≠ 0 := by
  set s : ℂ := 1 - w with hs_def
  have hs_re : 1 < s.re := by
    rw [hs_def]; simp only [Complex.sub_re, Complex.one_re]; linarith
  obtain ⟨hs1, hs2⟩ := side_conditions_of_one_lt_re hs_re
  have heq := riemannZeta_one_sub hs1 hs2
  rw [show (1 : ℂ) - s = w from by
      rw [hs_def]; ring] at heq
  intro hzero
  rw [hzero] at heq
  have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
  have h2pipos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcpowne : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    intro h
    exact
      (Complex.ofReal_ne_zero.mpr h2pipos.ne')
        (by simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, mul_eq_zero, OfNat.ofNat_ne_zero,
          Complex.ofReal_eq_zero, Real.pi_ne_zero, or_self] using
          ((Complex.cpow_eq_zero_iff _ _).mp h).1)
  have hGammane : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hzetane : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs_re
  have hcosz : Complex.cos ((Real.pi : ℂ) * s / 2) = 0 := by
    have h1 : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s ≠ 0 :=
      mul_ne_zero (mul_ne_zero h2ne hcpowne) hGammane
    rcases mul_eq_zero.mp heq.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' h1
      · exact h'
    · exact absurd h hzetane
  rw [Complex.cos_eq_zero_iff] at hcosz
  obtain ⟨k, hk⟩ := hcosz
  have hseq : s = 2 * (k : ℂ) + 1 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp at hk
    linear_combination hk
  have hcomb : (1 : ℂ) - w = 2 * (k : ℂ) + 1 := by
    rw [← hs_def]; exact hseq
  have hw_eq : w = -2 * (k : ℂ) := by linear_combination -hcomb
  have hwre : w.re = -2 * (k : ℝ) := by
    rw [hw_eq]
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.intCast_re,
      Complex.im_ofNat, Complex.intCast_im, mul_zero, sub_zero]
  have hk0 : (1 : ℤ) ≤ k := by
    have : (-2 : ℝ) * (k : ℝ) < 0 := hwre ▸ hw
    have hkr : (0 : ℝ) < (k : ℝ) := by linarith
    have : (0 : ℤ) < k := by exact_mod_cast hkr
    omega
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ k - 1)
  have hkn : k = (n : ℤ) + 1 := by omega
  have hwval : w = -2 * ((n : ℕ) + 1 : ℂ) := by
    rw [hw_eq, hkn]; push_cast; ring
  exact hnt n hwval

/-- `(s-1)ζ(s)`, updated to its removable-singularity value `1` at `s=1`, is entire. This
removes the one obstruction to applying `PhragmenLindelof.vertical_strip` directly to `ζ`
across a strip containing `Re s = 1` (`ζ`'s only pole): apply the strip bound to this entire
function instead, then divide back out by `s-1` away from `s=1`. -/
noncomputable def zetaEntire : ℂ → ℂ :=
  Function.update (fun w => (w - 1) * riemannZeta w) 1 1

theorem zetaEntire_eq_of_ne {w : ℂ} (hw : w ≠ 1) :
    zetaEntire w = (w - 1) * riemannZeta w :=
  Function.update_of_ne hw _ _

/-- `|cosh(x+iy)|² = sinh²x + cos²y`, the key real/imaginary decomposition used to analyze the
growth-canceling auxiliary function below. -/
theorem normSq_cosh_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.cosh ((x : ℂ) + (y : ℂ) * Complex.I)) =
      Real.sinh x ^ 2 + Real.cos y ^ 2 := by
  have heq :
    Complex.cosh ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((Real.cosh x * Real.cos y : ℝ) : ℂ) + ((Real.sinh x * Real.sin y : ℝ) : ℂ) * Complex.I := by
    rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh, ←
      Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_sin]
    push_cast; ring
  rw [heq, Complex.normSq_add_mul_I]
  nlinarith only [Real.cosh_sq_sub_sinh_sq x, Real.sin_sq_add_cos_sq y]

/-- The growth-canceling auxiliary function for the `PhragmenLindelof.vertical_strip`
application: `K=2`, `z₀=1/2`. Chosen so its only zeros (on the real axis, spaced by `π/2`)
avoid the target strip `[-1/10, 11/10]`, while growing at a strictly faster exponential rate
than `ζ` on the left edge (rate `2` vs. `π/2`), comfortably swallowing the extra polynomial
factor from `(w-1)ζ(w)`. -/
noncomputable def zetaAux (w : ℂ) : ℂ :=
  Complex.cosh (2 * Complex.I * (w - 1 / 2))

theorem normSq_zetaAux_apply (σ t : ℝ) :
    Complex.normSq (zetaAux ((σ : ℂ) + (t : ℂ) * Complex.I)) =
      Real.sinh (2 * t) ^ 2 + Real.cos (2 * (σ - 1 / 2)) ^ 2 := by
  have harg :
    2 * Complex.I * (((σ : ℂ) + (t : ℂ) * Complex.I) - 1 / 2) =
      ((-(2 * t) : ℝ) : ℂ) + ((2 * (σ - 1 / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring_nf
    simp only [Complex.I_sq, neg_mul, one_mul]
    ring
  rw [zetaAux, harg, normSq_cosh_add_mul_I,
    Real.sinh_neg]
  ring

theorem norm_zetaAux_ge_cos (σ t : ℝ) :
    |Real.cos (2 * (σ - 1 / 2))| ≤ ‖zetaAux ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have hsq := normSq_zetaAux_apply σ t
  have hnn : (0 : ℝ) ≤ ‖zetaAux ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  nlinarith only [Complex.normSq_eq_norm_sq (zetaAux ((σ : ℂ) + (t : ℂ) * Complex.I)),
    sq_nonneg (Real.sinh (2 * t)), sq_abs (Real.cos (2 * (σ - 1 / 2))), hsq, hnn,
    sq_nonneg (‖zetaAux ((σ : ℂ) + (t : ℂ) * Complex.I)‖ - |Real.cos (2 * (σ - 1 / 2))|)]

theorem norm_zetaAux_ge_sinh (σ t : ℝ) :
    |Real.sinh (2 * t)| ≤ ‖zetaAux ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have hsq := normSq_zetaAux_apply σ t
  have hnn : (0 : ℝ) ≤ ‖zetaAux ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
  nlinarith only [Complex.normSq_eq_norm_sq (zetaAux ((σ : ℂ) + (t : ℂ) * Complex.I)),
    sq_nonneg (Real.cos (2 * (σ - 1 / 2))), sq_abs (Real.sinh (2 * t)), hsq, hnn,
    sq_nonneg (‖zetaAux ((σ : ℂ) + (t : ℂ) * Complex.I)‖ - |Real.sinh (2 * t)|)]

/-- For any real `x` and `c > 0`, `x*exp(-c*x) ≤ 1/c`, using
`c*x ≤ exp(c*x)`. This absorbs a linear factor into an exponential envelope. -/
theorem mul_exp_neg_le (c x : ℝ) (hc : 0 < c) : x * Real.exp (-(c * x)) ≤ 1 / c := by
  have h1 : c * x ≤ Real.exp (c * x) := by linarith [Real.add_one_le_exp (c * x)]
  have h2 : c * x * Real.exp (-(c * x)) ≤ Real.exp (c * x) * Real.exp (-(c * x)) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  rw [← Real.exp_add] at h2
  simp only [add_neg_cancel, Real.exp_zero] at h2
  rw [le_div_iff₀ hc]
  nlinarith [h2]

/-- Constant bounding `‖ζ‖` on the left edge `Re = -1/10` in terms of `cosh(πt/2)`
(`s = 11/10 - it` in `PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_riemannZeta_one_sub_le`). -/
noncomputable def leftEdgeConst : ℝ :=
  4 * (2 * Real.pi) ^ (-(11 / 10 : ℝ)) * Real.Gamma (11 / 10) * ∑' n : ℕ, (n : ℝ) ^ (-(11 / 10 : ℝ))

theorem norm_riemannZeta_left_edge_le (t : ℝ) :
    ‖riemannZeta ((-(1 : ℝ) / 10 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      leftEdgeConst * Real.cosh (Real.pi * t / 2) := by
  set s : ℂ := (11 / 10 : ℝ) - (t : ℂ) * Complex.I with hs_def
  have hs_re : 1 < s.re := by
    rw [hs_def];
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
    norm_num only
  have hws : (1 : ℂ) - s = (-(1 : ℝ) / 10 : ℂ) + (t : ℂ) * Complex.I := by
    rw [hs_def]; push_cast; ring
  have hbound := norm_riemannZeta_one_sub_le hs_re
  rw [hws] at hbound
  have hsre : s.re = 11 / 10 := by
    rw [hs_def];
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
  have hsim : s.im = -t := by
    rw [hs_def];
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_sub]
  rw [hsre, hsim] at hbound
  rw [show Real.pi * (-t) / 2 = -(Real.pi * t / 2) from by ring, Real.cosh_neg] at hbound
  have heq :
    2 * (2 * Real.pi) ^ (-(11 / 10 : ℝ)) * Real.Gamma (11 / 10) *
        (2 * Real.cosh (Real.pi * t / 2)) *
        ∑' n : ℕ, (n : ℝ) ^ (-(11 / 10 : ℝ)) =
      leftEdgeConst * Real.cosh (Real.pi * t / 2) := by
    rw [leftEdgeConst]; ring
  rwa [heq] at hbound

theorem norm_sub_one_le (σ t : ℝ) : ‖(σ : ℂ) + (t : ℂ) * Complex.I - 1‖ ≤ |σ - 1| + |t| := by
  have heq : (σ : ℂ) + (t : ℂ) * Complex.I - 1 = ((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    push_cast; ring
  rw [heq]
  calc
    ‖((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖((σ - 1 : ℝ) : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = |σ - 1| + |t| := by
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]

theorem cos_six_fifths_pos : 0 < Real.cos (6 / 5 : ℝ) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by nlinarith [Real.pi_gt_three]⟩

theorem two_sub_pi_div_two_pos : (0 : ℝ) < 2 - Real.pi / 2 := by nlinarith [Real.pi_lt_d2]

/-- Constant for the "small `|t|`" regime of the left-edge ratio bound. -/
noncomputable def leftEdgeC1 : ℝ :=
  21 / 10 * leftEdgeConst * Real.cosh (Real.pi / 2) /
    Real.cos (6 / 5)

/-- Constant for the "large `|t|`" regime of the left-edge ratio bound. -/
noncomputable def leftEdgeC2 : ℝ :=
  4 * leftEdgeConst * (11 / 10 + 1 / (2 - Real.pi / 2))

noncomputable def leftEdgeRatioConst : ℝ :=
  max leftEdgeC1 leftEdgeC2

theorem leftEdgeConst_nonneg : 0 ≤ leftEdgeConst := by
  rw [leftEdgeConst]
  have h1 : (0 : ℝ) ≤ (2 * Real.pi) ^ (-(11 / 10 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have h2 : (0 : ℝ) ≤ Real.Gamma (11 / 10) := (Real.Gamma_pos_of_pos (by norm_num only)).le
  have h3 : (0 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-(11 / 10 : ℝ)) := by
    apply tsum_nonneg
    intro n
    positivity
  positivity

theorem zetaEntire_le_mul_zetaAux_left (t : ℝ) :
    ‖zetaEntire ((-(1 : ℝ) / 10 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      leftEdgeRatioConst *
        ‖zetaAux ((-(1 : ℝ) / 10 : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set w : ℂ := (-(1 : ℝ) / 10 : ℂ) + (t : ℂ) * Complex.I with hw_def
  have hcast : ((-(1 : ℝ) / 10 : ℝ) : ℂ) = (-(1 : ℝ) / 10 : ℂ) := by
    push_cast; ring
  have hw1 : w ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hw_def] at hre
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.one_re] at hre
    norm_num only [Complex.div_re, Complex.neg_re, Complex.ofReal_re, Complex.re_ofNat,
      Complex.im_ofNat, Complex.normSq_ofNat, Complex.one_re, Complex.one_im, zero_mul, mul_zero,
      zero_div, add_zero] at hre
  have hzeta_le := norm_riemannZeta_left_edge_le t
  rw [← hw_def] at hzeta_le
  have hw1norm := norm_sub_one_le (-(1 : ℝ) / 10) t
  rw [hcast, ← hw_def] at hw1norm
  have hstep1 :
    ‖zetaEntire w‖ ≤
      (11 / 10 + |t|) *
        (leftEdgeConst * Real.cosh (Real.pi * t / 2)) := by
    rw [zetaEntire_eq_of_ne hw1, norm_mul]
    have h1 : |(-(1 : ℝ) / 10) - 1| = 11 / 10 := by norm_num only
    rw [h1] at hw1norm
    have hLnn :
      (0 : ℝ) ≤
        leftEdgeConst * Real.cosh (Real.pi * t / 2) :=
      mul_nonneg leftEdgeConst_nonneg
        (Real.cosh_pos _).le
    exact mul_le_mul hw1norm hzeta_le (norm_nonneg _) (by linarith [abs_nonneg t])
  by_cases ht : |t| ≤ 1
  · have hcos_lb :=
      norm_zetaAux_ge_cos (-(1 : ℝ) / 10) t
    rw [hcast, ← hw_def] at hcos_lb
    have hy : (2 : ℝ) * (-(1 : ℝ) / 10 - 1 / 2) = -(6 / 5) := by norm_num only
    rw [hy,
      abs_of_pos
        (by
          rw [Real.cos_neg];
          exact cos_six_fifths_pos)] at hcos_lb
    rw [Real.cos_neg] at hcos_lb
    have hcosh_le : Real.cosh (Real.pi * t / 2) ≤ Real.cosh (Real.pi / 2) := by
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_pos (show (0 : ℝ) < Real.pi / 2 from by positivity)]
      rw [show Real.pi * t / 2 = Real.pi / 2 * t from by ring, abs_mul,
        abs_of_pos (show (0 : ℝ) < Real.pi / 2 from by positivity)]
      nlinarith [ht, abs_le.mp ht, Real.pi_pos]
    have hpoly_le : (11 / 10 + |t| : ℝ) ≤ 21 / 10 := by linarith [ht]
    have hstep2 :
      ‖zetaEntire w‖ ≤
        21 / 10 *
          (leftEdgeConst * Real.cosh (Real.pi / 2)) := by
      calc
        ‖zetaEntire w‖ ≤
            (11 / 10 + |t|) *
              (leftEdgeConst * Real.cosh (Real.pi * t / 2)) :=
          hstep1
        _ ≤
            21 / 10 *
              (leftEdgeConst *
                Real.cosh (Real.pi / 2)) :=
          by
          apply mul_le_mul hpoly_le
          · exact
              mul_le_mul_of_nonneg_left hcosh_le
                leftEdgeConst_nonneg
          · exact
              mul_nonneg leftEdgeConst_nonneg
                (Real.cosh_pos _).le
          · norm_num only
    have hC1eq :
      leftEdgeC1 * Real.cos (6 / 5) =
        21 / 10 *
          (leftEdgeConst *
            Real.cosh (Real.pi / 2)) := by
      rw [leftEdgeC1,
        div_mul_cancel₀ _ cos_six_fifths_pos.ne'];
      ring
    have hC1_nonneg : 0 ≤ leftEdgeC1 := by
      rw [leftEdgeC1]
      apply div_nonneg _ cos_six_fifths_pos.le
      exact
        mul_nonneg
          (mul_nonneg (by norm_num only)
            leftEdgeConst_nonneg)
          (Real.cosh_pos _).le
    calc
      ‖zetaEntire w‖ ≤
          21 / 10 *
            (leftEdgeConst *
              Real.cosh (Real.pi / 2)) :=
        hstep2
      _ = leftEdgeC1 * Real.cos (6 / 5) := hC1eq.symm
      _ ≤ leftEdgeC1 * ‖zetaAux w‖ :=
        mul_le_mul_of_nonneg_left hcos_lb hC1_nonneg
      _ ≤ leftEdgeRatioConst * ‖zetaAux w‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · rw [not_le] at ht
    have hsinh_lb :=
      norm_zetaAux_ge_sinh (-(1 : ℝ) / 10) t
    rw [hcast, ← hw_def] at hsinh_lb
    have habs2t : |Real.sinh (2 * t)| = Real.sinh (2 * |t|) := by
      by_cases ht0 : 0 ≤ t
      · rw [abs_of_nonneg ht0, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by linarith))]
      · push Not at ht0
        rw [abs_of_neg ht0, show 2 * -t = -(2 * t) from by ring, Real.sinh_neg,
          abs_of_neg (Real.sinh_neg_iff.mpr (by linarith))]
    rw [habs2t] at hsinh_lb
    set c : ℝ := 2 - Real.pi / 2 with hc_def
    have hc_pos : 0 < c := two_sub_pi_div_two_pos
    have hcosh_exp : Real.cosh (Real.pi * t / 2) ≤ Real.exp (Real.pi * |t| / 2) := by
      rw [Real.cosh_eq]
      have h1 : |Real.pi * t / 2| = Real.pi * |t| / 2 := by
        rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]; norm_num only
      have h2 : Real.exp (-(Real.pi * t / 2)) ≤ Real.exp (Real.pi * |t| / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [neg_abs_le (Real.pi * t / 2), h1]
      have h3 : Real.exp (Real.pi * t / 2) ≤ Real.exp (Real.pi * |t| / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [le_abs_self (Real.pi * t / 2), h1]
      linarith
    have hsinh_exp : Real.exp (2 * |t|) / 4 ≤ Real.sinh (2 * |t|) := by
      rw [Real.sinh_eq]
      have hexp2x : (4 : ℝ) ≤ Real.exp (2 * (2 * |t|)) := by
        have := Real.add_one_le_exp (2 * (2 * |t|))
        nlinarith [ht, abs_nonneg t, le_abs_self t]
      have hexpsq : Real.exp (2 * |t|) * Real.exp (2 * |t|) = Real.exp (2 * (2 * |t|)) := by
        rw [← Real.exp_add]; ring_nf
      have hexppos : 0 < Real.exp (2 * |t|) := Real.exp_pos _
      have hexpge2 : (2 : ℝ) ≤ Real.exp (2 * |t|) := by nlinarith [hexpsq, hexp2x, hexppos]
      have hmulinv : Real.exp (2 * |t|) * Real.exp (-(2 * |t|)) = 1 := by
        rw [← Real.exp_add]
        simp only [add_neg_cancel, Real.exp_zero]
      nlinarith [hmulinv, hexpge2, hexppos, Real.exp_pos (-(2 * |t|))]
    have hpoly_bound : (11 / 10 + |t|) * Real.exp (-(c * |t|)) ≤ 11 / 10 + 1 / c := by
      have h1 : |t| * Real.exp (-(c * |t|)) ≤ 1 / c :=
        mul_exp_neg_le c |t| hc_pos
      have h2 : Real.exp (-(c * |t|)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith [hc_pos.le, abs_nonneg t]
      nlinarith [h1, h2]
    have hratio :
      (11 / 10 + |t|) * Real.exp (Real.pi * |t| / 2) / Real.exp (2 * |t|) ≤ 11 / 10 + 1 / c := by
      have hsplit :
        (11 / 10 + |t|) * Real.exp (Real.pi * |t| / 2) / Real.exp (2 * |t|) =
          (11 / 10 + |t|) * Real.exp (-(c * |t|)) := by
        rw [div_eq_iff (Real.exp_pos _).ne', mul_assoc, ← Real.exp_add,
          show -(c * |t|) + 2 * |t| = Real.pi * |t| / 2 from by
            rw [hc_def]; ring]
      rw [hsplit]; exact hpoly_bound
    have hbig_le :
      (11 / 10 + |t|) * Real.exp (Real.pi * |t| / 2) ≤ (11 / 10 + 1 / c) * Real.exp (2 * |t|) := by
      have := mul_le_mul_of_nonneg_right hratio (Real.exp_pos (2 * |t|)).le
      rwa [div_mul_cancel₀ _ (Real.exp_pos (2 * |t|)).ne'] at this
    have hzetaentire_le :
      ‖zetaEntire w‖ ≤
        4 * (11 / 10 + 1 / c) * leftEdgeConst *
          Real.sinh (2 * |t|) := by
      have hLnn : 0 ≤ leftEdgeConst :=
        leftEdgeConst_nonneg
      have hstep2 :
        ‖zetaEntire w‖ ≤
          (11 / 10 + |t|) *
            (leftEdgeConst *
              Real.exp (Real.pi * |t| / 2)) := by
        refine hstep1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        exact mul_le_mul_of_nonneg_left hcosh_exp hLnn
      have hstep3 :
        ‖zetaEntire w‖ ≤
          leftEdgeConst *
            ((11 / 10 + 1 / c) * Real.exp (2 * |t|)) := by
        refine hstep2.trans ?_
        rw [show
            (11 / 10 + |t|) *
                (leftEdgeConst *
                  Real.exp (Real.pi * |t| / 2)) =
              leftEdgeConst *
                ((11 / 10 + |t|) * Real.exp (Real.pi * |t| / 2))
            from by ring]
        exact mul_le_mul_of_nonneg_left hbig_le hLnn
      have hstep4 :
        leftEdgeConst *
            ((11 / 10 + 1 / c) * Real.exp (2 * |t|)) ≤
          leftEdgeConst *
            ((11 / 10 + 1 / c) * (4 * Real.sinh (2 * |t|))) := by
        apply mul_le_mul_of_nonneg_left _ hLnn
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hsinh_exp]
      calc
        ‖zetaEntire w‖ ≤
            leftEdgeConst *
              ((11 / 10 + 1 / c) * Real.exp (2 * |t|)) :=
          hstep3
        _ ≤
            leftEdgeConst *
              ((11 / 10 + 1 / c) * (4 * Real.sinh (2 * |t|))) :=
          hstep4
        _ =
            4 * (11 / 10 + 1 / c) * leftEdgeConst *
              Real.sinh (2 * |t|) :=
          by ring
    calc
      ‖zetaEntire w‖ ≤
          4 * (11 / 10 + 1 / c) * leftEdgeConst *
            Real.sinh (2 * |t|) :=
        hzetaentire_le
      _ ≤
          4 * (11 / 10 + 1 / c) * leftEdgeConst *
            ‖zetaAux w‖ :=
        by
        apply mul_le_mul_of_nonneg_left hsinh_lb
        have hLnn : 0 ≤ leftEdgeConst :=
          leftEdgeConst_nonneg
        positivity
      _ = leftEdgeC2 * ‖zetaAux w‖ := by
        rw [leftEdgeC2, hc_def]; ring
      _ ≤ leftEdgeRatioConst * ‖zetaAux w‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- Constant bounding `‖ζ‖` on the right edge `Re = 11/10` — no `t`-growth at all here, unlike
the left edge, since `Re s = 11/10 > 1` puts us directly in the region of absolute convergence
of the Dirichlet series. -/
noncomputable def rightEdgeConst : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ (-(11 / 10 : ℝ))

theorem rightEdgeConst_nonneg :
    0 ≤ rightEdgeConst := by
  rw [rightEdgeConst];
  exact tsum_nonneg (fun n => by positivity)

theorem norm_riemannZeta_right_edge_le (t : ℝ) :
    ‖riemannZeta ((11 / 10 : ℝ) + (t : ℂ) * Complex.I)‖ ≤
      rightEdgeConst := by
  have hs_re : (1 : ℝ) < ((11 / 10 : ℝ) + (t : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
    norm_num only
  have hbound := norm_riemannZeta_le hs_re
  have hre : ((11 / 10 : ℝ) + (t : ℂ) * Complex.I).re = 11 / 10 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
  rw [hre] at hbound
  exact hbound

/-- Constant for the "small `|t|`" regime of the right-edge ratio bound. -/
noncomputable def rightEdgeC1 : ℝ :=
  11 / 10 * rightEdgeConst / Real.cos (6 / 5)

/-- Constant for the "large `|t|`" regime of the right-edge ratio bound. -/
noncomputable def rightEdgeC2 : ℝ :=
  12 / 5 * rightEdgeConst

noncomputable def rightEdgeRatioConst : ℝ :=
  max rightEdgeC1 rightEdgeC2

/-- Elementary crude bound `‖sin z‖ ≤ 2 cosh(Im z)`, the `sin` analogue of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_cos_le_two_mul_cosh_im`. -/
theorem norm_sin_le_two_mul_cosh_im (z : ℂ) : ‖Complex.sin z‖ ≤ 2 * Real.cosh z.im := by
  have hsinh_le : |Real.sinh z.im| ≤ Real.cosh z.im := by
    have hpos : (0 : ℝ) < Real.cosh z.im := Real.cosh_pos _
    nlinarith only [Real.cosh_sq_sub_sinh_sq z.im, sq_abs (Real.sinh z.im),
      abs_nonneg (Real.sinh z.im), hpos]
  rw [Complex.sin_eq, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ←
    Complex.ofReal_sinh]
  calc
    ‖(Real.sin z.re : ℂ) * (Real.cosh z.im : ℂ) +
            (Real.cos z.re : ℂ) * (Real.sinh z.im : ℂ) * Complex.I‖ ≤
        ‖(Real.sin z.re : ℂ) * (Real.cosh z.im : ℂ)‖ +
          ‖(Real.cos z.re : ℂ) * (Real.sinh z.im : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = |Real.sin z.re| * Real.cosh z.im + |Real.cos z.re| * |Real.sinh z.im| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
        Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
    _ ≤ 1 * Real.cosh z.im + 1 * Real.cosh z.im := by
      gcongr
      · exact Real.abs_sin_le_one _
      · exact Real.abs_cos_le_one _
    _ = 2 * Real.cosh z.im := by ring

/-- **Lower bound for `Γ` on `Re s < 1`**, via the reflection formula: since
`Γ(s)Γ(1-s) = π/sin(πs)` and `‖Γ(1-s)‖ ≤ Γ(1-Re s)` (elementary upper bound, valid since
`Re(1-s) > 0`), we get `‖Γ(s)‖ = π/(‖sin(πs)‖‖Γ(1-s)‖) ≥ π/(‖sin(πs)‖Γ(1-Re s))`, and
`‖sin(πs)‖ ≤ 2cosh(π·Im s)` bounds the denominator from above. This is what lets the
`completedHurwitzZetaEven/Gammaℝ` ratio stay controlled even though `Γ` (hence `Gammaℝ`) decays
exponentially as `|Im s|→∞`. -/
theorem norm_Gamma_ge_of_re_lt_one {s : ℂ} (hs : s.re < 1)
    (hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0) :
    Real.pi / (2 * Real.cosh (Real.pi * s.im) * Real.Gamma (1 - s.re)) ≤ ‖Complex.Gamma s‖ := by
  have h1mspos : (0 : ℝ) < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]; linarith
  have hGamma1s_ne : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h1mspos
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  have hpine : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hGammas_ne : Complex.Gamma s ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrefl
    exact hsin ((div_eq_zero_iff.mp hrefl.symm).resolve_left hpine)
  have hnorm_eq :
    ‖Complex.Gamma s‖ =
      Real.pi / (‖Complex.sin ((Real.pi : ℂ) * s)‖ * ‖Complex.Gamma (1 - s)‖) := by
    have h2 :
      ‖Complex.Gamma s * Complex.Gamma (1 - s)‖ =
        ‖(Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)‖ := by
      rw [hrefl]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at h2
    rw [eq_div_iff (mul_ne_zero (norm_ne_zero_iff.mpr hsin) (norm_ne_zero_iff.mpr hGamma1s_ne))]
    rw [mul_comm (‖Complex.sin _‖) _, ← mul_assoc, h2,
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hsin)]
  rw [hnorm_eq]
  have hupper : ‖Complex.Gamma (1 - s)‖ ≤ Real.Gamma (1 - s).re :=
    norm_Gamma_le_Gamma_re h1mspos
  have hupper' : ‖Complex.Gamma (1 - s)‖ ≤ Real.Gamma (1 - s.re) := by
    rwa [show (1 - s).re = 1 - s.re from by rw [Complex.sub_re, Complex.one_re]] at hupper
  have hsinbound : ‖Complex.sin ((Real.pi : ℂ) * s)‖ ≤ 2 * Real.cosh (Real.pi * s.im) := by
    have :=
      norm_sin_le_two_mul_cosh_im ((Real.pi : ℂ) * s)
    have him : ((Real.pi : ℂ) * s).im = Real.pi * s.im := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rwa [him] at this
  have hGpos : (0 : ℝ) < Real.Gamma (1 - s.re) := Real.Gamma_pos_of_pos h1mspos
  have hsinpos : (0 : ℝ) < ‖Complex.sin ((Real.pi : ℂ) * s)‖ := norm_pos_iff.mpr hsin
  have hcoshpos : (0 : ℝ) < Real.cosh (Real.pi * s.im) := Real.cosh_pos _
  apply div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
  exact mul_le_mul hsinbound hupper' (norm_nonneg _) (by positivity)

/-- **Uniform-in-`Im s` bound for Mellin transforms.** Since `‖(t:ℂ)^(s-1)‖ = t^(Re s - 1)`
depends only on `Re s` (not `Im s`) for `t > 0`, the triangle inequality gives a bound on
`‖mellin f s‖` depending only on `Re s` — no growth in the imaginary direction at all. This is
the key fact that resolves the `hB` hypothesis of `PhragmenLindelof.vertical_strip`: it reduces
the whole "growth envelope on the interior of the strip" question to the convergence of the
defining integral, already available unconditionally from
`WeakFEPair.isStrongFEPair_toStrongFEPair.mellinConvergent`. -/
theorem norm_mellin_le {f : ℝ → ℂ} {s : ℂ} (_hf : MellinConvergent f s) :
    ‖mellin f s‖ ≤ ∫ t in Set.Ioi (0 : ℝ), t ^ (s.re - 1) * ‖f t‖ := by
  rw [mellin]
  calc
    ‖∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • f t‖ ≤
        ∫ t in Set.Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • f t‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t in Set.Ioi (0 : ℝ), t ^ (s.re - 1) * ‖f t‖ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]

/-- The real integral bounding `‖Λ₀ s‖` for `s.re = σ` — a function of `σ` alone, giving the
"uniform in `Im s`" property that resolves `hB`. -/
noncomputable def mellinBoundConst (σ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), t ^ (σ - 1) *
    ‖(HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t‖

theorem norm_Λ₀_zero_le (s : ℂ) :
    ‖(HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).Λ₀ s‖ ≤
      mellinBoundConst s.re :=
  norm_mellin_le
    (IsStrongFEPair.hasMellin
    (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).isStrongFEPair_toStrongFEPair
        s).1

theorem norm_Λ_zero_le_of_one_le_norm {s : ℂ} (hs : 1 ≤ ‖s‖) (hs' : 1 ≤ ‖(1 / 2 : ℂ) - s‖) :
    ‖(HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).Λ s‖ ≤
      mellinBoundConst s.re + 2 := by
  have hf0 : (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).f₀ = 1 := by
    simp only [HurwitzZeta.hurwitzEvenFEPair, one_div, ↓reduceIte]
  have hg0 : (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).g₀ = 1 := rfl
  have hε : (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).ε = 1 := rfl
  have hk : (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).k = 1 / 2 := rfl
  have heq :
    (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).Λ s =
      (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).Λ₀ s - (1 / s) - (1 / (1 / 2 - s)) := by
    rw [WeakFEPair.Λ, hf0, hg0, hε, hk, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    push_cast
    ring
  rw [heq]
  have h1 : ‖(1 : ℂ) / s‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact div_le_one_of_le₀ hs (norm_nonneg _)
  have h2 : ‖(1 : ℂ) / (1 / 2 - s)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact div_le_one_of_le₀ hs' (norm_nonneg _)
  calc
    ‖(HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).Λ₀ s - (1 / s) - (1 / (1 / 2 - s))‖ ≤
        ‖(HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).Λ₀ s - (1 / s)‖
          + ‖(1 : ℂ) / (1 / 2 - s)‖ :=
      norm_sub_le _ _
    _ ≤
        (‖(HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).Λ₀ s‖ + ‖(1 : ℂ) / s‖) +
          ‖(1 : ℂ) / (1 / 2 - s)‖ :=
      by
      gcongr
      exact norm_sub_le _ _
    _ ≤ (mellinBoundConst s.re + 1) + 1 := by
      gcongr
      exact norm_Λ₀_zero_le s
    _ = mellinBoundConst s.re + 2 := by ring

theorem norm_completedHurwitzZetaEven_zero_le {s : ℂ} (hs : 1 ≤ ‖s / 2‖)
    (hs' : 1 ≤ ‖(1 / 2 : ℂ) - s / 2‖) :
    ‖HurwitzZeta.completedHurwitzZetaEven (0 : UnitAddCircle) s‖ ≤
      (mellinBoundConst (s / 2).re + 2) / 2 := by
  rw [HurwitzZeta.completedHurwitzZetaEven, norm_div, Complex.norm_two]
  gcongr
  exact norm_Λ_zero_le_of_one_le_norm hs hs'

/-- Lower bound on `‖Gammaℝ s‖`, combining the elementary `Γ` reflection-formula lower bound
with the `π^{-s/2}` factor (whose norm depends only on `Re s`). -/
theorem norm_Gammaℝ_ge {s : ℂ} (hs : s.re < 2) (hsin : Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0) :
    Real.pi ^ (1 - s.re / 2) / (2 * Real.cosh (Real.pi * s.im / 2) * Real.Gamma (1 - s.re / 2)) ≤
      ‖Complex.Gammaℝ s‖ := by
  have hre : (s / 2).re = s.re / 2 := by
    rw [Complex.div_re]
    simp only [Complex.re_ofNat, Complex.normSq_ofNat, Complex.im_ofNat, mul_zero, zero_div,
      add_zero]
    ring
  have him : (s / 2).im = s.im / 2 := by
    rw [Complex.div_im]
    simp only [Complex.re_ofNat, Complex.normSq_ofNat, Complex.im_ofNat, mul_zero, zero_div,
      sub_zero]
    ring
  have hs2 : (s / 2).re < 1 := by
    rw [hre]; linarith [hs]
  have hlow := norm_Gamma_ge_of_re_lt_one hs2 hsin
  rw [him, hre] at hlow
  rw [Complex.Gammaℝ_def, norm_mul]
  have hcpow : ‖(Real.pi : ℂ) ^ (-s / 2)‖ = Real.pi ^ (-(s.re / 2)) := by
    rw [show (Real.pi : ℂ) = ((Real.pi : ℝ) : ℂ) from rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    rw [show (-s / 2 : ℂ) = -(s / 2) from by ring, Complex.neg_re, hre]
  rw [hcpow]
  have hpisplit : Real.pi ^ (1 - s.re / 2) = Real.pi * Real.pi ^ (-(s.re / 2)) := by
    rw [show (1 - s.re / 2 : ℝ) = 1 + (-(s.re / 2)) from by ring, Real.rpow_add Real.pi_pos,
      Real.rpow_one]
  rw [hpisplit]
  calc
    Real.pi * Real.pi ^ (-(s.re / 2)) /
          (2 * Real.cosh (Real.pi * s.im / 2) * Real.Gamma (1 - s.re / 2)) =
        Real.pi ^ (-(s.re / 2)) *
          (Real.pi / (2 * Real.cosh (Real.pi * s.im / 2) * Real.Gamma (1 - s.re / 2))) :=
      by ring
    _ ≤ Real.pi ^ (-(s.re / 2)) * ‖Complex.Gamma (s / 2)‖ := by
      rw [show Real.pi * (s.im / 2) = Real.pi * s.im / 2 from by ring] at hlow
      gcongr

/-- **The interior growth bound for `riemannZeta`.** Combines the Mellin-uniform bound on
`completedHurwitzZetaEven` with the reflection-formula lower bound on `Gammaℝ`, giving a bound
on `‖ζ(s)‖` valid throughout the strip (not just its two edges), which is exactly what resolves
the `hB` hypothesis of `PhragmenLindelof.vertical_strip`. -/
theorem norm_riemannZeta_interior_le {s : ℂ} (hs0 : s ≠ 0) (hs : 1 ≤ ‖s / 2‖)
    (hs' : 1 ≤ ‖(1 / 2 : ℂ) - s / 2‖) (hsre : s.re < 2)
    (hsin : Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0) :
    ‖riemannZeta s‖ ≤
      (mellinBoundConst (s / 2).re + 2) / 2 *
        (2 * Real.cosh (Real.pi * s.im / 2) * Real.Gamma (1 - s.re / 2) /
          Real.pi ^ (1 - s.re / 2)) := by
  have heq : riemannZeta s =
    HurwitzZeta.completedHurwitzZetaEven (0 : UnitAddCircle) s / Complex.Gammaℝ s :=
    HurwitzZeta.hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs0)
  rw [heq, norm_div]
  have hnum :=
    norm_completedHurwitzZetaEven_zero_le hs hs'
  have hden := norm_Gammaℝ_ge hsre hsin
  have hlowpos :
    (0 : ℝ) <
      Real.pi ^ (1 - s.re / 2) /
        (2 * Real.cosh (Real.pi * s.im / 2) * Real.Gamma (1 - s.re / 2)) := by
    apply div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    exact mul_pos (by positivity) (Real.Gamma_pos_of_pos (by linarith [hsre]))
  have hGpos : (0 : ℝ) < ‖Complex.Gammaℝ s‖ := lt_of_lt_of_le hlowpos hden
  have hnumnn :
    (0 : ℝ) ≤ (mellinBoundConst (s / 2).re + 2) / 2 :=
    le_trans (norm_nonneg _) hnum
  calc
    ‖HurwitzZeta.completedHurwitzZetaEven (0 : UnitAddCircle) s‖ / ‖Complex.Gammaℝ s‖ ≤
        (mellinBoundConst (s / 2).re + 2) / 2 /
          ‖Complex.Gammaℝ s‖ :=
      by gcongr
    _ ≤
        (mellinBoundConst (s / 2).re + 2) / 2 /
          (Real.pi ^ (1 - s.re / 2) /
            (2 * Real.cosh (Real.pi * s.im / 2) * Real.Gamma (1 - s.re / 2))) :=
      by apply div_le_div_of_nonneg_left hnumnn hlowpos hden
    _ =
        (mellinBoundConst (s / 2).re + 2) / 2 *
          (2 * Real.cosh (Real.pi * s.im / 2) * Real.Gamma (1 - s.re / 2) /
            Real.pi ^ (1 - s.re / 2)) :=
      by rw [div_div_eq_mul_div, mul_div_assoc]

/-- Uniform (over `σ ∈ [-1/10, 11/10]`) bound for the `σ`-dependent factor
`Γ(1-σ/2)/π^{1-σ/2}` appearing in
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_riemannZeta_interior_le`:
`Γ` is bounded via convexity
(as in `PseudoPrime.AnalyticNumberTheory.RiemannZeta.Real.Gamma_le_sqrt_pi_of_mem_Icc`) and
`π^x` is monotone increasing in `x` (`π > 1`). -/
noncomputable def sigmaFactorBound : ℝ :=
  max (Real.Gamma (9 / 20)) (Real.Gamma (21 / 20)) / Real.pi ^ (9 / 20 : ℝ)

theorem sigmaFactor_le {σ : ℝ} (hσ1 : -1 / 10 ≤ σ) (hσ2 : σ ≤ 11 / 10) :
    Real.Gamma (1 - σ / 2) / Real.pi ^ (1 - σ / 2) ≤
      sigmaFactorBound := by
  have hmem : (1 - σ / 2) ∈ Set.Icc (9 / 20 : ℝ) (21 / 20) := ⟨by linarith, by linarith⟩
  have hgam_le : Real.Gamma (1 - σ / 2) ≤ max (Real.Gamma (9 / 20)) (Real.Gamma (21 / 20)) := by
    have hseg : (1 - σ / 2) ∈ segment ℝ (9 / 20 : ℝ) (21 / 20) := by
      rw [segment_eq_Icc (by norm_num only : (9 / 20 : ℝ) ≤ 21 / 20)]; exact hmem
    exact
      Real.convexOn_Gamma.le_on_segment
        (show (9 / 20 : ℝ) ∈ Set.Ioi (0 : ℝ)
          by
          simp only [Set.mem_Ioi]
          norm_num only)
        (show (21 / 20 : ℝ) ∈ Set.Ioi (0 : ℝ)
          by
          simp only [Set.mem_Ioi]
          norm_num only)
        hseg
  have hpi_ge : Real.pi ^ (9 / 20 : ℝ) ≤ Real.pi ^ (1 - σ / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hmem.1
  have hpipos : (0 : ℝ) < Real.pi ^ (9 / 20 : ℝ) := Real.rpow_pos_of_pos Real.pi_pos _
  have hgampos : (0 : ℝ) ≤ max (Real.Gamma (9 / 20)) (Real.Gamma (21 / 20)) := by
    have := (Real.Gamma_pos_of_pos (show (0 : ℝ) < 9 / 20 by norm_num only)).le
    exact le_max_of_le_left this
  rw [sigmaFactorBound]
  have hpi1mspos : (0 : ℝ) < Real.pi ^ (1 - σ / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  calc
    Real.Gamma (1 - σ / 2) / Real.pi ^ (1 - σ / 2) ≤
        max (Real.Gamma (9 / 20)) (Real.Gamma (21 / 20)) / Real.pi ^ (1 - σ / 2) :=
      by gcongr
    _ ≤ max (Real.Gamma (9 / 20)) (Real.Gamma (21 / 20)) / Real.pi ^ (9 / 20 : ℝ) := by
      apply div_le_div_of_nonneg_left hgampos hpipos hpi_ge

/-- All the side conditions needed for
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_riemannZeta_interior_le`
hold automatically once
`|Im w| ≥ 4`, for `w` in the target strip. -/
theorem side_conditions_of_four_le_abs_im {w : ℂ} (hw4 : 4 ≤ |w.im|) :
    w ≠ 0 ∧
      w ≠ 1 ∧
      1 ≤ ‖w / 2‖ ∧ 1 ≤ ‖(1 / 2 : ℂ) - w / 2‖ ∧ Complex.sin ((Real.pi : ℂ) * (w / 2)) ≠ 0 := by
  have himne : w.im ≠ 0 := by
    intro h
    rw [h] at hw4
    norm_num only at hw4
  refine
    ⟨fun h =>
      himne
        (by rw [h]; simp only [Complex.zero_im]),
      fun h =>
      himne
        (by rw [h]; simp only [Complex.one_im]),
      ?_, ?_, ?_⟩
  · calc
      (1 : ℝ) ≤ ‖w‖ / 2 := by
        have := Complex.abs_im_le_norm w
        linarith [hw4, this, abs_nonneg w.im]
      _ = ‖w / 2‖ := by rw [norm_div, Complex.norm_two]
  · have himsub : ((1 / 2 : ℂ) - w / 2).im = -(w.im / 2) := by
      simp only [one_div, Complex.sub_im, Complex.inv_im, Complex.im_ofNat, neg_zero,
        Complex.normSq_ofNat, zero_div, Complex.div_ofNat_im, zero_sub]
    calc
      (1 : ℝ) ≤ |w.im| / 2 := by linarith [hw4]
      _ = |((1 / 2 : ℂ) - w / 2).im| := by
        rw [himsub, abs_neg, abs_div]; norm_num only
      _ ≤ ‖(1 / 2 : ℂ) - w / 2‖ := Complex.abs_im_le_norm _
  · intro h
    rw [Complex.sin_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    have him : ((Real.pi : ℂ) * (w / 2)).im = Real.pi * (w.im / 2) := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.div_ofNat_im, Complex.ofReal_im,
        Complex.div_ofNat_re, zero_mul, add_zero]
    have him' : ((k : ℂ) * (Real.pi : ℂ)).im = 0 := by
      simp only [Complex.mul_im, Complex.intCast_re, Complex.ofReal_im, mul_zero,
        Complex.intCast_im, Complex.ofReal_re, zero_mul, add_zero]
    rw [hk, him'] at him
    apply himne
    have hpi := Real.pi_ne_zero
    have h2 : Real.pi * (w.im / 2) = 0 := him.symm
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact absurd h1 hpi
    · linarith [h1]

theorem integrableOn_rpow_mul_norm_f_modif (σ : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (σ - 1) * ‖(HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t‖)
      (Set.Ioi 0) := by
  have hconv :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1) •
        (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t)
      (Set.Ioi 0) :=
    (IsStrongFEPair.hasMellin
      (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).isStrongFEPair_toStrongFEPair
        (σ : ℂ)).1
  have hnormconv :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => ‖(t : ℂ) ^ ((σ : ℂ) - 1) •
        (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t‖)
      (Set.Ioi 0) :=
    hconv.norm
  apply hnormconv.congr_fun _ measurableSet_Ioi
  intro t ht
  simp only [Set.mem_Ioi] at ht
  change
    ‖(t : ℂ) ^ ((σ : ℂ) - 1) • (HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t‖ =
      t ^ (σ - 1) * ‖(HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t‖
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re,
    Complex.ofReal_re]

theorem rpow_sub_one_le_add {t : ℝ} (ht : 0 < t) {σ a b : ℝ} (ha : a ≤ σ) (hb : σ ≤ b) :
    t ^ (σ - 1) ≤ t ^ (a - 1) + t ^ (b - 1) := by
  by_cases ht1 : 1 ≤ t
  · have h1 : t ^ (σ - 1) ≤ t ^ (b - 1) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    have h2 : (0 : ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg ht.le _
    linarith
  · push Not at ht1
    have h1 : t ^ (σ - 1) ≤ t ^ (a - 1) := Real.rpow_le_rpow_of_exponent_ge ht ht1.le (by linarith)
    have h2 : (0 : ℝ) ≤ t ^ (b - 1) := Real.rpow_nonneg ht.le _
    linarith

/-- **Uniform bound for `mellinBoundConst` over a compact `σ`-range**: since `t^(σ-1)` is
monotone in `σ` for fixed `t` (increasing for `t ≥ 1`, decreasing for `t ≤ 1`), it is bounded
by the sum of its values at the two endpoints, and this transfers to the integral. Closes the
last gap in the interior ratio bound. -/
theorem mellinBoundConst_le_add {σ a b : ℝ} (ha : a ≤ σ) (hb : σ ≤ b) :
    mellinBoundConst σ ≤
      mellinBoundConst a +
        mellinBoundConst b := by
  rw [mellinBoundConst,
    mellinBoundConst,
    mellinBoundConst, ←
    MeasureTheory.integral_add
      (integrableOn_rpow_mul_norm_f_modif a)
      (integrableOn_rpow_mul_norm_f_modif b)]
  apply
    MeasureTheory.setIntegral_mono_on
      (integrableOn_rpow_mul_norm_f_modif σ)
      ((integrableOn_rpow_mul_norm_f_modif a).add
        (integrableOn_rpow_mul_norm_f_modif b))
      measurableSet_Ioi
  intro t ht
  simp only [Set.mem_Ioi] at ht
  simp only [Pi.add_apply]
  have hrpow := rpow_sub_one_le_add ht ha hb
  have hnn : (0 : ℝ) ≤
    ‖(HurwitzZeta.hurwitzEvenFEPair (0 : UnitAddCircle)).f_modif t‖ := norm_nonneg _
  nlinarith [hrpow, hnn]

theorem mellinBoundConst_nonneg (σ : ℝ) :
    0 ≤ mellinBoundConst σ := by
  rw [mellinBoundConst]
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro t ht
  simp only [Set.mem_Ioi] at ht
  exact mul_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _)

theorem sigmaFactorBound_nonneg :
    0 ≤ sigmaFactorBound := by
  rw [sigmaFactorBound]
  apply div_nonneg
  · exact le_max_of_le_left (Real.Gamma_pos_of_pos (show (0 : ℝ) < 9 / 20 by norm_num only)).le
  · exact (Real.rpow_pos_of_pos Real.pi_pos _).le

/-- Uniform (over `w` in the target strip) constant bounding `‖ζ‖` throughout the strip in terms
of `cosh(π·Im(w)/2)`, obtained by combining
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_riemannZeta_interior_le` with the two uniform
bounds `PseudoPrime.AnalyticNumberTheory.RiemannZeta.mellinBoundConst_le_add` and
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.sigmaFactor_le` on its two `σ`-dependent factors. -/
noncomputable def interiorRatioConst0 : ℝ :=
  (mellinBoundConst (-1 / 20) +
      mellinBoundConst (11 / 20) +
      2) *
    sigmaFactorBound

theorem interiorRatioConst0_nonneg :
    0 ≤ interiorRatioConst0 := by
  rw [interiorRatioConst0]
  apply mul_nonneg _ sigmaFactorBound_nonneg
  have h1 := mellinBoundConst_nonneg (-1 / 20 : ℝ)
  have h2 := mellinBoundConst_nonneg (11 / 20 : ℝ)
  linarith

theorem norm_riemannZeta_interior_le_uniform {w : ℂ} (hσ1 : -1 / 10 ≤ w.re) (hσ2 : w.re ≤ 11 / 10)
    (hw4 : 4 ≤ |w.im|) :
    ‖riemannZeta w‖ ≤
      interiorRatioConst0 *
        Real.cosh (Real.pi * w.im / 2) := by
  obtain ⟨hw0, _, hs, hs', hsin⟩ :=
    side_conditions_of_four_le_abs_im hw4
  have hsre : w.re < 2 := by linarith
  have hbound :=
    norm_riemannZeta_interior_le hw0 hs hs' hsre hsin
  have hdiv2 : (w / 2).re = w.re / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by simp only [Complex.ofReal_ofNat],
      Complex.div_ofReal_re]
  have ha : (-1 / 20 : ℝ) ≤ (w / 2).re := by
    rw [hdiv2]; linarith
  have hb : (w / 2).re ≤ (11 / 20 : ℝ) := by
    rw [hdiv2]; linarith
  have hmell := mellinBoundConst_le_add ha hb
  have hsig := sigmaFactor_le hσ1 hσ2
  have hGpos : 0 < Real.Gamma (1 - w.re / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hpipos : 0 < Real.pi ^ (1 - w.re / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hf1 :
    (mellinBoundConst (w / 2).re + 2) / 2 ≤
      (mellinBoundConst (-1 / 20) +
          mellinBoundConst (11 / 20) +
          2) /
        2 := by
    linarith
  have hf1nn :
    (0 : ℝ) ≤
      (mellinBoundConst (w / 2).re + 2) / 2 := by
    have := mellinBoundConst_nonneg (w / 2).re;
    linarith
  have hf2eq :
    2 * Real.cosh (Real.pi * w.im / 2) * Real.Gamma (1 - w.re / 2) / Real.pi ^ (1 - w.re / 2) =
      2 * Real.cosh (Real.pi * w.im / 2) *
        (Real.Gamma (1 - w.re / 2) / Real.pi ^ (1 - w.re / 2)) := by
    ring
  have hf2 :
    2 * Real.cosh (Real.pi * w.im / 2) * Real.Gamma (1 - w.re / 2) / Real.pi ^ (1 - w.re / 2) ≤
      2 * Real.cosh (Real.pi * w.im / 2) *
        sigmaFactorBound := by
    rw [hf2eq]
    exact mul_le_mul_of_nonneg_left hsig (mul_nonneg (by norm_num only) (Real.cosh_pos _).le)
  have hf2nn :
    (0 : ℝ) ≤
      2 * Real.cosh (Real.pi * w.im / 2) * Real.Gamma (1 - w.re / 2) /
        Real.pi ^ (1 - w.re / 2) := by
    apply div_nonneg _ hpipos.le
    exact mul_nonneg (mul_nonneg (by norm_num only) (Real.cosh_pos _).le) hGpos.le
  calc
    ‖riemannZeta w‖ ≤
        (mellinBoundConst (w / 2).re + 2) / 2 *
          (2 * Real.cosh (Real.pi * w.im / 2) * Real.Gamma (1 - w.re / 2) /
            Real.pi ^ (1 - w.re / 2)) :=
      hbound
    _ ≤
        (mellinBoundConst (-1 / 20) +
              mellinBoundConst (11 / 20) +
              2) /
            2 *
          (2 * Real.cosh (Real.pi * w.im / 2) *
            sigmaFactorBound) :=
      mul_le_mul hf1 hf2 hf2nn (le_trans hf1nn hf1)
    _ =
        interiorRatioConst0 *
          Real.cosh (Real.pi * w.im / 2) :=
      by
      rw [interiorRatioConst0]
      ring

/-- Generalization of the exponential envelope used in the left-edge argument: `cosh(πt/2)` is
dominated by `exp(π|t|/2)`. -/
theorem cosh_half_pi_mul_le_exp_half_pi_mul_abs (t : ℝ) :
    Real.cosh (Real.pi * t / 2) ≤ Real.exp (Real.pi * |t| / 2) := by
  rw [Real.cosh_eq]
  have h1 : |Real.pi * t / 2| = Real.pi * |t| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num only
  have h2 : Real.exp (-(Real.pi * t / 2)) ≤ Real.exp (Real.pi * |t| / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [neg_abs_le (Real.pi * t / 2), h1]
  have h3 : Real.exp (Real.pi * t / 2) ≤ Real.exp (Real.pi * |t| / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [le_abs_self (Real.pi * t / 2), h1]
  linarith

theorem abs_sinh_two_mul_eq (t : ℝ) : |Real.sinh (2 * t)| = Real.sinh (2 * |t|) := by
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by linarith))]
  · push Not at ht0
    rw [abs_of_neg ht0, show 2 * -t = -(2 * t) from by ring, Real.sinh_neg,
      abs_of_neg (Real.sinh_neg_iff.mpr (by linarith))]

theorem exp_two_mul_abs_div_four_le_sinh {t : ℝ} (ht : 1 < |t|) :
    Real.exp (2 * |t|) / 4 ≤ Real.sinh (2 * |t|) := by
  rw [Real.sinh_eq]
  have hexp2x : (4 : ℝ) ≤ Real.exp (2 * (2 * |t|)) := by
    have := Real.add_one_le_exp (2 * (2 * |t|))
    nlinarith [ht, abs_nonneg t, le_abs_self t]
  have hexpsq : Real.exp (2 * |t|) * Real.exp (2 * |t|) = Real.exp (2 * (2 * |t|)) := by
    rw [← Real.exp_add]
    ring_nf
  have hexppos : 0 < Real.exp (2 * |t|) := Real.exp_pos _
  have hexpge2 : (2 : ℝ) ≤ Real.exp (2 * |t|) := by nlinarith only [hexpsq, hexp2x, hexppos]
  have hmulinv : Real.exp (2 * |t|) * Real.exp (-(2 * |t|)) = 1 := by
    rw [← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero]
  nlinarith only [hmulinv, hexpge2, hexppos, Real.exp_pos (-(2 * |t|))]

/-- Constant for the interior ratio bound (only needed for `|Im w| ≥ 4`, matching the
`comap (|im|) atTop` filter in `PhragmenLindelof.vertical_strip`'s `hB` hypothesis — no
small-`|Im w|` regime is required here, unlike the two edge bounds). -/
noncomputable def interiorLargeTConst : ℝ :=
  4 * interiorRatioConst0 *
    (11 / 10 + 1 / (2 - Real.pi / 2))

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
