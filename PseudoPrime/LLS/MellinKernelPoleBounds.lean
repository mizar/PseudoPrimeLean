/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.XiEndpointNormNumerics
public import PseudoPrime.LLS.MellinKernelFiniteContour

/-!
# Conductor bound for the Mellin kernel pole

The existing xi endpoint estimate bounds the raw completed logarithmic derivative at zero.
It gives a uniform conductor error for the possible kernel pole.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal data of modulus at least eight under GRH, the raw completed
logarithmic derivative at zero has norm at most (7/6) log q + 4. Apply the cutoff-100 xi
endpoint bound and subtract the half-conductor logarithm. This supplies the pole estimate
without assuming that the kernel residue is real. -/
private theorem norm_completedLogDeriv_zero_le_affine_log {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 8 ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ‖logDeriv χ.completedLFunction 0‖ ≤ (7 / 6 : ℝ) * Real.log q + 4 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (by linarith only [hq] : 1 ≤ q)
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqR
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hqR
  have hpi : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 3).trans Real.pi_gt_three.le)
  have hb := norm_logDeriv_xi_zero_le_log_level hq hp hGRH
  rw [Real.log_div hqpos.ne' Real.pi_ne_zero] at hb
  have he : logDeriv χ.completedLFunction 0 = logDeriv (xi χ) 0 - Complex.log q / 2 := by
    rw [PseudoPrime.LLS.logDeriv_xi_zero_eq hp hne]
    ring
  have hn := norm_sub_le (logDeriv (xi χ) 0) (Complex.log q / 2)
  rw [← he, norm_div, ← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog, Complex.norm_ofNat] at hn
  linarith only [hn, hb, hpi]

/-- Under GRH, primitive nonprincipal data of conductor m at least three and at most
an ambient modulus q at least 20000 have completed endpoint norm at most (7/6) log q + 4.
Use the ambient xi estimate and bound the half-conductor logarithm by log q/2. This also
handles the small primitive conductors arising when a character is primitivized. -/
private theorem norm_completedLogDeriv_zero_le_ambient_affine_log {q m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ‖logDeriv χ.completedLFunction 0‖ ≤ (7 / 6 : ℝ) * Real.log q + 4 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (by linarith only [hm] : 1 ≤ m)
  have hmpos : (0 : ℝ) < m := zero_lt_one.trans_le hmR
  have hmqR : (m : ℝ) ≤ q := by exact_mod_cast hmq
  have hqpos : (0 : ℝ) < q := hmpos.trans_le hmqR
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hmR
  have hlmq : Real.log m ≤ Real.log q := Real.log_le_log hmpos hmqR
  have hpi : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 3).trans Real.pi_gt_three.le)
  have hb := norm_logDeriv_xi_zero_le_log_ambient_level hq hm hmq hp hGRH
  rw [Real.log_div hqpos.ne' Real.pi_ne_zero] at hb
  have he : logDeriv χ.completedLFunction 0 = logDeriv (xi χ) 0 - Complex.log m / 2 := by
    rw [PseudoPrime.LLS.logDeriv_xi_zero_eq hp hne]
    ring
  have hn := norm_sub_le (logDeriv (xi χ) 0) (Complex.log m / 2)
  rw [← he, norm_div, ← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog, Complex.norm_ofNat] at hn
  linarith only [hn, hb, hpi, hlmq]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a general kernel and primitive nonprincipal GRH data with modulus at least eight,
the kernel-pole residue has norm at most C log q / sqrt x for scales at least one. The
positive constant depends only on the kernel. Bound the completed endpoint norm by its xi
estimate, absorb the constant into log q, and use the inverse-square-root Mellin power.
This removes the pole contribution from the primitive arithmetic explicit formula. -/
theorem exists_norm_completed_poleResidue_le_log_div_sqrt (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q],
          8 ≤ q →
            ∀ {χ : DirichletCharacter ℂ q},
              PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                χ.IsPrimitive →
                χ ≠ 1 →
                ∀ {x : ℝ},
                  1 ≤ x →
                    ‖weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x (-1 / 2)‖ ≤
                      C * Real.log q / Real.sqrt x := by
  let B := (7 / 6 : ℝ) + 4 / Real.log 2
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hB : 0 < B := add_pos (by norm_num only) (div_pos (by norm_num only) h2)
  refine
    ⟨1 + ‖K.regularized (-(1 / 2))‖ * B,
      add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (norm_nonneg _) hB.le), ?_⟩
  intro q _ hq χ hGRH hp hne x hx
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast (by linarith only [hq] : 2 ≤ q)
  have hlog2 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num only) hqR
  have hlog : 0 ≤ Real.log q := h2.le.trans hlog2
  have hunit : 1 ≤ Real.log q / Real.log 2 :=
    (le_div_iff₀ h2).mpr (by simpa only [one_mul] using hlog2)
  have hb : ‖logDeriv χ.completedLFunction 0‖ ≤ B * Real.log q := by
    have h := norm_completedLogDeriv_zero_le_affine_log hq hp hne hGRH
    dsimp only [B]
    simp only [div_eq_mul_inv] at hunit ⊢
    nlinarith only [hunit, h]
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have he : (-1 / 2 : ℂ) + 1 / 2 = 0 := by ring
  simp only [weightedResidue, ite_true]
  rw [logDeriv_shifted_completed hne, he, norm_mul, norm_neg, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  norm_num only [Complex.div_ofNat_re, Complex.neg_re, Complex.one_re]
  have hpow : x ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt x := by
    rw [Real.rpow_neg hxpos.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hpow]
  calc
    _ ≤ (B * Real.log q) * (‖K.regularized (-(1 / 2))‖ * (1 / Real.sqrt x)) :=
      mul_le_mul_of_nonneg_right hb
        (mul_nonneg (norm_nonneg _) (div_nonneg zero_le_one (Real.sqrt_nonneg x)))
    _ = (‖K.regularized (-(1 / 2))‖ * B) * (Real.log q / Real.sqrt x) := by ring
    _ ≤ (1 + ‖K.regularized (-(1 / 2))‖ * B) * (Real.log q / Real.sqrt x) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
        (div_nonneg hlog (Real.sqrt_nonneg x))
    _ = _ := by ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a general kernel, primitive nonprincipal GRH data of conductor m between three
and an ambient modulus q at least 20000 have kernel-pole residue norm at most
C log q / sqrt x for x at least one. The positive constant depends only on the kernel.
Apply the ambient completed endpoint bound and the inverse-square-root Mellin power.
This supplies the pole estimate when primitivization produces a small conductor. -/
theorem exists_norm_completed_poleResidue_le_ambient_log_div_sqrt (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q m : ℕ} [NeZero m],
          20000 ≤ q →
            3 ≤ m →
            m ≤ q →
            ∀ {χ : DirichletCharacter ℂ m},
              PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
                χ.IsPrimitive →
                χ ≠ 1 →
                ∀ {x : ℝ},
                  1 ≤ x →
                    ‖weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x (-1 / 2)‖ ≤
                      C * Real.log q / Real.sqrt x := by
  let B := (7 / 6 : ℝ) + 4 / Real.log 2
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hB : 0 < B := add_pos (by norm_num only) (div_pos (by norm_num only) h2)
  refine
    ⟨1 + ‖K.regularized (-(1 / 2))‖ * B,
      add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (norm_nonneg _) hB.le), ?_⟩
  intro q m _ hq hm hmq χ hGRH hp hne x hx
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast (by linarith only [hq] : 2 ≤ q)
  have hlog2 : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num only) hqR
  have hlog : 0 ≤ Real.log q := h2.le.trans hlog2
  have hunit : 1 ≤ Real.log q / Real.log 2 :=
    (le_div_iff₀ h2).mpr (by simpa only [one_mul] using hlog2)
  have hb : ‖logDeriv χ.completedLFunction 0‖ ≤ B * Real.log q := by
    have h := norm_completedLogDeriv_zero_le_ambient_affine_log hq hm hmq hp hne hGRH
    dsimp only [B]
    simp only [div_eq_mul_inv] at hunit ⊢
    nlinarith only [hunit, h]
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have he : (-1 / 2 : ℂ) + 1 / 2 = 0 := by ring
  simp only [weightedResidue, ite_true]
  rw [logDeriv_shifted_completed hne, he, norm_mul, norm_neg, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  norm_num only [Complex.div_ofNat_re, Complex.neg_re, Complex.one_re]
  have hpow : x ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt x := by
    rw [Real.rpow_neg hxpos.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hpow]
  calc
    _ ≤ (B * Real.log q) * (‖K.regularized (-(1 / 2))‖ * (1 / Real.sqrt x)) :=
      mul_le_mul_of_nonneg_right hb
        (mul_nonneg (norm_nonneg _) (div_nonneg zero_le_one (Real.sqrt_nonneg x)))
    _ = (‖K.regularized (-(1 / 2))‖ * B) * (Real.log q / Real.sqrt x) := by ring
    _ ≤ (1 + ‖K.regularized (-(1 / 2))‖ * B) * (Real.log q / Real.sqrt x) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
        (div_nonneg hlog (Real.sqrt_nonneg x))
    _ = _ := by ring

end PseudoPrime.LLS.PaperStatements.MellinKernel
