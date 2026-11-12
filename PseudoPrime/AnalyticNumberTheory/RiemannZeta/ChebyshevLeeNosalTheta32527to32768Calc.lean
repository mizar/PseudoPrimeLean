/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect32768
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope16384
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
def theta32527Cells : List LeeNosalCell :=
  [⟨32527, 32631, 32266667, 32627131, 365000, 365000⟩,
    ⟨32631, 32766, 32401137, 32736649, 365000, 365000⟩,
    ⟨32766, 32768, 32510655, 32736649, 365000, 365000⟩]

/-- The kernel-checked prefix bounds for 32507. -/
theorem theta32527_psi_32507_bounds :
    (32491967 : ℝ) / 1000 ≤ Chebyshev.psi 32507 ∧ Chebyshev.psi 32507 ≤ (32492661 : ℝ) / 1000 := by
  have hl : 2 ^ 46876 ≤ Nat.lcmUpto 32507 := by decide +kernel
  have hu : Nat.lcmUpto 32507 ≤ 2 ^ (46876 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32621. -/
theorem theta32527_psi_32621_bounds :
    (32626437 : ℝ) / 1000 ≤ Chebyshev.psi 32621 ∧ Chebyshev.psi 32621 ≤ (32627131 : ℝ) / 1000 := by
  have hl : 2 ^ 47070 ≤ Nat.lcmUpto 32621 := by decide +kernel
  have hu : Nat.lcmUpto 32621 ≤ 2 ^ (47070 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32761. -/
theorem theta32527_psi_32761_bounds :
    (32735955 : ℝ) / 1000 ≤ Chebyshev.psi 32761 ∧ Chebyshev.psi 32761 ≤ (32736649 : ℝ) / 1000 := by
  have hl : 2 ^ 47228 ≤ Nat.lcmUpto 32761 := by decide +kernel
  have hu : Nat.lcmUpto 32761 ≤ 2 ^ (47228 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta32527_lower : ∀ r ∈ theta32527Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta32527Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change (32266667 : ℝ) / 1000 ≤ Chebyshev.theta (↑(32527 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 32527) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32507) (b := 32527) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta32527_psi_32507_bounds.1]
  · change (32401137 : ℝ) / 1000 ≤ Chebyshev.theta (↑(32631 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 32631) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32621) (b := 32631) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta32527_psi_32621_bounds.1]
  · change (32510655 : ℝ) / 1000 ≤ Chebyshev.theta (↑(32766 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 32766) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32761) (b := 32766) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta32527_psi_32761_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta32527_upper :
    ∀ r ∈ theta32527Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta32527Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change Chebyshev.theta (↑(32630 : ℕ) : ℝ) ≤ (32627131 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 32630
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32621) (b := 32630) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta32527_psi_32621_bounds.2]
  · change Chebyshev.theta (↑(32765 : ℕ) : ℝ) ≤ (32736649 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 32765
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32761) (b := 32765) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta32527_psi_32761_bounds.2]
  · change Chebyshev.theta (↑(32767 : ℕ) : ℝ) ≤ (32736649 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 32767
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 32761) (b := 32767) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta32527_psi_32761_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta32527_a :
    ∀ r ∈ theta32527Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta32527Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32527 *
          (Real.log 32527 * (Real.log 32527 - Real.log (Real.log 32527)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32631 *
          (Real.log 32631 * (Real.log 32631 - Real.log (Real.log 32631)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32766 *
          (Real.log 32766 * (Real.log 32766 - Real.log (Real.log 32766)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta32527_b :
    ∀ r ∈ theta32527Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta32527Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32631 *
          (Real.log 32631 * (Real.log 32631 - Real.log (Real.log 32631)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32766 *
          (Real.log 32766 * (Real.log 32766 - Real.log (Real.log 32766)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 32768 *
          (Real.log 32768 * (Real.log 32768 - Real.log (Real.log 32768)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The cells form a checked chain covering `[32527, 32768)`. -/
theorem theta32527_check : leeNosalChainCheck 32527 32768 theta32527Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
