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
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks.LeeNosal113To121

/-! # Batch certificate for Lee–Nosal psi cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks

/-- The local cells store endpoint bounds in thousandths. -/
private def batchCells : List RiemannZeta.LeeNosalCell :=
  [⟨121, 125, 119221, 119915, 6500, 6500⟩, ⟨125, 127, 121300, 121994, 6500, 6500⟩,
    ⟨127, 132, 126152, 132392, 6500, 6500⟩, ⟨132, 138, 131697, 137244, 6500, 6500⟩,
    ⟨138, 143, 136549, 142096, 6500, 6500⟩, ⟨143, 147, 141402, 142096, 6500, 6500⟩]

/-- The kernel-checked prefix bounds for 121. -/
private theorem psi_121_bounds :
    (119221 : ℝ) / 1000 ≤ Chebyshev.psi 121 ∧ Chebyshev.psi 121 ≤ (119915 : ℝ) / 1000 := by
  have hl : 2 ^ 172 ≤ Nat.lcmUpto 121 := by decide +kernel
  have hu : Nat.lcmUpto 121 ≤ 2 ^ (172 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 125. -/
private theorem psi_125_bounds :
    (121300 : ℝ) / 1000 ≤ Chebyshev.psi 125 ∧ Chebyshev.psi 125 ≤ (121994 : ℝ) / 1000 := by
  have hl : 2 ^ 175 ≤ Nat.lcmUpto 125 := by decide +kernel
  have hu : Nat.lcmUpto 125 ≤ 2 ^ (175 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 127. -/
private theorem psi_127_bounds :
    (126152 : ℝ) / 1000 ≤ Chebyshev.psi 127 ∧ Chebyshev.psi 127 ≤ (126846 : ℝ) / 1000 := by
  have hl : 2 ^ 182 ≤ Nat.lcmUpto 127 := by decide +kernel
  have hu : Nat.lcmUpto 127 ≤ 2 ^ (182 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 131. -/
private theorem psi_131_bounds :
    (131697 : ℝ) / 1000 ≤ Chebyshev.psi 131 ∧ Chebyshev.psi 131 ≤ (132392 : ℝ) / 1000 := by
  have hl : 2 ^ 190 ≤ Nat.lcmUpto 131 := by decide +kernel
  have hu : Nat.lcmUpto 131 ≤ 2 ^ (190 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 137. -/
private theorem psi_137_bounds :
    (136549 : ℝ) / 1000 ≤ Chebyshev.psi 137 ∧ Chebyshev.psi 137 ≤ (137244 : ℝ) / 1000 := by
  have hl : 2 ^ 197 ≤ Nat.lcmUpto 137 := by decide +kernel
  have hu : Nat.lcmUpto 137 ≤ 2 ^ (197 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 139. -/
private theorem psi_139_bounds :
    (141402 : ℝ) / 1000 ≤ Chebyshev.psi 139 ∧ Chebyshev.psi 139 ≤ (142096 : ℝ) / 1000 := by
  have hl : 2 ^ 204 ≤ Nat.lcmUpto 139 := by decide +kernel
  have hu : Nat.lcmUpto 139 ≤ 2 ^ (204 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 121 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 121 ≤ t) :
    (13 / 2 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    RiemannZeta.lee_nosal_envelope_of_log_checks (N := 121) (lo := 479 / 100) (hi := 24 / 5) (vlo :=
      39 / 25) (vhi := 157 / 100) (c := 13 / 2) (j := 7) (k := 3) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (RiemannZeta.lee_nosal_envelope_mono (x := 121) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · change (119221 : ℝ) / 1000 ≤ Chebyshev.psi (↑(121 : ℕ) : ℝ)
    exact psi_121_bounds.1
  · change (121300 : ℝ) / 1000 ≤ Chebyshev.psi (↑(125 : ℕ) : ℝ)
    exact psi_125_bounds.1
  · change (126152 : ℝ) / 1000 ≤ Chebyshev.psi (↑(127 : ℕ) : ℝ)
    exact psi_127_bounds.1
  · change (131697 : ℝ) / 1000 ≤ Chebyshev.psi (↑(132 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 131) (b := 132) (by decide) (by decide +kernel)]
    exact psi_131_bounds.1
  · change (136549 : ℝ) / 1000 ≤ Chebyshev.psi (↑(138 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 137) (b := 138) (by decide) (by decide +kernel)]
    exact psi_137_bounds.1
  · change (141402 : ℝ) / 1000 ≤ Chebyshev.psi (↑(143 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 139) (b := 143) (by decide) (by decide +kernel)]
    exact psi_139_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(124 : ℕ) : ℝ) ≤ (119915 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 121) (b := 124) (by decide) (by decide +kernel)]
    exact psi_121_bounds.2
  · change Chebyshev.psi (↑(126 : ℕ) : ℝ) ≤ (121994 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 125) (b := 126) (by decide) (by decide +kernel)]
    exact psi_125_bounds.2
  · change Chebyshev.psi (↑(131 : ℕ) : ℝ) ≤ (132392 : ℝ) / 1000
    exact psi_131_bounds.2
  · change Chebyshev.psi (↑(137 : ℕ) : ℝ) ≤ (137244 : ℝ) / 1000
    exact psi_137_bounds.2
  · change Chebyshev.psi (↑(142 : ℕ) : ℝ) ≤ (142096 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 139) (b := 142) (by decide) (by decide +kernel)]
    exact psi_139_bounds.2
  · change Chebyshev.psi (↑(146 : ℕ) : ℝ) ≤ (142096 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 139) (b := 146) (by decide) (by decide +kernel)]
    exact psi_139_bounds.2

/-- The envelope lower bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (6500 : ℝ) / 1000 ≤
        Real.sqrt 121 * (Real.log 121 * (Real.log 121 - Real.log (Real.log 121)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (6500 : ℝ) / 1000 ≤
        Real.sqrt 125 * (Real.log 125 * (Real.log 125 - Real.log (Real.log 125)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (6500 : ℝ) / 1000 ≤
        Real.sqrt 127 * (Real.log 127 * (Real.log 127 - Real.log (Real.log 127)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (6500 : ℝ) / 1000 ≤
        Real.sqrt 132 * (Real.log 132 * (Real.log 132 - Real.log (Real.log 132)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (6500 : ℝ) / 1000 ≤
        Real.sqrt 138 * (Real.log 138 * (Real.log 138 - Real.log (Real.log 138)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (6500 : ℝ) / 1000 ≤
        Real.sqrt 143 * (Real.log 143 * (Real.log 143 - Real.log (Real.log 143)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The envelope lower bound applies at every cell b endpoint. -/
private theorem batch_b :
    ∀ r ∈ batchCells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (6500 : ℝ) / 1000 ≤
        Real.sqrt 125 * (Real.log 125 * (Real.log 125 - Real.log (Real.log 125)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (6500 : ℝ) / 1000 ≤
        Real.sqrt 127 * (Real.log 127 * (Real.log 127 - Real.log (Real.log 127)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (6500 : ℝ) / 1000 ≤
        Real.sqrt 132 * (Real.log 132 * (Real.log 132 - Real.log (Real.log 132)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (6500 : ℝ) / 1000 ≤
        Real.sqrt 138 * (Real.log 138 * (Real.log 138 - Real.log (Real.log 138)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (6500 : ℝ) / 1000 ≤
        Real.sqrt 143 * (Real.log 143 * (Real.log 143 - Real.log (Real.log 143)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (6500 : ℝ) / 1000 ≤
        Real.sqrt 147 * (Real.log 147 * (Real.log 147 - Real.log (Real.log 147)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[121, 147)`. -/
theorem bound_121_147 {x : ℝ} (ha : 121 ≤ x) (hb : x < 147) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    RiemannZeta.lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor
      (by decide +kernel) batch_lower batch_upper batch_a batch_b ha hb

/-- Combining adjoining certified batches gives the estimate on `[101, 147)`. -/
theorem bound_101_147 {x : ℝ} (ha : 101 ≤ x) (hb : x < 147) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 121
  · exact bound_101_121 ha h
  · exact bound_121_147 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks
