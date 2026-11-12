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
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal121to147

/-! # Batch certificate for Lee–Nosal psi cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
private def batchCells : List LeeNosalCell :=
  [⟨147, 149, 141402, 142096, 8000, 8000⟩, ⟨149, 154, 146254, 151800, 8000, 8000⟩,
    ⟨154, 159, 151106, 157345, 8000, 8000⟩, ⟨159, 164, 156651, 162197, 8000, 8000⟩,
    ⟨164, 169, 161503, 167049, 8000, 8000⟩, ⟨169, 177, 169127, 174674, 8000, 8000⟩,
    ⟨177, 181, 173979, 180219, 8000, 8000⟩, ⟨181, 191, 184377, 185071, 8000, 8000⟩,
    ⟨191, 197, 189922, 196161, 8000, 8000⟩, ⟨197, 199, 200319, 201013, 8000, 8000⟩,
    ⟨199, 211, 205864, 206558, 8000, 8000⟩, ⟨211, 219, 211409, 212104, 8000, 8000⟩]

/-- The kernel-checked prefix bounds for 139. -/
private theorem psi_139_bounds :
    (141402 : ℝ) / 1000 ≤ Chebyshev.psi 139 ∧ Chebyshev.psi 139 ≤ (142096 : ℝ) / 1000 := by
  have hl : 2 ^ 204 ≤ Nat.lcmUpto 139 := by decide +kernel
  have hu : Nat.lcmUpto 139 ≤ 2 ^ (204 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 149. -/
private theorem psi_149_bounds :
    (146254 : ℝ) / 1000 ≤ Chebyshev.psi 149 ∧ Chebyshev.psi 149 ≤ (146948 : ℝ) / 1000 := by
  have hl : 2 ^ 211 ≤ Nat.lcmUpto 149 := by decide +kernel
  have hu : Nat.lcmUpto 149 ≤ 2 ^ (211 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 151. -/
private theorem psi_151_bounds :
    (151106 : ℝ) / 1000 ≤ Chebyshev.psi 151 ∧ Chebyshev.psi 151 ≤ (151800 : ℝ) / 1000 := by
  have hl : 2 ^ 218 ≤ Nat.lcmUpto 151 := by decide +kernel
  have hu : Nat.lcmUpto 151 ≤ 2 ^ (218 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 157. -/
private theorem psi_157_bounds :
    (156651 : ℝ) / 1000 ≤ Chebyshev.psi 157 ∧ Chebyshev.psi 157 ≤ (157345 : ℝ) / 1000 := by
  have hl : 2 ^ 226 ≤ Nat.lcmUpto 157 := by decide +kernel
  have hu : Nat.lcmUpto 157 ≤ 2 ^ (226 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 163. -/
private theorem psi_163_bounds :
    (161503 : ℝ) / 1000 ≤ Chebyshev.psi 163 ∧ Chebyshev.psi 163 ≤ (162197 : ℝ) / 1000 := by
  have hl : 2 ^ 233 ≤ Nat.lcmUpto 163 := by decide +kernel
  have hu : Nat.lcmUpto 163 ≤ 2 ^ (233 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 167. -/
private theorem psi_167_bounds :
    (166355 : ℝ) / 1000 ≤ Chebyshev.psi 167 ∧ Chebyshev.psi 167 ≤ (167049 : ℝ) / 1000 := by
  have hl : 2 ^ 240 ≤ Nat.lcmUpto 167 := by decide +kernel
  have hu : Nat.lcmUpto 167 ≤ 2 ^ (240 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 169. -/
private theorem psi_169_bounds :
    (169127 : ℝ) / 1000 ≤ Chebyshev.psi 169 ∧ Chebyshev.psi 169 ≤ (169822 : ℝ) / 1000 := by
  have hl : 2 ^ 244 ≤ Nat.lcmUpto 169 := by decide +kernel
  have hu : Nat.lcmUpto 169 ≤ 2 ^ (244 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 173. -/
private theorem psi_173_bounds :
    (173979 : ℝ) / 1000 ≤ Chebyshev.psi 173 ∧ Chebyshev.psi 173 ≤ (174674 : ℝ) / 1000 := by
  have hl : 2 ^ 251 ≤ Nat.lcmUpto 173 := by decide +kernel
  have hu : Nat.lcmUpto 173 ≤ 2 ^ (251 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 179. -/
private theorem psi_179_bounds :
    (179525 : ℝ) / 1000 ≤ Chebyshev.psi 179 ∧ Chebyshev.psi 179 ≤ (180219 : ℝ) / 1000 := by
  have hl : 2 ^ 259 ≤ Nat.lcmUpto 179 := by decide +kernel
  have hu : Nat.lcmUpto 179 ≤ 2 ^ (259 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 181. -/
private theorem psi_181_bounds :
    (184377 : ℝ) / 1000 ≤ Chebyshev.psi 181 ∧ Chebyshev.psi 181 ≤ (185071 : ℝ) / 1000 := by
  have hl : 2 ^ 266 ≤ Nat.lcmUpto 181 := by decide +kernel
  have hu : Nat.lcmUpto 181 ≤ 2 ^ (266 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 191. -/
private theorem psi_191_bounds :
    (189922 : ℝ) / 1000 ≤ Chebyshev.psi 191 ∧ Chebyshev.psi 191 ≤ (190616 : ℝ) / 1000 := by
  have hl : 2 ^ 274 ≤ Nat.lcmUpto 191 := by decide +kernel
  have hu : Nat.lcmUpto 191 ≤ 2 ^ (274 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 193. -/
private theorem psi_193_bounds :
    (195467 : ℝ) / 1000 ≤ Chebyshev.psi 193 ∧ Chebyshev.psi 193 ≤ (196161 : ℝ) / 1000 := by
  have hl : 2 ^ 282 ≤ Nat.lcmUpto 193 := by decide +kernel
  have hu : Nat.lcmUpto 193 ≤ 2 ^ (282 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 197. -/
private theorem psi_197_bounds :
    (200319 : ℝ) / 1000 ≤ Chebyshev.psi 197 ∧ Chebyshev.psi 197 ≤ (201013 : ℝ) / 1000 := by
  have hl : 2 ^ 289 ≤ Nat.lcmUpto 197 := by decide +kernel
  have hu : Nat.lcmUpto 197 ≤ 2 ^ (289 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 199. -/
private theorem psi_199_bounds :
    (205864 : ℝ) / 1000 ≤ Chebyshev.psi 199 ∧ Chebyshev.psi 199 ≤ (206558 : ℝ) / 1000 := by
  have hl : 2 ^ 297 ≤ Nat.lcmUpto 199 := by decide +kernel
  have hu : Nat.lcmUpto 199 ≤ 2 ^ (297 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 211. -/
private theorem psi_211_bounds :
    (211409 : ℝ) / 1000 ≤ Chebyshev.psi 211 ∧ Chebyshev.psi 211 ≤ (212104 : ℝ) / 1000 := by
  have hl : 2 ^ 305 ≤ Nat.lcmUpto 211 := by decide +kernel
  have hu : Nat.lcmUpto 211 ≤ 2 ^ (305 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 147 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 147 ≤ t) :
    (8 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 147) (lo := 499 / 100) (hi := 5) (vlo := 8 / 5) (vhi :=
      161 / 100) (c := 8) (j := 8) (k := 3) (n := 32) (m := 32) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by decide +kernel)
      (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 147) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (141402 : ℝ) / 1000 ≤ Chebyshev.psi (↑(147 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 139) (b := 147) (by decide) (by decide +kernel)]
    exact psi_139_bounds.1
  · change (146254 : ℝ) / 1000 ≤ Chebyshev.psi (↑(149 : ℕ) : ℝ)
    exact psi_149_bounds.1
  · change (151106 : ℝ) / 1000 ≤ Chebyshev.psi (↑(154 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 151) (b := 154) (by decide) (by decide +kernel)]
    exact psi_151_bounds.1
  · change (156651 : ℝ) / 1000 ≤ Chebyshev.psi (↑(159 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 157) (b := 159) (by decide) (by decide +kernel)]
    exact psi_157_bounds.1
  · change (161503 : ℝ) / 1000 ≤ Chebyshev.psi (↑(164 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 163) (b := 164) (by decide) (by decide +kernel)]
    exact psi_163_bounds.1
  · change (169127 : ℝ) / 1000 ≤ Chebyshev.psi (↑(169 : ℕ) : ℝ)
    exact psi_169_bounds.1
  · change (173979 : ℝ) / 1000 ≤ Chebyshev.psi (↑(177 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 173) (b := 177) (by decide) (by decide +kernel)]
    exact psi_173_bounds.1
  · change (184377 : ℝ) / 1000 ≤ Chebyshev.psi (↑(181 : ℕ) : ℝ)
    exact psi_181_bounds.1
  · change (189922 : ℝ) / 1000 ≤ Chebyshev.psi (↑(191 : ℕ) : ℝ)
    exact psi_191_bounds.1
  · change (200319 : ℝ) / 1000 ≤ Chebyshev.psi (↑(197 : ℕ) : ℝ)
    exact psi_197_bounds.1
  · change (205864 : ℝ) / 1000 ≤ Chebyshev.psi (↑(199 : ℕ) : ℝ)
    exact psi_199_bounds.1
  · change (211409 : ℝ) / 1000 ≤ Chebyshev.psi (↑(211 : ℕ) : ℝ)
    exact psi_211_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(148 : ℕ) : ℝ) ≤ (142096 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 139) (b := 148) (by decide) (by decide +kernel)]
    exact psi_139_bounds.2
  · change Chebyshev.psi (↑(153 : ℕ) : ℝ) ≤ (151800 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 151) (b := 153) (by decide) (by decide +kernel)]
    exact psi_151_bounds.2
  · change Chebyshev.psi (↑(158 : ℕ) : ℝ) ≤ (157345 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 157) (b := 158) (by decide) (by decide +kernel)]
    exact psi_157_bounds.2
  · change Chebyshev.psi (↑(163 : ℕ) : ℝ) ≤ (162197 : ℝ) / 1000
    exact psi_163_bounds.2
  · change Chebyshev.psi (↑(168 : ℕ) : ℝ) ≤ (167049 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 167) (b := 168) (by decide) (by decide +kernel)]
    exact psi_167_bounds.2
  · change Chebyshev.psi (↑(176 : ℕ) : ℝ) ≤ (174674 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 173) (b := 176) (by decide) (by decide +kernel)]
    exact psi_173_bounds.2
  · change Chebyshev.psi (↑(180 : ℕ) : ℝ) ≤ (180219 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 179) (b := 180) (by decide) (by decide +kernel)]
    exact psi_179_bounds.2
  · change Chebyshev.psi (↑(190 : ℕ) : ℝ) ≤ (185071 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 181) (b := 190) (by decide) (by decide +kernel)]
    exact psi_181_bounds.2
  · change Chebyshev.psi (↑(196 : ℕ) : ℝ) ≤ (196161 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 193) (b := 196) (by decide) (by decide +kernel)]
    exact psi_193_bounds.2
  · change Chebyshev.psi (↑(198 : ℕ) : ℝ) ≤ (201013 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 197) (b := 198) (by decide) (by decide +kernel)]
    exact psi_197_bounds.2
  · change Chebyshev.psi (↑(210 : ℕ) : ℝ) ≤ (206558 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 199) (b := 210) (by decide) (by decide +kernel)]
    exact psi_199_bounds.2
  · change Chebyshev.psi (↑(218 : ℕ) : ℝ) ≤ (212104 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 211) (b := 218) (by decide) (by decide +kernel)]
    exact psi_211_bounds.2

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 147 * (Real.log 147 * (Real.log 147 - Real.log (Real.log 147)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 149 * (Real.log 149 * (Real.log 149 - Real.log (Real.log 149)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 154 * (Real.log 154 * (Real.log 154 - Real.log (Real.log 154)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 159 * (Real.log 159 * (Real.log 159 - Real.log (Real.log 159)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 164 * (Real.log 164 * (Real.log 164 - Real.log (Real.log 164)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 169 * (Real.log 169 * (Real.log 169 - Real.log (Real.log 169)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 177 * (Real.log 177 * (Real.log 177 - Real.log (Real.log 177)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 181 * (Real.log 181 * (Real.log 181 - Real.log (Real.log 181)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 191 * (Real.log 191 * (Real.log 191 - Real.log (Real.log 191)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 197 * (Real.log 197 * (Real.log 197 - Real.log (Real.log 197)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 199 * (Real.log 199 * (Real.log 199 - Real.log (Real.log 199)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 211 * (Real.log 211 * (Real.log 211 - Real.log (Real.log 211)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
private theorem batch_b :
    ∀ r ∈ batchCells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 149 * (Real.log 149 * (Real.log 149 - Real.log (Real.log 149)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 154 * (Real.log 154 * (Real.log 154 - Real.log (Real.log 154)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 159 * (Real.log 159 * (Real.log 159 - Real.log (Real.log 159)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 164 * (Real.log 164 * (Real.log 164 - Real.log (Real.log 164)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 169 * (Real.log 169 * (Real.log 169 - Real.log (Real.log 169)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 177 * (Real.log 177 * (Real.log 177 - Real.log (Real.log 177)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 181 * (Real.log 181 * (Real.log 181 - Real.log (Real.log 181)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 191 * (Real.log 191 * (Real.log 191 - Real.log (Real.log 191)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 197 * (Real.log 197 * (Real.log 197 - Real.log (Real.log 197)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 199 * (Real.log 199 * (Real.log 199 - Real.log (Real.log 199)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 211 * (Real.log 211 * (Real.log 211 - Real.log (Real.log 211)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (8000 : ℝ) / 1000 ≤
        Real.sqrt 219 * (Real.log 219 * (Real.log 219 - Real.log (Real.log 219)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[147, 219)`. -/
theorem psi_lee_nosal_147_219 {x : ℝ} (ha : 147 ≤ x) (hb : x < 219) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

/-- Combining adjacent certified batches gives the estimate on `[101, 219)`. -/
theorem psi_lee_nosal_101_219 {x : ℝ} (ha : 101 ≤ x) (hb : x < 219) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 147
  · exact psi_lee_nosal_101_147 ha h
  · exact psi_lee_nosal_147_219 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
