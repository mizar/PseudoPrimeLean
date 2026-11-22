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
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks.LeeNosal147To219

/-! # Batch certificate for Lee–Nosal psi cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks

/-- The local cells store endpoint bounds in thousandths. -/
private def batchCells : List RiemannZeta.LeeNosalCell :=
  [⟨219, 223, 211409, 212104, 11700, 11700⟩, ⟨223, 227, 216261, 216956, 11700, 11700⟩,
    ⟨227, 233, 221807, 228046, 11700, 11700⟩, ⟨233, 243, 232897, 244681, 11700, 11700⟩,
    ⟨243, 256, 244680, 250920, 11700, 11700⟩, ⟨256, 262, 250919, 257158, 11700, 11700⟩,
    ⟨262, 268, 256464, 262703, 11700, 11700⟩, ⟨268, 273, 262009, 274487, 11700, 11700⟩,
    ⟨273, 281, 273793, 280032, 11700, 11700⟩, ⟨281, 289, 284883, 291122, 11700, 11700⟩,
    ⟨289, 304, 293201, 299440, 11700, 11700⟩, ⟨304, 310, 298746, 304985, 11700, 11700⟩,
    ⟨310, 315, 304291, 316769, 11700, 11700⟩, ⟨315, 327, 316075, 322314, 11700, 11700⟩]

/-- The kernel-checked prefix bounds for 211. -/
private theorem psi_211_bounds :
    (211409 : ℝ) / 1000 ≤ Chebyshev.psi 211 ∧ Chebyshev.psi 211 ≤ (212104 : ℝ) / 1000 := by
  have hl : 2 ^ 305 ≤ Nat.lcmUpto 211 := by decide +kernel
  have hu : Nat.lcmUpto 211 ≤ 2 ^ (305 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 223. -/
private theorem psi_223_bounds :
    (216261 : ℝ) / 1000 ≤ Chebyshev.psi 223 ∧ Chebyshev.psi 223 ≤ (216956 : ℝ) / 1000 := by
  have hl : 2 ^ 312 ≤ Nat.lcmUpto 223 := by decide +kernel
  have hu : Nat.lcmUpto 223 ≤ 2 ^ (312 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 227. -/
private theorem psi_227_bounds :
    (221807 : ℝ) / 1000 ≤ Chebyshev.psi 227 ∧ Chebyshev.psi 227 ≤ (222501 : ℝ) / 1000 := by
  have hl : 2 ^ 320 ≤ Nat.lcmUpto 227 := by decide +kernel
  have hu : Nat.lcmUpto 227 ≤ 2 ^ (320 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 229. -/
private theorem psi_229_bounds :
    (227352 : ℝ) / 1000 ≤ Chebyshev.psi 229 ∧ Chebyshev.psi 229 ≤ (228046 : ℝ) / 1000 := by
  have hl : 2 ^ 328 ≤ Nat.lcmUpto 229 := by decide +kernel
  have hu : Nat.lcmUpto 229 ≤ 2 ^ (328 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 233. -/
private theorem psi_233_bounds :
    (232897 : ℝ) / 1000 ≤ Chebyshev.psi 233 ∧ Chebyshev.psi 233 ≤ (233591 : ℝ) / 1000 := by
  have hl : 2 ^ 336 ≤ Nat.lcmUpto 233 := by decide +kernel
  have hu : Nat.lcmUpto 233 ≤ 2 ^ (336 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 241. -/
private theorem psi_241_bounds :
    (243987 : ℝ) / 1000 ≤ Chebyshev.psi 241 ∧ Chebyshev.psi 241 ≤ (244681 : ℝ) / 1000 := by
  have hl : 2 ^ 352 ≤ Nat.lcmUpto 241 := by decide +kernel
  have hu : Nat.lcmUpto 241 ≤ 2 ^ (352 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 243. -/
private theorem psi_243_bounds :
    (244680 : ℝ) / 1000 ≤ Chebyshev.psi 243 ∧ Chebyshev.psi 243 ≤ (245375 : ℝ) / 1000 := by
  have hl : 2 ^ 353 ≤ Nat.lcmUpto 243 := by decide +kernel
  have hu : Nat.lcmUpto 243 ≤ 2 ^ (353 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 251. -/
private theorem psi_251_bounds :
    (250226 : ℝ) / 1000 ≤ Chebyshev.psi 251 ∧ Chebyshev.psi 251 ≤ (250920 : ℝ) / 1000 := by
  have hl : 2 ^ 361 ≤ Nat.lcmUpto 251 := by decide +kernel
  have hu : Nat.lcmUpto 251 ≤ 2 ^ (361 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 256. -/
private theorem psi_256_bounds :
    (250919 : ℝ) / 1000 ≤ Chebyshev.psi 256 ∧ Chebyshev.psi 256 ≤ (251613 : ℝ) / 1000 := by
  have hl : 2 ^ 362 ≤ Nat.lcmUpto 256 := by decide +kernel
  have hu : Nat.lcmUpto 256 ≤ 2 ^ (362 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 257. -/
private theorem psi_257_bounds :
    (256464 : ℝ) / 1000 ≤ Chebyshev.psi 257 ∧ Chebyshev.psi 257 ≤ (257158 : ℝ) / 1000 := by
  have hl : 2 ^ 370 ≤ Nat.lcmUpto 257 := by decide +kernel
  have hu : Nat.lcmUpto 257 ≤ 2 ^ (370 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 263. -/
private theorem psi_263_bounds :
    (262009 : ℝ) / 1000 ≤ Chebyshev.psi 263 ∧ Chebyshev.psi 263 ≤ (262703 : ℝ) / 1000 := by
  have hl : 2 ^ 378 ≤ Nat.lcmUpto 263 := by decide +kernel
  have hu : Nat.lcmUpto 263 ≤ 2 ^ (378 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 271. -/
private theorem psi_271_bounds :
    (273793 : ℝ) / 1000 ≤ Chebyshev.psi 271 ∧ Chebyshev.psi 271 ≤ (274487 : ℝ) / 1000 := by
  have hl : 2 ^ 395 ≤ Nat.lcmUpto 271 := by decide +kernel
  have hu : Nat.lcmUpto 271 ≤ 2 ^ (395 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 277. -/
private theorem psi_277_bounds :
    (279338 : ℝ) / 1000 ≤ Chebyshev.psi 277 ∧ Chebyshev.psi 277 ≤ (280032 : ℝ) / 1000 := by
  have hl : 2 ^ 403 ≤ Nat.lcmUpto 277 := by decide +kernel
  have hu : Nat.lcmUpto 277 ≤ 2 ^ (403 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 281. -/
private theorem psi_281_bounds :
    (284883 : ℝ) / 1000 ≤ Chebyshev.psi 281 ∧ Chebyshev.psi 281 ≤ (285577 : ℝ) / 1000 := by
  have hl : 2 ^ 411 ≤ Nat.lcmUpto 281 := by decide +kernel
  have hu : Nat.lcmUpto 281 ≤ 2 ^ (411 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 283. -/
private theorem psi_283_bounds :
    (290428 : ℝ) / 1000 ≤ Chebyshev.psi 283 ∧ Chebyshev.psi 283 ≤ (291122 : ℝ) / 1000 := by
  have hl : 2 ^ 419 ≤ Nat.lcmUpto 283 := by decide +kernel
  have hu : Nat.lcmUpto 283 ≤ 2 ^ (419 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 289. -/
private theorem psi_289_bounds :
    (293201 : ℝ) / 1000 ≤ Chebyshev.psi 289 ∧ Chebyshev.psi 289 ≤ (293895 : ℝ) / 1000 := by
  have hl : 2 ^ 423 ≤ Nat.lcmUpto 289 := by decide +kernel
  have hu : Nat.lcmUpto 289 ≤ 2 ^ (423 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 293. -/
private theorem psi_293_bounds :
    (298746 : ℝ) / 1000 ≤ Chebyshev.psi 293 ∧ Chebyshev.psi 293 ≤ (299440 : ℝ) / 1000 := by
  have hl : 2 ^ 431 ≤ Nat.lcmUpto 293 := by decide +kernel
  have hu : Nat.lcmUpto 293 ≤ 2 ^ (431 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 307. -/
private theorem psi_307_bounds :
    (304291 : ℝ) / 1000 ≤ Chebyshev.psi 307 ∧ Chebyshev.psi 307 ≤ (304985 : ℝ) / 1000 := by
  have hl : 2 ^ 439 ≤ Nat.lcmUpto 307 := by decide +kernel
  have hu : Nat.lcmUpto 307 ≤ 2 ^ (439 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 313. -/
private theorem psi_313_bounds :
    (316075 : ℝ) / 1000 ≤ Chebyshev.psi 313 ∧ Chebyshev.psi 313 ≤ (316769 : ℝ) / 1000 := by
  have hl : 2 ^ 456 ≤ Nat.lcmUpto 313 := by decide +kernel
  have hu : Nat.lcmUpto 313 ≤ 2 ^ (456 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 317. -/
private theorem psi_317_bounds :
    (321620 : ℝ) / 1000 ≤ Chebyshev.psi 317 ∧ Chebyshev.psi 317 ≤ (322314 : ℝ) / 1000 := by
  have hl : 2 ^ 464 ≤ Nat.lcmUpto 317 := by decide +kernel
  have hu : Nat.lcmUpto 317 ≤ 2 ^ (464 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 219 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 219 ≤ t) :
    (117 / 10 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    RiemannZeta.lee_nosal_envelope_of_log_checks (N := 219) (lo := 5389 / 1000) (hi := 539 / 100)
      (vlo := 168 / 100) (vhi := 169 / 100) (c := 117 / 10) (j := 8) (k := 3) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (RiemannZeta.lee_nosal_envelope_mono (x := 219) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (211409 : ℝ) / 1000 ≤ Chebyshev.psi (↑(219 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 211) (b := 219) (by decide) (by decide +kernel)]
    exact psi_211_bounds.1
  · change (216261 : ℝ) / 1000 ≤ Chebyshev.psi (↑(223 : ℕ) : ℝ)
    exact psi_223_bounds.1
  · change (221807 : ℝ) / 1000 ≤ Chebyshev.psi (↑(227 : ℕ) : ℝ)
    exact psi_227_bounds.1
  · change (232897 : ℝ) / 1000 ≤ Chebyshev.psi (↑(233 : ℕ) : ℝ)
    exact psi_233_bounds.1
  · change (244680 : ℝ) / 1000 ≤ Chebyshev.psi (↑(243 : ℕ) : ℝ)
    exact psi_243_bounds.1
  · change (250919 : ℝ) / 1000 ≤ Chebyshev.psi (↑(256 : ℕ) : ℝ)
    exact psi_256_bounds.1
  · change (256464 : ℝ) / 1000 ≤ Chebyshev.psi (↑(262 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 257) (b := 262) (by decide) (by decide +kernel)]
    exact psi_257_bounds.1
  · change (262009 : ℝ) / 1000 ≤ Chebyshev.psi (↑(268 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 263) (b := 268) (by decide) (by decide +kernel)]
    exact psi_263_bounds.1
  · change (273793 : ℝ) / 1000 ≤ Chebyshev.psi (↑(273 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 271) (b := 273) (by decide) (by decide +kernel)]
    exact psi_271_bounds.1
  · change (284883 : ℝ) / 1000 ≤ Chebyshev.psi (↑(281 : ℕ) : ℝ)
    exact psi_281_bounds.1
  · change (293201 : ℝ) / 1000 ≤ Chebyshev.psi (↑(289 : ℕ) : ℝ)
    exact psi_289_bounds.1
  · change (298746 : ℝ) / 1000 ≤ Chebyshev.psi (↑(304 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 293) (b := 304) (by decide) (by decide +kernel)]
    exact psi_293_bounds.1
  · change (304291 : ℝ) / 1000 ≤ Chebyshev.psi (↑(310 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 307) (b := 310) (by decide) (by decide +kernel)]
    exact psi_307_bounds.1
  · change (316075 : ℝ) / 1000 ≤ Chebyshev.psi (↑(315 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 313) (b := 315) (by decide) (by decide +kernel)]
    exact psi_313_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(222 : ℕ) : ℝ) ≤ (212104 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 211) (b := 222) (by decide) (by decide +kernel)]
    exact psi_211_bounds.2
  · change Chebyshev.psi (↑(226 : ℕ) : ℝ) ≤ (216956 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 223) (b := 226) (by decide) (by decide +kernel)]
    exact psi_223_bounds.2
  · change Chebyshev.psi (↑(232 : ℕ) : ℝ) ≤ (228046 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 229) (b := 232) (by decide) (by decide +kernel)]
    exact psi_229_bounds.2
  · change Chebyshev.psi (↑(242 : ℕ) : ℝ) ≤ (244681 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 241) (b := 242) (by decide) (by decide +kernel)]
    exact psi_241_bounds.2
  · change Chebyshev.psi (↑(255 : ℕ) : ℝ) ≤ (250920 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 251) (b := 255) (by decide) (by decide +kernel)]
    exact psi_251_bounds.2
  · change Chebyshev.psi (↑(261 : ℕ) : ℝ) ≤ (257158 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 257) (b := 261) (by decide) (by decide +kernel)]
    exact psi_257_bounds.2
  · change Chebyshev.psi (↑(267 : ℕ) : ℝ) ≤ (262703 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 263) (b := 267) (by decide) (by decide +kernel)]
    exact psi_263_bounds.2
  · change Chebyshev.psi (↑(272 : ℕ) : ℝ) ≤ (274487 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 271) (b := 272) (by decide) (by decide +kernel)]
    exact psi_271_bounds.2
  · change Chebyshev.psi (↑(280 : ℕ) : ℝ) ≤ (280032 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 277) (b := 280) (by decide) (by decide +kernel)]
    exact psi_277_bounds.2
  · change Chebyshev.psi (↑(288 : ℕ) : ℝ) ≤ (291122 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 283) (b := 288) (by decide) (by decide +kernel)]
    exact psi_283_bounds.2
  · change Chebyshev.psi (↑(303 : ℕ) : ℝ) ≤ (299440 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 293) (b := 303) (by decide) (by decide +kernel)]
    exact psi_293_bounds.2
  · change Chebyshev.psi (↑(309 : ℕ) : ℝ) ≤ (304985 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 307) (b := 309) (by decide) (by decide +kernel)]
    exact psi_307_bounds.2
  · change Chebyshev.psi (↑(314 : ℕ) : ℝ) ≤ (316769 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 313) (b := 314) (by decide) (by decide +kernel)]
    exact psi_313_bounds.2
  · change Chebyshev.psi (↑(326 : ℕ) : ℝ) ≤ (322314 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 317) (b := 326) (by decide) (by decide +kernel)]
    exact psi_317_bounds.2

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 219 * (Real.log 219 * (Real.log 219 - Real.log (Real.log 219)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 223 * (Real.log 223 * (Real.log 223 - Real.log (Real.log 223)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 227 * (Real.log 227 * (Real.log 227 - Real.log (Real.log 227)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 233 * (Real.log 233 * (Real.log 233 - Real.log (Real.log 233)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 243 * (Real.log 243 * (Real.log 243 - Real.log (Real.log 243)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 256 * (Real.log 256 * (Real.log 256 - Real.log (Real.log 256)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 262 * (Real.log 262 * (Real.log 262 - Real.log (Real.log 262)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 268 * (Real.log 268 * (Real.log 268 - Real.log (Real.log 268)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 273 * (Real.log 273 * (Real.log 273 - Real.log (Real.log 273)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 281 * (Real.log 281 * (Real.log 281 - Real.log (Real.log 281)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 289 * (Real.log 289 * (Real.log 289 - Real.log (Real.log 289)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 304 * (Real.log 304 * (Real.log 304 - Real.log (Real.log 304)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 310 * (Real.log 310 * (Real.log 310 - Real.log (Real.log 310)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 315 * (Real.log 315 * (Real.log 315 - Real.log (Real.log 315)) / (8 * Real.pi))
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
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 223 * (Real.log 223 * (Real.log 223 - Real.log (Real.log 223)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 227 * (Real.log 227 * (Real.log 227 - Real.log (Real.log 227)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 233 * (Real.log 233 * (Real.log 233 - Real.log (Real.log 233)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 243 * (Real.log 243 * (Real.log 243 - Real.log (Real.log 243)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 256 * (Real.log 256 * (Real.log 256 - Real.log (Real.log 256)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 262 * (Real.log 262 * (Real.log 262 - Real.log (Real.log 262)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 268 * (Real.log 268 * (Real.log 268 - Real.log (Real.log 268)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 273 * (Real.log 273 * (Real.log 273 - Real.log (Real.log 273)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 281 * (Real.log 281 * (Real.log 281 - Real.log (Real.log 281)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 289 * (Real.log 289 * (Real.log 289 - Real.log (Real.log 289)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 304 * (Real.log 304 * (Real.log 304 - Real.log (Real.log 304)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 310 * (Real.log 310 * (Real.log 310 - Real.log (Real.log 310)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 315 * (Real.log 315 * (Real.log 315 - Real.log (Real.log 315)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (11700 : ℝ) / 1000 ≤
        Real.sqrt 327 * (Real.log 327 * (Real.log 327 - Real.log (Real.log 327)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[219, 327)`. -/
theorem bound_219_327 {x : ℝ} (ha : 219 ≤ x) (hb : x < 327) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    RiemannZeta.lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor
      (by decide +kernel) batch_lower batch_upper batch_a batch_b ha hb

/-- Combining adjacent certified batches gives the estimate on `[101, 327)`. -/
theorem bound_101_327 {x : ℝ} (ha : 101 ≤ x) (hb : x < 327) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 219
  · exact bound_101_219 ha h
  · exact bound_219_327 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks
