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

/-! # Batch certificate for Lee–Nosal psi cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
private def batchCells : List LeeNosalCell :=
  [⟨17761, 18127, 17769521, 18132731, 380000, 380000⟩,
    ⟨18127, 18457, 18141741, 18505644, 380000, 380000⟩,
    ⟨18457, 18859, 18514654, 18834889, 380000, 380000⟩,
    ⟨18859, 19224, 18844592, 19160668, 380000, 380000⟩,
    ⟨19224, 19539, 19159974, 19510707, 380000, 380000⟩,
    ⟨19539, 19890, 19510013, 19848270, 380000, 380000⟩,
    ⟨19890, 20227, 19847576, 20214945, 380000, 380000⟩,
    ⟨20227, 20594, 20214251, 20571916, 380000, 380000⟩,
    ⟨20594, 20951, 20571222, 20910172, 380000, 380000⟩,
    ⟨20951, 21289, 20909477, 21258131, 380000, 380000⟩,
    ⟨21289, 21637, 21257437, 21637283, 380000, 380000⟩,
    ⟨21637, 22016, 21636589, 22007423, 380000, 380000⟩]

/-- The kernel-checked prefix bounds for 17761. -/
private theorem psi_17761_bounds :
    (17769521 : ℝ) / 1000 ≤ Chebyshev.psi 17761 ∧ Chebyshev.psi 17761 ≤ (17770215 : ℝ) / 1000 := by
  have hl : 2 ^ 25636 ≤ Nat.lcmUpto 17761 := by decide +kernel
  have hu : Nat.lcmUpto 17761 ≤ 2 ^ (25636 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 18121. -/
private theorem psi_18121_bounds :
    (18132037 : ℝ) / 1000 ≤ Chebyshev.psi 18121 ∧ Chebyshev.psi 18121 ≤ (18132731 : ℝ) / 1000 := by
  have hl : 2 ^ 26159 ≤ Nat.lcmUpto 18121 := by decide +kernel
  have hu : Nat.lcmUpto 18121 ≤ 2 ^ (26159 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 18127. -/
private theorem psi_18127_bounds :
    (18141741 : ℝ) / 1000 ≤ Chebyshev.psi 18127 ∧ Chebyshev.psi 18127 ≤ (18142435 : ℝ) / 1000 := by
  have hl : 2 ^ 26173 ≤ Nat.lcmUpto 18127 := by decide +kernel
  have hu : Nat.lcmUpto 18127 ≤ 2 ^ (26173 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 18451. -/
private theorem psi_18451_bounds :
    (18504950 : ℝ) / 1000 ≤ Chebyshev.psi 18451 ∧ Chebyshev.psi 18451 ≤ (18505644 : ℝ) / 1000 := by
  have hl : 2 ^ 26697 ≤ Nat.lcmUpto 18451 := by decide +kernel
  have hu : Nat.lcmUpto 18451 ≤ 2 ^ (26697 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 18457. -/
private theorem psi_18457_bounds :
    (18514654 : ℝ) / 1000 ≤ Chebyshev.psi 18457 ∧ Chebyshev.psi 18457 ≤ (18515348 : ℝ) / 1000 := by
  have hl : 2 ^ 26711 ≤ Nat.lcmUpto 18457 := by decide +kernel
  have hu : Nat.lcmUpto 18457 ≤ 2 ^ (26711 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 18839. -/
private theorem psi_18839_bounds :
    (18834195 : ℝ) / 1000 ≤ Chebyshev.psi 18839 ∧ Chebyshev.psi 18839 ≤ (18834889 : ℝ) / 1000 := by
  have hl : 2 ^ 27172 ≤ Nat.lcmUpto 18839 := by decide +kernel
  have hu : Nat.lcmUpto 18839 ≤ 2 ^ (27172 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 18859. -/
private theorem psi_18859_bounds :
    (18844592 : ℝ) / 1000 ≤ Chebyshev.psi 18859 ∧ Chebyshev.psi 18859 ≤ (18845286 : ℝ) / 1000 := by
  have hl : 2 ^ 27187 ≤ Nat.lcmUpto 18859 := by decide +kernel
  have hu : Nat.lcmUpto 18859 ≤ 2 ^ (27187 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19219. -/
private theorem psi_19219_bounds :
    (19159974 : ℝ) / 1000 ≤ Chebyshev.psi 19219 ∧ Chebyshev.psi 19219 ≤ (19160668 : ℝ) / 1000 := by
  have hl : 2 ^ 27642 ≤ Nat.lcmUpto 19219 := by decide +kernel
  have hu : Nat.lcmUpto 19219 ≤ 2 ^ (27642 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19531. -/
private theorem psi_19531_bounds :
    (19510013 : ℝ) / 1000 ≤ Chebyshev.psi 19531 ∧ Chebyshev.psi 19531 ≤ (19510707 : ℝ) / 1000 := by
  have hl : 2 ^ 28147 ≤ Nat.lcmUpto 19531 := by decide +kernel
  have hu : Nat.lcmUpto 19531 ≤ 2 ^ (28147 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19889. -/
private theorem psi_19889_bounds :
    (19847576 : ℝ) / 1000 ≤ Chebyshev.psi 19889 ∧ Chebyshev.psi 19889 ≤ (19848270 : ℝ) / 1000 := by
  have hl : 2 ^ 28634 ≤ Nat.lcmUpto 19889 := by decide +kernel
  have hu : Nat.lcmUpto 19889 ≤ 2 ^ (28634 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 20219. -/
private theorem psi_20219_bounds :
    (20214251 : ℝ) / 1000 ≤ Chebyshev.psi 20219 ∧ Chebyshev.psi 20219 ≤ (20214945 : ℝ) / 1000 := by
  have hl : 2 ^ 29163 ≤ Nat.lcmUpto 20219 := by decide +kernel
  have hu : Nat.lcmUpto 20219 ≤ 2 ^ (29163 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 20593. -/
private theorem psi_20593_bounds :
    (20571222 : ℝ) / 1000 ≤ Chebyshev.psi 20593 ∧ Chebyshev.psi 20593 ≤ (20571916 : ℝ) / 1000 := by
  have hl : 2 ^ 29678 ≤ Nat.lcmUpto 20593 := by decide +kernel
  have hu : Nat.lcmUpto 20593 ≤ 2 ^ (29678 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 20947. -/
private theorem psi_20947_bounds :
    (20909477 : ℝ) / 1000 ≤ Chebyshev.psi 20947 ∧ Chebyshev.psi 20947 ≤ (20910172 : ℝ) / 1000 := by
  have hl : 2 ^ 30166 ≤ Nat.lcmUpto 20947 := by decide +kernel
  have hu : Nat.lcmUpto 20947 ≤ 2 ^ (30166 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 21283. -/
private theorem psi_21283_bounds :
    (21257437 : ℝ) / 1000 ≤ Chebyshev.psi 21283 ∧ Chebyshev.psi 21283 ≤ (21258131 : ℝ) / 1000 := by
  have hl : 2 ^ 30668 ≤ Nat.lcmUpto 21283 := by decide +kernel
  have hu : Nat.lcmUpto 21283 ≤ 2 ^ (30668 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 21617. -/
private theorem psi_21617_bounds :
    (21636589 : ℝ) / 1000 ≤ Chebyshev.psi 21617 ∧ Chebyshev.psi 21617 ≤ (21637283 : ℝ) / 1000 := by
  have hl : 2 ^ 31215 ≤ Nat.lcmUpto 21617 := by decide +kernel
  have hu : Nat.lcmUpto 21617 ≤ 2 ^ (31215 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 22013. -/
private theorem psi_22013_bounds :
    (22006729 : ℝ) / 1000 ≤ Chebyshev.psi 22013 ∧ Chebyshev.psi 22013 ≤ (22007423 : ℝ) / 1000 := by
  have hl : 2 ^ 31749 ≤ Nat.lcmUpto 22013 := by decide +kernel
  have hu : Nat.lcmUpto 22013 ≤ 2 ^ (31749 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 17761 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 17761 ≤ t) :
    (380 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 17761) (lo := 978 / 100) (hi := 979 / 100) (vlo :=
      228 / 100) (vhi := 229 / 100) (c := 380) (j := 15) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 17761) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (17769521 : ℝ) / 1000 ≤ Chebyshev.psi (↑(17761 : ℕ) : ℝ)
    exact psi_17761_bounds.1
  · change (18141741 : ℝ) / 1000 ≤ Chebyshev.psi (↑(18127 : ℕ) : ℝ)
    exact psi_18127_bounds.1
  · change (18514654 : ℝ) / 1000 ≤ Chebyshev.psi (↑(18457 : ℕ) : ℝ)
    exact psi_18457_bounds.1
  · change (18844592 : ℝ) / 1000 ≤ Chebyshev.psi (↑(18859 : ℕ) : ℝ)
    exact psi_18859_bounds.1
  · change (19159974 : ℝ) / 1000 ≤ Chebyshev.psi (↑(19224 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 19219) (b := 19224) (by decide)
        (by decide +kernel)]
    exact psi_19219_bounds.1
  · change (19510013 : ℝ) / 1000 ≤ Chebyshev.psi (↑(19539 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 19531) (b := 19539) (by decide)
        (by decide +kernel)]
    exact psi_19531_bounds.1
  · change (19847576 : ℝ) / 1000 ≤ Chebyshev.psi (↑(19890 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 19889) (b := 19890) (by decide)
        (by decide +kernel)]
    exact psi_19889_bounds.1
  · change (20214251 : ℝ) / 1000 ≤ Chebyshev.psi (↑(20227 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 20219) (b := 20227) (by decide)
        (by decide +kernel)]
    exact psi_20219_bounds.1
  · change (20571222 : ℝ) / 1000 ≤ Chebyshev.psi (↑(20594 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 20593) (b := 20594) (by decide)
        (by decide +kernel)]
    exact psi_20593_bounds.1
  · change (20909477 : ℝ) / 1000 ≤ Chebyshev.psi (↑(20951 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 20947) (b := 20951) (by decide)
        (by decide +kernel)]
    exact psi_20947_bounds.1
  · change (21257437 : ℝ) / 1000 ≤ Chebyshev.psi (↑(21289 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 21283) (b := 21289) (by decide)
        (by decide +kernel)]
    exact psi_21283_bounds.1
  · change (21636589 : ℝ) / 1000 ≤ Chebyshev.psi (↑(21637 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 21617) (b := 21637) (by decide)
        (by decide +kernel)]
    exact psi_21617_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(18126 : ℕ) : ℝ) ≤ (18132731 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 18121) (b := 18126) (by decide)
        (by decide +kernel)]
    exact psi_18121_bounds.2
  · change Chebyshev.psi (↑(18456 : ℕ) : ℝ) ≤ (18505644 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 18451) (b := 18456) (by decide)
        (by decide +kernel)]
    exact psi_18451_bounds.2
  · change Chebyshev.psi (↑(18858 : ℕ) : ℝ) ≤ (18834889 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 18839) (b := 18858) (by decide)
        (by decide +kernel)]
    exact psi_18839_bounds.2
  · change Chebyshev.psi (↑(19223 : ℕ) : ℝ) ≤ (19160668 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 19219) (b := 19223) (by decide)
        (by decide +kernel)]
    exact psi_19219_bounds.2
  · change Chebyshev.psi (↑(19538 : ℕ) : ℝ) ≤ (19510707 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 19531) (b := 19538) (by decide)
        (by decide +kernel)]
    exact psi_19531_bounds.2
  · change Chebyshev.psi (↑(19889 : ℕ) : ℝ) ≤ (19848270 : ℝ) / 1000
    exact psi_19889_bounds.2
  · change Chebyshev.psi (↑(20226 : ℕ) : ℝ) ≤ (20214945 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 20219) (b := 20226) (by decide)
        (by decide +kernel)]
    exact psi_20219_bounds.2
  · change Chebyshev.psi (↑(20593 : ℕ) : ℝ) ≤ (20571916 : ℝ) / 1000
    exact psi_20593_bounds.2
  · change Chebyshev.psi (↑(20950 : ℕ) : ℝ) ≤ (20910172 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 20947) (b := 20950) (by decide)
        (by decide +kernel)]
    exact psi_20947_bounds.2
  · change Chebyshev.psi (↑(21288 : ℕ) : ℝ) ≤ (21258131 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 21283) (b := 21288) (by decide)
        (by decide +kernel)]
    exact psi_21283_bounds.2
  · change Chebyshev.psi (↑(21636 : ℕ) : ℝ) ≤ (21637283 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 21617) (b := 21636) (by decide)
        (by decide +kernel)]
    exact psi_21617_bounds.2
  · change Chebyshev.psi (↑(22015 : ℕ) : ℝ) ≤ (22007423 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 22013) (b := 22015) (by decide)
        (by decide +kernel)]
    exact psi_22013_bounds.2

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
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 17761 *
          (Real.log 17761 * (Real.log 17761 - Real.log (Real.log 17761)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 18127 *
          (Real.log 18127 * (Real.log 18127 - Real.log (Real.log 18127)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 18457 *
          (Real.log 18457 * (Real.log 18457 - Real.log (Real.log 18457)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 18859 *
          (Real.log 18859 * (Real.log 18859 - Real.log (Real.log 18859)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 19224 *
          (Real.log 19224 * (Real.log 19224 - Real.log (Real.log 19224)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 19539 *
          (Real.log 19539 * (Real.log 19539 - Real.log (Real.log 19539)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 19890 *
          (Real.log 19890 * (Real.log 19890 - Real.log (Real.log 19890)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 20227 *
          (Real.log 20227 * (Real.log 20227 - Real.log (Real.log 20227)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 20594 *
          (Real.log 20594 * (Real.log 20594 - Real.log (Real.log 20594)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 20951 *
          (Real.log 20951 * (Real.log 20951 - Real.log (Real.log 20951)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 21289 *
          (Real.log 21289 * (Real.log 21289 - Real.log (Real.log 21289)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 21637 *
          (Real.log 21637 * (Real.log 21637 - Real.log (Real.log 21637)) / (8 * Real.pi))
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
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 18127 *
          (Real.log 18127 * (Real.log 18127 - Real.log (Real.log 18127)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 18457 *
          (Real.log 18457 * (Real.log 18457 - Real.log (Real.log 18457)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 18859 *
          (Real.log 18859 * (Real.log 18859 - Real.log (Real.log 18859)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 19224 *
          (Real.log 19224 * (Real.log 19224 - Real.log (Real.log 19224)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 19539 *
          (Real.log 19539 * (Real.log 19539 - Real.log (Real.log 19539)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 19890 *
          (Real.log 19890 * (Real.log 19890 - Real.log (Real.log 19890)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 20227 *
          (Real.log 20227 * (Real.log 20227 - Real.log (Real.log 20227)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 20594 *
          (Real.log 20594 * (Real.log 20594 - Real.log (Real.log 20594)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 20951 *
          (Real.log 20951 * (Real.log 20951 - Real.log (Real.log 20951)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 21289 *
          (Real.log 21289 * (Real.log 21289 - Real.log (Real.log 21289)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 21637 *
          (Real.log 21637 * (Real.log 21637 - Real.log (Real.log 21637)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (380000 : ℝ) / 1000 ≤
        Real.sqrt 22016 *
          (Real.log 22016 * (Real.log 22016 - Real.log (Real.log 22016)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[17761, 22016)`. -/
theorem psi_lee_nosal_17761_22016 {x : ℝ} (ha : 17761 ≤ x) (hb : x < 22016) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
