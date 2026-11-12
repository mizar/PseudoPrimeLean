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
  [⟨1006, 1038, 996052, 1039028, 42000, 42000⟩, ⟨1038, 1069, 1038334, 1074379, 42000, 42000⟩,
    ⟨1069, 1103, 1080616, 1109036, 42000, 42000⟩, ⟨1103, 1151, 1115273, 1144386, 42000, 42000⟩,
    ⟨1151, 1192, 1150624, 1186668, 42000, 42000⟩, ⟨1192, 1227, 1185974, 1222019, 42000, 42000⟩,
    ⟨1227, 1263, 1221325, 1257369, 42000, 42000⟩, ⟨1263, 1298, 1256675, 1300345, 42000, 42000⟩,
    ⟨1298, 1327, 1299650, 1336388, 42000, 42000⟩, ⟨1327, 1373, 1342626, 1364114, 42000, 42000⟩,
    ⟨1373, 1412, 1370351, 1393226, 42000, 42000⟩, ⟨1412, 1434, 1392532, 1422339, 42000, 42000⟩,
    ⟨1434, 1463, 1421644, 1458382, 42000, 42000⟩, ⟨1463, 1499, 1457688, 1502050, 42000, 42000⟩,
    ⟨1499, 1549, 1508981, 1538787, 42000, 42000⟩, ⟨1549, 1587, 1545718, 1590773, 42000, 42000⟩,
    ⟨1587, 1619, 1590079, 1627510, 42000, 42000⟩, ⟨1619, 1657, 1633747, 1656622, 42000, 42000⟩,
    ⟨1657, 1697, 1663553, 1697518, 42000, 42000⟩, ⟨1697, 1733, 1704448, 1734948, 42000, 42000⟩,
    ⟨1733, 1777, 1741878, 1772378, 42000, 42000⟩, ⟨1777, 1821, 1779308, 1817432, 42000, 42000⟩,
    ⟨1821, 1858, 1816738, 1843772, 42000, 42000⟩, ⟨1858, 1885, 1843078, 1888827, 42000, 42000⟩,
    ⟨1885, 1930, 1888132, 1918632, 42000, 42000⟩]

/-- The kernel-checked prefix bounds for 997. -/
private theorem psi_997_bounds :
    (996052 : ℝ) / 1000 ≤ Chebyshev.psi 997 ∧ Chebyshev.psi 997 ≤ (996746 : ℝ) / 1000 := by
  have hl : 2 ^ 1437 ≤ Nat.lcmUpto 997 := by decide +kernel
  have hu : Nat.lcmUpto 997 ≤ 2 ^ (1437 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1033. -/
private theorem psi_1033_bounds :
    (1038334 : ℝ) / 1000 ≤ Chebyshev.psi 1033 ∧ Chebyshev.psi 1033 ≤ (1039028 : ℝ) / 1000 := by
  have hl : 2 ^ 1498 ≤ Nat.lcmUpto 1033 := by decide +kernel
  have hu : Nat.lcmUpto 1033 ≤ 2 ^ (1498 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1063. -/
private theorem psi_1063_bounds :
    (1073684 : ℝ) / 1000 ≤ Chebyshev.psi 1063 ∧ Chebyshev.psi 1063 ≤ (1074379 : ℝ) / 1000 := by
  have hl : 2 ^ 1549 ≤ Nat.lcmUpto 1063 := by decide +kernel
  have hu : Nat.lcmUpto 1063 ≤ 2 ^ (1549 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1069. -/
private theorem psi_1069_bounds :
    (1080616 : ℝ) / 1000 ≤ Chebyshev.psi 1069 ∧ Chebyshev.psi 1069 ≤ (1081310 : ℝ) / 1000 := by
  have hl : 2 ^ 1559 ≤ Nat.lcmUpto 1069 := by decide +kernel
  have hu : Nat.lcmUpto 1069 ≤ 2 ^ (1559 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1097. -/
private theorem psi_1097_bounds :
    (1108342 : ℝ) / 1000 ≤ Chebyshev.psi 1097 ∧ Chebyshev.psi 1097 ≤ (1109036 : ℝ) / 1000 := by
  have hl : 2 ^ 1599 ≤ Nat.lcmUpto 1097 := by decide +kernel
  have hu : Nat.lcmUpto 1097 ≤ 2 ^ (1599 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1103. -/
private theorem psi_1103_bounds :
    (1115273 : ℝ) / 1000 ≤ Chebyshev.psi 1103 ∧ Chebyshev.psi 1103 ≤ (1115967 : ℝ) / 1000 := by
  have hl : 2 ^ 1609 ≤ Nat.lcmUpto 1103 := by decide +kernel
  have hu : Nat.lcmUpto 1103 ≤ 2 ^ (1609 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1129. -/
private theorem psi_1129_bounds :
    (1143692 : ℝ) / 1000 ≤ Chebyshev.psi 1129 ∧ Chebyshev.psi 1129 ≤ (1144386 : ℝ) / 1000 := by
  have hl : 2 ^ 1650 ≤ Nat.lcmUpto 1129 := by decide +kernel
  have hu : Nat.lcmUpto 1129 ≤ 2 ^ (1650 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1151. -/
private theorem psi_1151_bounds :
    (1150624 : ℝ) / 1000 ≤ Chebyshev.psi 1151 ∧ Chebyshev.psi 1151 ≤ (1151318 : ℝ) / 1000 := by
  have hl : 2 ^ 1660 ≤ Nat.lcmUpto 1151 := by decide +kernel
  have hu : Nat.lcmUpto 1151 ≤ 2 ^ (1660 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1187. -/
private theorem psi_1187_bounds :
    (1185974 : ℝ) / 1000 ≤ Chebyshev.psi 1187 ∧ Chebyshev.psi 1187 ≤ (1186668 : ℝ) / 1000 := by
  have hl : 2 ^ 1711 ≤ Nat.lcmUpto 1187 := by decide +kernel
  have hu : Nat.lcmUpto 1187 ≤ 2 ^ (1711 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1223. -/
private theorem psi_1223_bounds :
    (1221325 : ℝ) / 1000 ≤ Chebyshev.psi 1223 ∧ Chebyshev.psi 1223 ≤ (1222019 : ℝ) / 1000 := by
  have hl : 2 ^ 1762 ≤ Nat.lcmUpto 1223 := by decide +kernel
  have hu : Nat.lcmUpto 1223 ≤ 2 ^ (1762 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1259. -/
private theorem psi_1259_bounds :
    (1256675 : ℝ) / 1000 ≤ Chebyshev.psi 1259 ∧ Chebyshev.psi 1259 ≤ (1257369 : ℝ) / 1000 := by
  have hl : 2 ^ 1813 ≤ Nat.lcmUpto 1259 := by decide +kernel
  have hu : Nat.lcmUpto 1259 ≤ 2 ^ (1813 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1297. -/
private theorem psi_1297_bounds :
    (1299650 : ℝ) / 1000 ≤ Chebyshev.psi 1297 ∧ Chebyshev.psi 1297 ≤ (1300345 : ℝ) / 1000 := by
  have hl : 2 ^ 1875 ≤ Nat.lcmUpto 1297 := by decide +kernel
  have hu : Nat.lcmUpto 1297 ≤ 2 ^ (1875 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1321. -/
private theorem psi_1321_bounds :
    (1335694 : ℝ) / 1000 ≤ Chebyshev.psi 1321 ∧ Chebyshev.psi 1321 ≤ (1336388 : ℝ) / 1000 := by
  have hl : 2 ^ 1927 ≤ Nat.lcmUpto 1321 := by decide +kernel
  have hu : Nat.lcmUpto 1321 ≤ 2 ^ (1927 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1327. -/
private theorem psi_1327_bounds :
    (1342626 : ℝ) / 1000 ≤ Chebyshev.psi 1327 ∧ Chebyshev.psi 1327 ≤ (1343320 : ℝ) / 1000 := by
  have hl : 2 ^ 1937 ≤ Nat.lcmUpto 1327 := by decide +kernel
  have hu : Nat.lcmUpto 1327 ≤ 2 ^ (1937 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1369. -/
private theorem psi_1369_bounds :
    (1363420 : ℝ) / 1000 ≤ Chebyshev.psi 1369 ∧ Chebyshev.psi 1369 ≤ (1364114 : ℝ) / 1000 := by
  have hl : 2 ^ 1967 ≤ Nat.lcmUpto 1369 := by decide +kernel
  have hu : Nat.lcmUpto 1369 ≤ 2 ^ (1967 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1373. -/
private theorem psi_1373_bounds :
    (1370351 : ℝ) / 1000 ≤ Chebyshev.psi 1373 ∧ Chebyshev.psi 1373 ≤ (1371046 : ℝ) / 1000 := by
  have hl : 2 ^ 1977 ≤ Nat.lcmUpto 1373 := by decide +kernel
  have hu : Nat.lcmUpto 1373 ≤ 2 ^ (1977 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1409. -/
private theorem psi_1409_bounds :
    (1392532 : ℝ) / 1000 ≤ Chebyshev.psi 1409 ∧ Chebyshev.psi 1409 ≤ (1393226 : ℝ) / 1000 := by
  have hl : 2 ^ 2009 ≤ Nat.lcmUpto 1409 := by decide +kernel
  have hu : Nat.lcmUpto 1409 ≤ 2 ^ (2009 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1433. -/
private theorem psi_1433_bounds :
    (1421644 : ℝ) / 1000 ≤ Chebyshev.psi 1433 ∧ Chebyshev.psi 1433 ≤ (1422339 : ℝ) / 1000 := by
  have hl : 2 ^ 2051 ≤ Nat.lcmUpto 1433 := by decide +kernel
  have hu : Nat.lcmUpto 1433 ≤ 2 ^ (2051 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1459. -/
private theorem psi_1459_bounds :
    (1457688 : ℝ) / 1000 ≤ Chebyshev.psi 1459 ∧ Chebyshev.psi 1459 ≤ (1458382 : ℝ) / 1000 := by
  have hl : 2 ^ 2103 ≤ Nat.lcmUpto 1459 := by decide +kernel
  have hu : Nat.lcmUpto 1459 ≤ 2 ^ (2103 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1493. -/
private theorem psi_1493_bounds :
    (1501356 : ℝ) / 1000 ≤ Chebyshev.psi 1493 ∧ Chebyshev.psi 1493 ≤ (1502050 : ℝ) / 1000 := by
  have hl : 2 ^ 2166 ≤ Nat.lcmUpto 1493 := by decide +kernel
  have hu : Nat.lcmUpto 1493 ≤ 2 ^ (2166 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1499. -/
private theorem psi_1499_bounds :
    (1508981 : ℝ) / 1000 ≤ Chebyshev.psi 1499 ∧ Chebyshev.psi 1499 ≤ (1509675 : ℝ) / 1000 := by
  have hl : 2 ^ 2177 ≤ Nat.lcmUpto 1499 := by decide +kernel
  have hu : Nat.lcmUpto 1499 ≤ 2 ^ (2177 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1543. -/
private theorem psi_1543_bounds :
    (1538093 : ℝ) / 1000 ≤ Chebyshev.psi 1543 ∧ Chebyshev.psi 1543 ≤ (1538787 : ℝ) / 1000 := by
  have hl : 2 ^ 2219 ≤ Nat.lcmUpto 1543 := by decide +kernel
  have hu : Nat.lcmUpto 1543 ≤ 2 ^ (2219 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1549. -/
private theorem psi_1549_bounds :
    (1545718 : ℝ) / 1000 ≤ Chebyshev.psi 1549 ∧ Chebyshev.psi 1549 ≤ (1546412 : ℝ) / 1000 := by
  have hl : 2 ^ 2230 ≤ Nat.lcmUpto 1549 := by decide +kernel
  have hu : Nat.lcmUpto 1549 ≤ 2 ^ (2230 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1583. -/
private theorem psi_1583_bounds :
    (1590079 : ℝ) / 1000 ≤ Chebyshev.psi 1583 ∧ Chebyshev.psi 1583 ≤ (1590773 : ℝ) / 1000 := by
  have hl : 2 ^ 2294 ≤ Nat.lcmUpto 1583 := by decide +kernel
  have hu : Nat.lcmUpto 1583 ≤ 2 ^ (2294 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1613. -/
private theorem psi_1613_bounds :
    (1626816 : ℝ) / 1000 ≤ Chebyshev.psi 1613 ∧ Chebyshev.psi 1613 ≤ (1627510 : ℝ) / 1000 := by
  have hl : 2 ^ 2347 ≤ Nat.lcmUpto 1613 := by decide +kernel
  have hu : Nat.lcmUpto 1613 ≤ 2 ^ (2347 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1619. -/
private theorem psi_1619_bounds :
    (1633747 : ℝ) / 1000 ≤ Chebyshev.psi 1619 ∧ Chebyshev.psi 1619 ≤ (1634442 : ℝ) / 1000 := by
  have hl : 2 ^ 2357 ≤ Nat.lcmUpto 1619 := by decide +kernel
  have hu : Nat.lcmUpto 1619 ≤ 2 ^ (2357 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1637. -/
private theorem psi_1637_bounds :
    (1655928 : ℝ) / 1000 ≤ Chebyshev.psi 1637 ∧ Chebyshev.psi 1637 ≤ (1656622 : ℝ) / 1000 := by
  have hl : 2 ^ 2389 ≤ Nat.lcmUpto 1637 := by decide +kernel
  have hu : Nat.lcmUpto 1637 ≤ 2 ^ (2389 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1657. -/
private theorem psi_1657_bounds :
    (1663553 : ℝ) / 1000 ≤ Chebyshev.psi 1657 ∧ Chebyshev.psi 1657 ≤ (1664247 : ℝ) / 1000 := by
  have hl : 2 ^ 2400 ≤ Nat.lcmUpto 1657 := by decide +kernel
  have hu : Nat.lcmUpto 1657 ≤ 2 ^ (2400 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1693. -/
private theorem psi_1693_bounds :
    (1696824 : ℝ) / 1000 ≤ Chebyshev.psi 1693 ∧ Chebyshev.psi 1693 ≤ (1697518 : ℝ) / 1000 := by
  have hl : 2 ^ 2448 ≤ Nat.lcmUpto 1693 := by decide +kernel
  have hu : Nat.lcmUpto 1693 ≤ 2 ^ (2448 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1697. -/
private theorem psi_1697_bounds :
    (1704448 : ℝ) / 1000 ≤ Chebyshev.psi 1697 ∧ Chebyshev.psi 1697 ≤ (1705143 : ℝ) / 1000 := by
  have hl : 2 ^ 2459 ≤ Nat.lcmUpto 1697 := by decide +kernel
  have hu : Nat.lcmUpto 1697 ≤ 2 ^ (2459 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1723. -/
private theorem psi_1723_bounds :
    (1734254 : ℝ) / 1000 ≤ Chebyshev.psi 1723 ∧ Chebyshev.psi 1723 ≤ (1734948 : ℝ) / 1000 := by
  have hl : 2 ^ 2502 ≤ Nat.lcmUpto 1723 := by decide +kernel
  have hu : Nat.lcmUpto 1723 ≤ 2 ^ (2502 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1733. -/
private theorem psi_1733_bounds :
    (1741878 : ℝ) / 1000 ≤ Chebyshev.psi 1733 ∧ Chebyshev.psi 1733 ≤ (1742573 : ℝ) / 1000 := by
  have hl : 2 ^ 2513 ≤ Nat.lcmUpto 1733 := by decide +kernel
  have hu : Nat.lcmUpto 1733 ≤ 2 ^ (2513 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1759. -/
private theorem psi_1759_bounds :
    (1771684 : ℝ) / 1000 ≤ Chebyshev.psi 1759 ∧ Chebyshev.psi 1759 ≤ (1772378 : ℝ) / 1000 := by
  have hl : 2 ^ 2556 ≤ Nat.lcmUpto 1759 := by decide +kernel
  have hu : Nat.lcmUpto 1759 ≤ 2 ^ (2556 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1777. -/
private theorem psi_1777_bounds :
    (1779308 : ℝ) / 1000 ≤ Chebyshev.psi 1777 ∧ Chebyshev.psi 1777 ≤ (1780002 : ℝ) / 1000 := by
  have hl : 2 ^ 2567 ≤ Nat.lcmUpto 1777 := by decide +kernel
  have hu : Nat.lcmUpto 1777 ≤ 2 ^ (2567 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1811. -/
private theorem psi_1811_bounds :
    (1816738 : ℝ) / 1000 ≤ Chebyshev.psi 1811 ∧ Chebyshev.psi 1811 ≤ (1817432 : ℝ) / 1000 := by
  have hl : 2 ^ 2621 ≤ Nat.lcmUpto 1811 := by decide +kernel
  have hu : Nat.lcmUpto 1811 ≤ 2 ^ (2621 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1849. -/
private theorem psi_1849_bounds :
    (1843078 : ℝ) / 1000 ≤ Chebyshev.psi 1849 ∧ Chebyshev.psi 1849 ≤ (1843772 : ℝ) / 1000 := by
  have hl : 2 ^ 2659 ≤ Nat.lcmUpto 1849 := by decide +kernel
  have hu : Nat.lcmUpto 1849 ≤ 2 ^ (2659 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1879. -/
private theorem psi_1879_bounds :
    (1888132 : ℝ) / 1000 ≤ Chebyshev.psi 1879 ∧ Chebyshev.psi 1879 ≤ (1888827 : ℝ) / 1000 := by
  have hl : 2 ^ 2724 ≤ Nat.lcmUpto 1879 := by decide +kernel
  have hu : Nat.lcmUpto 1879 ≤ 2 ^ (2724 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1913. -/
private theorem psi_1913_bounds :
    (1917938 : ℝ) / 1000 ≤ Chebyshev.psi 1913 ∧ Chebyshev.psi 1913 ≤ (1918632 : ℝ) / 1000 := by
  have hl : 2 ^ 2767 ≤ Nat.lcmUpto 1913 := by decide +kernel
  have hu : Nat.lcmUpto 1913 ≤ 2 ^ (2767 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 1006 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 1006 ≤ t) :
    (42 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 1006) (lo := 691 / 100) (hi := 692 / 100) (vlo :=
      193 / 100) (vhi := 194 / 100) (c := 42) (j := 10) (k := 3) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 1006) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (996052 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1006 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 997) (b := 1006) (by decide) (by decide +kernel)]
    exact psi_997_bounds.1
  · change (1038334 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1038 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1033) (b := 1038) (by decide) (by decide +kernel)]
    exact psi_1033_bounds.1
  · change (1080616 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1069 : ℕ) : ℝ)
    exact psi_1069_bounds.1
  · change (1115273 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1103 : ℕ) : ℝ)
    exact psi_1103_bounds.1
  · change (1150624 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1151 : ℕ) : ℝ)
    exact psi_1151_bounds.1
  · change (1185974 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1192 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1187) (b := 1192) (by decide) (by decide +kernel)]
    exact psi_1187_bounds.1
  · change (1221325 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1227 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1223) (b := 1227) (by decide) (by decide +kernel)]
    exact psi_1223_bounds.1
  · change (1256675 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1263 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1259) (b := 1263) (by decide) (by decide +kernel)]
    exact psi_1259_bounds.1
  · change (1299650 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1298 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1297) (b := 1298) (by decide) (by decide +kernel)]
    exact psi_1297_bounds.1
  · change (1342626 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1327 : ℕ) : ℝ)
    exact psi_1327_bounds.1
  · change (1370351 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1373 : ℕ) : ℝ)
    exact psi_1373_bounds.1
  · change (1392532 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1412 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1409) (b := 1412) (by decide) (by decide +kernel)]
    exact psi_1409_bounds.1
  · change (1421644 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1434 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1433) (b := 1434) (by decide) (by decide +kernel)]
    exact psi_1433_bounds.1
  · change (1457688 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1463 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1459) (b := 1463) (by decide) (by decide +kernel)]
    exact psi_1459_bounds.1
  · change (1508981 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1499 : ℕ) : ℝ)
    exact psi_1499_bounds.1
  · change (1545718 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1549 : ℕ) : ℝ)
    exact psi_1549_bounds.1
  · change (1590079 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1587 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1583) (b := 1587) (by decide) (by decide +kernel)]
    exact psi_1583_bounds.1
  · change (1633747 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1619 : ℕ) : ℝ)
    exact psi_1619_bounds.1
  · change (1663553 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1657 : ℕ) : ℝ)
    exact psi_1657_bounds.1
  · change (1704448 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1697 : ℕ) : ℝ)
    exact psi_1697_bounds.1
  · change (1741878 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1733 : ℕ) : ℝ)
    exact psi_1733_bounds.1
  · change (1779308 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1777 : ℕ) : ℝ)
    exact psi_1777_bounds.1
  · change (1816738 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1821 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1811) (b := 1821) (by decide) (by decide +kernel)]
    exact psi_1811_bounds.1
  · change (1843078 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1858 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1849) (b := 1858) (by decide) (by decide +kernel)]
    exact psi_1849_bounds.1
  · change (1888132 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1885 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1879) (b := 1885) (by decide) (by decide +kernel)]
    exact psi_1879_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(1037 : ℕ) : ℝ) ≤ (1039028 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1033) (b := 1037) (by decide) (by decide +kernel)]
    exact psi_1033_bounds.2
  · change Chebyshev.psi (↑(1068 : ℕ) : ℝ) ≤ (1074379 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1063) (b := 1068) (by decide) (by decide +kernel)]
    exact psi_1063_bounds.2
  · change Chebyshev.psi (↑(1102 : ℕ) : ℝ) ≤ (1109036 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1097) (b := 1102) (by decide) (by decide +kernel)]
    exact psi_1097_bounds.2
  · change Chebyshev.psi (↑(1150 : ℕ) : ℝ) ≤ (1144386 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1129) (b := 1150) (by decide) (by decide +kernel)]
    exact psi_1129_bounds.2
  · change Chebyshev.psi (↑(1191 : ℕ) : ℝ) ≤ (1186668 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1187) (b := 1191) (by decide) (by decide +kernel)]
    exact psi_1187_bounds.2
  · change Chebyshev.psi (↑(1226 : ℕ) : ℝ) ≤ (1222019 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1223) (b := 1226) (by decide) (by decide +kernel)]
    exact psi_1223_bounds.2
  · change Chebyshev.psi (↑(1262 : ℕ) : ℝ) ≤ (1257369 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1259) (b := 1262) (by decide) (by decide +kernel)]
    exact psi_1259_bounds.2
  · change Chebyshev.psi (↑(1297 : ℕ) : ℝ) ≤ (1300345 : ℝ) / 1000
    exact psi_1297_bounds.2
  · change Chebyshev.psi (↑(1326 : ℕ) : ℝ) ≤ (1336388 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1321) (b := 1326) (by decide) (by decide +kernel)]
    exact psi_1321_bounds.2
  · change Chebyshev.psi (↑(1372 : ℕ) : ℝ) ≤ (1364114 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1369) (b := 1372) (by decide) (by decide +kernel)]
    exact psi_1369_bounds.2
  · change Chebyshev.psi (↑(1411 : ℕ) : ℝ) ≤ (1393226 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1409) (b := 1411) (by decide) (by decide +kernel)]
    exact psi_1409_bounds.2
  · change Chebyshev.psi (↑(1433 : ℕ) : ℝ) ≤ (1422339 : ℝ) / 1000
    exact psi_1433_bounds.2
  · change Chebyshev.psi (↑(1462 : ℕ) : ℝ) ≤ (1458382 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1459) (b := 1462) (by decide) (by decide +kernel)]
    exact psi_1459_bounds.2
  · change Chebyshev.psi (↑(1498 : ℕ) : ℝ) ≤ (1502050 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1493) (b := 1498) (by decide) (by decide +kernel)]
    exact psi_1493_bounds.2
  · change Chebyshev.psi (↑(1548 : ℕ) : ℝ) ≤ (1538787 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1543) (b := 1548) (by decide) (by decide +kernel)]
    exact psi_1543_bounds.2
  · change Chebyshev.psi (↑(1586 : ℕ) : ℝ) ≤ (1590773 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1583) (b := 1586) (by decide) (by decide +kernel)]
    exact psi_1583_bounds.2
  · change Chebyshev.psi (↑(1618 : ℕ) : ℝ) ≤ (1627510 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1613) (b := 1618) (by decide) (by decide +kernel)]
    exact psi_1613_bounds.2
  · change Chebyshev.psi (↑(1656 : ℕ) : ℝ) ≤ (1656622 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1637) (b := 1656) (by decide) (by decide +kernel)]
    exact psi_1637_bounds.2
  · change Chebyshev.psi (↑(1696 : ℕ) : ℝ) ≤ (1697518 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1693) (b := 1696) (by decide) (by decide +kernel)]
    exact psi_1693_bounds.2
  · change Chebyshev.psi (↑(1732 : ℕ) : ℝ) ≤ (1734948 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1723) (b := 1732) (by decide) (by decide +kernel)]
    exact psi_1723_bounds.2
  · change Chebyshev.psi (↑(1776 : ℕ) : ℝ) ≤ (1772378 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1759) (b := 1776) (by decide) (by decide +kernel)]
    exact psi_1759_bounds.2
  · change Chebyshev.psi (↑(1820 : ℕ) : ℝ) ≤ (1817432 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1811) (b := 1820) (by decide) (by decide +kernel)]
    exact psi_1811_bounds.2
  · change Chebyshev.psi (↑(1857 : ℕ) : ℝ) ≤ (1843772 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1849) (b := 1857) (by decide) (by decide +kernel)]
    exact psi_1849_bounds.2
  · change Chebyshev.psi (↑(1884 : ℕ) : ℝ) ≤ (1888827 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1879) (b := 1884) (by decide) (by decide +kernel)]
    exact psi_1879_bounds.2
  · change Chebyshev.psi (↑(1929 : ℕ) : ℝ) ≤ (1918632 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1913) (b := 1929) (by decide) (by decide +kernel)]
    exact psi_1913_bounds.2

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1006 *
          (Real.log 1006 * (Real.log 1006 - Real.log (Real.log 1006)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1038 *
          (Real.log 1038 * (Real.log 1038 - Real.log (Real.log 1038)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1069 *
          (Real.log 1069 * (Real.log 1069 - Real.log (Real.log 1069)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1103 *
          (Real.log 1103 * (Real.log 1103 - Real.log (Real.log 1103)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1151 *
          (Real.log 1151 * (Real.log 1151 - Real.log (Real.log 1151)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1192 *
          (Real.log 1192 * (Real.log 1192 - Real.log (Real.log 1192)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1227 *
          (Real.log 1227 * (Real.log 1227 - Real.log (Real.log 1227)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1263 *
          (Real.log 1263 * (Real.log 1263 - Real.log (Real.log 1263)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1298 *
          (Real.log 1298 * (Real.log 1298 - Real.log (Real.log 1298)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1327 *
          (Real.log 1327 * (Real.log 1327 - Real.log (Real.log 1327)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1373 *
          (Real.log 1373 * (Real.log 1373 - Real.log (Real.log 1373)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1412 *
          (Real.log 1412 * (Real.log 1412 - Real.log (Real.log 1412)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1434 *
          (Real.log 1434 * (Real.log 1434 - Real.log (Real.log 1434)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1463 *
          (Real.log 1463 * (Real.log 1463 - Real.log (Real.log 1463)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1499 *
          (Real.log 1499 * (Real.log 1499 - Real.log (Real.log 1499)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1549 *
          (Real.log 1549 * (Real.log 1549 - Real.log (Real.log 1549)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1587 *
          (Real.log 1587 * (Real.log 1587 - Real.log (Real.log 1587)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1619 *
          (Real.log 1619 * (Real.log 1619 - Real.log (Real.log 1619)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1657 *
          (Real.log 1657 * (Real.log 1657 - Real.log (Real.log 1657)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1697 *
          (Real.log 1697 * (Real.log 1697 - Real.log (Real.log 1697)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1733 *
          (Real.log 1733 * (Real.log 1733 - Real.log (Real.log 1733)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1777 *
          (Real.log 1777 * (Real.log 1777 - Real.log (Real.log 1777)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1821 *
          (Real.log 1821 * (Real.log 1821 - Real.log (Real.log 1821)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1858 *
          (Real.log 1858 * (Real.log 1858 - Real.log (Real.log 1858)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1885 *
          (Real.log 1885 * (Real.log 1885 - Real.log (Real.log 1885)) / (8 * Real.pi))
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
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1038 *
          (Real.log 1038 * (Real.log 1038 - Real.log (Real.log 1038)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1069 *
          (Real.log 1069 * (Real.log 1069 - Real.log (Real.log 1069)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1103 *
          (Real.log 1103 * (Real.log 1103 - Real.log (Real.log 1103)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1151 *
          (Real.log 1151 * (Real.log 1151 - Real.log (Real.log 1151)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1192 *
          (Real.log 1192 * (Real.log 1192 - Real.log (Real.log 1192)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1227 *
          (Real.log 1227 * (Real.log 1227 - Real.log (Real.log 1227)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1263 *
          (Real.log 1263 * (Real.log 1263 - Real.log (Real.log 1263)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1298 *
          (Real.log 1298 * (Real.log 1298 - Real.log (Real.log 1298)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1327 *
          (Real.log 1327 * (Real.log 1327 - Real.log (Real.log 1327)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1373 *
          (Real.log 1373 * (Real.log 1373 - Real.log (Real.log 1373)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1412 *
          (Real.log 1412 * (Real.log 1412 - Real.log (Real.log 1412)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1434 *
          (Real.log 1434 * (Real.log 1434 - Real.log (Real.log 1434)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1463 *
          (Real.log 1463 * (Real.log 1463 - Real.log (Real.log 1463)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1499 *
          (Real.log 1499 * (Real.log 1499 - Real.log (Real.log 1499)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1549 *
          (Real.log 1549 * (Real.log 1549 - Real.log (Real.log 1549)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1587 *
          (Real.log 1587 * (Real.log 1587 - Real.log (Real.log 1587)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1619 *
          (Real.log 1619 * (Real.log 1619 - Real.log (Real.log 1619)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1657 *
          (Real.log 1657 * (Real.log 1657 - Real.log (Real.log 1657)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1697 *
          (Real.log 1697 * (Real.log 1697 - Real.log (Real.log 1697)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1733 *
          (Real.log 1733 * (Real.log 1733 - Real.log (Real.log 1733)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1777 *
          (Real.log 1777 * (Real.log 1777 - Real.log (Real.log 1777)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1821 *
          (Real.log 1821 * (Real.log 1821 - Real.log (Real.log 1821)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1858 *
          (Real.log 1858 * (Real.log 1858 - Real.log (Real.log 1858)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1885 *
          (Real.log 1885 * (Real.log 1885 - Real.log (Real.log 1885)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (42000 : ℝ) / 1000 ≤
        Real.sqrt 1930 *
          (Real.log 1930 * (Real.log 1930 - Real.log (Real.log 1930)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[1006, 1930)`. -/
theorem psi_lee_nosal_1006_1930 {x : ℝ} (ha : 1006 ≤ x) (hb : x < 1930) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
