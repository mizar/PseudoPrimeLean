/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.PointwiseRationalSmoothSupply
public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiberInterval

/-! # Explicit finite-fiber Fermat extraction with pointwise smooth budgets -/

public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For an odd prime above P(1388714689827), the displayed pointwise smooth budgets
give a prime q≤log(p)^(1838239/1000000) with nontrivial Fermat quotient modulo p².
Use the proved explicit interval cutoff and then extract a prime factor.
The quantitative prime-supply and floor budgets remain explicit hypotheses. -/
theorem exists_prime_nontrivial_power_of_explicit_fiber_smooth_bounds {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold (1388714689827) ≤ p)
    (hL : 2 ≤ Real.log p) (hB : 0 < Nat.floor ((Real.log p) ^ (1838239 / 1000000 : ℝ)))
    (hC : 0 < Nat.floor ((p : ℝ) ^ (8382354 / 10000000 : ℝ)))
    (hcL : 2 * (999997 / 1000000 : ℝ) ≤ Real.log (Real.log p))
    (hMp :
      2 * (Real.log p) ^ (1838238 / 1000000 : ℝ) ≤
        ((Nat.floor ((Real.log p) ^ (1838239 / 1000000 : ℝ))).primeCounting : ℝ))
    (hgap :
      (999997 / 1000000 : ℝ) * (1838239 / 1000000) * Real.log p +
          (1838239 / 1000000 : ℝ) * Real.log (Real.log p) <
        (125 / 68) * Real.log p)
    (henv :
      ∀ k : ℕ,
        k ^ 68 ≤ 2 ^ 68 * p ^ 125 → 256 * k ≤ p * Nat.floor ((p : ℝ) ^ (8382354 / 10000000 : ℝ))) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (1838239 / 1000000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  obtain ⟨k, hk, _, hlo, hhi, hcount⟩ := exists_fixed_finite_fiber_interval_bound hodd hlarge
  have hsmooth :=
    fixed_smooth_count_at_rational_cutoff_of_bounds (Fact.out : p.Prime).pos hk hL hB hC hcL hMp
      hgap (henv k hhi) hlo
  obtain ⟨q, hq, hqB, hpow⟩ := exists_prime_nontrivial_power_of_interval_and_smooth hcount hsmooth
  exact
    ⟨q, hq,
      (Nat.cast_le.mpr (Nat.lt_add_one_iff.mp hqB)).trans
        (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)),
      hpow⟩

/-- At scale 70/38, pointwise smooth budgets yield a prime q≤log(p)^(184211/100000)
whose Fermat quotient is nontrivial modulo p². Apply the explicit interval
cutoff and extract a prime factor from its smooth inputs. -/
theorem exists_prime_nontrivial_power_of_explicit_fiber_smooth_bounds_74_40 {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 283000007562 ≤ p)
    (hL : 2 ≤ Real.log p) (hB : 0 < Nat.floor ((Real.log p) ^ (1850004 / 1000000 : ℝ)))
    (hC : 0 < Nat.floor ((p : ℝ) ^ (8500002 / 10000000 : ℝ)))
    (hcL : 2 * (999997 / 1000000 : ℝ) ≤ Real.log (Real.log p))
    (hMp :
      2 * (Real.log p) ^ (1850003 / 1000000 : ℝ) ≤
        ((Nat.floor ((Real.log p) ^ (1850004 / 1000000 : ℝ))).primeCounting : ℝ))
    (hgap :
      (999997 / 1000000 : ℝ) * (1850004 / 1000000) * Real.log p +
          (1850004 / 1000000 : ℝ) * Real.log (Real.log p) <
        (74 / 40) * Real.log p)
    (henv :
      ∀ k : ℕ,
        k ^ 40 ≤ 2 ^ 40 * p ^ 74 → 256 * k ≤ p * Nat.floor ((p : ℝ) ^ (8500002 / 10000000 : ℝ))) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (1850004 / 1000000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  obtain ⟨k, hk, _, hlo, hhi, hcount⟩ := exists_fixed_finite_fiber_interval_bound_40_74 hodd hlarge
  have hsmooth :=
    fixed_smooth_count_at_rational_cutoff_74_40_of_bounds (Fact.out : p.Prime).pos hk hL hB hC hcL
      hMp hgap (henv k hhi) hlo
  obtain ⟨q, hq, hqB, hpow⟩ := exists_prime_nontrivial_power_of_interval_and_smooth hcount hsmooth
  exact
    ⟨q, hq,
      (Nat.cast_le.mpr (Nat.lt_add_one_iff.mp hqB)).trans
        (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)),
      hpow⟩

/-- At scale 74/40, pointwise smooth budgets yield a prime q≤log(p)^(1.850004)
whose Fermat quotient is nontrivial modulo p². Apply the explicit interval
cutoff and extract a prime factor from its smooth inputs. -/
theorem exists_prime_nontrivial_power_of_explicit_fiber_smooth_bounds_38_70 {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 242591045876 ≤ p)
    (hL : 2 ≤ Real.log p) (hB : 0 < Nat.floor ((Real.log p) ^ (184211 / 100000 : ℝ)))
    (hC : 0 < Nat.floor ((p : ℝ) ^ (160000019 / 190000000 : ℝ)))
    (hcL : 2 * (999997 / 1000000 : ℝ) ≤ Real.log (Real.log p))
    (hMp :
      2 * (Real.log p) ^ (1842109 / 1000000 : ℝ) ≤
        ((Nat.floor ((Real.log p) ^ (184211 / 100000 : ℝ))).primeCounting : ℝ))
    (hgap :
      (999997 / 1000000 : ℝ) * (184211 / 100000) * Real.log p +
          (184211 / 100000 : ℝ) * Real.log (Real.log p) <
        (70 / 38) * Real.log p)
    (henv :
      ∀ k : ℕ,
        k ^ 38 ≤ 2 ^ 38 * p ^ 70 →
          256 * k ≤ p * Nat.floor ((p : ℝ) ^ (160000019 / 190000000 : ℝ))) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (184211 / 100000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  obtain ⟨k, hk, _, hlo, hhi, hcount⟩ := exists_fixed_finite_fiber_interval_bound_38_70 hodd hlarge
  have hsmooth :=
    fixed_smooth_count_at_rational_cutoff_70_38_of_bounds (Fact.out : p.Prime).pos hk hL hB hC hcL
      hMp hgap (henv k hhi) hlo
  obtain ⟨q, hq, hqB, hpow⟩ := exists_prime_nontrivial_power_of_interval_and_smooth hcount hsmooth
  exact
    ⟨q, hq,
      (Nat.cast_le.mpr (Nat.lt_add_one_iff.mp hqB)).trans
        (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)),
      hpow⟩

/-- At scale 59/32, pointwise smooth budgets yield a prime q≤log(p)^(1.843755)
whose Fermat quotient is nontrivial modulo p². Apply the explicit interval
cutoff and extract a prime factor from its smooth inputs. -/
theorem exists_prime_nontrivial_power_of_explicit_fiber_smooth_bounds_32_59 {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 145000006050 ≤ p)
    (hL : 2 ≤ Real.log p) (hB : 0 < Nat.floor ((Real.log p) ^ (1843755 / 1000000 : ℝ)))
    (hC : 0 < Nat.floor ((p : ℝ) ^ (8437505 / 10000000 : ℝ)))
    (hcL : 2 * (999997 / 1000000 : ℝ) ≤ Real.log (Real.log p))
    (hMp :
      2 * (Real.log p) ^ (1843754 / 1000000 : ℝ) ≤
        ((Nat.floor ((Real.log p) ^ (1843755 / 1000000 : ℝ))).primeCounting : ℝ))
    (hgap :
      (999997 / 1000000 : ℝ) * (1843755 / 1000000) * Real.log p +
          (1843755 / 1000000 : ℝ) * Real.log (Real.log p) <
        (59 / 32) * Real.log p)
    (henv :
      ∀ k : ℕ,
        k ^ 32 ≤ 2 ^ 32 * p ^ 59 → 256 * k ≤ p * Nat.floor ((p : ℝ) ^ (8437505 / 10000000 : ℝ))) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (1843755 / 1000000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  obtain ⟨k, hk, _, hlo, hhi, hcount⟩ := exists_fixed_finite_fiber_interval_bound_32_59 hodd hlarge
  have hsmooth :=
    fixed_smooth_count_at_rational_cutoff_59_32_of_bounds (Fact.out : p.Prime).pos hk hL hB hC hcL
      hMp hgap (henv k hhi) hlo
  obtain ⟨q, hq, hqB, hpow⟩ := exists_prime_nontrivial_power_of_interval_and_smooth hcount hsmooth
  exact
    ⟨q, hq,
      (Nat.cast_le.mpr (Nat.lt_add_one_iff.mp hqB)).trans
        (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)),
      hpow⟩

/-- At scale 19/10, pointwise smooth budgets yield a prime q≤log(p)^1.900002716
whose Fermat quotient is nontrivial modulo p². Apply the explicit interval
cutoff and extract a prime factor from its smooth inputs. -/
theorem exists_prime_nontrivial_power_of_explicit_fiber_smooth_bounds_10_19 {p : ℕ} [Fact p.Prime]
    (hodd : Odd p) (hlarge : explicitFiniteFiberPrimeThreshold 4449271510 ≤ p) (hL : 2 ≤ Real.log p)
    (hB : 0 < Nat.floor ((Real.log p) ^ (1900000016707 / 1000000000000 : ℝ)))
    (hC : 0 < Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ)))
    (hcL : 2 * (999999990558 / 1000000000000 : ℝ) ≤ Real.log (Real.log p))
    (hMp :
      2 * (Real.log p) ^ (1900000008498 / 1000000000000 : ℝ) ≤
        ((Nat.floor ((Real.log p) ^ (1900000016707 / 1000000000000 : ℝ))).primeCounting : ℝ))
    (hgap :
      (999999990558 / 1000000000000 : ℝ) * (1900000016707 / 1000000000000) * Real.log p +
          (1900000016707 / 1000000000000 : ℝ) * Real.log (Real.log p) <
        (19 / 10) * Real.log p)
    (henv :
      ∀ k : ℕ,
        k ^ 10 ≤ 2 ^ 10 * p ^ 19 →
          256 * k ≤ p * Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ))) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (1900000016707 / 1000000000000 : ℝ) ∧
        (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  obtain ⟨k, hk, _, hlo, hhi, hcount⟩ :=
    exists_fixed_finite_fiber_interval_bound_10_19 hodd (by norm_num only : 76598623 ≤ 4449271510)
      hlarge
  have hsmooth :=
    fixed_smooth_count_at_rational_cutoff_19_10_of_bounds (Fact.out : p.Prime).pos hk hL hB hC hcL
      hMp hgap (henv k hhi) hlo
  obtain ⟨q, hq, hqB, hpow⟩ := exists_prime_nontrivial_power_of_interval_and_smooth hcount hsmooth
  exact
    ⟨q, hq,
      (Nat.cast_le.mpr (Nat.lt_add_one_iff.mp hqB)).trans
        (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)),
      hpow⟩

/-- At scale 19/10, the sharper threshold-specific smooth budgets yield a
prime q at most (log p)^1.9000007986 with nontrivial Fermat quotient modulo p². -/
theorem exists_prime_nontrivial_power_of_explicit_fiber_smooth_bounds_10_19_53m {p u : ℕ}
    [Fact p.Prime] (hodd : Odd p) (hu : 76598623 ≤ u)
    (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) (hL : 2 ≤ Real.log p)
    (hB : 0 < Nat.floor ((Real.log p) ^ (19000007986 / 10000000000 : ℝ)))
    (hC : 0 < Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ)))
    (hcL : 2 * (99999954008 / 100000000000 : ℝ) ≤ Real.log (Real.log p))
    (hMp :
      2 * (Real.log p) ^ (1900000414 / 1000000000 : ℝ) ≤
        ((Nat.floor ((Real.log p) ^ (19000007986 / 10000000000 : ℝ))).primeCounting : ℝ))
    (hgap :
      (99999954008 / 100000000000 : ℝ) * (19000007986 / 10000000000) * Real.log p +
          (19000007986 / 10000000000 : ℝ) * Real.log (Real.log p) <
        (19 / 10) * Real.log p)
    (henv :
      ∀ k : ℕ,
        k ^ 10 ≤ 2 ^ 10 * p ^ 19 →
          256 * k ≤ p * Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ))) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (19000007986 / 10000000000 : ℝ) ∧
        (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  obtain ⟨k, hk, _, hlo, hhi, hcount⟩ :=
    exists_fixed_finite_fiber_interval_bound_10_19 hodd hu hlarge
  have hp := (Fact.out : p.Prime).pos
  have hlogC :=
    Real.log_le_log (Nat.cast_pos.mpr hC)
      (Nat.floor_le
        (Real.rpow_nonneg (Nat.cast_nonneg p) (900000000000000001 / 1000000000000000000 : ℝ)))
  rw [Real.log_rpow (Nat.cast_pos.mpr hp) (900000000000000001 / 1000000000000000000 : ℝ)] at hlogC
  have hsmooth :=
    smooth_count_at_rational_cutoff_of_log_bounds (a := 10) (t := 19) (A :=
      19000007986 / 10000000000) (b := 1900000414 / 1000000000) (c := 99999954008 / 100000000000)
      (beta := 900000000000000001 / 1000000000000000000) (by decide) hp hB hC hk hL
      (by norm_num only) (by norm_num only : (1 : ℝ) < 1900000414 / 1000000000)
      (by norm_num only : (0 : ℝ) < 99999954008 / 100000000000)
      (by norm_num only :
        (900000000000000001 : ℝ) / 1000000000000000000 <
          (99999954008 / 100000000000) * (1900000414 / 1000000000 - 1))
      hcL hMp (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)) hgap hlogC (henv k hhi)
      hlo
  obtain ⟨q, hq, hqB, hpow⟩ := exists_prime_nontrivial_power_of_interval_and_smooth hcount hsmooth
  exact
    ⟨q, hq,
      (Nat.cast_le.mpr (Nat.lt_add_one_iff.mp hqB)).trans
        (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)),
      hpow⟩

end PseudoPrime.NumberTheory.Heilbronn
