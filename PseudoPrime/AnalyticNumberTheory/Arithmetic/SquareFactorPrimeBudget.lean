/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

/-! # Prime-factor budgets retaining a square-factor decomposition -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For n=s^2*d with nonzero factors, prime divisors lying in d have logarithm
sum at most log d, while the remaining prime divisors have sum at most log s.
The second support lies in s by prime divisibility of powers. This retains the
factor two in the input size before bounding two kinds of exclusion costs. -/
theorem primeFactor_log_square_split {n d s : ℕ} (hd : d ≠ 0) (hs : s ≠ 0) (hdec : s ^ 2 * d = n) :
    (∑ p ∈ n.primeFactors.filter (fun p ↦ p ∣ d), Real.log p) ≤ Real.log d ∧
      (∑ p ∈ n.primeFactors.filter (fun p ↦ ¬p ∣ d), Real.log p) ≤ Real.log s := by
  have hn : n ≠ 0 := hdec ▸ Nat.mul_ne_zero (pow_ne_zero 2 hs) hd
  have hR : n.primeFactors.filter (fun p ↦ p ∣ d) ⊆ d.primeFactors := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    exact (Nat.mem_primeFactors_of_ne_zero hd).mpr ⟨Nat.prime_of_mem_primeFactors h.1, h.2⟩
  have hE : n.primeFactors.filter (fun p ↦ ¬p ∣ d) ⊆ s.primeFactors := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    have hpr := (Nat.mem_primeFactors_of_ne_zero hn).mp h.1
    have hpn := hpr.2
    rw [← hdec] at hpn
    exact
      (Nat.mem_primeFactors_of_ne_zero hs).mpr
        ⟨hpr.1, hpr.1.dvd_of_dvd_pow ((hpr.1.dvd_mul.mp hpn).resolve_right h.2)⟩
  have hr :=
    Finset.sum_le_sum_of_subset_of_nonneg hR
      (fun p hp _ ↦ Real.log_nonneg (Nat.one_le_cast.mpr (Nat.prime_of_mem_primeFactors hp).one_le))
  have he :=
    Finset.sum_le_sum_of_subset_of_nonneg hE
      (fun p hp _ ↦ Real.log_nonneg (Nat.one_le_cast.mpr (Nat.prime_of_mem_primeFactors hp).one_le))
  exact ⟨hr.trans (sum_log_primeFactors_le_log hd), he.trans (sum_log_primeFactors_le_log hs)⟩

/-- For nonzero d,s with n=s^2*d, log n=log d+2log s. Rewrite the product
and square with nonzero real casts. This connects support costs with the input
and conductor logarithms without discarding the square-factor saving. -/
theorem log_square_factor_decomposition {n d s : ℕ} (hd : d ≠ 0) (hs : s ≠ 0)
    (hdec : s ^ 2 * d = n) : Real.log n = Real.log d + 2 * Real.log s := by
  rw [← hdec, Nat.cast_mul, Nat.cast_pow,
    Real.log_mul (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hs)) (Nat.cast_ne_zero.mpr hd), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  ring

/-- For n=s^2*d and nonnegative rates a,b, a prime cost bounded by a log p on
d and 2b log p off d has total at most b log n+(a-b)log d. Split the supports
before using their logarithm bounds. No sign assumption on the cost itself is needed. -/
theorem sum_prime_cost_le_square_factor_budget {n d s : ℕ} (hd : d ≠ 0) (hs : s ≠ 0)
    (hdec : s ^ 2 * d = n) (F : ℕ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hR : ∀ p ∈ n.primeFactors, p ∣ d → F p ≤ a * Real.log p)
    (hE : ∀ p ∈ n.primeFactors, ¬p ∣ d → F p ≤ 2 * b * Real.log p) :
    (∑ p ∈ n.primeFactors, F p) ≤ b * Real.log n + (a - b) * Real.log d := by
  have hl := primeFactor_log_square_split hd hs hdec
  have h1 :=
    Finset.sum_le_sum (s := n.primeFactors.filter (fun p ↦ p ∣ d))
      (fun p hp ↦ hR p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2)
  have h2 :=
    Finset.sum_le_sum (s := n.primeFactors.filter (fun p ↦ ¬p ∣ d))
      (fun p hp ↦ hE p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2)
  rw [← Finset.mul_sum] at h1 h2
  have h3 := mul_le_mul_of_nonneg_left hl.1 ha
  have h4 := mul_le_mul_of_nonneg_left hl.2 (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hb)
  rw [← Finset.sum_filter_add_sum_filter_not n.primeFactors (fun p ↦ p ∣ d) F,
    log_square_factor_decomposition hd hs hdec]
  linarith only [h1, h2, h3, h4]

/-- The square-factor budget with nonnegative finite exceptional costs.
Subtract each exception before applying the two-rate bound, then enlarge its
support to the fixed exception set. This accepts analytic prime tails and small
prime deficits while retaining the conductor/input correlation. -/
theorem sum_prime_cost_le_square_factor_budget_add_excess {n d s : ℕ} (hd : d ≠ 0) (hs : s ≠ 0)
    (hdec : s ^ 2 * d = n) (F : ℕ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (T : Finset ℕ)
    (e : ℕ → ℝ) (he : ∀ p ∈ T, 0 ≤ e p)
    (hR : ∀ p ∈ n.primeFactors, p ∣ d → F p ≤ a * Real.log p + if p ∈ T then e p else 0)
    (hE : ∀ p ∈ n.primeFactors, ¬p ∣ d → F p ≤ 2 * b * Real.log p + if p ∈ T then e p else 0) :
    (∑ p ∈ n.primeFactors, F p) ≤ b * Real.log n + (a - b) * Real.log d + ∑ p ∈ T, e p := by
  let G := fun p : ℕ ↦ F p - (if p ∈ T then e p else 0)
  have hG :=
    sum_prime_cost_le_square_factor_budget hd hs hdec G ha hb
      (fun p hp hpd ↦ by
        dsimp only [G]; linarith only [hR p hp hpd])
      (fun p hp hpd ↦ by
        dsimp only [G]; linarith only [hE p hp hpd])
  have hsub : n.primeFactors.filter (fun p ↦ p ∈ T) ⊆ T := fun _ hp ↦ (Finset.mem_filter.mp hp).2
  have hδ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ ↦ he p hp)
  rw [Finset.sum_filter] at hδ
  dsimp only [G] at hG
  rw [Finset.sum_sub_distrib] at hG
  linarith only [hG, hδ]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
