/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix
import Mathlib.Tactic.Linarith

/-! # Certified lower prime counts using a shared remainder per batch -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev

/-- Multiply the wheel survivors in the dyadic interval (a,a+2^d]. -/
def candidateProduct (w : ℕ) : ℕ → ℕ → ℕ
  | 0, a => if (a + 1).gcd w = 1 then a + 1 else 1
  | d + 1, a => candidateProduct w d a * candidateProduct w d (a + 2 ^ d)

/-- Every wheel survivor divides the product used to reduce the large common factor base. -/
private theorem candidate_dvd {w n : ℕ} (d a : ℕ) (hl : a < n) (hu : n ≤ a + 2 ^ d)
    (hw : n.gcd w = 1) : n ∣ candidateProduct w d a := by
  induction d generalizing a with
  | zero =>
    have he : n = a + 1 := Nat.le_antisymm hu hl
    subst n
    simp only [candidateProduct, hw, ite_true, dvd_refl]
  | succ d ih =>
    rw [candidateProduct]
    by_cases hm : n ≤ a + 2 ^ d
    · exact dvd_mul_of_dvd_left (ih a hl hm) _
    · apply dvd_mul_of_dvd_right (ih (a + 2 ^ d) (Nat.lt_of_not_ge hm) _) _
      simpa only [pow_succ, Nat.mul_two, Nat.add_assoc] using hu

/-- Count only integers that survive the wheel and are coprime to the batch remainder. -/
def remainderCount (w r : ℕ) : ℕ → ℕ → ℕ
  | 0, a => if (a + 1).gcd w = 1 then (if (a + 1).gcd r = 1 then 1 else 0) else 0
  | d + 1, a => remainderCount w r d a + remainderCount w r d (a + 2 ^ d)

/-- The count of certified primes in a dyadic interval supplies a lower theta increment.
The predicate is needed only for the surviving integers in that interval. -/
private theorem count_increment {w r : ℕ} (d a lo : ℕ) (hlo : 1 ≤ lo) (ha : lo ≤ a)
    (ok : ∀ n, a < n → n ≤ a + 2 ^ d → n.gcd w = 1 → n.gcd r = 1 → n.Prime) :
    (remainderCount w r d a : ℝ) * Real.log lo ≤
      Chebyshev.theta (a + 2 ^ d : ℕ) - Chebyshev.theta a := by
  induction d generalizing a with
  | zero =>
    have hz : (0 : ℝ) ≤ Chebyshev.theta (a + 1 : ℕ) - Chebyshev.theta a :=
      sub_nonneg.mpr (Chebyshev.theta_mono (Nat.cast_le.mpr (Nat.le_succ a)))
    by_cases hw : (a + 1).gcd w = 1
    · by_cases hr : (a + 1).gcd r = 1
      · have hp := ok _ (Nat.lt_succ_self a) le_rfl hw hr
        have he := Arithmetic.theta_prefix_add_interval (Nat.le_succ a)
        simp only [Nat.Ioc_succ_singleton, Finset.filter_singleton, hp, ite_true,
          Finset.sum_singleton] at he
        have hl :=
          Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hlo) : (0 : ℝ) < lo)
            (Nat.cast_le.mpr (ha.trans (Nat.le_succ a)))
        simp only [remainderCount, hw, hr, ite_true, Nat.cast_one, one_mul, pow_zero]
        simp only [Nat.succ_eq_add_one] at he hl
        rw [← he, add_sub_cancel_left]
        exact hl
      · simpa only [remainderCount, hw, hr, ite_true, ite_false, Nat.cast_zero, zero_mul,
          pow_zero] using hz
    · simpa only [remainderCount, hw, ite_false, Nat.cast_zero, zero_mul, pow_zero] using hz
  | succ d
    ih =>
    have he : a + 2 ^ (d + 1) = a + 2 ^ d + 2 ^ d := by rw [pow_succ, Nat.mul_two, Nat.add_assoc]
    have h1 := ih a ha (fun n hn hb => ok n hn (hb.trans (he ▸ Nat.le_add_right _ _)))
    have h2 :=
      ih (a + 2 ^ d) (ha.trans (Nat.le_add_right _ _))
        (fun n hn hb => ok n (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hn) (he ▸ hb))
    rw [remainderCount, Nat.cast_add, add_mul, he]
    linarith only [h1, h2]

/-- Count survivors of the small wheel using one reduction of P per batch. -/
def batchPrimeCount (P w d a : ℕ) : ℕ :=
  remainderCount w (P % candidateProduct w d a) d a

/-- If P contains every trial divisor through B, the scalar batch count certifies a theta
increment as long as the interval ends below (B+1)^2. -/
theorem batch_prime_increment {P B : ℕ} (w d a lo : ℕ) (hlo : 1 ≤ lo) (ha : lo ≤ a)
    (hb : a + 2 ^ d < (B + 1) * (B + 1)) (cover : ∀ m, 2 ≤ m → m ≤ B → m ∣ P) :
    (batchPrimeCount P w d a : ℝ) * Real.log lo ≤
      Chebyshev.theta (a + 2 ^ d : ℕ) - Chebyshev.theta a := by
  unfold batchPrimeCount
  apply count_increment d a lo hlo ha
  intro n hn hu hw hr
  have hdiv := candidate_dvd d a hn hu hw
  have hmod := Nat.mod_mod_of_dvd P hdiv
  have hg : n.gcd P = 1 := by
    rw [Nat.gcd_rec n P, ← hmod, ← Nat.gcd_rec]
    exact hr
  have hs : n.sqrt ≤ B := Nat.le_of_lt_succ (Nat.sqrt_lt.mpr (hu.trans_lt hb))
  refine Nat.prime_def_le_sqrt.mpr ⟨Nat.succ_le_of_lt (lt_of_le_of_lt (hlo.trans ha) hn), ?_⟩
  intro m hm hms hmn
  exact (Nat.ne_of_gt hm) (Nat.eq_one_of_dvd_one (hg ▸ Nat.dvd_gcd hmn (cover m hm (hms.trans hs))))

/-- Sum dyadic batches of width 2^t, sharing one reduced factor base in each batch. -/
def tiledPrimeCount (P w t : ℕ) : ℕ → ℕ → ℕ
  | 0, a => batchPrimeCount P w t a
  | d + 1, a => tiledPrimeCount P w t d a + tiledPrimeCount P w t d (a + 2 ^ (t + d))

/-- On a dyadic tile the sum of batch counts certifies the lower theta increment.
Each batch uses the same logarithmic floor and independently reduces the common factor base. -/
theorem tiled_prime_increment {P B : ℕ} (w t d a lo : ℕ) (hlo : 1 ≤ lo) (ha : lo ≤ a)
    (hb : a + 2 ^ (t + d) < (B + 1) * (B + 1)) (cover : ∀ m, 2 ≤ m → m ≤ B → m ∣ P) :
    (tiledPrimeCount P w t d a : ℝ) * Real.log lo ≤
      Chebyshev.theta (a + 2 ^ (t + d) : ℕ) - Chebyshev.theta a := by
  induction d generalizing a with
  | zero => exact batch_prime_increment w t a lo hlo ha hb cover
  | succ d
    ih =>
    have he : a + 2 ^ (t + (d + 1)) = a + 2 ^ (t + d) + 2 ^ (t + d) := by
      rw [← Nat.add_assoc, pow_succ, Nat.mul_two, Nat.add_assoc]
    have h1 := ih a ha (lt_of_le_of_lt (Nat.le_add_right _ _) (he ▸ hb))
    have h2 := ih (a + 2 ^ (t + d)) (ha.trans (Nat.le_add_right _ _)) (he ▸ hb)
    rw [tiledPrimeCount, Nat.cast_add, add_mul, he]
    linarith only [h1, h2]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev
