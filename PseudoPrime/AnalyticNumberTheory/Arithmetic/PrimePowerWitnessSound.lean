/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimePowerWitnessExecution
import Mathlib.Order.Interval.Finset.Nat

/-! # Soundness of sequential prime-power support certificates -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A product of two coprime naturals greater than one is not a prime power.
A prime power dividing their product would have to divide one factor, which
is impossible because the product is strictly larger than either factor. -/
private theorem not_prime_power_mul {d e : ℕ} (hd : 1 < d) (he : 1 < e) (hc : Nat.Coprime d e) :
    ¬IsPrimePow (d * e) := by
  intro hp
  have h := (hc.isPrimePow_dvd_mul hp).mp (dvd_refl (d * e))
  rcases h with h | h
  · have hle := Nat.le_of_dvd (Nat.zero_lt_of_lt hd) h
    have hm := Nat.mul_lt_mul_of_pos_left he (Nat.zero_lt_of_lt hd)
    rw [Nat.mul_one] at hm
    exact (Nat.not_lt_of_ge hle) hm
  · have hle := Nat.le_of_dvd (Nat.zero_lt_of_lt he) h
    have hm := Nat.mul_lt_mul_of_pos_right hd (Nat.zero_lt_of_lt he)
    rw [Nat.one_mul] at hm
    exact (Nat.not_lt_of_ge hle) hm

/-- A successful witness check marks every prime power with zero. Nonzero
witnesses are checked by division and coprimality rather than a prime-power
search; zero marks require a separate prime-power certification. -/
theorem prime_power_witness_sound {n d : ℕ} (h : primePowerWitnessCheck n d = true)
    (hp : IsPrimePow n) : d = 0 := by
  by_contra hd
  simp only [primePowerWitnessCheck, hd, ite_false, decide_eq_true_eq] at h
  have hdiv : d ∣ n := Nat.dvd_of_mod_eq_zero h.2.1
  have heq : d * (n / d) = n := Nat.mul_div_cancel' hdiv
  have hn : ¬IsPrimePow n := by
    rw [← heq]
    exact not_prime_power_mul h.1 h.2.2.1 h.2.2.2
  exact hn hp

/-- A successful sequential scan extracts exactly the prime powers in the
consecutive range beginning at `n`, provided every zero-marked event is a
prime power. The proof follows the witness list without indexed lookup. -/
theorem prime_power_events_eq_filter {n : ℕ} {ws : List ℕ} (h : primePowerWitnessScan n ws = true)
    (hv : ∀ m ∈ primePowerWitnessEvents n ws, IsPrimePow m) :
    primePowerWitnessEvents n ws =
      (List.range' n ws.length).filter (fun t ↦ decide (IsPrimePow t)) := by
  induction ws generalizing n with
  | nil => rfl
  | cons d ds ih =>
    simp only [primePowerWitnessScan, Bool.and_eq_true] at h
    have htail : ∀ m ∈ primePowerWitnessEvents (n + 1) ds, IsPrimePow m := by
      intro m hm
      apply hv m
      simp only [primePowerWitnessEvents]
      by_cases hd : d = 0
      · simp only [hd, ite_true, List.mem_cons]
        exact Or.inr hm
      · simpa only [hd, ite_false] using hm
    have ht := ih h.2 htail
    simp only [List.length_cons, List.range'_succ, List.filter_cons, primePowerWitnessEvents]
    rw [ht]
    by_cases hzero : d = 0
    · have hp : IsPrimePow n := by
        apply hv n
        simp only [primePowerWitnessEvents, hzero, ite_true, List.mem_cons, true_or]
      simp only [hzero, ite_true, decide_eq_true hp]
    · have hp : ¬IsPrimePow n := fun hn ↦ hzero (prime_power_witness_sound h.1 hn)
      simp only [hzero, ite_false, decide_eq_false hp, Bool.false_eq_true]

/-- A checked witness stream and independently certified zero marks give the
exact finite set of prime powers in `[n, n + length)`. -/
theorem prime_power_events_finset {n : ℕ} {ws : List ℕ} (h : primePowerWitnessScan n ws = true)
    (hv : ∀ m ∈ primePowerWitnessEvents n ws, IsPrimePow m) :
    (primePowerWitnessEvents n ws).toFinset = (Finset.Ico n (n + ws.length)).filter IsPrimePow := by
  rw [prime_power_events_eq_filter h hv, List.toFinset_filter, List.toFinset_range'_1]
  simp only [decide_eq_true_eq]

/-- The events extracted from a valid witness stream with certified zero marks
are distinct, because they form a sublist of a consecutive range. -/
theorem prime_power_events_nodup {n : ℕ} {ws : List ℕ} (h : primePowerWitnessScan n ws = true)
    (hv : ∀ m ∈ primePowerWitnessEvents n ws, IsPrimePow m) :
    (primePowerWitnessEvents n ws).Nodup := by
  rw [prime_power_events_eq_filter h hv]
  exact List.Nodup.filter _ (List.nodup_range')

end PseudoPrime.AnalyticNumberTheory.Arithmetic
