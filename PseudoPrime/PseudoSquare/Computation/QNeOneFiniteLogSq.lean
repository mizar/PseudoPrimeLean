/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PseudoSquare.Computation.QThresholds
import PseudoPrime.PseudoSquare.Computation.MillionWitnessBridge
import PseudoPrime.PseudoSquare.Bounds.ElementaryOmegaFinal

/-!
# Finite logarithmic bounds for Q witnesses

The results in this module use only the neutral Q witness API and finite small-wheel bounds.
-/

namespace PseudoPrime.PseudoSquare

theorem fortySeven_le_log_sq_of_1024_le {n : ℕ} (hn : 1024 ≤ n) :
    (47 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hnR : (1024 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog :=
    Real.strictMonoOn_log.monotoneOn (by norm_num only : (0 : ℝ) < 1024)
      (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n) hnR
  have hlog1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num only, Real.log_pow]
    norm_num only
  have hloglower : (6.9 : ℝ) < Real.log (n : ℝ) := by
    linarith only [hlog, hlog1024, Real.log_two_gt_d9]
  nlinarith only [hloglower, sq_nonneg (Real.log (n : ℝ) - (69 / 10 : ℝ))]

theorem primeNeOneWitness_cast_le_log_sq_of_1024_le_of_lt_million {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : 1024 ≤ n) (hhi : n < 1000000) :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  have hw := primeNeOneWitness_le_fortySeven_of_lt_million hn hns hhi
  have hwR :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      47 := by
    exact_mod_cast hw
  exact hwR.trans (fortySeven_le_log_sq_of_1024_le hlo)

theorem primeNeOneWitness_le_five_of_lt_sixteen {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hB : n < 16) :
    NumberTheory.primeNeOneWitness n
        (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) ≤
      5 := by
  obtain ⟨p, hp, hj⟩ := qNeOneSmall15_exists hn hns hB
  simp only [qNeOneSmall15Primes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  all_goals
    exact
      (NumberTheory.primeNeOneWitness_le n _ ⟨by decide, by decide, hj⟩).trans (by norm_num only)

theorem primeNeOneWitness_le_seven_of_lt_sixtyFour {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hB : n < 64) :
    NumberTheory.primeNeOneWitness n
        (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) ≤
      7 := by
  obtain ⟨p, hp, hj⟩ := qNeOneSmall63_exists hn hns hB
  simp only [qNeOneSmall63Primes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    exact
      (NumberTheory.primeNeOneWitness_le n _ ⟨by decide, by decide, hj⟩).trans (by norm_num only)

theorem log_two_mul_le_log_of_pow_two_le {n k : ℕ} (hn : 2 ^ k ≤ n) :
    (k : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
  have hR : (2 : ℝ) ^ k ≤ n := by exact_mod_cast hn
  have hlog :=
    Real.strictMonoOn_log.monotoneOn
      (by exact_mod_cast Nat.pow_pos (by norm_num only : (0 : ℕ) < 2) : (0 : ℝ) < 2 ^ k)
      (lt_of_lt_of_le
        (by exact_mod_cast Nat.pow_pos (by norm_num only : (0 : ℕ) < 2) : (0 : ℝ) < 2 ^ k) hR)
      hR
  simpa only [Real.log_pow] using hlog

theorem five_le_log_sq_of_eleven_le {n : ℕ} (hn : 11 ≤ n) : (5 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast (show 10 ≤ n by omega)
  have hlog :=
    Real.strictMonoOn_log.monotoneOn (by norm_num only : (0 : ℝ) < 10)
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 10) hnR) hnR
  rw [show (10 : ℝ) = 2 * 5 by norm_num only,
    Real.log_mul (by norm_num only) (by norm_num only)] at hlog
  have hloglower : (2.3 : ℝ) < Real.log (n : ℝ) := by
    linarith only [hlog, Real.log_two_gt_d9, Real.log_five_gt_d9]
  nlinarith only [hloglower, sq_nonneg (Real.log (n : ℝ) - (23 / 10 : ℝ))]

theorem seven_le_log_sq_of_sixteen_le {n : ℕ} (hn : 16 ≤ n) : (7 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hlog := log_two_mul_le_log_of_pow_two_le (k := 4) hn
  norm_num only at hlog
  have hloglower : (2.7 : ℝ) < Real.log (n : ℝ) := by linarith only [hlog, Real.log_two_gt_d9]
  nlinarith only [hloglower, sq_nonneg (Real.log (n : ℝ) - (27 / 10 : ℝ))]

theorem thirteen_le_log_sq_of_sixtyFour_le {n : ℕ} (hn : 64 ≤ n) :
    (13 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hlog := log_two_mul_le_log_of_pow_two_le (k := 6) hn
  norm_num only at hlog
  have hloglower : (4 : ℝ) < Real.log (n : ℝ) := by linarith only [hlog, Real.log_two_gt_d9]
  nlinarith only [hloglower, sq_nonneg (Real.log (n : ℝ) - 4)]

theorem primeNeOneWitness_cast_le_log_sq_of_eleven_le_of_lt_sixtyFour {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : 11 ≤ n) (hhi : n < 64) :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  by_cases h16 : 16 ≤ n
  · exact
      (Nat.cast_le.mpr (primeNeOneWitness_le_seven_of_lt_sixtyFour hn hns hhi)).trans
        (seven_le_log_sq_of_sixteen_le h16)
  · exact
      (Nat.cast_le.mpr (primeNeOneWitness_le_five_of_lt_sixteen hn hns (by omega))).trans
        (five_le_log_sq_of_eleven_le hlo)

/-- For odd nonsquares from `1001` through `1030`, one of the odd primes at most `19`
has Jacobi value different from `1`. Nonsquareness is expressed by finite square exclusions. -/
def Through1030NeOneCertificate : Prop :=
  ∀ n : Fin 1031,
    1001 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 33, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

/-- For odd nonsquares from `1031` through `1060`, one of the odd primes at most `19`
has Jacobi value different from `1`. Nonsquareness is expressed by finite square exclusions. -/
def Through1060NeOneCertificate : Prop :=
  ∀ n : Fin 1061,
    1031 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 34, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

/-- For odd nonsquares from `1061` through `1090`, one of the odd primes at most `19`
has Jacobi value different from `1`. Nonsquareness is expressed by finite square exclusions. -/
def Through1090NeOneCertificate : Prop :=
  ∀ n : Fin 1091,
    1061 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 35, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

/-- For odd nonsquares from `1091` through `1125`, one of the odd primes at most `19`
has Jacobi value different from `1`. Nonsquareness is expressed by finite square exclusions. -/
def Through1125TailNeOneCertificate : Prop :=
  ∀ n : Fin 1126,
    1091 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 36, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

theorem through1030NeOneCertificate_valid : Through1030NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem through1060NeOneCertificate_valid : Through1060NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem through1090NeOneCertificate_valid : Through1090NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem through1125TailNeOneCertificate_valid : Through1125TailNeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

/-- The combined certificate for odd nonsquares from `1001` through `1125`, supplying an
odd-prime Jacobi witness different from `1` at most `19`. -/
def Through1125NeOneCertificate : Prop :=
  ∀ n : Fin 1126,
    1001 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 36, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

/-- The combined finite certificate for `1001 ≤ n ≤ 1125`. -/
theorem through1125NeOneCertificate_valid : Through1125NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

/-- Every odd nonsquare in `1001 ≤ n ≤ 1125` has least witness at most `19`. -/
theorem primeNeOneWitness_le_nineteen_of_1001_le_of_le_1125 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hn1001 : 1001 ≤ n) (hn1125 : n ≤ 1125) :
    NumberTheory.primeNeOneWitness n
        (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) ≤
      19 := by
  have hnosquare : ∀ k : Fin 36, n ≠ k.val ^ 2 := by
    intro k hk
    exact hns ⟨k.val, by simpa only [pow_two] using hk⟩
  have hcertificate :=
    through1125NeOneCertificate_valid ⟨n, Nat.lt_succ_iff.mpr hn1125⟩ hn1001 (Nat.odd_iff.mp hn)
      hnosquare
  obtain hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi := hcertificate
  all_goals
    exact
      (NumberTheory.primeNeOneWitness_le n _ ⟨by decide, by decide, hjacobi⟩).trans
        (by norm_num only)

/-- The `1001`--`1125` finite block lies inside the logarithmic witness radius. -/
theorem nineteen_le_log_sq_of_1001_le {n : ℕ} (hn1001 : 1001 ≤ n) :
    (19 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hn128 : (128 : ℝ) ≤ n := by exact_mod_cast (show 128 ≤ n by omega)
  have hlog :=
    Real.strictMonoOn_log.monotoneOn (show (0 : ℝ) < 128 by norm_num only)
      (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n) hn128
  have hlog128 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num only, Real.log_pow]
    norm_num only
  have h2 := Real.log_two_gt_d9
  have hloglower : (4.83 : ℝ) < Real.log (n : ℝ) := by linarith only [hlog, hlog128, h2]
  nlinarith only [hloglower, sq_nonneg (Real.log (n : ℝ) - (483 / 100 : ℝ))]

theorem primeNeOneWitness_cast_le_log_sq_of_1001_le_of_le_1125 {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hn1001 : 1001 ≤ n) (hn1125 : n ≤ 1125) :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  have hw := primeNeOneWitness_le_nineteen_of_1001_le_of_le_1125 hn hns hn1001 hn1125
  have hwR :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      19 := by
    exact_mod_cast hw
  exact hwR.trans (nineteen_le_log_sq_of_1001_le hn1001)

/-- For odd nonsquares from `1126` through `1155`, one of the odd primes at most `19`
has Jacobi value different from `1`. Nonsquareness is expressed by finite square exclusions. -/
def Through1155NeOneCertificate : Prop :=
  ∀ n : Fin 1156,
    1126 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 35, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

/-- For odd nonsquares from `1156` through `1185`, one of the odd primes at most `19`
has Jacobi value different from `1`. Nonsquareness is expressed by finite square exclusions. -/
def Through1185NeOneCertificate : Prop :=
  ∀ n : Fin 1186,
    1156 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 35, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

/-- For odd nonsquares from `1186` through `1215`, one of the odd primes at most `19`
has Jacobi value different from `1`. Nonsquareness is expressed by finite square exclusions. -/
def Through1215NeOneCertificate : Prop :=
  ∀ n : Fin 1216,
    1186 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 35, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

/-- For odd nonsquares from `1216` through `1250`, one of the odd primes at most `19`
has Jacobi value different from `1`. Nonsquareness is expressed by finite square exclusions. -/
def Through1250TailNeOneCertificate : Prop :=
  ∀ n : Fin 1251,
    1216 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 36, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

theorem through1155NeOneCertificate_valid : Through1155NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem through1185NeOneCertificate_valid : Through1185NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem through1215NeOneCertificate_valid : Through1215NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem through1250TailNeOneCertificate_valid : Through1250TailNeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

/-- The combined certificate for odd nonsquares from `1126` through `1250`, supplying an
odd-prime Jacobi witness different from `1` at most `19`. -/
def Through1250NeOneCertificate : Prop :=
  ∀ n : Fin 1251,
    1126 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 36, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

theorem through1250NeOneCertificate_valid : Through1250NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

/-- Every odd nonsquare in `1126 ≤ n ≤ 1250` has least witness at most `19`. -/
theorem primeNeOneWitness_le_nineteen_of_1126_le_of_le_1250 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hn1126 : 1126 ≤ n) (hn1250 : n ≤ 1250) :
    NumberTheory.primeNeOneWitness n
        (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) ≤
      19 := by
  have hnosquare : ∀ k : Fin 36, n ≠ k.val ^ 2 := by
    intro k hk
    exact hns ⟨k.val, by simpa only [pow_two] using hk⟩
  have hcertificate :=
    through1250NeOneCertificate_valid ⟨n, Nat.lt_succ_iff.mpr hn1250⟩ hn1126 (Nat.odd_iff.mp hn)
      hnosquare
  obtain hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi := hcertificate
  all_goals
    exact
      (NumberTheory.primeNeOneWitness_le n _ ⟨by decide, by decide, hjacobi⟩).trans
        (by norm_num only)

/-- The `1126`--`1250` finite block supplies the logarithmic witness bound. -/
theorem primeNeOneWitness_cast_le_log_sq_of_1126_le_of_le_1250 {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hn1126 : 1126 ≤ n) (hn1250 : n ≤ 1250) :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  have hw := primeNeOneWitness_le_nineteen_of_1126_le_of_le_1250 hn hns hn1126 hn1250
  have hwR :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      19 := by
    exact_mod_cast hw
  exact hwR.trans (nineteen_le_log_sq_of_1001_le (by omega))

/-- The first small block of the `1251`--`1375` finite certificate. -/
def Through1280NeOneCertificate : Prop :=
  ∀ n : Fin 1281,
    1251 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 36, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

/-- The second small block of the `1251`--`1375` finite certificate. -/
def Through1310NeOneCertificate : Prop :=
  ∀ n : Fin 1311,
    1281 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 37, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

/-- The third small block of the `1251`--`1375` finite certificate. -/
def Through1340NeOneCertificate : Prop :=
  ∀ n : Fin 1341,
    1311 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 37, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

/-- The fourth small block of the `1251`--`1375` finite certificate. -/
def Through1375TailNeOneCertificate : Prop :=
  ∀ n : Fin 1376,
    1341 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 38, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

theorem through1280NeOneCertificate_valid : Through1280NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem through1310NeOneCertificate_valid : Through1310NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem through1340NeOneCertificate_valid : Through1340NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem through1375TailNeOneCertificate_valid : Through1375TailNeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

def Through1375NeOneCertificate : Prop :=
  ∀ n : Fin 1376,
    1251 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 38, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

theorem through1375NeOneCertificate_valid : Through1375NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem primeNeOneWitness_le_nineteen_of_1251_le_of_le_1375 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hn1251 : 1251 ≤ n) (hn1375 : n ≤ 1375) :
    NumberTheory.primeNeOneWitness n
        (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) ≤
      19 := by
  have hnosquare : ∀ k : Fin 38, n ≠ k.val ^ 2 := by
    intro k hk
    exact hns ⟨k.val, by simpa only [pow_two] using hk⟩
  have hcertificate :=
    through1375NeOneCertificate_valid ⟨n, Nat.lt_succ_iff.mpr hn1375⟩ hn1251 (Nat.odd_iff.mp hn)
      hnosquare
  obtain hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi := hcertificate
  all_goals
    exact
      (NumberTheory.primeNeOneWitness_le n _ ⟨by decide, by decide, hjacobi⟩).trans
        (by norm_num only)

theorem primeNeOneWitness_cast_le_log_sq_of_1251_le_of_le_1375 {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hn1251 : 1251 ≤ n) (hn1375 : n ≤ 1375) :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  have hw := primeNeOneWitness_le_nineteen_of_1251_le_of_le_1375 hn hns hn1251 hn1375
  have hwR :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      19 := by
    exact_mod_cast hw
  exact hwR.trans (nineteen_le_log_sq_of_1001_le (by omega))

/-- The first small block of the `1376`--`1500` finite certificate. -/
def Through1405NeOneCertificate : Prop :=
  ∀ n : Fin 1406,
    1376 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 39, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

/-- The second small block of the `1376`--`1500` finite certificate. -/
def Through1435NeOneCertificate : Prop :=
  ∀ n : Fin 1436,
    1406 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 39, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

/-- The third small block of the `1376`--`1500` finite certificate. -/
def Through1465NeOneCertificate : Prop :=
  ∀ n : Fin 1466,
    1436 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 40, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

/-- The fourth small block of the `1376`--`1500` finite certificate. -/
def Through1500TailNeOneCertificate : Prop :=
  ∀ n : Fin 1501,
    1466 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 40, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

theorem through1405NeOneCertificate_valid : Through1405NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem through1435NeOneCertificate_valid : Through1435NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem through1465NeOneCertificate_valid : Through1465NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem through1500TailNeOneCertificate_valid : Through1500TailNeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

def Through1500NeOneCertificate : Prop :=
  ∀ n : Fin 1501,
    1376 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 40, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨
        jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1 ∨ jacobiSym n.val 19 ≠ 1

theorem through1500NeOneCertificate_valid : Through1500NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1500_to_or hw

theorem primeNeOneWitness_le_nineteen_of_1376_le_of_le_1500 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hn1376 : 1376 ≤ n) (hn1500 : n ≤ 1500) :
    NumberTheory.primeNeOneWitness n
        (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) ≤
      19 := by
  have hnosquare : ∀ k : Fin 40, n ≠ k.val ^ 2 := by
    intro k hk
    exact hns ⟨k.val, by simpa only [pow_two] using hk⟩
  have hcertificate :=
    through1500NeOneCertificate_valid ⟨n, Nat.lt_succ_iff.mpr hn1500⟩ hn1376 (Nat.odd_iff.mp hn)
      hnosquare
  obtain hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi := hcertificate
  all_goals
    exact
      (NumberTheory.primeNeOneWitness_le n _ ⟨by decide, by decide, hjacobi⟩).trans
        (by norm_num only)

theorem primeNeOneWitness_cast_le_log_sq_of_1376_le_of_le_1500 {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hn1376 : 1376 ≤ n) (hn1500 : n ≤ 1500) :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  have hw := primeNeOneWitness_le_nineteen_of_1376_le_of_le_1500 hn hns hn1376 hn1500
  have hwR :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      19 := by
    exact_mod_cast hw
  exact hwR.trans (nineteen_le_log_sq_of_1001_le (by omega))

/-! The finite certificate and logarithmic bound for `751 ≤ n ≤ 1000`. -/

def Through1000NeOneCertificate : Prop :=
  ∀ n : Fin 1001,
    751 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 32, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨ jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1

theorem through1000NeOneCertificate_valid : Through1000NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall1000_exists (Nat.odd_iff.mpr hnodd) hsq (by omega)
  exact exists_qNeOneSmall1000_to_or hw

theorem primeNeOneWitness_le_seventeen_of_751_le_of_le_1000 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hn751 : 751 ≤ n) (hn1000 : n ≤ 1000) :
    NumberTheory.primeNeOneWitness n
        (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) ≤
      17 := by
  have hnosquare : ∀ k : Fin 32, n ≠ k.val ^ 2 := by
    intro k hk
    exact hns ⟨k.val, by simpa only [pow_two] using hk⟩
  have hcertificate :=
    through1000NeOneCertificate_valid ⟨n, Nat.lt_succ_iff.mpr hn1000⟩ hn751 (Nat.odd_iff.mp hn)
      hnosquare
  obtain hjacobi | hjacobi | hjacobi | hjacobi | hjacobi | hjacobi := hcertificate
  all_goals
    exact
      (NumberTheory.primeNeOneWitness_le n _ ⟨by decide, by decide, hjacobi⟩).trans
        (by norm_num only)

theorem seventeen_le_log_sq_of_751_le {n : ℕ} (hn751 : 751 ≤ n) :
    (17 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hn64 : (64 : ℝ) ≤ n := by exact_mod_cast (show 64 ≤ n by omega)
  have hlog :=
    Real.strictMonoOn_log.monotoneOn (show (0 : ℝ) < 64 by norm_num only)
      (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n) hn64
  have hlog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num only, Real.log_pow]
    norm_num only
  have h2 := Real.log_two_gt_d9
  have hloglower : (4.14 : ℝ) < Real.log (n : ℝ) := by
    have h069 : (0.69 : ℝ) < Real.log 2 := (by norm_num only : (0.69 : ℝ) < 0.6931471803).trans h2
    exact
      calc
        (4.14 : ℝ) = 6 * (0.69 : ℝ) := by norm_num only
        _ < 6 * Real.log 2 := by exact mul_lt_mul_of_pos_left h069 (by norm_num only)
        _ = Real.log (64 : ℝ) := hlog64.symm
        _ ≤ Real.log (n : ℝ) := hlog
  nlinarith only [hloglower, sq_nonneg (Real.log (n : ℝ) - (207 / 50 : ℝ))]

theorem primeNeOneWitness_cast_le_log_sq_of_751_le_of_le_1000 {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hn751 : 751 ≤ n) (hn1000 : n ≤ 1000) :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  have hw := primeNeOneWitness_le_seventeen_of_751_le_of_le_1000 hn hns hn751 hn1000
  have hwR :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      17 := by
    exact_mod_cast hw
  exact hwR.trans (seventeen_le_log_sq_of_751_le hn751)

theorem primeNeOneWitness_cast_le_log_sq_of_eleven_le_of_lt_million {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : 11 ≤ n) (hhi : n < 1000000) :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  by_cases h1024 : 1024 ≤ n
  · exact primeNeOneWitness_cast_le_log_sq_of_1024_le_of_lt_million hn hns h1024 hhi
  by_cases h1001 : 1001 ≤ n
  · exact primeNeOneWitness_cast_le_log_sq_of_1001_le_of_le_1125 hn hns h1001 (by omega)
  by_cases h751 : 751 ≤ n
  · exact primeNeOneWitness_cast_le_log_sq_of_751_le_of_le_1000 hn hns h751 (by omega)
  by_cases h64 : 64 ≤ n
  · exact
      (Nat.cast_le.mpr (primeNeOneWitness_le_thirteen_of_le_750 hn hns (by omega))).trans
        (thirteen_le_log_sq_of_sixtyFour_le h64)
  exact primeNeOneWitness_cast_le_log_sq_of_eleven_le_of_lt_sixtyFour hn hns hlo (by omega)

end PseudoPrime.PseudoSquare
