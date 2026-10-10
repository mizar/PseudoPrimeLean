/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Computation.QThresholds
public import PseudoPrime.PseudoSquare.Computation.MillionWitnessBridge
public import PseudoPrime.Analysis.LogarithmicConstants

/-!
# Finite logarithmic bounds for Q witnesses

The results in this module use only the neutral Q witness API and finite small-wheel bounds.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/--
For natural `n ≥ 1024`, `47 ≤ (log n)^2`. Monotonicity compares `log n` with
`log 1024 = 10 log 2`; the explicit lower bound on `log 2` gives `6.9 < log n`,
whose square exceeds `47`. This absorbs the million-wheel witness bound into the radius.
-/
theorem fortySeven_le_log_sq_of_1024_le {n : ℕ} (hn : 1024 ≤ n) :
    (47 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hnR : (1024 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog :=
    Real.strictMonoOn_log.monotoneOn (by norm_num only : (0 : ℝ) < 1024)
      (by exact_mod_cast (show 0 < n from Nat.lt_of_lt_of_le (by decide) hn) : (0 : ℝ) < n) hnR
  have hlog1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num only, Real.log_pow]
    norm_num only
  have hloglower : (6.9 : ℝ) < Real.log (n : ℝ) := by
    linarith only [hlog, hlog1024, Real.log_two_gt_d9]
  nlinarith only [hloglower, sq_nonneg (Real.log (n : ℝ) - (69 / 10 : ℝ))]

/--
For odd nonsquare `1024 ≤ n < 1000000`, the least odd-prime Jacobi `≠ 1` witness,
cast to the reals, is at most `(log n)^2`. The proof casts the million-wheel bound `47`
and composes it with the logarithmic lower bound at `1024`. This is the large finite
branch of the unconditional logarithmic-square estimate.
-/
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

/--
For odd nonsquare `n < 16`, the least odd-prime Jacobi `≠ 1` witness is at most `5`.
The small CRT wheel supplies a witness in `{3, 5}`; finite-set membership selects the
prime and minimality gives the bound. This handles the first logarithmic-square interval.
-/
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

/--
For odd nonsquare `n < 64`, the least odd-prime Jacobi `≠ 1` witness is at most `7`.
The small CRT wheel supplies a witness in `{3, 5, 7}`; finite-set membership selects
the prime and minimality gives the bound. This handles the interval below `64`.
-/
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

/--
If `2^k ≤ n` for naturals `k` and `n`, then `k * log 2 ≤ log n` after real casting.
The proof applies logarithm monotonicity to the positive power of two and rewrites
its logarithm with `Real.log_pow`. This supplies exact power-of-two comparison points
for the finite logarithmic lower bounds.
-/
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

/--
For natural `n ≥ 11`, `5 ≤ (log n)^2`. The proof compares with `10`, rewrites
`log 10 = log 2 + log 5`, and uses the explicit lower bounds to obtain `2.3 < log n`.
Squaring gives the claim used for witness bound `5` in the first finite interval.
-/
theorem five_le_log_sq_of_eleven_le {n : ℕ} (hn : 11 ≤ n) : (5 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast (show 10 ≤ n from Nat.le_trans (by decide) hn)
  have hlog :=
    Real.strictMonoOn_log.monotoneOn (by norm_num only : (0 : ℝ) < 10)
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 10) hnR) hnR
  rw [show (10 : ℝ) = 2 * 5 by norm_num only,
    Real.log_mul (by norm_num only) (by norm_num only)] at hlog
  have hloglower : (2.3 : ℝ) < Real.log (n : ℝ) := by
    linarith only [hlog, Real.log_two_gt_d9, Real.log_five_gt_d9]
  nlinarith only [hloglower, sq_nonneg (Real.log (n : ℝ) - (23 / 10 : ℝ))]

/--
For natural `n ≥ 16`, `7 ≤ (log n)^2`. Comparison with `16 = 2^4` and the checked
lower bound on `log 2` give `2.7 < log n`; squaring absorbs the constant `7`.
This turns the small-wheel witness bound into a logarithmic bound above `16`.
-/
theorem seven_le_log_sq_of_sixteen_le {n : ℕ} (hn : 16 ≤ n) : (7 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hlog := log_two_mul_le_log_of_pow_two_le (k := 4) hn
  norm_num only at hlog
  have hloglower : (2.7 : ℝ) < Real.log (n : ℝ) := by linarith only [hlog, Real.log_two_gt_d9]
  nlinarith only [hloglower, sq_nonneg (Real.log (n : ℝ) - (27 / 10 : ℝ))]

/--
For natural `n ≥ 64`, `13 ≤ (log n)^2`. Comparison with `64 = 2^6` and the explicit
lower bound on `log 2` give `4 < log n`; squaring absorbs the constant `13`.
This handles the small-wheel witness bound on the range from `64` through `750`.
-/
theorem thirteen_le_log_sq_of_sixtyFour_le {n : ℕ} (hn : 64 ≤ n) :
    (13 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hlog := log_two_mul_le_log_of_pow_two_le (k := 6) hn
  norm_num only at hlog
  have hloglower : (4 : ℝ) < Real.log (n : ℝ) := by linarith only [hlog, Real.log_two_gt_d9]
  nlinarith only [hloglower, sq_nonneg (Real.log (n : ℝ) - 4)]

/--
For odd nonsquare `11 ≤ n < 64`, the least odd-prime Jacobi `≠ 1` witness, cast
to the reals, is at most `(log n)^2`. Split at `16`: below it use witness bound `5`,
and above it use bound `7`, with the corresponding logarithmic lower bounds.
This covers the first finite branch without GRH.
-/
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
      (Nat.cast_le.mpr (primeNeOneWitness_le_five_of_lt_sixteen hn hns (lt_of_not_ge h16))).trans
        (five_le_log_sq_of_eleven_le hlo)

/--
The finite certificate for odd inputs `1001 ≤ n.val ≤ 1030` in `Fin 1031`:
if every square with root in `Fin 33` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
The finite certificate for odd inputs `1031 ≤ n.val ≤ 1060` in `Fin 1061`:
if every square with root in `Fin 34` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
The finite certificate for odd inputs `1061 ≤ n.val ≤ 1090` in `Fin 1091`:
if every square with root in `Fin 35` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
The finite certificate for odd inputs `1091 ≤ n.val ≤ 1125` in `Fin 1126`:
if every square with root in `Fin 36` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
Verify `Through1030NeOneCertificate` for odd inputs from `1001` through `1030`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1030NeOneCertificate_valid : Through1030NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
Verify `Through1060NeOneCertificate` for odd inputs from `1031` through `1060`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1060NeOneCertificate_valid : Through1060NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
Verify `Through1090NeOneCertificate` for odd inputs from `1061` through `1090`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1090NeOneCertificate_valid : Through1090NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
Verify `Through1125TailNeOneCertificate` for odd inputs from `1091` through `1125`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1125TailNeOneCertificate_valid : Through1125TailNeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
The finite certificate for odd inputs `1001 ≤ n.val ≤ 1125` in `Fin 1126`:
if every square with root in `Fin 36` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
Verify `Through1125NeOneCertificate` for odd inputs from `1001` through `1125`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1125NeOneCertificate_valid : Through1125NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
For odd nonsquare `1001 ≤ n ≤ 1125`, the least odd-prime Jacobi `≠ 1` witness
is at most `19`. The proof supplies the finite square exclusions to the interval
certificate and applies minimality to each concrete prime alternative.
This is the pointwise finite bound used by the corresponding logarithmic-square adapter.
-/
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

/--
For natural `n ≥ 1001`, `19 ≤ (log n)^2`. The proof uses the weaker comparison
`128 ≤ n`, rewrites `log 128 = 7 log 2`, and obtains `4.83 < log n` from the explicit
logarithm constant. Squaring absorbs the finite witness bound `19`.
-/
theorem nineteen_le_log_sq_of_1001_le {n : ℕ} (hn1001 : 1001 ≤ n) :
    (19 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hn128nat : 128 ≤ n := Nat.le_trans (by decide : 128 ≤ 1001) hn1001
  have hn128 : (128 : ℝ) ≤ n := by exact_mod_cast hn128nat
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide : 0 < 128) hn128nat
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlog := Real.strictMonoOn_log.monotoneOn (show (0 : ℝ) < 128 by norm_num only) hnposR hn128
  have hlog128 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num only, Real.log_pow]
    norm_num only
  have h2 := Real.log_two_gt_d9
  have hloglower : (4.83 : ℝ) < Real.log (n : ℝ) := by linarith only [hlog, hlog128, h2]
  nlinarith only [hloglower, sq_nonneg (Real.log (n : ℝ) - (483 / 100 : ℝ))]

/--
For odd nonsquare `1001 ≤ n ≤ 1125`, the least odd-prime Jacobi `≠ 1` witness,
cast to the reals, is at most `(log n)^2`. The proof casts the finite bound `19` and
composes it with the logarithmic lower bound absorbing that constant.
This connects the interval certificate to the unconditional logarithmic witness interface.
-/
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

/--
The finite certificate for odd inputs `1126 ≤ n.val ≤ 1155` in `Fin 1156`:
if every square with root in `Fin 35` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
The finite certificate for odd inputs `1156 ≤ n.val ≤ 1185` in `Fin 1186`:
if every square with root in `Fin 35` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
The finite certificate for odd inputs `1186 ≤ n.val ≤ 1215` in `Fin 1216`:
if every square with root in `Fin 35` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
The finite certificate for odd inputs `1216 ≤ n.val ≤ 1250` in `Fin 1251`:
if every square with root in `Fin 36` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
Verify `Through1155NeOneCertificate` for odd inputs from `1126` through `1155`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1155NeOneCertificate_valid : Through1155NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
Verify `Through1185NeOneCertificate` for odd inputs from `1156` through `1185`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1185NeOneCertificate_valid : Through1185NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
Verify `Through1215NeOneCertificate` for odd inputs from `1186` through `1215`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1215NeOneCertificate_valid : Through1215NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
Verify `Through1250TailNeOneCertificate` for odd inputs from `1216` through `1250`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1250TailNeOneCertificate_valid : Through1250TailNeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
The finite certificate for odd inputs `1126 ≤ n.val ≤ 1250` in `Fin 1251`:
if every square with root in `Fin 36` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
Verify `Through1250NeOneCertificate` for odd inputs from `1126` through `1250`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1250NeOneCertificate_valid : Through1250NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
For odd nonsquare `1126 ≤ n ≤ 1250`, the least odd-prime Jacobi `≠ 1` witness
is at most `19`. The proof supplies the finite square exclusions to the interval
certificate and applies minimality to each concrete prime alternative.
This is the pointwise finite bound used by the corresponding logarithmic-square adapter.
-/
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

/--
For odd nonsquare `1126 ≤ n ≤ 1250`, the least odd-prime Jacobi `≠ 1` witness,
cast to the reals, is at most `(log n)^2`. The proof casts the finite bound `19` and
composes it with the logarithmic lower bound absorbing that constant.
This connects the interval certificate to the unconditional logarithmic witness interface.
-/
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
  exact hwR.trans (nineteen_le_log_sq_of_1001_le (Nat.le_trans (by decide : 1001 ≤ 1126) hn1126))

/--
The finite certificate for odd inputs `1251 ≤ n.val ≤ 1280` in `Fin 1281`:
if every square with root in `Fin 36` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
The finite certificate for odd inputs `1281 ≤ n.val ≤ 1310` in `Fin 1311`:
if every square with root in `Fin 37` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
The finite certificate for odd inputs `1311 ≤ n.val ≤ 1340` in `Fin 1341`:
if every square with root in `Fin 37` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
The finite certificate for odd inputs `1341 ≤ n.val ≤ 1375` in `Fin 1376`:
if every square with root in `Fin 38` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
Verify `Through1280NeOneCertificate` for odd inputs from `1251` through `1280`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1280NeOneCertificate_valid : Through1280NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
Verify `Through1310NeOneCertificate` for odd inputs from `1281` through `1310`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1310NeOneCertificate_valid : Through1310NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
Verify `Through1340NeOneCertificate` for odd inputs from `1311` through `1340`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1340NeOneCertificate_valid : Through1340NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
Verify `Through1375TailNeOneCertificate` for odd inputs from `1341` through `1375`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1375TailNeOneCertificate_valid : Through1375TailNeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
The finite certificate for odd inputs `1251 ≤ n.val ≤ 1375` in `Fin 1376`:
if every square with root in `Fin 38` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
Verify `Through1375NeOneCertificate` for odd inputs from `1251` through `1375`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1375NeOneCertificate_valid : Through1375NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
For odd nonsquare `1251 ≤ n ≤ 1375`, the least odd-prime Jacobi `≠ 1` witness
is at most `19`. The proof supplies the finite square exclusions to the interval
certificate and applies minimality to each concrete prime alternative.
This is the pointwise finite bound used by the corresponding logarithmic-square adapter.
-/
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

/--
For odd nonsquare `1251 ≤ n ≤ 1375`, the least odd-prime Jacobi `≠ 1` witness,
cast to the reals, is at most `(log n)^2`. The proof casts the finite bound `19` and
composes it with the logarithmic lower bound absorbing that constant.
This connects the interval certificate to the unconditional logarithmic witness interface.
-/
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
  exact hwR.trans (nineteen_le_log_sq_of_1001_le (Nat.le_trans (by decide : 1001 ≤ 1251) hn1251))

/--
The finite certificate for odd inputs `1376 ≤ n.val ≤ 1405` in `Fin 1406`:
if every square with root in `Fin 39` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
The finite certificate for odd inputs `1406 ≤ n.val ≤ 1435` in `Fin 1436`:
if every square with root in `Fin 39` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
The finite certificate for odd inputs `1436 ≤ n.val ≤ 1465` in `Fin 1466`:
if every square with root in `Fin 40` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
The finite certificate for odd inputs `1466 ≤ n.val ≤ 1500` in `Fin 1501`:
if every square with root in `Fin 40` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
Verify `Through1405NeOneCertificate` for odd inputs from `1376` through `1405`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1405NeOneCertificate_valid : Through1405NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
Verify `Through1435NeOneCertificate` for odd inputs from `1406` through `1435`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1435NeOneCertificate_valid : Through1435NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
Verify `Through1465NeOneCertificate` for odd inputs from `1436` through `1465`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1465NeOneCertificate_valid : Through1465NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := Nat.lt_of_lt_of_le n.isLt (by decide)
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
Verify `Through1500TailNeOneCertificate` for odd inputs from `1466` through `1500`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction. Oddness excludes the even
endpoint before the wheel is applied.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1500TailNeOneCertificate_valid : Through1500TailNeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := by
    apply Nat.lt_of_le_of_ne (Nat.le_of_lt_succ n.isLt)
    intro heq
    rw [heq] at hnodd
    norm_num only at hnodd
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
The finite certificate for odd inputs `1376 ≤ n.val ≤ 1500` in `Fin 1501`:
if every square with root in `Fin 40` is excluded, one of the listed odd primes
through `19` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
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

/--
Verify `Through1500NeOneCertificate` for odd inputs from `1376` through `1500`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction. Oddness excludes the even
endpoint before the wheel is applied.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1500NeOneCertificate_valid : Through1500NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1500 : n.val < 1500 := by
    apply Nat.lt_of_le_of_ne (Nat.le_of_lt_succ n.isLt)
    intro heq
    rw [heq] at hnodd
    norm_num only at hnodd
  have hw := qNeOneSmall1500_exists (Nat.odd_iff.mpr hnodd) hsq hn1500
  exact exists_qNeOneSmall1500_to_or hw

/--
For odd nonsquare `1376 ≤ n ≤ 1500`, the least odd-prime Jacobi `≠ 1` witness
is at most `19`. The proof supplies the finite square exclusions to the interval
certificate and applies minimality to each concrete prime alternative.
This is the pointwise finite bound used by the corresponding logarithmic-square adapter.
-/
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

/--
For odd nonsquare `1376 ≤ n ≤ 1500`, the least odd-prime Jacobi `≠ 1` witness,
cast to the reals, is at most `(log n)^2`. The proof casts the finite bound `19` and
composes it with the logarithmic lower bound absorbing that constant.
This connects the interval certificate to the unconditional logarithmic witness interface.
-/
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
  exact hwR.trans (nineteen_le_log_sq_of_1001_le (Nat.le_trans (by decide : 1001 ≤ 1376) hn1376))

/-! The finite certificate and logarithmic bound for `751 ≤ n ≤ 1000`. -/

/--
The finite certificate for odd inputs `751 ≤ n.val ≤ 1000` in `Fin 1001`:
if every square with root in `Fin 32` is excluded, one of the listed odd primes
through `17` has Jacobi value different from `1`. The root bound covers every
square in this interval. The verified proposition supplies the corresponding witness bound.
-/
def Through1000NeOneCertificate : Prop :=
  ∀ n : Fin 1001,
    751 ≤ n.val →
      n.val % 2 = 1 →
      (∀ k : Fin 32, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨
        jacobiSym n.val 11 ≠ 1 ∨ jacobiSym n.val 13 ≠ 1 ∨ jacobiSym n.val 17 ≠ 1

/--
Verify `Through1000NeOneCertificate` for odd inputs from `751` through `1000`.
The proof turns the finite square exclusions into nonsquareness, applies the small CRT
wheel, and expands its prime-set witness into the required disjunction. Oddness excludes the even
endpoint before the wheel is applied.
This supplies the finite bound for the corresponding least-witness adapter.
-/
theorem through1000NeOneCertificate_valid : Through1000NeOneCertificate := by
  intro n _hlo hnodd hns
  have hsq := not_isSquare_of_fin_certificate (Nat.lt_of_lt_of_le n.isLt (by decide)) hns
  have hn1000 : n.val < 1000 := by
    apply Nat.lt_of_le_of_ne (Nat.le_of_lt_succ n.isLt)
    intro heq
    rw [heq] at hnodd
    norm_num only at hnodd
  have hw := qNeOneSmall1000_exists (Nat.odd_iff.mpr hnodd) hsq hn1000
  exact exists_qNeOneSmall1000_to_or hw

/--
For odd nonsquare `751 ≤ n ≤ 1000`, the least odd-prime Jacobi `≠ 1` witness
is at most `17`. The proof supplies the finite square exclusions to the interval
certificate and applies minimality to each concrete prime alternative.
This is the pointwise finite bound used by the corresponding logarithmic-square adapter.
-/
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

/--
For natural `n ≥ 751`, `17 ≤ (log n)^2`. The proof compares with `64 = 2^6`, uses
`0.69 < log 2` to obtain `4.14 < log n`, and squares this positive lower bound.
This absorbs the finite witness bound `17` on the interval through `1000`.
-/
theorem seventeen_le_log_sq_of_751_le {n : ℕ} (hn751 : 751 ≤ n) :
    (17 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hn64nat : 64 ≤ n := Nat.le_trans (by decide : 64 ≤ 751) hn751
  have hn64 : (64 : ℝ) ≤ n := by exact_mod_cast hn64nat
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide : 0 < 64) hn64nat
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlog := Real.strictMonoOn_log.monotoneOn (show (0 : ℝ) < 64 by norm_num only) hnposR hn64
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

/--
For odd nonsquare `751 ≤ n ≤ 1000`, the least odd-prime Jacobi `≠ 1` witness,
cast to the reals, is at most `(log n)^2`. The proof casts the finite bound `17` and
composes it with the logarithmic lower bound absorbing that constant.
This connects the interval certificate to the unconditional logarithmic witness interface.
-/
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

/--
For odd nonsquare `11 ≤ n < 1000000`, the least odd-prime Jacobi `≠ 1` witness,
cast to the reals, is at most `(log n)^2`, without GRH. The proof splits at `64`,
`751`, `1001`, and `1024`, combining the small-wheel bounds `5, 7, 13, 17, 19` and
the million-wheel bound `47` with logarithmic lower bounds. This is the finite branch
used in the integrated GRH theorem after reduction to the squarefree part.
-/
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
  · exact
      primeNeOneWitness_cast_le_log_sq_of_1001_le_of_le_1125 hn hns h1001
        (Nat.le_trans (Nat.le_of_lt_succ (lt_of_not_ge h1024)) (by decide))
  by_cases h751 : 751 ≤ n
  · exact
      primeNeOneWitness_cast_le_log_sq_of_751_le_of_le_1000 hn hns h751
        (Nat.le_of_lt_succ (lt_of_not_ge h1001))
  by_cases h64 : 64 ≤ n
  · exact
      (Nat.cast_le.mpr
            (primeNeOneWitness_le_thirteen_of_le_750 hn hns
              (Nat.le_of_lt_succ (lt_of_not_ge h751)))).trans
        (thirteen_le_log_sq_of_sixtyFour_le h64)
  exact primeNeOneWitness_cast_le_log_sq_of_eleven_le_of_lt_sixtyFour hn hns hlo (lt_of_not_ge h64)

end PseudoPrime.PseudoSquare
