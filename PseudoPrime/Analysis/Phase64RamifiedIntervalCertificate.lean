/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PrimeLocalIntervalBounds
public import PseudoPrime.Analysis.Phase64RamifiedTailBounds
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Compact rational data for the 24-prime ramified excess -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The 24 odd primes below 100, in increasing order. The finite-set equality
below checks this list against the already proved ramified support. -/
def phase64LocalPrimes : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

/-- Candidate lower ratio numerators on the grid 1/100000000 for each local
prime and the ten phase nodes. The interval checks validate all entries exactly. -/
def phase64LocalRatioDigits (p : ℕ) : List ℕ :=
  match p with
  | 3 => [19245008, 15448768, 12401368, 3703703, 2138334, 237592, 26399, 977, 4, 0]
  | 5 => [8944271, 6482626, 4698475, 800000, 357770, 14310, 572, 4, 0, 0]
  | 7 => [5399492, 3658755, 2479212, 291545, 110193, 2248, 45, 0, 0, 0]
  | 11 => [2741012, 1696806, 1050398, 75131, 22652, 187, 1, 0, 0, 0]
  | 13 => [2133462, 1277309, 764729, 45516, 12624, 74, 0, 0, 0, 0]
  | 17 => [1426680, 809537, 459353, 20354, 4936, 17, 0, 0, 0, 0]
  | 19 => [1207451, 670068, 371850, 14579, 3344, 9, 0, 0, 0, 0]
  | 23 => [906584, 484242, 258652, 8218, 1713, 3, 0, 0, 0, 0]
  | 29 => [640328, 326530, 166511, 4100, 761, 0, 0, 0, 0, 0]
  | 31 => [579371, 291531, 146694, 3356, 602, 0, 0, 0, 0, 0]
  | 37 => [444321, 215802, 104813, 1974, 324, 0, 0, 0, 0, 0]
  | 41 => [380911, 181245, 86240, 1450, 226, 0, 0, 0, 0, 0]
  | 43 => [354647, 167148, 78778, 1257, 191, 0, 0, 0, 0, 0]
  | 47 => [310351, 143692, 66529, 963, 140, 0, 0, 0, 0, 0]
  | 53 => [259170, 117146, 52951, 671, 92, 0, 0, 0, 0, 0]
  | 59 => [220659, 97622, 43189, 486, 63, 0, 0, 0, 0, 0]
  | 61 => [209896, 92244, 40539, 440, 56, 0, 0, 0, 0, 0]
  | 67 => [182342, 78645, 33920, 332, 40, 0, 0, 0, 0, 0]
  | 71 => [167152, 71262, 30381, 279, 33, 0, 0, 0, 0, 0]
  | 73 => [160330, 67975, 28819, 257, 30, 0, 0, 0, 0, 0]
  | 79 => [142416, 59433, 24803, 202, 22, 0, 0, 0, 0, 0]
  | 83 => [132246, 54647, 22581, 174, 19, 0, 0, 0, 0, 0]
  | 89 => [119100, 48532, 19776, 141, 15, 0, 0, 0, 0, 0]
  | 97 => [104674, 41926, 16793, 109, 11, 0, 0, 0, 0, 0]
  | _ => []

/-- The rational interval obtained from a stored numerator and the next grid
point, indexed by the actual phase-node list. All uses are guarded by kernel
checks of the real-power endpoint inequalities. -/
def phase64LocalRatioInterval (p : ℕ) (a : ℚ) : ℚ × ℚ :=
  let j := ((phaseResolvent64Coefficients.map Prod.fst).idxOf a)
  let v := (phase64LocalRatioDigits p).getD j 0
  ((v : ℚ) / 100000000, ((v : ℚ) + 1) / 100000000)

/-- The positive-power prefix length whose next power exceeds (99/40)*1660.
The finite certificate verifies the cutoff for every retained local prime. -/
def phase64LocalPowerCount (p : ℕ) : ℕ :=
  if p = 3 then 7
  else if p = 5 then 5 else if p = 7 then 4 else if p ≤ 13 then 3 else if p ≤ 61 then 2 else 1

/-- A rational logarithm upper candidate with denominator one million.
The logarithm interval checker certifies each local-prime value independently. -/
def phase64LocalLogUpper (p : ℕ) : ℚ :=
  (match p with
      | 3 => 1098613
      | 5 => 1609438
      | 7 => 1945911
      | 11 => 2397896
      | 13 => 2564950
      | 17 => 2833214
      | 19 => 2944439
      | 23 => 3135495
      | 29 => 3367296
      | 31 => 3433988
      | 37 => 3610918
      | 41 => 3713573
      | 43 => 3761201
      | 47 => 3850148
      | 53 => 3970292
      | 59 => 4077538
      | 61 => 4110874
      | 67 => 4204693
      | 71 => 4262680
      | 73 => 4290460
      | 79 => 4369448
      | 83 => 4418841
      | 89 => 4488637
      | 97 => 4574711
      | _ => 0 :
      ℕ) /
    1000000

/-- A rounded rational upper candidate for the signed full Euler cost plus
the reciprocal-Taylor ramp prefix divided by 40. Individual kernel checks avoid
combining the large Taylor denominators across different primes. -/
def phase64LocalCostUpper (p : ℕ) : ℚ :=
  (match p with
      | 3 => 574577
      | 5 => 288627
      | 7 => 194489
      | 11 => 121593
      | 13 => 103128
      | 17 => 79208
      | 19 => 73357
      | 23 => 64511
      | 29 => 55139
      | 31 => 52629
      | 37 => 46293
      | 41 => 42842
      | 43 => 41308
      | 47 => 38581
      | 53 => 35248
      | 59 => 32689
      | 61 => 31983
      | 67 => 28563
      | 71 => 28131
      | 73 => 27933
      | 79 => 27404
      | 83 => 27094
      | 89 => 26682
      | 97 => 26209
      | _ => 0 :
      ℕ) /
    1000000

/-- The sign-sensitive rational geometric allowance summed over the ten
phase nodes for a selected prime. Negative coefficients use the lower endpoint. -/
def phase64LocalEulerUpper (p : ℕ) : ℚ :=
  (phaseResolvent64Coefficients.map
      (fun ab ↦
        rationalGeometricUpper ab.2 (phase64LocalRatioInterval p ab.1).1
          (phase64LocalRatioInterval p ab.1).2 1)).sum

/-- Exact certificate predicate: base positivity, ratio endpoint powers,
ramp cutoff, logarithm interval check, and combined rational local upper bound.
It contains only rational and natural arithmetic and Boolean logarithm data. -/
def phase64LocalIntervalValid (p : ℕ) : Prop :=
  1 < p ∧
    phaseResolvent64Coefficients.Forall
        (fun ab ↦
          let lu := phase64LocalRatioInterval p ab.1
          0 ≤ lu.1 ∧
            lu.1 ≤ lu.2 ∧
            lu.2 < 1 ∧
            20 * ab.1 + 10 = (gammaSmallPrimeRatioExponent ab.1 : ℚ) ∧
            lu.1 ^ 20 * (p : ℚ) ^ gammaSmallPrimeRatioExponent ab.1 ≤ 1 ∧
            1 ≤ lu.2 ^ 20 * (p : ℚ) ^ gammaSmallPrimeRatioExponent ab.1) ∧
      (99 / 40 : ℚ) * 1660 ≤ (p : ℚ) ^ (phase64LocalPowerCount p + 1) ∧
      rationalLogIntervalCheck (p : ℚ) (Nat.log2 p + 1) 20 0 (phase64LocalLogUpper p) = true ∧
      phase64LocalEulerUpper p + primeExpPrefixUpper p 1660 (phase64LocalPowerCount p) / 40 ≤
        phase64LocalCostUpper p

/-- The local certificate has computable decidability, obtained from its
finite rational arithmetic fields. This supports kernel-only certificate reduction. -/
instance phase64LocalIntervalDecidable (p : ℕ) : Decidable (phase64LocalIntervalValid p) := by
  dsimp only [phase64LocalIntervalValid]
  infer_instance

/-- The first eight local primes satisfy every certificate field.
Kernel rational arithmetic checks this bounded block without resource overrides. -/
theorem phase64_local_interval_block0 :
    ([3, 5, 7, 11, 13, 17, 19, 23] : List ℕ).Forall phase64LocalIntervalValid := by decide +kernel

/-- The next eight local primes satisfy every certificate field.
Kernel rational arithmetic checks the block independently of the first one. -/
theorem phase64_local_interval_block1 :
    ([29, 31, 37, 41, 43, 47, 53, 59] : List ℕ).Forall phase64LocalIntervalValid := by
  decide +kernel

/-- The last eight local primes satisfy every certificate field.
This completes the bounded local interval checks before summing allowances. -/
theorem phase64_local_interval_block2 :
    ([61, 67, 71, 73, 79, 83, 89, 97] : List ℕ).Forall phase64LocalIntervalValid := by
  decide +kernel

/-- All 24 local primes satisfy the exact interval predicate.
Join the three independently checked eight-prime blocks using finite-list append. -/
theorem phase64_local_interval_checks : phase64LocalPrimes.Forall phase64LocalIntervalValid := by
  have he :
    phase64LocalPrimes =
      ([3, 5, 7, 11, 13, 17, 19, 23] : List ℕ) ++ [29, 31, 37, 41, 43, 47, 53, 59] ++
        [61, 67, 71, 73, 79, 83, 89, 97] := by
    decide +kernel
  rw [he, List.forall_append, List.forall_append]
  exact
    ⟨⟨phase64_local_interval_block0, phase64_local_interval_block1⟩, phase64_local_interval_block2⟩

/-- The certificate list is exactly the fixed ramified prime support.
Kernel finite arithmetic checks the equality with the prime-filtered set. -/
theorem phase64_local_prime_set_eq : phase64LocalPrimes.toFinset = phase64RamifiedPrimeSet := by
  decide +kernel

/-- The log-weighted positive excess of the rounded rational local upper
bounds above 3/100 sums to at most 13/5. Kernel arithmetic checks this small-
denominator sum after the separate local Taylor checks. -/
theorem phase64_local_excess_upper_check :
    (phase64LocalPrimes.map
          (fun p ↦ phase64LocalLogUpper p * max (phase64LocalCostUpper p - 3 / 100) 0)).sum ≤
      (13 / 5 : ℚ) := by
  decide +kernel

end PseudoPrime.Analysis
