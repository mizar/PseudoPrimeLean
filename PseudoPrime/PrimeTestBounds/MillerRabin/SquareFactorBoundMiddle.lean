/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareFactorBoundCoverage

/-! # Square-divisor 0.30 coverage in the middle range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, a prime-square divisor gives a 0.30 rejecting prime throughout
`[42.5, 80.5]`. Three existing certified coverage rows provide the witnesses. -/
theorem exists_prime_reject_03_square_mid {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (85 / 2 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 161 / 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h1 : Real.log n ≤ 99 / 2
  · let d : SquareCoverageData :=
      ⟨541, 3147633000719 / 250000000000, 3098894526487 / 62500000000, 10,
        [95, 69, 96, 90, 71, 91, 98, 92, 99, 93, 100, 94]⟩
    have hd : d ∈ squareCoverages :=
      List.mem_of_getElem? (show squareCoverages[21]? = some d by rfl)
    apply
      squareCoverage_divisor_03 hn ho hp hdiv hRH d hd (lo := (85 / 2 : ℝ)) (hi := (99 / 2 : ℝ))
        (by norm_num only) hL h1
    all_goals norm_num only [d, Rat.cast_div, Rat.cast_ofNat]
  · by_cases h2 : Real.log n ≤ 62
    · let d : SquareCoverageData :=
        ⟨701, 819241675503 / 62500000000, 31073199677503 / 500000000000, 10,
          [116, 89, 70, 111, 103, 92, 117, 105, 118, 106, 119, 101, 107, 120]⟩
      have hd : d ∈ squareCoverages :=
        List.mem_of_getElem? (show squareCoverages[23]? = some d by rfl)
      apply
        squareCoverage_divisor_03 hn ho hp hdiv hRH d hd (lo := (99 / 2 : ℝ)) (hi := (62 : ℝ))
          (by norm_num only) (le_of_not_ge h1) h2
      all_goals norm_num only [d, Rat.cast_div, Rat.cast_ofNat]
    · let d : SquareCoverageData :=
        ⟨1103, 1751673806709 / 125000000000, 5033898982571 / 62500000000, 11,
          [161, 110, 97, 163, 164, 165, 166, 167, 158, 168, 159, 169, 145, 160, 170]⟩
      have hd : d ∈ squareCoverages :=
        List.mem_of_getElem? (show squareCoverages[29]? = some d by rfl)
      apply
        squareCoverage_divisor_03 hn ho hp hdiv hRH d hd (lo := (62 : ℝ)) (hi := (161 / 2 : ℝ))
          (by norm_num only) (le_of_not_ge h2) hU
      all_goals norm_num only [d, Rat.cast_div, Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
