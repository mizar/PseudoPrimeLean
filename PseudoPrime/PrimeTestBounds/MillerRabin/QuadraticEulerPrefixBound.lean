/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerAggregate
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerAggregateCap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerPrefix

/-! # Unconditional finite Euler-prefix upper certificate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The prime support has no repetitions, since it is a filtered range.
This permits transfer between list sums and finite-set sums. -/
theorem centerPrimes50000_nodup : centerPrimes50000.Nodup := by
  rw [centerPrimes50000_eq]
  exact (List.nodup_range' 1).filter _

/-- Kernel checking certifies distinctness of the 84 higher-power pairs.
Together with exact support this justifies their finite-set sum. -/
theorem centerHigherPowers_nodup : centerHigherPowers.Nodup := by decide +kernel

/-- The actual finite Euler prefix equals the sum over checked numerical
rows. Use exact support, its distinctness, and the certified permutation.
No numerical approximation or support hypothesis remains in this identity. -/
theorem center50000_prefix_rows :
    (∑ m ∈ Finset.Ioc 0 50000, Analysis.gammaResolventMangoldtWeight m) =
      (centerRows50000.map
          (fun r ↦ Analysis.gammaResolventMangoldtWeight (r.p ^ (r.k + 1)))).sum := by
  rw [center50000_prefix_split, List.sum_toFinset _ centerPrimes50000_nodup,
    List.sum_toFinset _ centerHigherPowers_nodup,
    euler_rows_sum_of_index_perm _ _ centerRows50000_index_perm]
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def, Nat.zero_add,
    pow_one]

/-- Add the real bounds of all independently checked row blocks.
This bound reuses their scalar certificates without repeating root checks. -/
theorem center50000_rows_upper :
    (centerRows50000.map (fun r ↦ Analysis.gammaResolventMangoldtWeight (r.p ^ (r.k + 1)))).sum ≤
      (centerRows50000Upper : ℝ) := by
  simp only [centerRows50000, List.map_append, List.sum_append, centerRows50000Upper, Rat.cast_add,
    add_assoc]
  exact
    add_le_add centerRows0_actual_upper
      (add_le_add centerRows250_actual_upper
        (add_le_add centerRows500_actual_upper
          (add_le_add centerRows750_actual_upper
            (add_le_add centerRows1000_actual_upper
              (add_le_add centerRows1250_actual_upper
                (add_le_add centerRows1500_actual_upper
                  (add_le_add centerRows1750_actual_upper
                    (add_le_add centerRows2000_actual_upper
                      (add_le_add centerRows2250_actual_upper
                        (add_le_add centerRows2500_actual_upper
                          (add_le_add centerRows2750_actual_upper
                            (add_le_add centerRows3000_actual_upper
                              (add_le_add centerRows3250_actual_upper
                                (add_le_add centerRows3500_actual_upper
                                  (add_le_add centerRows3750_actual_upper
                                    (add_le_add centerRows4000_actual_upper
                                      (add_le_add centerRows4250_actual_upper
                                        (add_le_add centerRows4500_actual_upper
                                          (add_le_add centerRows4750_actual_upper
                                            (centerRows5000_actual_upper))))))))))))))))))))

/-- The actual Euler prefix through 50000 is at most 5.805279.
All prime and higher-power terms, logarithm enclosures, root enclosures,
and rational aggregation are kernel certified. This is the finite-prefix
input to the signed Gamma center bound. -/
theorem center50000_prefix_upper :
    (∑ m ∈ Finset.Ioc 0 50000, Analysis.gammaResolventMangoldtWeight m) ≤
      (5805279 / 1000000 : ℝ) := by
  rw [center50000_prefix_rows]
  have h := center50000_rows_upper.trans ((Rat.cast_le (K := ℝ)).mpr centerRows50000_upper_check)
  norm_num only [Rat.cast_div, Rat.cast_natCast] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
