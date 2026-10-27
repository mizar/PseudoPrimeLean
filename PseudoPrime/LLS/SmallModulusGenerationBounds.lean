/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.UnitGenerationBalanced
public import PseudoPrime.LLS.ParityRationalWitnessProfiles

/-! # Transferring finite generation certificates to the parity profile

Proper subgroups omit an eligible prime from every valid generation tree.
The analytic profile exceeds seven for q ≥ 3 and eighty-one for q ≥ 8,
so uniform integer caps suffice for the finite small-modulus extension.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- A valid generation tree at a nonzero modulus gives an outside prime through cap.
Assume all eligible prime residues belong to H and use generation to contradict H proper.
No GRH or analytic premise is needed for this finite algebraic result. -/
theorem exists_prime_outside_of_generation_tree {q cap : ℕ} [NeZero q]
    {tree : ℕ → NumberTheory.UnitGenerationNode}
    (hvalid : NumberTheory.UnitGenerationTreeValid q cap tree) (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) : ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ p ≤ cap := by
  classical
  by_contra hn
  apply hH
  apply NumberTheory.subgroup_eq_top_of_valid_generation_tree hvalid H
  intro p hp hd hb u hu
  by_contra hout
  exact hn ⟨p, ⟨hp, hd, u, hout, hu⟩, hb⟩

/-- At a nonzero modulus with a valid tree and proper H, the least outside prime is at most cap.
Minimize the unbounded outside-prime predicate and compare it with the bounded witness.
Minimality ranges over every coprime outside prime. -/
theorem exists_least_prime_outside_of_generation_tree {q cap : ℕ} [NeZero q]
    {tree : ℕ → NumberTheory.UnitGenerationNode}
    (hvalid : NumberTheory.UnitGenerationTreeValid q cap tree) (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ p ≤ cap ∧ ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  classical
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_of_generation_tree hvalid H hH
  have hex : ∃ r, PrimeOutsideSubgroup q H r := ⟨p, hp⟩
  exact
    ⟨Nat.find hex, Nat.find_spec hex, (Nat.find_min' hex hp).trans hb, fun _ hr =>
      Nat.find_min' hex hr⟩

end PseudoPrime.LLS

namespace PseudoPrime.Analysis

/-- For q ≥ 3, the parity profile square is at least seven.
Use log 3 > 1 and nonnegative log-log to bound its positive root.
This accommodates the smallest finite generation certificates. -/
theorem parity_square_ge_seven {q : ℕ} (hq : 3 ≤ q) :
    (7 : ℝ) ≤ (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25) ^ 2 := by
  have h3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num only : (0 : ℝ) < 3)).mpr Real.exp_one_lt_three
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) (Nat.cast_le.mpr hq)
  have hL : 1 ≤ Real.log q := le_of_lt (h3.trans_le hlog)
  have hz := Real.log_nonneg hL
  have hroot : 3 ≤ Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25 := by
    linarith only [hL, hz]
  nlinarith only [sq_nonneg (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25 - 3),
    hroot]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- For q ≥ 8, the parity profile square is at least eighty-one.
Use log 8 > 2 and log 2's rational lower bound to obtain root at least nine.
This permits a common integer prime cap for all remaining small moduli. -/
theorem parity_square_ge_eighty_one {q : ℕ} (hq : 8 ≤ q) :
    (81 : ℝ) ≤ (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25) ^ 2 := by
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 8) (Nat.cast_le.mpr hq)
  have h8 : (2 : ℝ) < Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hL : 2 ≤ Real.log q := le_of_lt (h8.trans_le hlog)
  have hz := Real.log_le_log (by norm_num only : (0 : ℝ) < 2) hL
  have hroot : 9 ≤ Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25 := by
    linarith only [hL, hz, Real.log_two_gt_d9]
  nlinarith only [sq_nonneg (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25 - 9),
    hroot]

end PseudoPrime.Analysis

namespace PseudoPrime.LLS

/-- Use cap seven below modulus eight and cap eighty-one otherwise.
The cap is independent of factorization and the certificate search algorithm.
It is bounded by the parity profile for every modulus at least three. -/
def smallModulusPrimeCap (q : ℕ) : ℕ :=
  if q < 8 then 7 else 81

/-- For q ≥ 3, the selected integer cap lies below the parity profile.
Split at modulus eight and apply the corresponding positive-root square comparison.
This transfers finite integer witness bounds to the public analytic formula. -/
theorem smallModulusPrimeCap_le_parity_square {q : ℕ} (hq : 3 ≤ q) :
    (smallModulusPrimeCap q : ℝ) ≤
      (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25) ^ 2 := by
  by_cases h8 : q < 8
  · simpa only [smallModulusPrimeCap, ite_eq_left h8, Nat.cast_ofNat] using
      Analysis.parity_square_ge_seven hq
  · simpa only [smallModulusPrimeCap, ite_eq_right h8, Nat.cast_ofNat] using
      Analysis.parity_square_ge_eighty_one (Nat.le_of_not_gt h8)

/-- For q ≥ 3 with a valid tree at the selected cap, every proper subgroup has an outside prime
through the parity profile. Transfer the integer witness using the cap comparison.
This is the small-modulus consumer for the finite certificate catalog. -/
theorem exists_prime_outside_le_parity_of_generation_tree {q : ℕ} [NeZero q]
    {tree : ℕ → NumberTheory.UnitGenerationNode} (hq : 3 ≤ q)
    (hvalid : NumberTheory.UnitGenerationTreeValid q (smallModulusPrimeCap q) tree)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25) ^ 2 := by
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_of_generation_tree hvalid H hH
  exact ⟨p, hp, (Nat.cast_le.mpr hb).trans (smallModulusPrimeCap_le_parity_square hq)⟩

end PseudoPrime.LLS
