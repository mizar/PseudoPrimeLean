/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaScaledRampTree

/-! # Integer prefix evaluation of actual rational ramp lower bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a positive rational scale and nonnegative rational height cutoff.
Claim: the height comparison equals a natural prefix-bound comparison.
Proof: clear the positive denominator and use the floor order equivalence.
This removes rational comparisons from each row of the integer evaluator. -/
theorem gamma_ramp_height_le_iff_index_floor {x c : ℚ} (hx : 0 < x) (hc : 0 ≤ c) (m : ℕ) :
    (m : ℚ) / x ≤ c ↔ m ≤ ⌊c * x⌋₊ := by
  exact (div_le_iff₀ hx).trans (Nat.le_floor_iff (mul_nonneg hc hx.le)).symm

/-- Input: a checked tree, nonzero integer scale, positive target and height cutoff.
Claim: the integer prefix divided by D equals the exact rational prefix moment.
Proof: use the integer cast identity, the floor cutoff equivalence and cancel D.
This is the reusable bridge from cheap integer sums to the moving ramp mask. -/
theorem GammaScaledRampTree.prefixMoment_div {a : ℚ} {D lo hi : ℕ}
    (t : GammaScaledRampTree a D lo hi) (hD : D ≠ 0) {x c : ℚ} (hx : 0 < x) (hc : 0 ≤ c) (k : ℕ) :
    (t.prefixMoment ⌊c * x⌋₊ k : ℚ) / (D : ℚ) =
      gammaRationalListMoment
        ((t.block.rows.map Prod.fst).filter (fun r ↦ decide ((r.index : ℚ) / x ≤ c)))
        (fun r ↦ r.logLower * r.rampLower ^ 2) (fun r ↦ (r.index : ℚ)) k := by
  rw [t.prefixMoment_cast]
  simp only [gamma_ramp_height_le_iff_index_floor hx hc]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hD)

/-- The exact masked moment evaluated from balanced integer prefixes.
At both moving joins divide the prefix integer by D, then use the linear-ramp
identity. All row summation is integer arithmetic at natural cutoffs. -/
def GammaScaledRampTree.rampMoment {a : ℚ} {D lo hi : ℕ} (t : GammaScaledRampTree a D lo hi) (x : ℚ)
    (k : ℕ) : ℚ :=
  let P := fun (c : ℚ) (j : ℕ) ↦ (t.prefixMoment ⌊c * x⌋₊ j : ℚ) / (D : ℚ)
  P (247 / 100) k +
    ((99 / 40) * (P (99 / 40) k - P (247 / 100) k) -
        (P (99 / 40) (k + 1) - P (247 / 100) (k + 1)) / x) /
      (1 / 200)

/-- Input: a checked tree with nonzero scale and a positive rational target.
Claim: integer masked-moment evaluation equals the existing exact rational moment.
Proof: identify the four integer prefixes with their rational counterparts.
This preserves the cancellation between exact prefix values. -/
theorem GammaScaledRampTree.rampMoment_eq {a x : ℚ} {D lo hi : ℕ}
    (t : GammaScaledRampTree a D lo hi) (hD : D ≠ 0) (hx : 0 < x) (k : ℕ) :
    t.rampMoment x k = gammaReservedRampMoment (t.block.rows.map Prod.fst) x k := by
  rw [gamma_reserved_ramp_moment_eq_prefix]
  dsimp only [GammaScaledRampTree.rampMoment]
  simp only [t.prefixMoment_div (c := 247 / 100) hD hx (by norm_num only),
    t.prefixMoment_div (c := 99 / 40) hD hx (by norm_num only)]

/-- The exact rational transported lower polynomial using integer prefix evaluation.
The tree supplies its anchor. Target scale and Taylor term count remain parameters.
The latter is a term count, so a degree-four evaluation uses n = 5. -/
def GammaScaledRampTree.rampLower {a : ℚ} {D lo hi : ℕ} (t : GammaScaledRampTree a D lo hi) (x : ℚ)
    (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (1 / a - 1 / x) ^ k / (k.factorial : ℚ) * t.rampMoment x k

/-- Input: a checked tree, nonzero integer scale and positive target.
Claim: integer-prefix evaluation equals the original rational lower polynomial.
Proof: substitute the masked-moment identity in the finite Taylor sum.
This allows the earlier finite-cover interfaces to reuse the efficient evaluator. -/
theorem GammaScaledRampTree.rampLower_eq {a x : ℚ} {D lo hi : ℕ} (t : GammaScaledRampTree a D lo hi)
    (hD : D ≠ 0) (hx : 0 < x) (n : ℕ) :
    t.rampLower x n = gammaReservedRampLowerFromMoments (t.block.rows.map Prod.fst) a x n := by
  simp only [GammaScaledRampTree.rampLower, gammaReservedRampLowerFromMoments,
    t.rampMoment_eq hD hx]

/-- Input: a checked tree starting at zero, positive anchor, nonzero scale,
and any later rational target. Claim: its efficient lower evaluation bounds the
actual ramp sum. Proof: rewrite to the certified rational lower polynomial.
All prime, endpoint, distinctness and integer-weight inputs come from the tree. -/
theorem GammaScaledRampTree.rampLower_le_actual {a x : ℚ} {D hi : ℕ}
    (t : GammaScaledRampTree a D 0 hi) (hD : D ≠ 0) (ha : 0 < a) (hax : a ≤ x) (n : ℕ) :
    (t.rampLower x n : ℝ) ≤ AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x := by
  rw [t.rampLower_eq hD (ha.trans_le hax) n]
  exact (t.block.toCertificate ha).lower_le_actual hax n

end PseudoPrime.Analysis
