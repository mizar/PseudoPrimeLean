/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaFiniteEulerRowBlocks
public import PseudoPrime.Analysis.FiniteSignedRamifiedCosts

/-! # Coefficient-parametric finite Euler intervals and row certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At a positive base, exact endpoint inequalities after any positive natural
power certify an interval for the negative rational exponent. Real-power
multiplication and natural-power monotonicity prove the root transfer. -/
theorem rpow_neg_div_nat_interval {p lo hi : ℝ} (hp : 0 < p) (hl : 0 ≤ lo) (hu : 0 ≤ hi) (m d : ℕ)
    (hd : 0 < d) (hlo : lo ^ d * p ^ m ≤ 1) (hhi : 1 ≤ hi ^ d * p ^ m) :
    lo ≤ p ^ (-(m : ℝ) / d) ∧ p ^ (-(m : ℝ) / d) ≤ hi := by
  have hpw : 0 < p ^ m := pow_pos hp _
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have he : (p ^ (-(m : ℝ) / d)) ^ d = (p ^ m)⁻¹ := by
    rw [← Real.rpow_mul_natCast hp.le, div_mul_cancel₀ _ hd0, Real.rpow_neg hp.le,
      Real.rpow_natCast]
  have hr := Real.rpow_nonneg hp.le (-(m : ℝ) / d)
  constructor
  · apply (pow_le_pow_iff_left₀ hl hr hd.ne').mp
    rw [he, ← one_div]
    exact (le_div_iff₀ hpw).mpr hlo
  · apply (pow_le_pow_iff_left₀ hr hu hd.ne').mp
    rw [he, ← one_div]
    exact (div_le_iff₀ hpw).mpr hhi

/-- The candidate integer exponent for a chosen positive denominator and a
rational Euler node. A successful check requires the exact rational identity;
nonintegral exponents cannot silently pass. -/
def finiteEulerExponent (d : ℕ) (a : ℚ) : ℕ :=
  ((d : ℚ) * (1 / 2 + a)).num.toNat

/-- The signed rational lower endpoint for an arbitrary finite Euler list.
Choose lower power endpoints for nonnegative coefficients and upper ones for
negative coefficients, preserving cancellation. -/
def finiteSignedEulerLower (l : List (ℚ × ℚ)) (r : ℚ → ℚ × ℚ) : ℚ :=
  (l.map (fun ab ↦ ab.2 * (if 0 ≤ ab.2 then (r ab.1).1 else (r ab.1).2))).sum

/-- The signed rational upper endpoint for an arbitrary finite Euler list.
Choose the opposite interval endpoints according to coefficient sign. -/
def finiteSignedEulerUpper (l : List (ℚ × ℚ)) (r : ℚ → ℚ × ℚ) : ℚ :=
  (l.map (fun ab ↦ ab.2 * (if 0 ≤ ab.2 then (r ab.1).2 else (r ab.1).1))).sum

/-- Real intervals for all node powers bound the combined signed Euler weight
on both sides. Reuse the generic signed-node comparison and cast finite sums. -/
theorem finiteSigned_euler_interval_bounds (l : List (ℚ × ℚ)) {u : ℝ} (r : ℚ → ℚ × ℚ)
    (hr :
      ∀ ab ∈ l,
        ((r ab.1).1 : ℝ) ≤ u ^ (-(1 / 2 + (ab.1 : ℝ))) ∧
          u ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ ((r ab.1).2 : ℝ)) :
    (finiteSignedEulerLower l r : ℝ) ≤ finiteSignedEulerWeight l u ∧
      finiteSignedEulerWeight l u ≤ (finiteSignedEulerUpper l r : ℝ) := by
  have hl :=
    List.sum_le_sum
      (fun ab hab ↦ (signed_rational_node_bounds (b := ab.2) (hr ab hab).1 (hr ab hab).2).1)
  have hu :=
    List.sum_le_sum
      (fun ab hab ↦ (signed_rational_node_bounds (b := ab.2) (hr ab hab).1 (hr ab hab).2).2)
  norm_num only [finiteSignedEulerLower, finiteSignedEulerUpper, finiteSignedEulerWeight,
    Rat.cast_list_sum, List.map_map, Function.comp_def]
  exact ⟨hl, hu⟩

/-- The computable check for a positive rational base and node-power intervals
with an arbitrary natural denominator. It checks endpoint signs, exact exponent
identities and both powered inequalities. -/
def finiteSignedEulerRatioCheck (l : List (ℚ × ℚ)) (d : ℕ) (u : ℚ) (r : ℚ → ℚ × ℚ) : Bool :=
  decide
    (0 < u ∧
      l.Forall
        (fun ab ↦
          0 ≤ (r ab.1).1 ∧
            0 ≤ (r ab.1).2 ∧
            (d : ℚ) * (1 / 2 + ab.1) = (finiteEulerExponent d ab.1 : ℚ) ∧
            (r ab.1).1 ^ d * u ^ finiteEulerExponent d ab.1 ≤ 1 ∧
            1 ≤ (r ab.1).2 ^ d * u ^ finiteEulerExponent d ab.1))

/-- At a positive denominator, every successful finite ratio check encloses
the actual real node power. Cast the rational checks and apply the generic
negative-rational-power interval theorem. -/
theorem finiteSigned_ratio_check_sound (l : List (ℚ × ℚ)) {d : ℕ} (hd : 0 < d) {u : ℚ}
    {r : ℚ → ℚ × ℚ} (hc : finiteSignedEulerRatioCheck l d u r = true) (ab : ℚ × ℚ) (hab : ab ∈ l) :
    ((r ab.1).1 : ℝ) ≤ (u : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ∧
      (u : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ ((r ab.1).2 : ℝ) := by
  have h := of_decide_eq_true hc
  obtain ⟨hl, hu, he, hlo, hhi⟩ := List.forall_iff_forall_mem.mp h.2 ab hab
  have hlR := (Rat.cast_le (K := ℝ)).mpr hl
  have huR := (Rat.cast_le (K := ℝ)).mpr hu
  have hloR := (Rat.cast_le (K := ℝ)).mpr hlo
  have hhiR := (Rat.cast_le (K := ℝ)).mpr hhi
  have heR := congrArg (fun q : ℚ ↦ (q : ℝ)) he
  norm_num only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_one, Rat.cast_zero] at hlR huR hloR hhiR heR
  have hexp : -(finiteEulerExponent d ab.1 : ℝ) / d = -(1 / 2 + (ab.1 : ℝ)) := by
    apply (div_eq_iff (Nat.cast_ne_zero.mpr hd.ne')).mpr
    nlinarith only [heR]
  simpa only [hexp] using
    rpow_neg_div_nat_interval ((Rat.cast_pos (K := ℝ)).mpr h.1) hlR huR (finiteEulerExponent d ab.1)
      d hd hloR hhiR

/-- A successful ratio check bounds the entire actual signed Euler weight.
Combine the checked node enclosures with the finite signed-sum theorem. -/
theorem finiteSigned_ratio_check_euler_bounds (l : List (ℚ × ℚ)) {d : ℕ} (hd : 0 < d) {u : ℚ}
    {r : ℚ → ℚ × ℚ} (hc : finiteSignedEulerRatioCheck l d u r = true) :
    (finiteSignedEulerLower l r : ℝ) ≤ finiteSignedEulerWeight l u ∧
      finiteSignedEulerWeight l u ≤ (finiteSignedEulerUpper l r : ℝ) := by
  exact finiteSigned_euler_interval_bounds l r (finiteSigned_ratio_check_sound l hd hc)

/-- The rational Mangoldt lower allowance for an existing prime-power row
and any signed coefficient list. Reuse the row's logarithm and power data;
the coefficient list is supplied separately. -/
def GammaFiniteEulerRow.signedLower (r : GammaFiniteEulerRow) (l : List (ℚ × ℚ)) : ℚ :=
  r.logLower * finiteSignedEulerLower l r.ratios

/-- The coefficient-list and denominator-parametric row check. It validates
power and logarithm intervals and nonnegativity of the signed Euler lower endpoint.
Primality remains a separate input for flexible arithmetic certificates. -/
def GammaFiniteEulerRow.signedCheck (r : GammaFiniteEulerRow) (l : List (ℚ × ℚ)) (d : ℕ) : Bool :=
  finiteSignedEulerRatioCheck l d r.index r.ratios &&
    rationalLogIntervalCheck r.prime r.logScale r.logTerms r.logLower r.logUpper &&
    decide (0 ≤ finiteSignedEulerLower l r.ratios)

/-- A prime row with a successful parametric check gives a lower bound for
the actual signed Mangoldt weight. Evaluate Mangoldt on the positive prime power
and multiply the certified logarithm and nonnegative Euler lower bounds. -/
theorem GammaFiniteEulerRow.signedLower_le (r : GammaFiniteEulerRow) (l : List (ℚ × ℚ)) {d : ℕ}
    (hd : 0 < d) (hp : r.prime.Prime) (hc : r.signedCheck l d = true) :
    (r.signedLower l : ℝ) ≤ finiteSignedMangoldtWeight l r.index := by
  obtain ⟨hb, hlo⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hpow, hlog⟩ := Bool.and_eq_true_iff.mp hb
  have he := (finiteSigned_ratio_check_euler_bounds l hd hpow).1
  have hl := (rationalLogIntervalCheck_sound hlog).1
  norm_num only [Rat.cast_natCast] at he hl
  have hh : (0 : ℝ) ≤ finiteSignedEulerLower l r.ratios :=
    (Rat.cast_nonneg (K := ℝ)).mpr (of_decide_eq_true hlo)
  have hw := mul_le_mul hl he hh (Real.log_natCast_nonneg r.prime)
  simpa only [GammaFiniteEulerRow.signedLower, GammaFiniteEulerRow.index,
    finiteSignedMangoldtWeight, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Rat.cast_mul] using hw

/-- For any nonnegative natural weight and any row type, distinct indices
inside a finite interval give a lower bound from their rational row allowances.
Unselected indices are nonnegative, so exact support coverage is unnecessary. -/
theorem nonnegative_weight_prefix_le_of_rows {ι : Type*} (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (rows : List ι) (idx : ι → ℕ) (lower : ι → ℚ) (hn : (rows.map idx).Nodup) {a b : ℕ}
    (hm : ∀ r ∈ rows, a < idx r ∧ idx r ≤ b) (hl : ∀ r ∈ rows, (lower r : ℝ) ≤ w (idx r)) :
    (((rows.map lower).sum : ℚ) : ℝ) ≤ ∑ n ∈ Finset.Ioc a b, w n := by
  have hs := List.sum_le_sum hl
  have hsub : (rows.map idx).toFinset ⊆ Finset.Ioc a b := by
    intro n hmem
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hmem)
    exact Finset.mem_Ioc.mpr (hm r hr)
  have ht := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ ↦ hw n)
  rw [List.sum_toFinset w hn, List.map_map] at ht
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def]
  exact hs.trans ht

end PseudoPrime.Analysis
