/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaPairedEulerMass

/-! # Signed finite resolvents and exact paired Euler tails -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a summable real weight and a multiplier of absolute value at most one.
Claim: the signed weighted series is summable. Proof: bound its norm by the weight norm.
Role: justify the exact signed Euler decomposition. -/
theorem summable_signed_weight {ι : Type*} (w c : ι → ℝ) (hw : Summable w) (hc : ∀ i, |c i| ≤ 1) :
    Summable (fun i ↦ -c i * w i) := by
  refine hw.norm.of_norm_bounded (fun i ↦ ?_)
  simp only [norm_mul, Real.norm_eq_abs, abs_neg]
  exact (mul_le_mul_of_nonneg_right (hc i) (abs_nonneg (w i))).trans_eq (one_mul _)

/-- Input: a summable weight and a bounded multiplier.
Claim: the paired series is summable.
Proof: subtract the signed series from the total. Role: retain paired Euler tails. -/
theorem summable_paired_weight {ι : Type*} (w c : ι → ℝ) (hw : Summable w) (hc : ∀ i, |c i| ≤ 1) :
    Summable (fun i ↦ (1 + c i) * w i) := by
  exact (hw.sub (summable_signed_weight w c hw hc)).congr (fun i ↦ by ring)

/-- Input: a nonnegative weight and a multiplier in [-1,1]. Claim: each paired term is nonnegative.
Proof: multiply nonnegative factors. Role: discard only a certified nonnegative tail. -/
theorem paired_weight_nonneg {ι : Type*} (w c : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hc : ∀ i, |c i| ≤ 1)
    (i : ι) : 0 ≤ (1 + c i) * w i := by
  exact mul_nonneg (by linarith only [(abs_le.mp (hc i)).1]) (hw0 i)

/-- Input: a summable weight and a bounded multiplier.
Claim: signed and paired totals add to the total.
Proof: interchange addition with summation and cancel pointwise. Role: preserve Euler savings. -/
theorem signed_weight_add_paired_eq_total {ι : Type*} (w c : ι → ℝ) (hw : Summable w)
    (hc : ∀ i, |c i| ≤ 1) : (∑' i, -c i * w i) + (∑' i, (1 + c i) * w i) = ∑' i, w i := by
  rw [← (summable_signed_weight w c hw hc).tsum_add (summable_paired_weight w c hw hc)]
  exact tsum_congr (fun i ↦ by ring)

/-- Input: a nonnegative summable weight, bounded multiplier and finite prefix.
Claim: subtracting the paired prefix bounds the signed series above.
Proof: use the nonnegative paired tail. Role: retain finite prime-power information. -/
theorem signed_weight_le_total_sub_paired_prefix {ι : Type*} (w c : ι → ℝ) (hw : Summable w)
    (hw0 : ∀ i, 0 ≤ w i) (hc : ∀ i, |c i| ≤ 1) (B : Finset ι) :
    (∑' i, -c i * w i) ≤ (∑' i, w i) - ∑ i ∈ B, (1 + c i) * w i := by
  have he := signed_weight_add_paired_eq_total w c hw hc
  have hp :=
    (summable_paired_weight w c hw hc).sum_le_tsum B (fun i _ ↦ paired_weight_nonneg w c hw0 hc i)
  linarith only [he, hp]

/-- Input: a nonnegative summable weight, bounded multiplier and finite prefix.
Claim: the signed total is bounded by total minus twice the prefix plus its defect.
Proof: expand the paired prefix. Role: expose the witness-dependent defect. -/
theorem signed_weight_prefix_le {ι : Type*} (w c : ι → ℝ) (hw : Summable w) (hw0 : ∀ i, 0 ≤ w i)
    (hc : ∀ i, |c i| ≤ 1) (B : Finset ι) :
    (∑' i, -c i * w i) ≤ (∑' i, w i) - 2 * (∑ i ∈ B, w i) + ∑ i ∈ B, (1 - c i) * w i := by
  have h := signed_weight_le_total_sub_paired_prefix w c hw hw0 hc B
  have he : (∑ i ∈ B, (1 + c i) * w i) = 2 * (∑ i ∈ B, w i) - ∑ i ∈ B, (1 - c i) * w i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ ↦ by ring)
  rw [he] at h
  linarith only [h]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: a finite list of rational nodes and signed coefficients,
and a real ordinate.
Output: the sum of c*a/(a^2+t^2). No positivity or distinctness is imposed here.
Role: accept scale-dependent one-sided spectral majorants. -/
noncomputable def finiteSignedResolvent (l : List (ℚ × ℚ)) (t : ℝ) : ℝ :=
  (l.map (fun ab ↦ (ab.2 : ℝ) * ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + t ^ 2)))).sum

/-- Input: rational node-coefficient pairs and a real base u.
Output: the common Euler weight, the sum of c*u^(-1/2-a).
Role: combine coefficients before imposing positivity. -/
noncomputable def finiteSignedEulerWeight (l : List (ℚ × ℚ)) (u : ℝ) : ℝ :=
  (l.map (fun ab ↦ (ab.2 : ℝ) * u ^ (-(1 / 2 + (ab.1 : ℝ))))).sum

/-- Input: rational node-coefficient pairs and a natural index.
Output: von Mangoldt times the common Euler weight. Role: express the prime-power series. -/
noncomputable def finiteSignedMangoldtWeight (l : List (ℚ × ℚ)) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * finiteSignedEulerWeight l n

/-- Input: rational node-coefficient pairs and real scalars.
Claim: multiplication distributes over nodes.
Proof: distribute over the finite list and reassociate. Role: interchange finite and zero sums. -/
theorem mul_finiteSignedResolvent (l : List (ℚ × ℚ)) (d t : ℝ) :
    d * finiteSignedResolvent l t =
      (l.map (fun ab ↦ (ab.2 : ℝ) * (d * ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + t ^ 2))))).sum := by
  rw [finiteSignedResolvent, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab _
  ring

/-- Input: every node exceeds one half. Claim: the common Mangoldt series is summable.
Proof: reuse absolute convergence at each node. Role: justify signed Euler manipulations. -/
theorem summable_finiteSignedMangoldtWeight (l : List (ℚ × ℚ)) (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) :
    Summable (finiteSignedMangoldtWeight l) := by exact summable_gamma_euler_list l hl

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: a real weight, a real multiplier and a finite prefix.
Output: the paired infinite total minus its prefix; convergence is asserted separately.
Role: keep the exact discarded prime-power contribution visible. -/
noncomputable def pairedWeightTail {ι : Type*} (w c : ι → ℝ) (B : Finset ι) : ℝ :=
  (∑' i, (1 + c i) * w i) - ∑ i ∈ B, (1 + c i) * w i

/-- Input: nonnegative summable weights, bounded multipliers and a finite prefix.
Claim: the paired tail is nonnegative. Proof: compare a finite subsum with its total.
Role: obtain an upper bound from the exact identity. -/
theorem pairedWeightTail_nonneg {ι : Type*} (w c : ι → ℝ) (hw : Summable w) (hw0 : ∀ i, 0 ≤ w i)
    (hc : ∀ i, |c i| ≤ 1) (B : Finset ι) : 0 ≤ pairedWeightTail w c B := by
  exact
    sub_nonneg.mpr
      ((summable_paired_weight w c hw hc).sum_le_tsum B
        (fun i _ ↦ paired_weight_nonneg w c hw0 hc i))

/-- Input: summable real weights, bounded multipliers and a finite prefix.
Claim: exact decomposition into total, doubled prefix, defect and paired tail.
Proof: cancel signed and paired terms and expand the prefix.
Role: avoid premature loss of nonnegative prime-power mass. -/
theorem signed_weight_eq_prefix_sub_paired_tail {ι : Type*} (w c : ι → ℝ) (hw : Summable w)
    (hc : ∀ i, |c i| ≤ 1) (B : Finset ι) :
    (∑' i, -c i * w i) =
      (∑' i, w i) - 2 * (∑ i ∈ B, w i) + (∑ i ∈ B, (1 - c i) * w i) - pairedWeightTail w c B := by
  have he := signed_weight_add_paired_eq_total w c hw hc
  have hp : (∑ i ∈ B, (1 + c i) * w i) = 2 * (∑ i ∈ B, w i) - ∑ i ∈ B, (1 - c i) * w i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ ↦ by ring)
  dsimp only [pairedWeightTail]
  linarith only [he, hp]

/-- Input: the combined Euler weight is nonnegative on bases at least one.
Claim: every natural-index Mangoldt weight is nonnegative.
Proof: the zero term vanishes; all other factors are nonnegative.
Role: allow negative node coefficients without losing paired-tail positivity. -/
theorem finiteSignedMangoldtWeight_nonneg (l : List (ℚ × ℚ))
    (hH : ∀ u : ℝ, 1 ≤ u → 0 ≤ finiteSignedEulerWeight l u) (n : ℕ) :
    0 ≤ finiteSignedMangoldtWeight l n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [finiteSignedMangoldtWeight, ArithmeticFunction.map_zero, zero_mul, le_refl]
  · exact
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (hH n (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn))

end PseudoPrime.Analysis
