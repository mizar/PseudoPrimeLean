/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.PSeries

/-!
# Convergent reciprocal differences in the digamma recurrence

Inverse-square bounds give the series limit of the finite recurrence.
The vanishing of translated digamma differences is a separate analytic step.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- For two points with nonnegative real parts and a positive natural index, the difference
of shifted reciprocals has norm at most the point separation divided by the index squared.
This gives the common majorant for digamma resolvent differences. -/
theorem norm_resolventDifference_le {s t : ℂ} (hs : 0 ≤ s.re) (ht : 0 ≤ t.re) {n : ℕ} (hn : 0 < n) :
    ‖1 / (s + n) - 1 / (t + n)‖ ≤ ‖t - s‖ / (n : ℝ) ^ 2 := by
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsn : (n : ℝ) ≤ ‖s + n‖ := by
    have h := Complex.re_le_norm (s + n)
    rw [Complex.add_re, Complex.natCast_re] at h
    linarith only [hs, h]
  have htn : (n : ℝ) ≤ ‖t + n‖ := by
    have h := Complex.re_le_norm (t + n)
    rw [Complex.add_re, Complex.natCast_re] at h
    linarith only [ht, h]
  have hsz : s + n ≠ 0 := norm_pos_iff.mp (hnreal.trans_le hsn)
  have htz : t + n ≠ 0 := norm_pos_iff.mp (hnreal.trans_le htn)
  have he : 1 / (s + n) - 1 / (t + n) = (t - s) / ((s + n) * (t + n)) := by
    field_simp [hsz, htz]
    ring
  rw [he, norm_div, norm_mul]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hnreal)
  simpa only [pow_two] using mul_le_mul hsn htn hnreal.le (norm_nonneg _)

/-- For points with nonnegative real parts, the shifted reciprocal difference series converges.
The inverse-square majorant controls every positive index; the zero index is a finite exception. -/
theorem summable_resolventDifference {s t : ℂ} (hs : 0 ≤ s.re) (ht : 0 ≤ t.re) :
    Summable (fun n : ℕ ↦ 1 / (s + n) - 1 / (t + n)) := by
  have hb : Summable (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by
    simpa only [Real.rpow_two] using
      (Real.summable_nat_rpow_inv.mpr (by norm_num only : (1 : ℝ) < 2))
  apply Summable.of_norm_bounded_eventually_nat (hb.mul_left ‖t - s‖)
  filter_upwards [Nat.eventually_pos] with n hn
  simpa only [div_eq_mul_inv] using norm_resolventDifference_le hs ht hn

/-- A complex point with positive real part avoids all nonpositive integer gamma poles.
Compare real parts with the nonpositive real part of the proposed pole. -/
theorem not_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) (n : ℕ) : s ≠ -(n : ℂ) := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  linarith only [hs, hr, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- For two points with positive real parts, the digamma difference after a natural translation
is the original difference plus the corresponding finite reciprocal difference sum.
Subtract the two iterated digamma recurrence identities. -/
theorem digamma_sub_add_nat_eq_partial_resolvent {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) (n : ℕ) :
    Complex.digamma (s + n) - Complex.digamma (t + n) =
      Complex.digamma s - Complex.digamma t +
        ∑ k ∈ Finset.range n, (1 / (s + k) - 1 / (t + k)) := by
  rw [Complex.digamma_apply_add_nat (not_neg_nat_of_re_pos hs) n,
    Complex.digamma_apply_add_nat (not_neg_nat_of_re_pos ht) n, Finset.sum_sub_distrib]
  simp only [one_div]
  ring

/-- For two points with positive real parts, translated digamma differences converge
to the original difference plus the reciprocal difference series. The finite recurrence
and absolute convergence give this limit. The Euler logarithmic gamma representation
identifies this expression with zero in the corresponding zero-limit theorem. -/
theorem tendsto_digamma_sub_add_nat {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    Filter.Tendsto (fun n : ℕ ↦ Complex.digamma (s + n) - Complex.digamma (t + n)) Filter.atTop
      (nhds (Complex.digamma s - Complex.digamma t + ∑' k : ℕ, (1 / (s + k) - 1 / (t + k)))) := by
  have h := (summable_resolventDifference hs.le ht.le).hasSum.tendsto_sum_nat
  exact
    ((tendsto_const_nhds (x := Complex.digamma s - Complex.digamma t)).add h).congr'
      (Filter.Eventually.of_forall
        (fun n ↦ (digamma_sub_add_nat_eq_partial_resolvent hs ht n).symm))

end PseudoPrime.AnalyticNumberTheory.Gamma
