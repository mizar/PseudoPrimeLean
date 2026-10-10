/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CosetRootTail
public import PseudoPrime.LLS.RiemannWeightedUpperBounds
public import Mathlib.Data.Rat.Cast.Order

/-!
# Explicit bounds for odd composite prime powers

The odd finite root prefix and the full remaining tail fit below one seventh of
the cutoff square root. Apply the RH Mangoldt bound to each odd exponent slice.
At smaller cutoffs, retain the finite root sum and bound it with natural-power
and square certificates instead of using the one-seventh estimate.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open Classical in
/-- For a nonnegative cutoff and an upper exponent limit, bounds on the roots
and their square roots give an upper bound for the full odd root sum. The root
bounds follow from ordinary natural powers; extra exponents have nonnegative
contributions. This turns the finite root majorant into rational certificates. -/
theorem oddRootSum_le_of_power_certificates {x : ℝ} (hx : 0 ≤ x) {K : ℕ}
    (hK : ⌊Real.log x / Real.log 2⌋₊ ≤ K) (b c : ℕ → ℝ)
    (hb : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ b k)
    (hc : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ c k)
    (hpow : ∀ k ∈ (Finset.Icc 3 K).filter Odd, x ≤ b k ^ k)
    (hsq : ∀ k ∈ (Finset.Icc 3 K).filter Odd, b k ≤ c k ^ 2) :
    (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
        (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) ≤
      ∑ k ∈ (Finset.Icc 3 K).filter Odd, (k : ℝ) * (b k + c k / 20) := by
  have hsub :
    (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd ⊆ (Finset.Icc 3 K).filter Odd := by
    intro k hk
    obtain ⟨hki, ho⟩ := Finset.mem_filter.mp hk
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hki
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl, hu.trans hK⟩, ho⟩
  have hs :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ ↦
        mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
          (add_nonneg (Real.rpow_nonneg hx ((1 : ℝ) / k))
            (div_nonneg (Real.sqrt_nonneg (x ^ ((1 : ℝ) / k))) (by norm_num only : (0 : ℝ) ≤ 20))))
  apply hs.trans
  apply Finset.sum_le_sum
  intro k hk
  have hk0 : 0 < k :=
    lt_of_lt_of_le (by norm_num only : 0 < 3) (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
  have hr := root_le_of_le_nat_pow hx (hb k hk) hk0 (hpow k hk)
  have ht := (Real.sqrt_le_left (hc k hk)).mpr (hr.trans (hsq k hk))
  exact
    mul_le_mul_of_nonneg_left (add_le_add hr (div_le_div_of_nonneg_right ht (by norm_num only)))
      (Nat.cast_nonneg k)

/-- Above cutoff one billion, the root majorant over odd exponents at least three
is at most one seventh of the cutoff square root. Cover the exponent set by the
odd prefix through twenty-eight and the full tail; their coefficients are
27/200 and 7/1000. This supplies the numerical nonsquare majorant in Section 4.1. -/
theorem oddRootSum_le_sqrt_seventh {x : ℝ} (hx : 1000000000 ≤ x) :
    (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
        (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) ≤
      Real.sqrt x / 7 := by
  classical
  let K := ⌊Real.log x / Real.log 2⌋₊
  let s := (Finset.Icc 3 28).filter Odd
  let t := Finset.Icc 29 K
  have hd : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro k hs ht
    have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
    have h2 := (Finset.mem_Icc.mp ht).1
    linarith only [h1, h2]
  have hsub : (Finset.Icc 3 K).filter Odd ⊆ s ∪ t := by
    intro k hk
    obtain ⟨hki, hodd⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk3, hkK⟩ := Finset.mem_Icc.mp hki
    by_cases hk28 : k ≤ 28
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk3, hk28⟩, hodd⟩)
    · exact
        Finset.mem_union_right _
          (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge hk28), hkK⟩)
  have hx0 : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 1000000000).trans hx
  have hb :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ ↦
        mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
          (add_nonneg (Real.rpow_nonneg hx0 ((1 : ℝ) / k))
            (div_nonneg (Real.sqrt_nonneg (x ^ ((1 : ℝ) / k))) (by norm_num only : (0 : ℝ) ≤ 20))))
  rw [Finset.sum_union hd] at hb
  have hp := smallOddRootPrefix_le_sqrt_fraction hx
  have ht := rootTail_le_sqrt_fraction hx
  change
    (∑ k ∈ (Finset.Icc 3 K).filter Odd,
        (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) ≤
      Real.sqrt x / 7
  change
    (∑ k ∈ s, (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) ≤
      (27 / 200 : ℝ) * Real.sqrt x at hp
  change
    (∑ k ∈ t, (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20)) ≤
      (7 / 1000 : ℝ) * Real.sqrt x at ht
  linarith only [hb, hp, ht, Real.sqrt_nonneg x]

/-- Under RH, for any cutoff greater than one, odd prime powers with exponent
at least three contribute at most the finite root majorant. Bound each prime
slice by the full Mangoldt sum at its root cutoff and apply the RH estimate.
Retaining this sum allows the residue-class comparison at smaller cutoffs. -/
theorem oddPrimePowerLogWeightedSum_le_explicit_root_sum (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 1 < x) :
    (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x (p ^ k)) ≤
      ∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
        (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20) := by
  apply Finset.sum_le_sum
  intro k hk
  have hk3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num only) hk3
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk0
  have hs :=
    AnalyticNumberTheory.Arithmetic.primePowerExponentSlice_le_logWeightedMangoldtSum
      (zero_lt_one.trans hx) hk0
  have hb :=
    mul_le_mul_of_nonneg_left
      (logWeightedMangoldtSum_le_add_sqrt_twentieth hRH
        (Real.one_lt_rpow hx (div_pos zero_lt_one hkR)))
      hkR.le
  exact hs.trans hb

/-- Under RH and cutoff greater than one, retain the negative corrections in
the finite upper bound for odd prime powers of exponent at least three.
Bound each prime slice by the corrected Mangoldt estimate at its root cutoff.
This supplies the odd-power term for the sharper small-modulus residue comparison. -/
theorem oddPrimePowerLogWeightedSum_le_corrected_root_sum (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 1 < x) :
    (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x (p ^ k)) ≤
      ∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
        (k : ℝ) *
          (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20 -
              Real.log (2 * Real.pi) * Real.log (x ^ ((1 : ℝ) / k)) -
              19 / 20 +
            Real.pi ^ 2 / 24) := by
  apply Finset.sum_le_sum
  intro k hk
  have hk3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num only) hk3
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk0
  exact
    (AnalyticNumberTheory.Arithmetic.primePowerExponentSlice_le_logWeightedMangoldtSum
          (zero_lt_one.trans hx) hk0).trans
      (mul_le_mul_of_nonneg_left
        (logWeightedMangoldtSum_le_explicit hRH (Real.one_lt_rpow hx (div_pos zero_lt_one hkR)))
        hkR.le)

/-- Under RH and above cutoff one billion, the logarithmic Mangoldt contribution
of odd prime powers with exponent at least three is at most one seventh of the
cutoff square root. Bound each prime slice by the full Mangoldt sum at its root
cutoff and apply the odd root majorant. This gives the odd-power upper estimate
needed in the residue-class argument of LLS Section 4.1. -/
theorem oddPrimePowerLogWeightedSum_le_sqrt_seventh (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 1000000000 ≤ x) :
    (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x (p ^ k)) ≤
      Real.sqrt x / 7 := by
  exact
    (oddPrimePowerLogWeightedSum_le_explicit_root_sum hRH
          (lt_of_lt_of_le (by norm_num only) hx)).trans
      (oddRootSum_le_sqrt_seventh hx)

/-- Check rational power bounds for each odd exponent from three through `K`.
The natural values `b` bound the roots of `X`, and `c` bound their square roots.
This finite Boolean test supplies root data for analytic residue certificates. -/
def oddRootPowerCheck (X : ℚ) (K : ℕ) (b c : ℕ → ℕ) : Bool :=
  decide (∀ k ∈ (Finset.Icc 3 K).filter Odd, X ≤ (b k : ℚ) ^ k ∧ b k ≤ c k ^ 2)

/-- A successful rational power check gives the corresponding real inequalities
at every checked odd exponent. Reflect the Boolean result and cast the rational
and natural inequalities. These bounds feed the finite root-sum majorant. -/
theorem oddRootPowerCheck_sound {X : ℚ} {K : ℕ} {b c : ℕ → ℕ}
    (h : oddRootPowerCheck X K b c = true) :
    ∀ k ∈ (Finset.Icc 3 K).filter Odd, (X : ℝ) ≤ (b k : ℝ) ^ k ∧ (b k : ℝ) ≤ (c k : ℝ) ^ 2 := by
  have hc : ∀ k ∈ (Finset.Icc 3 K).filter Odd, X ≤ (b k : ℚ) ^ k ∧ b k ≤ c k ^ 2 :=
    of_decide_eq_true h
  intro k hk
  have hp := (Rat.cast_le (K := ℝ)).mpr (hc k hk).1
  have hs := (Nat.cast_le (α := ℝ)).mpr (hc k hk).2
  exact
    ⟨by simpa only [Rat.cast_pow, Rat.cast_natCast] using hp, by simpa only [Nat.cast_pow] using hs⟩

/-- Under RH and cutoff greater than one, the odd prime-power root bound retains
the rational saving `183/100 * log x + k/2` for each exponent `k`.
Apply the corrected Mangoldt bound at its root cutoff and use
`k * log(x^(1/k)) = log x`. This is the odd-power expression in refined rational certificates. -/
theorem oddPrimePowerLogWeightedSum_le_rational_corrected_root_sum (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 1 < x) :
    (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x (p ^ k)) ≤
      ∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
        ((k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20) -
          (183 / 100 : ℝ) * Real.log x -
          (k : ℝ) / 2) := by
  apply Finset.sum_le_sum
  intro k hk
  have hk0 : 0 < k :=
    lt_of_lt_of_le (by norm_num only : 0 < 3) (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk0
  have hs :=
    (AnalyticNumberTheory.Arithmetic.primePowerExponentSlice_le_logWeightedMangoldtSum
          (zero_lt_one.trans hx) hk0).trans
      (mul_le_mul_of_nonneg_left
        (logWeightedMangoldtSum_le_simple_corrected hRH
          (Real.one_lt_rpow hx (div_pos zero_lt_one hkR)))
        hkR.le)
  rw [Real.log_rpow (zero_lt_one.trans hx)] at hs
  have hi : (k : ℝ) * ((1 : ℝ) / k) = 1 := by rw [← mul_div_assoc, mul_one, div_self hkR.ne']
  have hl := congrArg (fun z : ℝ ↦ z * Real.log x) hi
  nlinarith only [hs, hl]

open Classical in
/-- Under RH, bound the odd composite prime-power contribution using supplied
root and square-root bounds, a lower cutoff logarithm, and an upper exponent limit.
Require every corrected rational summand to be nonnegative: this permits extending
the exponent set without discarding the negative logarithmic correction.
Apply the corrected Mangoldt bound, bound each root by its natural-power certificate,
and extend the resulting finite sum. This supplies refined residue-gap certificates. -/
theorem oddPrimePowerLogWeightedSum_le_corrected_power_certificates (hRH : RiemannHypothesis)
    {x T : ℝ} (hx : 1 < x) (hT : T ≤ Real.log x) {K : ℕ} (hK : ⌊Real.log x / Real.log 2⌋₊ ≤ K)
    (b c : ℕ → ℝ) (hb : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ b k)
    (hc : ∀ k ∈ (Finset.Icc 3 K).filter Odd, 0 ≤ c k)
    (hpow : ∀ k ∈ (Finset.Icc 3 K).filter Odd, x ≤ b k ^ k)
    (hsq : ∀ k ∈ (Finset.Icc 3 K).filter Odd, b k ≤ c k ^ 2)
    (hpos :
      ∀ k ∈ (Finset.Icc 3 K).filter Odd,
        0 ≤ (k : ℝ) * (b k + c k / 20) - 183 / 100 * T - (k : ℝ) / 2) :
    (∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
          AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x (p ^ k)) ≤
      ∑ k ∈ (Finset.Icc 3 K).filter Odd,
        ((k : ℝ) * (b k + c k / 20) - 183 / 100 * T - (k : ℝ) / 2) := by
  have hsub :
    (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd ⊆ (Finset.Icc 3 K).filter Odd := by
    intro k hk
    obtain ⟨hki, ho⟩ := Finset.mem_filter.mp hk
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hki
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl, hu.trans hK⟩, ho⟩
  have hs :=
    Finset.sum_le_sum (s := (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd) (f :=
      fun (k : ℕ) ↦
      (k : ℝ) * (x ^ ((1 : ℝ) / k) + Real.sqrt (x ^ ((1 : ℝ) / k)) / 20) - 183 / 100 * Real.log x -
        (k : ℝ) / 2)
      (g := fun (k : ℕ) ↦ (k : ℝ) * (b k + c k / 20) - 183 / 100 * T - (k : ℝ) / 2)
      (fun k hk ↦ by
        have hkK := hsub hk
        have hk0 : 0 < k :=
          lt_of_lt_of_le (by norm_num only : 0 < 3)
            (Finset.mem_Icc.mp (Finset.mem_filter.mp hkK).1).1
        have hr := root_le_of_le_nat_pow (zero_lt_one.trans hx).le (hb k hkK) hk0 (hpow k hkK)
        have ht := (Real.sqrt_le_left (hc k hkK)).mpr (hr.trans (hsq k hkK))
        have hm :=
          mul_le_mul_of_nonneg_left
            (add_le_add hr (div_le_div_of_nonneg_right ht (by norm_num only : (0 : ℝ) ≤ 20)))
            (Nat.cast_nonneg k)
        linarith only [hm, hT])
  exact
    (oddPrimePowerLogWeightedSum_le_rational_corrected_root_sum hRH hx).trans
      (hs.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ ↦ hpos k hk)))

end PseudoPrime.LLS.PaperStatements
