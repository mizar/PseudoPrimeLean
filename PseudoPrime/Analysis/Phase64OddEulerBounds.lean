/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64DyadicEulerBounds

/-! # Uniform odd-prime Euler costs for the first phase candidate -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Rational intervals of width 1/100000000 for the ten phase-candidate ratios
at primes three, five and seven. Exact twentieth-power checks validate these endpoints. -/
def phase64OddRatioInterval (p : ℕ) (a : ℚ) : ℚ × ℚ :=
  if p = 3 then
    if a = 1 then (19245008 / 100000000, 19245009 / 100000000)
    else
      if a = 6 / 5 then (15448768 / 100000000, 15448769 / 100000000)
      else
        if a = 7 / 5 then (12401368 / 100000000, 12401369 / 100000000)
        else
          if a = 5 / 2 then (3703703 / 100000000, 3703704 / 100000000)
          else
            if a = 3 then (2138334 / 100000000, 2138335 / 100000000)
            else
              if a = 5 then (237592 / 100000000, 237593 / 100000000)
              else
                if a = 7 then (26399 / 100000000, 26400 / 100000000)
                else
                  if a = 10 then (977 / 100000000, 978 / 100000000)
                  else
                    if a = 15 then (4 / 100000000, 5 / 100000000)
                    else if a = 20 then (0 / 100000000, 1 / 100000000) else (0, 0)
  else
    if p = 5 then
      if a = 1 then (8944271 / 100000000, 8944272 / 100000000)
      else
        if a = 6 / 5 then (6482626 / 100000000, 6482627 / 100000000)
        else
          if a = 7 / 5 then (4698475 / 100000000, 4698476 / 100000000)
          else
            if a = 5 / 2 then (800000 / 100000000, 800001 / 100000000)
            else
              if a = 3 then (357770 / 100000000, 357771 / 100000000)
              else
                if a = 5 then (14310 / 100000000, 14311 / 100000000)
                else
                  if a = 7 then (572 / 100000000, 573 / 100000000)
                  else
                    if a = 10 then (4 / 100000000, 5 / 100000000)
                    else
                      if a = 15 then (0 / 100000000, 1 / 100000000)
                      else if a = 20 then (0 / 100000000, 1 / 100000000) else (0, 0)
    else
      if p = 7 then
        if a = 1 then (5399492 / 100000000, 5399493 / 100000000)
        else
          if a = 6 / 5 then (3658755 / 100000000, 3658756 / 100000000)
          else
            if a = 7 / 5 then (2479212 / 100000000, 2479213 / 100000000)
            else
              if a = 5 / 2 then (291545 / 100000000, 291546 / 100000000)
              else
                if a = 3 then (110193 / 100000000, 110194 / 100000000)
                else
                  if a = 5 then (2248 / 100000000, 2249 / 100000000)
                  else
                    if a = 7 then (45 / 100000000, 46 / 100000000)
                    else
                      if a = 10 then (0 / 100000000, 1 / 100000000)
                      else
                        if a = 15 then (0 / 100000000, 1 / 100000000)
                        else if a = 20 then (0 / 100000000, 1 / 100000000) else (0, 0)
      else (0, 0)

/-- The three prime rows have bases above one, ordered ratio intervals below one,
and exact twentieth-power inequalities. Kernel reduction checks the finite rational data. -/
theorem phase64_odd_ratio_checks :
    ([3, 5, 7] : List ℕ).Forall
      (fun p ↦
        1 < p ∧
          phaseResolvent64Coefficients.Forall
            (fun ab ↦
              let lu := phase64OddRatioInterval p ab.1
              0 ≤ lu.1 ∧
                lu.1 ≤ lu.2 ∧
                lu.2 < 1 ∧
                20 * ab.1 + 10 = (gammaSmallPrimeRatioExponent ab.1 : ℚ) ∧
                lu.1 ^ 20 * (p : ℚ) ^ gammaSmallPrimeRatioExponent ab.1 ≤ 1 ∧
                1 ≤ lu.2 ^ 20 * (p : ℚ) ^ gammaSmallPrimeRatioExponent ab.1)) := by
  decide +kernel

/-- The certified odd-prime interval contains each actual real Euler ratio.
Cast the finite checks and apply the proved twentieth-root interval theorem.
This connects the rational data to both odd-prime geometric cost formulas. -/
theorem phase64_odd_ratio_interval_valid {p : ℕ} (hp : p ∈ ([3, 5, 7] : List ℕ)) (ab : ℚ × ℚ)
    (hab : ab ∈ phaseResolvent64Coefficients) :
    (phase64OddRatioInterval p ab.1).1 ≤ (p : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ∧
      (p : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ (phase64OddRatioInterval p ab.1).2 := by
  obtain ⟨hl, hlu, _, he, hlo, hhi⟩ :=
    List.forall_iff_forall_mem.mp (List.forall_iff_forall_mem.mp phase64_odd_ratio_checks p hp).2 ab
      hab
  have hlR := (Rat.cast_le (K := ℝ)).mpr hl
  have huR := (Rat.cast_le (K := ℝ)).mpr hlu
  have hloR := (Rat.cast_le (K := ℝ)).mpr hlo
  have hhiR := (Rat.cast_le (K := ℝ)).mpr hhi
  have heR := congrArg (fun q : ℚ ↦ (q : ℝ)) he
  norm_num only [Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_one, Rat.cast_zero] at hlR huR hloR hhiR heR
  have hexp : -(gammaSmallPrimeRatioExponent ab.1 : ℝ) / 20 = -(1 / 2 + (ab.1 : ℝ)) := by
    linarith only [heR]
  simpa only [hexp] using
    gamma_rpow_neg_twentieth_interval
      (by
        exact_mod_cast
          (Nat.zero_lt_of_lt (List.forall_iff_forall_mem.mp phase64_odd_ratio_checks p hp).1))
      hlR (hlR.trans huR) (gammaSmallPrimeRatioExponent ab.1) hloR hhiR

def phase64OddNodeUpper (p : ℕ) (ab : ℚ × ℚ) : ℚ :=
  let lu := phase64OddRatioInterval p ab.1
  let r := if 0 ≤ ab.2 then lu.2 else lu.1
  ab.2 * (r / (1 - r ^ 2))

/-- Each actual signed odd-prime node is bounded by its rational allowance.
Apply ratio monotonicity with the correct endpoint for the coefficient sign.
This validates both even-conductor and odd-conductor Euler certificates. -/
theorem phase64_odd_node_le {p : ℕ} (hp : p ∈ ([3, 5, 7] : List ℕ)) (ab : ℚ × ℚ)
    (hab : ab ∈ phaseResolvent64Coefficients) :
    (ab.2 : ℝ) *
        ((p : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) / (1 - ((p : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ)))) ^ 2)) ≤
      (phase64OddNodeUpper p ab : ℝ) := by
  obtain ⟨hl, _, hu, _⟩ :=
    List.forall_iff_forall_mem.mp (List.forall_iff_forall_mem.mp phase64_odd_ratio_checks p hp).2 ab
      hab
  obtain ⟨hlo, hhi⟩ := phase64_odd_ratio_interval_valid hp ab hab
  have hlR := (Rat.cast_le (K := ℝ)).mpr hl
  have huR := (Rat.cast_lt (K := ℝ)).mpr hu
  norm_num only [Rat.cast_zero, Rat.cast_one] at hlR huR
  have hr0 := hlR.trans hlo
  have hr1 := hhi.trans_lt huR
  by_cases hb : 0 ≤ ab.2
  · simp only [phase64OddNodeUpper, ite_eq_left hb, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_one, Rat.cast_pow]
    exact
      mul_le_mul_of_nonneg_left
        (gamma_geometric_ratio_monotone hr0 hhi huR (by norm_num only : 0 < (2 : ℕ)))
        (by exact_mod_cast hb)
  · simp only [phase64OddNodeUpper, ite_eq_right hb, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_one, Rat.cast_pow]
    exact
      mul_le_mul_of_nonpos_left
        (gamma_geometric_ratio_monotone hlR hlo hr1 (by norm_num only : 0 < (2 : ℕ)))
        (by exact_mod_cast (le_of_not_ge hb))

/-- At three, five and seven, the signed rational node allowances sum to at most
349/1000. The kernel checks this finite certificate before any real-number transfer. -/
theorem phase64_small_odd_euler_upper_checks :
    ([3, 5, 7] : List ℕ).Forall
      (fun p ↦
        (phaseResolvent64Coefficients.map (phase64OddNodeUpper p)).sum ≤ (349 / 1000 : ℚ)) := by
  decide +kernel

/-- At the three certified primes, the exact signed odd Euler cost is at most
349/1000. Sum the sign-sensitive node inequalities and cast the rational certificate. -/
theorem phase64_small_odd_euler_cost_le {p : ℕ} (hp : p ∈ ([3, 5, 7] : List ℕ)) :
    finiteSignedPrimeProgressionCost phaseResolvent64Coefficients p 2 1 ≤ (349 / 1000 : ℝ) := by
  have h := List.sum_le_sum (fun ab hab ↦ phase64_odd_node_le hp ab hab)
  have hc :=
    (Rat.cast_le (K := ℝ)).mpr
      (List.forall_iff_forall_mem.mp phase64_small_odd_euler_upper_checks p hp)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_list_sum, List.map_map,
    Function.comp_def] at hc
  have he :
    finiteSignedPrimeProgressionCost phaseResolvent64Coefficients p 2 1 ≤
      (phaseResolvent64Coefficients.map (fun ab ↦ (phase64OddNodeUpper p ab : ℝ))).sum := by
    simpa only [finiteSignedPrimeProgressionCost, pow_one] using h
  exact he.trans hc

/-- The nonnegative-coefficient part of the prime-seven upper envelope.
Negative nodes are discarded only for the unbounded prime range, retaining a valid upper bound. -/
def phase64PositiveOddNodeUpper (ab : ℚ × ℚ) : ℚ :=
  if 0 ≤ ab.2 then phase64OddNodeUpper 7 ab else 0

/-- The positive prime-seven node envelope is at most 349/1000.
Kernel rational arithmetic validates the large-prime allowance. -/
theorem phase64_positive_odd_upper_check :
    (phaseResolvent64Coefficients.map phase64PositiveOddNodeUpper).sum ≤ (349 / 1000 : ℚ) := by
  decide +kernel

/-- For every real base at least seven, a signed odd Euler node is bounded by
the positive prime-seven envelope. Negative powers and geometric-ratio monotonicity prove
this coefficientwise comparison, without a finite enumeration of the base. -/
theorem phase64_large_odd_node_le {p : ℝ} (hp : 7 ≤ p) (ab : ℚ × ℚ)
    (hab : ab ∈ phaseResolvent64Coefficients) :
    (ab.2 : ℝ) * (p ^ (-(1 / 2 + (ab.1 : ℝ))) / (1 - (p ^ (-(1 / 2 + (ab.1 : ℝ)))) ^ 2)) ≤
      (phase64PositiveOddNodeUpper ab : ℝ) := by
  have ha := phase64_node_exponents_pos ab hab
  have hr0 := Real.rpow_nonneg (by linarith only [hp] : 0 ≤ p) (-(1 / 2 + (ab.1 : ℝ)))
  have hmem : 7 ∈ ([3, 5, 7] : List ℕ) := by decide +kernel
  have hdata :=
    List.forall_iff_forall_mem.mp (List.forall_iff_forall_mem.mp phase64_odd_ratio_checks 7 hmem).2
      ab hab
  have hhi := (phase64_odd_ratio_interval_valid hmem ab hab).2
  have hu := (Rat.cast_lt (K := ℝ)).mpr hdata.2.2.1
  norm_num only [Rat.cast_one] at hu
  have hr :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 7) hp (neg_nonpos.mpr ha.le)).trans
      hhi
  by_cases hc : 0 ≤ ab.2
  · simp only [phase64PositiveOddNodeUpper, phase64OddNodeUpper, ite_eq_left hc, Rat.cast_mul,
      Rat.cast_div, Rat.cast_sub, Rat.cast_one, Rat.cast_pow]
    exact
      mul_le_mul_of_nonneg_left
        (gamma_geometric_ratio_monotone hr0 hr hu (by norm_num only : 0 < (2 : ℕ)))
        (by exact_mod_cast hc)
  · simp only [phase64PositiveOddNodeUpper, ite_eq_right hc, Rat.cast_zero]
    have hd : 0 ≤ 1 - (p ^ (-(1 / 2 + (ab.1 : ℝ)))) ^ 2 :=
      sub_nonneg.mpr ((pow_le_pow_left₀ hr0 (hr.trans hu.le) 2).trans_eq (one_pow 2))
    exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast le_of_not_ge hc) (div_nonneg hr0 hd)

/-- For every real base at least seven, the exact signed odd Euler cost is at most
349/1000. Sum the positive prime-seven envelope and its rational certificate. -/
theorem phase64_large_odd_euler_cost_le {p : ℝ} (hp : 7 ≤ p) :
    finiteSignedPrimeProgressionCost phaseResolvent64Coefficients p 2 1 ≤ (349 / 1000 : ℝ) := by
  have h := List.sum_le_sum (fun ab hab ↦ phase64_large_odd_node_le hp ab hab)
  have hc := (Rat.cast_le (K := ℝ)).mpr phase64_positive_odd_upper_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_list_sum, List.map_map,
    Function.comp_def] at hc
  have he :
    finiteSignedPrimeProgressionCost phaseResolvent64Coefficients p 2 1 ≤
      (phaseResolvent64Coefficients.map (fun ab ↦ (phase64PositiveOddNodeUpper ab : ℝ))).sum := by
    simpa only [finiteSignedPrimeProgressionCost, pow_one] using h
  exact he.trans hc

/-- For every prime at least three, twice the signed odd Euler cost is at most
349/500. The small signed certificates and large-base positive envelope cover all primes. -/
theorem phase64_odd_euler_cost_uniform {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    2 * finiteSignedPrimeProgressionCost phaseResolvent64Coefficients p 2 1 ≤ (349 / 500 : ℝ) := by
  by_cases hl : 7 ≤ p
  · have h := phase64_large_odd_euler_cost_le (by exact_mod_cast hl : (7 : ℝ) ≤ p)
    linarith only [h]
  · have hf : ∀ q ∈ Finset.range 7, q.Prime → 3 ≤ q → q ∈ ([3, 5, 7] : List ℕ) := by decide +kernel
    have h := phase64_small_odd_euler_cost_le (hf p (Finset.mem_range.mpr (lt_of_not_ge hl)) hp hp3)
    linarith only [h]

end PseudoPrime.Analysis
