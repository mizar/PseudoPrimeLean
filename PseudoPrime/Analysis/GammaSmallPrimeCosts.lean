/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaLargePrimeCosts
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # Rational certificates for small-prime Gamma costs -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At every scale at least 10000, the cutoff logarithm plus one divided
by the square root is at most 9/50. Apply the logarithm tangent inequality
at sqrt x divided by twenty, using log twenty below 7/2. The uniform
bound is small enough to combine with the exact prime-three Euler cost. -/
theorem gamma_small_prime_scale_ramp_bound {x : ℝ} (hx : 10000 ≤ x) :
    (Real.log ((99 / 40 : ℝ) * x) + 1) / Real.sqrt x ≤ (9 / 50 : ℝ) := by
  have hx0 : 0 < x := by linarith only [hx]
  have ht : (100 : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num only) hx0.le).mpr
      (by
        norm_num only; exact hx)
  have ht0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have h := Real.log_le_sub_one_of_pos (div_pos ht0 (by norm_num only : (0 : ℝ) < 20))
  rw [Real.log_div ht0.ne' (by norm_num only : (20 : ℝ) ≠ 0)] at h
  have hl32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    have he := Real.log_pow (2 : ℝ) 5
    norm_num only [Nat.cast_ofNat] at he
    exact he
  have hl20 : Real.log (20 : ℝ) ≤ 7 / 2 := by
    have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 20) (by norm_num only : (20 : ℝ) ≤ 32)
    linarith only [hm, hl32, Real.log_two_lt_d9]
  have he := Real.log_sqrt hx0.le
  have hc : Real.log (99 / 40 : ℝ) ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 99 / 40)
    linarith only [hh]
  rw [Real.log_mul (by norm_num only : (99 / 40 : ℝ) ≠ 0) hx0.ne']
  apply (div_le_iff₀ ht0).mpr
  linarith only [h, hl20, he, hc, ht]

/-- Exact twentieth-power inequalities give a real interval for p^(-m/20).
For a positive base, raising the real power to twenty gives p^(-m).
Monotonicity of the natural power transfers both rational endpoint checks.
This validates the small-prime ratio data without floating-point arithmetic. -/
theorem gamma_rpow_neg_twentieth_interval {p l u : ℝ} (hp : 0 < p) (hl : 0 ≤ l) (hu : 0 ≤ u) (m : ℕ)
    (hlo : l ^ 20 * p ^ m ≤ 1) (hhi : 1 ≤ u ^ 20 * p ^ m) :
    l ≤ p ^ (-(m : ℝ) / 20) ∧ p ^ (-(m : ℝ) / 20) ≤ u := by
  have hpow : 0 < p ^ m := pow_pos hp _
  have he : (p ^ (-(m : ℝ) / 20)) ^ 20 = (p ^ m)⁻¹ := by
    rw [← Real.rpow_mul_natCast hp.le]
    norm_num only [Nat.cast_ofNat]
    rw [show -(m : ℝ) / 20 * 20 = -(m : ℝ) by ring, Real.rpow_neg hp.le, Real.rpow_natCast]
  have hr := Real.rpow_nonneg hp.le (-(m : ℝ) / 20)
  constructor
  · apply (pow_le_pow_iff_left₀ hl hr (by decide : (20 : ℕ) ≠ 0)).mp
    rw [he, ← one_div]
    exact (le_div_iff₀ hpow).mpr hlo
  · apply (pow_le_pow_iff_left₀ hr hu (by decide : (20 : ℕ) ≠ 0)).mp
    rw [he, ← one_div]
    exact (div_le_iff₀ hpow).mpr hhi

/-- Rational ratio intervals for primes three, five and seven at each node.
Integer twentieth-power comparisons generated the endpoints with denominator
one million. The finite certificate below validates every endpoint in Lean. -/
def gammaSmallPrimeRatioInterval (p : ℕ) (a : ℚ) : ℚ × ℚ :=
  if p = 3 then
    if a = 11 / 20 then (315516 / 1000000, 315517 / 1000000)
    else
      if a = 13 / 20 then (282690 / 1000000, 282691 / 1000000)
      else
        if a = 16 / 20 then (239741 / 1000000, 239742 / 1000000)
        else
          if a = 20 / 20 then (192450 / 1000000, 192451 / 1000000)
          else
            if a = 26 / 20 then (138414 / 1000000, 138415 / 1000000)
            else
              if a = 34 / 20 then (89193 / 1000000, 89194 / 1000000)
              else
                if a = 46 / 20 then (46138 / 1000000, 46139 / 1000000)
                else
                  if a = 64 / 20 then (17165 / 1000000, 17166 / 1000000)
                  else
                    if a = 90 / 20 then (4115 / 1000000, 4116 / 1000000)
                    else if a = 140 / 20 then (263 / 1000000, 264 / 1000000) else (0, 0)
  else
    if p = 5 then
      if a = 11 / 20 then (184536 / 1000000, 184537 / 1000000)
      else
        if a = 13 / 20 then (157103 / 1000000, 157104 / 1000000)
        else
          if a = 16 / 20 then (123406 / 1000000, 123407 / 1000000)
          else
            if a = 20 / 20 then (89442 / 1000000, 89443 / 1000000)
            else
              if a = 26 / 20 then (55189 / 1000000, 55190 / 1000000)
              else
                if a = 34 / 20 then (28991 / 1000000, 28992 / 1000000)
                else
                  if a = 46 / 20 then (11037 / 1000000, 11038 / 1000000)
                  else
                    if a = 64 / 20 then (2593 / 1000000, 2594 / 1000000)
                    else
                      if a = 90 / 20 then (320 / 1000000, 321 / 1000000)
                      else if a = 140 / 20 then (5 / 1000000, 6 / 1000000) else (0, 0)
    else
      if p = 7 then
        if a = 11 / 20 then (129612 / 1000000, 129613 / 1000000)
        else
          if a = 13 / 20 then (106693 / 1000000, 106694 / 1000000)
          else
            if a = 16 / 20 then (79684 / 1000000, 79685 / 1000000)
            else
              if a = 20 / 20 then (53994 / 1000000, 53995 / 1000000)
              else
                if a = 26 / 20 then (30117 / 1000000, 30118 / 1000000)
                else
                  if a = 34 / 20 then (13828 / 1000000, 13829 / 1000000)
                  else
                    if a = 46 / 20 then (4302 / 1000000, 4303 / 1000000)
                    else
                      if a = 64 / 20 then (746 / 1000000, 747 / 1000000)
                      else
                        if a = 90 / 20 then (59 / 1000000, 60 / 1000000)
                        else if a = 140 / 20 then (0 / 1000000, 1 / 1000000) else (0, 0)
      else (0, 0)

/-- Integer exponent for p^(-(1/2+a)); the finite checks verify its value. -/
def gammaSmallPrimeRatioExponent (a : ℚ) : ℕ :=
  (20 * a + 10).num.toNat

/-- Each small-prime ratio has nonnegative ordered endpoints below one,
its exact integer exponent, and both twentieth-power inequalities.
Kernel computation on rational numbers supplies the finite certificate. -/
theorem gamma_small_prime_ratio_checks :
    ([3, 5, 7] : List ℕ).Forall
      (fun p ↦
        gammaResolventCoefficients.Forall
          (fun ab ↦
            let lu := gammaSmallPrimeRatioInterval p ab.1
            0 ≤ lu.1 ∧
              lu.1 ≤ lu.2 ∧
              lu.2 < 1 ∧
              20 * ab.1 + 10 = (gammaSmallPrimeRatioExponent ab.1 : ℚ) ∧
              lu.1 ^ 20 * (p : ℚ) ^ gammaSmallPrimeRatioExponent ab.1 ≤ 1 ∧
              1 ≤ lu.2 ^ 20 * (p : ℚ) ^ gammaSmallPrimeRatioExponent ab.1)) := by
  decide +kernel

/-- The certified rational interval contains the actual real ratio at every
small prime and every resolvent node. Cast the finite checks and compare
twentieth powers. This connects the exact rational data to the real Euler cost. -/
theorem gamma_small_prime_ratio_interval_valid {p : ℕ} (hp : p ∈ ([3, 5, 7] : List ℕ)) (ab : ℚ × ℚ)
    (hab : ab ∈ gammaResolventCoefficients) :
    (gammaSmallPrimeRatioInterval p ab.1).1 ≤ (p : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ∧
      (p : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ (gammaSmallPrimeRatioInterval p ab.1).2 := by
  obtain ⟨hl, hlu, hu, he, hlo, hhi⟩ :=
    List.forall_iff_forall_mem.mp
      (List.forall_iff_forall_mem.mp gamma_small_prime_ratio_checks p hp) ab hab
  have hp0 : (0 : ℝ) < p := by
    have hpos : ∀ q ∈ ([3, 5, 7] : List ℕ), 0 < q := by decide +kernel
    exact_mod_cast hpos p hp
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
    gamma_rpow_neg_twentieth_interval hp0 hlR (hlR.trans huR) (gammaSmallPrimeRatioExponent ab.1)
      hloR hhiR

/-- The odd-power geometric ratio is increasing between zero and one.
Increase the numerator and decrease the positive denominator. This permits
signed coefficients to choose the appropriate certified interval endpoint. -/
theorem gamma_odd_ratio_monotone {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s < 1) :
    r / (1 - r ^ 2) ≤ s / (1 - s ^ 2) := by
  have hs0 : 0 ≤ s := hr.trans hrs
  have hd : 0 < 1 - s ^ 2 := by nlinarith only [hs, hs0]
  have hds : 1 - s ^ 2 ≤ 1 - r ^ 2 := by nlinarith only [hr, hrs, hs0]
  exact div_le_div₀ hs0 hrs hd hds

/-- Select the upper ratio endpoint for a nonnegative coefficient and the
lower endpoint for a negative coefficient. The resulting rational node value
bounds the signed contribution without dropping its negative part. -/
def gammaSmallPrimeOddNodeUpper (p : ℕ) (ab : ℚ × ℚ) : ℚ :=
  let lu := gammaSmallPrimeRatioInterval p ab.1
  let r := if 0 ≤ ab.2 then lu.2 else lu.1
  ab.2 * (r / (1 - r ^ 2))

/-- Each real signed odd-power node is bounded by its rational certificate.
Ratio monotonicity and the sign of the coefficient select the correct
endpoint. This preserves the cancellation required at prime three. -/
theorem gamma_small_prime_odd_node_le {p : ℕ} (hp : p ∈ ([3, 5, 7] : List ℕ)) (ab : ℚ × ℚ)
    (hab : ab ∈ gammaResolventCoefficients) :
    (ab.2 : ℝ) *
        ((p : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) / (1 - ((p : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ)))) ^ 2)) ≤
      (gammaSmallPrimeOddNodeUpper p ab : ℝ) := by
  obtain ⟨hl, hlu, hu, _⟩ :=
    List.forall_iff_forall_mem.mp
      (List.forall_iff_forall_mem.mp gamma_small_prime_ratio_checks p hp) ab hab
  obtain ⟨hlo, hhi⟩ := gamma_small_prime_ratio_interval_valid hp ab hab
  have hlR := (Rat.cast_le (K := ℝ)).mpr hl
  have huR := (Rat.cast_lt (K := ℝ)).mpr hu
  norm_num only [Rat.cast_zero, Rat.cast_one] at hlR huR
  have hr0 := hlR.trans hlo
  have hr1 := hhi.trans_lt huR
  by_cases hb : 0 ≤ ab.2
  · simp only [gammaSmallPrimeOddNodeUpper, ite_eq_left hb, Rat.cast_mul, Rat.cast_div,
      Rat.cast_sub, Rat.cast_one, Rat.cast_pow]
    exact mul_le_mul_of_nonneg_left (gamma_odd_ratio_monotone hr0 hhi huR) (by exact_mod_cast hb)
  · simp only [gammaSmallPrimeOddNodeUpper, ite_eq_right hb, Rat.cast_mul, Rat.cast_div,
      Rat.cast_sub, Rat.cast_one, Rat.cast_pow]
    exact
      mul_le_mul_of_nonpos_left (gamma_odd_ratio_monotone hlR hlo hr1)
        (by exact_mod_cast (le_of_not_ge hb))

/-- The finite rational node bounds give twice the odd Euler cost at most
19/25 for each of the three small primes. Kernel arithmetic preserves all
signed terms and verifies the final numerical margin. -/
theorem gamma_small_prime_odd_upper_checks :
    ([3, 5, 7] : List ℕ).Forall
      (fun p ↦
        2 * (gammaResolventCoefficients.map (gammaSmallPrimeOddNodeUpper p)).sum ≤
          (19 / 25 : ℚ)) := by
  decide +kernel

/-- The actual signed odd Euler cost satisfies the certified bound at
three, five and seven. Sum the real node inequalities and cast the finite
rational certificate. This removes numerical assumptions at small primes. -/
theorem gamma_small_prime_odd_cost_le {p : ℕ} (hp : p ∈ ([3, 5, 7] : List ℕ)) :
    2 * gammaPrimeOddEulerCost p ≤ (19 / 25 : ℝ) := by
  have h := List.sum_le_sum (fun ab hab ↦ gamma_small_prime_odd_node_le hp ab hab)
  have hc :=
    (Rat.cast_le (K := ℝ)).mpr
      (List.forall_iff_forall_mem.mp gamma_small_prime_odd_upper_checks p hp)
  norm_num only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div, Rat.cast_list_sum, List.map_map,
    Function.comp_def] at hc
  change gammaPrimeOddEulerCost p ≤ _ at h
  linarith only [h, hc]

/-- For a natural base at least three and every scale at least 10000,
the continuous per-log-prime ramp allowance is at most 9/50. The logarithm
of the base is at least one, so the uniform cutoff bound applies directly. -/
theorem gamma_odd_prime_log_ramp_le {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 10000 ≤ x) :
    (Real.log ((99 / 40 : ℝ) * x) / Real.log p + 1) / Real.sqrt x ≤ (9 / 50 : ℝ) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hlp : (1 : ℝ) ≤ Real.log p := by
    have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) hpR
    linarith only [h, Real.log_three_gt_d9]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hcut : 0 ≤ Real.log ((99 / 40 : ℝ) * x) := Real.log_nonneg (by nlinarith only [hx1])
  have hdiv : Real.log ((99 / 40 : ℝ) * x) / Real.log p ≤ Real.log ((99 / 40 : ℝ) * x) := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hlp)).mpr
    nlinarith only [hcut, hlp]
  exact
    (div_le_div_of_nonneg_right (add_le_add hdiv le_rfl) (Real.sqrt_nonneg x)).trans
      (gamma_small_prime_scale_ramp_bound hx)

/-- Every prime at least three has combined square-prime allowance at
most 47/50 at scales at least 10000. Use the rational small-prime certificate
below eleven and the uniform large-prime estimate above it. This discharges
the per-prime numerical absorption condition for all odd primes. -/
theorem gamma_odd_prime_square_cost_le {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {x : ℝ}
    (hx : 10000 ≤ x) : gammaSquareCombinedCost p x ≤ (47 / 50 : ℝ) := by
  by_cases hlarge : 11 ≤ p
  · exact (gamma_large_prime_square_cost_le hlarge hx).trans (by norm_num only)
  · have hfinite : ∀ q ∈ Finset.range 11, q.Prime → 3 ≤ q → q ∈ ([3, 5, 7] : List ℕ) := by
      decide +kernel
    have hsmall := hfinite p (Finset.mem_range.mpr (lt_of_not_ge hlarge)) hp hp3
    have he := gamma_small_prime_odd_cost_le hsmall
    have hr := gamma_odd_prime_log_ramp_le hp3 hx
    have hc :=
      gamma_square_combined_cost_le_log (lt_of_lt_of_le (by norm_num only : (1 : ℕ) < 3) hp3)
        (by linarith only [hx] : (1 : ℝ) ≤ x)
    linarith only [he, hr, hc]

/-- For an odd ambient input and scales at least 10000, all selected
minus-one prime losses are absorbed by the certified conductor gap.
Oddness excludes prime two; the small and large prime certificates
discharge every remaining local numerical condition. -/
theorem gamma_odd_input_actual_cost_absorbed_by_conductor_gap {n d m f : ℕ} (hn : n = d * m ^ 2)
    (hodd : Odd n) (hd : 0 < d) (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d)
    (S : Finset ℕ) (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {x : ℝ} (hx : 10000 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log f +
        (∑ p ∈ S,
          ((∑ k ∈ K p,
              (1 - (χ (p ^ (2 * k + 1))).re) * gammaResolventMangoldtWeight (p ^ (2 * k + 1))) +
            Real.log p *
              ((∑' k : ℕ, exponentialRampLocalCorrection (-1) ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
                Real.sqrt x))) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) := by
  apply
    gamma_minus_one_actual_cost_absorbed_by_conductor_gap hn hd hm hf hdf hfd S hS χ hχ K
      (by linarith only [hx]) (by norm_num only)
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors (hS hp)
  have hpne : p ≠ 2 := by
    intro he
    exact hodd.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors (hS hp))
  have hp3 : 3 ≤ p := Nat.succ_le_iff.mpr (lt_of_le_of_ne hprime.two_le (Ne.symm hpne))
  exact
    (gamma_odd_prime_square_cost_le hprime hp3 hx).trans
      (by norm_num only : (47 / 50 : ℝ) ≤ 2 * (11783423 / 25000000 : ℝ))

end PseudoPrime.Analysis
