/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSignedRamifiedCosts
public import PseudoPrime.Analysis.Phase64DyadicEulerBounds
public import PseudoPrime.Analysis.GammaRamifiedFiniteSupport

/-! # Fixed finite support for the first-phase ramified dual cost -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Rational upper endpoints for the ten phase-candidate Euler ratios at base
100. The finite twentieth-power certificate validates every endpoint without
floating-point assumptions. Only the positive coefficients are used by the tail cap. -/
def phase64Anchor100RatioUpper (a : ℚ) : ℚ :=
  if a = 1 then 1 / 1000
  else
    if a = 6 / 5 then 39811 / 100000000
    else
      if a = 7 / 5 then 15849 / 100000000
      else if a = 5 / 2 then 101 / 100000000 else if a = 3 then 11 / 100000000 else 1 / 100000000

/-- Every anchor ratio lies in [0,1), its exponent matches the certified node,
and its twentieth power bounds the exact reciprocal power of 100. Kernel
reduction checks the finite rational data. -/
theorem phase64_anchor100_ratio_checks :
    phaseResolvent64Coefficients.Forall
      (fun ab ↦
        0 ≤ phase64Anchor100RatioUpper ab.1 ∧
          phase64Anchor100RatioUpper ab.1 < 1 ∧
          20 * ab.1 + 10 = (gammaSmallPrimeRatioExponent ab.1 : ℚ) ∧
          1 ≤
            (phase64Anchor100RatioUpper ab.1) ^ 20 * 100 ^ gammaSmallPrimeRatioExponent ab.1) := by
  decide +kernel

/-- For each phase node, the real Euler ratio at 100 is bounded by the rational
endpoint. Cast the checked power inequalities and apply the twentieth-root lemma. -/
theorem phase64_anchor100_ratio_valid (ab : ℚ × ℚ) (hab : ab ∈ phaseResolvent64Coefficients) :
    (100 : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ (phase64Anchor100RatioUpper ab.1 : ℝ) := by
  obtain ⟨hl, _, he, hh⟩ := List.forall_iff_forall_mem.mp phase64_anchor100_ratio_checks ab hab
  have hlR := (Rat.cast_le (K := ℝ)).mpr hl
  have hhR := (Rat.cast_le (K := ℝ)).mpr hh
  have heR := congrArg (fun q : ℚ ↦ (q : ℝ)) he
  norm_num only [Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_one, Rat.cast_zero] at hlR hhR heR
  have hexp : -(gammaSmallPrimeRatioExponent ab.1 : ℝ) / 20 = -(1 / 2 + (ab.1 : ℝ)) := by
    linarith only [heR]
  have h :=
    (gamma_rpow_neg_twentieth_interval (by norm_num only : (0 : ℝ) < 100) (le_refl (0 : ℝ)) hlR
        (gammaSmallPrimeRatioExponent ab.1) (by norm_num only [zero_pow, zero_mul]) hhR).2
  simpa only [hexp] using h

/-- The positive-coefficient geometric Euler allowance at the anchor 100.
Negative nodes contribute zero to this tail upper bound; signs remain exact in
the ramified cost used on the finite interior set. -/
def phase64Anchor100NodeUpper (ab : ℚ × ℚ) : ℚ :=
  if 0 ≤ ab.2 then ab.2 * (phase64Anchor100RatioUpper ab.1 / (1 - phase64Anchor100RatioUpper ab.1))
  else 0

/-- The positive anchor allowances sum to at most 1/200. Exact rational
kernel arithmetic certifies this bound for all ten phase nodes. -/
theorem phase64_anchor100_euler_check :
    (phaseResolvent64Coefficients.map phase64Anchor100NodeUpper).sum ≤ (1 / 200 : ℚ) := by
  decide +kernel

/-- For every real base at least 100, a signed Euler node is bounded by its
positive anchor allowance. Negative-power and geometric-ratio monotonicity
control the whole unbounded range of bases. -/
theorem phase64_anchor100_node_le {p : ℝ} (hp : 100 ≤ p) (ab : ℚ × ℚ)
    (hab : ab ∈ phaseResolvent64Coefficients) :
    (ab.2 : ℝ) * (p ^ (-(1 / 2 + (ab.1 : ℝ))) / (1 - p ^ (-(1 / 2 + (ab.1 : ℝ))))) ≤
      (phase64Anchor100NodeUpper ab : ℝ) := by
  have ha := phase64_node_exponents_pos ab hab
  have hr0 := Real.rpow_nonneg (by linarith only [hp] : 0 ≤ p) (-(1 / 2 + (ab.1 : ℝ)))
  have hdata := List.forall_iff_forall_mem.mp phase64_anchor100_ratio_checks ab hab
  have hu := (Rat.cast_lt (K := ℝ)).mpr hdata.2.1
  norm_num only [Rat.cast_one] at hu
  have hr :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 100) hp (neg_nonpos.mpr ha.le)).trans
      (phase64_anchor100_ratio_valid ab hab)
  by_cases hc : 0 ≤ ab.2
  · simp only [phase64Anchor100NodeUpper, ite_eq_left hc, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_one]
    have h := gamma_geometric_ratio_monotone hr0 hr hu (by norm_num only : 0 < (1 : ℕ))
    simp only [pow_one] at h
    exact mul_le_mul_of_nonneg_left h (by exact_mod_cast hc)
  · simp only [phase64Anchor100NodeUpper, ite_eq_right hc, Rat.cast_zero]
    exact
      mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast le_of_not_ge hc)
        (div_nonneg hr0 (sub_nonneg.mpr (hr.trans hu.le)))

/-- For every real base at least 100, the full signed Euler progression cost
is at most 1/200. Sum the anchor node inequalities and its rational certificate. -/
theorem phase64_euler_cost_le_of_ge_100 {p : ℝ} (hp : 100 ≤ p) :
    finiteSignedPrimeProgressionCost phaseResolvent64Coefficients p 1 1 ≤ (1 / 200 : ℝ) := by
  have h := List.sum_le_sum (fun ab hab ↦ phase64_anchor100_node_le hp ab hab)
  have hc := (Rat.cast_le (K := ℝ)).mpr phase64_anchor100_euler_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_list_sum, List.map_map,
    Function.comp_def] at hc
  have he :
    finiteSignedPrimeProgressionCost phaseResolvent64Coefficients p 1 1 ≤
      (phaseResolvent64Coefficients.map (fun ab ↦ (phase64Anchor100NodeUpper ab : ℝ))).sum := by
    simpa only [finiteSignedPrimeProgressionCost, pow_one] using h
  exact he.trans hc

/-- For natural bases at least 100 and scales from 1600 to 1700, the full Euler
cost plus the normalized ramp count is at most 3/100. The square of the base is
above the cutoff, so at most one power remains; sqrt x is at least 40. -/
theorem phase64_count_cost_le_three_hundredths {p : ℕ} (hp : 100 ≤ p) {x : ℝ} (hlo : 1600 ≤ x)
    (hhi : x ≤ 1700) :
    finiteSignedPrimeProgressionCost phaseResolvent64Coefficients p 1 1 +
        gammaRampPowerCount p x / Real.sqrt x ≤
      (3 / 100 : ℝ) := by
  have hpR : (100 : ℝ) ≤ p := by exact_mod_cast hp
  have he := phase64_euler_cost_le_of_ge_100 hpR
  have hpow := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 100) hpR 2
  norm_num only at hpow
  have hc :=
    gamma_ramp_count_le_one_of_square_above (Nat.lt_of_lt_of_le (by decide : 1 < 100) hp)
      (by linarith only [hlo] : 1 ≤ x)
      (by linarith only [hhi, hpow] : (99 / 40 : ℝ) * x < (p : ℝ) ^ 2)
  have hs : (40 : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num only) (by linarith only [hlo])).mpr
      (by
        norm_num only; exact hlo)
  have ht : 0 < Real.sqrt x := by linarith only [hs]
  have hr : gammaRampPowerCount p x / Real.sqrt x ≤ (1 / 40 : ℝ) := by
    apply (div_le_iff₀ ht).mpr
    linarith only [hc, hs]
  linarith only [he, hr]

/-- On scales 1600 to 1700, every base at least 100 has signed ramified cost
at most 3/100. The actual negative ramp tail is retained inside the finite set;
only this tail-support proof uses the coarser count envelope. -/
theorem phase64_signed_ramified_cost_le_three_hundredths {p : ℕ} (hp : 100 ≤ p) {x : ℝ}
    (hlo : 1600 ≤ x) (hhi : x ≤ 1700) :
    finiteSignedRamifiedCost phaseResolvent64Coefficients p x ≤ (3 / 100 : ℝ) := by
  exact
    (finiteSigned_ramified_cost_le_count phaseResolvent64Coefficients
          (Nat.lt_of_lt_of_le (by decide : 1 < 100) hp) (by linarith only [hlo] : 0 < x)).trans
      (phase64_count_cost_le_three_hundredths hp hlo hhi)

/-- The finite set of odd primes below 100. It contains all possible positive
ramified dual excess on scales 1600 to 1700, independent of the input factorization. -/
def phase64RamifiedPrimeSet : Finset ℕ :=
  (Finset.Icc 3 99).filter Nat.Prime

/-- The log-weighted positive excess of the exact signed ramified costs above
3/100 over the fixed prime set below 100. It retains both signed Euler coefficients
and the exact ramp series. This is the remaining finite numerical target. -/
noncomputable def phase64RamifiedExcess (x : ℝ) : ℝ :=
  ∑ p ∈ phase64RamifiedPrimeSet,
    Real.log p * max (finiteSignedRamifiedCost phaseResolvent64Coefficients p x - 3 / 100) 0

/-- For any finite odd-prime set and scales 1600 to 1700, its positive excess
is bounded by the fixed finite excess. Outside primes have cost at most 3/100,
so their positive parts vanish exactly. -/
theorem phase64_ramified_excess_le_finite (R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime ∧ 3 ≤ p) {x : ℝ}
    (hlo : 1600 ≤ x) (hhi : x ≤ 1700) :
    (∑ p ∈ R,
        Real.log p * max (finiteSignedRamifiedCost phaseResolvent64Coefficients p x - 3 / 100) 0) ≤
      phase64RamifiedExcess x := by
  apply prime_weighted_positive_excess_le_finite
  intro p hp hnot
  have hd := hR p hp
  have hpbig : 100 ≤ p := by
    apply le_of_not_gt
    intro hlt
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd.2, Nat.le_of_lt_succ hlt⟩, hd.1⟩)
  exact phase64_signed_ramified_cost_le_three_hundredths hpbig hlo hhi

/-- For selected ramified prime factors of an odd input, arbitrary finite Euler
prefixes and scales 1600 to 1700, all actual local costs fit (3/100) log n plus
the fixed finite signed excess. No factorization-dependent numerical hypothesis
or finite-input enumeration remains. -/
theorem phase64_actual_ramified_cost_le_finite_dual {n f : ℕ} (hn : Odd n) (R : Finset ℕ)
    (hR : R ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ R, χ p = 0)
    (K : ℕ → Finset ℕ) {x : ℝ} (hlo : 1600 ≤ x) (hhi : x ≤ 1700) :
    (∑ p ∈ R, finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ p (K p) x) ≤
      (3 / 100 : ℝ) * Real.log n + phase64RamifiedExcess x := by
  have hs :=
    finiteSigned_ramified_cost_le_input_dual phaseResolvent64Coefficients phase64_node_exponents_pos
      (fun u hu ↦ phaseResolvent64_euler_nonneg hu) hn.pos R hR χ hχ K x
      (by norm_num only : (0 : ℝ) ≤ 3 / 100)
  have he :=
    phase64_ramified_excess_le_finite R
      (fun p hp ↦ by
        have hprime := Nat.prime_of_mem_primeFactors (hR hp)
        have hpne : p ≠ 2 := fun h ↦ hn.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors (hR hp))
        exact ⟨hprime, Nat.succ_le_iff.mpr (lt_of_le_of_ne hprime.two_le (Ne.symm hpne))⟩)
      hlo hhi
  linarith only [hs, he]

end PseudoPrime.Analysis
