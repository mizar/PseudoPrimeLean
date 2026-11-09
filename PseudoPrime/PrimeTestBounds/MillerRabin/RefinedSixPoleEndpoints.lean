/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalDecimalScale
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalDivisorLogBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleMonotonicity
public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors
public import PseudoPrime.PrimeTestBounds.MillerRabin.TotalFactorWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.MixedTwoAdicLogBounds

/-! # Rational endpoint inputs for the refined residual -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Exact rational checks enclose the logarithms and negative powers at the three
entrance radii. The logarithm and power soundness theorems convert these finite
checks into the real inequalities needed to bound the residual endpoints. -/
theorem refined_endpoint_checks :
    Analysis.rationalLogIntervalCheck 522 10 64 0 (6258 / 1000) = true ∧
      Analysis.rationalLogIntervalCheck 1566 11 64 0 (7357 / 1000) = true ∧
      Analysis.rationalLogIntervalCheck 5220 13 64 0 (8561 / 1000) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (522 ^ 2) 0 (135 / 100000000) 27
          25 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (1566 ^ 2) 0 (126 / 1000000000) 27
          25 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (5220 ^ 2) 0 (934 / 100000000000)
          27 25 =
        true := by
  decide +kernel

/-- The logarithms and negative squared-radius powers at the three entrances
satisfy explicit rational upper bounds. These follow by soundness of the exact
checks and supply the numerical inputs to the residual endpoint estimates. -/
theorem refined_endpoint_inputs :
    Real.log 522 ≤ (6258 / 1000 : ℝ) ∧
      Real.log 1566 ≤ (7357 / 1000 : ℝ) ∧
      Real.log 5220 ≤ (8561 / 1000 : ℝ) ∧
      ((522 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ 135 / 100000000 ∧
      ((1566 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ 126 / 1000000000 ∧
      ((5220 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ 934 / 100000000000 := by
  have h1 := Analysis.rationalLogIntervalCheck_sound refined_endpoint_checks.1
  have h2 := Analysis.rationalLogIntervalCheck_sound refined_endpoint_checks.2.1
  have h3 := Analysis.rationalLogIntervalCheck_sound refined_endpoint_checks.2.2.1
  have h4 :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound refined_endpoint_checks.2.2.2.1
  have h5 :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      refined_endpoint_checks.2.2.2.2.1
  have h6 :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      refined_endpoint_checks.2.2.2.2.2
  norm_num only at h1 h2 h3 h4 h5 h6 ⊢
  exact ⟨h1.2, h2.2, h3.2, h4.2, h5.2, h6.2⟩

/-- The second exponential factor has a rational upper bound. A finite positive
Taylor sum bounds the reciprocal from below, and inversion gives the result. -/
theorem refined_exp_half_neg_le : Real.exp (-(21 / 16 : ℝ)) ≤ 27 / 100 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 21 / 16) 10
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    pow_zero, pow_one] at h
  have hb : (100 / 27 : ℝ) ≤ Real.exp (21 / 16 : ℝ) := by linarith only [h]
  rw [Real.exp_neg, ← one_div]
  have hi := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 100 / 27) hb
  norm_num only at hi ⊢
  exact hi

/-- Simple rational lower bounds for the square roots at the three entrances.
Square each nonnegative endpoint and compare with the corresponding radius. -/
theorem refined_endpoint_sqrts :
    (2284 / 100 : ℝ) ≤ Real.sqrt 522 ∧
      (3957 / 100 : ℝ) ≤ Real.sqrt 1566 ∧ (7224 / 100 : ℝ) ≤ Real.sqrt 5220 := by
  exact
    ⟨Real.le_sqrt_of_sq_le (by norm_num only), Real.le_sqrt_of_sq_le (by norm_num only),
      Real.le_sqrt_of_sq_le (by norm_num only)⟩

/-- A rational expression bounding the residual when the logarithm and negative
power are bounded above and the square root is bounded below. Its inputs are the
radius and those three bounds; it enables exact arithmetic at each entrance. -/
noncomputable def refinedEndpointBound (r u v s : ℝ) : ℝ :=
  (2 * ((500 / 261 : ℝ) * r)) *
          (((27 / 25 : ℝ) ^ 5 / 120) * (588 / 10000) * v * ((21 / 8 : ℝ) + 2 * u) ^ 5) +
        5 * (27 / 25 : ℝ) ^ 5 +
        (((27 / 25 : ℝ) ^ 5 / 120) * (588 / 10000)) * 16 * v *
          (((21 / 8 : ℝ) + 2 * u) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
            (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59)) -
      (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
    5 *
      ((231 / 5000 : ℝ) * (6889 / 2700) +
        ((1839 / 1000 : ℝ) * (2 * u + 21 / 8) + 2) * ((918330048 / 17682025 : ℝ) * (27 / 100)) /
          r) +
    4 * (119 / 1000 : ℝ) * ((231 / 5000 : ℝ) * r + (1839 / 1000 : ℝ) * (2 * u) + 2) / r +
    4 * (9 / 100 : ℝ) * ((231 / 2500 : ℝ) * (7 / 3) / s + (1839 / 1000 : ℝ) / r)

/-- If the radius is at least one, certified logarithm and power upper bounds and
a positive square-root lower bound give the displayed rational residual bound.
Compare each nonnegative product using the supplied bounds and the fixed numerical
bounds for the exponential and kernel weights. -/
theorem refined_residual_le_endpoint_bound {r u v s : ℝ} (hr : 1 ≤ r) (hs : 0 < s)
    (hlog : Real.log r ≤ u) (hp : (r ^ 2) ^ (-(27 / 25 : ℝ)) ≤ v) (hsqrt : s ≤ Real.sqrt r) :
    refinedResidualEnvelope r ≤ refinedEndpointBound r u v s := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hl0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have hu0 : 0 ≤ u := hl0.trans hlog
  have hp0 : 0 ≤ (r ^ 2) ^ (-(27 / 25 : ℝ)) := Real.rpow_nonneg (sq_nonneg r) _
  have hv0 : 0 ≤ v := hp0.trans hp
  have hE := refined_exp_neg_unit_le
  have hE2 := refined_exp_half_neg_le
  have hE20 := (Real.exp_pos (-(21 / 16 : ℝ))).le
  have hW : refinedWeight 1 ≤ (9 / 100 : ℝ) := (le_abs_self _).trans refined_weight_unit_lt.le
  have hD : |refinedWeightDeriv 1| ≤ (119 / 1000 : ℝ) := refined_deriv_unit_lt.le
  have hF0 : 0 ≤ ((21 / 8 : ℝ) + 2 * Real.log r) ^ 5 := by positivity
  have hF :=
    pow_le_pow_left₀ (show (0 : ℝ) ≤ (21 / 8) + 2 * Real.log r by positivity)
      (show (21 / 8 : ℝ) + 2 * Real.log r ≤ 21 / 8 + 2 * u by linarith only [hlog]) 5
  have hEP := mul_le_mul hE hp hp0 (by norm_num only : (0 : ℝ) ≤ 588 / 10000)
  have hEP0 : 0 ≤ (588 / 10000 : ℝ) * v := mul_nonneg (by norm_num only) hv0
  have hEPF := mul_le_mul hEP hF hF0 hEP0
  have hQ0 :
    0 ≤
      (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59) +
        ((21 / 8 : ℝ) + 2 * Real.log r) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) := by
    positivity
  have hQ :=
    add_le_add_right
      (mul_le_mul_of_nonneg_right hF (show (0 : ℝ) ≤ (50 / 29 : ℝ) ^ 2 + 50 / 79 by positivity))
      ((25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59))
  have hEPQ := mul_le_mul hEP hQ hQ0 hEP0
  have hlin0 : 0 ≤ (1839 / 1000 : ℝ) * (2 * Real.log r + 21 / 8) + 2 := by positivity
  have hlin :
    (1839 / 1000 : ℝ) * (2 * Real.log r + 21 / 8) + 2 ≤
      (1839 / 1000 : ℝ) * (2 * u + 21 / 8) + 2 := by
    linarith only [hlog]
  have hlinupper0 : 0 ≤ (1839 / 1000 : ℝ) * (2 * u + 21 / 8) + 2 := hlin0.trans hlin
  have hEE := mul_le_mul hlin hE2 hE20 hlinupper0
  have hder0 : 0 ≤ (231 / 5000 : ℝ) * r + (1839 / 1000 : ℝ) * (2 * Real.log r) + 2 := by positivity
  have hder :
    (231 / 5000 : ℝ) * r + (1839 / 1000 : ℝ) * (2 * Real.log r) + 2 ≤
      (231 / 5000 : ℝ) * r + (1839 / 1000 : ℝ) * (2 * u) + 2 := by
    linarith only [hlog]
  have hDD := mul_le_mul hD hder hder0 (by norm_num only : (0 : ℝ) ≤ 119 / 1000)
  have hss := one_div_le_one_div_of_le hs hsqrt
  have hrest0 : 0 ≤ (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt r + (1839 / 1000 : ℝ) / r := by
    positivity
  have hrest :
    (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt r + (1839 / 1000 : ℝ) / r ≤
      (231 / 2500 : ℝ) * (7 / 3) / s + (1839 / 1000 : ℝ) / r := by
    have hm :=
      mul_le_mul_of_nonneg_left hss (show (0 : ℝ) ≤ (231 / 2500 : ℝ) * (7 / 3) by positivity)
    simp only [div_eq_mul_inv, one_mul] at hm ⊢
    linarith only [hm]
  have hWW := mul_le_mul hW hrest hrest0 (by norm_num only : (0 : ℝ) ≤ 9 / 100)
  have hC :=
    mul_le_mul_of_nonneg_left hEPF
      (show (0 : ℝ) ≤ 2 * (500 / 261 * r) * ((27 / 25 : ℝ) ^ 5 / 120) by positivity)
  have hT :=
    mul_le_mul_of_nonneg_left hEPQ (show (0 : ℝ) ≤ ((27 / 25 : ℝ) ^ 5 / 120) * 16 by positivity)
  have hL :=
    mul_le_mul_of_nonneg_left hEE (show (0 : ℝ) ≤ 5 * (918330048 / 17682025 : ℝ) / r by positivity)
  have hD' := mul_le_mul_of_nonneg_left hDD (show (0 : ℝ) ≤ 4 / r by positivity)
  have hW' := mul_le_mul_of_nonneg_left hWW (show (0 : ℝ) ≤ 4 by norm_num only)
  dsimp only [refinedResidualEnvelope, refinedPaperResidual, refinedEndpointBound]
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv] at hC hT hL hD' hW' ⊢
  nlinarith only [hC, hT, hL, hD', hW']

/-- The residual envelope meets the three piecewise allowances at their entrance
radii. Substitute the certified endpoint inputs into the rational envelope and
verify its three inequalities by exact arithmetic. -/
theorem refined_residual_endpoint_bounds :
    refinedResidualEnvelope 522 ≤ (27 / 25 : ℝ) ^ 5 * 3 ∧
      refinedResidualEnvelope 1566 ≤ (27 / 25 : ℝ) ^ 5 * 1 ∧
      refinedResidualEnvelope 5220 ≤ (27 / 25 : ℝ) ^ 5 * 0 := by
  have h3 :=
    refined_residual_le_endpoint_bound (r := 522) (u := 6258 / 1000) (v := 135 / 100000000) (s :=
      2284 / 100) (by norm_num only) (by norm_num only) refined_endpoint_inputs.1
      refined_endpoint_inputs.2.2.2.1 refined_endpoint_sqrts.1
  have h1 :=
    refined_residual_le_endpoint_bound (r := 1566) (u := 7357 / 1000) (v := 126 / 1000000000) (s :=
      3957 / 100) (by norm_num only) (by norm_num only) refined_endpoint_inputs.2.1
      refined_endpoint_inputs.2.2.2.2.1 refined_endpoint_sqrts.2.1
  have h0 :=
    refined_residual_le_endpoint_bound (r := 5220) (u := 8561 / 1000) (v := 934 / 100000000000)
      (s := 7224 / 100) (by norm_num only) (by norm_num only) refined_endpoint_inputs.2.2.1
      refined_endpoint_inputs.2.2.2.2.2 refined_endpoint_sqrts.2.2
  constructor
  · exact h3.trans (by norm_num only [refinedEndpointBound])
  constructor
  · exact h1.trans (by norm_num only [refinedEndpointBound])
  · exact h0.trans (by norm_num only [refinedEndpointBound])

/-- For `L ≥ 1000`, the residual at the selected root satisfies its piecewise
allowance. Combine the three certified endpoint inequalities with the decreasing
envelope; no numerical residual hypothesis remains. -/
theorem refined_selected_residual_certified {L : ℝ} (hL : 1000 ≤ L) :
    refinedPaperResidual L (refinedPaperRoot L (refinedPaperAllowance L) ^ 2) ≤
      (27 / 25 : ℝ) ^ 5 * refinedPaperAllowance L := by
  exact
    refined_selected_residual_of_three hL refined_residual_endpoint_bounds.1
      refined_residual_endpoint_bounds.2.1 refined_residual_endpoint_bounds.2.2

/-- Under GRH, a uniform three-prime Korselt product with logarithm at least `1000`
has a rejecting prime within the piecewise paper bound. The certified residual
at the selected root discharges the sole numerical hypothesis of the witness theorem. -/
theorem refined_pair_certified_witness {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : 1000 ≤ Real.log n) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ refinedPaperCoefficient (Real.log n) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    refined_pair_piecewise_witness hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK
      hrK hvq hvr hL
  exact refined_selected_residual_certified hL

/-- Under GRH, every odd uniform Korselt triple with logarithm at least `1000`
has a rejecting prime within the piecewise paper bound. Extract its three distinct
prime factors and apply the certified three-prime witness theorem. -/
theorem refined_uniform_certified_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 1000 ≤ Real.log n) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ refinedPaperCoefficient (Real.log n) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hu.2.1
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hpD := (Nat.mem_primeFactors.mp hpMem).2.1
  have hqD := (Nat.mem_primeFactors.mp hqMem).2.1
  have hrD := (Nat.mem_primeFactors.mp hrMem).2.1
  have hprod := (Nat.prod_primeFactors_of_squarefree hu.1).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
  have hpO := Odd.of_dvd_nat ho hpD
  have hqO := Odd.of_dvd_nat ho hqD
  have hrO := Odd.of_dvd_nat ho hrD
  have hp2 : p ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hpO)
  have hq2 : q ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hqO)
  have hr2 : r ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hrO)
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm hq2)⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm hr2)⟩
  have hpqD : p * q ∣ n := ⟨r, hnprod⟩
  have hprD : p * r ∣ n := ⟨q, hnprod.trans (by ac_rfl)⟩
  have hqrD : q * r ∣ n := ⟨p, hnprod.trans (by ac_rfl)⟩
  exact
    refined_pair_certified_witness hu.1 hnprod hGRH hn ho hpO hqO hrO hpD hqD hrD hpqD hprD hqrD
      (hu.2.2.1 p hp hpD) (hu.2.2.1 q hq hqD) (hu.2.2.1 r hr hrD) (hu.2.2.2 q p hq hp hqD hpD)
      (hu.2.2.2 r p hr hp hrD hpD) hL

/-- Above the first entrance the piecewise cutoff is at least one quarter of
`L²`. Square the lower bound for the selected root and compare the rational
coefficient with one quarter. This accommodates existing four-factor witnesses. -/
theorem refined_piecewise_quarter_lower {L : ℝ} (hL : 1000 ≤ L) :
    (1 / 4 : ℝ) * L ^ 2 ≤ refinedPaperCoefficient L * L ^ 2 := by
  rw [refined_piecewise_high hL, refinedPaperBound]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hroot := refined_root_lower hL0 (refined_allowance_range L).1
  have hs := pow_le_pow_left₀ (show (0 : ℝ) ≤ (261 / 500 : ℝ) * L by positivity) hroot 2
  have hid :
    (refinedPaperRoot L (refinedPaperAllowance L) ^ 2) ^ 2 =
      refinedPaperRoot L (refinedPaperAllowance L) ^ 4 := by
    ring
  rw [hid] at hs
  nlinarith only [hs, sq_nonneg L]

/-- Under GRH, an odd composite with at least four prime factors counted with
multiplicity and logarithm at least `1000` has a witness within the piecewise
cutoff. The existing total-factor estimate is at most one quarter of `L²`,
which the selected paper cutoff dominates. -/
theorem refined_four_factors_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hk : 4 ≤ ArithmeticFunction.cardFactors n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_cardFactors_log_sq hn ho hc hGRH
  have hkR : (4 : ℝ) ≤ ArithmeticFunction.cardFactors n := by exact_mod_cast hk
  have hden : (16 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by nlinarith only [hkR]
  have hcoef : (4 : ℝ) / (ArithmeticFunction.cardFactors n : ℝ) ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ (by linarith only [hden])).2
    nlinarith only [hden]
  exact
    ⟨p, hp,
      (hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))).trans
        (refined_piecewise_quarter_lower hL),
      hf⟩

/-- Under GRH, an odd input with at least three distinct prime factors has a
piecewise-bound witness if a factor fails the Korselt condition or two predecessor
valuations differ. Its local-factor coefficient is at most one quarter. -/
theorem refined_local_factor_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : 3 ≤ n.primeFactors.card)
    (hlocal :
      (∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1)) ∨
        ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hf, hb, _⟩ := exists_leastWitness_le_local_factor_coefficient hn ho hc hlocal hGRH
  have hcR : (3 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast hc
  have hden : (16 : ℝ) ≤ ((n.primeFactors.card : ℝ) + 1) ^ 2 := by nlinarith only [hcR]
  have hcoef : (4 : ℝ) / ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ (by linarith only [hden])).2
    nlinarith only [hden]
  exact
    ⟨p, hp,
      (hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))).trans
        (refined_piecewise_quarter_lower hL),
      hf⟩

/-- Under GRH, every odd squarefree input with exactly three prime factors and
logarithm at least `1000` has a witness within the piecewise cutoff. The uniform
case uses the certified pair-character estimate; the other case uses a local factor. -/
theorem refined_three_factors_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 1000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  classical
  by_cases hu : UniformKorseltTriple n
  · exact refined_uniform_certified_witness hn ho hu hGRH hL
  · have hlocal :
      (∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1)) ∨
        ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1 := by
      by_contra h
      have hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
        intro p hp hd
        by_contra hbad
        exact h (Or.inr ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hd, Nat.ne_zero_of_lt hn⟩, hbad⟩)
      have hV :
        ∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1) := by
        intro p q hp hq hpd hqd
        have hpm := Nat.mem_primeFactors.mpr ⟨hp, hpd, Nat.ne_zero_of_lt hn⟩
        have hqm := Nat.mem_primeFactors.mpr ⟨hq, hqd, Nat.ne_zero_of_lt hn⟩
        apply le_antisymm
        · exact Nat.le_of_not_gt (fun hv ↦ h (Or.inl ⟨p, hpm, q, hqm, hv⟩))
        · exact Nat.le_of_not_gt (fun hv ↦ h (Or.inl ⟨q, hqm, p, hpm, hv⟩))
      exact hu ⟨hsf, hc, hK, hV⟩
    exact refined_local_factor_witness hn ho hc.ge hlocal hGRH hL

/-- Above `1000`, the selected cutoff dominates the square of `(261/500)L`.
Square the certified lower bound for the positive root; this radius comparison
allows the local subgroup witnesses to be compared directly with the paper bound. -/
theorem refined_piecewise_radius_lower {L : ℝ} (hL : 1000 ≤ L) :
    ((261 / 500 : ℝ) * L) ^ 2 ≤ refinedPaperCoefficient L * L ^ 2 := by
  rw [refined_piecewise_high hL, refinedPaperBound]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hroot := refined_root_lower hL0 (refined_allowance_range L).1
  have hs := pow_le_pow_left₀ (show (0 : ℝ) ≤ (261 / 500 : ℝ) * L by positivity) hroot 2
  simpa only [← pow_mul, Nat.reduceMul] using hs

/-- Under GRH, a proper local subgroup at a divisor whose square is at most
`10^9 * n` gives a piecewise-bound witness when `log n ≥ 1000`. The certified
radius-48 local correction is bounded by `(261/500) log n`, which is no larger
than the square root of the selected paper cutoff. -/
theorem refined_local_subgroup_witness {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n) (hq : 0 < q)
    (hqn : q ∣ n) (hsize : q ^ 2 ≤ 10 ^ 9 * n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hm : ((48 : ℚ), (579107 / 100000 : ℚ), 6) ∈ localEvenAnchors := by decide +kernel
  have hs := local_log_le_of_square_le (Nat.zero_lt_of_lt hn) hq hsize
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_reject_of_local_anchor hn ho hqn H hH hpass hGRH hm hs
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  have h10 := log_ten_lt_seven_thirds
  have hmax :
    max (48 : ℝ) ((Real.log n + 9 * Real.log 10) / 2 - 579107 / 100000) ≤
      (261 / 500 : ℝ) * Real.log n := by
    apply max_le
    · linarith only [hL]
    · linarith only [hL, h10]
  have hnonneg : 0 ≤ max (48 : ℝ) ((Real.log n + 9 * Real.log 10) / 2 - 579107 / 100000) :=
    le_trans (by norm_num only) (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hnonneg hmax
  have hfinal :
    (max (48 : ℝ) ((Real.log n + 9 * Real.log 10) / 2 - 579107 / 100000)) ^ 2 ≤
      ((261 / 500 : ℝ) * Real.log n) ^ 2 := by
    nlinarith only [hsquare]
  exact ⟨p, hp, (hb.trans hfinal).trans (refined_piecewise_radius_lower hL), hf⟩

/-- Under GRH, every odd composite of logarithmic scale at least `1000` whose
Fermat subgroup has index at most `10^9` has a witness within the piecewise
cutoff. The finite-index classification gives either a proper local subgroup or
a uniform Korselt triple, both covered by the certified bounds. -/
theorem refined_low_index_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 1000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have hJ : (1 : ℕ) ≤ 10 ^ 9 := by norm_num only
  have hJ3 : (10 ^ 9 : ℕ) ^ 3 ≤ n := by
    norm_num only [show (10 ^ 9 : ℕ) ^ 3 = 10 ^ 27 by norm_num only]
    exact ten_pow_27_le_of_log100 (by linarith only [hL])
  rcases
    localSubgroup_or_uniformKorseltTriple hn ho hc (PrimeTest.fermatSubgroup n) le_rfl hJ hJ3
      hi with
    hlocal | htriple
  · obtain ⟨q, hq, hqn, hsize, K, hproper, hpass⟩ := hlocal
    let : NeZero q := ⟨Nat.ne_zero_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    exact
      refined_local_subgroup_witness hn ho (lt_of_lt_of_le (by decide : 0 < 2) hq) hqn hsize K
        hproper hpass hGRH hL
  · exact refined_uniform_certified_witness hn ho htriple hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
