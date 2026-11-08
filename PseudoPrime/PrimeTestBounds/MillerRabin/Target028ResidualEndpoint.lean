/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ResidualMonotone
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEndpoints

/-! # Rational certificate for the 0.28 high-range residual -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational expression bounding the residual when the logarithm and negative
power are bounded above and the square root is bounded below. Its inputs are the
radius and those three bounds; it enables exact arithmetic at each entrance. -/
noncomputable def target028EndpointBound (r u v s : ℝ) : ℝ :=
  (2 * ((1000 / 529 : ℝ) * r)) *
          (((27 / 25 : ℝ) ^ 5 / 120) * (588 / 10000) * v * ((21 / 8 : ℝ) + 2 * u) ^ 5) +
        (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
        (((27 / 25 : ℝ) ^ 5 / 120) * (588 / 10000)) * 16 * v *
          (((21 / 8 : ℝ) + 2 * u) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
            (100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27)) -
      (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
    5 *
      ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
        ((1839 / 1000 : ℝ) * (2 * u + 21 / 8) + 2) * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) / r) +
    4 * (119 / 1000 : ℝ) * ((231 / 5000 : ℝ) * r + (1839 / 1000 : ℝ) * (2 * u) + 2) / r +
    4 * (9 / 100 : ℝ) * ((231 / 2500 : ℝ) * (7 / 3) / s + (1839 / 1000 : ℝ) / r)

/-- If the radius is at least one, certified logarithm and power upper bounds and
a positive square-root lower bound give the displayed rational residual bound.
Compare each nonnegative product using the supplied bounds and the fixed numerical
bounds for the exponential and kernel weights. -/
theorem target028_residual_le_endpoint_bound {r u v s : ℝ} (hr : 1 ≤ r) (hs : 0 < s)
    (hlog : Real.log r ≤ u) (hp : (r ^ 2) ^ (-(27 / 25 : ℝ)) ≤ v) (hsqrt : s ≤ Real.sqrt r) :
    target028ResidualEnvelope r ≤ target028EndpointBound r u v s := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hl0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have hu0 : 0 ≤ u := hl0.trans hlog
  have hp0 : 0 ≤ (r ^ 2) ^ (-(27 / 25 : ℝ)) := Real.rpow_nonneg (sq_nonneg r) _
  have hv0 : 0 ≤ v := hp0.trans hp
  have hE := refined_exp_neg_unit_le
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
      (100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27) +
        ((21 / 8 : ℝ) + 2 * Real.log r) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) := by
    positivity
  have hQ :=
    add_le_add_right
      (mul_le_mul_of_nonneg_right hF (show (0 : ℝ) ≤ (50 / 29 : ℝ) ^ 2 + 50 / 79 by positivity))
      ((100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27))
  have hEPQ := mul_le_mul hEP hQ hQ0 hEP0
  have hlin0 : 0 ≤ (1839 / 1000 : ℝ) * (2 * Real.log r + 21 / 8) + 2 := by positivity
  have hlin :
    (1839 / 1000 : ℝ) * (2 * Real.log r + 21 / 8) + 2 ≤
      (1839 / 1000 : ℝ) * (2 * u + 21 / 8) + 2 := by
    linarith only [hlog]
  have hlinupper0 : 0 ≤ (1839 / 1000 : ℝ) * (2 * u + 21 / 8) + 2 := hlin0.trans hlin
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
      (show (0 : ℝ) ≤ 2 * (1000 / 529 * r) * ((27 / 25 : ℝ) ^ 5 / 120) by positivity)
  have hT :=
    mul_le_mul_of_nonneg_left hEPQ (show (0 : ℝ) ≤ ((27 / 25 : ℝ) ^ 5 / 120) * 16 by positivity)
  have hL :=
    mul_le_mul_of_nonneg_left hlin
      (show (0 : ℝ) ≤ 5 * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) / r by positivity)
  have hD' := mul_le_mul_of_nonneg_left hDD (show (0 : ℝ) ≤ 4 / r by positivity)
  have hW' := mul_le_mul_of_nonneg_left hWW (show (0 : ℝ) ≤ 4 by norm_num only)
  dsimp only [target028ResidualEnvelope, target028PaperResidual, target028EndpointBound]
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv] at hC hT hL hD' hW' ⊢
  nlinarith only [hC, hT, hL, hD', hW']

/-- Exact rational certificates enclose the logarithm and negative power at
the high-range entrance. They are interpreted by the analytic soundness lemmas. -/
theorem target028_residual_endpoint_checks :
    Analysis.rationalLogIntervalCheck (529 / 10) 6 32 0 (397 / 100) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck ((529 / 10) ^ 2) 0 (191 / 1000000)
          27 25 =
        true := by
  decide +kernel

/-- The residual envelope at the paper's high-range entrance is at most
negative three halves times the kernel normalization. Exact rational interval
checks bound the logarithm, real power and square root. -/
theorem target028_residual_endpoint :
    target028ResidualEnvelope (529 / 10) ≤ -(3 / 2 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have hl := Analysis.rationalLogIntervalCheck_sound target028_residual_endpoint_checks.1
  have hp :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      target028_residual_endpoint_checks.2
  have hs : (727 / 100 : ℝ) ≤ Real.sqrt (529 / 10 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num only)
  norm_num only at hl hp
  have hp' : ((529 / 10 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ 191 / 1000000 := by
    norm_num only
    exact hp.2
  have h :=
    target028_residual_le_endpoint_bound (r := 529 / 10) (u := 397 / 100) (v := 191 / 1000000) (s :=
      727 / 100) (by norm_num only) (by norm_num only) hl.2 hp' hs
  have hc :
    target028EndpointBound (529 / 10) (397 / 100) (191 / 1000000) (727 / 100) ≤
      -(3 / 2 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
    norm_num only [target028EndpointBound]
  exact h.trans hc

/-- For every high-range radius and logarithmic scale satisfying the paper's
linear relation, the residual is bounded by negative three halves times the
kernel normalization. Antitonicity reduces the estimate to the certified entrance. -/
theorem target028_high_residual_bound {L R : ℝ} (hR : (529 / 10 : ℝ) ≤ R)
    (hLR : (529 / 1000 : ℝ) * L ≤ R) :
    target028PaperResidual L R ≤ -(3 / 2 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h := target028_residual_le_envelope hR hLR
  have ha := target028_residual_antitone (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hR) hR
  exact h.trans (ha.trans target028_residual_endpoint)

/-- Under GRH, every uniform three-prime Korselt product with logarithm at
least 100 has a rejecting prime within the 0.28 cutoff. The rational endpoint
certificate removes the residual hypothesis from the scalar witness theorem. -/
theorem target028_high_pair_witness {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (100 : ℝ) ≤ Real.log n) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hL0 : 0 ≤ Real.log n := by linarith only [hL]
  have hs : (529 / 1000 : ℝ) ≤ Real.sqrt (7 / 25 : ℝ) := by
    apply (Real.le_sqrt (by norm_num only) (by norm_num only)).2
    norm_num only
  have hLR : (529 / 1000 : ℝ) * Real.log n ≤ Real.sqrt (7 / 25 : ℝ) * Real.log n :=
    mul_le_mul_of_nonneg_right hs hL0
  have hR : (529 / 10 : ℝ) ≤ Real.sqrt (7 / 25 : ℝ) * Real.log n := by linarith only [hLR, hL]
  exact
    target028_high_pair_witness_of_residual hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn
      hqrn hpK hqK hrK hvq hvr hL (target028_high_residual_bound hR hLR)

/-- Under GRH, every odd uniform Korselt triple with logarithm at least `100`
has a rejecting prime within the 0.28 cutoff. Extract its three distinct
prime factors and apply the certified three-prime witness theorem. -/
theorem target028_uniform_high_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (100 : ℝ) ≤ Real.log n) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
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
    target028_high_pair_witness hu.1 hnprod hGRH hn ho hpO hqO hrO hpD hqD hrD hpqD hprD hqrD
      (hu.2.2.1 p hp hpD) (hu.2.2.1 q hq hqD) (hu.2.2.1 r hr hrD) (hu.2.2.2 q p hq hp hqD hpD)
      (hu.2.2.2 r p hr hp hrD hpD) hL

end PseudoPrime.PrimeTestBounds.MillerRabin
