/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighFactorialRepeated

/-! # Gaussian scale for the factorial coefficient -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Gaussian argument whose `21 / 10` cutoff equals the squared factorial coefficient times
`L ^ 2`. It is used for the index-four branch of the factorial high-range bound. -/
noncomputable def factorialGaussianScale (L : ℝ) : ℝ :=
  (10 / 21 : ℝ) * (factorialAlpha (2 * Real.log L)) ^ 2 * L ^ 2

/-- At `L ≥ 80000`, the square root of the factorial Gaussian scale is at least `223 * L / 500`.
The coefficient lower bound reduces the estimate to a rational square inequality. -/
theorem factorialGaussian_sqrt_lower {L : ℝ} (hL : 80000 ≤ L) :
    (223 / 500 : ℝ) * L ≤ Real.sqrt (factorialGaussianScale L) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hα := (factorialAlpha_bounds (high_log_twice_ge_22 (by linarith only [hL]))).1
  have hαL := mul_le_mul_of_nonneg_right hα hL0
  have hs := pow_le_pow_left₀ (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 647 / 1000) hL0) hαL 2
  have hx : 0 ≤ factorialGaussianScale L := by
    dsimp only [factorialGaussianScale]
    exact mul_nonneg (mul_nonneg (by norm_num only) (sq_nonneg _)) (sq_nonneg _)
  apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0) hx).mpr
  dsimp only [factorialGaussianScale]
  nlinarith only [hs]

/-- At `L ≥ 80000`, the square root of the factorial Gaussian scale is at most `289 * L / 625`.
This upper bound controls the fourth-root error term. -/
theorem factorialGaussian_sqrt_upper {L : ℝ} (hL : 80000 ≤ L) :
    Real.sqrt (factorialGaussianScale L) ≤ (289 / 625 : ℝ) * L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hα := (factorialAlpha_bounds (high_log_twice_ge_22 (by linarith only [hL]))).2
  have hα0 : 0 ≤ factorialAlpha (2 * Real.log L) := by
    have hh := (factorialAlpha_bounds (high_log_twice_ge_22 (by linarith only [hL]))).1
    linarith only [hh]
  have hαL := mul_le_mul_of_nonneg_right hα hL0
  have hs := pow_le_pow_left₀ (mul_nonneg hα0 hL0) hαL 2
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (by norm_num only) hL0
  · dsimp only [factorialGaussianScale]
    nlinarith only [hs]

/-- The factorial Gaussian scale is nonnegative for every real logarithmic parameter, being a
positive rational multiple of two squares. -/
theorem factorialGaussian_nonneg (L : ℝ) : 0 ≤ factorialGaussianScale L := by
  dsimp only [factorialGaussianScale]
  exact mul_nonneg (mul_nonneg (by norm_num only) (sq_nonneg _)) (sq_nonneg _)

/-- For `L ≥ 80000`, the fourth root of the factorial Gaussian scale is at most
`17 * sqrt L / 25`. This follows by square-root monotonicity from the upper scale estimate. -/
theorem factorialGaussian_fourth_le {L : ℝ} (hL : 80000 ≤ L) :
    factorialGaussianScale L ^ (1 / 4 : ℝ) ≤ (17 / 25 : ℝ) * Real.sqrt L := by
  have he :
    factorialGaussianScale L ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt (factorialGaussianScale L)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (factorialGaussian_nonneg L)]
    norm_num only
  rw [he]
  convert Real.sqrt_le_sqrt (factorialGaussian_sqrt_upper hL) using 1
  norm_num only [Real.sqrt_mul, Real.sqrt_div]

/-- At `L ≥ 80000`, the factorial Gaussian scale is at least `3 ^ 16`, allowing use of the
left-moment decay estimate in the Gaussian comparison. -/
theorem factorialGaussian_ge_three_pow {L : ℝ} (hL : 80000 ≤ L) :
    (3 : ℝ) ^ 16 ≤ factorialGaussianScale L := by
  have hs := factorialGaussian_sqrt_lower hL
  have hsq := Real.sq_sqrt (factorialGaussian_nonneg L)
  have hp := Real.sqrt_nonneg (factorialGaussianScale L)
  nlinarith only [hL, hs, hsq, hp, sq_nonneg (Real.sqrt (factorialGaussianScale L) - 223 * L / 500)]

/-- At `L ≥ 80000`, the factorial Gaussian scale satisfies the strict index-four main-term
budget whenever the ambient error is at most 30. The square- and fourth-root bounds leave a
positive rational margin at the entrance. -/
theorem factorialGaussian_budget {L E : ℝ} (hL : 80000 ≤ L) (hE : E ≤ 30) :
    (161 / 200 : ℝ) * L + 70 * factorialGaussianScale L ^ (1 / 4 : ℝ) + 3 * E <
      (21943 / 10000 : ℝ) * Real.sqrt (factorialGaussianScale L) := by
  have hs : Real.sqrt L ≤ L / 280 := by
    nlinarith only [Real.sq_sqrt (show 0 ≤ L by linarith only [hL]), Real.sqrt_nonneg L, hL]
  have hr := factorialGaussian_sqrt_lower hL
  have hfour := factorialGaussian_fourth_le hL
  linarith only [hL, hE, hs, hr, hfour]

/-- For `L ≥ 80000` and `log q ≤ L`, the Gaussian ambient error at the factorial scale is at
most 30. The square-root bound controls both the pole and left-moment terms. -/
theorem factorialGaussian_ambient_error {q : ℕ} {L : ℝ} (hL : 80000 ≤ L) (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianAmbientError q (factorialGaussianScale L) ≤ 30 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hs := factorialGaussian_sqrt_lower hL
  have hs0 : 0 < Real.sqrt (factorialGaussianScale L) :=
    (mul_pos (by norm_num only : (0 : ℝ) < 223 / 500) hL0).trans_le hs
  have hP :
    (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / Real.sqrt (factorialGaussianScale L)) ≤
      4 := by
    rw [← mul_div_assoc, div_le_iff₀ hs0]
    linarith only [hL, hq, hs]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_three_sqrt
      (factorialGaussian_ge_three_pow hL)
  have hC : 0 ≤ (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) := by
    linarith only [Real.log_natCast_nonneg q]
  have hb := mul_le_mul_of_nonneg_left hdec hC
  have hB :
    (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) /
        (3 * Real.sqrt (factorialGaussianScale L)) ≤
      4 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 3) hs0)).mpr
    linarith only [hL, hq, hs]
  have hJ :
    (11 / 10 : ℝ) * factorialGaussianScale L ^ (-9 / 16 : ℝ) *
        ((16 / 5) * (Real.log q + 283) + 5 / 3) ≤
      4 := by
    simp only [div_eq_mul_inv] at hb hB ⊢
    nlinarith only [hb, hB]
  dsimp only [LLS.PaperStatements.gaussianAmbientError]
  linarith only [hP, hJ]

/-- The index-four Gaussian comparison at the factorial scale contradicts the strict budget.
The conductor sum, certified kernel lower bound, and ambient error supply the opposing bounds. -/
private theorem factorial_indexFour_contradiction {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : H.index = 4) (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hL : 80000 ≤ Real.log n)
    (hcmp :
      ((H.index : ℝ) *
              (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt (factorialGaussianScale (Real.log n)) ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          14 * ((H.index : ℝ) + 1) * factorialGaussianScale (Real.log n) ^ (1 / 4 : ℝ) +
          ((H.index - 1 : ℕ) : ℝ) *
            LLS.PaperStatements.gaussianAmbientError n (factorialGaussianScale (Real.log n))) :
    False := by
  rw [hi] at hcmp
  norm_num only [Nat.cast_ofNat] at hcmp
  have hd := LLS.gaussian_tripleDenominator_fixedCutoff
  have hd' :
    (21943 / 10000 : ℝ) ≤
      4 *
          (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
            (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
        (LLS.PaperStatements.gaussianGammaMellinKernel.function (1 / 2)).re := by
    exact (by norm_num only : (21943 / 10000 : ℝ) ≤ 10971611 / 5000000).trans hd
  have he :
    (LLS.PaperStatements.gaussianGammaMellinKernel.function (1 / 2)).re = Real.exp (1 / 16 : ℝ) :=
    Analysis.gaussianGammaFunction_endpoint
  rw [he] at hd'
  have hm := mul_le_mul_of_nonneg_right hd' (Real.sqrt_nonneg (factorialGaussianScale (Real.log n)))
  have hc := mul_le_mul_of_nonneg_left hC (by norm_num only : (0 : ℝ) ≤ 161 / 400)
  have hE := factorialGaussian_ambient_error hL (le_refl (Real.log n))
  have hs := factorialGaussian_budget hL hE
  linarith only [hcmp, hm, hc, hs]

/-- Under GRH, an index-four subgroup containing all strong passes gives a rejecting prime within
the factorial bound. The Gaussian comparison at the selected scale contradicts the strict budget. -/
theorem factorial_indexFour_witness {n : ℕ} [NeZero n] (hnlarge : 20000 ≤ n) (hnOdd : Odd n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hL : 80000 ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (factorialAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  classical
  by_contra hnone
  have hx : 4 ≤ factorialGaussianScale (Real.log n) :=
    (by norm_num only : (4 : ℝ) ≤ 3 ^ 16).trans (factorialGaussian_ge_three_pow hL)
  have hcut :
    (21 / 10 : ℝ) * factorialGaussianScale (Real.log n) =
      (factorialAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 := by
    dsimp only [factorialGaussianScale]
    ring
  have hpass :
    ∀ r : ℕ,
      r.Prime →
        (r : ℝ) ≤ (21 / 10 : ℝ) * factorialGaussianScale (Real.log n) →
        PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
    intro r hr hb
    rw [hcut] at hb
    by_contra hfail
    exact hnone ⟨r, hr, hb, hfail⟩
  have hcmp :=
    gaussian_inequality_of_prime_passes_in_subgroup hnlarge hnOdd H hHpass hGRH hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hpass
  exact factorial_indexFour_contradiction H hi hC hL hcmp

/-- Under GRH, a Korselt product of three distinct odd primes with matching predecessor valuations
has a rejecting prime within the factorial bound. Its index-four subgroup supplies the input. -/
theorem factorial_threeKorselt_witness {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1) (hrdiv : r - 1 ∣ n - 1)
    (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 80000 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (factorialAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hnOdd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hu := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (NeZero.pos n) : (0 : ℝ) < n)
  have hnlarge : 20000 ≤ n := by
    apply Nat.cast_le (α := ℝ).mp
    norm_num only [Nat.cast_ofNat]
    linarith only [hL, hu]
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr hpOdd hqOdd hrOdd hpq hpr hqr hn hpdiv
      hqdiv hrdiv hpv hprv
  exact factorial_indexFour_witness hnlarge hnOdd H hi hpass hGRH hC.le hL

/-- Under GRH, a squarefree odd input with three prime factors and `log n ≥ 80000` has a
rejecting prime within the factorial bound. Local factor bounds handle the non-Korselt and mixed
valuation cases; the index-four Gaussian comparison handles the remaining case. -/
theorem factorial_squarefreeThree_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hsf : Squarefree n)
    (hcard : n.primeFactors.card = 3) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (80000 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (factorialAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hc : 3 ≤ n.primeFactors.card := hcard.ge
  by_cases hlocal :
    (∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1)) ∨
      ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1
  · obtain ⟨r, hr, hf, hb, _⟩ :=
      exists_leastWitness_le_local_factor_coefficient hn ho hc hlocal hGRH
    have hα := (factorialAlpha_bounds (high_log_twice_ge_22 (by linarith only [hL]))).1
    have hcoeff :
      (4 : ℝ) / ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤
        (factorialAlpha (2 * Real.log (Real.log n))) ^ 2 := by
      rw [hcard]
      norm_num only [Nat.cast_ofNat]
      nlinarith only [hα, sq_nonneg (factorialAlpha (2 * Real.log (Real.log n)) - 647 / 1000)]
    exact ⟨r, hr, hb.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)), hf⟩
  · have hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
      intro p hp hpn
      by_contra hbad
      apply hlocal
      right
      exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpn, Nat.ne_zero_of_lt hn⟩, hbad⟩
    have hU :
      ∀ p q : ℕ,
        p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1) := by
      intro p q hp hq hpn hqn
      by_contra hne
      have hpMem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, Nat.ne_zero_of_lt hn⟩
      have hqMem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, Nat.ne_zero_of_lt hn⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hlocal (Or.inl ⟨q, hqMem, p, hpMem, hlt⟩)
      · exact hlocal (Or.inl ⟨p, hpMem, q, hqMem, hgt⟩)
    obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hcard
    have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
    have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
    have hrMem : r ∈ n.primeFactors :=
      hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
    have hp := (Nat.mem_primeFactors.mp hpMem).1
    have hq := (Nat.mem_primeFactors.mp hqMem).1
    have hr := (Nat.mem_primeFactors.mp hrMem).1
    have hpn := (Nat.mem_primeFactors.mp hpMem).2.1
    have hqn := (Nat.mem_primeFactors.mp hqMem).2.1
    have hrn := (Nat.mem_primeFactors.mp hrMem).2.1
    have hprod := (Nat.prod_primeFactors_of_squarefree hsf).symm
    rw [hset] at hprod
    have hnprod : n = p * q * r := by
      simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert,
        Finset.mem_singleton, hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
    exact
      factorial_threeKorselt_witness hp hq hr (hp.odd_of_ne_two (ho.ne_two_of_dvd_nat hpn))
        (hq.odd_of_ne_two (ho.ne_two_of_dvd_nat hqn)) (hr.odd_of_ne_two (ho.ne_two_of_dvd_nat hrn))
        hpq hpr hqr hnprod (hK p hp hpn) (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn)
        (hU p r hp hr hpn hrn) hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
