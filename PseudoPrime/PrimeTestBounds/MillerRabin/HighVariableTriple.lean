/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighVariableCoefficient
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighCoefficientTriple
public import PseudoPrime.PrimeTestBounds.MillerRabin.MixedTwoAdicLogBounds

/-! # Gaussian scale for the variable paired-prime coefficient -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Gaussian argument whose `21 / 10` cutoff equals the squared paired coefficient times
`L ^ 2`. It is used in the index-four branch of the variable high-range witness bound. -/
noncomputable def pairedGaussianScale (L : ℝ) : ℝ :=
  (10 / 21 : ℝ) * (pairedAlpha (2 * Real.log L)) ^ 2 * L ^ 2

/-- At `L ≥ 70000`, the Gaussian scale has square root at least `901 * L / 2000`. The lower
bound on the paired coefficient reduces the comparison to a rational square inequality. -/
theorem pairedGaussian_sqrt_lower {L : ℝ} (hL : 70000 ≤ L) :
    (901 / 2000 : ℝ) * L ≤ Real.sqrt (pairedGaussianScale L) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hα := pairedAlpha_ge_653 (high_log_twice_ge_22 hL)
  have hαL := mul_le_mul_of_nonneg_right hα hL0
  have hs := pow_le_pow_left₀ (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 653 / 1000) hL0) hαL 2
  have hx : 0 ≤ pairedGaussianScale L := by
    dsimp only [pairedGaussianScale]
    exact mul_nonneg (mul_nonneg (by norm_num only) (sq_nonneg _)) (sq_nonneg _)
  apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0) hx).mpr
  dsimp only [pairedGaussianScale]
  nlinarith only [hs]

/-- At `L ≥ 70000`, the square root of the Gaussian scale is at most `289 * L / 625`.
The upper bound on the coefficient supplies the fourth-root error estimate. -/
theorem pairedGaussian_sqrt_upper {L : ℝ} (hL : 70000 ≤ L) :
    Real.sqrt (pairedGaussianScale L) ≤ (289 / 625 : ℝ) * L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hα := (pairedAlpha_bounds (high_log_twice_ge_22 hL)).2
  have hα0 : 0 ≤ pairedAlpha (2 * Real.log L) := by
    have hh := pairedAlpha_ge_653 (high_log_twice_ge_22 hL)
    linarith only [hh]
  have hαL := mul_le_mul_of_nonneg_right hα hL0
  have hs := pow_le_pow_left₀ (mul_nonneg hα0 hL0) hαL 2
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (by norm_num only) hL0
  · dsimp only [pairedGaussianScale]
    nlinarith only [hs]

/-- The paired Gaussian scale is nonnegative for every real logarithmic parameter because it
is a positive rational multiple of two squares. This supports its square- and fourth-root bounds. -/
theorem pairedGaussian_nonneg (L : ℝ) : 0 ≤ pairedGaussianScale L := by
  dsimp only [pairedGaussianScale]
  exact mul_nonneg (mul_nonneg (by norm_num only) (sq_nonneg _)) (sq_nonneg _)

/-- For `L ≥ 70000`, the fourth root of the paired Gaussian scale is at most `17 * sqrt L / 25`.
Apply square-root monotonicity to the upper square-root estimate. -/
theorem pairedGaussian_fourth_le {L : ℝ} (hL : 70000 ≤ L) :
    pairedGaussianScale L ^ (1 / 4 : ℝ) ≤ (17 / 25 : ℝ) * Real.sqrt L := by
  have he :
    pairedGaussianScale L ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt (pairedGaussianScale L)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (pairedGaussian_nonneg L)]
    norm_num only
  rw [he]
  convert Real.sqrt_le_sqrt (pairedGaussian_sqrt_upper hL) using 1
  norm_num only [Real.sqrt_mul, Real.sqrt_div]

/-- The paired Gaussian scale is at least `3 ^ 16` throughout the high range. Its square-root
lower bound clears the threshold needed by the ambient-error decay estimate. -/
theorem pairedGaussian_ge_three_pow {L : ℝ} (hL : 70000 ≤ L) :
    (3 : ℝ) ^ 16 ≤ pairedGaussianScale L := by
  have hs := pairedGaussian_sqrt_lower hL
  have hsq := Real.sq_sqrt (pairedGaussian_nonneg L)
  have hp := Real.sqrt_nonneg (pairedGaussianScale L)
  nlinarith only [hL, hs, hsq, hp, sq_nonneg (Real.sqrt (pairedGaussianScale L) - 901 * L / 2000)]

/-- At `L ≥ 70000`, the square-root and fourth-root estimates give a strict Gaussian main-term
budget when the ambient error is at most 30. The rational margin remains positive at the
smallest allowed logarithmic scale. -/
theorem pairedGaussian_budget {L E : ℝ} (hL : 70000 ≤ L) (hE : E ≤ 30) :
    (161 / 200 : ℝ) * L + 70 * pairedGaussianScale L ^ (1 / 4 : ℝ) + 3 * E <
      (21943 / 10000 : ℝ) * Real.sqrt (pairedGaussianScale L) := by
  have hs : Real.sqrt L ≤ L / 264 := by
    nlinarith only [Real.sq_sqrt (show 0 ≤ L by linarith only [hL]), Real.sqrt_nonneg L, hL]
  have hr := pairedGaussian_sqrt_lower hL
  have hfour := pairedGaussian_fourth_le hL
  linarith only [hL, hE, hs, hr, hfour]

/-- For `L ≥ 70000` and `log q ≤ L`, the Gaussian ambient error at the paired scale is at most
30. The lower square-root bound controls the pole term and the left-moment decay estimate. -/
theorem pairedGaussian_ambient_error {q : ℕ} {L : ℝ} (hL : 70000 ≤ L) (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianAmbientError q (pairedGaussianScale L) ≤ 30 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hs := pairedGaussian_sqrt_lower hL
  have hs0 : 0 < Real.sqrt (pairedGaussianScale L) :=
    (mul_pos (by norm_num only : (0 : ℝ) < 901 / 2000) hL0).trans_le hs
  have hP :
    (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / Real.sqrt (pairedGaussianScale L)) ≤ 4 := by
    rw [← mul_div_assoc, div_le_iff₀ hs0]
    linarith only [hL, hq, hs]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_three_sqrt (pairedGaussian_ge_three_pow hL)
  have hC : 0 ≤ (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) := by
    linarith only [Real.log_natCast_nonneg q]
  have hb := mul_le_mul_of_nonneg_left hdec hC
  have hB :
    (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) /
        (3 * Real.sqrt (pairedGaussianScale L)) ≤
      4 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 3) hs0)).mpr
    linarith only [hL, hq, hs]
  have hJ :
    (11 / 10 : ℝ) * pairedGaussianScale L ^ (-9 / 16 : ℝ) *
        ((16 / 5) * (Real.log q + 283) + 5 / 3) ≤
      4 := by
    simp only [div_eq_mul_inv] at hb hB ⊢
    nlinarith only [hb, hB]
  dsimp only [LLS.PaperStatements.gaussianAmbientError]
  linarith only [hP, hJ]

/-- The index-four Gaussian comparison contradicts the paired-scale budget when the conductor
logarithm sum is at most twice `log n`. The certified kernel lower bound and the ambient error
estimate provide the strict opposite inequality. -/
private theorem paired_indexFour_contradiction {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : H.index = 4) (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hL : 70000 ≤ Real.log n)
    (hcmp :
      ((H.index : ℝ) *
              (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt (pairedGaussianScale (Real.log n)) ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          14 * ((H.index : ℝ) + 1) * pairedGaussianScale (Real.log n) ^ (1 / 4 : ℝ) +
          ((H.index - 1 : ℕ) : ℝ) *
            LLS.PaperStatements.gaussianAmbientError n (pairedGaussianScale (Real.log n))) :
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
  have hm := mul_le_mul_of_nonneg_right hd' (Real.sqrt_nonneg (pairedGaussianScale (Real.log n)))
  have hc := mul_le_mul_of_nonneg_left hC (by norm_num only : (0 : ℝ) ≤ 161 / 400)
  have hE := pairedGaussian_ambient_error hL (le_refl (Real.log n))
  have hs := pairedGaussian_budget hL hE
  linarith only [hcmp, hm, hc, hs]

/-- Under GRH, an odd modulus with passes contained in an index-four subgroup and with the
corresponding conductor-log sum at most `2 * log n` has an MR witness within the variable
paired bound. The Gaussian comparison at the paired scale contradicts the strict budget. -/
theorem paired_indexFour_witness {n : ℕ} [NeZero n] (hnlarge : 20000 ≤ n) (hnOdd : Odd n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hL : 70000 ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  classical
  by_contra hnone
  have hx : 4 ≤ pairedGaussianScale (Real.log n) :=
    (by norm_num only : (4 : ℝ) ≤ 3 ^ 16).trans (pairedGaussian_ge_three_pow hL)
  have hcut :
    (21 / 10 : ℝ) * pairedGaussianScale (Real.log n) =
      (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 := by
    dsimp only [pairedGaussianScale]
    ring
  have hpass :
    ∀ r : ℕ,
      r.Prime →
        (r : ℝ) ≤ (21 / 10 : ℝ) * pairedGaussianScale (Real.log n) →
        PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
    intro r hr hb
    rw [hcut] at hb
    by_contra hfail
    exact hnone ⟨r, hr, hb, hfail⟩
  have hcmp :=
    gaussian_inequality_of_prime_passes_in_subgroup hnlarge hnOdd H hHpass hGRH hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hpass
  exact paired_indexFour_contradiction H hi hC hL hcmp

/-- Under GRH, a product of three distinct odd primes satisfying the Korselt divisibility
conditions and equal predecessor two-adic valuations has a rejecting prime within the variable
paired bound at `log n ≥ 70000`. The existing index-four subgroup supplies the Gaussian input. -/
theorem paired_threeKorselt_witness {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1) (hrdiv : r - 1 ∣ n - 1)
    (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 70000 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 ∧
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
  exact paired_indexFour_witness hnlarge hnOdd H hi hpass hGRH hC.le hL

/-- Under GRH, an odd squarefree integer with three distinct prime factors and `log n ≥ 70000`
has a rejecting prime within the paired-coefficient bound. Non-Korselt and mixed-valuation cases
use the local factor estimate; the remaining case uses the index-four Gaussian comparison. -/
theorem paired_squarefreeThree_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hsf : Squarefree n)
    (hcard : n.primeFactors.card = 3) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (70000 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hc : 3 ≤ n.primeFactors.card := hcard.ge
  by_cases hlocal :
    (∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1)) ∨
      ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1
  · obtain ⟨r, hr, hf, hb, _⟩ :=
      exists_leastWitness_le_local_factor_coefficient hn ho hc hlocal hGRH
    have hα := pairedAlpha_ge_653 (high_log_twice_ge_22 hL)
    have hcoeff :
      (4 : ℝ) / ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤
        (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 := by
      rw [hcard]
      norm_num only [Nat.cast_ofNat]
      nlinarith only [hα, sq_nonneg (pairedAlpha (2 * Real.log (Real.log n)) - 653 / 1000)]
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
      paired_threeKorselt_witness hp hq hr (hp.odd_of_ne_two (ho.ne_two_of_dvd_nat hpn))
        (hq.odd_of_ne_two (ho.ne_two_of_dvd_nat hqn)) (hr.odd_of_ne_two (ho.ne_two_of_dvd_nat hrn))
        hpq hpr hqr hnprod (hK p hp hpn) (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn)
        (hU p r hp hr hpn hrn) hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
