/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianKorseltTriple

/-! # Numerical budget for the high-range Gaussian triple branch -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Gaussian scale whose cutoff `21 / 10` gives the coefficient `7 / 16`. -/
noncomputable def highCoefficientScale (L : ℝ) : ℝ :=
  (5 / 24 : ℝ) * L ^ 2

/-- The Gaussian scale is nonnegative for every real logarithmic parameter. -/
theorem highCoefficientScale_nonneg (L : ℝ) : 0 ≤ highCoefficientScale L :=
  mul_nonneg (by norm_num only : (0 : ℝ) ≤ 5 / 24) (sq_nonneg L)

/-- At nonnegative scale, the square root is at least `91 / 200` of the logarithm. -/
theorem highCoefficientScale_sqrt_lower {L : ℝ} (hL : 0 ≤ L) :
    (91 / 200 : ℝ) * L ≤ Real.sqrt (highCoefficientScale L) := by
  apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL) (highCoefficientScale_nonneg L)).mpr
  change (91 / 200 * L) ^ 2 ≤ (5 / 24 : ℝ) * L ^ 2
  nlinarith only [sq_nonneg L]

/-- At nonnegative scale, the square root is at most `289 / 625` of the logarithm.
Its rational coefficient is the square of `17 / 25` for the fourth-root estimate. -/
theorem highCoefficientScale_sqrt_upper {L : ℝ} (hL : 0 ≤ L) :
    Real.sqrt (highCoefficientScale L) ≤ (289 / 625 : ℝ) * L := by
  apply Real.sqrt_le_iff.mpr
  exact
    ⟨mul_nonneg (by norm_num only) hL, by
      dsimp only [highCoefficientScale]
      nlinarith only [sq_nonneg L]⟩

/-- For nonnegative logarithmic scale, the Gaussian fourth root is at most
`(17 / 25) * sqrt L`. This bounds the secondary term in the triple comparison. -/
theorem highCoefficientScale_fourth_root_le {L : ℝ} (hL : 0 ≤ L) :
    highCoefficientScale L ^ (1 / 4 : ℝ) ≤ (17 / 25 : ℝ) * Real.sqrt L := by
  have he :
    highCoefficientScale L ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt (highCoefficientScale L)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (highCoefficientScale_nonneg L)]
    norm_num only
  rw [he]
  convert Real.sqrt_le_sqrt (highCoefficientScale_sqrt_upper hL) using 1
  norm_num only [Real.sqrt_mul, Real.sqrt_div]

/-- The `7 / 16` Gaussian scale exceeds the threshold required by the
left-moment decay estimate throughout the high-range domain. -/
theorem highCoefficientScale_ge_three_pow_sixteen {L : ℝ} (hL : 70000 ≤ L) :
    (3 : ℝ) ^ 16 ≤ highCoefficientScale L := by
  change (3 : ℝ) ^ 16 ≤ (5 / 24 : ℝ) * L ^ 2
  nlinarith only [hL]

/-- For a logarithmic scale at least 70000, a square-root contribution bounded by `L / 260`
and an ambient error at most 30 fit strictly within the rational Gaussian coefficient gap.
The explicit arithmetic margin is used to exclude the index-four Gaussian comparison. -/
theorem highCoefficient_triple_budget {L s E : ℝ} (hL : 70000 ≤ L) (hs : s ≤ L / 260)
    (hE : E ≤ 30) :
    70 * (17 / 25 : ℝ) * s + 3 * E < ((21943 / 10000 : ℝ) * (91 / 200) - 161 / 200) * L := by
  linarith only [hL, hs, hE]

/-- From logarithmic scale 70000, the square root is at most `L / 260`.
This controls the secondary term of the high-range Gaussian budget. -/
theorem highCoefficient_sqrt_le {L : ℝ} (hL : 70000 ≤ L) : Real.sqrt L ≤ L / 260 := by
  nlinarith only [Real.sq_sqrt (show 0 ≤ L by linarith only [hL]), Real.sqrt_nonneg L, hL]

/-- With logarithmic scale at least 70000 and ambient error at most 30, the Gaussian
secondary terms are strictly below the rational main-term margin. -/
theorem highCoefficient_triple_sqrt_budget {L E : ℝ} (hL : 70000 ≤ L) (hE : E ≤ 30) :
    70 * (17 / 25 : ℝ) * Real.sqrt L + 3 * E <
      ((21943 / 10000 : ℝ) * (91 / 200) - 161 / 200) * L := by
  exact highCoefficient_triple_budget hL (highCoefficient_sqrt_le hL) hE

/-- The rational square-root and fourth-root estimates reduce the Gaussian comparison to the
strict budget above. This is the numerical interface for the index-four conductor bound. -/
theorem highCoefficient_triple_main_term {L x E : ℝ} (hL : 70000 ≤ L) (hE : E ≤ 30)
    (hroot : (91 / 200 : ℝ) * L ≤ Real.sqrt x)
    (hfourth : x ^ (1 / 4 : ℝ) ≤ (17 / 25 : ℝ) * Real.sqrt L) :
    (161 / 200 : ℝ) * L + 70 * x ^ (1 / 4 : ℝ) + 3 * E < (21943 / 10000 : ℝ) * Real.sqrt x := by
  linarith only [highCoefficient_triple_sqrt_budget hL hE, hroot, hfourth]

/-- At the `7 / 16` scale, an ambient error at most 30 implies the strict
numerical inequality required by the index-four Gaussian comparison. -/
theorem highCoefficient_triple_scale_budget {L E : ℝ} (hL : 70000 ≤ L) (hE : E ≤ 30) :
    (161 / 200 : ℝ) * L + 70 * highCoefficientScale L ^ (1 / 4 : ℝ) + 3 * E <
      (21943 / 10000 : ℝ) * Real.sqrt (highCoefficientScale L) := by
  exact
    highCoefficient_triple_main_term hL hE (highCoefficientScale_sqrt_lower (by linarith only [hL]))
      (highCoefficientScale_fourth_root_le (by linarith only [hL]))

/-- For `L ≥ 70000`, a modulus with logarithm at most `L` has Gaussian ambient error
at most 30 at the `7 / 16` scale. The pole and left-moment terms are each at most 4. -/
theorem highCoefficient_ambient_error_le {q : ℕ} {L : ℝ} (hL : 70000 ≤ L) (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianAmbientError q (highCoefficientScale L) ≤ 30 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hs := highCoefficientScale_sqrt_lower hL0.le
  have hs0 : 0 < Real.sqrt (highCoefficientScale L) :=
    (mul_pos (by norm_num only : (0 : ℝ) < 91 / 200) hL0).trans_le hs
  have hP :
    (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / Real.sqrt (highCoefficientScale L)) ≤ 4 := by
    rw [← mul_div_assoc, div_le_iff₀ hs0]
    linarith only [hL, hq, hs]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_three_sqrt
      (highCoefficientScale_ge_three_pow_sixteen hL)
  have hC : 0 ≤ (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) := by
    linarith only [Real.log_natCast_nonneg q]
  have hb := mul_le_mul_of_nonneg_left hdec hC
  have hB :
    (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) /
        (3 * Real.sqrt (highCoefficientScale L)) ≤
      4 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 3) hs0)).mpr
    linarith only [hL, hq, hs]
  have hJ :
    (11 / 10 : ℝ) * highCoefficientScale L ^ (-9 / 16 : ℝ) *
        ((16 / 5) * (Real.log q + 283) + 5 / 3) ≤
      4 := by
    simp only [div_eq_mul_inv] at hb hB ⊢
    nlinarith only [hb, hB]
  dsimp only [LLS.PaperStatements.gaussianAmbientError]
  linarith only [hP, hJ]

/-- At logarithmic scale at least 70000, the Gaussian comparison for an index-four
subgroup with conductor-log sum at most twice the modulus logarithm is impossible.
The ambient-error estimate and strict rational budget give the contradiction. -/
private theorem highCoeff_indexFour_contradiction {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : H.index = 4) (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hL : 70000 ≤ Real.log n)
    (hcmp :
      ((H.index : ℝ) *
              (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt (highCoefficientScale (Real.log n)) ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          14 * ((H.index : ℝ) + 1) * highCoefficientScale (Real.log n) ^ (1 / 4 : ℝ) +
          ((H.index - 1 : ℕ) : ℝ) *
            LLS.PaperStatements.gaussianAmbientError n (highCoefficientScale (Real.log n))) :
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
  have hm := mul_le_mul_of_nonneg_right hd' (Real.sqrt_nonneg (highCoefficientScale (Real.log n)))
  have hc := mul_le_mul_of_nonneg_left hC (by norm_num only : (0 : ℝ) ≤ 161 / 400)
  have hE := highCoefficient_ambient_error_le hL (le_refl (Real.log n))
  have hs := highCoefficient_triple_scale_budget hL hE
  linarith only [hcmp, hm, hc, hs]

/-- Under GRH, an odd modulus at logarithmic scale at least 70000 has a prime MR
witness bounded by `(7 / 16) * log n ^ 2` when its strong passes lie in an
index-four subgroup with conductor-log sum at most twice `log n`. The Gaussian
comparison contradicts the certified high-range numerical budget. -/
theorem highCoeff_indexFour_witness {n : ℕ} [NeZero n] (hnlarge : 20000 ≤ n) (hnOdd : Odd n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n)
    (hL : 70000 ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  classical
  by_contra hnone
  have hx : 4 ≤ highCoefficientScale (Real.log n) :=
    (by norm_num only : (4 : ℝ) ≤ 3 ^ 16).trans (highCoefficientScale_ge_three_pow_sixteen hL)
  have hcut :
    (21 / 10 : ℝ) * highCoefficientScale (Real.log n) = (7 / 16 : ℝ) * (Real.log n) ^ 2 := by
    dsimp only [highCoefficientScale]
    ring
  have hpass :
    ∀ r : ℕ,
      r.Prime →
        (r : ℝ) ≤ (21 / 10 : ℝ) * highCoefficientScale (Real.log n) →
        PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
    intro r hr hb
    rw [hcut] at hb
    by_contra hfail
    exact hnone ⟨r, hr, hb, hfail⟩
  have hcmp :=
    gaussian_inequality_of_prime_passes_in_subgroup hnlarge hnOdd H hHpass hGRH hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hpass
  exact highCoeff_indexFour_contradiction H hi hC hL hcmp

/-- Under GRH, a product of three distinct odd primes satisfying Korselt divisibility
and equal predecessor two-adic valuations has a prime MR witness at most
`(7 / 16) * log n ^ 2` when `log n ≥ 70000`. The existing index-four subgroup
and its conductor-log sum feed the high-range Gaussian witness bound. -/
theorem highCoeff_threeKorselt_witness {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1) (hrdiv : r - 1 ∣ n - 1)
    (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 70000 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 ∧
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
  exact highCoeff_indexFour_witness hnlarge hnOdd H hi hpass hGRH hC.le hL

end PseudoPrime.PrimeTestBounds.MillerRabin
