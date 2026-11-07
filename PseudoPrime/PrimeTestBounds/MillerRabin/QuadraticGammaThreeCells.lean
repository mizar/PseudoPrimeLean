/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaThirdGap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaLowCombined

/-! # Third Gamma cell and the combined low range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple in the third Gamma cell has a prime
rejecting base within the `3/10` cutoff. Its ordered prime factors supply
the three-character Gamma theorem, and the certified scalar gap forces a
rejecting prime below the cell's cutoff 487. -/
theorem uniform_third_cell_reject {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (gammaSecondRight : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (gammaThirdRight : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  obtain ⟨p, q, r, hp, hq, hr, hpq, hqr, hnp⟩ := uniformKorselt_ordered_factors hu
  have hpD : p ∣ n := hnp ▸ dvd_mul_of_dvd_left (dvd_mul_right p q) r
  have hqD : q ∣ n := hnp ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) r
  have hrD : r ∣ n := hnp ▸ dvd_mul_left r (p * q)
  have hpO := Odd.of_dvd_nat ho hpD
  have hqO := Odd.of_dvd_nat ho hqD
  have hrO := Odd.of_dvd_nat ho hrD
  have hp2 := ho.ne_two_of_dvd_nat hpD
  have hq2 := ho.ne_two_of_dvd_nat hqD
  have hr2 := ho.ne_two_of_dvd_nat hrD
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
  have hpqD : p * q ∣ n := ⟨r, hnp⟩
  have hprD : p * r ∣ n := ⟨q, hnp.trans (by ac_rfl)⟩
  have hqrD : q * r ∣ n := ⟨p, hnp.trans (by ac_rfl)⟩
  have hcut : (487 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    norm_num only [gammaSecondRight, Rat.cast_div, Rat.cast_ofNat] at hlo
    nlinarith only [hlo, sq_nonneg (Real.log n - 40290610982379 / 1000000000000)]
  obtain ⟨l, hl, hb, hf⟩ :=
    exists_prime_reject_of_gamma_gap (X := (487 : ℝ)) (x := (gammaMainCell2Scale : ℝ)) hu.1 hnp hGRH
      hn ho hpO hqO hrO hpD hqD hrD hpqD hprD hqrD (hu.2.2.1 p hp hpD) (hu.2.2.1 q hq hqD)
      (hu.2.2.1 r hr hrD) (hu.2.2.2 q p hq hp hqD hpD) (hu.2.2.2 r p hr hp hrD hpD)
      (by norm_num only [gammaMainCell2Scale, Rat.cast_div, Rat.cast_ofNat]) (Finset.Ioc 0 487)
      (by
        intro k hk; exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      (by norm_num only) (gamma_third_gap hGRH.riemann hhi)
  exact ⟨l, hl, hb.trans hcut, hf⟩

/-- Under GRH, every odd composite from logarithmic scale 8 through the third
Gamma cell has a rejecting prime within the coefficient `3/10` cutoff. The
new uniform cell and the existing nonuniform theorem extend the low result. -/
theorem exists_reject_03_low_three_cells {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (gammaThirdRight : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases h : Real.log n ≤ (gammaSecondRight : ℝ)
  · exact exists_reject_03_low_two_cells hn ho hc hGRH hL h
  · by_cases hu : UniformKorseltTriple n
    · exact uniform_third_cell_reject hn ho hu hGRH (le_of_not_ge h) hU
    · exact exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
