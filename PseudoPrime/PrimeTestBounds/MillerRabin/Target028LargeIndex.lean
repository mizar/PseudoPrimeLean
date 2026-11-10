/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SmallIndex
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028HighWitness

/-! # Large-index triangular witnesses for the coefficient 0.28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational bounds for logarithm, roots, and index imply the strict
triangular joint gap on the scale beginning at 106. This algebraic certificate
is independent of the construction of those bounds. -/
private theorem triangular_gap_028_scalar (L z r y ri yi I : ℝ) (hL : 106 ≤ L) (hz1 : 8 ≤ z)
    (hz2 : z ≤ 14) (hr1 : (52915 / 100000 : ℝ) * L ≤ r) (hr2 : r ≤ (53 / 100 : ℝ) * L)
    (hy : y ≤ (71 / 1000 : ℝ) * L) (hy0 : 0 ≤ y) (hri : ri ≤ 1) (hyi : yi ≤ 1) (hI : 50000000 ≤ I) :
    300000000 * (r + ri) + 1300000 * (y + yi) + 602600000 + (I - 1) * ((72 - z) * L) <
      I * ((220 - 4 * z) * r - (1064 / 5 - (19 / 5 : ℝ) * z) * y - 855) := by
  have hA : 0 ≤ (14 - z) * r := mul_nonneg (by linarith only [hz2]) (by linarith only [hL, hr1])
  have hB : 0 ≤ (z - 8) * y := mul_nonneg (by linarith only [hz1]) hy0
  have hC : 0 ≤ (z - 8) * L := mul_nonneg (by linarith only [hz1]) (by linarith only [hL])
  have hD : 0 ≤ (I - 1) * ((z - 8) * L) := mul_nonneg (by linarith only [hI]) hC
  have hE : 0 ≤ I * ((14 - z) * r) := mul_nonneg (by linarith only [hI]) hA
  have hF : 0 ≤ I * ((z - 8) * y) := mul_nonneg (by linarith only [hI]) hB
  have hG : 0 ≤ I * (r - (52915 / 100000 : ℝ) * L) :=
    mul_nonneg (by linarith only [hI]) (by linarith only [hr1])
  have hH : 0 ≤ I * ((71 / 1000 : ℝ) * L - y) :=
    mul_nonneg (by linarith only [hI]) (by linarith only [hy])
  have hK : 0 ≤ (I - 50000000) * (L - 106) :=
    mul_nonneg (by linarith only [hI]) (by linarith only [hL])
  nlinarith only [hD, hE, hF, hG, hH, hK, hI, hL, hr2, hy, hri, hyi]

/-- The 0.28 quadratic cutoff is at least 16 at scale 106. Its square root
lies between two rational multiples of the scale and its fourth root is at
most `71L/1000`; square comparison supplies the numerical gap bounds. -/
private theorem triangular_028_roots {L : ℝ} (hL : 106 ≤ L) :
    let x := (7 / 25 : ℝ) * L ^ 2
    16 ≤ x ∧
      (52915 / 100000 : ℝ) * L ≤ Real.sqrt x ∧
      Real.sqrt x ≤ (53 / 100 : ℝ) * L ∧ x ^ (1 / 4 : ℝ) ≤ (71 / 1000 : ℝ) * L := by
  let x := (7 / 25 : ℝ) * L ^ 2
  have hLp : 0 < L := by linarith only [hL]
  have hx : 16 ≤ x := by
    dsimp only [x]; nlinarith only [hL]
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hcl : (52915 / 100000 : ℝ) ^ 2 ≤ 7 / 25 := by norm_num only
  have hcu : (7 / 25 : ℝ) ≤ (53 / 100 : ℝ) ^ 2 := by norm_num only
  have hcl' := mul_le_mul_of_nonneg_right hcl (sq_nonneg L)
  have hcu' := mul_le_mul_of_nonneg_right hcu (sq_nonneg L)
  have hl : (52915 / 100000 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by linarith only [hL]) hx0).2
    dsimp only [x]
    nlinarith only [hcl']
  have hu : Real.sqrt x ≤ (53 / 100 : ℝ) * L := by
    apply (Real.sqrt_le_iff).2
    constructor
    · linarith only [hL]
    · dsimp only [x]
      nlinarith only [hcu']
  have ht : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    have he := Real.rpow_mul hx0 (1 / 4) 2
    norm_num only [Real.rpow_two] at he
    rw [Real.sqrt_eq_rpow]
    exact he.symm
  have hpow := mul_le_mul_of_nonneg_right hL hLp.le
  have hquarter : x ^ (1 / 4 : ℝ) ≤ (71 / 1000 : ℝ) * L := by
    have hp := Real.rpow_nonneg hx0 (1 / 4)
    nlinarith only [ht, hu, hpow, hp, hLp]
  exact ⟨hx, hl, hu, hquarter⟩

/-- Between scales 106 and 2000, the logarithm of the quadratic cutoff lies
between 8 and 14, and the cutoff lies inside the triangular support. Exact
rational logarithm certificates and monotonicity give both endpoints. -/
private theorem triangular_028_logs {L : ℝ} (hL : 106 ≤ L) (hU : L ≤ 2000) :
    let x := (7 / 25 : ℝ) * L ^ 2
    8 ≤ Real.log x ∧ Real.log x ≤ 14 ∧ x ≤ Real.exp 36 := by
  let x := (7 / 25 : ℝ) * L ^ 2
  have hlo : (3000 : ℝ) ≤ x := by
    dsimp only [x]; nlinarith only [hL]
  have hhi : x ≤ (1120000 : ℝ) := by
    dsimp only [x]; nlinarith only [hL, hU]
  have hc1 : Analysis.rationalLogIntervalCheck 3000 12 16 8 9 = true := by decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 1120000 21 16 13 14 = true := by decide +kernel
  have hl := (Analysis.rationalLogIntervalCheck_sound hc1).1
  have hu := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_ofNat] at hl hu
  have hxpos : 0 < x := by linarith only [hlo]
  have hlx : 8 ≤ Real.log x := hl.trans (Real.log_le_log (by norm_num only) hlo)
  have hux : Real.log x ≤ 14 := (Real.log_le_log hxpos hhi).trans hu
  have hex : x ≤ Real.exp 36 := (Real.log_le_iff_le_exp hxpos).mp (by linarith only [hux])
  exact ⟨hlx, hux, hex⟩

/-- Under GRH, an odd input whose Fermat index is at least 50000000 has a
0.28 rejecting prime throughout logarithmic scales 106 to 2000. The root and
logarithm bounds establish the strict triangular gap at the target cutoff. -/
theorem exists_prime_reject_028_high_index {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hi : 50000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (106 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 2000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let L := Real.log n
  let x := (7 / 25 : ℝ) * L ^ 2
  have roots := triangular_028_roots hL
  have logs := triangular_028_logs hL hU
  change
    16 ≤ x ∧
      (52915 / 100000 : ℝ) * L ≤ Real.sqrt x ∧
      Real.sqrt x ≤ (53 / 100 : ℝ) * L ∧ x ^ (1 / 4 : ℝ) ≤ (71 / 1000 : ℝ) * L at roots
  change 8 ≤ Real.log x ∧ Real.log x ≤ 14 ∧ x ≤ Real.exp 36 at logs
  have hx1 : 1 ≤ x := by linarith only [roots.1]
  have hinv : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx1
  have hri : Real.sqrt x⁻¹ ≤ 1 := Real.sqrt_le_one.mpr hinv
  have hyi : (x⁻¹) ^ (1 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one (inv_nonneg.mpr (by linarith only [hx1])) hinv (by norm_num only)
  have hiR : (50000000 : ℝ) ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by exact_mod_cast hi
  have hgap :=
    triangular_gap_028_scalar L (Real.log x) (Real.sqrt x) (x ^ (1 / 4 : ℝ)) (Real.sqrt x⁻¹)
      ((x⁻¹) ^ (1 / 4 : ℝ)) ((PrimeTest.fermatSubgroup n).index : ℝ) hL logs.1 logs.2.1 roots.2.1
      roots.2.2.1 roots.2.2.2 (Real.rpow_nonneg (by linarith only [hx1]) _) hri hyi hiR
  let H := PrimeTest.fermatSubgroup n
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.PaperStatements.exists_prime_joint_interior H hGRH roots.1 logs.2.2 (by linarith only [hiR])
      hgap
  refine ⟨p, hp, hb, ?_⟩
  intro hpass
  rcases hout with hd | hout
  · have hcop :=
      (ZMod.isUnit_iff_coprime p n).mp (PrimeTest.strongMillerRabinPass_isUnit hn ho hpass)
    exact (hp.coprime_iff_not_dvd.mp hcop) hd
  · exact hout (PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn ho hpass)

/-- Under GRH, every nonuniform odd composite of logarithmic scale at least
106 has a rejecting prime within the 0.28 cutoff. Split the middle range at
Fermat index 50000000 and apply the existing high-scale witness above 2000. -/
theorem exists_prime_reject_028_nonuniform106 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (106 : ℝ) ≤ Real.log n)
    (hU : ¬UniformKorseltTriple n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  by_cases h2000 : 2000 ≤ Real.log n
  · exact exists_prime_reject_028_high hn ho hc hGRH h2000
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 50000000
  · exact
      exists_prime_reject_028_small_index hn ho hc (PrimeTest.fermatSubgroup n) le_rfl hi hGRH hL hU
  · exact
      exists_prime_reject_028_high_index hn ho (Nat.le_of_lt (Nat.lt_of_not_ge hi)) hGRH hL
        (le_of_not_ge h2000)

end PseudoPrime.PrimeTestBounds.MillerRabin
