/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ScaleOneNumerics

/-! # Scale-one witness for the large-index branch -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH at logarithmic scale at least 25000, a large Fermat-subgroup index yields
an actual rejecting prime within the adaptive Gaussian cutoff. Use the credited
interior gap or the all-scale dual gap according to the triangular support. -/
theorem scaleOne_large_witness {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hi : 1000000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (25000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let L := Real.log n
  let x := ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2
  let H := PrimeTest.fermatSubgroup n
  have hiR : (1000000000000 : ℝ) ≤ (H.index : ℝ) := by exact_mod_cast hi
  have hr := scaleOne_cutoff_roots (v := 158) hL (by norm_num only) (by nlinarith only [hL])
  have hx : 1 < x := hr.1
  have hex : ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ (p ∣ n ∨ ¬NumberTheory.residueInSubgroup n H p) := by
    by_cases hU : x ≤ Real.exp 36
    · have hmargin := scaleOne_interior_margin hL hU
      have hgap := LLS.PaperStatements.scaleOne_interior_gap_of_margin hx hU hL hiR hr.2.1 hmargin
      exact LLS.PaperStatements.exists_prime_scaleOne_interior H hGRH hx hU hgap
    · have houter : Real.exp 36 ≤ x := le_of_not_ge hU
      have hgap := scaleOne_outer_gap hL hiR houter
      exact LLS.PaperStatements.exists_prime_dual_gap H hGRH hx hgap
  obtain ⟨p, hp, hb, hout⟩ := hex
  refine ⟨p, hp, hb, ?_⟩
  intro hpass
  rcases hout with hd | hout
  · have hcop :=
      (ZMod.isUnit_iff_coprime p n).mp (PrimeTest.strongMillerRabinPass_isUnit hn ho hpass)
    exact (hp.coprime_iff_not_dvd.mp hcop) hd
  · exact hout (PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn ho hpass)

/-- Under GRH, every odd composite of logarithmic scale at least 25000 has an actual
rejecting prime below the adaptive Gaussian cutoff. The large-index, local subgroup,
and uniform three-factor branches are all discharged. -/
theorem prime_witness_scaleOne {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (25000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply scaleOne_reduce_large hn ho hc hGRH hL
  intro hi
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact scaleOne_large_witness hn ho hi hGRH hL

/-- Under GRH, every odd composite with logarithmic scale at least 25000 has a
rejecting prime strictly below 0.29 times the squared scale. Compare the certified
adaptive coefficient with 0.29 and use positivity of the scale. -/
theorem prime_witness_scaleOne_lt {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (25000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) < (29 / 100 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := prime_witness_scaleOne hn ho hc hGRH hL
  have hs := scaleOne_gaussian_slope (Real.log n) hL
  have hsq := pow_le_pow_left₀ (by linarith only [hs.1] : 0 ≤ adaptiveGaussianA (Real.log n)) hs.2 2
  have hC : (21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2 < 29 / 100 := by nlinarith only [hsq]
  have hLpos : 0 < Real.log n := by linarith only [hL]
  have hlt := mul_lt_mul_of_pos_right hC (sq_pos_of_pos hLpos)
  exact ⟨p, hp, hb.trans_lt hlt, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
