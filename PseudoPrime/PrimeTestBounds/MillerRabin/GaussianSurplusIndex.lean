/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.JointSurplusNumerics

/-! # Large-index witnesses for surplus Gaussian cutoffs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH and a large Fermat-subgroup index, either certified surplus cutoff
contains an actual rejecting prime. Use the joint signed interior gap inside support
and the all-scale dual gap outside it. -/
theorem jointSurplus_large_witness {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hi : 1000000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {rho R T : ℝ} (hT : 280 ≤ T)
    (hL : T ≤ Real.log n) (hR : 29 ≤ R) (hRup : R ≤ 30) (hrho : 130 ≤ rho) (hrhoMax : rho ≤ 155)
    (hrhoT : rho ≤ (467 / 1000 : ℝ) * T) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius rho R (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let L := Real.log n
  let x := (21 / 10 : ℝ) * (jointSurplusRadius rho R L) ^ 2
  let H := PrimeTest.fermatSubgroup n
  have hiR : (1000000000000 : ℝ) ≤ (H.index : ℝ) := by exact_mod_cast hi
  have hb :=
    jointSurplus_cutoff_roots hT hL hR hRup hrho hrhoT (v := 16) (by norm_num only)
      (by nlinarith only [hT])
  have hx16 : 16 ≤ x := hb.1
  have hx : 1 < x := by linarith only [hx16]
  have hex : ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ (p ∣ n ∨ ¬NumberTheory.residueInSubgroup n H p) := by
    by_cases hU : x ≤ Real.exp 36
    · have hmargin := jointSurplus_interior_margin hT hL hR hRup hrho hrhoMax hrhoT hU
      have hgap :=
        LLS.PaperStatements.joint_gap_of_margin hx hU (Real.log_natCast_nonneg n) hiR hmargin
      exact
        LLS.PaperStatements.exists_prime_joint_interior H hGRH hx16 hU (by linarith only [hiR]) hgap
    · have houter : Real.exp 36 ≤ x := le_of_not_ge hU
      have hgap := jointSurplus_outer_gap hT hL hR hRup hrho hrhoMax hrhoT hiR houter
      exact LLS.PaperStatements.exists_prime_dual_gap H hGRH hx hgap
  obtain ⟨p, hp, hb, hout⟩ := hex
  refine ⟨p, hp, hb, ?_⟩
  intro hpass
  rcases hout with hd | hout
  · have hcop :=
      (ZMod.isUnit_iff_coprime p n).mp (PrimeTest.strongMillerRabinPass_isUnit hn ho hpass)
    exact (hp.coprime_iff_not_dvd.mp hcop) hd
  · exact hout (PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn ho hpass)

/-- Under GRH, every odd composite of logarithmic scale at least 280 has a rejecting
prime below the 35000-prefix Gaussian cutoff. All factor structures are covered. -/
theorem jointSurplus_witness35000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (280 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius 130 30 (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply jointSurplus_reduce35000 hn ho hc hGRH hL
  intro hi
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    jointSurplus_large_witness hn ho hi hGRH (T := 280) (by norm_num only) hL (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)

/-- Under GRH, every odd composite of logarithmic scale at least 340 has a rejecting
prime below the 50000-prefix Gaussian cutoff. All factor structures are covered. -/
theorem jointSurplus_witness50000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (340 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * (jointSurplusRadius 155 29 (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply jointSurplus_reduce50000 hn ho hc hGRH (by linarith only [hL])
  intro hi
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    jointSurplus_large_witness hn ho hi hGRH (T := 340) (by norm_num only) hL (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
