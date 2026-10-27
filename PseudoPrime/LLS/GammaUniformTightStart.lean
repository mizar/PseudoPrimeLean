/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformReducedStart
public import PseudoPrime.LLS.GammaUniformLocalBudgetParameters

/-! # Tighter uniform coefficient-four-fifths starting value

Refined rational square-root and logarithmic-ratio certificates lower the common
logarithmic start to 45561. The decimal logarithm gives 10^19787 for subgroup,
general-character and least-prime witnesses, with the same analytic kernel.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a natural n ≥ 10 ^ 19787, log n > 45561. Take logs of the decimal
power and use the certified lower bound log 10 > 115129 / 50000.
This converts the reduced uniform Gamma budget to a concrete decimal start. -/
theorem log_nat_gt_45561_of_decimal_19787 {n : ℕ} (hn : 10 ^ 19787 ≤ n) :
    (45561 : ℝ) < Real.log n := by
  have h :=
    Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 10) 19787)
      (by exact_mod_cast hn : (10 : ℝ) ^ 19787 ≤ n)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, log_ten_gt_230258]

end PseudoPrime.Analysis

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, nonzero q, log q ≥ 35000 and H proper, a strict budget for the
actual normalized nonunit loss gives a unit prime outside H through (4/5)(log q)^2.
Contradict the uniform ramp comparison and the main-term gap.
This internal interface keeps the witness proof independent of the local-budget parameters. -/
private theorem exists_prime_outside_of_uniform_gamma_local_budget {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 35000 ≤ Real.log q)
    (hbudget :
      (40159 / 900 : ℝ) +
          2 *
            (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum
                ((32 / 99 : ℝ) * (Real.log q) ^ 2) ((4 / 5 : ℝ) * (Real.log q) ^ 2) q /
              Real.sqrt ((32 / 99 : ℝ) * (Real.log q) ^ 2)) <
        Real.log q / 795) :
    ∃ p : ℕ,
      p.Prime ∧ ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 := by
  classical
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have ht := Real.log_le_sub_one_of_pos hq0
  have hq : 20000 ≤ q := by exact_mod_cast (show (20000 : ℝ) ≤ q by linarith only [ht, hL])
  by_contra hn
  have hsmall (p : ℕ) (hp : p.Prime) (hd : ¬p ∣ q) (hb : (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2) :
    residueInSubgroup q H p := by
    by_contra hout
    exact hn ⟨p, hp, hd, hout, hb⟩
  have hc := gamma_ramp_subgroup_comparison_uniform hq H hH hGRH hL hsmall
  have he :
    (99 / 40 : ℝ) * ((32 / 99 : ℝ) * (Real.log q) ^ 2) = (4 / 5 : ℝ) * (Real.log q) ^ 2 := by ring
  dsimp only at hc
  rw [he] at hc
  have hm := Analysis.nonOne_main_term_gap (show 0 < Real.log q by linarith only [hL])
  linarith only [hc, hbudget, hm]

/-- Under GRH, nonzero q, log q ≥ 45561 and H proper, a unit prime outside H
exists through (4/5)(log q)^2. Apply the parameterized local allowance 63960/5041
and the rational strict error budget to the common contradiction interface.
No additional arithmetic or analytic premise remains in this log entrance. -/
theorem exists_prime_outside_le_gamma_four_fifths_log_45561 {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 45561 ≤ Real.log q) :
    ∃ p : ℕ,
      p.Prime ∧ ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 := by
  apply
    exists_prime_outside_of_uniform_gamma_local_budget H hH hGRH
      ((by norm_num only : (35000 : ℝ) ≤ 45561).trans hL)
  have hD :=
    Analysis.gamma_commonFactor_budget_of_log_ge_44739
      ((by norm_num only : (44739 : ℝ) ≤ 45561).trans hL)
  have hE := Analysis.gamma_uniform_error_budget_of_ge_45561 hL
  have he :
    (99 / 40 : ℝ) * ((32 / 99 : ℝ) * (Real.log q) ^ 2) = (4 / 5 : ℝ) * (Real.log q) ^ 2 := by ring
  dsimp only at hD
  rw [he] at hD
  linarith only [hD, hE]

/-- Under GRH, q ≥ 10^19787 and H any proper subgroup of the units,
there is a prime coprime to q outside H at most (4/5)(log q)^2.
Convert the decimal threshold to log q > 45561 and apply the tighter log entrance.
The starting value is uniform in the index and in the level's factorization type. -/
theorem exists_prime_outside_le_gamma_four_fifths_19787 {q : ℕ} (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hq : 10 ^ 19787 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧ ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 := by
  have hq0 : q ≠ 0 :=
    Nat.ne_zero_of_lt ((pow_pos (by norm_num only : (0 : ℕ) < 10) 19787).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  exact
    exists_prime_outside_le_gamma_four_fifths_log_45561 H hH hGRH
      (Analysis.log_nat_gt_45561_of_decimal_19787 hq).le

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- Under GRH, q ≥ 10 ^ 19787 and χ nonprincipal, there is a prime p coprime
to q with χ(p) ≠ 1 and p ≤ (4 / 5)(log q) ^ 2. Apply the uniform proper-subgroup
bound to the unit kernel and translate nonmembership into a non-one value.
This improves the large-level general-character form of LLS Theorem 1.1. -/
theorem exists_prime_character_ne_one_le_gamma_four_fifths_19787 {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 19787 ≤ q) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 := by
  obtain ⟨p, hp, hd, hout, hb⟩ :=
    PaperStatements.exists_prime_outside_le_gamma_four_fifths_19787 χ.toUnitHom.ker
      (NumberTheory.ker_toUnitHom_ne_top_of_ne_one χ hne) hGRH hq
  refine ⟨p, hp, hd, ?_, hb⟩
  intro he
  have hc := hp.coprime_iff_not_dvd.mpr hd
  have hu := (ZMod.isUnit_iff_coprime p q).mpr hc
  apply hout
  refine ⟨hu.unit, ?_, IsUnit.unit_spec hu⟩
  apply MonoidHom.mem_ker.mpr
  apply Units.ext
  simpa only [MulChar.coe_toUnitHom, Units.val_one, IsUnit.unit_spec] using he

/-- Under GRH, q ≥ 10 ^ 19787 and H proper, the project predicate for a prime
outside H has a witness at most (4 / 5)(log q) ^ 2. Recover the residue unit from
coprimality and transfer the uniform subgroup witness to the existing predicate.
This is the existence interface used to construct the least outside prime. -/
theorem exists_prime_outside_subgroup_le_gamma_four_fifths_19787 {q : ℕ} (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hq : 10 ^ 19787 ≤ q) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 := by
  obtain ⟨p, hp, hd, hout, hb⟩ :=
    PaperStatements.exists_prime_outside_le_gamma_four_fifths_19787 H hH hGRH hq
  have hu := (ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd)
  refine ⟨p, ⟨hp, hd, hu.unit, ?_, IsUnit.unit_spec hu⟩, hb⟩
  intro hm
  exact hout ⟨hu.unit, hm, IsUnit.unit_spec hu⟩

/-- Under GRH, q ≥ 10 ^ 19787 and H proper, the least prime coprime to q
outside H is at most (4 / 5)(log q) ^ 2. Minimize the unbounded prime predicate
using the bounded existence witness. Minimality holds among all eligible primes,
without restricting the comparison candidates to the displayed upper bound. -/
theorem exists_least_prime_outside_subgroup_le_gamma_four_fifths_19787 {q : ℕ}
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 19787 ≤ q) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 ∧ ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  classical
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_subgroup_le_gamma_four_fifths_19787 H hH hGRH hq
  have hex : ∃ r, PrimeOutsideSubgroup q H r := ⟨p, hp⟩
  exact
    ⟨Nat.find hex, Nat.find_spec hex, (Nat.cast_le.mpr (Nat.find_min' hex hp)).trans hb, fun _ hr ↦
      Nat.find_min' hex hr⟩

end PseudoPrime.LLS
