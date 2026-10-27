/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSignedProfiles
public import PseudoPrime.LLS.GammaUniformTightStart
public import PseudoPrime.Analysis.LogarithmicShiftBounds

/-! # Decimal and character interfaces for rational signed Gamma profiles

The concrete rational triples (4/5,0,29), (4/5,0,-2) and (4/5,-1,0)
have decimal entrances 15188, 20121 and 22097. General characters and least
outside primes use the same cutoffs. A rational-parameter interface retains
the actual analytic budget for further coefficient optimization.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For n ≥ 10^d with d > 0, any t < d*(115129/50000) satisfies t < log n.
Take logarithms of the power and use the certified lower bound for log 10.
This gives a common exact decimal conversion for the signed profiles. -/
theorem log_nat_gt_of_decimal_lower {n d : ℕ} {t : ℝ} (hd : 0 < d) (hn : 10 ^ d ≤ n)
    (ht : t < (d : ℝ) * (115129 / 50000)) : t < Real.log n := by
  have h :=
    Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 10) d)
      (by exact_mod_cast hn : (10 : ℝ) ^ d ≤ n)
  rw [Real.log_pow] at h
  have hlo := mul_lt_mul_of_pos_left log_ten_gt_230258 (Nat.cast_pos.mpr hd : (0 : ℝ) < d)
  exact ht.trans (hlo.trans_le h)

end PseudoPrime.Analysis

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, q ≥ 10^15188 and H proper, a coprime prime outside H exists
through (4/5)(log q+29)². Convert the exact decimal entrance to log q > 34971.
This is the decimal proper-subgroup interface for the signed profile. -/
theorem exists_prime_outside_le_gamma_four_fifths_plus_twentyNine_15188 {q : ℕ}
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 15188 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q + 29) ^ 2 := by
  have hq0 : q ≠ 0 :=
    Nat.ne_zero_of_lt ((pow_pos (by norm_num only : (0 : ℕ) < 10) 15188).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  apply exists_prime_outside_le_gamma_four_fifths_log_plus_twentyNine H hH hGRH
  exact
    (Analysis.log_nat_gt_of_decimal_lower (by norm_num only : 0 < 15188) hq
        (by norm_num only : (34971 : ℝ) < (15188 : ℝ) * (115129 / 50000))).le

/-- Under GRH, q ≥ 10^20121 and H proper, a coprime prime outside H exists
through (4/5)(log q-2)². Convert the exact decimal entrance to log q > 46330.
This is the decimal proper-subgroup interface for the signed profile. -/
theorem exists_prime_outside_le_gamma_four_fifths_minus_two_20121 {q : ℕ} (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hq : 10 ^ 20121 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ ¬residueInSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q - 2) ^ 2 := by
  have hq0 : q ≠ 0 :=
    Nat.ne_zero_of_lt ((pow_pos (by norm_num only : (0 : ℕ) < 10) 20121).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  apply exists_prime_outside_le_gamma_four_fifths_log_minus_two H hH hGRH
  exact
    (Analysis.log_nat_gt_of_decimal_lower (by norm_num only : 0 < 20121) hq
        (by norm_num only : (46330 : ℝ) < (20121 : ℝ) * (115129 / 50000))).le

/-- Under GRH, q ≥ 10^22097 and H proper, a coprime prime outside H exists
through (4/5)(log q-log log q)². Convert the exact decimal entrance to log q > 50880.
This is the decimal proper-subgroup interface for the signed profile. -/
theorem exists_prime_outside_le_gamma_four_fifths_minus_loglog_22097 {q : ℕ}
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 22097 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        ¬residueInSubgroup q H p ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q - Real.log (Real.log q)) ^ 2 := by
  have hq0 : q ≠ 0 :=
    Nat.ne_zero_of_lt ((pow_pos (by norm_num only : (0 : ℕ) < 10) 22097).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  apply exists_prime_outside_le_gamma_four_fifths_log_minus_loglog H hH hGRH
  exact
    (Analysis.log_nat_gt_of_decimal_lower (by norm_num only : 0 < 22097) hq
        (by norm_num only : (50880 : ℝ) < (22097 : ℝ) * (115129 / 50000))).le

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS

/-- If every proper unit subgroup at q has an outside prime through B,
every nonprincipal character has a coprime prime with non-one value through B.
Apply the subgroup bound to the unit kernel and recover the non-one value.
This transfers any certified cutoff without changing its expression or entrance. -/
theorem exists_prime_character_ne_one_of_uniform_subgroup_cutoff {q : ℕ} {B : ℝ}
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hbound :
      ∀ H : Subgroup (ZMod q)ˣ,
        H ≠ ⊤ →
          ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ ¬PaperStatements.residueInSubgroup q H p ∧ (p : ℝ) ≤ B) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ B := by
  obtain ⟨p, hp, hd, hout, hb⟩ :=
    hbound χ.toUnitHom.ker (NumberTheory.ker_toUnitHom_ne_top_of_ne_one χ hne)
  refine ⟨p, hp, hd, ?_, hb⟩
  intro he
  have hu := (ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd)
  apply hout
  refine ⟨hu.unit, ?_, IsUnit.unit_spec hu⟩
  apply MonoidHom.mem_ker.mpr
  apply Units.ext
  simpa only [MulChar.coe_toUnitHom, Units.val_one, IsUnit.unit_spec] using he

/-- A bounded coprime outside prime yields the least outside prime through
the same bound B, with minimality among all eligible primes.
Construct the project predicate and minimize it on the natural numbers.
This preserves the pointwise cutoff in the least-prime interface. -/
theorem exists_least_prime_outside_of_subgroup_cutoff {q : ℕ} {B : ℝ} (H : Subgroup (ZMod q)ˣ)
    (hbound : ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ ¬PaperStatements.residueInSubgroup q H p ∧ (p : ℝ) ≤ B) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ B ∧ ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  classical
  obtain ⟨p, hp, hd, hout, hb⟩ := hbound
  have hu := (ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd)
  have hprime : PrimeOutsideSubgroup q H p :=
    ⟨hp, hd, hu.unit, (fun hm ↦ hout ⟨hu.unit, hm, IsUnit.unit_spec hu⟩), IsUnit.unit_spec hu⟩
  have hex : ∃ r, PrimeOutsideSubgroup q H r := ⟨p, hprime⟩
  exact
    ⟨Nat.find hex, Nat.find_spec hex, (Nat.cast_le.mpr (Nat.find_min' hex hprime)).trans hb,
      fun _ hr ↦ Nat.find_min' hex hr⟩

/-- Under GRH, q ≥ 10^15188 and χ nonprincipal, a coprime prime with χ(p) ≠ 1
exists through (4/5)(log q+29)². Apply the uniform subgroup bound to the unit kernel.
This is the general-character interface with the same decimal entrance. -/
theorem exists_prime_character_ne_one_le_gamma_four_fifths_plus_twentyNine_15188 {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 15188 ≤ q) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q + 29) ^ 2 := by
  exact
    exists_prime_character_ne_one_of_uniform_subgroup_cutoff χ hne
      (fun H hH ↦
        PaperStatements.exists_prime_outside_le_gamma_four_fifths_plus_twentyNine_15188 H hH hGRH
          hq)

/-- Under GRH, q ≥ 10^15188 and H proper, the least coprime outside prime is
at most (4/5)(log q+29)². Minimize the bounded subgroup witness.
Minimality is among all eligible primes and retains the same entrance and cutoff. -/
theorem exists_least_prime_outside_le_gamma_four_fifths_plus_twentyNine_15188 {q : ℕ}
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 15188 ≤ q) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q + 29) ^ 2 ∧
        ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  exact
    exists_least_prime_outside_of_subgroup_cutoff H
      (PaperStatements.exists_prime_outside_le_gamma_four_fifths_plus_twentyNine_15188 H hH hGRH hq)

/-- Under GRH, q ≥ 10^20121 and χ nonprincipal, a coprime prime with χ(p) ≠ 1
exists through (4/5)(log q-2)². Apply the uniform subgroup bound to the unit kernel.
This is the general-character interface with the same decimal entrance. -/
theorem exists_prime_character_ne_one_le_gamma_four_fifths_minus_two_20121 {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 20121 ≤ q) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q - 2) ^ 2 := by
  exact
    exists_prime_character_ne_one_of_uniform_subgroup_cutoff χ hne
      (fun H hH ↦
        PaperStatements.exists_prime_outside_le_gamma_four_fifths_minus_two_20121 H hH hGRH hq)

/-- Under GRH, q ≥ 10^20121 and H proper, the least coprime outside prime is
at most (4/5)(log q-2)². Minimize the bounded subgroup witness.
Minimality is among all eligible primes and retains the same entrance and cutoff. -/
theorem exists_least_prime_outside_le_gamma_four_fifths_minus_two_20121 {q : ℕ}
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 20121 ≤ q) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q - 2) ^ 2 ∧ ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  exact
    exists_least_prime_outside_of_subgroup_cutoff H
      (PaperStatements.exists_prime_outside_le_gamma_four_fifths_minus_two_20121 H hH hGRH hq)

/-- Under GRH, q ≥ 10^22097 and χ nonprincipal, a coprime prime with χ(p) ≠ 1
exists through (4/5)(log q-log log q)². Apply the uniform subgroup bound to the unit kernel.
This is the general-character interface with the same decimal entrance. -/
theorem exists_prime_character_ne_one_le_gamma_four_fifths_minus_loglog_22097 {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 22097 ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q - Real.log (Real.log q)) ^ 2 := by
  exact
    exists_prime_character_ne_one_of_uniform_subgroup_cutoff χ hne
      (fun H hH ↦
        PaperStatements.exists_prime_outside_le_gamma_four_fifths_minus_loglog_22097 H hH hGRH hq)

/-- Under GRH, q ≥ 10^22097 and H proper, the least coprime outside prime is
at most (4/5)(log q-log log q)². Minimize the bounded subgroup witness.
Minimality is among all eligible primes and retains the same entrance and cutoff. -/
theorem exists_least_prime_outside_le_gamma_four_fifths_minus_loglog_22097 {q : ℕ}
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 22097 ≤ q) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q - Real.log (Real.log q)) ^ 2 ∧
        ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  exact
    exists_least_prime_outside_of_subgroup_cutoff H
      (PaperStatements.exists_prime_outside_le_gamma_four_fifths_minus_loglog_22097 H hH hGRH hq)

end PseudoPrime.LLS

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH and q ≥ 20000, rational a > 0 and signed rational b,c give
a coprime outside prime through a(log q+b log log q+c)² whenever the displayed
scale entrance and strict error budget hold. Rescale the common Gamma scale.
This research interface separates rational coefficient selection from the actual analytic budget. -/
theorem exists_prime_outside_le_rational_logarithmic_shift {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {a b c : ℚ} (ha : 0 < a)
    (hT :
      35000 ≤ Real.sqrt ((5 / 4 : ℝ) * (a : ℝ)) * Analysis.logarithmicShiftRoot (Real.log q) b c)
    (hbudget :
      let T := Real.sqrt ((5 / 4 : ℝ) * (a : ℝ)) * Analysis.logarithmicShiftRoot (Real.log q) b c;
      (11783423 / 25000000 : ℝ) * Real.log q + gammaScaleExcess (Real.log q) T + 40159 / 900 +
          2 *
            (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum ((32 / 99 : ℝ) * T ^ 2)
                ((4 / 5 : ℝ) * T ^ 2) q /
              Real.sqrt ((32 / 99 : ℝ) * T ^ 2)) <
        (11783423 / 25000000 + 1 / 795 : ℝ) * T) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        ¬residueInSubgroup q H p ∧
        (p : ℝ) ≤ Analysis.logarithmicShiftCutoff (Real.log q) a b c := by
  let T := Real.sqrt ((5 / 4 : ℝ) * (a : ℝ)) * Analysis.logarithmicShiftRoot (Real.log q) b c
  have haR : (0 : ℝ) ≤ (5 / 4 : ℝ) * (a : ℝ) :=
    mul_nonneg (by norm_num only) (by exact_mod_cast ha.le)
  have he : (4 / 5 : ℝ) * T ^ 2 = Analysis.logarithmicShiftCutoff (Real.log q) a b c := by
    dsimp only [T, Analysis.logarithmicShiftCutoff]
    rw [mul_pow, Real.sq_sqrt haR]
    ring
  obtain ⟨p, hp, hd, hout, hb⟩ :=
    exists_prime_outside_le_gamma_four_fifths_signed_scale hq H hH hGRH hT hbudget
  exact ⟨p, hp, hd, hout, he ▸ hb⟩

end PseudoPrime.LLS.PaperStatements
