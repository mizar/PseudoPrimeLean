/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTailFinite

/-! # Splitting the inverse-square ordinate tail -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, for `0 ≤ a ≤ b`, the tail beyond `a` is the finite sum over
heights in `(a, b]` plus the tail beyond `b`. The closed upper ledger and
strict lower cutoff retain the correct multiplicities at both endpoints. -/
theorem ordinateTail_split (hRH : RiemannHypothesis) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ordinateTail a =
      (∑ ρ ∈ (zerosUpTo b).filter (fun ρ ↦ a < |ρ.im|),
          (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) +
        ordinateTail b := by
  classical
  have hb : 0 ≤ b := ha.trans hab
  have hout (ρ : ℂ) (hρ : ρ ∉ zerosUpTo b) :
    ordinateTailWeight a ρ - ordinateTailWeight b ρ = 0 := by
    by_cases hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
    · have hbig : b < |ρ.im| := by
        apply lt_of_not_ge
        intro hh
        exact hρ ((mem_zerosUpTo hb).2 ⟨hz.1, hz.2, hh⟩)
      have hsmall : a < |ρ.im| := lt_of_le_of_lt hab hbig
      simp only [ordinateTailWeight_eq, hz.1, hz.2, hsmall, hbig, and_self, ↓reduceIte, sub_self]
    · have ha' : ¬(riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ a < |ρ.im|) := fun h ↦ hz ⟨h.1, h.2.1⟩
      have hb' : ¬(riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ b < |ρ.im|) := fun h ↦ hz ⟨h.1, h.2.1⟩
      simp only [ordinateTailWeight_eq, ha', hb', ↓reduceIte, sub_self]
  have hsum :
    (∑' ρ : ℂ, (ordinateTailWeight a ρ - ordinateTailWeight b ρ)) =
      ∑ ρ ∈ (zerosUpTo b).filter (fun ρ ↦ a < |ρ.im|),
        (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2 := by
    rw [tsum_eq_sum (s := zerosUpTo b) hout, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hz := (mem_zerosUpTo hb).1 hρ
    have hnot : ¬b < |ρ.im| := not_lt_of_ge hz.2.2
    simp only [ordinateTailWeight_eq, hz.1, hz.2.1, hnot, true_and, and_false, ↓reduceIte, sub_zero]
  have hdiff := (ordinateTailWeight_summable hRH a).tsum_sub (ordinateTailWeight_summable hRH b)
  rw [← ordinateTail_eq, ← ordinateTail_eq] at hdiff
  exact (sub_eq_iff_eq_add).1 (hdiff.symm.trans hsum)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
