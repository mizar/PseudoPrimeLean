/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation

/-! # Right limits of the closed-height zero count -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For nonnegative `t`, the closed-height zero ledger is locally constant to
the right. The finitely many zeros below `t + 1` have no new ordinate
arbitrarily close above `t`. -/
theorem zerosUpTo_eventually_right {t : ℝ} (ht : 0 ≤ t) :
    ∀ᶠ u in nhdsWithin t (Set.Ioi t), zerosUpTo u = zerosUpTo t := by
  classical
  have hsmall : ∀ᶠ u in nhdsWithin t (Set.Ioi t), u < t + 1 :=
    (eventually_lt_nhds (show t < t + 1 by linarith only)).filter_mono nhdsWithin_le_nhds
  have hright : ∀ᶠ u in nhdsWithin t (Set.Ioi t), t ≤ u :=
    eventually_mem_nhdsWithin.mono (fun _ h ↦ le_of_lt h)
  have havoid :
    ∀ᶠ u in nhdsWithin t (Set.Ioi t), ∀ ρ ∈ zerosUpTo (t + 1), t < |ρ.im| → u < |ρ.im| := by
    apply (Finset.eventually_all _).2
    intro ρ hρ
    by_cases h : t < |ρ.im|
    · exact ((eventually_lt_nhds h).filter_mono nhdsWithin_le_nhds).mono (fun _ hu _ ↦ hu)
    · exact Filter.Eventually.of_forall (fun _ hh ↦ (h hh).elim)
  filter_upwards [hsmall, hright, havoid] with u hu ht' hav
  apply Finset.Subset.antisymm
  · intro ρ hρ
    have hm := (mem_zerosUpTo (ht.trans ht')).1 hρ
    have hρ' : ρ ∈ zerosUpTo (t + 1) :=
      (mem_zerosUpTo (by linarith only [ht])).2 ⟨hm.1, hm.2.1, hm.2.2.trans hu.le⟩
    have hle : |ρ.im| ≤ t := by
      by_contra hn
      have hlt : t < |ρ.im| := lt_of_not_ge hn
      have hh := hav ρ hρ' hlt
      linarith only [hm.2.2, hh]
    exact (mem_zerosUpTo ht).2 ⟨hm.1, hm.2.1, hle⟩
  · exact zerosUpTo_mono ht ht'

/-- For nonnegative `t`, the positive-height multiplicity count is locally
constant immediately to the right, including when `t` is a zero ordinate. -/
theorem positiveZeroCount_eventually_right {t : ℝ} (ht : 0 ≤ t) :
    ∀ᶠ u in nhdsWithin t (Set.Ioi t), positiveZeroCount u = positiveZeroCount t := by
  exact (zerosUpTo_eventually_right ht).mono (fun _ hu ↦ positiveZeroCount_eq_of_zerosUpTo_eq hu)

/-- Immediately to the right of a nonnegative height, no point has the
positive ordinate of a nontrivial zeta zero. This includes an ordinate at
the left endpoint, whose multiplicity is already counted there. -/
theorem zero_ordinate_eventually_ne {t : ℝ} (ht : 0 ≤ t) :
    ∀ᶠ u in nhdsWithin t (Set.Ioi t), ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ u := by
  have heq := zerosUpTo_eventually_right ht
  have hgt : ∀ᶠ u in nhdsWithin t (Set.Ioi t), t < u := eventually_mem_nhdsWithin
  filter_upwards [heq, hgt] with u hu htu
  intro ρ hz hre h
  have hu0 : 0 ≤ u := ht.trans (le_of_lt htu)
  have him : |ρ.im| = u := by rw [h, abs_of_nonneg hu0]
  have hρ : ρ ∈ zerosUpTo u := (mem_zerosUpTo hu0).2 ⟨hz, hre, le_of_eq him⟩
  rw [hu] at hρ
  have hle := ((mem_zerosUpTo ht).1 hρ).2.2
  linarith only [him, hle, htu]

/-- A bound for the closed positive-height count, proved away from zero
ordinates above a nonnegative threshold, extends to every height when its
main term and error bound are continuous there. The right limit preserves
the multiplicity at a zero on the endpoint. -/
theorem positiveZeroCount_bound_of_good {a t : ℝ} {M E : ℝ → ℝ} (ha : 0 ≤ a) (hat : a ≤ t)
    (hM : ContinuousAt M t) (hE : ContinuousAt E t)
    (hgood :
      ∀ u : ℝ,
        a ≤ u →
          (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ u) → |positiveZeroCount u - M u| ≤ E u) :
    |positiveZeroCount t - M t| ≤ E t := by
  have ht : 0 ≤ t := ha.trans hat
  have hcount :
    Filter.Tendsto positiveZeroCount (nhdsWithin t (Set.Ioi t)) (nhds (positiveZeroCount t)) :=
    Filter.Tendsto.congr' ((positiveZeroCount_eventually_right ht).mono (fun _ h ↦ h.symm))
      tendsto_const_nhds
  have hmain := hM.tendsto.mono_left (nhdsWithin_le_nhds : nhdsWithin t (Set.Ioi t) ≤ nhds t)
  have herr := hE.tendsto.mono_left (nhdsWithin_le_nhds : nhdsWithin t (Set.Ioi t) ≤ nhds t)
  apply le_of_tendsto_of_tendsto (hcount.sub hmain).abs herr
  have hright : ∀ᶠ u in nhdsWithin t (Set.Ioi t), t ≤ u :=
    eventually_mem_nhdsWithin.mono (fun _ h ↦ le_of_lt h)
  filter_upwards [zero_ordinate_eventually_ne ht, hright] with u hu htu
  exact hgood u (hat.trans htu) hu

/-- If the logarithmic zero-count error holds at all nonzero ordinates above
`2πe`, it also holds at every zero ordinate. Continuity of the main term and
of the logarithm lets the closed count be approached from the right. -/
theorem positiveZeroCount_log_of_good
    (hgood :
      ∀ t : ℝ,
        2 * Real.pi * Real.exp 1 ≤ t →
          (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) →
          |positiveZeroCount t -
                (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
            Real.log t) :
    ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
      |positiveZeroCount t -
            (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
        Real.log t := by
  intro t ht
  have ha : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  have ht0 : 0 < t := lt_of_lt_of_le ha ht
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num only) Real.pi_pos)
  have hv : t / (2 * Real.pi) ≠ 0 := div_ne_zero ht0.ne' hpi
  have hdiv : ContinuousAt (fun u : ℝ ↦ u / (2 * Real.pi)) t := continuousAt_id.div_const _
  apply
    positiveZeroCount_bound_of_good ha.le ht
      (((hdiv.mul (hdiv.log hv)).sub hdiv).add continuousAt_const) (Real.continuousAt_log ht0.ne')
  exact hgood

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
