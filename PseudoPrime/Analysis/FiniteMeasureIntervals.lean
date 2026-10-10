/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Weak convergence of finite measures from real interval masses

Convergence on half-open intervals, together with total-mass convergence, implies weak
convergence. Normalization reduces the nonzero case to the probability-measure pi-system API.
The resulting bounded continuous integral interface supports weighted arithmetic limits.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a nonzero limiting finite measure, convergence of total masses and masses of
all half-open real intervals implies weak convergence. Normalize by the total mass and
apply the probability-measure pi-system criterion; interval neighborhoods supply its basis.
This is the nonzero case of the weighted-integral convergence interface. -/
private theorem tendsto_finiteMeasure_of_nonzero_mass_and_Ioc {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (μ : ι → MeasureTheory.FiniteMeasure ℝ)
    (ν : MeasureTheory.FiniteMeasure ℝ) (hν : ν ≠ 0)
    (hmass : Filter.Tendsto (fun i ↦ (μ i).mass) l (nhds ν.mass))
    (hinterval :
      ∀ a b : ℝ, a < b → Filter.Tendsto (fun i ↦ μ i (Set.Ioc a b)) l (nhds (ν (Set.Ioc a b)))) :
    Filter.Tendsto μ l (nhds ν) := by
  have hmne := ν.mass_nonzero_iff.mpr hν
  have he := hmass.eventually_ne hmne
  have hn : Filter.Tendsto (fun i ↦ (μ i).normalize) l (nhds ν.normalize) := by
    apply (isPiSystem_Ioc (id : ℝ → ℝ) (id : ℝ → ℝ)).tendsto_probabilityMeasure_of_tendsto_of_mem
    · rintro s ⟨a, b, _, rfl⟩
      exact measurableSet_Ioc
    · intro u hu x hx
      obtain ⟨a, b, hx', hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hx)
      refine ⟨Set.Ioc a ((x + b) / 2), ⟨a, (x + b) / 2, ?_, rfl⟩, Ioc_mem_nhds hx'.1 ?_, ?_⟩
      · change a < (x + b) / 2
        linarith only [hx'.1, hx'.2]
      · linarith only [hx'.2]
      · intro y hy
        exact hab ⟨hy.1, by linarith only [hy.2, hx'.2]⟩
    · rintro s ⟨a, b, hab, rfl⟩
      have ht := (hmass.inv₀ hmne).mul (hinterval a b hab)
      rw [ν.normalize_eq_of_nonzero hν]
      apply ht.congr'
      filter_upwards [he] with i hi
      exact ((μ i).normalize_eq_of_nonzero ((μ i).mass_nonzero_iff.mp hi) (Set.Ioc a b)).symm
  exact
    MeasureTheory.FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass hn hmass

/-- If total masses and masses of every half-open real interval converge, the finite
measures converge weakly. The zero case follows from vanishing total mass; the nonzero case
uses normalized probability measures. No arithmetic or positivity of the limiting mass
is required, so the result also handles empty cutoff intervals. -/
theorem tendsto_finiteMeasure_of_mass_and_Ioc {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (μ : ι → MeasureTheory.FiniteMeasure ℝ) (ν : MeasureTheory.FiniteMeasure ℝ)
    (hmass : Filter.Tendsto (fun i ↦ (μ i).mass) l (nhds ν.mass))
    (hinterval :
      ∀ a b : ℝ, a < b → Filter.Tendsto (fun i ↦ μ i (Set.Ioc a b)) l (nhds (ν (Set.Ioc a b)))) :
    Filter.Tendsto μ l (nhds ν) := by
  by_cases hν : ν = 0
  · subst ν
    exact MeasureTheory.FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hmass
  · exact tendsto_finiteMeasure_of_nonzero_mass_and_Ioc μ ν hν hmass hinterval

/-- Under total-mass and half-open-interval mass convergence, integrals of every bounded
continuous real test function converge. Apply the weak-convergence criterion and its integral
characterization. This transfers interval arithmetic limits to continuous cutoff weights. -/
theorem tendsto_integral_of_mass_and_Ioc {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (μ : ι → MeasureTheory.FiniteMeasure ℝ) (ν : MeasureTheory.FiniteMeasure ℝ)
    (hmass : Filter.Tendsto (fun i ↦ (μ i).mass) l (nhds ν.mass))
    (hinterval :
      ∀ a b : ℝ, a < b → Filter.Tendsto (fun i ↦ μ i (Set.Ioc a b)) l (nhds (ν (Set.Ioc a b))))
    (f : BoundedContinuousFunction ℝ ℝ) :
    Filter.Tendsto (fun i ↦ ∫ u, f u ∂(μ i : MeasureTheory.Measure ℝ)) l
      (nhds (∫ u, f u ∂(ν : MeasureTheory.Measure ℝ))) := by
  exact
    MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
      (tendsto_finiteMeasure_of_mass_and_Ioc μ ν hmass hinterval) f

/-- Lebesgue measure restricted to a finite half-open real interval, viewed as a finite
measure. Its total mass is the positive part of the interval length. This is the limiting
measure for normalized arithmetic sums on a fixed scaled interval. -/
noncomputable def intervalVolume (a b : ℝ) : MeasureTheory.FiniteMeasure ℝ :=
  ⟨MeasureTheory.volume.restrict (Set.Ioc a b), inferInstance⟩

/-- The real mass of a half-open interval under restricted interval volume is the positive
part of the intersection length. Intersect the intervals and evaluate Lebesgue measure.
This identifies limiting interval masses in the weak-convergence criterion. -/
theorem intervalVolume_Ioc_real (a b c d : ℝ) :
    (intervalVolume a b (Set.Ioc c d) : ℝ) = max (min b d - max a c) 0 := by
  rw [← MeasureTheory.FiniteMeasure.measureReal_eq_coe_coeFn]
  change (MeasureTheory.volume.restrict (Set.Ioc a b)).real (Set.Ioc c d) = _
  rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply measurableSet_Ioc,
    Set.Ioc_inter_Ioc, Real.volume_Ioc, ENNReal.toReal_ofReal']
  rw [min_comm d b, max_comm c a]

/-- For ordered endpoints, restricted interval volume has total mass equal to their
difference. Evaluate its restriction on the whole line. This matches normalized sums
whose endpoint asymptotics give the same interval length. -/
theorem intervalVolume_mass_real {a b : ℝ} (hab : a ≤ b) :
    ((intervalVolume a b).mass : ℝ) = b - a := by
  rw [MeasureTheory.FiniteMeasure.mass, ← MeasureTheory.FiniteMeasure.measureReal_eq_coe_coeFn]
  change (MeasureTheory.volume.restrict (Set.Ioc a b)).real Set.univ = _
  rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

end PseudoPrime.Analysis
