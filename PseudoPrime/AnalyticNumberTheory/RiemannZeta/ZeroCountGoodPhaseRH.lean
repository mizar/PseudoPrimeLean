/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountArgumentRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.EulerLog
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundRiemannVonMangoldt
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundNormalizedPhase
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCounting

/-! # Euler-normalized count argument at good heights -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, at a good height at least 100, every Euler-normalized
continuous horizontal zeta argument has central value π times the
count-defined argument. The Riemann–von Mangoldt identity supplies the
count, and its gamma and constant terms cancel. -/
theorem count_arg_eq_euler_phase (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) (φ : ℝ → ℝ)
    (hc : ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)))
    (hp :
      ∀ x : ℝ,
        x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
          riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I) =
            (‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I))
    (hn : φ (3 / 2) = (backlundZetaLog (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im) :
    Real.pi * zetaArgCount t = φ (1 / 2) := by
  have hbase : 2 * Real.pi * Real.exp 1 ≤ t := by
    have hm :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hm, ht]
  have hv := euler_riemann_von_mangoldt_of_RH hRH t hbase hgood φ hc hp hn
  rw [zetaArgCount, hv]
  field_simp
  ring

/-- Under RH, each good height at least 100 admits an Euler-normalized
continuous horizontal argument whose central value is π times the
count-defined argument. This supplies the normalization needed to identify
the latter with the boundary value of a holomorphic zeta logarithm. -/
theorem exists_euler_phase_of_count (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)) ∧
        (∀ x : ℝ,
          x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
            riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I) =
              (‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) *
                Complex.exp ((φ x : ℂ) * Complex.I)) ∧
        φ (3 / 2) = (backlundZetaLog (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im ∧
        Real.pi * zetaArgCount t = φ (1 / 2) := by
  obtain ⟨φ, hc, hp, hn⟩ := exists_euler_normalized_arg (show 0 < t by linarith only [ht]) hgood
  exact ⟨φ, hc, hp, hn, count_arg_eq_euler_phase hRH ht hgood φ hc hp hn⟩

/-- The set of all complex zeta zeros is countable. Each intersection with
a closed ball is finite by the compact-zero theorem, and the balls exhaust
the complex plane. -/
theorem countable_riemannZeta_zeros : (riemannZeta ⁻¹' ({0} : Set ℂ)).Countable := by
  apply
    Set.Countable.mono (s₂ :=
      ⋃ n : ℕ, Metric.closedBall (0 : ℂ) (n : ℝ) ∩ riemannZeta ⁻¹' ({0} : Set ℂ)) ?_
      (Set.countable_iUnion
        (fun n ↦
          (finite_riemannZeta_zerosOn_compact (isCompact_closedBall (0 : ℂ) (n : ℝ))).countable))
  intro z hz
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  apply Set.mem_iUnion.mpr
  refine ⟨n, ?_, hz⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hn.le

/-- Almost every real height avoids all zeta zeros. The exceptional
ordinates are the image of the countable zero set and have zero Lebesgue
measure. This permits replacement of count-defined arguments by good-height
boundary phases inside integrals. -/
theorem ae_zeta_good_height : ∀ᵐ t : ℝ, ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t := by
  have hc : (Complex.im '' (riemannZeta ⁻¹' ({0} : Set ℂ))).Countable :=
    countable_riemannZeta_zeros.image Complex.im
  have hz : MeasureTheory.volume (Complex.im '' (riemannZeta ⁻¹' ({0} : Set ℂ))) = 0 :=
    hc.measure_zero MeasureTheory.volume
  apply MeasureTheory.ae_iff.mpr
  apply MeasureTheory.measure_mono_null _ hz
  intro t ht
  simp only [Set.mem_ofPred_eq, not_forall, Classical.not_not] at ht
  obtain ⟨ρ, hρ, hre, him⟩ := ht
  exact ⟨ρ, hρ, him⟩

/-- Under RH, almost every height at least 100 admits an Euler-normalized
continuous zeta phase whose central value is π times the count-defined
argument. The exceptional zero ordinates form a null set. -/
theorem ae_exists_euler_phase_of_count (hRH : RiemannHypothesis) :
    ∀ᵐ t : ℝ,
      100 ≤ t →
        ∃ φ : ℝ → ℝ,
          ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)) ∧
            (∀ x : ℝ,
              x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
                riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I) =
                  (‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) *
                    Complex.exp ((φ x : ℂ) * Complex.I)) ∧
            φ (3 / 2) = (backlundZetaLog (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im ∧
            Real.pi * zetaArgCount t = φ (1 / 2) := by
  filter_upwards [ae_zeta_good_height] with t hgood ht
  exact exists_euler_phase_of_count hRH ht hgood

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
