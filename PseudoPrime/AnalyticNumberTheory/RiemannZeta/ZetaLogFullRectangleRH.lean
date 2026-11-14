/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaLogRectangleRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.EulerLogTail

/-! # Finite left edge and full horizontal logarithmic tails -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, one Euler-normalized logarithm gives a rectangle identity
whose horizontal sides include both the finite part and the tail to
infinity. Its left-edge imaginary part converges almost everywhere to the
count-defined argument at heights at least 100. -/
theorem exists_full_rectangle_with_boundary (hRH : RiemannHypothesis) :
    ∃ f : ℂ → ℂ,
      (∀ a u v : ℝ,
          1 / 2 < a →
            a ≤ 2 →
            1 < u →
            u ≤ v →
            ((∫ x in a..(2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (v : ℂ) * Complex.I)‖) -
                  (∫ x in a..(2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (u : ℂ) * Complex.I)‖)) +
                ((∫ x in Set.Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (v : ℂ) * Complex.I)‖) -
                  (∫ x in Set.Ioi (2 : ℝ),
                    Real.log ‖riemannZeta ((x : ℂ) + (u : ℂ) * Complex.I)‖)) =
              ∫ y in u..v, (f ((a : ℂ) + (y : ℂ) * Complex.I)).im) ∧
        ∀ᵐ t : ℝ,
          100 ≤ t →
            Filter.Tendsto (fun a : ℝ ↦ (f ((a : ℂ) + (t : ℂ) * Complex.I)).im)
              (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (nhds (Real.pi * zetaArgCount t)) := by
  obtain ⟨f, hrect, hboundary⟩ := exists_zeta_log_rectangle_with_boundary hRH
  refine ⟨f, ?_, hboundary⟩
  intro a u v ha ha2 hu huv
  have h := hrect a u v ha ha2 hu huv
  have htail := zeta_log_tail_rectangle huv
  linarith only [h, htail]

/-- Under RH, the vertical integral of a common normalized logarithm has a
finite limit as its real part approaches one half from the right. The limit
is the difference of the full horizontal logarithmic integrals, split at
two. Its pointwise boundary value agrees almost everywhere with the count
argument; identifying the limit with the integral of that boundary value
requires a separate limit-interchange argument. -/
theorem exists_vertical_limit_with_boundary (hRH : RiemannHypothesis) :
    ∃ f : ℂ → ℂ,
      (∀ u v : ℝ,
          100 ≤ u →
            u ≤ v →
            Filter.Tendsto (fun a : ℝ ↦ ∫ y in u..v, (f ((a : ℂ) + (y : ℂ) * Complex.I)).im)
              (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)))
              (nhds
                (((∫ x in (1 / 2 : ℝ)..2, Real.log ‖riemannZeta ((x : ℂ) + (v : ℂ) * Complex.I)‖) -
                    (∫ x in (1 / 2 : ℝ)..2,
                      Real.log ‖riemannZeta ((x : ℂ) + (u : ℂ) * Complex.I)‖)) +
                  ((∫ x in Set.Ioi (2 : ℝ),
                      Real.log ‖riemannZeta ((x : ℂ) + (v : ℂ) * Complex.I)‖) -
                    (∫ x in Set.Ioi (2 : ℝ),
                      Real.log ‖riemannZeta ((x : ℂ) + (u : ℂ) * Complex.I)‖))))) ∧
        ∀ᵐ t : ℝ,
          100 ≤ t →
            Filter.Tendsto (fun a : ℝ ↦ (f ((a : ℂ) + (t : ℂ) * Complex.I)).im)
              (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (nhds (Real.pi * zetaArgCount t)) := by
  obtain ⟨f, hrect, hboundary⟩ := exists_full_rectangle_with_boundary hRH
  refine ⟨f, ?_, hboundary⟩
  intro u v hu huv
  have hu0 : u ≠ 0 := (show (0 : ℝ) < u by linarith only [hu]).ne'
  have hv0 : v ≠ 0 := (show (0 : ℝ) < v by linarith only [hu, huv]).ne'
  have hlim :=
    ((tendsto_horizontal_logZeta_left hRH hv0).sub
          (tendsto_horizontal_logZeta_left hRH hu0)).add_const
      ((∫ x in Set.Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (v : ℂ) * Complex.I)‖) -
        (∫ x in Set.Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (u : ℂ) * Complex.I)‖))
  apply hlim.congr'
  have hlo : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), 1 / 2 < a := self_mem_nhdsWithin
  have hhi : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), a < 2 :=
    (eventually_lt_nhds (by norm_num only : (1 / 2 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hlo, hhi] with a ha ha2
  exact hrect a u v ha ha2.le (by linarith only [hu]) huv

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
