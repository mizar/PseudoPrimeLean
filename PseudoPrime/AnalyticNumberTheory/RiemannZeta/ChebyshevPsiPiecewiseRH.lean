/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPsiPiecewiseMillion
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidrangeTo15RH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiPost15MarginRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiPost20MarginRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevIntegratedMargin20RH
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPsiLeeNosalMillion

/-! # Conditional piecewise Lee–Nosal ψ envelope -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The normalized piecewise ψ envelope, with the breakpoints at 1423,
one million, `exp 15`, and `exp 20`. It combines the finite certificate,
the two phase margins, and the integrated envelope. -/
noncomputable def psiPiecewiseEnvelope (x : ℝ) : ℝ :=
  if x < 1423 then leeNosalPsiLog (Real.log x)
  else
    if x ≤ 1000000 then 4 / 5
    else
      if x < Real.exp 15 then leeNosalPsiLog (Real.log x) - 1 / 40
      else
        if x ≤ Real.exp 20 then leeNosalPsiLog (Real.log x) - 9 / 100
        else integratedPsiEnvelope (Real.log x)

/-- Under RH and the stated low-zero hypotheses, the normalized ψ error is
bounded by the complete piecewise envelope for every `x ≥ 101`. The proof
joins the independently certified finite, phase, and integrated branches. -/
theorem psi_piecewise_of_brackets (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {x : ℝ} (ha : 101 ≤ x) : |Chebyshev.psi x - x| / Real.sqrt x ≤ psiPiecewiseEnvelope x := by
  have hx : 0 < x := by linarith only [ha]
  unfold psiPiecewiseEnvelope
  split_ifs with h1 h2 h3 h4
  · exact Arithmetic.psi_normalized_101_1423 ha h1
  · exact Arithmetic.psi_normalized_1423_million (le_of_not_gt h1) h2
  · exact
      psi_midrange_margin_to_15 hRH g hmono hpos hheight hzero hcount hl hu (le_of_not_ge h2)
        (Real.log_le_iff_le_exp hx |>.2 h3.le)
  · exact
      psi_midrange_margin_15_20_of_brackets hRH g hmono hpos hheight hzero hcount hl hu hx
        (le_of_not_gt ((Real.log_lt_iff_lt_exp hx).not.mpr h3)) ((Real.log_le_iff_le_exp hx).2 h4)
  · exact
      (psi_integrated_envelope_of_brackets hRH g hmono hpos hheight hzero hcount hl hx
          (by
            have h := (Real.log_le_iff_le_exp hx).not.mpr h4
            linarith only [h])).1

/-- Under RH and the stated low-zero hypotheses, the normalized ψ error
is bounded by the Lee–Nosal logarithmic envelope for all `x ≥ 101`.
The finite interval is unconditional; the remaining intervals use the
corresponding phase or integrated margin. -/
theorem psi_lee_nosal_of_brackets (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {x : ℝ} (ha : 101 ≤ x) : |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) := by
  have hx : 0 < x := by linarith only [ha]
  by_cases hs : x ≤ 1000000
  · apply (div_le_iff₀ (Real.sqrt_pos.2 hx)).2
    have h := Arithmetic.psi_lee_nosal_101_million ha hs
    dsimp only [leeNosalPsiLog]
    linarith only [h]
  · by_cases hm : Real.log x ≤ 15
    · have h :=
        psi_midrange_margin_to_15 hRH g hmono hpos hheight hzero hcount hl hu (le_of_not_ge hs) hm
      linarith only [h]
    · by_cases ht : Real.log x ≤ 20
      · have h :=
          psi_midrange_margin_15_20_of_brackets hRH g hmono hpos hheight hzero hcount hl hu hx
            (le_of_not_ge hm) ht
        linarith only [h]
      · have h :=
          psi_integrated_margin20_of_brackets hRH g hmono hpos hheight hzero hcount hl hx
            (le_of_not_ge ht)
        linarith only [h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
