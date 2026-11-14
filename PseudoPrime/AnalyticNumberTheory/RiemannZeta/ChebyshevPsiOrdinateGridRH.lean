/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinateInterpolation
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiPhaseGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhaseGrid100

/-! # Two-dimensional interpolation for the signed zero head -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The second-derivative interpolation allowance for one ordinate bracket.
It depends on the phase range V and the bracket endpoints a and b. -/
@[expose]
noncomputable def ordinateCellError (V a b : ℝ) : ℝ :=
  (2 * (V ^ 2 / a + 2 * V / a ^ 2 + 2 / a ^ 3)) * (b - a) ^ 2 / 128

/-- Five ordinate samples at every logarithmic grid node, together with
their summed error budgets, bound the head phase on the entire log interval.
The additional term is the log-direction interpolation error. -/
theorem phase100_le_of_ordinate_grid (g a b : Fin 29 → ℝ) (lo hi : ℕ → Fin 29 → ℝ) (A V B : ℝ)
    (N : ℕ) (hpos : ∀ i, 0 ≤ g i) (hu : LowZero100UpperBounds g) (ha : ∀ i, 0 < a i)
    (hab : ∀ i, a i < b i) (hg : ∀ i, g i ∈ Set.Icc (a i) (b i))
    (hV : ∀ j : ℕ, j ≤ N → |A + (j : ℝ) / 250| ≤ V)
    (hnodes :
      ∀ (j : ℕ),
        j ≤ N →
          ∀ i (k : ℕ),
            k ≤ 4 →
              lo j i ≤ ordinateTerm (A + (j : ℝ) / 250) (a i + (k : ℝ) * (b i - a i) / 4) ∧
                ordinateTerm (A + (j : ℝ) / 250) (a i + (k : ℝ) * (b i - a i) / 4) ≤ hi j i)
    (hbudget :
      ∀ (j : ℕ),
        j ≤ N →
          -B ≤ ∑ i, (lo j i - ordinateCellError V (a i) (b i)) ∧
            (∑ i, (hi j i + ordinateCellError V (a i) (b i))) ≤ B)
    {v : ℝ} (hv : v ∈ Set.Icc A (A + (N : ℝ) / 250)) : |zeroHeadPhase g v| ≤ B + 3611 / 500000 := by
  apply phase100_le_of_grid g hpos hu hv
  intro j hj
  have h :=
    zeroHeadPhase_four_cells g a b (lo j) (hi j) (A + (j : ℝ) / 250) V ha hab hg (hV j hj)
      (hnodes j hj)
  have hb := hbudget j hj
  simp only [ordinateCellError] at hb
  apply abs_le.mpr
  constructor <;> linarith only [h.1, h.2, hb.1, hb.2]

/-- Under RH and the stated height-100 zero hypotheses, certified ordinate
samples at each logarithmic grid node imply the smoothed ψ error bound.
Both ordinate and logarithmic interpolation costs are included. -/
theorem psi_error_ordinate_grid (hRH : RiemannHypothesis) (g left right : Fin 29 → ℝ)
    (lo hi : ℕ → Fin 29 → ℝ) (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {T x h D a B V : ℝ} {N : ℕ} (hT : 100 ≤ T) (hh : 0 < h) (hx : 1 < x - h) (hD : 0 ≤ D)
    (hsqrt : Real.sqrt (x + h) ≤ D) (htail : ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h ≤ D * T)
    (hlo : Real.log ((x - h + x) / 2) ∈ Set.Icc a (a + (N : ℝ) / 250))
    (hhi : Real.log ((x + (x + h)) / 2) ∈ Set.Icc a (a + (N : ℝ) / 250)) (ha : ∀ i, 0 < left i)
    (hab : ∀ i, left i < right i) (hg : ∀ i, g i ∈ Set.Icc (left i) (right i))
    (hV : ∀ j : ℕ, j ≤ N → |a + (j : ℝ) / 250| ≤ V)
    (hnodes :
      ∀ (j : ℕ),
        j ≤ N →
          ∀ i (k : ℕ),
            k ≤ 4 →
              lo j i ≤
                  ordinateTerm (a + (j : ℝ) / 250) (left i + (k : ℝ) * (right i - left i) / 4) ∧
                ordinateTerm (a + (j : ℝ) / 250) (left i + (k : ℝ) * (right i - left i) / 4) ≤
                  hi j i)
    (hbudget :
      ∀ (j : ℕ),
        j ≤ N →
          -B ≤ ∑ i, (lo j i - ordinateCellError V (left i) (right i)) ∧
            (∑ i, (hi j i + ordinateCellError V (left i) (right i))) ≤ B) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        (Real.sqrt (x + h) * (B + 3611 / 500000) + 3640 * (x - h) ^ (-(3 / 2 : ℝ)) * h ^ 2 / 24) +
        D *
          (((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / T +
            1 / (15 * T ^ 2)) +
        1 / h := by
  apply psi_error_phase_brackets hRH g hmono hpos hheight hzero hcount hl hu hT hh hx hD hsqrt htail
  · exact
      phase100_le_of_ordinate_grid g left right lo hi a V B N (fun i ↦ (hpos i).le) hu ha hab hg hV
        hnodes hbudget hlo
  · exact
      phase100_le_of_ordinate_grid g left right lo hi a V B N (fun i ↦ (hpos i).le) hu ha hab hg hV
        hnodes hbudget hhi

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
