/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinateRotation
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRationalGridRH

/-! # Sequential phase walks for the signed zero head and ψ error -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Successful sequential checks for each rational ordinate sample bound
all real node values in the logarithmic grid. -/
theorem ordinate_grid_nodes_of_walks (A : ℚ) (a b : Fin 29 → ℚ) (lo hi : ℕ → Fin 29 → ℚ) (N : ℕ)
    (hN : N ≤ 1600) (hA : |(A : ℝ)| ≤ 21)
    (hq :
      ∀ i (k : ℕ),
        k ≤ 4 →
          let q := a i + (k : ℚ) * (b i - a i) / 4
          (0 : ℝ) < q ∧ (q : ℝ) ≤ 100)
    (hc :
      ∀ i (k : ℕ),
        k ≤ 4 →
          rotationOrdinateGridCheck A (a i + (k : ℚ) * (b i - a i) / 4) (fun j ↦ lo j i)
              (fun j ↦ hi j i) N =
            true) :
    ∀ (j : ℕ),
      j ≤ N →
        ∀ i (k : ℕ),
          k ≤ 4 →
            (lo j i : ℝ) ≤
                ordinateTerm ((A : ℝ) + (j : ℝ) / 250)
                  ((a i : ℝ) + (k : ℝ) * ((b i : ℝ) - (a i : ℝ)) / 4) ∧
              ordinateTerm ((A : ℝ) + (j : ℝ) / 250)
                  ((a i : ℝ) + (k : ℝ) * ((b i : ℝ) - (a i : ℝ)) / 4) ≤
                (hi j i : ℝ) := by
  intro j hj i k hk
  have h :=
    rotationOrdinateGridCheck_sound A (a i + (k : ℚ) * (b i - a i) / 4) (fun j ↦ lo j i)
      (fun j ↦ hi j i) (hq i k hk).1 (hq i k hk).2 hA hN (hc i k hk) j hj
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_natCast] at h
  exact h

/-- Sequential rational checks and summed budgets bound the signed zero
head throughout a logarithmic grid interval. -/
theorem phase100_le_of_rotation_walks (g : Fin 29 → ℝ) (A B : ℚ) (a b : Fin 29 → ℚ)
    (lo hi : ℕ → Fin 29 → ℚ) (N : ℕ) (hpos : ∀ i, 0 ≤ g i) (hu : LowZero100UpperBounds g)
    (ha : ∀ i, (0 : ℝ) < a i) (hab : ∀ i, (a i : ℝ) < b i)
    (hg : ∀ i, g i ∈ Set.Icc (a i : ℝ) (b i : ℝ)) (hN : N ≤ 1600) (hA : |(A : ℝ)| ≤ 21)
    (hv : ∀ j : ℕ, j ≤ N → |((A + (j : ℚ) / 250 : ℚ) : ℝ)| ≤ 21)
    (hq :
      ∀ i (k : ℕ),
        k ≤ 4 →
          let q := a i + (k : ℚ) * (b i - a i) / 4
          (0 : ℝ) < q ∧ (q : ℝ) ≤ 100)
    (hc :
      ∀ i (k : ℕ),
        k ≤ 4 →
          rotationOrdinateGridCheck A (a i + (k : ℚ) * (b i - a i) / 4) (fun j ↦ lo j i)
              (fun j ↦ hi j i) N =
            true)
    (hb : ∀ (j : ℕ), j ≤ N → rationalOrdinateBudgetCheck B 21 a b (lo j) (hi j) = true) {v : ℝ}
    (hgrid : v ∈ Set.Icc (A : ℝ) ((A : ℝ) + (N : ℝ) / 250)) :
    |zeroHeadPhase g v| ≤ (B : ℝ) + 3611 / 500000 := by
  apply
    phase100_le_of_ordinate_grid g (fun i ↦ (a i : ℝ)) (fun i ↦ (b i : ℝ)) (fun j i ↦ (lo j i : ℝ))
      (fun j i ↦ (hi j i : ℝ)) (A : ℝ) 21 (B : ℝ) N hpos hu ha hab hg
  · intro j hj
    have h := hv j hj
    norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at h
    exact h
  · exact ordinate_grid_nodes_of_walks A a b lo hi N hN hA hq hc
  · intro j hj
    have h := rationalOrdinateBudgetCheck_sound B 21 a b (lo j) (hi j) (hb j hj)
    norm_num only [Rat.cast_ofNat] at h
    exact h
  · exact hgrid

/-- Under RH and the stated height-100 zero hypotheses, successful
sequential rational checks imply the smoothed ψ error bound. -/
theorem psi_error_rotation_walks (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (A Br : ℚ)
    (a b : Fin 29 → ℚ) (lo hi : ℕ → Fin 29 → ℚ) (hmono : StrictMono g) (hpos : ∀ i, 0 < g i)
    (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {T x h D : ℝ} {N : ℕ} (hT : 100 ≤ T) (hh : 0 < h) (hx : 1 < x - h) (hD : 0 ≤ D)
    (hsqrt : Real.sqrt (x + h) ≤ D) (htail : ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h ≤ D * T)
    (hlo : Real.log ((x - h + x) / 2) ∈ Set.Icc (A : ℝ) ((A : ℝ) + (N : ℝ) / 250))
    (hhi : Real.log ((x + (x + h)) / 2) ∈ Set.Icc (A : ℝ) ((A : ℝ) + (N : ℝ) / 250))
    (ha : ∀ i, (0 : ℝ) < a i) (hab : ∀ i, (a i : ℝ) < b i)
    (hg : ∀ i, g i ∈ Set.Icc (a i : ℝ) (b i : ℝ)) (hN : N ≤ 1600) (hA : |(A : ℝ)| ≤ 21)
    (hv : ∀ j : ℕ, j ≤ N → |((A + (j : ℚ) / 250 : ℚ) : ℝ)| ≤ 21)
    (hq :
      ∀ i (k : ℕ),
        k ≤ 4 →
          let q := a i + (k : ℚ) * (b i - a i) / 4
          (0 : ℝ) < q ∧ (q : ℝ) ≤ 100)
    (hc :
      ∀ i (k : ℕ),
        k ≤ 4 →
          rotationOrdinateGridCheck A (a i + (k : ℚ) * (b i - a i) / 4) (fun j ↦ lo j i)
              (fun j ↦ hi j i) N =
            true)
    (hb : ∀ (j : ℕ), j ≤ N → rationalOrdinateBudgetCheck Br 21 a b (lo j) (hi j) = true) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        (Real.sqrt (x + h) * ((Br : ℝ) + 3611 / 500000) +
          3640 * (x - h) ^ (-(3 / 2 : ℝ)) * h ^ 2 / 24) +
        D *
          (((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / T +
            1 / (15 * T ^ 2)) +
        1 / h := by
  apply psi_error_phase_brackets hRH g hmono hpos hheight hzero hcount hl hu hT hh hx hD hsqrt htail
  · exact
      phase100_le_of_rotation_walks g A Br a b lo hi N (fun i ↦ (hpos i).le) hu ha hab hg hN hA hv
        hq hc hb hlo
  · exact
      phase100_le_of_rotation_walks g A Br a b lo hi N (fun i ↦ (hpos i).le) hu ha hab hg hN hA hv
        hq hc hb hhi

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
