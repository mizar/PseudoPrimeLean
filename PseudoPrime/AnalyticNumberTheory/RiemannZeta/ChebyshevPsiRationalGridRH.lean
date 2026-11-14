/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinateRational
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiOrdinateGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiPhaseGridRH

/-! # Rational finite checks for the signed zero head and ψ error -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Successful rational checks bound every real ordinate node on a logarithmic grid.
The height and ordinate restrictions ensure the uniform evaluator error. -/
theorem ordinate_grid_nodes_of_checks (A : ℚ) (a b : Fin 29 → ℚ) (lo hi : ℕ → Fin 29 → ℚ) (N : ℕ)
    (hv : ∀ j : ℕ, j ≤ N → |((A + (j : ℚ) / 250 : ℚ) : ℝ)| ≤ 21)
    (hq :
      ∀ i (k : ℕ),
        k ≤ 4 →
          let q := a i + (k : ℚ) * (b i - a i) / 4
          (0 : ℝ) < q ∧ (q : ℝ) ≤ 100)
    (hc :
      ∀ (j : ℕ),
        j ≤ N →
          ∀ i (k : ℕ),
            k ≤ 4 →
              rationalOrdinateNodeCheck (A + (j : ℚ) / 250) (a i + (k : ℚ) * (b i - a i) / 4)
                  (lo j i) (hi j i) (10 ^ 12) 16 12 =
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
    rationalOrdinateNodeCheck_100 (A + (j : ℚ) / 250) (a i + (k : ℚ) * (b i - a i) / 4) (lo j i)
      (hi j i) (hq i k hk).1 (hq i k hk).2 (hv j hj) (hc j hj i k hk)
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_natCast] at h
  exact h

/-- Rational form of the ordinate-direction quadratic interpolation cost. -/
@[expose]
def rationalOrdinateCellError (V a b : ℚ) : ℚ :=
  (2 * (V ^ 2 / a + 2 * V / a ^ 2 + 2 / a ^ 3)) * (b - a) ^ 2 / 128

/-- Decide the two summed rational error budgets for one logarithmic grid node. -/
@[expose]
def rationalOrdinateBudgetCheck (B V : ℚ) (a b lo hi : Fin 29 → ℚ) : Bool :=
  decide
    (-B ≤ ∑ i, (lo i - rationalOrdinateCellError V (a i) (b i)) ∧
      (∑ i, (hi i + rationalOrdinateCellError V (a i) (b i))) ≤ B)

/-- A successful rational budget check proves the corresponding real inequalities. -/
theorem rationalOrdinateBudgetCheck_sound (B V : ℚ) (a b lo hi : Fin 29 → ℚ)
    (hc : rationalOrdinateBudgetCheck B V a b lo hi = true) :
    -(B : ℝ) ≤ ∑ i, ((lo i : ℝ) - ordinateCellError (V : ℝ) (a i : ℝ) (b i : ℝ)) ∧
      (∑ i, ((hi i : ℝ) + ordinateCellError (V : ℝ) (a i : ℝ) (b i : ℝ))) ≤ (B : ℝ) := by
  have h := of_decide_eq_true hc
  change
    -B ≤ ∑ i, (lo i - rationalOrdinateCellError V (a i) (b i)) ∧
      (∑ i, (hi i + rationalOrdinateCellError V (a i) (b i))) ≤ B at h
  have h1 := (Rat.cast_le (K := ℝ)).mpr h.1
  have h2 := (Rat.cast_le (K := ℝ)).mpr h.2
  simp only [Rat.cast_neg, Rat.cast_sum, Rat.cast_sub, Rat.cast_add, rationalOrdinateCellError,
    Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Rational node and budget checks bound the signed zero head throughout
its logarithmic grid interval, including both interpolation errors. -/
theorem phase100_le_of_rational_grid (g : Fin 29 → ℝ) (A B : ℚ) (a b : Fin 29 → ℚ)
    (lo hi : ℕ → Fin 29 → ℚ) (N : ℕ) (hpos : ∀ i, 0 ≤ g i) (hu : LowZero100UpperBounds g)
    (ha : ∀ i, (0 : ℝ) < a i) (hab : ∀ i, (a i : ℝ) < b i)
    (hg : ∀ i, g i ∈ Set.Icc (a i : ℝ) (b i : ℝ))
    (hv : ∀ j : ℕ, j ≤ N → |((A + (j : ℚ) / 250 : ℚ) : ℝ)| ≤ 21)
    (hq :
      ∀ i (k : ℕ),
        k ≤ 4 →
          let q := a i + (k : ℚ) * (b i - a i) / 4
          (0 : ℝ) < q ∧ (q : ℝ) ≤ 100)
    (hc :
      ∀ (j : ℕ),
        j ≤ N →
          ∀ i (k : ℕ),
            k ≤ 4 →
              rationalOrdinateNodeCheck (A + (j : ℚ) / 250) (a i + (k : ℚ) * (b i - a i) / 4)
                  (lo j i) (hi j i) (10 ^ 12) 16 12 =
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
  · exact ordinate_grid_nodes_of_checks A a b lo hi N hv hq hc
  · intro j hj
    have h := rationalOrdinateBudgetCheck_sound B 21 a b (lo j) (hi j) (hb j hj)
    norm_num only [Rat.cast_ofNat] at h
    exact h
  · exact hgrid

/-- Under RH and the explicit height-100 zero hypotheses, successful rational
node and budget checks yield the stated smoothed ψ error on the grid interval. -/
theorem psi_error_rational_grid (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (A Br : ℚ)
    (a b : Fin 29 → ℚ) (lo hi : ℕ → Fin 29 → ℚ) (hmono : StrictMono g) (hpos : ∀ i, 0 < g i)
    (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {T x h D : ℝ} {N : ℕ} (hT : 100 ≤ T) (hh : 0 < h) (hx : 1 < x - h) (hD : 0 ≤ D)
    (hsqrt : Real.sqrt (x + h) ≤ D) (htail : ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h ≤ D * T)
    (hlo : Real.log ((x - h + x) / 2) ∈ Set.Icc (A : ℝ) ((A : ℝ) + (N : ℝ) / 250))
    (hhi : Real.log ((x + (x + h)) / 2) ∈ Set.Icc (A : ℝ) ((A : ℝ) + (N : ℝ) / 250))
    (ha : ∀ i, (0 : ℝ) < a i) (hab : ∀ i, (a i : ℝ) < b i)
    (hg : ∀ i, g i ∈ Set.Icc (a i : ℝ) (b i : ℝ))
    (hv : ∀ j : ℕ, j ≤ N → |((A + (j : ℚ) / 250 : ℚ) : ℝ)| ≤ 21)
    (hq :
      ∀ i (k : ℕ),
        k ≤ 4 →
          let q := a i + (k : ℚ) * (b i - a i) / 4
          (0 : ℝ) < q ∧ (q : ℝ) ≤ 100)
    (hc :
      ∀ (j : ℕ),
        j ≤ N →
          ∀ i (k : ℕ),
            k ≤ 4 →
              rationalOrdinateNodeCheck (A + (j : ℚ) / 250) (a i + (k : ℚ) * (b i - a i) / 4)
                  (lo j i) (hi j i) (10 ^ 12) 16 12 =
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
      phase100_le_of_rational_grid g A Br a b lo hi N (fun i ↦ (hpos i).le) hu ha hab hg hv hq hc hb
        hlo
  · exact
      phase100_le_of_rational_grid g A Br a b lo hi N (fun i ↦ (hpos i).le) hu ha hab hg hv hq hc hb
        hhi

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
