/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028PairSharp

/-! # Variable-width triple comparison at the 0.28 high-range entrance -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH and `r ≥ 529/10`, the unit-cutoff principal sum at `r²` satisfies the
explicit one-sided estimate at width `3/(7 sqrt r)` and maximum width `1/10`.
Specialize the relative Chebyshev bound and simplify its boundary costs. -/
theorem target028_paper_entrance_unit (hRH : RiemannHypothesis) {r : ℝ} (hr : (529 / 10 : ℝ) ≤ r) :
    r * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
        ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
          ((1839 / 1000 : ℝ) * (2 * Real.log r + 21 / 8) + 2) *
              ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) /
            r) -
        |refinedWeightDeriv 1| * ((231 / 5000 : ℝ) * r + (1839 / 1000 : ℝ) * (2 * Real.log r) + 2) /
          r -
        refinedWeight 1 *
          (((10 / 19 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt r +
            (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt r +
            (1839 / 1000 : ℝ) / r) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re := by
  have hr0 : 0 < r := (by norm_num only : (0 : ℝ) < 529 / 10).trans_le hr
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hs7 : (7 : ℝ) ≤ Real.sqrt r :=
    (Real.le_sqrt (by norm_num only) hr0.le).mpr (by nlinarith only [hr])
  have hwidth : (3 / 7 : ℝ) / Real.sqrt r ≤ 1 / 10 := by
    apply (div_le_iff₀ hs).mpr
    linarith only [hs7]
  have hx : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hh : 0 < (3 / 7 : ℝ) / Real.sqrt r := div_pos (by norm_num only) hs
  have hp := target028_unit_one_sided hRH hx hh hwidth (by norm_num only : (1 / 10 : ℝ) ≤ 1 / 2)
  rw [Real.sqrt_sq hr0.le, Real.log_pow] at hp
  norm_num only [Nat.cast_ofNat] at hp
  have hid :
    ((3 / 7 : ℝ) / Real.sqrt r / (19 / 10) * r ^ 2 +
          (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r) * r +
          (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r) +
          1839 / 1000) /
        r =
      ((10 / 19 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt r +
        (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt r +
        (1839 / 1000 : ℝ) / r := by
    field_simp (disch :=
      first
      | exact hs.ne'
      | exact hr0.ne'
      | norm_num only)
    rw [Real.sq_sqrt hr0.le]
    ring
  have hmul :
    refinedWeight 1 *
          ((3 / 7 : ℝ) / Real.sqrt r / (19 / 10) * r ^ 2 +
            (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r) * r +
            (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r) +
            1839 / 1000) /
        r =
      refinedWeight 1 *
        (((10 / 19 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt r +
          (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt r +
          (1839 / 1000 : ℝ) / r) := by
    rw [mul_div_assoc, hid]
  rw [hmul] at hp
  norm_num only at hp ⊢
  exact hp

/-- Under RH and `r ≥ 529/10`, the cutoff-minus-full principal gap at scale `r²`
has the displayed one-sided lower bound. Combine the paper-width unit estimate with
the sharp full-series estimate at the same scale. -/
theorem target028_paper_entrance_gap (hRH : RiemannHypothesis) {r : ℝ} (hr : (529 / 10 : ℝ) ≤ r) :
    r *
          (4 * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
            (refinedSixPoleKernel.function (1 / 2)).re) -
        5 *
          ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
            ((1839 / 1000 : ℝ) * (2 * Real.log r + 21 / 8) + 2) *
                ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) /
              r) -
        4 * |refinedWeightDeriv 1| *
            ((231 / 5000 : ℝ) * r + (1839 / 1000 : ℝ) * (2 * Real.log r) + 2) /
          r -
        4 * refinedWeight 1 *
          (((10 / 19 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt r +
            (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt r +
            (1839 / 1000 : ℝ) / r) ≤
      4 *
          (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re := by
  have hr0 : 0 < r := (by norm_num only : (0 : ℝ) < 529 / 10).trans_le hr
  have hx : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hf := target028_paper_entrance_unit hRH hr
  have ht := (abs_le.mp (target028_full_principal_error hRH hx)).2
  rw [Real.sqrt_sq hr0.le, Real.log_pow] at ht
  norm_num only [Nat.cast_ofNat] at ht
  ring_nf at hf ht ⊢
  linarith only [hf, ht]

/-- Under GRH, for a uniform three-prime Korselt product and `R ≥ 529/10`, passage
of every prime base up to `R²` forces the displayed strict scalar inequality. Combine
the one-sided principal gap with the explicit pair-character upper bound. -/
theorem target028_entrance_pair_necessary {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {R : ℝ} (hR : (529 / 10 : ℝ) ≤ R)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    R *
          (4 * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
            (refinedSixPoleKernel.function (1 / 2)).re) -
        5 *
          ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
            ((1839 / 1000 : ℝ) * (2 * Real.log R + 21 / 8) + 2) *
                ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) /
              R) -
        4 * |refinedWeightDeriv 1| *
            ((231 / 5000 : ℝ) * R + (1839 / 1000 : ℝ) * (2 * Real.log R) + 2) /
          R -
        4 * refinedWeight 1 *
          (((10 / 19 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt R +
            (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt R +
            (1839 / 1000 : ℝ) / R) <
      (2 * Real.log n) *
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
              (R ^ 2) ^ (-(27 / 25 : ℝ)) *
              ((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5) +
          (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
            (R ^ 2) ^ (-(27 / 25 : ℝ)) *
            (((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
              (100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27)) +
          (3 / 8 : ℝ) * Real.log n -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have hX : (1000 : ℝ) ≤ R ^ 2 := by nlinarith only [hR]
  have hlower := target028_paper_entrance_gap hGRH.riemann hR
  have hupper :=
    target028_pair_gap_numeric hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
      hvq hvr hX hpass
  exact lt_of_le_of_lt hlower hupper

end PseudoPrime.PrimeTestBounds.MillerRabin
