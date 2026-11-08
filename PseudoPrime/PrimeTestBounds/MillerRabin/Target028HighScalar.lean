/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EntrancePair
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePaperScalar

/-! # Scalar inequality at the 0.28 high-range entrance -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The variable-width square-root boundary cost is below the normalized
paper coefficient `11/100`. Use the certified unit-weight bound and exact
rational arithmetic. -/
theorem target028_paper_sqrt_cost :
    4 * refinedWeight 1 * ((10 / 19 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) <
      (27 / 25 : ℝ) ^ 5 * (11 / 100) := by
  have hw := refined_unit_weight_precise
  norm_num only at ⊢
  linarith only [hw]

/-- The normalized residual at logarithmic size `L` and root scale `R`. It combines
the conductor, dual Euler, Gamma, zero-mass, principal variation and endpoint costs;
the linear and square-root leading terms are kept outside for the scalar certificate. -/
noncomputable def target028PaperResidual (L R : ℝ) : ℝ :=
  (2 * L) *
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
            (R ^ 2) ^ (-(27 / 25 : ℝ)) *
            ((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5) +
        (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
        (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
          (R ^ 2) ^ (-(27 / 25 : ℝ)) *
          (((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
            (100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27)) -
      (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
    5 *
      ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
        ((1839 / 1000 : ℝ) * (2 * Real.log R + 21 / 8) + 2) *
            ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) /
          R) +
    4 * |refinedWeightDeriv 1| * ((231 / 5000 : ℝ) * R + (1839 / 1000 : ℝ) * (2 * Real.log R) + 2) /
      R +
    4 * refinedWeight 1 * ((231 / 2500 : ℝ) * (7 / 3) / Real.sqrt R + (1839 / 1000 : ℝ) / R)

/-- For `R ≥ 529/10`, the explicit character-gap inequality implies the paper scalar
inequality with its exact rational leading coefficients. Compare the kernel main mass
and square-root boundary coefficient with their certified strict bounds. -/
theorem target028_scalar_from_gap {L R : ℝ} (hR : (529 / 10 : ℝ) ≤ R)
    (hgap :
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
        (2 * L) *
              (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                (R ^ 2) ^ (-(27 / 25 : ℝ)) *
                ((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5) +
            (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
              (R ^ 2) ^ (-(27 / 25 : ℝ)) *
              (((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
                (100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27)) +
            (3 / 8 : ℝ) * L -
          (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5) :
    (27 / 25 : ℝ) ^ 5 * (24439 / 50000) * R <
      (3 / 8 : ℝ) * L + (27 / 25 : ℝ) ^ 5 * (11 / 100) * Real.sqrt R +
        target028PaperResidual L R := by
  have hR0 : 0 < R := (by norm_num only : (0 : ℝ) < 529 / 10).trans_le hR
  have hd := mul_lt_mul_of_pos_right refined_paper_delta_lower hR0
  have hv := mul_le_mul_of_nonneg_right target028_paper_sqrt_cost.le (Real.sqrt_nonneg R)
  dsimp only [target028PaperResidual]
  ring_nf at hd hv hgap ⊢
  linarith only [hd, hv, hgap]

/-- Under GRH, a uniform three-prime Korselt product for which all prime bases at
most `R²` pass must satisfy the explicit scalar inequality. Combine the paper-width
principal comparison with the certified leading constants. -/
theorem target028_pair_scalar_necessary {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {R : ℝ} (hR : (529 / 10 : ℝ) ≤ R)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    (27 / 25 : ℝ) ^ 5 * (24439 / 50000) * R <
      (3 / 8 : ℝ) * Real.log n + (27 / 25 : ℝ) ^ 5 * (11 / 100) * Real.sqrt R +
        target028PaperResidual (Real.log n) R := by
  apply target028_scalar_from_gap hR
  exact
    target028_entrance_pair_necessary hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr hR hpass

/-- The paper's scalar inequality is impossible when `R ≥ (529/1000)L`
and the normalized residual is at most `-3/2`. The remaining positive
quadratic is certified by completing the square in `sqrt R`. -/
theorem target028_high_scalar_excludes {L R : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLR : (529 / 1000 : ℝ) * L ≤ R)
    (hres : target028PaperResidual L R ≤ -(3 / 2 : ℝ) * (27 / 25 : ℝ) ^ 5)
    (hnecessary :
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000) * R <
        (3 / 8 : ℝ) * L + (27 / 25 : ℝ) ^ 5 * (11 / 100) * Real.sqrt R +
          target028PaperResidual L R) :
    False := by
  have hc : (3 / 8 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 * ((24439 / 50000 : ℝ) - 3 / 500) * (529 / 1000) := by
    norm_num only
  have hm := mul_le_mul_of_nonneg_right hc hL
  have hk : 0 ≤ (27 / 25 : ℝ) ^ 5 * ((24439 / 50000 : ℝ) - 3 / 500) := by norm_num only
  have hr := mul_le_mul_of_nonneg_left hLR hk
  have hs := Real.sq_sqrt hR
  have hsq := sq_nonneg (Real.sqrt R - (55 / 6 : ℝ))
  norm_num only at hm hr hres hnecessary hs hsq ⊢
  nlinarith only [hm, hr, hres, hnecessary, hs, hsq]

/-- Under GRH, a uniform Korselt triple of logarithmic scale at least 100 has
a rejecting prime below the 0.28 cutoff once the paper's residual estimate is
available at the selected scale. The scalar exclusion supplies the contradiction. -/
theorem target028_high_pair_witness_of_residual {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q]
    [NeZero r] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)]
    [Fact (2 < r)] (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (100 : ℝ) ≤ Real.log n)
    (hres :
      target028PaperResidual (Real.log n) (Real.sqrt (7 / 25 : ℝ) * Real.log n) ≤
        -(3 / 2 : ℝ) * (27 / 25 : ℝ) ^ 5) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  let R : ℝ := Real.sqrt (7 / 25 : ℝ) * Real.log n
  have hL0 : 0 ≤ Real.log n := by linarith only [hL]
  have hs : (529 / 1000 : ℝ) ≤ Real.sqrt (7 / 25 : ℝ) := by
    apply (Real.le_sqrt (by norm_num only) (by norm_num only)).2
    norm_num only
  have hLR : (529 / 1000 : ℝ) * Real.log n ≤ R := mul_le_mul_of_nonneg_right hs hL0
  have hR : (529 / 10 : ℝ) ≤ R := by linarith only [hLR, hL]
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hR2 : R ^ 2 = (7 / 25 : ℝ) * Real.log n ^ 2 := by
    dsimp only [R]
    rw [mul_pow, Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 7 / 25)]
  by_contra h
  have hpass :
    ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
    intro l hl hb
    rw [hR2] at hb
    exact Classical.byContradiction (fun hf ↦ h ⟨l, hl, hb, hf⟩)
  have hnecessary :=
    target028_pair_scalar_necessary hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr hR hpass
  exact target028_high_scalar_excludes hL0 hR0 hLR hres hnecessary

end PseudoPrime.PrimeTestBounds.MillerRabin
