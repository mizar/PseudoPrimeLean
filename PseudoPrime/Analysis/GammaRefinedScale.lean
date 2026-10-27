/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSmallPrimeCosts

/-! # The prescribed logarithmic scale for the refined Gamma bound -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The prescribed scale x=(32/99)(L+2 log L+10)^2 for the cutoff
X=(4/5)(L+2 log L+10)^2. The ratio 99/40 sends x to X, as certified below.
This definition connects the local cost thresholds to the intended witness bound. -/
noncomputable def gammaRefinedScale (L : ℝ) : ℝ :=
  (32 / 99 : ℝ) * (L + 2 * Real.log L + 10) ^ 2

/-- The actual cutoff associated with the refined scale is exactly the
prescribed coefficient-four-fifths witness cutoff. Rational algebra fixes
the relationship rather than introducing an independent scale parameter. -/
theorem gamma_refined_scale_cutoff (L : ℝ) :
    (99 / 40 : ℝ) * gammaRefinedScale L = (4 / 5 : ℝ) * (L + 2 * Real.log L + 10) ^ 2 := by
  unfold gammaRefinedScale
  ring

/-- The logarithmic range beginning at 100 log ten lies above 230.
Use the certified logarithms of two and five and log ten's product identity.
This provides a rational input threshold for the local-cost scale certificates. -/
theorem gamma_refined_log_lower {L : ℝ} (hL : 100 * Real.log 10 ≤ L) : (230 : ℝ) ≤ L := by
  rw [Real.log_ten_eq] at hL
  linarith only [hL, Real.log_two_gt_d9, Real.log_five_gt_d9]

/-- Throughout the prescribed logarithmic range, log L is at least five.
Compare with log 200=log two+2 log ten, whose lower bound is certified.
This contributes the two logarithmic terms to the scale threshold. -/
theorem gamma_refined_log_log_lower {L : ℝ} (hL : 100 * Real.log 10 ≤ L) :
    (5 : ℝ) ≤ Real.log L := by
  have hl := gamma_refined_log_lower hL
  have he : Real.log (200 : ℝ) = Real.log 2 + 2 * Real.log 10 := by
    have h := Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (10 : ℝ) ^ 2 ≠ 0)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hm :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 200) (by linarith only [hl] : (200 : ℝ) ≤ L)
  rw [he, Real.log_ten_eq] at hm
  linarith only [hm, Real.log_two_gt_d9, Real.log_five_gt_d9]

/-- The prescribed scale is at least 20000 throughout L>=100 log ten.
The certified lower bounds give L+2 log L+10>=250; square this and multiply
by 32/99. This discharges all local-cost scale thresholds on the intended range. -/
theorem gamma_refined_scale_ge_twenty_thousand {L : ℝ} (hL : 100 * Real.log 10 ≤ L) :
    (20000 : ℝ) ≤ gammaRefinedScale L := by
  have hT : (250 : ℝ) ≤ L + 2 * Real.log L + 10 := by
    linarith only [gamma_refined_log_lower hL, gamma_refined_log_log_lower hL]
  have hs :=
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 250)
          (by linarith only [hT] : 0 ≤ L + 2 * Real.log L + 10)).mpr
      hT
  dsimp only [gammaRefinedScale]
  nlinarith only [hs]

/-- At the prescribed refined scale and throughout L>=100 log ten, all
minus-one losses from the odd ambient input are absorbed by the conductor
gap. The scale threshold and every odd-prime numerical condition have been
proved, leaving only the arithmetic decomposition and character inputs. -/
theorem gamma_refined_scale_actual_cost_absorbed {n d m f : ℕ} (hn : n = d * m ^ 2) (hodd : Odd n)
    (hd : 0 < d) (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {L : ℝ} (hL : 100 * Real.log 10 ≤ L) :
    (11783423 / 25000000 : ℝ) * Real.log f +
        (∑ p ∈ S,
          ((∑ k ∈ K p,
              (1 - (χ (p ^ (2 * k + 1))).re) * gammaResolventMangoldtWeight (p ^ (2 * k + 1))) +
            Real.log p *
              ((∑' k : ℕ,
                  exponentialRampLocalCorrection (-1) ((p : ℝ) ^ (k + 1) / gammaRefinedScale L)
                    (k + 1)) /
                Real.sqrt (gammaRefinedScale L)))) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) := by
  exact
    gamma_odd_input_actual_cost_absorbed_by_conductor_gap hn hodd hd hm hf hdf hfd S hS χ hχ K
      (by linarith only [gamma_refined_scale_ge_twenty_thousand hL])

/-- An input at least ten to the hundredth power belongs to the prescribed
logarithmic range. Cast the integer power inequality and apply log monotonicity.
This ties the analytic scale's logarithmic input to the actual ambient integer. -/
theorem gamma_refined_log_range_of_decimal {n : ℕ} (hn : 10 ^ 100 ≤ n) :
    100 * Real.log 10 ≤ Real.log n := by
  have hc : (10 : ℝ) ^ 100 ≤ (n : ℝ) := by exact_mod_cast hn
  have h := Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 10) 100) hc
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

/-- For an odd input n>=10^100, use L=log n and the prescribed scale
to absorb every selected minus-one prime loss by the conductor gap.
The actual input bound supplies the logarithmic range, completing the
connection from the local analytic certificate to the intended scale. -/
theorem gamma_refined_input_actual_cost_absorbed {n d m f : ℕ} (hn : n = d * m ^ 2) (hodd : Odd n)
    (hd : 0 < d) (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) (hlarge : 10 ^ 100 ≤ n) :
    (11783423 / 25000000 : ℝ) * Real.log f +
        (∑ p ∈ S,
          ((∑ k ∈ K p,
              (1 - (χ (p ^ (2 * k + 1))).re) * gammaResolventMangoldtWeight (p ^ (2 * k + 1))) +
            Real.log p *
              ((∑' k : ℕ,
                  exponentialRampLocalCorrection (-1)
                    ((p : ℝ) ^ (k + 1) / gammaRefinedScale (Real.log n)) (k + 1)) /
                Real.sqrt (gammaRefinedScale (Real.log n))))) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) := by
  exact
    gamma_refined_scale_actual_cost_absorbed hn hodd hd hm hf hdf hfd S hS χ hχ K
      (gamma_refined_log_range_of_decimal hlarge)

end PseudoPrime.Analysis
