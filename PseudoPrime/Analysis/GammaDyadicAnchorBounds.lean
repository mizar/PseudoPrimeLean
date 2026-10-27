/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaAdaptiveAnchorBounds
public import PseudoPrime.Analysis.GammaMixedEulerCells

/-! # Five checked dyadic anchors and an adaptive prime-Euler envelope -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Definition: the five anchors 40,80,160,320,640. Output: a finite natural set.
Role: keep the anchor certificate independent of any witness-search interval. -/
def gammaDyadicAnchors : Finset ℕ :=
  {40,80,160,320,640}

/-- Input: an anchor. Definition: ten millionth-grid node intervals, with an empty fallback.
Output: rational node bounds. Role: certify each common envelope using only fifty integers. -/
def gammaDyadicAnchorRatios (a : ℕ) : ℚ → ℚ × ℚ :=
  smallSeedRatios
    (match a with
    | 40 => [20789, 14375, 8266, 3952, 1307, 298, 32, 1, 0, 0]
    | 80 => [10040, 6478, 3357, 1397, 375, 65, 4, 0, 0, 0]
    | 160 => [4849, 2919, 1363, 494, 107, 14, 0, 0, 0, 0]
    | 320 => [2342, 1315, 553, 174, 30, 3, 0, 0, 0, 0]
    | 640 => [1131, 592, 224, 61, 8, 0, 0, 0, 0, 0]
    | _ => [])

/-- Input: an anchor. Definition: the displayed rational common-envelope coefficient.
Output: a rational cap; zero outside the certified set. Role: specify the grouped certificate. -/
def gammaDyadicAnchorCap (a : ℕ) : ℚ :=
  match a with
  | 40 => 63 / 100
  | 80 => 57 / 100
  | 160 => 52 / 100
  | 320 => 49 / 100
  | 640 => 46 / 100
  | _ => 0

/-- Claim: every listed anchor passes its node and positive-mass checks.
Proof: kernel integer and rational arithmetic. Role: certify all five anchors in one theorem. -/
theorem gamma_dyadic_anchor_checks :
    ∀ a ∈ gammaDyadicAnchors,
      gammaFiniteEulerRatioCheck a (gammaDyadicAnchorRatios a) = true ∧
        (gammaResolventCoefficients.map
              (fun ab ↦ max ab.2 0 * ((a : ℚ) * (gammaDyadicAnchorRatios a ab.1).2))).sum ≤
          gammaDyadicAnchorCap a := by
  decide +kernel

/-- Input: membership in the certified anchor set. Claim: the actual anchored coefficient
is at most its rational cap. Proof: apply generic certificate soundness.
Role: transfer the grouped numerical check to real Euler weights. -/
theorem gamma_dyadic_anchor_coefficient_le {a : ℕ} (ha : a ∈ gammaDyadicAnchors) :
    gammaAnchoredReciprocalCoefficient a ≤ (gammaDyadicAnchorCap a : ℝ) := by
  have hc := gamma_dyadic_anchor_checks a ha
  have hpos : (0 : ℚ) < a := (of_decide_eq_true hc.1).1
  have h := gamma_anchored_coefficient_le_of_check hpos hc.1 hc.2
  norm_num only [Rat.cast_natCast] at h
  exact h

/-- Input: a certified anchor and a real p>1 above it. Claim: the actual signed prime
Euler cost is at most cap/(p-1). Proof: apply the generic anchored series comparison.
Role: supply large-prime allowances without per-prime node tables. -/
theorem gamma_prime_euler_cost_le_dyadic_anchor {a : ℕ} (ha : a ∈ gammaDyadicAnchors) {p : ℝ}
    (hp : 1 < p) (hap : (a : ℝ) ≤ p) :
    gammaPrimeEulerCost p ≤ (gammaDyadicAnchorCap a : ℝ) / (p - 1) := by
  have hc := gamma_dyadic_anchor_checks a ha
  have hpos : (0 : ℚ) < a := (of_decide_eq_true hc.1).1
  have hposR := Rat.cast_pos (K := ℝ).mpr hpos
  norm_num only [Rat.cast_natCast] at hposR
  exact
    gamma_prime_euler_cost_le_of_anchored_coefficient hposR hp hap
      (gamma_dyadic_anchor_coefficient_le ha)

/-- Input: a natural prime candidate. Definition: use the largest certified dyadic anchor
below it, falling back to the existing mixed bound below 40. Output: rational Euler allowance.
Role: lower local dual costs while preserving the compact row-certificate format. -/
def gammaAdaptiveEulerUpper (p : ℕ) : ℚ :=
  if 640 ≤ p then gammaDyadicAnchorCap 640 / ((p : ℚ) - 1)
  else
    if 320 ≤ p then gammaDyadicAnchorCap 320 / ((p : ℚ) - 1)
    else
      if 160 ≤ p then gammaDyadicAnchorCap 160 / ((p : ℚ) - 1)
      else
        if 80 ≤ p then gammaDyadicAnchorCap 80 / ((p : ℚ) - 1)
        else if 40 ≤ p then gammaDyadicAnchorCap 40 / ((p : ℚ) - 1) else gammaMixedEulerUpper p

/-- Input: a prime p>=3. Claim: the actual signed Euler cost is at most the adaptive allowance.
Proof: split the five explicit anchor thresholds and use the certified prime-cost comparison.
Role: discharge the separate analytic Euler hypothesis in every adaptive row. -/
theorem gamma_adaptive_euler_upper_sound {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) :
    gammaPrimeEulerCost p ≤ (gammaAdaptiveEulerUpper p : ℝ) := by
  have step (a : ℕ) (ha : a ∈ gammaDyadicAnchors) (hap : a ≤ p) :
    gammaPrimeEulerCost p ≤ ((gammaDyadicAnchorCap a / ((p : ℚ) - 1) : ℚ) : ℝ) := by
    have h :=
      gamma_prime_euler_cost_le_dyadic_anchor ha (show (1 : ℝ) < p by exact_mod_cast hp.one_lt)
        (Nat.cast_le.mpr hap)
    norm_num only [Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, Rat.cast_one] at h ⊢
    exact h
  unfold gammaAdaptiveEulerUpper
  split_ifs with h640 h320 h160 h80 h40
  · exact step 640 (by decide +kernel) h640
  · exact step 320 (by decide +kernel) h320
  · exact step 160 (by decide +kernel) h160
  · exact step 80 (by decide +kernel) h80
  · exact step 40 (by decide +kernel) h40
  · exact gamma_mixed_euler_upper_sound hp h3

end PseudoPrime.Analysis
