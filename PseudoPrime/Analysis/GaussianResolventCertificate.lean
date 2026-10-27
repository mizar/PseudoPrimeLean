/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaResolventCertificate

/-! # Finite arithmetic for a Gaussian resolvent zero-mass candidate -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Twelve signed rational resolvent coefficients for the Gaussian zero-mass candidate.
The scale a sets the Poisson line 1/2+a and b is its signed weight.
Mass and finite error arithmetic are certified below; global domination is a separate obligation. -/
def gaussianResolventCoefficients : List (ℚ × ℚ) :=
  [(110 / 200, 61938394 / 100000000), (139 / 200, 23848901 / 100000000),
    (175 / 200, -171023537 / 100000000), (220 / 200, 899494130 / 100000000),
    (277 / 200, -2075895953 / 100000000), (350 / 200, 4073757753 / 100000000),
    (441 / 200, -5802640304 / 100000000), (555 / 200, 4885741845 / 100000000),
    (700 / 200, -2438645895 / 100000000), (882 / 200, 745378529 / 100000000),
    (1111 / 200, -132236424 / 100000000), (1400 / 200, 10745045 / 100000000)]

/-- All candidate scales exceed one half. Exact rational verification keeps
all Poisson evaluation points in the ordinary L-series half-plane. -/
theorem gaussianResolvent_scales_gt_half :
    gaussianResolventCoefficients.Forall (fun ab ↦ (1 / 2 : ℚ) < ab.1) := by decide +kernel

/-- Both parity shifts of every candidate node lie in [1/2,17/4].
Exact rational verification permits reuse of the existing uniform digamma interval bound. -/
theorem gaussianResolvent_gamma_arguments :
    gaussianResolventCoefficients.Forall
      (fun ab ↦
        ((1 / 2 : ℚ) ≤ (1 / 2 + ab.1) / 2 ∧ (1 / 2 + ab.1) / 2 ≤ 17 / 4) ∧
          ((1 / 2 : ℚ) ≤ (3 / 2 + ab.1) / 2 ∧ (3 / 2 + ab.1) / 2 ≤ 17 / 4)) := by
  decide +kernel

/-- The signed rational candidate sum of b a/(a²+t²).
Its global domination of the Gaussian critical-line norm is not assumed in this definition.
The arithmetic certificate supports a separate interpolation and tail proof. -/
noncomputable def gaussianResolventMajorant (t : ℝ) : ℝ :=
  (gaussianResolventCoefficients.map
      (fun ab ↦ (ab.2 : ℝ) * ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + t ^ 2)))).sum

/-- Half the candidate's signed total weight is 20115621/50000000.
Evaluate the finite rational data after casting. This is its conductor-log coefficient. -/
theorem gaussianResolvent_mass_eq :
    (gaussianResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum / 2 =
      (20115621 / 50000000 : ℝ) := by
  norm_num only [gaussianResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]

/-- The candidate's conductor coefficient is strictly below 161/400.
Use the exact mass value and rational comparison. Global domination remains separate. -/
theorem gaussianResolvent_mass_lt_target :
    (gaussianResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum / 2 < (161 / 400 : ℝ) := by
  rw [gaussianResolvent_mass_eq]
  norm_num only

/-- The candidate's absolute-weight baseline Poisson error allowance is below 1811.
Evaluate the existing per-line error expression on the rational data.
This is a candidate-specific finite allowance, not the old Gamma additive constant. -/
theorem gaussianResolvent_error_lt :
    (gaussianResolventCoefficients.map
          (fun ab ↦ |(ab.2 : ℝ)| * (((ab.1 : ℝ) - 1 / 2)⁻¹ ^ 2 + ((ab.1 : ℝ) - 1 / 2)⁻¹ + 6))).sum <
      (1811 : ℝ) := by
  norm_num only [gaussianResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]

/-- The candidate's summed scaled-resolvent curvature allowance is below 434.
Evaluate the absolute-weight rational expression. The analytic derivative estimate
and interpolation connection are separate obligations. -/
theorem gaussianResolvent_scaled_curvature_lt :
    (gaussianResolventCoefficients.map
          (fun ab ↦ |(ab.2 : ℝ)| * (6 * |1 - (ab.1 : ℝ) ^ 2| / (ab.1 : ℝ) ^ 3))).sum <
      (434 : ℝ) := by
  norm_num only [gaussianResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]

/-- If each Poisson node has the existing centered baseline error estimate,
the signed candidate sum is less than its conductor coefficient times L plus 1811.
Retain signs in the main term and use absolute weights only in the finite error.
The Gaussian norm domination and actual Poisson node estimates remain separate. -/
theorem gaussianResolvent_weighted_lt_of_centered_bounds (P : ℚ → ℝ) (L : ℝ)
    (h :
      ∀ ab ∈ gaussianResolventCoefficients,
        |P ab.1 - L / 2| ≤ ((ab.1 : ℝ) - 1 / 2)⁻¹ ^ 2 + ((ab.1 : ℝ) - 1 / 2)⁻¹ + 6) :
    (gaussianResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * P ab.1)).sum <
      (20115621 / 50000000 : ℝ) * L + 1811 := by
  have ht :=
    sum_signed_centered_le gaussianResolventCoefficients (fun ab ↦ (ab.2 : ℝ)) (fun ab ↦ P ab.1)
      (fun ab ↦ ((ab.1 : ℝ) - 1 / 2)⁻¹ ^ 2 + ((ab.1 : ℝ) - 1 / 2)⁻¹ + 6) (L / 2) h
  have he :
    (gaussianResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum * (L / 2) =
      (20115621 / 50000000 : ℝ) * L := by
    calc
      _ = ((gaussianResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum / 2) * L := by ring
      _ = _ := by rw [gaussianResolvent_mass_eq]
  rw [he] at ht
  linarith only [ht, gaussianResolvent_error_lt]

end PseudoPrime.Analysis
