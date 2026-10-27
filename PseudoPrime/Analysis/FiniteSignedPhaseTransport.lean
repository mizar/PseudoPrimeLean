/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaPhaseScaleTransport
public import PseudoPrime.Analysis.SignedResolventEulerBounds
public import PseudoPrime.Analysis.RealLog

/-! # One-node resolvent extension for nearby logarithmic scales -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Append the rational node (1,2*delta) to a finite signed resolvent list.
Its resolvent contribution is 2*delta/(1+t^2), and its Euler exponent is 3/2.
This absorbs logarithmic-scale motion while keeping all original nodes. -/
def logarithmicPhaseExtension (l : List (ℚ × ℚ)) (δ : ℚ) : List (ℚ × ℚ) :=
  l ++ [(1, 2 * δ)]

/-- The extended list's resolvent is exactly the original plus
2*delta/(1+t^2). Distribute the finite list sum and cast rational coefficients. -/
theorem finiteSignedResolvent_logarithmicPhaseExtension (l : List (ℚ × ℚ)) (δ : ℚ) (t : ℝ) :
    finiteSignedResolvent (logarithmicPhaseExtension l δ) t =
      finiteSignedResolvent l t + 2 * (δ : ℝ) / (1 + t ^ 2) := by
  simp only [logarithmicPhaseExtension, finiteSignedResolvent, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_one, one_pow, add_zero]
  ring

/-- If all original nodes exceed one half, so do the extended nodes.
The only new node is one. This preserves ordinary Euler-series convergence. -/
theorem logarithmicPhaseExtension_admissible {l : List (ℚ × ℚ)} (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1)
    (δ : ℚ) : ∀ ab ∈ logarithmicPhaseExtension l δ, (1 / 2 : ℚ) < ab.1 := by
  intro ab hab
  rcases List.mem_append.mp hab with h | h
  · exact hl ab h
  · have he := List.mem_singleton.mp h
    rw [he]
    norm_num only

/-- Given a phase majorant at a positive anchor and a rational upper bound
for the logarithmic distance, the extended resolvent majorizes the phase at the new
positive scale. Combine the one-sided phase difference and exact node extension. -/
theorem gammaHalf_phase_majorant_of_log_distance {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (l : List (ℚ × ℚ)) (δ : ℚ) (hd : |Real.log x - Real.log y| ≤ (δ : ℝ))
    (hyphase :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (y : ℂ) ^ (Complex.I * t)).re ≤
          finiteSignedResolvent l t)
    (t : ℝ) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      finiteSignedResolvent (logarithmicPhaseExtension l δ) t := by
  have hp := gammaHalf_negative_phase_le_at_scale_add hx hy t
  have hm :=
    mul_le_mul_of_nonneg_left hd
      (div_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
        (by nlinarith only [sq_nonneg t] : (0 : ℝ) ≤ 1 + t ^ 2))
  rw [finiteSignedResolvent_logarithmicPhaseExtension]
  have hh := hyphase t
  rw [show 2 / (1 + t ^ 2) * (δ : ℝ) = 2 * (δ : ℝ) / (1 + t ^ 2) by ring] at hm
  linarith only [hp, hm, hh]

/-- The extended common Euler weight is the old weight plus
2*delta*u^(-3/2). Unfold the one added node. This keeps the arithmetic cost exact. -/
theorem finiteSignedEulerWeight_logarithmicPhaseExtension (l : List (ℚ × ℚ)) (δ : ℚ) (u : ℝ) :
    finiteSignedEulerWeight (logarithmicPhaseExtension l δ) u =
      finiteSignedEulerWeight l u + 2 * (δ : ℝ) * u ^ (-3 / 2 : ℝ) := by
  simp only [logarithmicPhaseExtension, finiteSignedEulerWeight, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_one, add_zero]
  norm_num only

/-- For nonnegative delta and base, a nonnegative original Euler weight
remains nonnegative after extension. The added power weight is nonnegative. -/
theorem logarithmicPhaseExtension_euler_nonneg {l : List (ℚ × ℚ)} {δ : ℚ} (hd : 0 ≤ δ) {u : ℝ}
    (hu : 0 ≤ u) (hW : 0 ≤ finiteSignedEulerWeight l u) :
    0 ≤ finiteSignedEulerWeight (logarithmicPhaseExtension l δ) u := by
  rw [finiteSignedEulerWeight_logarithmicPhaseExtension]
  exact
    add_nonneg hW
      (mul_nonneg (mul_nonneg (by norm_num only) ((Rat.cast_nonneg (K := ℝ)).mpr hd))
        (Real.rpow_nonneg hu _))

/-- For positive interval left endpoint and x,y in the interval, the
absolute logarithm difference is at most (right-left)/left. Use logarithm monotonicity
and the tangent at the left endpoint. This supplies a rational scale-width gate. -/
theorem abs_log_sub_le_interval_ratio {a b x y : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b)
    (hay : a ≤ y) (hyb : y ≤ b) : |Real.log x - Real.log y| ≤ (b - a) / a := by
  have hxl := Real.log_le_log ha hax
  have hyl := Real.log_le_log ha hay
  have hxu := Real.log_le_log (ha.trans_le hax) hxb
  have hyu := Real.log_le_log (ha.trans_le hay) hyb
  have hspan := log_le_log_add_sub_div ha ((ha.trans_le hax).trans_le hxb)
  rw [abs_le]
  constructor <;> linarith only [hxl, hyl, hxu, hyu, hspan]

/-- A phase majorant at one anchor inside a positive interval transports
to every scale in that interval when its relative width is at most rational delta.
Apply the logarithm interval bound and the one-node extension at each real scale. -/
theorem gammaHalf_phase_majorant_on_interval {a b y : ℝ} (ha : 0 < a) (hay : a ≤ y) (hyb : y ≤ b)
    (l : List (ℚ × ℚ)) (δ : ℚ) (hwidth : (b - a) / a ≤ (δ : ℝ))
    (hyphase :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (y : ℂ) ^ (Complex.I * t)).re ≤
          finiteSignedResolvent l t) :
    ∀ x ∈ Set.Icc a b,
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
          finiteSignedResolvent (logarithmicPhaseExtension l δ) t := by
  intro x hx t
  exact
    gammaHalf_phase_majorant_of_log_distance (ha.trans_le hx.1) (ha.trans_le hay) l δ
      ((abs_log_sub_le_interval_ratio ha hx.1 hx.2 hay hyb).trans hwidth) hyphase t

/-- The half-sum of the extended coefficients equals the original mass
plus delta. Exact finite algebra identifies the added conductor-logarithm coefficient. -/
theorem logarithmicPhaseExtension_mass (l : List (ℚ × ℚ)) (δ : ℚ) :
    ((logarithmicPhaseExtension l δ).map (fun ab ↦ (ab.2 : ℝ))).sum / 2 =
      (l.map (fun ab ↦ (ab.2 : ℝ))).sum / 2 + (δ : ℝ) := by
  simp only [logarithmicPhaseExtension, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Rat.cast_mul, Rat.cast_ofNat, add_zero]
  ring

/-- For nonnegative delta and original Euler nonnegativity on bases at
least one, all extended natural Mangoldt weights are nonnegative. Apply the existing
Euler-to-Mangoldt support theorem. This permits the full paired-tail savings API. -/
theorem logarithmicPhaseExtension_mangoldt_nonneg {l : List (ℚ × ℚ)} {δ : ℚ} (hd : 0 ≤ δ)
    (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ finiteSignedEulerWeight l u) (n : ℕ) :
    0 ≤ finiteSignedMangoldtWeight (logarithmicPhaseExtension l δ) n := by
  apply finiteSignedMangoldtWeight_nonneg
  intro u hu
  exact logarithmicPhaseExtension_euler_nonneg hd (zero_le_one.trans hu) (hW u hu)

end PseudoPrime.Analysis
