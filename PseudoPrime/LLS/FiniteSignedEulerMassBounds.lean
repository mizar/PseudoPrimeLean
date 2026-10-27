/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaEulerTailErrorBounds
public import PseudoPrime.Analysis.SignedResolventEulerBounds
public import PseudoPrime.Analysis.FiniteSignedEulerIntervals
public import PseudoPrime.LLS.GammaEulerErrorEnvelopes

/-! # Finite-center bounds for arbitrary signed Euler masses -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The signed logarithmic slope of an arbitrary rational Euler list at a
cutoff. Retaining coefficients before the boundary comparison preserves cancellation. -/
noncomputable def finiteSignedEulerLogSlope (l : List (ℚ × ℚ)) (a : ℝ) : ℝ :=
  -(l.map (fun ab ↦ (ab.2 : ℝ) * (1 / 2 + (ab.1 : ℝ)) * a ^ (-(1 / 2 + (ab.1 : ℝ))))).sum

/-- The exact signed linear main integral of the Euler variation beyond a
cutoff. Each node contributes c*sigma^2*a^(1-sigma)/(sigma-1). -/
noncomputable def finiteSignedEulerTailMain (l : List (ℚ × ℚ)) (a : ℝ) : ℝ :=
  (l.map
      (fun ab ↦
        (ab.2 : ℝ) *
          ((1 / 2 + (ab.1 : ℝ)) ^ 2 * a ^ (1 - (1 / 2 + (ab.1 : ℝ))) /
            ((1 / 2 + (ab.1 : ℝ)) - 1)))).sum

/-- The explicit RH tail error budget for a rational Euler list. Absolute
coefficients occur only in the integrated error, while all main and boundary
terms retain their original signs. -/
noncomputable def finiteSignedEulerErrorBudget (l : List (ℚ × ℚ)) (a : ℝ) : ℝ :=
  (l.map (fun ab ↦ |(ab.2 : ℝ)| * powerRiemannErrorBudget (1 / 2 + (ab.1 : ℝ)) a)).sum

/-- The finite prefix, exact Chebyshev boundary, signed logarithmic boundary
and main integral at a cutoff. Under RH the full Euler mass differs from this
center by at most the explicit error budget. -/
noncomputable def finiteSignedEulerMassCenter (l : List (ℚ × ℚ)) (a : ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.finiteSignedMangoldtWeight l n) -
      Analysis.finiteSignedEulerWeight l a * Chebyshev.psi a +
    finiteSignedEulerLogSlope l a * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a +
    finiteSignedEulerTailMain l a

/-- Under RH, admissible rational nodes and cutoff at least one, the actual
full signed Euler mass lies between its finite center minus and plus the error
budget. Reuse the generic signed-list tail identity, justified integral subtraction
and the existing integrated RH error estimate. -/
theorem finiteSignedEulerMass_bounds (hRH : RiemannHypothesis) (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) {a : ℝ} (ha : 1 ≤ a) :
    finiteSignedEulerMassCenter l a - finiteSignedEulerErrorBudget l a ≤
        (∑' n : ℕ, Analysis.finiteSignedMangoldtWeight l n) ∧
      (∑' n : ℕ, Analysis.finiteSignedMangoldtWeight l n) ≤
        finiteSignedEulerMassCenter l a + finiteSignedEulerErrorBudget l a := by
  let L := l.map (fun ab ↦ ((1 / 2 + (ab.1 : ℝ)), (ab.2 : ℝ)))
  have hL : ∀ ab ∈ L, 1 < ab.1 := by
    intro ac hac
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hac
    have h := (Rat.cast_lt (K := ℝ)).mpr (hl ab hab)
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    linarith only [h]
  have ht := powerList_tail_eq_improper_log_integral hRH L hL ha
  have he := powerList_error_integral_abs_le hRH L hL ha
  have hm := powerList_linear_density_integral_eq L hL (zero_lt_one.trans_le ha)
  simp only [sub_mul] at he
  rw [MeasureTheory.integral_sub (integrableOn_powerList_density hRH L hL ha)
      (integrableOn_powerList_linear_density L hL (zero_lt_one.trans_le ha)),
    hm] at he
  have hb := abs_le.mp he
  dsimp only [L] at ht hb
  simp only [List.map_map, Function.comp_def] at ht hb
  dsimp only [finiteSignedEulerMassCenter, finiteSignedEulerErrorBudget, finiteSignedEulerLogSlope,
    finiteSignedEulerTailMain, Analysis.finiteSignedMangoldtWeight,
    Analysis.finiteSignedEulerWeight]
  constructor <;> nlinarith only [ht, hb.1, hb.2]

/-- A successful original-node ratio check also bounds any rational reweighting
of the coefficients. Node powers are unchanged, so no duplicate interval
certificate is needed for slopes and main integrals. -/
theorem finiteSigned_weighted_euler_bounds (l : List (ℚ × ℚ)) (w : ℚ × ℚ → ℚ) {d : ℕ} (hd : 0 < d)
    {a : ℚ} {r : ℚ → ℚ × ℚ} (hc : Analysis.finiteSignedEulerRatioCheck l d a r = true) :
    (Analysis.finiteSignedEulerLower (l.map (fun ab ↦ (ab.1, w ab))) r : ℝ) ≤
        Analysis.finiteSignedEulerWeight (l.map (fun ab ↦ (ab.1, w ab))) a ∧
      Analysis.finiteSignedEulerWeight (l.map (fun ab ↦ (ab.1, w ab))) a ≤
        (Analysis.finiteSignedEulerUpper (l.map (fun ab ↦ (ab.1, w ab))) r : ℝ) := by
  apply Analysis.finiteSigned_euler_interval_bounds
  intro ac hac
  obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hac
  exact Analysis.finiteSigned_ratio_check_sound l hd hc ab hab

/-- The signed logarithmic slope equals the same Euler powers with rational
coefficients -c*sigma. This connects generic node intervals to boundary slopes. -/
theorem finiteSigned_slope_eq_weighted (l : List (ℚ × ℚ)) (a : ℝ) :
    finiteSignedEulerLogSlope l a =
      Analysis.finiteSignedEulerWeight (l.map (fun ab ↦ (ab.1, -ab.2 * (1 / 2 + ab.1)))) a := by
  dsimp only [finiteSignedEulerLogSlope, Analysis.finiteSignedEulerWeight]
  rw [show
      -(l.map (fun ab ↦ (ab.2 : ℝ) * (1 / 2 + (ab.1 : ℝ)) * a ^ (-(1 / 2 + (ab.1 : ℝ))))).sum =
        (-1) *
          (l.map (fun ab ↦ (ab.2 : ℝ) * (1 / 2 + (ab.1 : ℝ)) * a ^ (-(1 / 2 + (ab.1 : ℝ))))).sum
      by ring,
    ← List.sum_map_mul_left, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  norm_num only [Function.comp_def, Rat.cast_mul, Rat.cast_neg, Rat.cast_add, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat]
  ring

/-- At a positive rational cutoff, the main integral equals the original
Euler powers with rational coefficients c*a*sigma^2/(sigma-1). Factor one power
of the cutoff, retaining every coefficient sign. -/
theorem finiteSigned_main_eq_weighted (l : List (ℚ × ℚ)) {a : ℚ} (ha : 0 < a) :
    finiteSignedEulerTailMain l a =
      Analysis.finiteSignedEulerWeight
        (l.map (fun ab ↦ (ab.1, ab.2 * a * (1 / 2 + ab.1) ^ 2 / ((1 / 2 + ab.1) - 1)))) a := by
  dsimp only [finiteSignedEulerTailMain, Analysis.finiteSignedEulerWeight]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  norm_num only [Function.comp_def, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_sub,
    Rat.cast_add, Rat.cast_one, Rat.cast_ofNat]
  rw [show (1 : ℝ) - (1 / 2 + (ab.1 : ℝ)) = -(1 / 2 + (ab.1 : ℝ)) + 1 by ring,
    Real.rpow_add_one ((Rat.cast_pos (K := ℝ)).mpr ha).ne']
  ring

/-- Under RH and admissible nodes, finite upper and lower scalar bounds for
the center and error yield an upper bound for the full signed Euler mass.
Compare the negative boundary products with their correct signs once. -/
theorem finiteSignedEulerMass_le_of_scalar_bounds (hRH : RiemannHypothesis) (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) {a P w p g v M e : ℝ} (ha : 1 ≤ a)
    (hP : (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.finiteSignedMangoldtWeight l n) ≤ P)
    (hW : w ≤ Analysis.finiteSignedEulerWeight l a) (hw : 0 ≤ w) (hpsi : p ≤ Chebyshev.psi a)
    (hp : 0 ≤ p) (hG : finiteSignedEulerLogSlope l a ≤ g) (hg : g ≤ 0)
    (hS : v ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a) (hv : 0 ≤ v)
    (hM : finiteSignedEulerTailMain l a ≤ M) (he : finiteSignedEulerErrorBudget l a ≤ e) :
    (∑' n : ℕ, Analysis.finiteSignedMangoldtWeight l n) ≤ P - w * p + g * v + M + e := by
  have hm := (finiteSignedEulerMass_bounds hRH l hl ha).2
  have h1 := mul_le_mul hW hpsi hp (hw.trans hW)
  have h2 := (mul_le_mul_of_nonneg_right hG (hv.trans hS)).trans (mul_le_mul_of_nonpos_left hS hg)
  dsimp only [finiteSignedEulerMassCenter] at hm
  nlinarith only [hm, hP, h1, h2, hM, he]

/-- At cutoff at least one, root, logarithm and node-power upper bounds give
a finite envelope for the full integrated error budget. Apply the existing
scalar RH envelope with nonnegative coefficient magnitudes. -/
theorem finiteSignedEulerErrorBudget_le_envelope (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) {a r b : ℝ} (ha : 1 ≤ a) (hr : Real.sqrt a ≤ r)
    (hb : Real.log a ≤ b) (v : ℚ → ℝ) (hv : ∀ ab ∈ l, a ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ v ab.1) :
    finiteSignedEulerErrorBudget l a ≤
      (l.map
          (fun ab ↦
            |(ab.2 : ℝ)| * gammaEulerErrorEnvelope r (v ab.1) b (1 / 2 + (ab.1 : ℝ)))).sum := by
  dsimp only [finiteSignedEulerErrorBudget]
  apply List.sum_le_sum
  intro ab hab
  have hh := (Rat.cast_lt (K := ℝ)).mpr (hl ab hab)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hh
  exact
    mul_le_mul_of_nonneg_left
      (powerRiemannErrorBudget_le_envelope (by linarith only [hh]) ha hr (hv ab hab) hb)
      (abs_nonneg (ab.2 : ℝ))

end PseudoPrime.LLS
