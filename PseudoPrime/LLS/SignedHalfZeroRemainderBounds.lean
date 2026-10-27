/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogHalfExplicitFormula
public import PseudoPrime.LLS.DirectHadamardConductorBounds
public import PseudoPrime.LLS.SignedHalfPowerWitnessBounds

/-! # Explicit remainder and actual zero-phase witness criterion -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Under primitive GRH, compute the real origin-residue difference for an
even character at positive x. The derivative constant cancels between scales. -/
theorem log_origin_half_even_re_eq {N : ℕ} [NeZero N] (hN : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (he : χ.Even) {x : ℝ} (hx : 0 < x) :
    (dirichletLogResidueAt hne x 0 - dirichletLogResidueAt hne (x / 2) 0).re =
      (|primitiveBRe χ| + Real.log N / 2 - (Real.log Real.pi + Real.eulerMascheroniConstant) / 2 -
            Real.log x) *
          Real.log 2 +
        (Real.log 2) ^ 2 / 2 := by
  rw [LLS.log_residue_zero_even_eq hp hne he hx,
    LLS.log_residue_zero_even_eq hp hne he (div_pos hx (by norm_num only : (0 : ℝ) < 2)),
    Real.log_div hx.ne' (by norm_num only : (2 : ℝ) ≠ 0)]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log hN hGRH hp hne hinv]
  ring

/-- Under primitive GRH, compute the real origin-residue difference for an
odd character at positive x. The result is independent of x. -/
theorem log_origin_half_odd_re_eq {N : ℕ} [NeZero N] (hN : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (ho : χ.Odd) {x : ℝ} (hx : 0 < x) :
    (dirichletLogResidueAt hne x 0 - dirichletLogResidueAt hne (x / 2) 0).re =
      (|primitiveBRe χ| + Real.log N / 2 -
          (Real.log Real.pi / 2 + Real.log 2 + Real.eulerMascheroniConstant / 2)) *
        Real.log 2 := by
  rw [LLS.log_residue_zero_odd_eq hp hne ho hx,
    LLS.log_residue_zero_odd_eq hp hne ho (div_pos hx (by norm_num only : (0 : ℝ) < 2)),
    Real.log_div hx.ne' (by norm_num only : (2 : ℝ) ≠ 0)]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log hN hGRH hp hne hinv]
  ring

/-- Under primitive GRH and x≥1, bound the real origin difference in terms
of the completed zero mass and log(N). Discard only nonpositive parity corrections. -/
theorem log_origin_half_re_le {N : ℕ} [NeZero N] (hN : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    (dirichletLogResidueAt hne x 0 - dirichletLogResidueAt hne (x / 2) 0).re ≤
      (|primitiveBRe χ| + Real.log N / 2) * Real.log 2 + (Real.log 2) ^ 2 / 2 := by
  have hx0 := zero_lt_one.trans_le hx
  have hl0 := Real.log_nonneg hx
  have h20 := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)
  have hp0 : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith only [Real.pi_gt_three] : 1 ≤ Real.pi)
  have hg0 := Real.one_half_lt_eulerMascheroniConstant
  rcases χ.even_or_odd with he | ho
  · rw [log_origin_half_even_re_eq hN hGRH hp hne hinv he hx0]
    have hm :=
      mul_nonneg
        (show 0 ≤ (Real.log Real.pi + Real.eulerMascheroniConstant) / 2 + Real.log x by
          linarith only [hp0, hg0, hl0])
        h20
    nlinarith only [hm]
  · rw [log_origin_half_odd_re_eq hN hGRH hp hne hinv ho hx0]
    have hm :=
      mul_nonneg
        (show 0 ≤ Real.log Real.pi / 2 + Real.log 2 + Real.eulerMascheroniConstant / 2 by
          linarith only [hp0, hg0, h20])
        h20
    nlinarith only [hm, sq_nonneg (Real.log 2)]

/-- Under primitive GRH, N≥3 and x≥4, the real half-scale remainder is at
most (4/5)log(N)+5. Combine the direct Hadamard mass bound with both trivial corrections. -/
theorem logarithmicHalfRemainder_re_le {N : ℕ} [NeZero N] (hN : 3 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {x : ℝ} (hx : 4 ≤ x) : (logarithmicHalfRemainder hne x).re ≤ (4 / 5 : ℝ) * Real.log N + 5 := by
  have hO :=
    log_origin_half_re_le (le_trans (by decide : 2 ≤ 3) hN) hGRH hp hne hinv
      (show 1 ≤ x by linarith only [hx])
  have ht :=
    Complex.re_le_norm (logarithmicTrivialCorrection χ x - logarithmicTrivialCorrection χ (x / 2))
  have htn :=
    norm_sub_le (logarithmicTrivialCorrection χ x) (logarithmicTrivialCorrection χ (x / 2))
  have h1 := norm_logarithmicTrivialCorrection_le_one χ (show 2 ≤ x by linarith only [hx])
  have h2 := norm_logarithmicTrivialCorrection_le_one χ (show 2 ≤ x / 2 by linarith only [hx])
  have hb := LLS.PaperStatements.abs_primitiveBRe_le_direct_reciprocal hN hp hGRH
  have hl := Real.log_natCast_nonneg N
  have h20 := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)
  have h21 : Real.log (2 : ℝ) ≤ 7 / 10 := by linarith only [Real.log_two_lt_d9]
  have hm :=
    mul_le_mul_of_nonneg_left h21
      (show 0 ≤ |primitiveBRe χ| + Real.log N / 2 by
        linarith only [abs_nonneg (primitiveBRe χ), hl])
  have hsq := pow_le_pow_left₀ h20 h21 2
  dsimp only [logarithmicHalfRemainder]
  simp only [Complex.sub_re, Complex.add_re] at hO ht ⊢
  nlinarith only [hO, ht, htn, h1, h2, hb, hm, hsq, hl]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

namespace PseudoPrime.LLS.PaperStatements

/-- Under primitive GRH, N≥3 and X≥4, bound the real half-scale sum by
sqrt(X) times its signed phase plus (4/5)log(N)+5. Keep the oscillatory sign. -/
theorem log_half_signed_phase_upper {N : ℕ} [NeZero N] (hN : 3 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {X : ℝ} (hX : 4 ≤ X) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum X χ -
          AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (X / 2) χ).re ≤
      Real.sqrt X * AnalyticNumberTheory.DirichletLFunction.logarithmicHalfPhase χ (Real.log X) +
        (4 / 5 : ℝ) * Real.log N +
        5 := by
  rw [AnalyticNumberTheory.DirichletLFunction.characterLogWeightedSum_half_phase_formula
      (le_trans (by decide : 2 ≤ 3) hN) hGRH hp hne hinv (show 2 < X by linarith only [hX])]
  have hr :=
    AnalyticNumberTheory.DirichletLFunction.logarithmicHalfRemainder_re_le hN hGRH hp hne hinv hX
  linarith only [hr]

/-- For a primitive nonprincipal character under GRH and RH, a strict actual
phase gap at X≥200 yields a prime outside m≠0 with non-one character value.
Apply the signed comparison using the explicit origin and trivial-zero remainder. -/
theorem exists_prime_ne_one_of_half_phase_gap {N m : ℕ} [NeZero N] (hN : 3 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hRH : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hm : m ≠ 0)
    {X : ℝ} (hX : 200 ≤ X)
    (hgap :
      Real.sqrt X * AnalyticNumberTheory.DirichletLFunction.logarithmicHalfPhase χ (Real.log X) +
          (4 / 5 : ℝ) * Real.log N +
          5 +
          ((1 / 2 : ℝ) + 36 * Real.log 2) * Real.sqrt X +
          2 * Real.log 2 * (∑ p ∈ m.primeFactors, Real.log p) <
        X / 2) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  apply exists_prime_ne_one_of_signed_half_gap χ hRH hm hX
  have hu := log_half_signed_phase_upper hN hGRH hp hne hinv (show 4 ≤ X by linarith only [hX])
  linarith only [hu, hgap]

/-- The additional analytic input for the actual completed-zero phase:
absence of witnesses through CL^a gives a scale X in [θCL^a,CL^a] where the signed
phase is at most C₁L^(1-δ)+C₂. This proposition is not established by GRH here. -/
def HalfZeroPhasePowerWindow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (m : ℕ)
    (L a δ C θ C₁ C₂ : ℝ) : Prop :=
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ C * L ^ a → ¬p ∣ m → χ p = 1) →
    ∃ X : ℝ,
      θ * (C * L ^ a) ≤ X ∧
        X ≤ C * L ^ a ∧
        AnalyticNumberTheory.DirichletLFunction.logarithmicHalfPhase χ (Real.log X) ≤
          C₁ * L ^ (1 - δ) + C₂

/-- For a primitive nonprincipal character under GRH and RH, log(N)≤L and
E(m)≤CₘL, the actual phase-window input and explicit power budget give a prime
through CL^a. Retain the conductor remainder as a linear cost, using L≥1. -/
theorem exists_prime_ne_one_le_of_half_phase_power_window {N m : ℕ} [NeZero N] (hN : 3 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hRH : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hm : m ≠ 0)
    {L a δ C θ C₁ C₂ Cₘ : ℝ} (hL : 1 ≤ L) (hlog : Real.log N ≤ L) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsmall : 200 ≤ θ * (C * L ^ a)) (hE : (∑ p ∈ m.primeFactors, Real.log p) ≤ Cₘ * L)
    (hbudget :
      C₁ * Real.sqrt (C * L ^ a) * L ^ (1 - δ) +
          (C₂ + ((1 / 2 : ℝ) + 36 * Real.log 2)) * Real.sqrt (C * L ^ a) +
          ((29 / 5 : ℝ) + 2 * Real.log 2 * Cₘ) * L <
        θ * (C * L ^ a) / 2)
    (hw : HalfZeroPhasePowerWindow χ m L a δ C θ C₁ C₂) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ C * L ^ a ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  by_contra hnone
  have hno (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) ≤ C * L ^ a) (hd : ¬p ∣ m) : χ p = 1 := by
    by_contra hv
    exact hnone ⟨p, hp, hb, hd, hv⟩
  obtain ⟨X, hl, hu, hz⟩ := hw hno
  have hs := Real.sqrt_le_sqrt hu
  have hK : 0 ≤ (1 / 2 : ℝ) + 36 * Real.log 2 := by
    have h2 := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)
    linarith only [h2]
  have hcoef : 0 ≤ C₁ * L ^ (1 - δ) + C₂ :=
    add_nonneg (mul_nonneg hC₁ (Real.rpow_nonneg (zero_le_one.trans hL) _)) hC₂
  have hphase :=
    (mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg X)).trans (mul_le_mul_of_nonneg_right hs hcoef)
  have hKX := mul_le_mul_of_nonneg_left hs hK
  have hcost :=
    mul_le_mul_of_nonneg_left hE
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
        (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)))
  have hrem : (4 / 5 : ℝ) * Real.log N + 5 ≤ (29 / 5 : ℝ) * L := by linarith only [hlog, hL]
  have hg :
    Real.sqrt X * AnalyticNumberTheory.DirichletLFunction.logarithmicHalfPhase χ (Real.log X) +
        (4 / 5 : ℝ) * Real.log N +
        5 +
        ((1 / 2 : ℝ) + 36 * Real.log 2) * Real.sqrt X +
        2 * Real.log 2 * (∑ p ∈ m.primeFactors, Real.log p) <
      X / 2 := by
    nlinarith only [hphase, hKX, hcost, hrem, hbudget, hl]
  obtain ⟨p, hp', hb, hd, hv⟩ :=
    exists_prime_ne_one_of_half_phase_gap hN hGRH hRH hp hne hinv hm (hsmall.trans hl) hg
  exact hnone ⟨p, hp', hb.trans hu, hd, hv⟩

/-- Fix a>1 and 1-δ<a/2 with positive C,θ and nonnegative phase constants.
Under GRH the actual phase-window input gives a prime through CL^a uniformly for
large L over all primitive nonprincipal conductors with log(N)≤L and E(m)≤CₘL.
Absorb the linear remainder in the existing power budget; no phase estimate is assumed proved. -/
theorem eventually_exists_prime_ne_one_of_half_phase_power_window {a δ C θ C₁ C₂ Cₘ : ℝ}
    (ha : 1 < a) (hδ : 1 - δ < a / 2) (hC : 0 < C) (hθ : 0 < θ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∀ᶠ L : ℝ in Filter.atTop,
      ∀ (N m : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
        3 ≤ N →
          χ.IsPrimitive →
          χ ≠ 1 →
          χ⁻¹ ≠ 1 →
          m ≠ 0 →
          Real.log N ≤ L →
          (∑ p ∈ m.primeFactors, Real.log p) ≤ Cₘ * L →
          HalfZeroPhasePowerWindow χ m L a δ C θ C₁ C₂ →
          ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ C * L ^ a ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  have hb :=
    Analysis.eventually_signed_half_power_budget (C₁ := C₁) (C₂ := C₂) (Cₘ :=
      Cₘ + 29 / (10 * Real.log 2)) ha hδ hC hθ
  have he :
    2 * Real.log 2 * (Cₘ + 29 / (10 * Real.log 2)) = (29 / 5 : ℝ) + 2 * Real.log 2 * Cₘ := by
    field_simp [(Real.log_pos (by norm_num only : (1 : ℝ) < 2)).ne']
    ring
  filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with L hbudget hL
  intro N m _ χ hN hp hne hinv hm hlog hE hw
  rw [he] at hbudget
  exact
    exists_prime_ne_one_le_of_half_phase_power_window hN hGRH hGRH.riemann hp hne hinv hm hL hlog
      hC₁ hC₂ hbudget.1 hE hbudget.2 hw

end PseudoPrime.LLS.PaperStatements
