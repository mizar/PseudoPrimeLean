/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularDualScaleInteriorComparison
public import PseudoPrime.LLS.TriangularSignedSharpConductorComparison
public import PseudoPrime.LLS.TriangularLargeFactorComparison

/-!
# Interior dual-scale conductor budgets and their numerical limitation

Evaluate the remaining averaged arithmetic terms and connect the ambient conductor
comparison to a witness gap. Quantify why this coarse comparison cannot certify
the small-scale coefficient-0.283 target by error reduction alone.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH and small-prime containment, for 1≤x with log x≤36, bound the finite
principal sum by the exact conductor logarithm sum and signed interior Gamma cost.
Remove the scale-one arithmetic pair by aggregate positivity and bound the principal
terms numerically. The conductor coefficient is 72-log x; no left-contour error remains. -/
theorem triangular18_principal_sum_le_dual_interior_conductor_numeric {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 1 ≤ x) (hlog : Real.log x ≤ 36)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
              (1 : DirichletCharacter ℂ q) x n).re) ≤
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
        1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        (72 - Real.log x) * subgroupConductorLogSum H +
        ((H.index : ℝ) - 1) * (-81 + (3 / 2) * Real.log x) := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hf : Finset.univ.filter (fun χ : A ↦ χ.val ≠ 1) = Finset.univ.erase (1 : A) := by
    have he (χ : A) : χ.val = 1 ↔ χ = 1 := by
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    apply Finset.ext
    intro χ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
      not_congr (he χ)]
  have hcard : ((Finset.univ.erase (1 : A)).card : ℝ) = (H.index : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))),
      Nat.cast_one, NumberTheory.card_subgroupAnnihilator]
  have hcond :
    (∑ χ ∈ Finset.univ.erase (1 : A), Real.log χ.val.conductor) = subgroupConductorLogSum H := by
    unfold subgroupConductorLogSum
    apply Finset.sum_congr
    · apply Finset.ext
      intro χ
      simp only [Finset.mem_erase, Finset.mem_univ]
    · intro χ _
      rfl
  have hp : triangularKernelProfile 18 x = 36 - Real.log x := by
    unfold triangularKernelProfile
    rw [abs_of_nonneg (Real.log_nonneg hx)]
    norm_num only
    exact max_eq_right (sub_nonneg.mpr hlog)
  have hb := triangular18_finite_principal_le_dual_interior H hGRH hx hlog hsmall
  dsimp only at hb
  rw [hf, hcard, hcond, hp] at hb
  have ha := triangular18_nonprincipal_arithmetic_pair_sum_lower H (x := 1) (by norm_num only)
  have h1 := triangular18_level_one_arithmetic_upper_of_rh hGRH.riemann (x := 1) (by norm_num only)
  simp only [Real.sqrt_one, Real.one_rpow, mul_one] at h1
  dsimp only at ha
  change (H.index : ℝ) * _ ≤ _
  nlinarith only [hb, ha, h1]

/-- Under GRH, large level factors and small-prime containment in the interior
range, combine the finite principal lower bound with the signed dual conductor upper
budget. Bound the conductor sum by the ambient level logarithm. This is the scalar
comparison whose strict gap would give a factor or subgroup witness. -/
theorem triangular18_dual_interior_comparison_of_large_prime_factors {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 < x) (hlog : Real.log x ≤ 36) (hlarge : ∀ p ∈ q.primeFactors, x ≤ (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → residueInSubgroup q H p) :
    (H.index : ℝ) *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
          36 * Real.log q / (Real.sqrt x - 1)) ≤
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
        1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        ((H.index : ℝ) - 1) * ((72 - Real.log x) * Real.log q - 81 + (3 / 2) * Real.log x) := by
  have hb := triangular18_level_prime_budget_le_of_large_factors hx hlarge
  have hl :=
    (sub_le_sub_left hb (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ))).trans
      (triangular18_finite_principal_lower_of_rh (q := q) hGRH.riemann (zero_lt_one.trans hx))
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg H.index)
  have hc :=
    hm.trans
      (triangular18_principal_sum_le_dual_interior_conductor_numeric H hGRH hx.le hlog hsmall)
  have hcoef : 0 ≤ 72 - Real.log x := by linarith only [hlog]
  have hu := mul_le_mul_of_nonneg_left (subgroupConductorLogSum_le H) hcoef
  nlinarith only [hc, hu]

/-- Under GRH, 1<x with log x≤36 and a strict scalar interior gap, a prime at
most x divides the level or lies outside the subgroup. Absence of a witness gives
the large-factor and containment conditions, contradicting the proved comparison. -/
theorem exists_prime_factor_or_outside_of_triangular18_dual_interior_gap {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 < x) (hlog : Real.log x ≤ 36)
    (hgap :
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
          1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
          602600000 +
          ((H.index : ℝ) - 1) * ((72 - Real.log x) * Real.log q - 81 + (3 / 2) * Real.log x) <
        (H.index : ℝ) *
          (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
            36 * Real.log q / (Real.sqrt x - 1))) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ (p ∣ q ∨ ¬residueInSubgroup q H p) := by
  classical
  by_contra hnone
  have hlarge (p : ℕ) (hp : p ∈ q.primeFactors) : x ≤ (p : ℝ) := by
    by_contra hlt
    exact
      hnone
        ⟨p, Nat.prime_of_mem_primeFactors hp, (lt_of_not_ge hlt).le,
          Or.inl (Nat.dvd_of_mem_primeFactors hp)⟩
  have hsmall (p : ℕ) (hp : p.Prime) (_ : ¬p ∣ q) (hle : (p : ℝ) ≤ x) :
    residueInSubgroup q H p := by
    by_contra hout
    exact hnone ⟨p, hp, hle, Or.inr hout⟩
  exact
    (not_le_of_gt hgap)
      (triangular18_dual_interior_comparison_of_large_prime_factors H hGRH hx hlog hlarge hsmall)

/-- For L≥100, h≥4 and x=(283/1000)L² with 0≤log x≤11, the ambient conductor
budget alone is at least h times the ideal triangular cutoff main term. Bound sqrt x
by (533/1000)L and the mass by 72. This proves that the coarse ambient dual comparison
cannot certify this range merely by reducing its nonnegative error costs; it says
nothing against the witness theorem or the exact conductor comparison. -/
theorem triangular18_dual_interior_ambient_budget_ge_main {L h x : ℝ} (hL : 100 ≤ L) (hh : 4 ≤ h)
    (hx : x = (283 / 1000) * L ^ 2) (hlog0 : 0 ≤ Real.log x) (hlog11 : Real.log x ≤ 11) :
    h * (Real.sqrt x * (68 + 4 * Real.exp (-18))) ≤
      (h - 1) * ((72 - Real.log x) * L - 81 + (3 / 2) * Real.log x) := by
  have hL0 : 0 ≤ L := (by norm_num only : (0 : ℝ) ≤ 100).trans hL
  have hs : Real.sqrt x ≤ (533 / 1000) * L := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact mul_nonneg (by norm_num only) hL0
    · rw [hx]
      nlinarith only [sq_nonneg L]
  have he : Real.exp (-18) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num only)
  have hm : Real.sqrt x * (68 + 4 * Real.exp (-18)) ≤ (38376 / 1000) * L := by
    have hc : 68 + 4 * Real.exp (-18) ≤ (72 : ℝ) := by linarith only [he]
    calc
      _ ≤ Real.sqrt x * 72 := mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg x)
      _ ≤ ((533 / 1000) * L) * 72 := mul_le_mul_of_nonneg_right hs (by norm_num only)
      _ = _ := by ring
  have hb : 61 * L - 81 ≤ (72 - Real.log x) * L - 81 + (3 / 2) * Real.log x := by
    have hp := mul_le_mul_of_nonneg_right hlog11 hL0
    linarith only [hp, hlog0]
  have hb0 : 0 ≤ 61 * L - 81 := by linarith only [hL]
  have hratio : (3 / 4) * h ≤ h - 1 := by linarith only [hh]
  have hunit : (38376 / 1000) * L ≤ (3 / 4) * (61 * L - 81) := by linarith only [hL]
  have hh0 : 0 ≤ h := (by norm_num only : (0 : ℝ) ≤ 4).trans hh
  calc
    _ ≤ h * ((38376 / 1000) * L) := mul_le_mul_of_nonneg_left hm hh0
    _ ≤ h * ((3 / 4) * (61 * L - 81)) := mul_le_mul_of_nonneg_left hunit hh0
    _ = ((3 / 4) * h) * (61 * L - 81) := by ring
    _ ≤ (h - 1) * (61 * L - 81) := mul_le_mul_of_nonneg_right hratio hb0
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by linarith only [hh])

end PseudoPrime.LLS.PaperStatements
