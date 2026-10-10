/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ShiftedGammaBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedContourResidues
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TrivialZeroMultiplicity

/-!
# Shifted residues at gamma-forced Dirichlet zeros

Identify the multiplicity-one residues with the general gamma series and apply
its integrated bound to both character parities.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character, sigma>=1 and Re kappa>=0, a gamma
zero at -kappa-2m has shifted residue equal to minus the general gamma residue.
Its multiplicity is one; the shifted point is nonzero by its negative real part. -/
theorem shiftedLogResidueAt_eq_neg_gammaShiftResidue {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) {κ : ℂ} (hκ : 0 ≤ κ.re) {σ : ℝ} (hσ : 1 ≤ σ) (x : ℝ) (m : ℕ)
    (hΓ : DirichletCharacter.gammaFactor χ (-κ - 2 * (m : ℂ)) = 0) :
    shiftedLogResidueAt χ x σ (-((σ : ℂ) + κ + 2 * (m : ℂ))) =
      -General.gammaShiftResidue x κ σ m := by
  have hs : -((σ : ℂ) + κ + 2 * (m : ℂ)) ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
      Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero,
      Complex.zero_re] at hr
    linarith only [hr, hσ, hκ, Nat.cast_nonneg (α := ℝ) m]
  have he : (σ : ℂ) + -((σ : ℂ) + κ + 2 * (m : ℂ)) = -κ - 2 * (m : ℂ) := by ring
  have hm :=
    dirichletLFunctionZeroMultiplicity_of_gamma_zero_eq_one hp hne (gammaFactor_zero_re_nonpos hΓ)
      hΓ
  rw [shiftedLogResidueAt, ite_eq_right hs, he, hm]
  simp only [Nat.cast_one, neg_mul, one_mul, General.gammaShiftResidue, neg_div, neg_sq]

/-- For an even character of nonzero modulus, the gamma factor vanishes at -2m
for every natural m, including zero. Apply the zero classification of the totalized
real archimedean gamma factor. For primitive nonprincipal characters these locations
then supply the even trivial-zero residues; parity alone asserts only gamma vanishing. -/
theorem gammaFactor_zero_even_location {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (he : χ.Even)
    (m : ℕ) : DirichletCharacter.gammaFactor χ (-(0 : ℂ) - 2 * (m : ℂ)) = 0 := by
  rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]
  exact ⟨m, by ring⟩

/-- For an odd character, every negative odd integer is a gamma-factor zero.
Apply the shifted real gamma zero classification. -/
theorem gammaFactor_zero_odd_location {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (ho : χ.Odd)
    (m : ℕ) : DirichletCharacter.gammaFactor χ (-(1 : ℂ) - 2 * (m : ℂ)) = 0 := by
  rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]
  exact ⟨m, by ring⟩

/-- For a primitive nonprincipal character of nonzero modulus, σ ≥ 1, and a complex κ
with Re κ ≥ 0, assume the gamma factor vanishes at every -κ-2m.
For any real x, the corresponding shifted residue tsum equals minus gammaShiftSum.
Use the multiplicity-one identity termwise and commute negation with tsum.
This identity alone does not assert convergence; x > 1 supplies it for later estimates. -/
theorem tsum_shiftedLogResidueAt_eq_neg_gammaShiftSum {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) {κ : ℂ} (hκ : 0 ≤ κ.re) {σ : ℝ}
    (hσ : 1 ≤ σ) (x : ℝ) (hΓ : ∀ m : ℕ, DirichletCharacter.gammaFactor χ (-κ - 2 * (m : ℂ)) = 0) :
    (∑' m : ℕ, shiftedLogResidueAt χ x σ (-((σ : ℂ) + κ + 2 * (m : ℂ)))) =
      -General.gammaShiftSum x κ σ := by
  simp only [shiftedLogResidueAt_eq_neg_gammaShiftResidue hp hne hκ hσ x _ (hΓ _), tsum_neg,
    General.gammaShiftSum]

/-- For a primitive nonprincipal character, x > 1, and a complex κ with Re κ ≥ 0,
assume gamma-factor vanishing at every -κ-2m. The shifted residue series integrated
over real σ > 1 and divided by log x has norm at most `2 / (x (log x)²)`.
Identify the series with minus the general gamma sum and apply its integrated bound.
This supplies the gamma error used in both parity specializations. -/
theorem norm_integrated_shiftedGammaResidues_div_log_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) {κ : ℂ} (hκ : 0 ≤ κ.re) {x : ℝ}
    (hx : 1 < x) (hΓ : ∀ m : ℕ, DirichletCharacter.gammaFactor χ (-κ - 2 * (m : ℂ)) = 0) :
    ‖(∫ σ : ℝ in Set.Ioi 1, ∑' m : ℕ, shiftedLogResidueAt χ x σ (-((σ : ℂ) + κ + 2 * (m : ℂ)))) /
          (Real.log x : ℂ)‖ ≤
      2 / (x * (Real.log x) ^ 2) := by
  have he :
    (∫ σ : ℝ in Set.Ioi 1, ∑' m : ℕ, shiftedLogResidueAt χ x σ (-((σ : ℂ) + κ + 2 * (m : ℂ)))) =
      -(∫ σ : ℝ in Set.Ioi 1, General.gammaShiftSum x κ σ) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro σ hσ
    exact tsum_shiftedLogResidueAt_eq_neg_gammaShiftSum hp hne hκ hσ.le x hΓ
  rw [he, neg_div, norm_neg]
  exact General.norm_integrated_gammaShiftSum_div_log_le hx hκ

/-- For an even primitive nonprincipal character and x>1, the integrated shifted
residues at all nonpositive even integers have normalized norm at most 2/(x*log(x)^2).
Use shift zero in the general bound, including the m=0 residue. -/
theorem norm_integrated_even_shiftedGammaResidues_div_log_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (he : χ.Even) {x : ℝ}
    (hx : 1 < x) :
    ‖(∫ σ : ℝ in Set.Ioi 1, ∑' m : ℕ, shiftedLogResidueAt χ x σ (-((σ : ℂ) + 0 + 2 * (m : ℂ)))) /
          (Real.log x : ℂ)‖ ≤
      2 / (x * (Real.log x) ^ 2) :=
  norm_integrated_shiftedGammaResidues_div_log_le hp hne (by norm_num only [Complex.zero_re]) hx
    (gammaFactor_zero_even_location he)

/-- For an odd primitive nonprincipal character and x>1, the integrated shifted
residues at negative odd integers have normalized norm at most 2/(x*log(x)^2).
Use shift one in the general gamma bound. -/
theorem norm_integrated_odd_shiftedGammaResidues_div_log_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (ho : χ.Odd) {x : ℝ}
    (hx : 1 < x) :
    ‖(∫ σ : ℝ in Set.Ioi 1, ∑' m : ℕ, shiftedLogResidueAt χ x σ (-((σ : ℂ) + 1 + 2 * (m : ℂ)))) /
          (Real.log x : ℂ)‖ ≤
      2 / (x * (Real.log x) ^ 2) :=
  norm_integrated_shiftedGammaResidues_div_log_le hp hne (by norm_num only [Complex.one_re]) hx
    (gammaFactor_zero_odd_location ho)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
