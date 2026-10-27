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
# Interior subgroup comparison retaining signed oscillating zeros

Keep the finite primitive zero aggregate throughout the Gamma and conductor
comparison, so sharper zero cancellation can replace the absolute-mass estimate.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The finite nonprincipal primitive annihilator sum of real oscillating zero
series for the alpha-18 kernel at scale x. Each series uses the primitive conductor.
This total definition retains the zero signs; GRH and positivity are assumptions of
the later comparison theorems, not of the definition. -/
noncomputable def triangular18_annihilator_zeroRealSum {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (x : ℝ) : ℝ :=
  letI := Classical.propDecidable
  letI : ∀ i : NumberTheory.subgroupAnnihilator H, NeZero i.val.conductor := fun i ↦
    ⟨i.val.conductor_ne_zero⟩
  ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
    (∑' ρ : ℂ,
        (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).oscillatingZeroTerm
          χ.val.primitiveCharacter x ρ).re

/-- Under GRH, small-prime containment and 1≤x with log x≤36, the finite principal
sum times the index plus the signed primitive zero aggregate is bounded by the
conductor profile, the signed Gamma budget and both principal scale costs. Split off
the principal character and evaluate the Gamma terms without replacing zeros by norms. -/
theorem triangular18_finite_principal_add_zero_le_dual_interior {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 1 ≤ x) (hlog : Real.log x ≤ 36)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    letI := Classical.propDecidable
    letI : ∀ i : NumberTheory.subgroupAnnihilator H, NeZero i.val.conductor := fun i ↦
      ⟨i.val.conductor_ne_zero⟩
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    let S := Finset.univ.filter (fun i : NumberTheory.subgroupAnnihilator H ↦ i.val ≠ 1)
    (H.index : ℝ) * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re) +
        ∑ i ∈ S, (∑' ρ : ℂ, K.oscillatingZeroTerm i.val.primitiveCharacter x ρ).re ≤
      triangularKernelProfile 18 x * (∑ i ∈ S, Real.log (i.val.conductor)) +
        (S.card : ℝ) * (-(3 / 2) * (36 - Real.log x) + 9) +
        300000000 * Real.sqrt x⁻¹ +
        1300000 * (x⁻¹) ^ (1 / 4 : ℝ) +
        300000000 * Real.sqrt x +
        1300000 * x ^ (1 / 4 : ℝ) := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let F := fun χ : A ↦ (∑' n : ℕ, K.summand χ.val.primitiveCharacter x n).re
  have hf : Finset.univ.filter (fun χ : A ↦ χ.val ≠ 1) = Finset.univ.erase (1 : A) := by
    have hn (χ : A) : χ.val = 1 ↔ χ = 1 := by
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    apply Finset.ext
    intro χ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
      not_congr (hn χ)]
  have hs := Finset.sum_erase_add (s := Finset.univ) F (Finset.mem_univ (1 : A))
  have hp : F (1 : A) = (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re :=
    congrArg Complex.re (tsum_congr (MellinKernel.principal_primitive_summand_eq_level_one K x))
  rw [hp] at hs
  have hc :=
    MellinKernel.principal_sum_le_primitive_average_of_noSmallPrimes K H (zero_lt_one.trans_le hx)
      hsmall
  let G :=
    fun (i : NumberTheory.subgroupAnnihilator H) (ψ : DirichletCharacter ℂ (i.val.conductor))
      (y : ℝ) ↦
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
  let S := Finset.univ.filter (fun i : NumberTheory.subgroupAnnihilator H ↦ i.val ≠ 1)
  have hpoint (i : NumberTheory.subgroupAnnihilator H) :
    (G i i.val.primitiveCharacter x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re ≤
      -(3 / 2) * (36 - Real.log x) + 9 := by
    have h1 :=
      triangular18_gammaIntegral_re_le_interior i.val.primitiveCharacter (b := 9 / 16)
        (by norm_num only) (by norm_num only) hx hlog
    have h2 :=
      triangular18_inverse_gammaIntegral_re_le_interior (i.val.primitiveCharacter)⁻¹ (b := 9 / 16)
        (by norm_num only) (by norm_num only) hx hlog
    change ((G i i.val.primitiveCharacter x).re + (G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re) ≤ _
    dsimp only at h1 h2
    dsimp only [G, K]
    simp only [Complex.ofReal_inv, triangularMellinKernel] at h1 h2 ⊢
    linarith only [h1, h2]
  have hgb :
    (∑ i ∈ S, (G i i.val.primitiveCharacter x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re) ≤
      (S.card : ℝ) * (-(3 / 2) * (36 - Real.log x) + 9) := by
    have hh := Finset.sum_le_sum (s := S) (fun i _ ↦ hpoint i)
    simpa only [Finset.sum_const, nsmul_eq_mul] using hh
  dsimp only [G, S] at hgb
  have hb := triangular18_annihilator_dual_scale_arithmetic_upper_numeric H hGRH hx
  simp only [Complex.add_re, Finset.sum_add_distrib] at hb
  have hP := triangular18_level_one_arithmetic_upper_of_rh hGRH.riemann (zero_lt_one.trans_le hx)
  dsimp only at hb ⊢
  rw [hf] at hb ⊢
  change (H.index : ℝ) * _ ≤ ∑ χ : A, F χ at hc
  rw [hf] at hgb
  simp only [Complex.add_re, Finset.sum_add_distrib] at hgb
  linarith only [hc, hs, hb, hP, hgb]

/-- Under the same hypotheses, express the zero-retained finite comparison using
the exact conductor logarithm sum. Its coefficient is 36-log x and its Gamma constant
is -45+3log x/2 per nonprincipal member. Identify the annihilator cardinality and
profile. This is the numerical interface for a sharper signed zero lower bound. -/
theorem triangular18_principal_add_zero_le_dual_interior_conductor_numeric {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 1 ≤ x) (hlog : Real.log x ≤ 36)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    letI := Classical.propDecidable
    letI : ∀ i : NumberTheory.subgroupAnnihilator H, NeZero i.val.conductor := fun i ↦
      ⟨i.val.conductor_ne_zero⟩
    (H.index : ℝ) *
          (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
            ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
                (1 : DirichletCharacter ℂ q) x n).re) +
        triangular18_annihilator_zeroRealSum H x ≤
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
        1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        (36 - Real.log x) * subgroupConductorLogSum H +
        ((H.index : ℝ) - 1) * (-45 + (3 / 2) * Real.log x) := by
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
  have hb := triangular18_finite_principal_add_zero_le_dual_interior H hGRH hx hlog hsmall
  dsimp only at hb
  rw [hf, hcard, hcond, hp] at hb
  change (H.index : ℝ) * _ + _ ≤ _
  dsimp only [triangular18_annihilator_zeroRealSum]
  nlinarith only [hb]

/-- Under GRH, large level factors and small-prime containment in the interior
range, retain the signed zero aggregate on the left of the scalar comparison.
Combine the cutoff lower bound and the zero-retained conductor estimate. This avoids
the extra mass-times-logarithm cost introduced by an absolute zero estimate. -/
theorem triangular18_zero_retained_comparison_of_large_prime_factors {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 < x) (hlog : Real.log x ≤ 36) (hlarge : ∀ p ∈ q.primeFactors, x ≤ (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → residueInSubgroup q H p) :
    (H.index : ℝ) *
          (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
            36 * Real.log q / (Real.sqrt x - 1)) +
        triangular18_annihilator_zeroRealSum H x ≤
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
        1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        ((H.index : ℝ) - 1) * ((36 - Real.log x) * Real.log q - 45 + (3 / 2) * Real.log x) := by
  have hb := triangular18_level_prime_budget_le_of_large_factors hx hlarge
  have hl :=
    (sub_le_sub_left hb (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ))).trans
      (triangular18_finite_principal_lower_of_rh (q := q) hGRH.riemann (zero_lt_one.trans hx))
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg H.index)
  have hupp :=
    triangular18_principal_add_zero_le_dual_interior_conductor_numeric H hGRH hx.le hlog hsmall
  have hc := (add_le_add_left hm (triangular18_annihilator_zeroRealSum H x)).trans hupp
  have hcoef : 0 ≤ 36 - Real.log x := by linarith only [hlog]
  have hu := mul_le_mul_of_nonneg_left (subgroupConductorLogSum_le H) hcoef
  nlinarith only [hc, hu]

/-- Under GRH, 1<x with log x≤36 and a strict zero-retained scalar gap, a prime
at most x divides the level or lies outside the subgroup. The no-witness assumption
gives the large-factor and containment conditions, contradicting the comparison.
The signed zero aggregate is part of the gap and is not assumed nonnegative. -/
theorem exists_prime_factor_or_outside_of_triangular18_zero_retained_gap {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 < x) (hlog : Real.log x ≤ 36)
    (hgap :
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
          1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
          ((H.index : ℝ) - 1) * ((36 - Real.log x) * Real.log q - 45 + (3 / 2) * Real.log x) <
        (H.index : ℝ) *
            (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
              36 * Real.log q / (Real.sqrt x - 1)) +
          triangular18_annihilator_zeroRealSum H x) :
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
      (triangular18_zero_retained_comparison_of_large_prime_factors H hGRH hx hlog hlarge hsmall)

end PseudoPrime.LLS.PaperStatements
