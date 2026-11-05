/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularDualScaleNumeric
public import PseudoPrime.LLS.PaperStatements.TriangularScaleOneCredit

/-! # All-scale triangular comparison with scale-one credit -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, prime-factor exclusion and containment through the cutoff, retain the
finite scale-one principal sum in the all-scale conductor comparison. Apply the signed
dual comparison, the scale-one group average, and both Gamma bounds. This is the
numerical budget used to extract an actual witness from a strict credited gap. -/
theorem triangular18_credited_numeric {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 1 ≤ x)
    (hX : 0 ≤ X) (hlarge : ∀ p : ℕ, p.Prime → p ∣ q → X < (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup q H p) :
    (H.index : ℝ) *
          (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
            ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
                (1 : DirichletCharacter ℂ q) x n).re) +
        2 * (H.index : ℝ) *
          (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
            ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
                (1 : DirichletCharacter ℂ 1) 1 n).re) ≤
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
        1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        (36 + triangularKernelProfile 18 x) * subgroupConductorLogSum H +
        ((H.index : ℝ) - 1) * 11964 := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let G := fun (i : A) (ψ : DirichletCharacter ℂ i.val.conductor) (y : ℝ) ↦
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
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
  have hg :
    (∑ χ ∈ Finset.univ.erase (1 : A),
        (G χ χ.val.primitiveCharacter x + G χ (χ.val.primitiveCharacter)⁻¹ x⁻¹).re) ≤
      ((H.index : ℝ) - 1) * 12000 := by
    have hp : 0 < x := zero_lt_one.trans_le hx
    have hs :
      ∀ χ : A,
        (G χ χ.val.primitiveCharacter x + G χ (χ.val.primitiveCharacter)⁻¹ x⁻¹).re ≤
          (12000 : ℝ) := by
      intro χ
      have h1 := triangular18_gamma_re_le χ.val.primitiveCharacter hp
      have h2 := triangular18_gamma_re_le (χ.val.primitiveCharacter)⁻¹ (inv_pos.mpr hp)
      change (G χ χ.val.primitiveCharacter x).re ≤ 6000 at h1
      change (G χ (χ.val.primitiveCharacter)⁻¹ x⁻¹).re ≤ 6000 at h2
      rw [Complex.add_re]
      linarith only [h1, h2]
    have ht := Finset.sum_le_sum (s := Finset.univ.erase (1 : A)) (fun χ _ ↦ hs χ)
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at ht
    exact ht
  have hb := triangular18_finite_principal_le_dual_signed H hGRH hx hsmall
  dsimp only at hb
  rw [hf, hcard, hcond] at hb
  have ha := triangular18_scaleOne_pair_lower H hX hlarge hsmall
  have h1 := triangular18_level_one_arithmetic_upper_of_rh hGRH.riemann (x := 1) (by norm_num only)
  simp only [Real.sqrt_one, Real.one_rpow, mul_one] at h1
  dsimp only at ha
  change (H.index : ℝ) * _ + 2 * (H.index : ℝ) * _ ≤ _
  change
    (H.index : ℝ) * _ ≤
      triangularKernelProfile 18 x * subgroupConductorLogSum H +
            (∑ χ ∈ Finset.univ.erase (1 : A),
              (G χ χ.val.primitiveCharacter x + G χ (χ.val.primitiveCharacter)⁻¹ x⁻¹).re) +
            300000000 * Real.sqrt x⁻¹ +
            1300000 * (x⁻¹) ^ (1 / 4 : ℝ) +
            36 * subgroupConductorLogSum H -
          _ -
          36 * ((H.index : ℝ) - 1) +
        300000000 * Real.sqrt x +
        1300000 * x ^ (1 / 4 : ℝ) at hb
  nlinarith only [hb, ha, h1, hg]

/-- Under GRH, exclusion of prime factors and containment through the cutoff imply the
credited comparison at every scale above one. Combine the finite principal lower bound
with the signed conductor budget and its scale-one credit. -/
theorem triangular18_credited_large_factors {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 < x)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ q → x < (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → NumberTheory.residueInSubgroup q H p) :
    (H.index : ℝ) *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
            36 * Real.log q / (Real.sqrt x - 1) +
          2 *
            (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
                  (1 : DirichletCharacter ℂ 1) 1 n).re)) ≤
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
        1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        ((H.index : ℝ) - 1) * ((36 + triangularKernelProfile 18 x) * Real.log q + 11964) := by
  have hlarg (p : ℕ) (hp : p ∈ q.primeFactors) : x ≤ (p : ℝ) := by
    exact (hlarge p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)).le
  have hb := triangular18_prime_budget_le_of_large hx hlarg
  have hl :=
    (sub_le_sub_left hb (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ))).trans
      (triangular18_finite_principal_lower_of_rh (q := q) hGRH.riemann (zero_lt_one.trans hx))
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg H.index)
  have hc := triangular18_credited_numeric H hGRH hx.le (zero_lt_one.trans hx).le hlarge hsmall
  have hcoef : 0 ≤ 36 + triangularKernelProfile 18 x := by
    have hp := triangularKernelProfile_nonneg 18 x
    linarith only [hp]
  have hu := mul_le_mul_of_nonneg_left (subgroupConductorLogSum_le H) hcoef
  nlinarith only [hc, hm, hu]

/-- Under GRH, a strict all-scale credited gap yields a prime factor or a prime outside
the subgroup. The absence of such a prime supplies strict prime-factor exclusion through
the cutoff, including the endpoint, and the small-prime containment needed above. -/
theorem exists_prime_credited_gap {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 < x)
    (hgap :
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
          1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
          602600000 +
          ((H.index : ℝ) - 1) * ((36 + triangularKernelProfile 18 x) * Real.log q + 11964) <
        (H.index : ℝ) *
          (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
              36 * Real.log q / (Real.sqrt x - 1) +
            2 *
              (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
                ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
                    (1 : DirichletCharacter ℂ 1) 1 n).re))) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ (p ∣ q ∨ ¬NumberTheory.residueInSubgroup q H p) := by
  classical
  by_contra hnone
  have hlarge (p : ℕ) (hp : p.Prime) (hd : p ∣ q) : x < (p : ℝ) := by
    by_contra h
    exact hnone ⟨p, hp, le_of_not_gt h, Or.inl hd⟩
  have hsmall (p : ℕ) (hp : p.Prime) (_ : ¬p ∣ q) (hle : (p : ℝ) ≤ x) :
    NumberTheory.residueInSubgroup q H p := by
    by_contra hout
    exact hnone ⟨p, hp, hle, Or.inr hout⟩
  exact (not_le_of_gt hgap) (triangular18_credited_large_factors H hGRH hx hlarge hsmall)

end PseudoPrime.LLS.PaperStatements
