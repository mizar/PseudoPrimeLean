/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularFamilyZeroMass

/-! # Signed triangular primitive arithmetic and subgroup comparison -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal GRH data and scale at least one, the alpha-18
arithmetic norm is bounded by 36 log(q), the negative real scale-one sums,
and the explicit remainder. The fixed cost is 165000. This combines the signed
zero budget with the oscillating phase bound and the precise contour remainder. -/
theorem triangular18_primitive_arithmetic_norm_le_signed {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖∑' n : ℕ, K.summand χ x n‖ ≤
      36 * Real.log q - (∑' n : ℕ, K.summand χ 1 n).re - (∑' n : ℕ, K.summand χ⁻¹ 1 n).re + 165000 +
        4000000000000 * (Real.log q + 284) * x ^ (-9 / 16 : ℝ) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let S := ∑' n : ℕ, K.summand χ x n
  let Z := ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ
  have hR := triangular18_primitive_remainder_norm_le_precise hq hGRH hp hne hinv hx
  have hs :=
    MellinKernel.summable_oscillatingZeroTerm K hq hGRH hp hne hinv (zero_lt_one.trans_le hx)
  have hZ : ‖Z‖ ≤ ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ := by
    have ht := norm_tsum_le_tsum_norm hs.norm
    have he : (∑' ρ : ℂ, ‖K.oscillatingZeroTerm χ x ρ‖) = ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ :=
      tsum_congr (MellinKernel.norm_oscillatingZeroTerm K χ (zero_lt_one.trans_le hx))
    exact ht.trans_eq he
  have hM := triangular18_absoluteMass_le_signed_arithmetic hq hGRH hp hne hinv
  have ht := norm_sub_le (S + Z) Z
  have he : (S + Z) - Z = S := by ring
  rw [he] at ht
  change ‖S‖ ≤ _
  linarith only [ht, hR, hZ, hM]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH and containment of eligible primes through X, bound the alpha-18
finite principal sum by the primitive annihilator budgets while retaining both
scale-one arithmetic real parts. Primitivization corrections are summed with
their signs before using this upper bound. This is the subgroup comparison
entry point for reducing the conservative zero-mass constant. -/
theorem triangular18_principal_sum_le_signed_budgets_of_noSmallPrimes {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 1 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    letI := Classical.propDecidable
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (H.index : ℝ) * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re) ≤
      ∑ χ : NumberTheory.subgroupAnnihilator H,
        if χ.val = 1 then (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re
        else
          36 * Real.log χ.val.conductor - (∑' n : ℕ, K.summand χ.val.primitiveCharacter 1 n).re -
              (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 n).re +
            165000 +
            4000000000000 * (Real.log χ.val.conductor + 284) * x ^ (-9 / 16 : ℝ) := by
  classical
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hc :=
    MellinKernel.principal_sum_le_primitive_average_of_noSmallPrimes K H (zero_lt_one.trans_le hx)
      hsmall
  apply hc.trans
  apply Finset.sum_le_sum
  intro χ _
  by_cases hn : χ.val = 1
  · rw [ite_eq_left hn, hn, tsum_congr (MellinKernel.principal_primitive_summand_eq_level_one K x)]
  · rw [ite_eq_right hn]
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    have hp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ.val hn
    have hq := NumberTheory.three_le_conductor_of_ne_one χ.val hn
    have hb :=
      triangular18_primitive_arithmetic_norm_le_signed ((by norm_num only : 2 ≤ 3).trans hq) hGRH
        (DirichletCharacter.primitiveCharacter_isPrimitive χ.val) hp (inv_ne_one.mpr hp) hx
    exact (Complex.re_le_norm _).trans hb

end PseudoPrime.LLS.PaperStatements
