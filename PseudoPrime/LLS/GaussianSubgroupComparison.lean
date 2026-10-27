/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianPrincipalBounds
public import PseudoPrime.LLS.GaussianPrimitiveRemainderBounds
public import PseudoPrime.LLS.ConductorSumComparison

/-! # Conductor-sensitive Gaussian subgroup comparison

Actual principal and nonprincipal bounds control the signed primitive average.
The primary comparison retains each nonprincipal conductor logarithm and the
precise variable-scale remainder, rather than replacing it with the coarse U contract.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under primitive nonprincipal GRH data, conductor 3≤m≤q, ambient q≥20000
and x≥4, the actual Gaussian sum is at most (161/400)log m+1811 plus the
U=128 remainder contract. Combine the actual zero-sum and remainder norm bounds. -/
theorem gaussian_primitive_sum_re_le_contract {q m : ℕ} [NeZero m] (hq : 20000 ≤ q) (hm : 3 ≤ m)
    (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 4 ≤ x) :
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n).re ≤
      (161 / 400 : ℝ) * Real.log m + 1811 + 128 * (1 + Real.log q * Real.log x / Real.sqrt x) := by
  let S := ∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ
  have hxpos : 0 < x := (by norm_num only : (0 : ℝ) < 4).trans_le hx
  have hz := norm_gaussian_oscillatingZeroSum_lt (by linarith only [hm]) hGRH hp hne hinv hxpos
  have hr := norm_gaussian_primitive_remainder_le_contract hq hm hmq hp hne hinv hGRH hx
  have hn : ‖S‖ ≤ ‖S + Z‖ + ‖Z‖ := by
    have h := norm_sub_le (S + Z) Z
    rw [add_sub_cancel_right] at h
    exact h
  have hre := Complex.re_le_norm S
  change S.re ≤ _
  linarith only [hz.le, hr, hn, hre]

/-- For a nonprincipal character at q≥20000 under GRH and x≥4, the primitive
Gaussian arithmetic sum obeys the conductor-sensitive U=128 contract. Transfer
to the actual primitive source and its nonprincipal inverse. -/
theorem gaussian_primitiveCharacter_sum_re_le_contract {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 4 ≤ x) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (161 / 400 : ℝ) * Real.log χ.conductor + 1811 +
        128 * (1 + Real.log q * Real.log x / Real.sqrt x) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    gaussian_primitive_sum_re_le_contract hq hm hmq hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hnp (inv_ne_one.mpr hnp) hx

/-- Zero allowance 12871/1000 plus the actual archimedean, pole and left-moment
allowances at ambient level q and scale x. Only the secondary left error replaces
the conductor by q; the leading conductor-log sum remains separate. -/
noncomputable def gaussianAmbientError (q : ℕ) (x : ℝ) : ℝ :=
  12871 / 1000 + 64 / 9 + (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / Real.sqrt x) +
    (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3)

/-- Ambient Gaussian error after transferring the 50000 Euler prefix. Its
zero-mass constant is 159169/50000 when the primitive characters are one on
all prime bases through the prefix. -/
noncomputable def gaussianAmbientErrorPrefix (q : ℕ) (x : ℝ) : ℝ :=
  159169 / 50000 + 64 / 9 + (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / Real.sqrt x) +
    (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3)

/-- Ambient Gaussian error after the 50000-prefix transfer and signed contour
estimates. The archimedean term decays as `512/(27x)`, and the left contour
contributes only its scale decay. -/
noncomputable def gaussianAmbientErrorPrefixSigned (q : ℕ) (x : ℝ) : ℝ :=
  159169 / 50000 + (512 / 27 : ℝ) / x +
    (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / Real.sqrt x) +
    (473 / 10 : ℝ) * x ^ (-9 / 16 : ℝ)

/-- Ambient Gaussian error after transferring the 1000 Euler prefix. -/
noncomputable def gaussianAmbientErrorPrefix1000 (q : ℕ) (x : ℝ) : ℝ :=
  5969 / 1000 + 64 / 9 + (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / Real.sqrt x) +
    (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3)

/-- The prefix-transfer error is no larger than the original ambient error. -/
theorem gaussianAmbientErrorPrefix_le {q : ℕ} {x : ℝ} :
    gaussianAmbientErrorPrefix q x ≤ gaussianAmbientError q x := by
  dsimp only [gaussianAmbientErrorPrefix, gaussianAmbientError]
  nlinarith only

/-- Under GRH at q≥20000 and x≥4, a finite character subgroup primitive
Gaussian average is bounded by the principal main term with error fourteen,
the exact nonprincipal conductor-log sum, and a per-character ambient error.
Use the actual variable-scale arithmetic bounds and retain their leading conductors. -/
private theorem gaussian_primitive_average_re_le_variable_scale {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] [DecidableEq S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 4 ≤ x) :
    (∑ χ : S, ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) +
        (161 / 400 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Fintype.card S - 1 : ℕ) : ℝ) * (gaussianAmbientError q x) := by
  classical
  let F := fun χ : S ↦ (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re
  have h1 : F 1 ≤ Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) := by
    simpa only [F, Subgroup.coe_one] using
      gaussian_primitive_principal_sum_upper_fourteen hGRH.riemann
        ((by norm_num only : (0 : ℝ) < 4).trans_le hx)
  have hrest :
    ∑ χ ∈ Finset.univ.erase (1 : S), F χ ≤
      (161 / 400 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Finset.univ.erase (1 : S)).card : ℝ) * (gaussianAmbientError q x) := by
    calc
      _ ≤
          ∑ χ ∈ Finset.univ.erase (1 : S),
            ((161 / 400 : ℝ) * Real.log χ.val.conductor + (gaussianAmbientError q x)) :=
        by
        apply Finset.sum_le_sum
        intro χ hχ
        have hn : χ.val ≠ 1 := fun he ↦ (Finset.mem_erase.mp hχ).1 (Subtype.ext he)
        have h :=
          gaussian_primitiveCharacter_sum_re_le_variable_scale hq χ.val hn hGRH
            (by linarith only [hx])
        have hmpos : (0 : ℝ) < χ.val.conductor :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.val.conductor_ne_zero)
        have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.val.conductor_dvd_level
        have hlog := Real.log_le_log hmpos (Nat.cast_le.mpr hmq)
        have hcoef : 0 ≤ (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * (16 / 5) :=
          mul_nonneg
            (mul_nonneg (by norm_num only) (Real.rpow_nonneg (by linarith only [hx] : 0 ≤ x) _))
            (by norm_num only)
        have hleft := mul_le_mul_of_nonneg_left hlog hcoef
        change F χ ≤ _ at h
        dsimp only [gaussianAmbientError]
        nlinarith only [h, hleft]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : S)), Finset.card_univ] at hrest
  have he := Finset.sum_erase_eq_sub (f := F) (Finset.mem_univ (1 : S))
  change
    Complex.reCLM
        (∑ χ : S, ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤
      _
  rw [map_sum]
  change (∑ χ : S, F χ) ≤ _
  linarith only [h1, hrest, he]

/-- Average primitive Gaussian sums using the transferred 50000-prefix bound
for each nonprincipal character. The conductor logarithms stay separate, while
the common ambient error uses the reduced additive constant. -/
private theorem gaussian_primitive_average_re_le_variable_scale_prefix_gain {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] [DecidableEq S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hsmall : ∀ χ : S, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 50000 → χ.val.primitiveCharacter p = 1) {x : ℝ}
    (hx : 4 ≤ x) :
    (∑ χ : S, ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) +
        (161 / 400 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Fintype.card S - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefix q x := by
  classical
  let F := fun χ : S ↦ (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re
  have h1 : F 1 ≤ Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) := by
    simpa only [F, Subgroup.coe_one] using
      gaussian_primitive_principal_sum_upper_fourteen hGRH.riemann
        ((by norm_num only : (0 : ℝ) < 4).trans_le hx)
  have hrest :
    ∑ χ ∈ Finset.univ.erase (1 : S), F χ ≤
      (161 / 400 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Finset.univ.erase (1 : S)).card : ℝ) * gaussianAmbientErrorPrefix q x := by
    calc
      _ ≤
          ∑ χ ∈ Finset.univ.erase (1 : S),
            ((161 / 400 : ℝ) * Real.log χ.val.conductor + gaussianAmbientErrorPrefix q x) :=
        by
        apply Finset.sum_le_sum
        intro χ hχ
        have hn : χ.val ≠ 1 := fun he ↦ (Finset.mem_erase.mp hχ).1 (Subtype.ext he)
        have h :=
          gaussian_primitiveCharacter_sum_re_le_variable_scale_prefix_gain hq χ.val hn hGRH
            (hsmall χ) (by linarith only [hx])
        have hmpos : (0 : ℝ) < χ.val.conductor :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.val.conductor_ne_zero)
        have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.val.conductor_dvd_level
        have hlog := Real.log_le_log hmpos (Nat.cast_le.mpr hmq)
        have hcoef : 0 ≤ (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * (16 / 5) := by positivity
        have hleft := mul_le_mul_of_nonneg_left hlog hcoef
        change F χ ≤ _
        dsimp only [gaussianAmbientErrorPrefix]
        nlinarith only [h, hleft]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : S)), Finset.card_univ] at hrest
  have he := Finset.sum_erase_eq_sub (f := F) (Finset.mem_univ (1 : S))
  change
    Complex.reCLM
        (∑ χ : S, ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤
      _
  rw [map_sum]
  change (∑ χ : S, F χ) ≤ _
  linarith only [h1, hrest, he]

/-- Average primitive Gaussian sums using the signed 50000-prefix bound.
Each nonprincipal character keeps its conductor logarithm, while the common
ambient error uses the conductor-independent left-contour term. -/
private theorem gaussian_primitive_average_re_le_variable_scale_prefix_gain_signed {q : ℕ}
    [NeZero q] (hq : 20000 ≤ q) (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] [DecidableEq S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hsmall : ∀ χ : S, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 50000 → χ.val.primitiveCharacter p = 1) {x : ℝ}
    (hx : 4 ≤ x) :
    (∑ χ : S, ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) +
        (161 / 400 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Fintype.card S - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefixSigned q x := by
  classical
  let F := fun χ : S ↦ (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re
  have h1 : F 1 ≤ Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) := by
    simpa only [F, Subgroup.coe_one] using
      gaussian_primitive_principal_sum_upper_fourteen hGRH.riemann
        ((by norm_num only : (0 : ℝ) < 4).trans_le hx)
  have hrest :
    ∑ χ ∈ Finset.univ.erase (1 : S), F χ ≤
      (161 / 400 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Finset.univ.erase (1 : S)).card : ℝ) * gaussianAmbientErrorPrefixSigned q x := by
    calc
      _ ≤
          ∑ χ ∈ Finset.univ.erase (1 : S),
            ((161 / 400 : ℝ) * Real.log χ.val.conductor + gaussianAmbientErrorPrefixSigned q x) :=
        by
        apply Finset.sum_le_sum
        intro χ hχ
        have hn : χ.val ≠ 1 := fun he ↦ (Finset.mem_erase.mp hχ).1 (Subtype.ext he)
        have h :=
          gaussian_primitiveCharacter_sum_re_le_variable_scale_prefix_gain_signed hq χ.val hn hGRH
            (hsmall χ) (by linarith only [hx])
        simpa only [F, gaussianAmbientErrorPrefixSigned, add_assoc] using h
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : S)), Finset.card_univ] at hrest
  have he := Finset.sum_erase_eq_sub (f := F) (Finset.mem_univ (1 : S))
  change
    Complex.reCLM
        (∑ χ : S, ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤
      _
  rw [map_sum]
  change (∑ χ : S, F χ) ≤ _
  linarith only [h1, hrest, he]

/-- Average primitive Gaussian sums using the transferred 1000-prefix bound
for each nonprincipal character, with the reduced common ambient error. -/
private theorem gaussian_primitive_average_re_le_variable_scale_prefix1000_gain {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] [DecidableEq S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hsmall : ∀ χ : S, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 1000 → χ.val.primitiveCharacter p = 1) {x : ℝ}
    (hx : 4 ≤ x) :
    (∑ χ : S, ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) +
        (161 / 400 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Fintype.card S - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefix1000 q x := by
  classical
  let F := fun χ : S ↦ (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re
  have h1 : F 1 ≤ Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) := by
    simpa only [F, Subgroup.coe_one] using
      gaussian_primitive_principal_sum_upper_fourteen hGRH.riemann
        ((by norm_num only : (0 : ℝ) < 4).trans_le hx)
  have hrest :
    ∑ χ ∈ Finset.univ.erase (1 : S), F χ ≤
      (161 / 400 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Finset.univ.erase (1 : S)).card : ℝ) * gaussianAmbientErrorPrefix1000 q x := by
    calc
      _ ≤
          ∑ χ ∈ Finset.univ.erase (1 : S),
            ((161 / 400 : ℝ) * Real.log χ.val.conductor + gaussianAmbientErrorPrefix1000 q x) :=
        by
        apply Finset.sum_le_sum
        intro χ hχ
        have hn : χ.val ≠ 1 := fun he ↦ (Finset.mem_erase.mp hχ).1 (Subtype.ext he)
        have h :=
          gaussian_primitiveCharacter_sum_re_le_variable_scale_prefix1000_gain hq χ.val hn hGRH
            (hsmall χ) (by linarith only [hx])
        have hmpos : (0 : ℝ) < χ.val.conductor :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.val.conductor_ne_zero)
        have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.val.conductor_dvd_level
        have hlog := Real.log_le_log hmpos (Nat.cast_le.mpr hmq)
        have hcoef : 0 ≤ (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * (16 / 5) := by positivity
        have hleft := mul_le_mul_of_nonneg_left hlog hcoef
        change F χ ≤ _
        dsimp only [gaussianAmbientErrorPrefix1000]
        nlinarith only [h, hleft]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : S)), Finset.card_univ] at hrest
  have he := Finset.sum_erase_eq_sub (f := F) (Finset.mem_univ (1 : S))
  change
    Complex.reCLM
        (∑ χ : S, ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤
      _
  rw [map_sum]
  change (∑ χ : S, F χ) ≤ _
  linarith only [h1, hrest, he]

/-- Under GRH at q≥20000 and x≥4, if every eligible prime below X lies in H,
the index multiple of the original principal finite sum is at most the numerical
primitive average. Apply the signed no-small-prime comparison and annihilator
cardinality, retaining the exact conductor-log cost and precise remainder. -/
theorem gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 4 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) +
        (161 / 400 : ℝ) * subgroupConductorLogSum H +
        ((H.index - 1 : ℕ) : ℝ) * (gaussianAmbientError q x) := by
  classical
  have hu :=
    gaussian_primitive_average_re_le_variable_scale hq (NumberTheory.subgroupAnnihilator H) hGRH hx
  rw [NumberTheory.card_subgroupAnnihilator] at hu
  change
    Complex.reCLM
        (∑ χ : NumberTheory.subgroupAnnihilator H,
          ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤
      _ at hu
  rw [map_sum] at hu
  exact
    (MellinKernel.principal_sum_le_primitive_average_of_noSmallPrimes gaussianGammaMellinKernel H
          ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hsmall).trans
      hu

/-- Under the same prime exclusion and subgroup assumptions, transfer the
50000-prefix gain to every nonprincipal character in the annihilator. The cutoff
must reach 50000 so every prime in the retained prefix is a unit modulo q. -/
theorem gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes_prefix_gain {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 4 ≤ x)
    (hX : 50000 ≤ X) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊X⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) +
        (161 / 400 : ℝ) * subgroupConductorLogSum H +
        ((H.index - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefix q x := by
  classical
  have hsmallChars :
    ∀ χ : NumberTheory.subgroupAnnihilator H,
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 50000 → χ.val.primitiveCharacter p = 1 := by
    intro χ p hp hpb
    have hpX : (p : ℝ) ≤ X := hpb.trans hX
    have hple : p ≤ ⌊X⌋₊ := (Nat.le_floor_iff' hp.ne_zero).mpr hpX
    have hnot : ¬p ∣ q := by
      intro h
      exact (not_lt_of_ge hple) (hdiv p hp h)
    obtain ⟨u, hu, hval⟩ := hsmall p hp hnot hpX
    have hann := (NumberTheory.mem_subgroupAnnihilator_iff H χ.val).mp χ.property
    have hone := hann u hu
    have hone' : χ.val p = 1 := by
      rw [← hval]
      exact hone
    exact primitiveCharacter_apply_one_of_apply_one χ.val hone'
  have hu :=
    gaussian_primitive_average_re_le_variable_scale_prefix_gain hq
      (NumberTheory.subgroupAnnihilator H) hGRH hsmallChars hx
  rw [NumberTheory.card_subgroupAnnihilator] at hu
  change
    Complex.reCLM
        (∑ χ : NumberTheory.subgroupAnnihilator H,
          ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤
      _ at hu
  rw [map_sum] at hu
  exact
    (MellinKernel.principal_sum_le_primitive_average_of_noSmallPrimes gaussianGammaMellinKernel H
          ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hsmall).trans
      hu

/-- Under the same prime exclusion and subgroup assumptions, transfer the
50000-prefix gain with the signed left-contour error. -/
theorem gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes_prefix_gain_signed {q : ℕ}
    [NeZero q] (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 4 ≤ x)
    (hX : 50000 ≤ X) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊X⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) +
        (161 / 400 : ℝ) * subgroupConductorLogSum H +
        ((H.index - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefixSigned q x := by
  classical
  have hsmallChars :
    ∀ χ : NumberTheory.subgroupAnnihilator H,
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 50000 → χ.val.primitiveCharacter p = 1 := by
    intro χ p hp hpb
    have hpX : (p : ℝ) ≤ X := hpb.trans hX
    have hple : p ≤ ⌊X⌋₊ := (Nat.le_floor_iff' hp.ne_zero).mpr hpX
    have hnot : ¬p ∣ q := by
      intro h
      exact (not_lt_of_ge hple) (hdiv p hp h)
    obtain ⟨u, hu, hval⟩ := hsmall p hp hnot hpX
    have hann := (NumberTheory.mem_subgroupAnnihilator_iff H χ.val).mp χ.property
    have hone := hann u hu
    have hone' : χ.val p = 1 := by
      rw [← hval]
      exact hone
    exact primitiveCharacter_apply_one_of_apply_one χ.val hone'
  have hu :=
    gaussian_primitive_average_re_le_variable_scale_prefix_gain_signed hq
      (NumberTheory.subgroupAnnihilator H) hGRH hsmallChars hx
  rw [NumberTheory.card_subgroupAnnihilator] at hu
  change
    Complex.reCLM
        (∑ χ : NumberTheory.subgroupAnnihilator H,
          ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤
      _ at hu
  rw [map_sum] at hu
  exact
    (MellinKernel.principal_sum_le_primitive_average_of_noSmallPrimes gaussianGammaMellinKernel H
          ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hsmall).trans
      hu

/-- Transfer the 1000-prefix gain to every nonprincipal character in the
annihilator when the cutoff reaches 1000. -/
theorem gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes_prefix1000_gain {q : ℕ}
    [NeZero q] (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 4 ≤ x)
    (hX : 1000 ≤ X) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊X⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) +
        (161 / 400 : ℝ) * subgroupConductorLogSum H +
        ((H.index - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefix1000 q x := by
  classical
  have hsmallChars :
    ∀ χ : NumberTheory.subgroupAnnihilator H,
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 1000 → χ.val.primitiveCharacter p = 1 := by
    intro χ p hp hpb
    have hpX : (p : ℝ) ≤ X := hpb.trans hX
    have hple : p ≤ ⌊X⌋₊ := (Nat.le_floor_iff' hp.ne_zero).mpr hpX
    have hnot : ¬p ∣ q := by
      intro h
      exact (not_lt_of_ge hple) (hdiv p hp h)
    obtain ⟨u, hu, hval⟩ := hsmall p hp hnot hpX
    have hann := (NumberTheory.mem_subgroupAnnihilator_iff H χ.val).mp χ.property
    have hone := hann u hu
    have hone' : χ.val p = 1 := by
      rw [← hval]
      exact hone
    exact primitiveCharacter_apply_one_of_apply_one χ.val hone'
  have hu :=
    gaussian_primitive_average_re_le_variable_scale_prefix1000_gain hq
      (NumberTheory.subgroupAnnihilator H) hGRH hsmallChars hx
  rw [NumberTheory.card_subgroupAnnihilator] at hu
  change
    Complex.reCLM
        (∑ χ : NumberTheory.subgroupAnnihilator H,
          ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n) ≤
      _ at hu
  rw [map_sum] at hu
  exact
    (MellinKernel.principal_sum_le_primitive_average_of_noSmallPrimes gaussianGammaMellinKernel H
          ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hsmall).trans
      hu

/-- Under GRH at q≥20000, x≥4 and nonnegative cutoff, suppose all eligible
primes below the cutoff lie in H and every prime divisor exceeds the natural cutoff.
The actual Gaussian cutoff mass and endpoint main term are bounded by the exact
conductor cost, principal error fourteen, and the variable-scale secondary errors.
The principal finite sum equals level one, so no finite modulus loss remains. -/
theorem gaussian_noSmallPrimes_explicit_inequality_of_no_small_divisor {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x lambda : ℝ} (hx : 4 ≤ x)
    (hl : 0 ≤ lambda) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊lambda * x⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    ((H.index : ℝ) *
            (∫ u in (0 : ℝ)..lambda, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * subgroupConductorLogSum H + 14 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
        ((H.index - 1 : ℕ) : ℝ) * (gaussianAmbientError q x) := by
  have hlo :=
    gaussian_level_one_sum_lower_fourteen hGRH.riemann
      ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hl
  have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg H.index)
  have hhi := gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes hq H hGRH hx hsmall
  have he : Finset.Icc 1 ⌊lambda * x⌋₊ = Finset.Ioc 0 ⌊lambda * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he, ← Complex.re_sum,
    MellinKernel.principal_sum_eq_level_one_of_no_small_prime_divisor gaussianGammaMellinKernel
      (q := q) x hdiv,
    Complex.re_sum] at hhi
  nlinarith only [hm, hhi]

/-- If every eligible prime below X lies in H, every prime divisor exceeds
floor(X), and X reaches 50000, the Gaussian comparison has the reduced prefix
error. The principal finite sum is level one, while the annihilator average
uses the transferred Gaussian prefix bound. -/
theorem gaussian_noSmallPrimes_explicit_inequality_prefix_gain {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x lambda : ℝ} (hx : 4 ≤ x) (hX : 50000 ≤ lambda * x)
    (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊lambda * x⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    ((H.index : ℝ) *
            (∫ u in (0 : ℝ)..lambda, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * subgroupConductorLogSum H + 14 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
        ((H.index - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefix q x := by
  have hl : 0 ≤ lambda := by
    have hxpos : 0 < x := by linarith only [hx]
    by_contra hn
    have hlneg : lambda < 0 := lt_of_not_ge hn
    have hprod : lambda * x < 0 := mul_neg_of_neg_of_pos hlneg hxpos
    linarith only [hX, hprod]
  have hlo :=
    gaussian_level_one_sum_lower_fourteen hGRH.riemann
      ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hl
  have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg H.index)
  have hhi :=
    gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes_prefix_gain hq H hGRH hx hX hdiv
      hsmall
  have he : Finset.Icc 1 ⌊lambda * x⌋₊ = Finset.Ioc 0 ⌊lambda * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he, ← Complex.re_sum,
    MellinKernel.principal_sum_eq_level_one_of_no_small_prime_divisor gaussianGammaMellinKernel
      (q := q) x hdiv,
    Complex.re_sum] at hhi
  nlinarith only [hm, hhi]

/-- The Gaussian comparison inequality with the signed 50000-prefix error. -/
theorem gaussian_noSmallPrimes_explicit_inequality_prefix_gain_signed {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x lambda : ℝ} (hx : 4 ≤ x)
    (hX : 50000 ≤ lambda * x) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊lambda * x⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    ((H.index : ℝ) *
            (∫ u in (0 : ℝ)..lambda, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * subgroupConductorLogSum H + 14 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
        ((H.index - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefixSigned q x := by
  have hl : 0 ≤ lambda := by
    have hxpos : 0 < x := by linarith only [hx]
    by_contra hn
    have hlneg : lambda < 0 := lt_of_not_ge hn
    have hprod : lambda * x < 0 := mul_neg_of_neg_of_pos hlneg hxpos
    linarith only [hX, hprod]
  have hlo :=
    gaussian_level_one_sum_lower_fourteen hGRH.riemann
      ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hl
  have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg H.index)
  have hhi :=
    gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes_prefix_gain_signed hq H hGRH hx hX
      hdiv hsmall
  have he : Finset.Icc 1 ⌊lambda * x⌋₊ = Finset.Ioc 0 ⌊lambda * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he, ← Complex.re_sum,
    MellinKernel.principal_sum_eq_level_one_of_no_small_prime_divisor gaussianGammaMellinKernel
      (q := q) x hdiv,
    Complex.re_sum] at hhi
  nlinarith only [hm, hhi]

/-- If eligible primes below X lie in H, prime divisors exceed floor(X), and
X reaches 1000, the Gaussian comparison uses the reduced 1000-prefix error. -/
theorem gaussian_noSmallPrimes_explicit_inequality_prefix1000_gain {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x lambda : ℝ} (hx : 4 ≤ x)
    (hX : 1000 ≤ lambda * x) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊lambda * x⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    ((H.index : ℝ) *
            (∫ u in (0 : ℝ)..lambda, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * subgroupConductorLogSum H + 14 * ((H.index : ℝ) + 1) * x ^ (1 / 4 : ℝ) +
        ((H.index - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefix1000 q x := by
  have hl : 0 ≤ lambda := by
    have hxpos : 0 < x := by linarith only [hx]
    by_contra hn
    have hlneg : lambda < 0 := lt_of_not_ge hn
    have hprod : lambda * x < 0 := mul_neg_of_neg_of_pos hlneg hxpos
    linarith only [hX, hprod]
  have hlo :=
    gaussian_level_one_sum_lower_fourteen hGRH.riemann
      ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hl
  have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg H.index)
  have hhi :=
    gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes_prefix1000_gain hq H hGRH hx hX hdiv
      hsmall
  have he : Finset.Icc 1 ⌊lambda * x⌋₊ = Finset.Ioc 0 ⌊lambda * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he, ← Complex.re_sum,
    MellinKernel.principal_sum_eq_level_one_of_no_small_prime_divisor gaussianGammaMellinKernel
      (q := q) x hdiv,
    Complex.re_sum] at hhi
  nlinarith only [hm, hhi]

end PseudoPrime.LLS.PaperStatements
