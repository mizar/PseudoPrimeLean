/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianSubgroupComparison
public import PseudoPrime.LLS.GaussianPrincipalConstantBounds

/-! # Gaussian subgroup comparison with constant principal upper error -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH at q≥20000 and x≥4, a finite character subgroup primitive
Gaussian average is bounded by the principal main term with constant error thirteen,
the exact nonprincipal conductor-log sum, and a per-character ambient error.
Use the actual variable-scale arithmetic bounds and retain their leading conductors. -/
theorem gaussian_primitive_average_re_le_constant_principal {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] [DecidableEq S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 4 ≤ x) :
    (∑ χ : S, ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 +
        (161 / 400 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Fintype.card S - 1 : ℕ) : ℝ) * (gaussianAmbientError q x) := by
  classical
  let F := fun χ : S ↦ (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re
  have h1 : F 1 ≤ Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 := by
    simpa only [F, Subgroup.coe_one] using
      gaussian_primitive_principal_sum_upper_constant hGRH.riemann
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

/-- Under the prime-one condition through 50000, the constant-principal
Gaussian average uses the transferred prefix error for every nonprincipal term. -/
theorem gaussian_primitive_average_re_le_constant_principal_prefix_gain {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] [DecidableEq S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hsmall : ∀ χ : S, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 50000 → χ.val.primitiveCharacter p = 1) {x : ℝ}
    (hx : 4 ≤ x) :
    (∑ χ : S, ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 +
        (161 / 400 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Fintype.card S - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefix q x := by
  classical
  let F := fun χ : S ↦ (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re
  have h1 : F 1 ≤ Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 := by
    simpa only [F, Subgroup.coe_one] using
      gaussian_primitive_principal_sum_upper_constant hGRH.riemann
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
        change F χ ≤ _ at h
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

/-- Under the prime-one condition through 1000, the constant-principal
Gaussian average uses the transferred prefix error for every nonprincipal term. -/
theorem gaussian_primitive_average_re_le_constant_principal_prefix1000_gain {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] [DecidableEq S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hsmall : ∀ χ : S, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 1000 → χ.val.primitiveCharacter p = 1) {x : ℝ}
    (hx : 4 ≤ x) :
    (∑ χ : S, ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 +
        (161 / 400 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Fintype.card S - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefix1000 q x := by
  classical
  let F := fun χ : S ↦ (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re
  have h1 : F 1 ≤ Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 := by
    simpa only [F, Subgroup.coe_one] using
      gaussian_primitive_principal_sum_upper_constant hGRH.riemann
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
        change F χ ≤ _ at h
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
theorem gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes_constant_principal {q : ℕ}
    [NeZero q] (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 4 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 + (161 / 400 : ℝ) * subgroupConductorLogSum H +
        ((H.index - 1 : ℕ) : ℝ) * (gaussianAmbientError q x) := by
  classical
  have hu :=
    gaussian_primitive_average_re_le_constant_principal hq (NumberTheory.subgroupAnnihilator H) hGRH
      hx
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

/-- Transfer the 50000 Gaussian prefix gain through the constant-principal
annihilator average. The retained prefix consists of units because every prime
divisor of q lies above the cutoff. -/
theorem gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes_constant_principal_prefix_gain
    {q : ℕ} [NeZero q] (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 4 ≤ x)
    (hX : 50000 ≤ X) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊X⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 + (161 / 400 : ℝ) * subgroupConductorLogSum H +
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
    gaussian_primitive_average_re_le_constant_principal_prefix_gain hq
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

/-- Average primitive Gaussian sums using the signed 50000-prefix bound and
the constant principal estimate. The nonprincipal ambient error is independent
of its conductor. -/
theorem gaussian_primitive_average_re_le_constant_principal_prefix_gain_signed {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] [DecidableEq S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hsmall : ∀ χ : S, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 50000 → χ.val.primitiveCharacter p = 1) {x : ℝ}
    (hx : 4 ≤ x) :
    (∑ χ : S, ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 +
        (161 / 400 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Fintype.card S - 1 : ℕ) : ℝ) * gaussianAmbientErrorPrefixSigned q x := by
  classical
  let F := fun χ : S ↦ (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re
  have h1 : F 1 ≤ Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 := by
    simpa only [F, Subgroup.coe_one] using
      gaussian_primitive_principal_sum_upper_constant hGRH.riemann
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

/-- Transfer the 1000 Gaussian prefix gain through the constant-principal
annihilator average when the cutoff reaches 1000. -/
theorem
  gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes_constant_principal_prefix1000_gain
    {q : ℕ} [NeZero q] (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 4 ≤ x)
    (hX : 1000 ≤ X) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊X⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 + (161 / 400 : ℝ) * subgroupConductorLogSum H +
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
    gaussian_primitive_average_re_le_constant_principal_prefix1000_gain hq
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
conductor cost, lower error fourteen, upper error thirteen, and secondary errors.
The principal finite sum equals level one, so no finite modulus loss remains. -/
theorem gaussian_noSmallPrimes_explicit_inequality_constant_principal {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x lambda : ℝ} (hx : 4 ≤ x)
    (hl : 0 ≤ lambda) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊lambda * x⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    ((H.index : ℝ) *
            (∫ u in (0 : ℝ)..lambda, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * subgroupConductorLogSum H + 14 * (H.index : ℝ) * x ^ (1 / 4 : ℝ) + 13 +
        ((H.index - 1 : ℕ) : ℝ) * (gaussianAmbientError q x) := by
  have hlo :=
    gaussian_level_one_sum_lower_fourteen hGRH.riemann
      ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hl
  have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg H.index)
  have hhi :=
    gaussian_principal_sum_le_conductor_bound_of_noSmallPrimes_constant_principal hq H hGRH hx
      hsmall
  have he : Finset.Icc 1 ⌊lambda * x⌋₊ = Finset.Ioc 0 ⌊lambda * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he, ← Complex.re_sum,
    MellinKernel.principal_sum_eq_level_one_of_no_small_prime_divisor gaussianGammaMellinKernel
      (q := q) x hdiv,
    Complex.re_sum] at hhi
  nlinarith only [hm, hhi]

/-- Transfer the signed 50000-prefix estimate through the constant-principal
annihilator average. -/
theorem gaussian_principal_sum_le_noSmall_prefix_signed {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 4 ≤ x) (hX : 50000 ≤ X) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊X⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 + (161 / 400 : ℝ) * subgroupConductorLogSum H +
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
    gaussian_primitive_average_re_le_constant_principal_prefix_gain_signed hq
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

end PseudoPrime.LLS.PaperStatements
