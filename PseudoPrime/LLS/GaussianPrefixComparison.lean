/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RelativeGaussianSubgroupComparison
public import PseudoPrime.LLS.GammaCheckpoint35000

/-! # Signed Gaussian prefix comparison with arbitrary certified cutoff mass -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH, every Gaussian prefix with cutoff at least 35000 has mass at least 47/10.
Scale the certified Gamma prefix by 17/20 and sum the pointwise weight inequality.
This supplies the shorter prefix used by the log240 MR budget. -/
theorem gaussian_prefix35000_lower {b : ℝ} (hRH : RiemannHypothesis) (hb : 35000 ≤ b) :
    (47 / 10 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have hg := gamma_prefix35000_lower hRH hb
  have hs := Finset.sum_le_sum (s := Finset.Ioc 0 ⌊b⌋₊)
    (fun n _ ↦ gaussian_gamma_mangoldt_weight_le n)
  rw [← Finset.mul_sum] at hs
  have h := mul_le_mul_of_nonneg_left hg (by norm_num only : (0 : ℝ) ≤ 17 / 20)
  linarith only [h, hs]

end PseudoPrime.LLS

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

variable {N : ℕ} {P : ℝ}

/-- Given a certified Gaussian prefix mass and triviality on its prime bases,
transfer the signed prefix gain through this comparison, retaining the exact conductor coefficient.
The result is used by the next stage of the constant-principal MR comparison. -/
theorem gaussian_zeroMass_prefix_lt

    (hprefix : P ≤ ∑ n ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight n)
    {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hRiemann : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ N → χ p = 1) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) +
        Analysis.gaussianPairedEulerTail χ (Finset.Ioc 0 (N : ℕ)) <
      (20115621 / 50000000 : ℝ) * Real.log q + (12871 / 1000 - 2 * P) := by
  let B := Finset.Ioc 0 (N : ℕ)
  have h := gaussian_zeroMass_add_pairedTail_lt_principal_prefix hq hRH hRiemann hp hne hinv B
  have htrivB : ∑ m ∈ B, (1 - (χ m).re) * Analysis.gaussianResolventMangoldtWeight m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    by_cases hΛ : ArithmeticFunction.vonMangoldt m = 0
    · simp only [Analysis.gaussianResolventMangoldtWeight, hΛ, zero_mul, mul_zero]
    · obtain ⟨p, r, hp, hr, rfl⟩ :=
        (isPrimePow_nat_iff (n := m)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
      have hpbound : (p : ℝ) ≤ N := by
        calc
          (p : ℝ) ≤ (p ^ r : ℕ) := by exact_mod_cast Nat.le_pow hr
          _ ≤ N := by exact_mod_cast (Finset.mem_Ioc.mp hm).2
      simp only [Analysis.gaussianResolventMangoldtWeight, Nat.cast_pow, map_pow,
        hsmall p hp hpbound, one_pow, Complex.one_re, sub_self, zero_mul]
  dsimp only [B] at h
  rw [htrivB, add_zero] at h
  linarith only [h, hprefix]

/-- Under primitive nonprincipal GRH, the kernel zero-term norm is its nonnegative
completed multiplicity times the Gaussian norm on the critical line. The divisor-zero split
handles all complex inputs and connects zero-mass bounds to oscillating kernel sums. -/
private theorem gaussian_kernel_zero_norm {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ρ : ℂ) :
    ‖LLS.PaperStatements.gaussianGammaMellinKernel.kernelZeroTerm χ ρ‖ =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖ := by
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  by_cases hD : D = 0
  · change
      ‖(D : ℂ) * Analysis.gaussianGammaFunction (Complex.I * ρ.im)‖ =
        (D : ℝ) * ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖
    rw [hD]
    norm_num only [Int.cast_zero, zero_mul, norm_zero]
  · have hz :=
      dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero
        hne hD
    have hr :=
      completedLFunction_zero_re_eq_half hGRH hp hne hinv hz
    have he : Complex.I * (ρ.im : ℂ) + 1 / 2 = ρ := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.div_ofNat_re, Complex.one_re,
          zero_add]
        exact hr.symm
      · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, one_mul, zero_mul, zero_add, Complex.div_ofNat_im, Complex.one_im,
          zero_div, add_zero]
    have hDn : (0 : ℝ) ≤ D := by
      have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
        (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
    change ‖(D : ℂ) * Analysis.gaussianGammaFunction (Complex.I * ρ.im)‖ = _
    have he' : Complex.I * (ρ.im : ℂ) = ρ - 1 / 2 := by
      calc
        _ = (Complex.I * (ρ.im : ℂ) + 1 / 2) - 1 / 2 := by ring
        _ = _ := by rw [he]
    rw [he', norm_mul, Complex.norm_intCast, abs_of_nonneg hDn]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

namespace PseudoPrime.LLS.PaperStatements

variable {N : ℕ} {P : ℝ}

/-- The signed ambient error for certified prefix mass P at level q and scale x.
The conductor coefficient stays separate. Specializing P recovers the fixed-prefix budgets.
This definition supplies the generic constant-principal and relative comparison APIs. -/
noncomputable def gaussianPrefixError (P : ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  12871 / 1000 - 2 * P +
        (512 / 27 : ℝ) / x +
    (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
    (473 / 10 : ℝ) * x ^ (-9 / 16 : ℝ)

/-- Given a certified Gaussian prefix mass and triviality on its prime bases,
transfer the signed prefix gain through this comparison, retaining the exact conductor coefficient.
The result is used by the next stage of the constant-principal MR comparison. -/
theorem norm_gaussian_zeroSum_prefix_lt

    (hprefix : P ≤ ∑ n ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight n)
    {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ N → χ p = 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ‖ <
      (20115621 / 50000000 : ℝ) * Real.log m + (12871 / 1000 - 2 * P) := by
  have hs :=
    MellinKernel.summable_oscillatingZeroTerm gaussianGammaMellinKernel hm hGRH hp hne hinv hx
  have hn := norm_tsum_le_tsum_norm hs.norm
  have he (ρ : ℂ) :=
    (MellinKernel.norm_oscillatingZeroTerm gaussianGammaMellinKernel χ hx ρ).trans
      (AnalyticNumberTheory.DirichletLFunction.gaussian_kernel_zero_norm hGRH hp hne hinv ρ)
  rw [tsum_congr he] at hn
  let B := Finset.Ioc 0 (N : ℕ)
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.gaussian_zeroMass_prefix_lt hprefix hm
      (hGRH m χ hp) hGRH.riemann hp hne hinv hsmall
  have ht := Analysis.gaussianPairedEulerTail_nonneg χ B
  dsimp only [B] at hz ht
  have hzero :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) <
      (20115621 / 50000000 : ℝ) * Real.log m + (12871 / 1000 - 2 * P) := by
    linarith only [hz, ht]
  exact hn.trans_lt hzero

/-- Given a certified Gaussian prefix mass and triviality on its prime bases,
transfer the signed prefix gain through this comparison, retaining the exact conductor coefficient.
The result is used by the next stage of the constant-principal MR comparison. -/
theorem gaussian_primitive_sum_prefix_le

    (hprefix : P ≤ ∑ n ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight n)
    {q m : ℕ} [NeZero m]
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ N → χ p = 1) {x : ℝ}
    (hx : 1 ≤ x) :
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n).re ≤
      (20115621 / 50000000 : ℝ) * Real.log m + (12871 / 1000 - 2 * P) +
        (512 / 27 : ℝ) / x +
        (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (473 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
  let S := ∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hz :=
    norm_gaussian_zeroSum_prefix_lt hprefix (by linarith only [hm]) hGRH hp hne hinv hsmall
      hxpos
  have hr := re_gaussian_primitive_remainder_le_variable_scale hq hm hmq hp hne hinv hGRH hx
  have hnegZ : -Z.re ≤ ‖Z‖ := by
    have h := Complex.re_le_norm (-Z)
    simpa only [Complex.neg_re, norm_neg] using h
  have hZ : -Z.re ≤ (20115621 / 50000000 : ℝ) * Real.log m + (12871 / 1000 - 2 * P) := by
    have hlogm : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast ((by decide : 1 ≤ 3).trans hm))
    linarith only [hnegZ, hz.le, hlogm]
  have hlogm : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ((by decide : 1 ≤ 3).trans hm))
  have hidentity : S.re = (S + Z).re - Z.re := by
    rw [Complex.add_re]
    ring
  rw [hidentity]
  change (S + Z).re - Z.re ≤ _
  linarith only [hr, hZ, hlogm]

/-- Given a certified Gaussian prefix mass and triviality on its prime bases,
transfer the signed prefix gain through this comparison, retaining the exact conductor coefficient.
The result is used by the next stage of the constant-principal MR comparison. -/
theorem gaussian_source_sum_prefix_le

    (hprefix : P ≤ ∑ n ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight n)
    {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ N → χ.primitiveCharacter p = 1) {x : ℝ}
    (hx : 1 ≤ x) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (20115621 / 50000000 : ℝ) * Real.log χ.conductor + (12871 / 1000 - 2 * P) +
        (512 / 27 : ℝ) / x +
        (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (473 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    gaussian_primitive_sum_prefix_le hprefix hq hm hmq hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hnp (inv_ne_one.mpr hnp) hsmall hx

/-- Given a certified Gaussian prefix mass and triviality on its prime bases,
transfer the signed prefix gain through this comparison, retaining the exact conductor coefficient.
The result is used by the next stage of the constant-principal MR comparison. -/
theorem gaussian_average_prefix_le

    (hprefix : P ≤ ∑ n ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight n)
    {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] [DecidableEq S]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hsmall : ∀ χ : S, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ N → χ.val.primitiveCharacter p = 1) {x : ℝ}
    (hx : 4 ≤ x) :
    (∑ χ : S, ∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 +
        (20115621 / 50000000 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Fintype.card S - 1 : ℕ) : ℝ) * gaussianPrefixError P q x := by
  classical
  let F := fun χ : S ↦ (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.val.primitiveCharacter x n).re
  have h1 : F 1 ≤ Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 := by
    simpa only [F, Subgroup.coe_one] using
      gaussian_primitive_principal_sum_upper_constant hGRH.riemann
        ((by norm_num only : (0 : ℝ) < 4).trans_le hx)
  have hrest :
    ∑ χ ∈ Finset.univ.erase (1 : S), F χ ≤
      (20115621 / 50000000 : ℝ) * (∑ χ ∈ Finset.univ.erase (1 : S), Real.log χ.val.conductor) +
        ((Finset.univ.erase (1 : S)).card : ℝ) * gaussianPrefixError P q x := by
    calc
      _ ≤
          ∑ χ ∈ Finset.univ.erase (1 : S),
            ((20115621 / 50000000 : ℝ) * Real.log χ.val.conductor + gaussianPrefixError P q x) :=
        by
        apply Finset.sum_le_sum
        intro χ hχ
        have hn : χ.val ≠ 1 := fun he ↦ (Finset.mem_erase.mp hχ).1 (Subtype.ext he)
        have h :=
          gaussian_source_sum_prefix_le hprefix hq χ.val hn hGRH
            (hsmall χ) (by linarith only [hx])
        simpa only [F, gaussianPrefixError, add_assoc] using h
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

/-- Given a certified Gaussian prefix mass and triviality on its prime bases,
transfer the signed prefix gain through this comparison, retaining the exact conductor coefficient.
The result is used by the next stage of the constant-principal MR comparison. -/
theorem gaussian_principal_prefix_le

    (hprefix : P ≤ ∑ n ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight n)
    {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x X : ℝ} (hx : 4 ≤ x) (hX : N ≤ X) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊X⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    (H.index : ℝ) *
        ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ q) x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 +
        (20115621 / 50000000 : ℝ) * subgroupConductorLogSum H +
        ((H.index - 1 : ℕ) : ℝ) * gaussianPrefixError P q x := by
  classical
  have hsmallChars :
    ∀ χ : NumberTheory.subgroupAnnihilator H,
      ∀ p : ℕ, p.Prime → (p : ℝ) ≤ N → χ.val.primitiveCharacter p = 1 := by
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
    gaussian_average_prefix_le hprefix hq
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

/-- Given a certified Gaussian prefix mass and triviality on its prime bases,
transfer the signed prefix gain through this comparison, retaining the exact conductor coefficient.
The result is used by the next stage of the constant-principal MR comparison. -/
theorem gaussian_relative_prefix_le

    (hprefix : P ≤ ∑ n ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight n)
    {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h x lambda : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1 / 2) (hx : 4 ≤ x) (hl : 0 ≤ lambda) (hX : N ≤ lambda * x)
    (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊lambda * x⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    ((H.index : ℝ) * (1 - h) *
            (∫ u in (0 : ℝ)..lambda, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (20115621 / 50000000 : ℝ) * subgroupConductorLogSum H +
        (H.index : ℝ) *
          (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
        13 +
        ((H.index - 1 : ℕ) : ℝ) * gaussianPrefixError P q x := by
  have hlo :=
    gaussian_level_one_sum_lower_relative hGRH.riemann hh hh1
      ((by norm_num only : (0 : ℝ) < 4).trans_le hx) hl
  have hm := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg H.index)
  have hhi := gaussian_principal_prefix_le hprefix hq H hGRH hx hX hdiv hsmall
  have he : Finset.Icc 1 ⌊lambda * x⌋₊ = Finset.Ioc 0 ⌊lambda * x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Nat.succ_le_iff]
  rw [he, ← Complex.re_sum,
    MellinKernel.principal_sum_eq_level_one_of_no_small_prime_divisor gaussianGammaMellinKernel
      (q := q) x hdiv,
    Complex.re_sum] at hhi
  nlinarith only [hm, hhi]

/-- A certified prefix also gives the legacy conductor coefficient 161/400.
Relax only the exact coefficient using the nonnegative conductor-log sum. This wrapper
connects the shorter prefix to the existing MR scalar normalization. -/
theorem gaussian_relative_prefix_le_coarse

    (hprefix : P ≤ ∑ n ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight n)
    {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h x lambda : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1 / 2) (hx : 4 ≤ x) (hl : 0 ≤ lambda) (hX : N ≤ lambda * x)
    (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊lambda * x⌋₊ < p)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ lambda * x → residueInSubgroup q H p) :
    ((H.index : ℝ) * (1 - h) *
            (∫ u in (0 : ℝ)..lambda, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        Real.sqrt x ≤
      (161 / 400 : ℝ) * subgroupConductorLogSum H +
        (H.index : ℝ) *
          (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
        13 +
        ((H.index - 1 : ℕ) : ℝ) * gaussianPrefixError P q x := by
  have h := gaussian_relative_prefix_le hprefix hq H hGRH hh hh1 hx hl hX hdiv hsmall
  have hc := subgroupConductorLogSum_nonneg H
  nlinarith only [h, hc]


/-- The existing signed 50000-prefix ambient error is exactly the generic error at its
certified mass 484381/100000. Expand the two expressions and normalize rational constants.
This makes the legacy fixed-prefix API an explicit specialization of the new budget. -/
theorem gaussianPrefixError_legacy (q : ℕ) (x : ℝ) :
    gaussianPrefixError (484381 / 100000) q x = gaussianAmbientErrorPrefixSigned q x := by
  dsimp only [gaussianPrefixError, gaussianAmbientErrorPrefixSigned]
  ring

end PseudoPrime.LLS.PaperStatements
