/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.GeneralScaleDensity

/-! # Unconditional log-free zero density for primitive Dirichlet families -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-- For a primitive nonprincipal completed function and a point to the right of one,
a rectangle contained in a disk of radius `r` has multiplicity count at most `r^2`
times the global inverse-square genus mass at that point. Compare each multiplicity
with its kernel contribution and use the nonnegative summable genus expansion.
This supplies coarse counting without any Riemann-hypothesis assumption. -/
theorem completedZeroMultiplicityCountInRectangle_le_inverse_square_mass {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    (z w s : ℂ) (hs : 1 < s.re) (r : ℝ)
    (hbox : ∀ ρ ∈ completedZerosInRectangle χ hχ z w, ‖s - ρ‖ ≤ r) :
    completedZeroMultiplicityCountInRectangle χ hχ z w ≤
      r ^ 2 *
        ∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 := by
  let F := χ.completedLFunction
  let D := MeromorphicOn.divisor F Set.univ
  let S := completedZerosInRectangle χ hχ z w
  let f := fun ρ : ℂ ↦ (D ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2
  have hF : AnalyticOnNhd ℂ F Set.univ := fun u _ ↦
    (χ.differentiable_completedLFunction hχ).analyticAt u
  have hDnonneg (ρ : ℂ) : 0 ≤ (D ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF ρ
  have hfnonneg (ρ : ℂ) : 0 ≤ f ρ := mul_nonneg (hDnonneg ρ) (sq_nonneg _)
  have hsum : Summable f := summable_completed_genus_inverse_square hq hχ hp hinv hs
  have hpoint (ρ : ℂ) (hρ : ρ ∈ S) : (analyticOrderNatAt F ρ : ℝ) ≤ r ^ 2 * f ρ := by
    have hzero := (mem_completedZerosInRectangle_iff.mp hρ).2
    have hsne : s - ρ ≠ 0 := by
      intro heq
      have hsρ := sub_eq_zero.mp heq
      have hsnonzero := DirichletLFunction.completedLFunction_ne_zero_of_one_le_re hχ hs.le
      exact hsnonzero (hsρ ▸ hzero)
    have hnorm : 0 < ‖s - ρ‖ := norm_pos_iff.mpr hsne
    have hnormle := hbox ρ hρ
    have hsquare : ‖s - ρ‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnormle 2
    have hcancel : ‖s - ρ‖ ^ 2 * ‖(s - ρ)⁻¹‖ ^ 2 = 1 := by
      rw [norm_inv, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hnorm.ne')]
    have hweight := mul_le_mul_of_nonneg_right hsquare (sq_nonneg ‖(s - ρ)⁻¹‖)
    rw [hcancel] at hweight
    have horder : D ρ = (analyticOrderNatAt F ρ : ℤ) := by
      rw [show D = MeromorphicOn.divisor F Set.univ from rfl,
        MeromorphicOn.AnalyticOnNhd.divisor_apply hF (Set.mem_univ ρ)]
      change
        ((analyticOrderAt F ρ).map (fun k : ℕ ↦ (k : ℤ))).untop₀ = ((analyticOrderAt F ρ).toNat : ℤ)
      induction analyticOrderAt F ρ using ENat.recTopCoe <;> rfl
    have hd : (D ρ : ℝ) = (analyticOrderNatAt F ρ : ℝ) := by
      rw [horder]
      push_cast
      rfl
    have h := mul_le_mul_of_nonneg_left hweight (hDnonneg ρ)
    dsimp only [f]
    rw [← hd]
    nlinarith only [h]
  calc
    _ = ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ) := rfl
    _ ≤ ∑ ρ ∈ S, r ^ 2 * f ρ := Finset.sum_le_sum hpoint
    _ = r ^ 2 * ∑ ρ ∈ S, f ρ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsum.sum_le_tsum S (fun ρ _ ↦ hfnonneg ρ)) (sq_nonneg r)

/-- One positive absolute constant bounds each primitive completed zero count in the
closed critical half-strip by `(T+3)^2(C+2 log q)`. Compare the rectangle with the
inverse-square genus mass centered at `3/2`, then use the uniform mass bound.
This provides a fixed polynomial estimate outside the small-shift detector range. -/
theorem exists_uniform_completedZeroCount_coarse_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
          2 ≤ q →
            ∀ hχ : χ ≠ 1,
              χ.IsPrimitive →
                χ⁻¹ ≠ 1 →
                ∀ σ T : ℝ,
                  (1 / 2 : ℝ) ≤ σ →
                    σ ≤ 1 →
                    0 ≤ T →
                    DirichletLFunction.completedZeroCount χ hχ σ T ≤
                      (T + 3) ^ 2 * (C + 2 * Real.log q) := by
  let C :=
    24 + 2 * (completedGenusMassShiftConstant + completedGenusMassCenterConstant) * (Real.log 4 + 1)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num only)
  have hC : 0 < C := by
    have h :=
      mul_pos (add_pos completedGenusMassShiftConstant_pos completedGenusMassCenterConstant_pos)
        (by linarith only [hlog4] : 0 < Real.log 4 + 1)
    dsimp only [C]
    linarith only [h]
  refine ⟨C, hC, ?_⟩
  intro q hq χ hqtwo hχ hp hinv σ T hσhalf hσ hT
  let s : ℂ := (3 / 2 : ℝ)
  have hs : 1 < s.re := by norm_num only [s, Complex.ofReal_re]
  obtain ⟨A, B, hAeq, hBeq, _, _, hmass⟩ :=
    exists_completed_genus_inverse_square_mass_le_uniform_bound hqtwo hχ hp hinv (η := 1 / 2)
      (by norm_num only) (by norm_num only) 0
  have hmass' :
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2) ≤
      C + 2 * Real.log q := by
    subst A
    subst B
    norm_num only [abs_zero, add_zero, Complex.ofReal_zero, mul_zero, add_zero,
      show (1 + (1 / 2 : ℝ)) = 3 / 2 by norm_num only] at hmass
    dsimp only [s, C]
    linarith only [hmass]
  have hbox (ρ : ℂ)
    (hρ : ρ ∈ completedZerosInRectangle χ hχ ((σ : ℂ) - T * Complex.I) ((1 : ℂ) + T * Complex.I)) :
    ‖s - ρ‖ ≤ T + 3 := by
    obtain ⟨hρlow, hρhigh, himlow, himhigh, _⟩ :=
      (DirichletLFunction.mem_completedZeroCountRegion_iff hσ hT).mp hρ
    have hre : 0 ≤ 3 / 2 - ρ.re := by linarith only [hρhigh]
    have him : |ρ.im| ≤ T := abs_le.mpr ⟨himlow, himhigh⟩
    have hnorm := Complex.norm_le_abs_re_add_abs_im (s - ρ)
    simp only [s, Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub,
      abs_neg, abs_of_nonneg hre] at hnorm
    linarith only [hnorm, him, hρlow, hσhalf]
  exact
    (completedZeroMultiplicityCountInRectangle_le_inverse_square_mass hqtwo hχ hp hinv _ _ s hs
          (T + 3) hbox).trans
      (mul_le_mul_of_nonneg_left hmass' (sq_nonneg _))

/-- One positive absolute constant bounds the actual primitive-family zero count by
the fifth power of every positive natural cutoff, uniformly in the closed critical
half-strip. Sum the per-character inverse-square estimate, bound the number of
characters by the modulus, and absorb the remaining logarithm into the cutoff.
This supplies the coarse branch of the full log-free density estimate. -/
theorem exists_primitiveCharacterFamily_coarse_count_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (R : ℕ) (σ : ℝ),
          1 ≤ R →
            (1 / 2 : ℝ) ≤ σ → σ ≤ 1 → primitiveCharacterFamilyZeroCount R σ ≤ C * (R : ℝ) ^ 5 := by
  classical
  obtain ⟨C, hC, hchar⟩ := exists_uniform_completedZeroCount_coarse_bound
  refine ⟨16 * (C + 2), by linarith only [hC], ?_⟩
  intro R σ hR hσhalf hσ
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < R := zero_lt_one.trans_le hRreal
  have hlogR : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg hRreal
  let H := ((R : ℝ) + 3) ^ 2 * (C + 2 * Real.log R)
  have hH : 0 ≤ H := mul_nonneg (sq_nonneg _) (by linarith only [hC, hlogR])
  have hper (q : Fin R) :
    (∑ χ : DirichletCharacter ℂ (q.val + 1),
        if hχ : χ ≠ 1 then
          if _hp : χ.IsPrimitive then DirichletLFunction.completedZeroCount χ hχ σ (R : ℝ) else 0
        else 0) ≤
      (R : ℝ) * H := by
    have hq : NeZero (q.val + 1) := ⟨Nat.succ_ne_zero _⟩
    have hqR : (q.val + 1 : ℕ) ≤ R := Nat.succ_le_of_lt q.isLt
    have hqRreal : ((q.val + 1 : ℕ) : ℝ) ≤ R := Nat.cast_le.mpr hqR
    have hcard : Fintype.card (DirichletCharacter ℂ (q.val + 1)) ≤ R := by
      rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
      exact (Nat.totient_le _).trans hqR
    calc
      _ ≤ ∑ _χ : DirichletCharacter ℂ (q.val + 1), H := by
        apply Finset.sum_le_sum
        intro χ hχmem
        by_cases hχ : χ ≠ 1
        · by_cases hp : χ.IsPrimitive
          · simp only [dite_eq_left hχ, dite_eq_left hp]
            have hbound :=
              hchar (two_le_succ_modulus_of_nonprincipal q.val χ hχ) hχ hp
                (fun h ↦ hχ (inv_eq_one.mp h)) σ R hσhalf hσ (Nat.cast_nonneg R)
            have hlogq := Real.log_le_log (Nat.cast_pos.mpr (Nat.succ_pos q.val)) hqRreal
            exact hbound.trans (mul_le_mul_of_nonneg_left (by linarith only [hlogq]) (sq_nonneg _))
          · simp only [dite_eq_left hχ, dite_eq_right hp]
            exact hH
        · simp only [dite_eq_right hχ]
          exact hH
      _ = (Fintype.card (DirichletCharacter ℂ (q.val + 1)) : ℝ) * H := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hH
  have hfamily : primitiveCharacterFamilyZeroCount R σ ≤ (R : ℝ) ^ 2 * H := by
    calc
      _ ≤ ∑ _q : Fin R, (R : ℝ) * H := Finset.sum_le_sum (fun q _ ↦ hper q)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hsize : ((R : ℝ) + 3) ^ 2 ≤ 16 * (R : ℝ) ^ 2 := by nlinarith only [hRreal]
  have hlogsize : C + 2 * Real.log R ≤ (C + 2) * (R : ℝ) := by
    have hCR := le_mul_of_one_le_right hC.le hRreal
    linarith only [hCR, Real.log_le_self hRpos.le]
  have hHsize : H ≤ 16 * (R : ℝ) ^ 2 * ((C + 2) * R) :=
    mul_le_mul hsize hlogsize (by linarith only [hC, hlogR])
      (mul_nonneg (by norm_num only) (sq_nonneg _))
  calc
    _ ≤ (R : ℝ) ^ 2 * H := hfamily
    _ ≤ (R : ℝ) ^ 2 * (16 * (R : ℝ) ^ 2 * ((C + 2) * R)) :=
      mul_le_mul_of_nonneg_left hHsize (sq_nonneg _)
    _ = _ := by ring

/-- There are positive absolute constants `A,C` such that for every natural cutoff at
least two and every real threshold in the closed critical half-strip, the original
primitive-family zero count is at most `C T^(A(1-σ))`, retaining analytic multiplicities.
Use the general-scale near-one density estimate, absorb the coarse fifth-power
bound by a larger fixed exponent outside that strip, and cover bounded cutoffs by
one absolute constant. This is the unconditional full-range log-free density input
for theta supply; it assumes neither a density estimate nor GRH. -/
theorem exists_primitiveCharacterFamily_log_free_density :
    ∃ A C : ℝ,
      0 < A ∧
        0 < C ∧
        ∀ T : ℕ,
          2 ≤ T →
            ∀ σ : ℝ,
              (1 / 2 : ℝ) ≤ σ →
                σ ≤ 1 →
                primitiveCharacterFamilyZeroCount T σ ≤ C * Real.rpow (T : ℝ) (A * (1 - σ)) := by
  obtain ⟨C₁, A₁, η₀, hC₁, hA₁, hη₀, R₀, hR₀, hnear⟩ :=
    exists_primitiveCharacterFamily_near_one_log_free_density
  obtain ⟨C₂, hC₂, hcoarse⟩ := exists_primitiveCharacterFamily_coarse_count_bound
  let A := max A₁ (5 / η₀)
  let C := C₁ + C₂ * ((R₀ : ℝ) ^ 5 + 1)
  have hA : 0 < A := hA₁.trans_le (le_max_left _ _)
  have hR₀nonneg : (0 : ℝ) ≤ R₀ := Nat.cast_nonneg R₀
  have hR₀power : 0 ≤ (R₀ : ℝ) ^ 5 := pow_nonneg hR₀nonneg _
  have hC : 0 < C := by
    have h := mul_pos hC₂ (by linarith only [hR₀power] : 0 < (R₀ : ℝ) ^ 5 + 1)
    dsimp only [C]
    linarith only [h, hC₁]
  have hC₁C : C₁ ≤ C := by
    have h := mul_nonneg hC₂.le (add_nonneg hR₀power zero_le_one)
    dsimp only [C]
    linarith only [h]
  have hC₂C : C₂ ≤ C := by
    have h := mul_nonneg hC₂.le hR₀power
    dsimp only [C]
    linarith only [hC₁, h]
  refine ⟨A, C, hA, hC, ?_⟩
  intro T hT σ hσhalf hσ
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast ((by norm_num only : 1 ≤ 2).trans hT)
  have hδ : 0 ≤ 1 - σ := sub_nonneg.mpr hσ
  have hrpow : 1 ≤ Real.rpow (T : ℝ) (A * (1 - σ)) := by
    rw [Real.rpow_eq_pow]
    exact Real.one_le_rpow hTreal (mul_nonneg hA.le hδ)
  by_cases hlarge : R₀ ≤ T
  · by_cases hstrip : 1 - η₀ ≤ σ
    · have h := hnear T σ hlarge hstrip hσ
      have hexp := mul_le_mul_of_nonneg_right (le_max_left A₁ (5 / η₀)) hδ
      have hpow : Real.rpow (T : ℝ) (A₁ * (1 - σ)) ≤ Real.rpow (T : ℝ) (A * (1 - σ)) := by
        simp only [Real.rpow_eq_pow]
        exact Real.rpow_le_rpow_of_exponent_le hTreal hexp
      exact
        h.trans
          ((mul_le_mul_of_nonneg_left hpow hC₁.le).trans
            (mul_le_mul_of_nonneg_right hC₁C (zero_le_one.trans hrpow)))
    · have hδlower : η₀ ≤ 1 - σ := by linarith only [lt_of_not_ge hstrip]
      have hAη : 5 ≤ A * η₀ := (div_le_iff₀ hη₀).mp (le_max_right A₁ (5 / η₀))
      have hexp : (5 : ℝ) ≤ A * (1 - σ) := hAη.trans (mul_le_mul_of_nonneg_left hδlower hA.le)
      have hpow : (T : ℝ) ^ 5 ≤ Real.rpow (T : ℝ) (A * (1 - σ)) := by
        rw [Real.rpow_eq_pow]
        have h := Real.rpow_le_rpow_of_exponent_le hTreal hexp
        simpa only [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num only, Real.rpow_natCast] using h
      exact
        (hcoarse T σ ((by norm_num only : 1 ≤ 2).trans hT) hσhalf hσ).trans
          ((mul_le_mul_of_nonneg_left hpow hC₂.le).trans
            (mul_le_mul_of_nonneg_right hC₂C (zero_le_one.trans hrpow)))
  · have hTupper : (T : ℝ) ≤ R₀ := Nat.cast_le.mpr (Nat.le_of_lt (Nat.lt_of_not_ge hlarge))
    have hpower := pow_le_pow_left₀ (Nat.cast_nonneg T : (0 : ℝ) ≤ T) hTupper 5
    have hbound : C₂ * (R₀ : ℝ) ^ 5 ≤ C := by
      dsimp only [C]
      nlinarith only [hC₁, hC₂]
    exact
      (hcoarse T σ ((by norm_num only : 1 ≤ 2).trans hT) hσhalf hσ).trans
        ((mul_le_mul_of_nonneg_left hpower hC₂.le).trans
          (hbound.trans (le_mul_of_one_le_right hC.le hrpow)))

/-- Absolute positive density constants also bound every separated-conductor
endpoint count, each finite inverse-height dyadic sum, and the infinite inverse-height
dyadic sum when the density exponent is at most one half. Instantiate the existing
partial-summation interfaces with the proved unconditional family density theorem.
No density hypothesis remains as an argument. This supplies the zero-height sums
needed by the next theta-supply stage while retaining the conductor factor. -/
theorem exists_primitiveCharacterFamily_log_free_density_height_sum_bounds :
    ∃ A C : ℝ,
      0 < A ∧
        0 < C ∧
        ∀ (Q : ℕ) (σ : ℝ),
          (1 / 2 : ℝ) ≤ σ →
            σ ≤ 1 →
            A * (1 - σ) ≤ 1 / 2 →
            (∀ n : ℕ,
                2 ≤ n →
                  primitiveCharacterFamilyZeroCountAtNatHeight Q σ n ≤
                    (C * Real.rpow ((Q + 1 : ℕ) : ℝ) (A * (1 - σ))) *
                      Real.rpow (n : ℝ) (A * (1 - σ))) ∧
              (∀ J : ℕ,
                (∑ j ∈ Finset.range J,
                    (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) -
                        primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ j)) *
                      (1 / 2 : ℝ) ^ j) ≤
                  2 * (C * Real.rpow ((Q + 1 : ℕ) : ℝ) (A * (1 - σ))) * J) ∧
              (∑' j : ℕ,
                  (primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ (j + 1)) -
                      primitiveCharacterFamilyZeroCountAtNatHeight Q σ (2 ^ j)) *
                    (1 / 2 : ℝ) ^ j) ≤
                8 * (C * Real.rpow ((Q + 1 : ℕ) : ℝ) (A * (1 - σ))) := by
  obtain ⟨A, C, hA, hC, hdensity⟩ := exists_primitiveCharacterFamily_log_free_density
  refine ⟨A, C, hA, hC, ?_⟩
  intro Q σ hσhalf hσ hδhalf
  have hδ : 0 ≤ A * (1 - σ) := mul_nonneg hA.le (sub_nonneg.mpr hσ)
  have hdiag :
    ∀ T : ℕ, 2 ≤ T → primitiveCharacterFamilyZeroCount T σ ≤ C * Real.rpow (T : ℝ) (A * (1 - σ)) :=
    fun T hT ↦ hdensity T hT σ hσhalf hσ
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    exact
      primitiveCharacterFamilyZeroCountAtNatHeight_le_rpow_of_diagonal_rpow_density Q n σ C
        (A * (1 - σ)) hσ hC.le hδ hn hdiag
  · intro J
    exact
      primitiveCharacterFamilyZeroCountAtNatHeight_dyadic_sum_le_two_mul_of_diagonal_density Q J σ C
        (A * (1 - σ)) hσ hC.le hδ (hδhalf.trans (by norm_num only)) hdiag
  · exact
      primitiveCharacterFamilyZeroCountAtNatHeight_tsum_le_eight_of_diagonal_density Q σ C
        (A * (1 - σ)) hσ hC.le hδ hδhalf hdiag

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
