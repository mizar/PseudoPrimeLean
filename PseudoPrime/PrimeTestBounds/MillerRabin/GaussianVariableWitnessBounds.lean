/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRVariableRelativeNumerics
public import PseudoPrime.Analysis.GaussianMR6FifthsNumerics
public import PseudoPrime.LLS.RelativeGaussianSubgroupComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalWitnessBounds

/-! # Variable-width Gaussian MR witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a subgroup index at least `10^9`, the actual relative Gaussian
comparison contradicts the classified radius budget at every logarithmic scale
beginning at 600. The conductor sum uses its universal `(index - 1) log n`
bound; the exact index remains in the main and secondary terms. -/
theorem gaussian_star_relative_inequality_contradiction {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : Analysis.gaussianMRStarIndex ≤ (H.index : ℝ)) (hL : 600 ≤ Real.log n) :
    let L := Real.log n
    let r := Analysis.gaussianMRStarRadius L
    let s := Analysis.gaussianMRStarRoot L
    let h := 1 / (3 * s)
    let x := r ^ 2
    ¬(((H.index : ℝ) * (1 - h) *
              (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt x ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          (H.index : ℝ) *
            (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
          13 +
          ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientError n x) := by
  intro L r s h x hcmp
  have hK : (1 : ℝ) < (Analysis.gaussianMRStarIndex : ℝ) := by
    norm_num only [Analysis.gaussianMRStarIndex]
  have hidxR : Analysis.gaussianMRStarIndex ≤ (H.index : ℝ) := by exact hi
  have hidxNat : 1 ≤ H.index := by
    have hidxPos : (1 : ℝ) ≤ (H.index : ℝ) := by linarith only [hi, hK]
    exact_mod_cast hidxPos
  have hmpos : (0 : ℝ) < (H.index : ℝ) - 1 := by linarith only [hidxR, hK]
  have hcast : ((H.index - 1 : ℕ) : ℝ) = (H.index : ℝ) - 1 := by
    rw [Nat.cast_sub hidxNat, Nat.cast_one]
  rw [hcast] at hcmp
  let m : ℝ := H.index
  let t : ℝ := m - 1
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(21 / 10 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  have ht : 0 < t := by
    dsimp only [t, m]
    exact hmpos
  have hL' : 600 ≤ L := by
    dsimp only [L]
    exact hL
  have hrpos : 0 < r := by
    dsimp only [r]
    exact sq_pos_of_pos (Analysis.gaussianMRStarRoot_pos hL')
  have hspos : 0 < s := by
    dsimp only [s]
    exact Analysis.gaussianMRStarRoot_pos hL'
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, Analysis.gaussianMRStarRadius]
  have hrbound : 294 ≤ r := by
    have hrad := Analysis.gaussianMRStarRadius_lower hL'
    dsimp only [r]
    nlinarith only [hrad, hL']
  have hsbound : 17 ≤ s := by nlinarith only [hrootSq, hrbound, hspos]
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  rw [hsqrtx] at hcmp
  have hmainMass := LLS.PaperStatements.gaussianGamma_cutoff_gt_target
  have hendpoint := Analysis.gaussian_endpoint_exp_le
  have hImass : Analysis.gaussianMRStarMass ≤ I := by
    dsimp only [I, Analysis.gaussianMRStarMass]
    exact hmainMass.le
  have hEbound : E ≤ Analysis.gaussianMRStarEndpoint := by
    dsimp only [E, Analysis.gaussianMRStarEndpoint]
    exact hendpoint
  have hh : h = 1 / (3 * s) := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    exact one_div_le_one_div_of_le (by norm_num only) (by nlinarith only [hsbound])
  have hmK : Analysis.gaussianMRStarIndex ≤ m := by
    dsimp only [m]
    exact hidxR
  have hm4 : (4 : ℝ) ≤ m := by
    have hKreal : (1000000000 : ℝ) ≤ m := by
      norm_num only [Analysis.gaussianMRStarIndex] at hmK ⊢
      exact hmK
    linarith only [hKreal]
  obtain ⟨hD, hgamma, hBeta⟩ := Analysis.gaussianMRStar_index_coefficients hmK
  have hCbound : LLS.PaperStatements.subgroupConductorLogSum H / t ≤ L := by
    have hC := LLS.PaperStatements.subgroupConductorLogSum_le H
    have hC' : LLS.PaperStatements.subgroupConductorLogSum H ≤ t * L := by
      dsimp only [t, m, L]
      exact hC
    exact (div_le_iff₀ ht).2 (by nlinarith only [hC'])
  have hA : LLS.PaperStatements.gaussianAmbientError n (r ^ 2) ≤ 125191 / 4500 :=
    Analysis.gaussianMRStar_ambient_error_le hL' (le_refl (Real.log n))
  have hcoeff := Analysis.gaussianMRStar_index_coefficients hmK
  rcases hcoeff with ⟨hD, hgamma, hBeta⟩
  have hcmp' :
    (m * (1 - h) * I - E) * r ≤
      Analysis.gaussianMRStarConductor * LLS.PaperStatements.subgroupConductorLogSum H +
        m * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) +
        13 +
        t * LLS.PaperStatements.gaussianAmbientError n (r ^ 2) := by
    simpa only [m, t, I, E, x, Analysis.gaussianMRStarConductor] using hcmp
  have hfinish :
    Analysis.gaussianMRStarD * r ≤
        Analysis.gaussianMRStarConductor * L + Analysis.gaussianMRStarBeta * s +
          (m / t) *
            (63 * Analysis.gaussianMRStarEndpoint / (10 * s) +
              1839 * Analysis.gaussianMRStarEndpoint / (1000 * r)) +
          13 / t +
          LLS.PaperStatements.gaussianAmbientError n (r ^ 2) →
      False := by
    intro hbudget
    exact
      Analysis.gaussianMRStar_large_index_comparison_impossible hmK hsbound hrbound hgamma hA
        (Analysis.gaussianMRStarRadius_equation hL') (by simpa only [t] using hbudget)
  exact
    Analysis.gaussianMR_relative_comparison_to_scalar hm4 (by rfl) hspos hrootSq hh hh1 hImass
      (by simpa only [E, Analysis.gaussianMRStarEndpoint] using hendpoint) hCbound
      (by norm_num only : (0 : ℝ) ≤ 161 / 400) hD hBeta hcmp' hfinish

/-- For the index-four common-sign subgroup with conductor cost at most `2L`,
the actual relative Gaussian comparison at the classified radius is impossible
once its explicit ambient and inverse-radius error is below `33`. -/
theorem gaussian_star_index_four_relative_inequality_contradiction {n : ℕ} [NeZero n]
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 600 ≤ Real.log n) :
    let L := Real.log n
    let r := Analysis.gaussianMRStarRadius L
    let s := Analysis.gaussianMRStarRoot L
    let h := 1 / (3 * s)
    let x := r ^ 2
    ¬(((H.index : ℝ) * (1 - h) *
              (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt x ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          (H.index : ℝ) *
            (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
          13 +
          ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientError n x) := by
  intro L r s h x hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(21 / 10 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  have hrpos : 0 < r := by
    dsimp only [r]
    exact sq_pos_of_pos (Analysis.gaussianMRStarRoot_pos hL)
  have hspos : 0 < s := by
    dsimp only [s]
    exact Analysis.gaussianMRStarRoot_pos hL
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, Analysis.gaussianMRStarRadius]
  have hrbound : 294 ≤ r := by
    have hr := Analysis.gaussianMRStarRadius_lower hL
    nlinarith only [hr, hL]
  have hsbound : 17 ≤ s := by nlinarith only [hrootSq, hrbound, hspos]
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  rw [hsqrtx] at hcmp
  have hI : Analysis.gaussianMRStarMass ≤ I := by
    dsimp only [I, Analysis.gaussianMRStarMass]
    exact LLS.PaperStatements.gaussianGamma_cutoff_gt_target.le
  have hE : E ≤ Analysis.gaussianMRStarEndpoint := by
    dsimp only [E, Analysis.gaussianMRStarEndpoint]
    exact Analysis.gaussian_endpoint_exp_le
  have hh : h = 1 / (3 * s) := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsbound]
  have hcmp' :
    (4 * (1 - h) * I - E) * r ≤
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * Real.exp (1 / 16 : ℝ)) +
        13 +
        3 * LLS.PaperStatements.gaussianAmbientError n (r ^ 2) := by
    dsimp only [x] at hcmp
    simpa only [hindex, hi, Nat.cast_ofNat, Nat.reduceSub] using hcmp
  have hA : LLS.PaperStatements.gaussianAmbientError n (r ^ 2) ≤ 125191 / 4500 :=
    Analysis.gaussianMRStar_ambient_error_le hL (le_refl (Real.log n))
  have hCscaled : LLS.PaperStatements.subgroupConductorLogSum H / 3 ≤ (2 / 3 : ℝ) * Real.log n := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 3)).2
    nlinarith only [hC]
  have herror := Analysis.gaussianMRStar_triple_scalar_error_lt hsbound hrbound hA
  exact
    Analysis.gaussianMR_relative_comparison_to_scalar (m := 4) (t := 3) (s := s) (r := r) (A :=
      LLS.PaperStatements.gaussianAmbientError n (r ^ 2)) (L := (2 / 3 : ℝ) * Real.log n) (I := I)
      (E := E) (C := LLS.PaperStatements.subgroupConductorLogSum H) (h := h) (M :=
      Analysis.gaussianMRStarMass) (Ecap := Analysis.gaussianMRStarEndpoint) (conductor :=
      (161 / 400 : ℝ)) (D :=
      (4 * Analysis.gaussianMRStarMass - Analysis.gaussianMRStarEndpoint) / 3) (beta :=
      (4 / 3 : ℝ) * (Analysis.gaussianMRStarMass / 3 + 3 / 10)) (by norm_num only : (4 : ℝ) ≤ 4)
      (by norm_num only : (3 : ℝ) = (4 : ℝ) - 1) hspos hrootSq.symm hh hh1 hI hE hCscaled
      (by norm_num only : (0 : ℝ) ≤ 161 / 400) le_rfl le_rfl hcmp'
      (by
        intro hbudget
        have hnorm' :
          ((4 * Analysis.gaussianMRStarMass - Analysis.gaussianMRStarEndpoint) / 3) * r ≤
            (161 / 600 : ℝ) * Real.log n +
              (4 / 3 : ℝ) * (Analysis.gaussianMRStarMass / 3 + 3 / 10) * s +
              33 := by
          dsimp only [Analysis.gaussianMRStarMass,
            Analysis.gaussianMRStarEndpoint] at hbudget herror ⊢
          nlinarith only [hbudget, herror]
        exact Analysis.gaussianMRStar_triple_comparison_impossible hL hnorm')

/-- Under GRH, an index-four subgroup containing all strong-MR passes and with
conductor-log sum at most `2 log n` yields a prime witness below the classified
Gaussian star bound from logarithmic scale `600`. -/
theorem exists_prime_witness_le_gaussian_star_of_index_four {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 600 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMRStarBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let L := Real.log n
  let r := Analysis.gaussianMRStarRadius L
  let x := r ^ 2
  have hcut : (21 / 10 : ℝ) * x = Analysis.gaussianMRStarBound (Real.log n) := by
    dsimp only [x, Analysis.gaussianMRStarBound, r, L]
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (21 / 10 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hpbound
    rw [hcut] at hpbound
    by_contra hfail
    exact hnone ⟨p, hp, hpbound, hfail⟩
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ n → ⌊(21 / 10 : ℝ) * x⌋₊ < p := by
    intro p hp hpdvd
    apply lt_of_not_ge
    intro hfloor
    have hbound : (p : ℝ) ≤ (21 / 10 : ℝ) * x := (Nat.le_floor_iff' hp.ne_zero).mp hfloor
    have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
    exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn1 hnOdd hp hpdvd (hpass p hp hbound)
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n → (p : ℝ) ≤ (21 / 10 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hrootSq : (Analysis.gaussianMRStarRoot (Real.log n)) ^ 2 = r := by
    dsimp only [r, L, Analysis.gaussianMRStarRadius]
  have hrbound : 294 ≤ r := by
    have hrad := Analysis.gaussianMRStarRadius_lower hL
    dsimp only [r, L]
    nlinarith only [hrad, hL]
  have hsbound : 17 ≤ Analysis.gaussianMRStarRoot (Real.log n) := by
    have hspos := Analysis.gaussianMRStarRoot_pos hL
    nlinarith only [hrootSq, hrbound, hspos]
  have hspos : 0 < Analysis.gaussianMRStarRoot (Real.log n) := Analysis.gaussianMRStarRoot_pos hL
  have hwidth : 0 < 1 / (3 * Analysis.gaussianMRStarRoot (Real.log n)) := by positivity
  have hwidth1 : 1 / (3 * Analysis.gaussianMRStarRoot (Real.log n)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsbound]
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative hnlarge H hGRH hwidth hwidth1 hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hdiv hsmall
  exact gaussian_star_index_four_relative_inequality_contradiction H hi hC hL hcmp

/-- Under GRH, an index at least `10^9` containing every strong-MR pass gives
a prime witness below the classified Gaussian cutoff from logarithmic scale
600 onward. The index and pass-containment conditions are internal branch data;
the all-input theorem closes them by the Fermat-index classification. -/
theorem exists_prime_witness_le_gaussian_star_of_index_ge_billion {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ)
    (hi : Analysis.gaussianMRStarIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 600 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMRStarBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let L := Real.log n
  let r := Analysis.gaussianMRStarRadius L
  let x := r ^ 2
  have hcut : (21 / 10 : ℝ) * x = Analysis.gaussianMRStarBound (Real.log n) := by
    dsimp only [x, Analysis.gaussianMRStarBound, r, L]
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (21 / 10 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hpbound
    rw [hcut] at hpbound
    by_contra hfail
    exact hnone ⟨p, hp, hpbound, hfail⟩
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ n → ⌊(21 / 10 : ℝ) * x⌋₊ < p := by
    intro p hp hpdvd
    apply lt_of_not_ge
    intro hfloor
    have hbound : (p : ℝ) ≤ (21 / 10 : ℝ) * x := (Nat.le_floor_iff' hp.ne_zero).mp hfloor
    have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
    exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn1 hnOdd hp hpdvd (hpass p hp hbound)
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n → (p : ℝ) ≤ (21 / 10 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hL' : 600 ≤ Real.log n := hL
  have hrootSq : (Analysis.gaussianMRStarRoot (Real.log n)) ^ 2 = r := by
    dsimp only [r, L, Analysis.gaussianMRStarRadius]
  have hrbound : 294 ≤ r := by
    have hrad := Analysis.gaussianMRStarRadius_lower hL'
    dsimp only [r, L]
    nlinarith only [hrad, hL']
  have hsbound : 17 ≤ Analysis.gaussianMRStarRoot (Real.log n) := by
    have hspos := Analysis.gaussianMRStarRoot_pos hL'
    nlinarith only [hrootSq, hrbound, hspos]
  have hspos : 0 < Analysis.gaussianMRStarRoot (Real.log n) := Analysis.gaussianMRStarRoot_pos hL'
  have hwidth : 0 < 1 / (3 * Analysis.gaussianMRStarRoot (Real.log n)) := by positivity
  have hwidth1 : 1 / (3 * Analysis.gaussianMRStarRoot (Real.log n)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsbound]
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative hnlarge H hGRH hwidth hwidth1 hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hdiv hsmall
  exact gaussian_star_relative_inequality_contradiction H hi hL hcmp

/-- The Fermat subgroup supplies the pass-containment condition for the
large-index Gaussian branch. -/
theorem exists_prime_witness_le_gaussian_star_of_large_fermat_index {n : ℕ} (hn1 : 1 < n)
    (hnOdd : Odd n) (hi : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 600 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMRStarBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hExp10 : (11 : ℝ) ≤ Real.exp 10 := by
    have h := Real.add_one_le_exp (10 : ℝ)
    norm_num only at h
    exact h
  have hExp600 : (20000 : ℝ) < Real.exp (600 : ℝ) := by
    have hpow : (11 : ℝ) ^ 5 ≤ Real.exp 10 ^ 60 := by
      calc
        (11 : ℝ) ^ 5 ≤ (11 : ℝ) ^ 60 := by
          exact pow_le_pow_right₀ (by norm_num only) (by norm_num only)
        _ ≤ Real.exp 10 ^ 60 := pow_le_pow_left₀ (by norm_num only) hExp10 60
    have hexp : Real.exp (600 : ℝ) = Real.exp 10 ^ 60 := by
      rw [show (600 : ℝ) = (60 : ℕ) * 10 by norm_num only]
      exact Real.exp_nat_mul 10 60
    rw [hexp]
    exact lt_of_lt_of_le (by norm_num only) hpow
  have hlog20000 : Real.log (20000 : ℝ) < 600 :=
    (Real.log_lt_iff_lt_exp (by norm_num only)).2 hExp600
  have hnlarge : 20000 ≤ n := by
    by_contra hnot
    have hnlt : n < 20000 := Nat.lt_of_not_ge hnot
    have hloglt : Real.log (n : ℝ) < Real.log (20000 : ℝ) :=
      Real.log_lt_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))) (Nat.cast_lt.mpr hnlt)
    exact (not_lt_of_ge hL) (hloglt.trans hlog20000)
  let H := PrimeTest.fermatSubgroup n
  have hiR : Analysis.gaussianMRStarIndex ≤ (H.index : ℝ) := by
    norm_num only [Analysis.gaussianMRStarIndex]
    exact_mod_cast hi
  have hHpass :
    ∀ z : ZMod n,
      PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z := by
    intro z hz
    obtain ⟨u, hu, hz⟩ := PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 hnOdd hz
    exact ⟨u, hu, hz⟩
  exact exists_prime_witness_le_gaussian_star_of_index_ge_billion hnOdd hnlarge H hiR hHpass hGRH hL

/-- Under GRH, a subgroup containing every strong-MR pass yields a prime
witness below the 6/5 Gaussian bound when its index is at least 10^9. -/
theorem gaussian6fifths_index_four_relative_inequality_contradiction {n : ℕ} [NeZero n]
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 500 ≤ Real.log n) :
    let L := Real.log n
    let r := Analysis.gaussianMR6FifthsRadius L
    let s := Analysis.gaussianMR6FifthsRoot L
    let h := 1 / (3 * s)
    let x := r ^ 2
    ¬(((H.index : ℝ) * (1 - h) *
              (∫ u in (0 : ℝ)..(6 / 5 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt x ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          (H.index : ℝ) *
            (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
          13 +
          ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientError n x) := by
  intro L r s h x hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  have hrpos : 0 < r := by
    dsimp only [r]
    exact sq_pos_of_pos (Analysis.gaussianMR6FifthsRoot_pos hL)
  have hspos : 0 < s := by
    dsimp only [s]
    exact Analysis.gaussianMR6FifthsRoot_pos hL
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, Analysis.gaussianMR6FifthsRadius]
  have hrbound : 625 / 2 ≤ r := by
    have hr := Analysis.gaussianMR6FifthsRadius_lower hL
    nlinarith only [hr, hL]
  have hsbound : 17 ≤ s := by nlinarith only [hrootSq, hrbound, hspos]
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  rw [hsqrtx] at hcmp
  have hI : Analysis.gaussianMR6FifthsMass ≤ I := by
    dsimp only [I, Analysis.gaussianMR6FifthsMass]
    exact LLS.PaperStatements.gaussianGamma_cutoff_sixFifths_gt_target.le
  have hE : E ≤ Analysis.gaussianMR6FifthsEndpoint := by
    dsimp only [E, Analysis.gaussianMR6FifthsEndpoint]
    exact Analysis.gaussian_endpoint_exp_le
  have hh : h = 1 / (3 * s) := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsbound]
  have hcmp' :
    (4 * (1 - h) * I - E) * r ≤
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * Real.exp (1 / 16 : ℝ)) +
        13 +
        3 * LLS.PaperStatements.gaussianAmbientError n (r ^ 2) := by
    dsimp only [x] at hcmp
    simpa only [hindex, hi, Nat.cast_ofNat, Nat.reduceSub] using hcmp
  have hA : LLS.PaperStatements.gaussianAmbientError n (r ^ 2) ≤ 27 := by
    dsimp only [r, L]
    exact Analysis.gaussianMR6Fifths_ambient_error_le hL (le_refl (Real.log n))
  have hCscaled : LLS.PaperStatements.subgroupConductorLogSum H / 3 ≤ (2 / 3 : ℝ) * Real.log n := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 3)).2
    nlinarith only [hC]
  have herror :
    (4 / 3 : ℝ) *
          (63 * Analysis.gaussianMR6FifthsEndpoint / (10 * s) +
            1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / 3 +
        LLS.PaperStatements.gaussianAmbientError n (r ^ 2) <
      33 := by
    have hterm1 :
      63 * Analysis.gaussianMR6FifthsEndpoint / (10 * s) ≤
        63 * Analysis.gaussianMR6FifthsEndpoint / (10 * 17) := by
      apply div_le_div_of_nonneg_left
      · norm_num only [Analysis.gaussianMR6FifthsEndpoint]
      · norm_num only
      · nlinarith only [hsbound]
    have hterm2 :
      1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r) ≤
        1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * (625 / 2)) := by
      apply div_le_div_of_nonneg_left
      · norm_num only [Analysis.gaussianMR6FifthsEndpoint]
      · norm_num only
      · nlinarith only [hrbound]
    rw [Analysis.gaussianMR6FifthsEndpoint] at hterm1 hterm2 ⊢
    norm_num only at hterm1 hterm2
    nlinarith only [hterm1, hterm2, hA]
  exact
    Analysis.gaussianMR_relative_comparison_to_scalar (m := 4) (t := 3) (s := s) (r := r) (A :=
      LLS.PaperStatements.gaussianAmbientError n (r ^ 2)) (L := (2 / 3 : ℝ) * Real.log n) (I := I)
      (E := E) (C := LLS.PaperStatements.subgroupConductorLogSum H) (h := h) (M :=
      Analysis.gaussianMR6FifthsMass) (Ecap := Analysis.gaussianMR6FifthsEndpoint) (conductor :=
      (161 / 400 : ℝ)) (D :=
      (4 * Analysis.gaussianMR6FifthsMass - Analysis.gaussianMR6FifthsEndpoint) / 3) (beta :=
      (4 / 3 : ℝ) * (Analysis.gaussianMR6FifthsMass / 3 + 3 / 10)) (by norm_num only : (4 : ℝ) ≤ 4)
      (by norm_num only : (3 : ℝ) = (4 : ℝ) - 1) hspos hrootSq.symm hh hh1 hI hE hCscaled
      (by norm_num only : (0 : ℝ) ≤ 161 / 400) le_rfl le_rfl hcmp'
      (by
        intro hbudget
        have hnorm' :
          ((4 * Analysis.gaussianMR6FifthsMass - Analysis.gaussianMR6FifthsEndpoint) / 3) * r ≤
            (161 / 600 : ℝ) * Real.log n +
              (4 / 3 : ℝ) * (Analysis.gaussianMR6FifthsMass / 3 + 3 / 10) * s +
              33 := by
          dsimp only [Analysis.gaussianMR6FifthsMass,
            Analysis.gaussianMR6FifthsEndpoint] at hbudget herror ⊢
          nlinarith only [hbudget, herror]
        exact Analysis.gaussianMR6Fifths_triple_comparison_impossible hL hnorm')

/-- The signed relative Gaussian comparison is impossible for an index-four
subgroup at the constant-6 radius from logarithmic scale 300. -/
theorem gaussianMR6_index_four_relative_inequality_contradiction {n : ℕ} [NeZero n]
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 300 ≤ Real.log n) :
    let L := Real.log n
    let r := Analysis.gaussianMR6Radius L
    let s := Analysis.gaussianMR6Root L
    let h := 1 / (3 * s)
    let x := r ^ 2
    ¬(((H.index : ℝ) * (1 - h) *
              (∫ u in (0 : ℝ)..(6 / 5 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt x ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          (H.index : ℝ) *
            (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
          13 +
          ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientErrorPrefixSigned n x) := by
  intro L r s h x hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  have hrpos : 0 < r := by
    dsimp only [r]
    exact sq_pos_of_pos (Analysis.gaussianMR6Root_pos hL)
  have hspos : 0 < s := by
    dsimp only [s]
    exact Analysis.gaussianMR6Root_pos hL
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, Analysis.gaussianMR6Radius]
  have hrbound : 415 / 2 ≤ r := by
    dsimp only [r]
    have hr := Analysis.gaussianMR6Radius_lower hL
    nlinarith only [hL, hr]
  have hsbound : 14 ≤ s := by
    dsimp only [s]
    exact Analysis.gaussianMR6Root_lower_14 hL
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  rw [hsqrtx] at hcmp
  have hI : Analysis.gaussianMR6FifthsMass ≤ I := by
    dsimp only [I, Analysis.gaussianMR6FifthsMass]
    exact LLS.PaperStatements.gaussianGamma_cutoff_sixFifths_gt_target.le
  have hE : E ≤ Analysis.gaussianMR6FifthsEndpoint := by
    dsimp only [E, Analysis.gaussianMR6FifthsEndpoint]
    exact Analysis.gaussian_endpoint_exp_le
  have hh : h = 1 / (3 * s) := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsbound]
  have hcmp' :
    (4 * (1 - h) * I - E) * r ≤
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * Real.exp (1 / 16 : ℝ)) +
        13 +
        3 * LLS.PaperStatements.gaussianAmbientErrorPrefixSigned n (r ^ 2) := by
    dsimp only [x] at hcmp
    simpa only [hindex, hi, Nat.cast_ofNat, Nat.reduceSub] using hcmp
  have hA : LLS.PaperStatements.gaussianAmbientErrorPrefixSigned n (r ^ 2) ≤ 27 / 5 := by
    dsimp only [r, L]
    exact Analysis.gaussianMR6_ambient_error_prefix_signed_le hL le_rfl
  have hCscaled : LLS.PaperStatements.subgroupConductorLogSum H / 3 ≤ (2 / 3 : ℝ) * Real.log n := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 3)).2
    nlinarith only [hC]
  have herror :
    (4 / 3 : ℝ) *
          (63 * Analysis.gaussianMR6FifthsEndpoint / (10 * s) +
            1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / 3 +
        LLS.PaperStatements.gaussianAmbientErrorPrefixSigned n (r ^ 2) <
      11 := by
    have hterm1 :
      63 * Analysis.gaussianMR6FifthsEndpoint / (10 * s) ≤
        63 * Analysis.gaussianMR6FifthsEndpoint / (10 * 14) := by
      apply div_le_div_of_nonneg_left
      · norm_num only [Analysis.gaussianMR6FifthsEndpoint]
      · norm_num only
      · nlinarith only [hsbound]
    have hterm2 :
      1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r) ≤
        1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * (415 / 2)) := by
      apply div_le_div_of_nonneg_left
      · norm_num only [Analysis.gaussianMR6FifthsEndpoint]
      · norm_num only
      · nlinarith only [hrbound]
    rw [Analysis.gaussianMR6FifthsEndpoint] at hterm1 hterm2 ⊢
    norm_num only at hterm1 hterm2
    nlinarith only [hterm1, hterm2, hA]
  exact
    Analysis.gaussianMR_relative_comparison_to_scalar (m := 4) (t := 3) (s := s) (r := r) (A :=
      LLS.PaperStatements.gaussianAmbientErrorPrefixSigned n (r ^ 2)) (L :=
      (2 / 3 : ℝ) * Real.log n) (I := I) (E := E) (C :=
      LLS.PaperStatements.subgroupConductorLogSum H) (h := h) (M := Analysis.gaussianMR6FifthsMass)
      (Ecap := Analysis.gaussianMR6FifthsEndpoint) (conductor := (161 / 400 : ℝ)) (D :=
      (4 * Analysis.gaussianMR6FifthsMass - Analysis.gaussianMR6FifthsEndpoint) / 3) (beta :=
      (4 / 3 : ℝ) * (Analysis.gaussianMR6FifthsMass / 3 + 3 / 10)) (by norm_num only : (4 : ℝ) ≤ 4)
      (by norm_num only : (3 : ℝ) = (4 : ℝ) - 1) hspos hrootSq.symm hh hh1 hI hE hCscaled
      (by norm_num only : (0 : ℝ) ≤ 161 / 400) le_rfl le_rfl hcmp'
      (by
        intro hbudget
        have hnorm :
          ((4 * Analysis.gaussianMR6FifthsMass - Analysis.gaussianMR6FifthsEndpoint) / 3) * r ≤
            (161 / 600 : ℝ) * Real.log n +
              (4 / 3 : ℝ) * (Analysis.gaussianMR6FifthsMass / 3 + 3 / 10) * s +
              11 := by
          dsimp only [Analysis.gaussianMR6FifthsMass,
            Analysis.gaussianMR6FifthsEndpoint] at hbudget herror ⊢
          nlinarith only [hbudget, herror]
        exact Analysis.gaussianMR6_triple_comparison_impossible hL hnorm)

/-- An index-four subgroup with conductor cost `2L` yields a prime witness
below the constant-6 Gaussian bound from logarithmic scale 300. -/
theorem exists_prime_witness_le_gaussianMR6_of_index_four {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let r := Analysis.gaussianMR6Radius (Real.log n)
  let x := r ^ 2
  have hcut : (6 / 5 : ℝ) * x = Analysis.gaussianMR6Bound (Real.log n) := by
    dsimp only [x, Analysis.gaussianMR6Bound, Analysis.gaussianMR6Radius, r]
  have hX : 50000 ≤ (6 / 5 : ℝ) * x := by
    rw [hcut]
    exact (Analysis.gaussianMR6Bound_gt_prefix hL).le
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (6 / 5 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hpbound
    rw [hcut] at hpbound
    by_contra hfail
    exact hnone ⟨p, hp, hpbound, hfail⟩
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ n → ⌊(6 / 5 : ℝ) * x⌋₊ < p := by
    intro p hp hpdvd
    apply lt_of_not_ge
    intro hfloor
    have hbound : (p : ℝ) ≤ (6 / 5 : ℝ) * x := (Nat.le_floor_iff' hp.ne_zero).mp hfloor
    have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
    exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn1 hnOdd hp hpdvd (hpass p hp hbound)
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n → (p : ℝ) ≤ (6 / 5 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hrootSq : (Analysis.gaussianMR6Root (Real.log n)) ^ 2 = r := by
    dsimp only [r, Analysis.gaussianMR6Radius]
  have hrbound : 415 / 2 ≤ r := by
    dsimp only [r]
    have hr := Analysis.gaussianMR6Radius_lower hL
    nlinarith only [hr, hL]
  have hspos : 0 < Analysis.gaussianMR6Root (Real.log n) := Analysis.gaussianMR6Root_pos hL
  have hsbound : 14 ≤ Analysis.gaussianMR6Root (Real.log n) := Analysis.gaussianMR6Root_lower_14 hL
  have hwidth : 0 < 1 / (3 * Analysis.gaussianMR6Root (Real.log n)) := by positivity
  have hwidth1 : 1 / (3 * Analysis.gaussianMR6Root (Real.log n)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsbound]
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative_prefix_gain_signed hnlarge H hGRH
      hwidth hwidth1 hx (by norm_num only : (0 : ℝ) ≤ 6 / 5) hX hdiv hsmall
  exact gaussianMR6_index_four_relative_inequality_contradiction H hi hC hL hcmp

/-- The prefix-adjusted relative Gaussian comparison is impossible for an
index-four subgroup at the constant-18 radius from logarithmic scale 300. -/
theorem gaussianMR18_index_four_relative_inequality_contradiction {n : ℕ} [NeZero n]
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 300 ≤ Real.log n) :
    let L := Real.log n
    let r := Analysis.gaussianMR18Radius L
    let s := Analysis.gaussianMR18Root L
    let h := 1 / (3 * s)
    let x := r ^ 2
    ¬(((H.index : ℝ) * (1 - h) *
              (∫ u in (0 : ℝ)..(6 / 5 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt x ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          (H.index : ℝ) *
            (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
          13 +
          ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientErrorPrefix n x) := by
  intro L r s h x hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  have hrpos : 0 < r := by
    dsimp only [r]
    exact sq_pos_of_pos (Analysis.gaussianMR18Root_pos hL)
  have hspos : 0 < s := by
    dsimp only [s]
    exact Analysis.gaussianMR18Root_pos hL
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, Analysis.gaussianMR18Radius]
  have hrbound : 455 / 2 ≤ r := by
    dsimp only [r]
    exact Analysis.gaussianMR18Radius_lower_455_over_2 hL
  have hsbound : 15 ≤ s := by
    dsimp only [s]
    exact Analysis.gaussianMR18Root_lower_15 hL
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  rw [hsqrtx] at hcmp
  have hI : Analysis.gaussianMR6FifthsMass ≤ I := by
    dsimp only [I, Analysis.gaussianMR6FifthsMass]
    exact LLS.PaperStatements.gaussianGamma_cutoff_sixFifths_gt_target.le
  have hE : E ≤ Analysis.gaussianMR6FifthsEndpoint := by
    dsimp only [E, Analysis.gaussianMR6FifthsEndpoint]
    exact Analysis.gaussian_endpoint_exp_le
  have hh : h = 1 / (3 * s) := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsbound]
  have hcmp' :
    (4 * (1 - h) * I - E) * r ≤
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
        4 * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * Real.exp (1 / 16 : ℝ)) +
        13 +
        3 * LLS.PaperStatements.gaussianAmbientErrorPrefix n (r ^ 2) := by
    dsimp only [x] at hcmp
    simpa only [hindex, hi, Nat.cast_ofNat, Nat.reduceSub] using hcmp
  have hA : LLS.PaperStatements.gaussianAmbientErrorPrefix n (r ^ 2) ≤ 27 - 484381 / 50000 := by
    dsimp only [r, L]
    exact Analysis.gaussianMR18_ambient_error_prefix_le hL (le_rfl)
  have hCscaled : LLS.PaperStatements.subgroupConductorLogSum H / 3 ≤ (2 / 3 : ℝ) * Real.log n := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 3)).2
    nlinarith only [hC]
  have herror :
    (4 / 3 : ℝ) *
          (63 * Analysis.gaussianMR6FifthsEndpoint / (10 * s) +
            1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / 3 +
        LLS.PaperStatements.gaussianAmbientErrorPrefix n (r ^ 2) <
      23 := by
    have hterm1 :
      63 * Analysis.gaussianMR6FifthsEndpoint / (10 * s) ≤
        63 * Analysis.gaussianMR6FifthsEndpoint / (10 * 15) := by
      apply div_le_div_of_nonneg_left
      · norm_num only [Analysis.gaussianMR6FifthsEndpoint]
      · norm_num only
      · nlinarith only [hsbound]
    have hterm2 :
      1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r) ≤
        1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * (455 / 2)) := by
      apply div_le_div_of_nonneg_left
      · norm_num only [Analysis.gaussianMR6FifthsEndpoint]
      · norm_num only
      · nlinarith only [hrbound]
    rw [Analysis.gaussianMR6FifthsEndpoint] at hterm1 hterm2 ⊢
    norm_num only at hterm1 hterm2
    nlinarith only [hterm1, hterm2, hA]
  exact
    Analysis.gaussianMR_relative_comparison_to_scalar (m := 4) (t := 3) (s := s) (r := r) (A :=
      LLS.PaperStatements.gaussianAmbientErrorPrefix n (r ^ 2)) (L := (2 / 3 : ℝ) * Real.log n)
      (I := I) (E := E) (C := LLS.PaperStatements.subgroupConductorLogSum H) (h := h) (M :=
      Analysis.gaussianMR6FifthsMass) (Ecap := Analysis.gaussianMR6FifthsEndpoint) (conductor :=
      (161 / 400 : ℝ)) (D :=
      (4 * Analysis.gaussianMR6FifthsMass - Analysis.gaussianMR6FifthsEndpoint) / 3) (beta :=
      (4 / 3 : ℝ) * (Analysis.gaussianMR6FifthsMass / 3 + 3 / 10)) (by norm_num only : (4 : ℝ) ≤ 4)
      (by norm_num only : (3 : ℝ) = (4 : ℝ) - 1) hspos hrootSq.symm hh hh1 hI hE hCscaled
      (by norm_num only : (0 : ℝ) ≤ 161 / 400) le_rfl le_rfl hcmp'
      (by
        intro hbudget
        have hnorm :
          ((4 * Analysis.gaussianMR6FifthsMass - Analysis.gaussianMR6FifthsEndpoint) / 3) * r ≤
            (161 / 600 : ℝ) * Real.log n +
              (4 / 3 : ℝ) * (Analysis.gaussianMR6FifthsMass / 3 + 3 / 10) * s +
              23 := by
          dsimp only [Analysis.gaussianMR6FifthsMass,
            Analysis.gaussianMR6FifthsEndpoint] at hbudget herror ⊢
          nlinarith only [hbudget, herror]
        exact Analysis.gaussianMR18_triple_comparison_impossible hL hnorm)

/-- An index-four subgroup with the three-character conductor cost yields a
prime witness below the 6/5 Gaussian bound from logarithmic scale 500. -/
theorem exists_prime_witness_le_gaussian6fifths_of_index_four {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMR6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let r := Analysis.gaussianMR6FifthsRadius (Real.log n)
  let x := r ^ 2
  have hcut : (6 / 5 : ℝ) * x = Analysis.gaussianMR6FifthsBound (Real.log n) := by
    dsimp only [x, Analysis.gaussianMR6FifthsBound, Analysis.gaussianMR6FifthsRadius, r]
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (6 / 5 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hpbound
    rw [hcut] at hpbound
    by_contra hfail
    exact hnone ⟨p, hp, hpbound, hfail⟩
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ n → ⌊(6 / 5 : ℝ) * x⌋₊ < p := by
    intro p hp hpdvd
    apply lt_of_not_ge
    intro hfloor
    have hbound : (p : ℝ) ≤ (6 / 5 : ℝ) * x := (Nat.le_floor_iff' hp.ne_zero).mp hfloor
    have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
    exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn1 hnOdd hp hpdvd (hpass p hp hbound)
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n → (p : ℝ) ≤ (6 / 5 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hrootSq : (Analysis.gaussianMR6FifthsRoot (Real.log n)) ^ 2 = r := by
    dsimp only [r, Analysis.gaussianMR6FifthsRadius]
  have hrbound : 625 / 2 ≤ r := by
    have hrad := Analysis.gaussianMR6FifthsRadius_lower hL
    dsimp only [r]
    nlinarith only [hrad, hL]
  have hspos : 0 < Analysis.gaussianMR6FifthsRoot (Real.log n) :=
    Analysis.gaussianMR6FifthsRoot_pos hL
  have hsbound : 17 ≤ Analysis.gaussianMR6FifthsRoot (Real.log n) := by
    nlinarith only [hrootSq, hrbound, hspos]
  have hwidth : 0 < 1 / (3 * Analysis.gaussianMR6FifthsRoot (Real.log n)) := by positivity
  have hwidth1 : 1 / (3 * Analysis.gaussianMR6FifthsRoot (Real.log n)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsbound]
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative hnlarge H hGRH hwidth hwidth1 hx
      (by norm_num only : (0 : ℝ) ≤ 6 / 5) hdiv hsmall
  exact gaussian6fifths_index_four_relative_inequality_contradiction H hi hC hL hcmp

/-- An index-four subgroup with conductor cost `2L` yields a prime witness
below the prefix-improved constant-18 Gaussian bound from logarithmic scale 300. -/
theorem exists_prime_witness_le_gaussianMR18_of_index_four {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMR18Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let r := Analysis.gaussianMR18Radius (Real.log n)
  let x := r ^ 2
  have hcut : (6 / 5 : ℝ) * x = Analysis.gaussianMR18Bound (Real.log n) := by
    dsimp only [x, Analysis.gaussianMR18Bound, Analysis.gaussianMR18Radius, r]
  have hX : 50000 ≤ (6 / 5 : ℝ) * x := by
    rw [hcut]
    exact (Analysis.gaussianMR18Bound_gt_prefix hL).le
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (6 / 5 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hpbound
    rw [hcut] at hpbound
    by_contra hfail
    exact hnone ⟨p, hp, hpbound, hfail⟩
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ n → ⌊(6 / 5 : ℝ) * x⌋₊ < p := by
    intro p hp hpdvd
    apply lt_of_not_ge
    intro hfloor
    have hbound : (p : ℝ) ≤ (6 / 5 : ℝ) * x := (Nat.le_floor_iff' hp.ne_zero).mp hfloor
    have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
    exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn1 hnOdd hp hpdvd (hpass p hp hbound)
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n → (p : ℝ) ≤ (6 / 5 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hrootSq : (Analysis.gaussianMR18Root (Real.log n)) ^ 2 = r := by
    dsimp only [r, Analysis.gaussianMR18Radius]
  have hrbound : 455 / 2 ≤ r := by
    dsimp only [r]
    exact Analysis.gaussianMR18Radius_lower_455_over_2 hL
  have hspos : 0 < Analysis.gaussianMR18Root (Real.log n) := Analysis.gaussianMR18Root_pos hL
  have hsbound : 15 ≤ Analysis.gaussianMR18Root (Real.log n) :=
    Analysis.gaussianMR18Root_lower_15 hL
  have hwidth : 0 < 1 / (3 * Analysis.gaussianMR18Root (Real.log n)) := by positivity
  have hwidth1 : 1 / (3 * Analysis.gaussianMR18Root (Real.log n)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hsbound]
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative_prefix_gain hnlarge H hGRH hwidth
      hwidth1 hx (by norm_num only : (0 : ℝ) ≤ 6 / 5) hX hdiv hsmall
  exact gaussianMR18_index_four_relative_inequality_contradiction H hi hC hL hcmp

/-- Under GRH, a subgroup containing every strong-MR pass yields a prime
witness below the 6/5 Gaussian bound when its index is at least 10^9. -/
theorem exists_prime_witness_le_gaussian6fifths_of_index_ge_billion {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ)
    (hi : Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMR6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let L := Real.log n
  let r := Analysis.gaussianMR6FifthsRadius L
  let s := Analysis.gaussianMR6FifthsRoot L
  let x := r ^ 2
  let h := 1 / (3 * s)
  let m : ℝ := H.index
  let t : ℝ := m - 1
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  let C : ℝ := LLS.PaperStatements.subgroupConductorLogSum H
  let A : ℝ := LLS.PaperStatements.gaussianAmbientError n x
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, Analysis.gaussianMR6FifthsRadius]
  have hrbound : 625 / 2 ≤ r := by
    have hrad := Analysis.gaussianMR6FifthsRadius_lower hL
    dsimp only [r, L]
    nlinarith only [hrad, hL]
  have hspos : 0 < s := by
    dsimp only [s, L]
    exact Analysis.gaussianMR6FifthsRoot_pos hL
  have hs17 : 17 ≤ s := by nlinarith only [hrootSq, hrbound, hspos]
  have hh : h = 1 / (3 * s) := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hs17]
  have hrpos : 0 < r := by
    have hscaled := mul_pos (by norm_num only : (0 : ℝ) < 5 / 8) (by linarith only [hL] : 0 < L)
    exact lt_of_lt_of_le hscaled (Analysis.gaussianMR6FifthsRadius_lower hL)
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcut : (6 / 5 : ℝ) * x = Analysis.gaussianMR6FifthsBound (Real.log n) := by
    dsimp only [Analysis.gaussianMR6FifthsBound, Analysis.gaussianMR6FifthsRadius, r, L, x]
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (6 / 5 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hpbound
    rw [hcut] at hpbound
    by_contra hfail
    exact hnone ⟨p, hp, hpbound, hfail⟩
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ n → ⌊(6 / 5 : ℝ) * x⌋₊ < p := by
    intro p hp hpdvd
    apply lt_of_not_ge
    intro hfloor
    have hbound : (p : ℝ) ≤ (6 / 5 : ℝ) * x := (Nat.le_floor_iff' hp.ne_zero).mp hfloor
    exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn1 hnOdd hp hpdvd (hpass p hp hbound)
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n → (p : ℝ) ≤ (6 / 5 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hwidth : 0 < h := by
    dsimp only [h]
    exact one_div_pos.mpr (mul_pos (by norm_num only) hspos)
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative hnlarge H hGRH hwidth hh1 hx
      (by norm_num only : (0 : ℝ) ≤ 6 / 5) hdiv hsmall
  have hcastIndex : ((H.index - 1 : ℕ) : ℝ) = (H.index : ℝ) - 1 := by
    have hidxReal : (1 : ℝ) ≤ (H.index : ℝ) := by
      have hK : (1 : ℝ) ≤ Analysis.gaussianMR6FifthsIndex := by
        norm_num only [Analysis.gaussianMR6FifthsIndex]
      exact hK.trans hi
    have hidxNat : 1 ≤ H.index := by exact_mod_cast hidxReal
    rw [Nat.cast_sub hidxNat, Nat.cast_one]
  rw [hsqrtx, hcastIndex] at hcmp
  have hI : Analysis.gaussianMR6FifthsMass ≤ I := by
    dsimp only [I, Analysis.gaussianMR6FifthsMass]
    exact LLS.PaperStatements.gaussianGamma_cutoff_sixFifths_gt_target.le
  have hE : E ≤ Analysis.gaussianMR6FifthsEndpoint := by
    dsimp only [E, Analysis.gaussianMR6FifthsEndpoint]
    exact Analysis.gaussian_endpoint_exp_le
  have hC : C / t ≤ L := by
    have ht : t = (H.index : ℝ) - 1 := by rfl
    have htpos : 0 < t := by
      dsimp only [t, m]
      have hiNat : (1000000000 : ℝ) ≤ (H.index : ℝ) := hi
      linarith only [hiNat]
    have hC' : C ≤ t * L := by
      dsimp only [C, t, m, L]
      exact LLS.PaperStatements.subgroupConductorLogSum_le H
    exact (div_le_iff₀ htpos).2 (by nlinarith only [hC'])
  have hA : A ≤ 27 := by
    dsimp only [A, x, r, L]
    exact Analysis.gaussianMR6Fifths_ambient_error_le hL (le_refl (Real.log n))
  have hroot :
    Analysis.gaussianMR6FifthsD * r =
      Analysis.gaussianMR6FifthsConductor * L + Analysis.gaussianMR6FifthsBeta * s + 29 := by
    dsimp only [r, s, L]
    exact Analysis.gaussianMR6FifthsRadius_equation hL
  have hcmp' :
    (m * (1 - h) * I - E) * r ≤
      Analysis.gaussianMR6FifthsConductor * C +
        m * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) +
        13 +
        t * A := by
    simpa only [m, t, I, E, C, A, Analysis.gaussianMR6FifthsConductor] using hcmp
  exact
    Analysis.gaussianMR6Fifths_relative_comparison_impossible (m := m) (t := t) (s := s) (r := r)
      (A := A) (L := L) (I := I) (E := E) (C := C) (h := h) hi rfl hspos hs17 rfl hrbound hh hh1 hI
      hE hC hA hcmp' hroot

/-- Under GRH, a subgroup containing every strong-MR pass yields a prime
witness below the signed constant-6 Gaussian bound from logarithmic scale 300. -/
theorem exists_prime_witness_le_gaussianMR6_of_index_ge_billion {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ)
    (hi : Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let L := Real.log n
  let r := Analysis.gaussianMR6Radius L
  let s := Analysis.gaussianMR6Root L
  let x := r ^ 2
  let h := 1 / (3 * s)
  let m : ℝ := H.index
  let t : ℝ := m - 1
  let I : ℝ :=
    ∫ u in (0 : ℝ)..(6 / 5 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  let C : ℝ := LLS.PaperStatements.subgroupConductorLogSum H
  let A : ℝ := LLS.PaperStatements.gaussianAmbientErrorPrefixSigned n x
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  have hrootSq : s ^ 2 = r := by dsimp only [s, r, Analysis.gaussianMR6Radius]
  have hrbound : 415 / 2 ≤ r := by
    dsimp only [r, L]
    have hr := Analysis.gaussianMR6Radius_lower hL
    nlinarith only [hL, hr]
  have hspos : 0 < s := by
    dsimp only [s, L]
    exact Analysis.gaussianMR6Root_pos hL
  have hs14 : 14 ≤ s := by
    dsimp only [s, L]
    exact Analysis.gaussianMR6Root_lower_14 hL
  have hh : h = 1 / (3 * s) := by rfl
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hs14]
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 415 / 2) hrbound
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hrbound]
  have hcut : (6 / 5 : ℝ) * x = Analysis.gaussianMR6Bound (Real.log n) := by
    dsimp only [Analysis.gaussianMR6Bound, Analysis.gaussianMR6Radius, r, L, x]
  have hX : 50000 ≤ (6 / 5 : ℝ) * x := by
    rw [hcut]
    exact (Analysis.gaussianMR6Bound_gt_prefix hL).le
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (6 / 5 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hpbound
    rw [hcut] at hpbound
    by_contra hfail
    exact hnone ⟨p, hp, hpbound, hfail⟩
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ n → ⌊(6 / 5 : ℝ) * x⌋₊ < p := by
    intro p hp hpdvd
    apply lt_of_not_ge
    intro hfloor
    have hbound : (p : ℝ) ≤ (6 / 5 : ℝ) * x := (Nat.le_floor_iff' hp.ne_zero).mp hfloor
    exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn1 hnOdd hp hpdvd (hpass p hp hbound)
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n → (p : ℝ) ≤ (6 / 5 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p := by
    intro p hp hpdvd hpbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hpbound)
    exact ⟨u, huH, hu⟩
  have hwidth : 0 < h := one_div_pos.mpr (mul_pos (by norm_num only) hspos)
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative_prefix_gain_signed hnlarge H hGRH
      hwidth hh1 hx (by norm_num only : (0 : ℝ) ≤ 6 / 5) hX hdiv hsmall
  have hcastIndex : ((H.index - 1 : ℕ) : ℝ) = (H.index : ℝ) - 1 := by
    have hidxReal : (1 : ℝ) ≤ (H.index : ℝ) := by
      have hK : (1 : ℝ) ≤ Analysis.gaussianMR6FifthsIndex := by
        norm_num only [Analysis.gaussianMR6FifthsIndex]
      exact hK.trans hi
    have hidxNat : 1 ≤ H.index := by exact_mod_cast hidxReal
    rw [Nat.cast_sub hidxNat, Nat.cast_one]
  rw [hsqrtx, hcastIndex] at hcmp
  have hI : Analysis.gaussianMR6FifthsMass ≤ I := by
    dsimp only [I, Analysis.gaussianMR6FifthsMass]
    exact LLS.PaperStatements.gaussianGamma_cutoff_sixFifths_gt_target.le
  have hE : E ≤ Analysis.gaussianMR6FifthsEndpoint := by
    dsimp only [E, Analysis.gaussianMR6FifthsEndpoint]
    exact Analysis.gaussian_endpoint_exp_le
  have hC : C / t ≤ L := by
    have ht : t = (H.index : ℝ) - 1 := by rfl
    have htpos : 0 < t := by
      dsimp only [t, m]
      have hiNat : (1000000000 : ℝ) ≤ (H.index : ℝ) := hi
      linarith only [hiNat]
    have hC' : C ≤ t * L := by
      dsimp only [C, t, m, L]
      exact LLS.PaperStatements.subgroupConductorLogSum_le H
    exact (div_le_iff₀ htpos).2 (by nlinarith only [hC'])
  have hA : A ≤ 27 / 5 := by
    dsimp only [A, x, r, L]
    exact Analysis.gaussianMR6_ambient_error_prefix_signed_le hL le_rfl
  have hroot :
    Analysis.gaussianMR6FifthsD * r =
      Analysis.gaussianMR6FifthsConductor * L + Analysis.gaussianMR6FifthsBeta * s + 6 := by
    dsimp only [r, s, L]
    exact Analysis.gaussianMR6Radius_equation hL
  have hcmp' :
    (m * (1 - h) * I - E) * r ≤
      Analysis.gaussianMR6FifthsConductor * C +
        m * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) +
        13 +
        t * A := by
    simpa only [m, t, I, E, C, A, Analysis.gaussianMR6FifthsConductor] using hcmp
  have hcoeff := Analysis.gaussianMR6Fifths_index_coefficients hi
  have hD :
    Analysis.gaussianMR6FifthsD ≤
      (m * Analysis.gaussianMR6FifthsMass - Analysis.gaussianMR6FifthsEndpoint) / t := by
    simpa only [t] using hcoeff.1
  have hbeta :
    (m / t) * (Analysis.gaussianMR6FifthsMass / 3 + 3 / 10) ≤ Analysis.gaussianMR6FifthsBeta := by
    simpa only [t] using hcoeff.2.2
  have hfinish :
    Analysis.gaussianMR6FifthsD * r ≤
        Analysis.gaussianMR6FifthsConductor * L + Analysis.gaussianMR6FifthsBeta * s +
          (m / t) *
            (63 * Analysis.gaussianMR6FifthsEndpoint / (10 * s) +
              1839 * Analysis.gaussianMR6FifthsEndpoint / (1000 * r)) +
          13 / t +
          A →
      False := by
    intro hbudget
    have ht : t = m - 1 := by rfl
    have hgamma := hcoeff.2.1
    exact
      Analysis.gaussianMR6_large_index_comparison_impossible hi hs14 hrbound hgamma hA hroot
        (by simpa only [ht] using hbudget)
  exact
    Analysis.gaussianMR_relative_comparison_to_scalar (m := m) (t := t) (s := s) (r := r) (A := A)
      (L := L) (I := I) (E := E) (C := C) (h := h) (M := Analysis.gaussianMR6FifthsMass) (Ecap :=
      Analysis.gaussianMR6FifthsEndpoint) (conductor := Analysis.gaussianMR6FifthsConductor) (D :=
      Analysis.gaussianMR6FifthsD) (beta := Analysis.gaussianMR6FifthsBeta)
      (by
        have hi' : (1000000000 : ℝ) ≤ m := by
          simpa only [m, Analysis.gaussianMR6FifthsIndex] using hi
        linarith only [hi'])
      rfl hspos rfl hh hh1 hI hE hC (by norm_num only [Analysis.gaussianMR6FifthsConductor]) hD
      hbeta hcmp' hfinish

/-- The constant-6 witness theorem also implies the older constant-18 bound. -/
theorem exists_prime_witness_le_gaussianMR18_of_index_ge_billion {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ)
    (hi : Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMR18Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hpbound, hfail⟩ :=
    exists_prime_witness_le_gaussianMR6_of_index_ge_billion hnOdd hnlarge H hi hHpass hGRH hL
  exact ⟨p, hp, hpbound.trans (Analysis.gaussianMR6Bound_le_gaussianMR18Bound hL), hfail⟩

/-- The Fermat subgroup supplies pass containment in the 6/5 branch. -/
theorem exists_prime_witness_le_gaussian6fifths_of_large_fermat_index {n : ℕ} (hn1 : 1 < n)
    (hnOdd : Odd n) (hi : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMR6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hExp10 : (11 : ℝ) ≤ Real.exp 10 := by
    have h := Real.add_one_le_exp (10 : ℝ)
    norm_num only at h
    exact h
  have hpow : (11 : ℝ) ^ 5 ≤ Real.exp 10 ^ 50 := by
    calc
      (11 : ℝ) ^ 5 ≤ (11 : ℝ) ^ 50 := pow_le_pow_right₀ (by norm_num only) (by norm_num only)
      _ ≤ Real.exp 10 ^ 50 := pow_le_pow_left₀ (by norm_num only) hExp10 50
  have hexp : Real.exp (500 : ℝ) = Real.exp 10 ^ 50 := by
    rw [show (500 : ℝ) = (50 : ℕ) * 10 by norm_num only]
    exact Real.exp_nat_mul 10 50
  have hExp500 : (20000 : ℝ) < Real.exp (500 : ℝ) := by
    rw [hexp]
    exact lt_of_lt_of_le (by norm_num only) hpow
  have hlog20000 : Real.log (20000 : ℝ) < 500 :=
    (Real.log_lt_iff_lt_exp (by norm_num only)).2 hExp500
  have hnlarge : 20000 ≤ n := by
    by_contra hnot
    have hnlt : n < 20000 := Nat.lt_of_not_ge hnot
    have hloglt : Real.log (n : ℝ) < Real.log (20000 : ℝ) :=
      Real.log_lt_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))) (Nat.cast_lt.mpr hnlt)
    exact (not_lt_of_ge hL) (hloglt.trans hlog20000)
  let H := PrimeTest.fermatSubgroup n
  have hiR : Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ) := by
    norm_num only [Analysis.gaussianMR6FifthsIndex]
    exact_mod_cast hi
  have hHpass :
    ∀ z : ZMod n,
      PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z := by
    intro z hz
    obtain ⟨u, hu, hz⟩ := PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 hnOdd hz
    exact ⟨u, hu, hz⟩
  exact
    exists_prime_witness_le_gaussian6fifths_of_index_ge_billion hnOdd hnlarge H hiR hHpass hGRH hL

/-- The Fermat subgroup supplies pass containment in the constant-6 branch. -/
theorem exists_prime_witness_le_gaussianMR6_of_large_fermat_index {n : ℕ} (hn1 : 1 < n)
    (hnOdd : Odd n) (hi : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hExp10 : (11 : ℝ) ≤ Real.exp 10 := by
    have h := Real.add_one_le_exp (10 : ℝ)
    norm_num only at h
    exact h
  have hpow : (11 : ℝ) ^ 5 ≤ Real.exp 10 ^ 30 := by
    calc
      (11 : ℝ) ^ 5 ≤ (11 : ℝ) ^ 30 := pow_le_pow_right₀ (by norm_num only) (by norm_num only)
      _ ≤ Real.exp 10 ^ 30 := pow_le_pow_left₀ (by norm_num only) hExp10 30
  have hexp : Real.exp (300 : ℝ) = Real.exp 10 ^ 30 := by
    rw [show (300 : ℝ) = (30 : ℕ) * 10 by norm_num only]
    exact Real.exp_nat_mul 10 30
  have hExp300 : (20000 : ℝ) < Real.exp (300 : ℝ) := by
    rw [hexp]
    exact lt_of_lt_of_le (by norm_num only) hpow
  have hlog20000 : Real.log (20000 : ℝ) < 300 :=
    (Real.log_lt_iff_lt_exp (by norm_num only)).2 hExp300
  have hnlarge : 20000 ≤ n := by
    by_contra hnot
    have hnlt : n < 20000 := Nat.lt_of_not_ge hnot
    have hloglt : Real.log (n : ℝ) < Real.log (20000 : ℝ) :=
      Real.log_lt_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))) (Nat.cast_lt.mpr hnlt)
    exact (not_lt_of_ge hL) (hloglt.trans hlog20000)
  let H := PrimeTest.fermatSubgroup n
  have hiR : Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ) := by
    norm_num only [Analysis.gaussianMR6FifthsIndex]
    exact_mod_cast hi
  have hHpass :
    ∀ z : ZMod n,
      PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z := by
    intro z hz
    obtain ⟨u, hu, hz⟩ := PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 hnOdd hz
    exact ⟨u, hu, hz⟩
  exact exists_prime_witness_le_gaussianMR6_of_index_ge_billion hnOdd hnlarge H hiR hHpass hGRH hL

/-- The constant-6 Fermat-index theorem implies the older constant-18 bound. -/
theorem exists_prime_witness_le_gaussianMR18_of_large_fermat_index {n : ℕ} (hn1 : 1 < n)
    (hnOdd : Odd n) (hi : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianMR18Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hpbound, hfail⟩ :=
    exists_prime_witness_le_gaussianMR6_of_large_fermat_index hn1 hnOdd hi hGRH hL
  exact ⟨p, hp, hpbound.trans (Analysis.gaussianMR6Bound_le_gaussianMR18Bound hL), hfail⟩

/-- At logarithmic scale at least 4000, the actual relative Gaussian
subgroup comparison contradicts the variable-radius numerical budget. -/
theorem gaussian_variable_relative_inequality_contradiction {n : ℕ} [NeZero n]
    (H : Subgroup (ZMod n)ˣ) (hi : 4 ≤ H.index) (hL : 4000 ≤ Real.log n) :
    let L := Real.log n
    let r := Analysis.gaussianMRVariableRadius L
    let h := 1 / (3 * Real.sqrt r)
    let x := r ^ 2
    ¬(((H.index : ℝ) * (1 - h) *
              (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
                (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
            Real.exp (1 / 16 : ℝ)) *
          Real.sqrt x ≤
        (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H +
          (H.index : ℝ) *
            (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
          13 +
          ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianAmbientError n x) := by
  intro L r h x hcmp
  have hm : (0 : ℝ) < (H.index : ℝ) - 1 := by
    have hiR : (4 : ℝ) ≤ H.index := Nat.cast_le.mpr hi
    linarith only [hiR]
  have hcast : ((H.index - 1 : ℕ) : ℝ) = (H.index : ℝ) - 1 := by
    rw [Nat.cast_sub (le_trans (by decide : 1 ≤ 4) hi), Nat.cast_one]
  rw [hcast] at hcmp
  have hrL : L / 2 ≤ r := by
    dsimp only [r, L]
    exact Analysis.gaussianMRVariableRadius_half hL
  have hrpos : 0 < r := by
    have hLpos : 0 < L := by
      dsimp only [L]; linarith only [hL]
    exact lt_of_lt_of_le (div_pos hLpos (by norm_num only)) hrL
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hrpos
  have hs20 : 20 ≤ Real.sqrt r := by
    dsimp only [r, L]
    exact Analysis.gaussianMRVariableRadius_sqrt_lower hL
  have hh : h = 1 / (3 * Real.sqrt r) := by rfl
  have hhpos : 0 < h := by
    rw [hh]; positivity
  have hh1 : h ≤ 1 / 2 := by
    rw [hh]
    have hsbound : 2 ≤ 3 * Real.sqrt r := by nlinarith only [hs20]
    exact (one_div_le_one_div_of_le (by norm_num only) hsbound)
  have hr2000 : 2000 ≤ r := by
    have hL' : 4000 ≤ L := by
      dsimp only [L]; exact hL
    have hrad := Analysis.gaussianMRVariableRadius_half (L := L) hL'
    dsimp only [r, Analysis.gaussianMRVariableRadius] at hrad ⊢
    have hLhalf : 2000 ≤ L / 2 := by linarith only [hL']
    exact hLhalf.trans hrad
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hr2000]
  have hsqrtx : Real.sqrt x = r := by
    dsimp only [x]
    exact Real.sqrt_sq hrpos.le
  have hE := Analysis.gaussian_endpoint_exp_le
  have hI := LLS.PaperStatements.gaussianGamma_cutoff_gt_target.le
  let m : ℝ := H.index
  let t : ℝ := m - 1
  let u : ℝ := m / t
  let v : ℝ := 1 / t
  have ht : 0 < t := by
    dsimp only [t, m]; exact hm
  have hu' : u ≤ 4 / 3 := by
    have hiR : 4 ≤ m := by
      dsimp only [m]; exact Nat.cast_le.mpr hi
    have ht' : 0 < m - 1 := by linarith only [hiR]
    change m / (m - 1) ≤ 4 / 3
    rw [div_le_iff₀ ht']
    nlinarith only [hiR]
  have hv0 : 0 ≤ v := by
    dsimp only [v]; positivity
  have hv3 : v ≤ 1 / 3 := by
    have hiR : 4 ≤ m := by
      dsimp only [m]; exact Nat.cast_le.mpr hi
    have ht' : 0 < m - 1 := by linarith only [hiR]
    change (1 : ℝ) / (m - 1) ≤ 1 / 3
    rw [div_le_iff₀ ht']
    nlinarith only [hiR]
  have huv : u = 1 + v := by
    dsimp only [u, v, t]
    have ht' : 0 < m - 1 := by simpa only [t] using ht
    field_simp [ne_of_gt ht']
    ring_nf
  let I : ℝ :=
    ∫ z in (0 : ℝ)..(21 / 10 : ℝ),
      (LLS.PaperStatements.gaussianGammaMellinKernel.transform z).re / Real.sqrt z
  let E : ℝ := Real.exp (1 / 16 : ℝ)
  have hI' : 8147 / 10000 ≤ I := by
    dsimp only [I]
    exact (by norm_num only : (8147 / 10000 : ℝ) ≤ 81470555 / 100000000).trans hI
  have hE' : E ≤ 2129 / 2000 := by
    dsimp only [E]; exact hE
  have hmain :=
    Analysis.gaussianMRVariable_normalized_main_lower huv hv0 hv3
      (by
        dsimp only [r]; exact hs)
      hh
      (by
        rw [hh]; exact hh1)
      hI' hE'
  have huMul : u * t = m := by
    dsimp only [u, t]
    exact div_mul_cancel₀ m (ne_of_gt hm)
  have hvMul : v * t = 1 := by
    dsimp only [v, t]
    exact one_div_mul_cancel (ne_of_gt hm)
  have hleft :
    t * ((21943 / 30000 : ℝ) * r - (4 / 9 * (8147 / 10000)) * Real.sqrt r) ≤
      ((m * (1 - h) * I - E) * r) := by
    have := mul_le_mul_of_nonneg_right hmain (mul_nonneg ht.le hrpos.le)
    have hratio :
      (4 / 9 * (8147 / 10000)) / Real.sqrt r * r = (4 / 9 * (8147 / 10000)) * Real.sqrt r := by
      rw [div_eq_mul_inv]
      field_simp [hs.ne']
      rw [Real.sq_sqrt hrpos.le]
    have hrel : (u * (1 - h) * I - v * E) * (t * r) = (m * (1 - h) * I - E) * r := by
      calc
        _ = ((u * t) * (1 - h) * I - (v * t) * E) * r := by ring
        _ = _ := by
          rw [huMul, hvMul]; ring
    have hleftEq :
      (21943 / 30000 - (4 / 9 * (8147 / 10000)) / Real.sqrt r) * (t * r) =
        t * ((21943 / 30000 : ℝ) * r - (4 / 9 * (8147 / 10000)) * Real.sqrt r) := by
      rw [div_eq_mul_inv]
      field_simp [hs.ne']
      have hsq : Real.sqrt r * Real.sqrt r = r := by nlinarith only [Real.sq_sqrt hrpos.le]
      nlinarith only [hsq]
    calc
      _ = (21943 / 30000 - (4 / 9 * (8147 / 10000)) / Real.sqrt r) * (t * r) := hleftEq.symm
      _ ≤ (u * (1 - h) * I - v * E) * (t * r) := this
      _ = _ := hrel
  have hcond := LLS.PaperStatements.subgroupConductorLogSum_le H
  have hcond' := mul_le_mul_of_nonneg_left hcond (by norm_num only : (0 : ℝ) ≤ 161 / 400)
  have hW :=
    Analysis.gaussianMRVariable_error_bracket_upper hs
      (by
        symm; exact Real.sq_sqrt hrpos.le)
      hh hE'
  let W : ℝ := 1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E
  have hW' :
    (4 / 3) * W ≤
      (2 / 5) * Real.sqrt r + 44709 / (5000 * Real.sqrt r) + 1305077 / (500000 * r) := by
    dsimp only [W]
    exact hW
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    rw [hh]
    positivity
  have hmu : m ≤ (4 / 3) * t := by
    calc
      m = u * t := huMul.symm
      _ ≤ (4 / 3) * t := mul_le_mul_of_nonneg_right hu' ht.le
  have hMW : m * W ≤ t * ((4 / 3) * W) := by
    calc
      _ ≤ ((4 / 3) * t) * W := mul_le_mul_of_nonneg_right hmu hW0
      _ = _ := by ring
  have hTW := mul_le_mul_of_nonneg_left hW' ht.le
  have hthree : 3 ≤ t := by
    have hiR : 4 ≤ m := by
      dsimp only [m]; exact Nat.cast_le.mpr hi
    dsimp only [t]
    linarith only [hiR]
  have h13 : (13 : ℝ) ≤ t * (13 / 3) := by nlinarith only [hthree]
  have hcmp' :
    (m * (1 - h) * I - E) * r ≤
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H + m * W + 13 +
        t * LLS.PaperStatements.gaussianAmbientError n (r ^ 2) := by
    rw [hsqrtx] at hcmp
    change _ ≤ _ at hcmp
    simpa only [m, t, I, E, W] using hcmp
  have hright :
    (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H + m * W + 13 +
        t * LLS.PaperStatements.gaussianAmbientError n (r ^ 2) ≤
      t *
        ((161 / 400 : ℝ) * L + (2 / 5) * Real.sqrt r + 44709 / (5000 * Real.sqrt r) +
          1305077 / (500000 * r) +
          13 / 3 +
          LLS.PaperStatements.gaussianAmbientError n (r ^ 2)) := by
    have hsum :
      (161 / 400 : ℝ) * LLS.PaperStatements.subgroupConductorLogSum H ≤
        t * ((161 / 400 : ℝ) * L) := by
      calc
        _ ≤ (161 / 400 : ℝ) * (((H.index : ℝ) - 1) * Real.log n) := hcond'
        _ = t * ((161 / 400 : ℝ) * L) := by
          rw [show (H.index : ℝ) - 1 = t by rfl, show Real.log n = L by rfl]
          ring
    nlinarith only [hsum, hMW, hTW, h13]
  have htargetScaled :
    t * ((21943 / 30000 : ℝ) * r - (4 / 9 * (8147 / 10000)) * Real.sqrt r) ≤
      t *
        ((161 / 400 : ℝ) * L + (2 / 5) * Real.sqrt r + 44709 / (5000 * Real.sqrt r) +
          1305077 / (500000 * r) +
          13 / 3 +
          LLS.PaperStatements.gaussianAmbientError n (r ^ 2)) :=
    hleft.trans (hcmp'.trans hright)
  have htarget := le_of_mul_le_mul_left htargetScaled ht
  have hbeta : 4 / 9 * (8147 / 10000) + 2 / 5 = 17147 / 22500 := by norm_num only
  have hfinal :
    (21943 / 30000 : ℝ) * r ≤
      (161 / 400 : ℝ) * L + (17147 / 22500 : ℝ) * Real.sqrt r + 44709 / (5000 * Real.sqrt r) +
        1305077 / (500000 * r) +
        13 / 3 +
        LLS.PaperStatements.gaussianAmbientError n (r ^ 2) := by
    nlinarith only [htarget, hbeta]
  have hL' : 4000 ≤ L := by
    dsimp only [L]; exact hL
  exact Analysis.gaussianMRVariable_comparison_impossible_of_ambient hL' (le_refl L) hfinal

/-- Under GRH, a subgroup of index at least four yields a prime strong
Miller--Rabin witness below the variable Gaussian cutoff. Assume every prime
base below the cutoff passes and every such nondivisor lies in the subgroup;
the relative Gaussian comparison then contradicts the numerical estimate. -/
theorem exists_prime_witness_le_gaussian_variable_of_index_ge_four {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : 4 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 4000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * (Analysis.gaussianMRVariableRadius (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  let L := Real.log n
  let r := Analysis.gaussianMRVariableRadius L
  let x := r ^ 2
  let h := 1 / (3 * Real.sqrt r)
  have hcut :
    (21 / 10 : ℝ) * x = (21 / 10 : ℝ) * (Analysis.gaussianMRVariableRadius (Real.log n)) ^ 2 := by
    dsimp only [x, r, L]
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (21 / 10 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hbound
    rw [hcut] at hbound
    by_contra hfail
    exact hnone ⟨p, hp, hbound, hfail⟩
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ n → ⌊(21 / 10 : ℝ) * x⌋₊ < p := by
    intro p hp hpdvd
    apply lt_of_not_ge
    intro hfloor
    have hbound : (p : ℝ) ≤ (21 / 10 : ℝ) * x := (Nat.le_floor_iff' hp.ne_zero).mp hfloor
    have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
    exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn1 hnOdd hp hpdvd (hpass p hp hbound)
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n → (p : ℝ) ≤ (21 / 10 : ℝ) * x → LLS.PaperStatements.residueInSubgroup n H p := by
    intro p hp hpdvd hbound
    obtain ⟨u, huH, hu⟩ := hHpass (p : ZMod n) (hpass p hp hbound)
    exact ⟨u, huH, hu⟩
  have hs20 : 20 ≤ Real.sqrt r := by
    dsimp only [r, L]
    exact Analysis.gaussianMRVariableRadius_sqrt_lower hL
  have hwidth : 0 < h := by
    dsimp only [h]; positivity
  have hwidth1 : h ≤ 1 / 2 := by
    dsimp only [h]
    apply one_div_le_one_div_of_le (by norm_num only)
    nlinarith only [hs20]
  have hr2000 : 2000 ≤ r := by
    dsimp only [r, L]
    have hrad := Analysis.gaussianMRVariableRadius_half hL
    have hLhalf : 2000 ≤ Real.log n / 2 := by linarith only [hL]
    dsimp only [Analysis.gaussianMRVariableRadius] at hrad ⊢
    exact hLhalf.trans hrad
  have hx : 4 ≤ x := by
    dsimp only [x]
    nlinarith only [hr2000]
  have hcmp :=
    LLS.PaperStatements.gaussian_noSmallPrimes_inequality_relative hnlarge H hGRH hwidth hwidth1 hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hdiv hsmall
  exact (gaussian_variable_relative_inequality_contradiction H hi hL) hcmp

/-- Under GRH, every odd composite with logarithm at least 4000 has a prime
strong Miller--Rabin witness below the variable Gaussian cutoff. The arithmetic
pass subgroup has index at least four; the threshold excludes modulus 9. -/
theorem exists_prime_witness_le_gaussian_variable {n : ℕ} (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 4000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * (Analysis.gaussianMRVariableRadius (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn0 : n ≠ 0 := by
    intro hz
    rw [hz, Nat.cast_zero, Real.log_zero] at hL
    norm_num only at hL
  have hExp10 : (11 : ℝ) ≤ Real.exp 10 := by
    have h := Real.add_one_le_exp (10 : ℝ)
    norm_num only at h
    exact h
  have hExp4000 : 20000 < Real.exp (4000 : ℝ) := by
    have hpow : (11 : ℝ) ^ 5 ≤ Real.exp 10 ^ 400 := by
      calc
        (11 : ℝ) ^ 5 ≤ (11 : ℝ) ^ 400 := by
          exact pow_le_pow_right₀ (by norm_num only) (by norm_num only)
        _ ≤ Real.exp 10 ^ 400 := pow_le_pow_left₀ (by norm_num only) hExp10 400
    have hexp : Real.exp (4000 : ℝ) = Real.exp 10 ^ 400 := by
      rw [show (4000 : ℝ) = (400 : ℕ) * 10 by norm_num only]
      exact Real.exp_nat_mul 10 400
    rw [hexp]
    exact lt_of_lt_of_le (by norm_num only) hpow
  have hlog20000 : Real.log (20000 : ℝ) < 4000 :=
    (Real.log_lt_iff_lt_exp (by norm_num only)).2 hExp4000
  have hnlarge : 20000 ≤ n := by
    by_contra hnot
    have hnlt : n < 20000 := Nat.lt_of_not_ge hnot
    have hloglt : Real.log (n : ℝ) < Real.log (20000 : ℝ) :=
      Real.log_lt_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)) (Nat.cast_lt.mpr hnlt)
    exact (not_lt_of_ge hL) (hloglt.trans hlog20000)
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hn9 : n ≠ 9 := by
    intro h
    rw [h] at hnlarge
    exact (by decide : ¬20000 ≤ 9) hnlarge
  obtain ⟨H, hi, hHpass⟩ :=
    PrimeTest.exists_index_ge_four_subgroup_containing_strongMillerRabinPass hn1 hnOdd hnComposite
      hn9
  exact exists_prime_witness_le_gaussian_variable_of_index_ge_four hnOdd hnlarge H hi hHpass hGRH hL

/-- The least prime rejecting the strong test inherits the variable Gaussian
cutoff from the explicit witness theorem. -/
theorem exists_least_prime_witness_le_gaussian_variable {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 4000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * (Analysis.gaussianMRVariableRadius (Real.log n)) ^ 2 ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hpbound, hreject⟩ :=
    exists_prime_witness_le_gaussian_variable hnOdd hnComposite hGRH hL
  have hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hpbound, fun q hq hqReject ↦
      Nat.find_min' hex ⟨hq, hqReject⟩⟩

/-- For `L ≥ 4000`, the new Gaussian cutoff is strictly below the index-four
cutoff. Combine the `7/10 L^2` estimate with the index-four leading term. -/
theorem gaussian_variable_cutoff_lt_index_four {L : ℝ} (hL : 4000 ≤ L) :
    (21 / 10 : ℝ) * (Analysis.gaussianMRVariableRadius L) ^ 2 <
      (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 := by
  have hBG := Analysis.gaussianMRVariable_cutoff_lt_seven_tenths hL
  have hB4 : (7 / 10 : ℝ) * L ^ 2 ≤ (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 := by
    nlinarith only [hL]
  exact lt_of_lt_of_le hBG hB4

/-- The classified Gaussian bound is strictly below the index-four Gamma
bound throughout its full range beginning at logarithmic scale 600. -/
theorem gaussian_star_cutoff_lt_index_four {L : ℝ} (hL : 600 ≤ L) :
    Analysis.gaussianMRStarBound L < (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 := by
  have hstar := Analysis.gaussianMRStarBound_lt_seven_tenths hL
  have hB4 : (7 / 10 : ℝ) * L ^ 2 ≤ (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 := by
    nlinarith only [hL]
  exact lt_of_lt_of_le hstar hB4

/-- For positive `L`, the coefficient bound is strictly below the variable-width
Gaussian bound. The radius lower bound `5503 L / 10000` gives a quadratic
coefficient larger than `282924 / 1000000`. -/
theorem gaussian_variable_cutoff_gt_triangular_coefficient {L : ℝ} (hL : 0 < L) :
    (282924 / 1000000 : ℝ) * L ^ 2 < (21 / 10 : ℝ) * (Analysis.gaussianMRVariableRadius L) ^ 2 := by
  have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hr : (5503 / 10000 : ℝ) * L ≤ Analysis.gaussianMRVariableRadius L := by
    dsimp only [Analysis.gaussianMRVariableRadius]
    nlinarith only [hs]
  have hb : 0 ≤ (5503 / 10000 : ℝ) * L := mul_nonneg (by norm_num only) (le_of_lt hL)
  have hsq : ((5503 / 10000 : ℝ) * L) ^ 2 ≤ (Analysis.gaussianMRVariableRadius L) ^ 2 := by
    nlinarith only [hr, hb]
  have hc : (282924 / 1000000 : ℝ) < (21 / 10 : ℝ) * (5503 / 10000 : ℝ) ^ 2 := by norm_num only
  have hp := mul_lt_mul_of_pos_right hc (sq_pos_of_pos hL)
  have hscale : ((5503 / 10000 : ℝ) * L) ^ 2 = (5503 / 10000 : ℝ) ^ 2 * L ^ 2 := by ring
  calc
    (282924 / 1000000 : ℝ) * L ^ 2 < (21 / 10 : ℝ) * ((5503 / 10000 : ℝ) * L) ^ 2 := by
      nlinarith only [hp, hscale]
    _ ≤ (21 / 10 : ℝ) * (Analysis.gaussianMRVariableRadius L) ^ 2 := by nlinarith only [hsq]

end PseudoPrime.PrimeTestBounds.MillerRabin
