/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianPrefix1000Surplus
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBudgetBranches

/-! # Actual MR witnesses from the stronger thousand-term Gaussian prefix

This leaf closes the large-index, scaled index-four and local branches for the single
surplus candidate. GRH supplies the actual prefix internally, so no prefix or scalar-gap
hypothesis remains at the all-input witness entrance. Finite certificate data is unchanged.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the stronger credit bounds the actual thousand-term Gaussian prefix.
Input: GRH. Claim: the exact prefix lower bound needed by all candidate branches.
Proof: apply the new LLS prefix leaf to the Riemann component of GRH.
Role: discharge the prefix assumption internally at the MR witness entrance. -/
theorem gaussianSurplus_prefix (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    gaussianSurplusPrefix ≤
      ∑ j ∈ Finset.Ioc 0 1000, Analysis.gaussianResolventMangoldtWeight j := by
  simpa only [gaussianSurplusPrefix, Nat.floor_ofNat] using
    LLS.gaussian_prefix1000_surplus hGRH.riemann (le_refl (1000 : ℝ))

/-- For odd composite inputs, the stronger prefix closes the large-index witness branch.
GRH supplies the prefix; the residual cap and index monotonicity give the rejecting prime. -/
theorem gaussianSurplus_witness_large {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : gaussian6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianSurplusBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have h0 : (0 : ℝ) ≤ Real.log n := by linarith only [hL]
  apply
    gaussianBudget_large_witness 1000 gaussianSurplusPrefix (38 / 5 : ℝ)
      (gaussianSurplusRoot (Real.log n)) (gaussianSurplus_root_floor _) (gaussianSurplus_budget h0)
      (gaussianSurplus_prefix hGRH)
      ((by norm_num only : (1000 : ℝ) ≤ (6 / 5) * ((91 / 10) ^ 2) ^ 2).trans
        (gaussianSurplus_cutoff_floor _))
      _ hnOdd hnlarge H hi hHpass hGRH
  intro m hm
  exact
    gaussianLow_index_error (gaussianSurplus_root_pos _)
      (sq_pos_of_pos (gaussianSurplus_root_pos _)) hm
      (gaussianSurplus_large_cap (gaussianSurplus_root_floor _) (gaussianSurplus_budget h0)
        (le_refl (Real.log n)))

/-- For the index-four subgroup with conductor at most twice log n, produce a rejecting prime.
The scaled relative inequality contradicts the certified scalar error and margin. -/
theorem gaussianSurplus_witness_four {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianSurplusBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let L := Real.log n
  let r := gaussianSurplusRadius L
  let s := gaussianSurplusRoot L
  let x := ((7559 / 10000 : ℝ) * r) ^ 2
  let h := (2 / 5 : ℝ) / s
  have hr100 : ((91 / 10 : ℝ) ^ 2) ≤ r := gaussianSurplus_radius_floor L
  have hs10 : (91 / 10 : ℝ) ≤ s := gaussianSurplus_root_floor L
  have hrpos : 0 < r := by linarith only [hr100]
  have hspos : 0 < s := by linarith only [hs10]
  have hs2 : r = s ^ 2 := rfl
  have hscaled : 0 ≤ (7559 / 10000 : ℝ) * r := by linarith only [hr100]
  have hh : 0 < h := div_pos (by norm_num only) hspos
  have hh1 : h ≤ 1 / 2 := by
    apply (div_le_iff₀ hspos).mpr
    linarith only [hs10]
  have hx : 4 ≤ x := by
    dsimp only [x]; nlinarith only [hr100]
  have hX : (1000 : ℝ) ≤ (21 / 10 : ℝ) * x := by
    dsimp only [x]
    nlinarith only [hr100]
  have hcut : (21 / 10 : ℝ) * x ≤ gaussianSurplusBound (Real.log n) := by
    change (21 / 10 : ℝ) * (((7559 / 10000 : ℝ) * r) ^ 2) ≤ (6 / 5 : ℝ) * r ^ 2
    nlinarith only [sq_nonneg r]
  have prefixActual :
    gaussianSurplusPrefix ≤ ∑ j ∈ Finset.Ioc 0 1000, Analysis.gaussianResolventMangoldtWeight j :=
    gaussianSurplus_prefix hGRH
  apply
    gaussianRelative_witness hnOdd hnlarge H hHpass hGRH prefixActual hh hh1 hx
      (by norm_num only : (0 : ℝ) ≤ 21 / 10) hX hcut
  intro hcmp
  have hindex : (H.index : ℝ) = 4 := by exact_mod_cast hi
  rw [Real.sqrt_sq hscaled] at hcmp
  have hcmp' :
    (4 * (1 - h) *
            (∫ u in (0 : ℝ)..(21 / 10 : ℝ),
              (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
          Real.exp (1 / 16 : ℝ)) *
        ((7559 / 10000 : ℝ) * r) ≤
      gaussianMRRefinedConductor * LLS.PaperStatements.subgroupConductorLogSum H +
        4 *
          (1 / (10 * h) +
            ((21 / (10 * h) + 1839 / 1000) / ((7559 / 10000 : ℝ) * r)) * Real.exp (1 / 16 : ℝ)) +
        13 +
        3 *
          LLS.PaperStatements.gaussianPrefixError gaussianSurplusPrefix n
            (((7559 / 10000 : ℝ) * r) ^ 2) := by
    simpa only [hindex, hi, Nat.reduceSub, Nat.cast_ofNat] using hcmp
  have hscalar :=
    LLS.gaussianRelativeFour_scalar hspos hs2 (by norm_num only : (0 : ℝ) < 7559 / 10000)
      (by norm_num only : (0 : ℝ) < 2 / 5) (show h = (2 / 5 : ℝ) / s from rfl) hh1
      LLS.PaperStatements.gaussianGamma_cutoff_gt_target.le Analysis.gaussian_endpoint_exp_le hC
      (by norm_num only [gaussianMRRefinedConductor]) hcmp'
  have hG := gaussianSurplus_budget (show 0 ≤ L by linarith only [hL])
  have herror := gaussianSurplus_four_error (gaussianSurplus_root_floor L) hG (le_refl (Real.log n))
  have hmargin := gaussianSurplus_four_margin (gaussianSurplus_root_floor L)
  norm_num only [gaussianMRRefinedConductor, gaussian6FifthsEndpoint,
    gaussianMRRefinedWidth] at hscalar hG herror hmargin
  rw [hs2] at hscalar
  dsimp only [s, r, L, gaussianSurplusRadius] at hscalar hG herror hmargin
  nlinarith only [hscalar, hG, herror, hmargin]

/-- For a positive local factor with q squared at most one billion times n, bound its local cutoff.
The logarithmic size estimate and the surplus quadratic lower bound close the local branch. -/
theorem gaussianSurplus_local {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (hsize : q ^ 2 ≤ 10 ^ 9 * n)
    (hL : 63 ≤ Real.log n) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤ gaussianSurplusBound (Real.log n) := by
  have hlog := local_log_le_of_square_le hn hq hsize
  have hcap : Real.log q ≤ (2 / 3 : ℝ) * Real.log n := by
    linarith only [hlog, hL, log_ten_lt_seven_thirds]
  have hpos : (0 : ℝ) ≤ (2 / 3) * Real.log n := by linarith only [hL]
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg q) hpos).mpr hcap
  have hwide := gaussianSurplus_bound_lower (le_trans (by norm_num only : (0 : ℝ) ≤ 63) hL)
  have hcut := gaussianSurplus_cutoff_floor (Real.log n)
  exact max_le (by linarith only [hcut]) (by nlinarith only [hs, hwide, sq_nonneg (Real.log n)])

/-- Under GRH, every odd composite with log n at least 63 has an actual rejecting prime.
The large-index, index-four and local alternatives discharge the generic budget interface. -/
theorem exists_prime_gaussianSurplus {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianSurplusBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  have hN := gaussian35000_size ho.pos hL
  have hnlarge : 20000 ≤ n := (by norm_num only : 20000 ≤ 10 ^ 27).trans hN
  apply exists_prime_gaussianBudget ho hc hGRH hL
  · intro H hi hp
    exact gaussianSurplus_witness_large ho hnlarge H hi hp hGRH hL
  · intro H hi hp hC
    exact gaussianSurplus_witness_four ho hnlarge H hi hp hGRH hC hL
  · intro q hq hs
    exact gaussianSurplus_local ho.pos hq hs hL

/-- Under GRH, the actual surplus cutoff contains a least rejecting prime.
Apply leastness to the actual witness entrance, preserving the same numerical cutoff. -/
theorem exists_least_gaussianSurplus {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianSurplusBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (exists_prime_gaussianSurplus ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
