/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianTightNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusBounds

/-! # Actual MR witnesses for Gaussian candidate A

The same actual thousand-term prefix and existing tail certificates support residual 7.2.
Large-index, scaled index-four and local branches are closed before the all-input entrance.
GRH supplies the prefix internally; no scalar-gap or prefix assumption is exposed there.
This witness leaf has no cumulative-history dependency.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd inputs and a sufficiently large subgroup index, candidate A contains a rejecting prime.
Use the actual GRH prefix, residual-7.2 cap and the existing index-error monotonicity.
This supplies the large-index branch of the complete witness theorem. -/
theorem gaussianTight_witness_large {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : gaussian6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianTightBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have h0 : (0 : ℝ) ≤ Real.log n := by linarith only [hL]
  apply
    gaussianBudget_large_witness 1000 gaussianSurplusPrefix (36 / 5 : ℝ)
      (gaussianTightRoot (Real.log n)) (gaussianTight_root_floor _) (gaussianTight_budget h0)
      (gaussianSurplus_prefix hGRH)
      ((by norm_num only : (1000 : ℝ) ≤ (6 / 5) * ((91 / 10) ^ 2) ^ 2).trans
        (gaussianTight_cutoff_floor _))
      _ hnOdd hnlarge H hi hHpass hGRH
  intro m hm
  exact
    gaussianLow_index_error (gaussianTight_root_pos _) (sq_pos_of_pos (gaussianTight_root_pos _)) hm
      (gaussianTight_large_cap (gaussianTight_root_floor _) (gaussianTight_budget h0)
        (le_refl (Real.log n)))

/-- For index four and conductor cost at most twice log n, candidate A contains a rejecting prime.
The actual scaled comparison contradicts the tighter budget, error below 36.63 and main
margin above 36.63. This keeps both sides of the index-four threshold consistent. -/
theorem gaussianTight_witness_four {n : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianTightBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let L := Real.log n
  let r := gaussianTightRadius L
  let s := gaussianTightRoot L
  let x := ((7559 / 10000 : ℝ) * r) ^ 2
  let h := (2 / 5 : ℝ) / s
  have hr100 : ((91 / 10 : ℝ) ^ 2) ≤ r := gaussianTight_radius_floor L
  have hs10 : (91 / 10 : ℝ) ≤ s := gaussianTight_root_floor L
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
  have hcut : (21 / 10 : ℝ) * x ≤ gaussianTightBound (Real.log n) := by
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
  have hG := gaussianTight_budget (show 0 ≤ L by linarith only [hL])
  have herror := gaussianTight_four_error (gaussianTight_root_floor L) hG (le_refl (Real.log n))
  have hmargin := gaussianTight_four_margin (gaussianTight_root_floor L)
  norm_num only [gaussianMRRefinedConductor, gaussian6FifthsEndpoint,
    gaussianMRRefinedWidth] at hscalar hG herror hmargin
  rw [hs2] at hscalar
  dsimp only [s, r, L, gaussianTightRadius] at hscalar hG herror hmargin
  nlinarith only [hscalar, hG, herror, hmargin]

/-- For positive local q with q squared at most one billion times n, candidate A covers
the local cap.
Use the logarithmic size estimate and the tighter quadratic lower bound.
This supplies the remaining local branch without new finite input checks. -/
theorem gaussianTight_local {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (hsize : q ^ 2 ≤ 10 ^ 9 * n)
    (hL : 63 ≤ Real.log n) : max (3000 : ℝ) (Real.log q ^ 2) ≤ gaussianTightBound (Real.log n) := by
  have hlog := local_log_le_of_square_le hn hq hsize
  have hcap : Real.log q ≤ (2 / 3 : ℝ) * Real.log n := by
    linarith only [hlog, hL, log_ten_lt_seven_thirds]
  have hpos : (0 : ℝ) ≤ (2 / 3) * Real.log n := by linarith only [hL]
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg q) hpos).mpr hcap
  have hwide := gaussianTight_bound_lower (le_trans (by norm_num only : (0 : ℝ) ≤ 63) hL)
  have hcut := gaussianTight_cutoff_floor (Real.log n)
  exact max_le (by linarith only [hcut]) (by nlinarith only [hs, hwide, sq_nonneg (Real.log n)])

/-- Under GRH, every odd composite at log scale at least 63 has an actual rejecting prime below A.
Combine the large-index, index-four and local branches through the established classifier.
The actual prefix and all scalar certificates are supplied internally. -/
theorem exists_prime_gaussianTight {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianTightBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  have hN := gaussian35000_size ho.pos hL
  have hnlarge : 20000 ≤ n := (by norm_num only : 20000 ≤ 10 ^ 27).trans hN
  apply exists_prime_gaussianBudget ho hc hGRH hL
  · intro H hi hp
    exact gaussianTight_witness_large ho hnlarge H hi hp hGRH hL
  · intro H hi hp hC
    exact gaussianTight_witness_four ho hnlarge H hi hp hGRH hC hL
  · intro q hq hs
    exact gaussianTight_local ho.pos hq hs hL

/-- Under GRH, candidate A contains a least rejecting prime for every odd composite above entrance.
Apply leastness to the actual witness theorem; no extra prefix or scalar premise remains. -/
theorem exists_least_gaussianTight {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianTightBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  exact exists_least_prime_reject_of_exists_prime_reject (exists_prime_gaussianTight ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
