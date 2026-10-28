/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianTunedProfiles
public import PseudoPrime.LLS.GammaSeedLogMoment
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBudgetBranches

/-! # Actual tuned Gaussian witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every profile cutoff exceeds the common floor needed to cover the 1000 prefix. -/
theorem gaussianTuned_cutoff_floor (f : Analysis.GaussianTunedProfile) (L : ℝ) :
    (6 / 5 : ℝ) * ((91 / 10) ^ 2) ^ 2 ≤ f.bound L := by
  have hr := f.radius_floor L
  have hs := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ (91 / 10) ^ 2) (sq_nonneg (f.root L))).mpr hr
  exact mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- Above logarithmic scale 63, each cutoff exceeds 15 L squared/32.
The linear radius bound covers all local subgroup witness bounds. -/
theorem gaussianTuned_bound_lower (f : Analysis.GaussianTunedProfile) {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < f.bound L := by
  have hr := f.radius_linear hL
  have hpos : (0 : ℝ) ≤ (5 / 8) * L := by linarith only [hL]
  have hs := (sq_lt_sq₀ hpos (hpos.trans hr.le)).mpr hr
  change _ < (6 / 5 : ℝ) * f.radius L ^ 2
  nlinarith only [hs]

/-- The old prefix supports low and bridge; the actual moment prefix supports
middle and upper. Each bound applies to the original finite resolvent sum. -/
theorem gaussianTuned_prefix (f : Analysis.GaussianTunedProfile)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    f.prefixValue ≤ ∑ j ∈ Finset.Ioc 0 1000, Analysis.gaussianResolventMangoldtWeight j := by
  cases f
  · simpa only [Analysis.GaussianTunedProfile.prefixValue, Nat.floor_ofNat] using
      LLS.gaussian_prefix1000_recovered hGRH.riemann (le_refl (1000 : ℝ))
  · simpa only [Analysis.GaussianTunedProfile.prefixValue, Nat.floor_ofNat] using
      LLS.gaussian_prefix1000_recovered hGRH.riemann (le_refl (1000 : ℝ))
  · simpa only [Analysis.GaussianTunedProfile.prefixValue, Nat.floor_ofNat] using
      LLS.gaussian_prefix1000_moment hGRH.riemann (le_refl (1000 : ℝ))
  · simpa only [Analysis.GaussianTunedProfile.prefixValue, Nat.floor_ofNat] using
      LLS.gaussian_prefix1000_moment hGRH.riemann (le_refl (1000 : ℝ))

/-- The generic large-index consumer, actual prefix and new profile budget
yield a rejecting prime under the tuned cutoff for every sufficiently large index. -/
theorem gaussianTuned_witness_large (f : Analysis.GaussianTunedProfile) {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ)
    (hi : Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ))
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound (Real.log n) ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have h0 : (0 : ℝ) ≤ Real.log n := by linarith only [hL]
  apply
    gaussianBudget_large_witness 1000 f.prefixValue f.residual (f.root (Real.log n))
      (f.signs.1.trans (f.root_floor _)) (f.budget h0) (gaussianTuned_prefix f hGRH)
      ((by norm_num only : (1000 : ℝ) ≤ (6 / 5) * ((91 / 10) ^ 2) ^ 2).trans
        (gaussianTuned_cutoff_floor f _))
      _ hnOdd hnlarge H hi hHpass hGRH
  intro m hm
  exact
    Analysis.gaussianLow_index_error (f.root_pos _) (sq_pos_of_pos (f.root_pos _)) hm
      (f.large_cap (f.root_floor _) (f.budget h0) (le_refl (Real.log n)))

/-- Under GRH, an index-four pass-containing subgroup with conductor at most
2 log n has an actual rejecting prime below the tuned single-root cutoff. Scale the comparison
radius by 7559/10000 while retaining width k/s. Both the strict residual and the main-term
budgets use 204/5. -/
theorem gaussianTuned_witness_four (f : Analysis.GaussianTunedProfile) {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound (Real.log n) ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let L := Real.log n
  let r := f.radius L
  let s := f.root L
  let x := ((7559 / 10000 : ℝ) * r) ^ 2
  let h := (2 / 5 : ℝ) / s
  have hr100 : ((91 / 10 : ℝ) ^ 2) ≤ r := f.radius_floor L
  have hs10 : (91 / 10 : ℝ) ≤ s := f.signs.1.trans (f.root_floor L)
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
  have hcut : (21 / 10 : ℝ) * x ≤ f.bound (Real.log n) := by
    change (21 / 10 : ℝ) * (((7559 / 10000 : ℝ) * r) ^ 2) ≤ (6 / 5 : ℝ) * r ^ 2
    nlinarith only [sq_nonneg r]
  have prefixActual :
    f.prefixValue ≤ ∑ j ∈ Finset.Ioc 0 1000, Analysis.gaussianResolventMangoldtWeight j :=
    gaussianTuned_prefix f hGRH
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
      Analysis.gaussianMRRefinedConductor * LLS.PaperStatements.subgroupConductorLogSum H +
        4 *
          (1 / (10 * h) +
            ((21 / (10 * h) + 1839 / 1000) / ((7559 / 10000 : ℝ) * r)) * Real.exp (1 / 16 : ℝ)) +
        13 +
        3 *
          LLS.PaperStatements.gaussianPrefixError f.prefixValue n
            (((7559 / 10000 : ℝ) * r) ^ 2) := by
    simpa only [hindex, hi, Nat.reduceSub, Nat.cast_ofNat] using hcmp
  have hscalar :=
    Analysis.gaussianRelativeFour_scalar hspos hs2 (by norm_num only : (0 : ℝ) < 7559 / 10000)
      (by norm_num only : (0 : ℝ) < 2 / 5) (show h = (2 / 5 : ℝ) / s from rfl) hh1
      LLS.PaperStatements.gaussianGamma_cutoff_gt_target.le Analysis.gaussian_endpoint_exp_le hC
      (by norm_num only [Analysis.gaussianMRRefinedConductor]) hcmp'
  have hG := f.budget (show 0 ≤ L by linarith only [hL])
  have herror := f.four_error (f.root_floor L) hG (le_refl (Real.log n))
  have hmargin := f.four_margin (f.root_floor L)
  norm_num only [Analysis.gaussianMRRefinedConductor, Analysis.gaussianMR6FifthsEndpoint,
    Analysis.gaussianMRRefinedWidth] at hscalar hG herror hmargin
  rw [hs2] at hscalar
  dsimp only [s, r, L, Analysis.GaussianTunedProfile.radius] at hscalar hG herror hmargin
  nlinarith only [hscalar, hG, herror, hmargin]

/-- For log n>=63 and q squared<=10^9*n, the local subgroup cutoff fits
the recovered-prefix single-root bound. Combine log q<=2 log n/3, the common profile floor and
the quadratic lower bound; keep the ambient passing-residue containment upstream. -/
theorem gaussianTuned_local (f : Analysis.GaussianTunedProfile) {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hsize : q ^ 2 ≤ 10 ^ 9 * n) (hL : 63 ≤ Real.log n) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤ f.bound (Real.log n) := by
  have hlog := Analysis.mr_local_log_le_of_square_le hn hq hsize
  have hcap : Real.log q ≤ (2 / 3 : ℝ) * Real.log n := by
    linarith only [hlog, hL, Analysis.log_ten_lt_seven_thirds]
  have hpos : (0 : ℝ) ≤ (2 / 3) * Real.log n := by linarith only [hL]
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg q) hpos).mpr hcap
  have hwide := gaussianTuned_bound_lower f hL
  have hcut := gaussianTuned_cutoff_floor f (Real.log n)
  exact max_le (by linarith only [hcut]) (by nlinarith only [hs, hwide, sq_nonneg (Real.log n)])

/-- Under GRH and log n at least 63, every odd composite has a rejecting prime
under the profile cutoff. Reuse the shared large/local/uniform-triple classification. -/
theorem exists_prime_gaussianTuned (f : Analysis.GaussianTunedProfile) {n : ℕ} (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound (Real.log n) ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  have hN := gaussian35000_size ho.pos hL
  have hnlarge : 20000 ≤ n := (by norm_num only : 20000 ≤ 10 ^ 27).trans hN
  apply exists_prime_gaussianBudget ho hc hGRH hL
  · intro H hi hp
    exact gaussianTuned_witness_large f ho hnlarge H hi hp hGRH hL
  · intro H hi hp hC
    exact gaussianTuned_witness_four f ho hnlarge H hi hp hGRH hC hL
  · intro q hq hs
    exact gaussianTuned_local f ho.pos hq hs hL

/-- Extract the least rejecting prime from the all-input actual witness and
preserve the tuned profile cutoff without factorization assumptions. -/
theorem exists_least_gaussianTuned (f : Analysis.GaussianTunedProfile) {n : ℕ} (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (exists_prime_gaussianTuned f ho hc hGRH hL)

/-- A common least rejecting prime lies below all four profile cutoffs.
Minimality transfers each independently certified witness bound to the same prime. -/
theorem exists_least_gaussianTunedFamily {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianTunedFamily (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hb, hr, hl⟩ := exists_least_gaussianTuned .low ho hc hGRH hL
  obtain ⟨q0, hq0, hqb0, hqr0⟩ := exists_prime_gaussianTuned .bridge ho hc hGRH hL
  have h0 : (p : ℝ) ≤ Analysis.GaussianTunedProfile.bridge.bound (Real.log n) :=
    (Nat.cast_le.mpr (hl q0 hq0 hqr0)).trans hqb0
  obtain ⟨q1, hq1, hqb1, hqr1⟩ := exists_prime_gaussianTuned .middle ho hc hGRH hL
  have h1 : (p : ℝ) ≤ Analysis.GaussianTunedProfile.middle.bound (Real.log n) :=
    (Nat.cast_le.mpr (hl q1 hq1 hqr1)).trans hqb1
  obtain ⟨q2, hq2, hqb2, hqr2⟩ := exists_prime_gaussianTuned .upper ho hc hGRH hL
  have h2 : (p : ℝ) ≤ Analysis.GaussianTunedProfile.upper.bound (Real.log n) :=
    (Nat.cast_le.mpr (hl q2 hq2 hqr2)).trans hqb2
  exact ⟨p, hp, le_min hb (le_min h0 (le_min h1 h2)), hr, hl⟩

/-- The four-profile family contains an actual rejecting prime for every
odd composite under GRH with log n at least 63. -/
theorem exists_prime_gaussianTunedFamily {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianTunedFamily (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  (exists_least_gaussianTunedFamily ho hc hGRH hL).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

/-- A common least rejecting prime lies below both existing-prefix profiles.
This supplies the early low/bridge family independently of the moment certificate. -/
theorem exists_least_gaussianTunedEarlyFamily {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianTunedEarlyFamily (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hb, hr, hl⟩ := exists_least_gaussianTuned .low ho hc hGRH hL
  obtain ⟨q0, hq0, hqb0, hqr0⟩ := exists_prime_gaussianTuned .bridge ho hc hGRH hL
  have h0 : (p : ℝ) ≤ Analysis.GaussianTunedProfile.bridge.bound (Real.log n) :=
    (Nat.cast_le.mpr (hl q0 hq0 hqr0)).trans hqb0
  exact ⟨p, hp, le_min hb h0, hr, hl⟩

/-- The early low/bridge family contains an actual rejecting prime under
the same all-input assumptions, by its least-witness theorem. -/
theorem exists_prime_gaussianTunedEarlyFamily {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianTunedEarlyFamily (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  (exists_least_gaussianTunedEarlyFamily ho hc hGRH hL).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
