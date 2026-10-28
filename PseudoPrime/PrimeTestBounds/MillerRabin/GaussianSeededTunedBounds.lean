/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianSeededTuned
public import PseudoPrime.LLS.GammaSeedLogMoment
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBudgetBranches
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBudgetFour

/-! # Actual tuned seeded Gaussian witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH each unchanged finite prefix has the tuned credit certified by its actual sum. -/
theorem seededTuned_prefix (f : Bool)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    Analysis.gaussianSeededTunedPrefix f ≤
      ∑ j ∈ Finset.Ioc 0 (Analysis.gaussianSeededSharpCutoff f),
        Analysis.gaussianResolventMangoldtWeight j := by
  cases f
  · simpa only [Analysis.gaussianSeededTunedPrefix, Analysis.gaussianSeededSharpCutoff,
      Bool.false_eq_true, ite_false, Nat.floor_ofNat] using
      LLS.gaussian_prefix35000_moment hGRH.riemann (le_refl (35000 : ℝ))
  · simpa only [Analysis.gaussianSeededTunedPrefix, Analysis.gaussianSeededSharpCutoff, ite_true,
      Nat.floor_ofNat] using LLS.gaussian_prefix50000_moment hGRH.riemann (le_refl (50000 : ℝ))

/-- For each tuned prefix profile, the large-index generic consumer yields an actual
rejecting prime; use the actual prefix, clipped budget and strict residual certificate. -/
theorem seededTuned_large (f : Bool) {n : ℕ} [NeZero n] (ho : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ))
    (hp :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianSeededTunedBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have h0 : (0 : ℝ) ≤ Real.log n := by linarith only [hL]
  apply
    gaussianBudget_large_witness (Analysis.gaussianSeededSharpCutoff f)
      (Analysis.gaussianSeededTunedPrefix f) (Analysis.gaussianSeededTunedConstant f)
      (Analysis.gaussianSeededTunedRoot f (Real.log n))
      ((by norm_num only : (91 / 10 : ℝ) ≤ 13).trans (Analysis.gaussianSeededTuned_root13 f _))
      (Analysis.gaussianSeededTuned_budget f h0) (seededTuned_prefix f hGRH)
      (Analysis.gaussianSeededTuned_cutoff_le f _) _ ho hnlarge H hi hp hGRH
  intro m hm
  exact Analysis.gaussianSeededTuned_residual f h0 hm (le_refl (Real.log n))

/-- The normalized index-four error and main margin close the generic actual witness rule
for each tuned profile without any public factorization hypothesis. -/
theorem seededTuned_four (f : Bool) {n : ℕ} [NeZero n] (ho : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hi : H.index = 4)
    (hp :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianSeededTunedBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have h0 : (0 : ℝ) ≤ Real.log n := by linarith only [hL]
  exact
    gaussianBudget_four_witness (Analysis.gaussianSeededSharpCutoff f)
      (Analysis.gaussianSeededTunedPrefix f) (Analysis.gaussianSeededTunedRoot f (Real.log n))
      (Analysis.gaussianSeededTuned_root13 f _) (seededTuned_prefix f hGRH)
      (Analysis.gaussianSeededTuned_cutoff_le f _)
      (Analysis.gaussianSeededTuned_four_error f h0 (le_refl (Real.log n)))
      (Analysis.gaussianSeededTuned_four_absurd f h0) ho hnlarge H hi hp hGRH hC

/-- For positive local conductor q with q squared at most 10^9 n, the local bound
fits each tuned seeded cutoff above logarithmic scale 63. -/
theorem seededTuned_local (f : Bool) {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hsize : q ^ 2 ≤ 10 ^ 9 * n) (hL : 63 ≤ Real.log n) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤ Analysis.gaussianSeededTunedBound f (Real.log n) := by
  have hlog := Analysis.mr_local_log_le_of_square_le hn hq hsize
  have hcap : Real.log q ≤ (2 / 3 : ℝ) * Real.log n := by
    linarith only [hlog, hL, Analysis.log_ten_lt_seven_thirds]
  have hpos : (0 : ℝ) ≤ (2 / 3) * Real.log n := by linarith only [hL]
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg q) hpos).mpr hcap
  have hw := Analysis.gaussianSeededTuned_bound_lower (f := f) hL
  have hc := Analysis.gaussianSeededTuned_cutoff_le f (Real.log n)
  have hcut : (3000 : ℝ) ≤ (Analysis.gaussianSeededSharpCutoff f : ℝ) := by
    cases f <;>
      norm_num only [Analysis.gaussianSeededSharpCutoff, Bool.false_eq_true, ite_false, ite_true,
        Nat.cast_ofNat]
  exact max_le (hcut.trans hc) (by nlinarith only [hs, hw, sq_nonneg (Real.log n)])

/-- Under GRH each odd composite at logarithmic scale at least 63 has a prime
rejecting strong MR below the tuned profile cutoff. The shared classification
closes the large, local and uniform triple branches internally. -/
theorem exists_prime_seededTuned (f : Bool) {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianSeededTunedBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  have hnlarge : 20000 ≤ n :=
    (by norm_num only : 20000 ≤ 10 ^ 27).trans (gaussian35000_size ho.pos hL)
  exact
    exists_prime_gaussianBudget ho hc hGRH hL
      (fun H hi hp ↦ seededTuned_large f ho hnlarge H hi hp hGRH hL)
      (fun H hi hp hC ↦ seededTuned_four f ho hnlarge H hi hp hGRH hC hL)
      (fun q hq hs ↦ seededTuned_local f ho.pos hq hs hL)

/-- Minimality transfers the actual tuned witness bound to the least rejecting prime. -/
theorem exists_least_seededTuned (f : Bool) {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ Analysis.gaussianSeededTunedBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  exact exists_least_prime_reject_of_exists_prime_reject (exists_prime_seededTuned f ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
