/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededSurplus
public import PseudoPrime.LLS.GaussianPrefixSurplus
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBudgetBranches
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBudgetFourThreshold

/-! # Actual surplus seeded Gaussian witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For each surplus profile with the supplied actual prefix,
the large-index consumer yields an actual
rejecting prime; use the actual prefix, clipped budget and strict residual certificate. -/
theorem seededSurplus_large (f : Bool)
    (hprefix :
      gaussianSeededSurplusPrefix f ≤
        ∑ j ∈ Finset.Ioc 0 (gaussianSeededSharpCutoff f),
          Analysis.gaussianResolventMangoldtWeight j)
    {n : ℕ} [NeZero n] (ho : Odd n) (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ)
    (hi : Analysis.gaussianMR6FifthsIndex ≤ (H.index : ℝ))
    (hp :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianSeededSurplusBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have h0 : (0 : ℝ) ≤ Real.log n := by linarith only [hL]
  apply
    gaussianBudget_large_witness (gaussianSeededSharpCutoff f)
      (gaussianSeededSurplusPrefix f) (gaussianSeededSurplusConstant f)
      (gaussianSeededSurplusRoot f (Real.log n))
      ((by norm_num only : (91 / 10 : ℝ) ≤ 13).trans (gaussianSeededSurplus_root13 f _))
      (gaussianSeededSurplus_budget f h0) hprefix
      (gaussianSeededSurplus_cutoff_le f _) _ ho hnlarge H hi hp hGRH
  intro m hm
  exact gaussianSeededSurplus_residual f h0 hm (le_refl (Real.log n))

/-- The normalized index-four error and main margin close the generic actual witness rule
for each surplus profile without any public factorization hypothesis. -/
theorem seededSurplus_four (f : Bool)
    (hprefix :
      gaussianSeededSurplusPrefix f ≤
        ∑ j ∈ Finset.Ioc 0 (gaussianSeededSharpCutoff f),
          Analysis.gaussianResolventMangoldtWeight j)
    {n : ℕ} [NeZero n] (ho : Odd n) (hnlarge : 20000 ≤ n) (H : Subgroup (ZMod n)ˣ)
    (hi : H.index = 4)
    (hp :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hC : LLS.PaperStatements.subgroupConductorLogSum H ≤ 2 * Real.log n) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianSeededSurplusBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have h0 : (0 : ℝ) ≤ Real.log n := by linarith only [hL]
  exact
    gaussianBudget_four_witness_threshold (gaussianSeededSharpCutoff f)
      (gaussianSeededSurplusPrefix f) (gaussianSeededSurplusRoot f (Real.log n))
      10 (gaussianSeededSurplus_root13 f _) hprefix
      (gaussianSeededSurplus_cutoff_le f _)
      (gaussianSeededSurplus_four_error f h0 (le_refl (Real.log n)))
      (gaussianSeededSurplus_four_absurd f h0) ho hnlarge H hi hp hGRH hC

/-- For positive local conductor q with q squared at most 10^9 n, the local bound
fits each surplus seeded cutoff above logarithmic scale 63. -/
theorem seededSurplus_local (f : Bool) {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hsize : q ^ 2 ≤ 10 ^ 9 * n) (hL : 63 ≤ Real.log n) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤ gaussianSeededSurplusBound f (Real.log n) := by
  have hlog := Analysis.mr_local_log_le_of_square_le hn hq hsize
  have hcap : Real.log q ≤ (2 / 3 : ℝ) * Real.log n := by
    linarith only [hlog, hL, Analysis.log_ten_lt_seven_thirds]
  have hpos : (0 : ℝ) ≤ (2 / 3) * Real.log n := by linarith only [hL]
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg q) hpos).mpr hcap
  have hw := gaussianSeededSurplus_bound_lower (f := f) hL
  have hc := gaussianSeededSurplus_cutoff_le f (Real.log n)
  have hcut : (3000 : ℝ) ≤ (gaussianSeededSharpCutoff f : ℝ) := by
    cases f <;>
      norm_num only [gaussianSeededSharpCutoff, Bool.false_eq_true, ite_false, ite_true,
        Nat.cast_ofNat]
  exact max_le (hcut.trans hc) (by nlinarith only [hs, hw, sq_nonneg (Real.log n)])

/-- Under GRH and the displayed actual prefix lower bound, each odd composite at scale at least 63
has a prime
rejecting strong MR below the surplus profile cutoff. The shared classification
closes the large, local and uniform triple branches internally. -/
theorem exists_prime_seededSurplus_of_prefix (f : Bool)
    (hprefix :
      gaussianSeededSurplusPrefix f ≤
        ∑ j ∈ Finset.Ioc 0 (gaussianSeededSharpCutoff f),
          Analysis.gaussianResolventMangoldtWeight j)
    {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianSeededSurplusBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  have hnlarge : 20000 ≤ n :=
    (by norm_num only : 20000 ≤ 10 ^ 27).trans (gaussian35000_size ho.pos hL)
  exact
    exists_prime_gaussianBudget ho hc hGRH hL
      (fun H hi hp ↦ seededSurplus_large f hprefix ho hnlarge H hi hp hGRH hL)
      (fun H hi hp hC ↦ seededSurplus_four f hprefix ho hnlarge H hi hp hGRH hC hL)
      (fun q hq hs ↦ seededSurplus_local f ho.pos hq hs hL)

/-- Given the actual prefix, minimality transfers the surplus bound to the least rejecting prime. -/
theorem exists_least_seededSurplus_of_prefix (f : Bool)
    (hprefix :
      gaussianSeededSurplusPrefix f ≤
        ∑ j ∈ Finset.Ioc 0 (gaussianSeededSharpCutoff f),
          Analysis.gaussianResolventMangoldtWeight j)
    {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianSeededSurplusBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject
      (exists_prime_seededSurplus_of_prefix f hprefix ho hc hGRH hL)

/-- Under GRH the same finite prefix cutoffs have the surplus credits
certified by their actual sums.
Only the Gaussian-minus-Gamma difference has been added to the existing Gamma prefix. -/
theorem seededSurplus_prefix (f : Bool)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    gaussianSeededSurplusPrefix f ≤
      ∑ j ∈ Finset.Ioc 0 (gaussianSeededSharpCutoff f),
        Analysis.gaussianResolventMangoldtWeight j := by
  cases f
  · simpa only [gaussianSeededSurplusPrefix, gaussianSeededSharpCutoff,
      Bool.false_eq_true, ite_false, Nat.floor_ofNat] using
      LLS.gaussian_prefix35000_surplus hGRH.riemann (le_refl (35000 : ℝ))
  · simpa only [gaussianSeededSurplusPrefix, gaussianSeededSharpCutoff, ite_true,
      Nat.floor_ofNat] using LLS.gaussian_prefix50000_surplus hGRH.riemann (le_refl (50000 : ℝ))

/-- Under GRH every odd composite at logarithmic scale at least 63 has an actual prime
rejecting strong MR under the chosen surplus cutoff. The finite prefix premise is closed
by its certified surplus sum, and all structural branches are internal. -/
theorem exists_prime_seededSurplus (f : Bool) {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianSeededSurplusBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  exists_prime_seededSurplus_of_prefix f (seededSurplus_prefix f hGRH) ho hc hGRH hL

/-- Under the same all-input assumptions, the least rejecting prime inherits the surplus cutoff. -/
theorem exists_least_seededSurplus (f : Bool) {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianSeededSurplusBound f (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q :=
  exists_least_seededSurplus_of_prefix f (seededSurplus_prefix f hGRH) ho hc hGRH hL

/-- Under GRH a single least rejecting prime lies below both surplus profiles.
Transfer the second independently certified cutoff by minimality of the first witness. -/
theorem exists_least_seededSurplusFamily {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianSeededSurplusFamily (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hb, hr, hl⟩ := exists_least_seededSurplus false ho hc hGRH hL
  obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_seededSurplus true ho hc hGRH hL
  have ht : (p : ℝ) ≤ gaussianSeededSurplusBound true (Real.log n) :=
    (Nat.cast_le.mpr (hl q hq hqr)).trans hqb
  exact ⟨p, hp, le_min hb ht, hr, hl⟩

/-- Under GRH the surplus minimum supplies an actual prime witness for every odd composite
at logarithmic scale at least 63, by the least-prime theorem for the whole family. -/
theorem exists_prime_seededSurplusFamily {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 63 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gaussianSeededSurplusFamily (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  (exists_least_seededSurplusFamily ho hc hGRH hL).imp fun _ h ↦ ⟨h.1, h.2.1, h.2.2.1⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
