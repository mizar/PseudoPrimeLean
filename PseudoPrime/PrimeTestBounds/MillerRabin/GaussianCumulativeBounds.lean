/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BaseHistoryBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.HistoryCumulativeBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusBounds

/-! # Gaussian common-scale bases for cumulative MR history

The selected MR profiles, canonical least rejecting prime and GRH witness contracts belong
in this consumer. The recurrence core imports Mathlib only. The present Gaussian base uses
the certified thousand-term prefix and absorbs every input below the analytic entrance.
Pointwise small-input selections and their local monotonicity remain unchanged.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For triangular profiles, the square base recovers the previous history expression exactly.
Induct through the identical recurrences; this comparison stays outside the minimal core. -/
theorem baseHistory_sq (fs : List TriangularProfile) (L : ℝ) :
    baseHistory TriangularProfile.T TriangularProfile.C (fun t ↦ t ^ 2) fs L =
      historyEnvelope fs L := by
  induction fs generalizing L with
  | nil => exact rfl
  | cons f fs ih => simp only [baseHistory, historyEnvelope, ih]

/-- A triangular history whose base is below the square never exceeds the old history.
Apply base-order preservation and the exact square-base identification. -/
theorem baseHistory_le_history (B : ℝ → ℝ) (hB : ∀ L, B L ≤ L ^ 2) (fs : List TriangularProfile)
    (L : ℝ) :
    baseHistory TriangularProfile.T TriangularProfile.C B fs L ≤ historyEnvelope fs L := by
  rw [← baseHistory_sq]
  exact baseHistory_mono TriangularProfile.T TriangularProfile.C B (fun t ↦ t ^ 2) hB fs L

/-- Under GRH, any common-scale base contract transfers to a triangular profile history.
For each odd composite use prior history below an entrance and the actual profile witness
above it, then transfer by leastness. No scale monotonicity of the base is required. -/
theorem leastPrime_le_baseHistory (B : ℝ → ℝ)
    (hB :
      ∀ {n : ℕ},
        1 < n → Odd n → ¬n.Prime → ∀ L : ℝ, Real.log n ≤ L → (compositeLeastPrime n : ℝ) ≤ B L)
    (fs : List TriangularProfile) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ baseHistory TriangularProfile.T TriangularProfile.C B fs L := by
  have h0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn.le)
  induction fs generalizing L with
  | nil => exact hB hn ho hc L hlog
  | cons f fs ih =>
    apply le_min (ih L hlog)
    by_cases he : f.T ≤ Real.log n
    · obtain ⟨p, hp, hb, hr⟩ := exists_prime_triangularProfile f hn ho hc hGRH he
      have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
      have hC : 0 ≤ f.C := (sq_nonneg f.a).trans f.square
      exact
        ((Nat.cast_le.mpr hm).trans hb).trans
          ((mul_le_mul_of_nonneg_left ((sq_le_sq₀ h0 (h0.trans hlog)).mpr hlog) hC).trans
            (le_max_right _ _))
    · exact (ih f.T (le_of_not_ge he)).trans (le_max_left _ _)

/-- A nonnegative certified base controls every total least-witness value below any endpoint.
Use the common-scale history on odd composites and zero on other inputs. -/
theorem compositeLeastPrime_le_base (B : ℝ → ℝ) (h0 : ∀ L, 0 ≤ B L)
    (hB :
      ∀ {n : ℕ},
        1 < n → Odd n → ¬n.Prime → ∀ L : ℝ, Real.log n ≤ L → (compositeLeastPrime n : ℝ) ≤ B L)
    (fs : List TriangularProfile) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n N : ℕ} (hnN : n ≤ N) :
    (compositeLeastPrime n : ℝ) ≤
      baseHistory TriangularProfile.T TriangularProfile.C B fs (Real.log N) := by
  by_cases hn : 1 < n ∧ Odd n ∧ ¬n.Prime
  · exact
      leastPrime_le_baseHistory B hB fs hGRH hn.1 hn.2.1 hn.2.2 _
        (Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn.1)) (Nat.cast_le.mpr hnN))
  · rw [compositeLeastPrime, ite_eq_right hn, Nat.cast_zero]
    exact baseHistory_nonneg TriangularProfile.T TriangularProfile.C B h0 fs _

/-- Under GRH, a certified nonnegative base controls the cumulative least prime at every endpoint.
Pass the individual total bounds through the natural floor and finite supremum. -/
theorem cumulativeLeastPrime_le_base (B : ℝ → ℝ) (h0 : ∀ L, 0 ≤ B L)
    (hB :
      ∀ {n : ℕ},
        1 < n → Odd n → ¬n.Prime → ∀ L : ℝ, Real.log n ≤ L → (compositeLeastPrime n : ℝ) ≤ B L)
    (fs : List TriangularProfile) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤
      baseHistory TriangularProfile.T TriangularProfile.C B fs (Real.log N) := by
  have hp : 0 ≤ baseHistory TriangularProfile.T TriangularProfile.C B fs (Real.log N) :=
    baseHistory_nonneg TriangularProfile.T TriangularProfile.C B h0 fs _
  have hb :
    cumulativeLeastPrime N ≤
      ⌊baseHistory TriangularProfile.T TriangularProfile.C B fs (Real.log N)⌋₊ := by
    apply Finset.sup_le
    intro n hn
    exact
      (Nat.le_floor_iff hp).mpr
        (compositeLeastPrime_le_base B h0 hB fs hGRH (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))
  exact (Nat.cast_le.mpr hb).trans (Nat.floor_le hp)

/-- The fixed surplus Gaussian cutoff is monotone on the entire real scale.
Compare its positive roots and square twice; this transports actual Gaussian witnesses. -/
theorem gaussianSurplus_mono : Monotone gaussianSurplusBound := by
  intro L K hLK
  have hs := gaussianLow_root_mono (u := 91 / 10) (D := 38 / 5) hLK
  have hsq := (sq_le_sq₀ (gaussianSurplus_root_pos L).le (gaussianSurplus_root_pos K).le).mpr hs
  have hsq2 :=
    (sq_le_sq₀ (sq_nonneg (gaussianSurplusRoot L)) (sq_nonneg (gaussianSurplusRoot K))).mpr hsq
  exact mul_le_mul_of_nonneg_left hsq2 (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- Under GRH, the Gaussian cutoff at max(63,L) bounds every odd composite with log n at most L.
Above the entrance transfer the actual witness by leastness and Gaussian monotonicity;
below it absorb the existing log-square cutoff into the fixed Gaussian floor. -/
theorem leastPrime_le_gaussianScale (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ gaussianSurplusBound (max 63 L) := by
  by_cases h63 : 63 ≤ Real.log n
  · obtain ⟨p, hp, hb, hr⟩ := exists_prime_gaussianSurplus ho hc hGRH h63
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    exact
      ((Nat.cast_le.mpr hm).trans hb).trans (gaussianSurplus_mono (hlog.trans (le_max_right _ _)))
  · have hs :=
      (sq_le_sq₀ (Real.log_natCast_nonneg n) (by norm_num only : (0 : ℝ) ≤ 63)).mpr
        (le_of_not_ge h63)
    have hf := gaussianSurplus_cutoff_floor (max 63 L)
    exact
      (compositeLeastPrime_le_log_sq hGRH hn ho hc).trans
        (hs.trans ((by norm_num only : (63 : ℝ) ^ 2 ≤ (6 / 5) * ((91 / 10) ^ 2) ^ 2).trans hf))

/-- Intersect the global square with the Gaussian cutoff at the covering analytic scale.
The max(63,L) guard covers all earlier inputs without new finite enumeration.
This real-scale base feeds the finite cumulative history recursion. -/
noncomputable def gaussianHistoryBase (L : ℝ) : ℝ :=
  min (L ^ 2) (gaussianSurplusBound (max 63 L))

/-- The Gaussian history base is nonnegative at every real scale, including zero.
Both the square and the unchanged Gaussian floor are nonnegative. -/
theorem gaussianHistoryBase_nonneg (L : ℝ) : 0 ≤ gaussianHistoryBase L := by
  exact
    le_min (sq_nonneg L)
      ((by norm_num only : (0 : ℝ) ≤ (6 / 5) * ((91 / 10) ^ 2) ^ 2).trans
        (gaussianSurplus_cutoff_floor _))

/-- The Gaussian history base never exceeds the previous square base.
Project the left minimum to retain the old cumulative guarantee. -/
theorem gaussianHistoryBase_le_sq (L : ℝ) : gaussianHistoryBase L ≤ L ^ 2 := by
  exact min_le_left _ _

/-- Under GRH, the Gaussian base bounds the true least rejecting prime at every covering scale.
Intersect the existing log-square theorem with the entrance-safe Gaussian bound. -/
theorem leastPrime_le_gaussianBase (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ gaussianHistoryBase L := by
  have h0 := Real.log_natCast_nonneg n
  exact
    le_min
      ((compositeLeastPrime_le_log_sq hGRH hn ho hc).trans
        ((sq_le_sq₀ h0 (h0.trans hlog)).mpr hlog))
      (leastPrime_le_gaussianScale hGRH hn ho hc L hlog)

/-- Evaluate the finite eight-profile history using the certified Gaussian common-scale base.
Every natural endpoint is allowed, including empty target domains.
This cumulative majorant leaves the canonical least-witness function unchanged. -/
noncomputable def gaussianCumulativeEnvelope (N : ℕ) : ℝ :=
  baseHistory TriangularProfile.T TriangularProfile.C gaussianHistoryBase historyProfiles
    (Real.log N)

/-- Under GRH, the Gaussian cumulative envelope bounds all least rejecting primes through N.
Apply the arbitrary-base transfer with the internally supplied Gaussian base contract. -/
theorem cumulativeLeastPrime_le_gaussian
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ gaussianCumulativeEnvelope N := by
  exact
    cumulativeLeastPrime_le_base gaussianHistoryBase gaussianHistoryBase_nonneg
      (fun hn ho hc L hlog ↦ leastPrime_le_gaussianBase hGRH hn ho hc L hlog) historyProfiles hGRH N

/-- The Gaussian cumulative envelope is below the previous full history at every natural endpoint.
Use the pointwise base comparison; neither pointwise-envelope monotonicity nor GRH is needed. -/
theorem gaussianCumulative_le_history (N : ℕ) :
    gaussianCumulativeEnvelope N ≤ historyCumulativeEnvelope N := by
  exact baseHistory_le_history gaussianHistoryBase gaussianHistoryBase_le_sq historyProfiles _

/-- At nonnegative scales through 63, the Gaussian base equals the old square exactly.
The fixed Gaussian floor absorbs the square at 63 and hence every smaller square. -/
theorem gaussianHistoryBase_eq_sq {L : ℝ} (h0 : 0 ≤ L) (hL : L ≤ 63) :
    gaussianHistoryBase L = L ^ 2 := by
  apply min_eq_left
  exact
    ((sq_le_sq₀ h0 (by norm_num only : (0 : ℝ) ≤ 63)).mpr hL).trans
      ((by norm_num only : (63 : ℝ) ^ 2 ≤ (6 / 5) * ((91 / 10) ^ 2) ^ 2).trans
        (gaussianSurplus_cutoff_floor _))

end PseudoPrime.PrimeTestBounds.MillerRabin
