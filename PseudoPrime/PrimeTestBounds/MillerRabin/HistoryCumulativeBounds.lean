/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.CumulativeHighBounds

/-! # Cumulative MR bounds with reduced finite-profile history

The finite list contains the seven improved triangular profiles and the retained eighth
profile. Each new profile covers earlier inputs using the already proved cumulative envelope
at its entrance. No monotonicity of the pointwise selected envelope is assumed.

These choices and their numerical certificates belong to the MR application. Keep this
proof layer outside the computational imports of independently checked finite certificates.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Intersect cumulative MR candidates using earlier profiles to cover each new entrance.
Input: profiles in reverse entrance order and a real upper logarithmic scale.
Definition: the empty family uses the global log-square bound; a new profile retains the
previous envelope at its entrance and its own quadratic bound above the entrance.
Output: a real cumulative majorant. Role: reduce the history cost without enumerating inputs. -/
noncomputable def historyEnvelope : List TriangularProfile → ℝ → ℝ
  | [], L => L ^ 2
  | f :: fs, L => min (historyEnvelope fs L) (max (historyEnvelope fs f.T) (f.C * L ^ 2))

/-- The eight selected triangular certificates, newest entrance first.
Input: none. Output: the retained eighth profile followed by all seven improved profiles.
Role: preserve the improved family while exposing the eighth cumulative candidate. -/
noncomputable def historyProfiles : List TriangularProfile :=
  [triangularP02823622, triangularP028289, triangularP028399, triangularP02891, triangularP02992,
    triangularP03315, triangularP04145, triangularP04603]

/-- Every retained history envelope is below the original log-square candidate.
Input: any finite profile family and real scale. Claim: the cumulative expression is no larger
than the squared scale. Proof: follow the left minimum by induction.
Role: compare every new history with the old single-profile entrance cost. -/
theorem historyEnvelope_le_sq (fs : List TriangularProfile) (L : ℝ) :
    historyEnvelope fs L ≤ L ^ 2 := by
  induction fs with
  | nil => exact le_rfl
  | cons f fs ih => exact (min_le_left _ _).trans ih

/-- Every finite-profile history expression is nonnegative.
Input: any profile family and real scale. Claim: nonnegativity, including empty families.
Proof: induction through the minima and retained-history maxima.
Role: handle empty admissible input domains without extra hypotheses. -/
theorem historyEnvelope_nonneg (fs : List TriangularProfile) (L : ℝ) :
    0 ≤ historyEnvelope fs L := by
  induction fs generalizing L with
  | nil => exact sq_nonneg L
  | cons f fs ih => exact le_min (ih L) ((ih f.T).trans (le_max_left _ _))

/-- The improved history family never exceeds a member's old cumulative expression.
Input: a selected profile and any real scale. Claim: the new minimum is below its original
entrance-square maximum. Proof: induction on membership and the log-square bound at entrances.
Role: retain every old candidate when the eighth profile is added. -/
theorem historyEnvelope_le_member (fs : List TriangularProfile) (f : TriangularProfile)
    (hf : f ∈ fs) (L : ℝ) : historyEnvelope fs L ≤ profileCumulative f L := by
  induction fs with
  | nil => exact False.elim (List.not_mem_nil hf)
  | cons g fs ih =>
    rcases List.mem_cons.mp hf with rfl | hm
    · exact (min_le_right _ _).trans (max_le_max (historyEnvelope_le_sq fs f.T) le_rfl)
    · exact (min_le_left _ _).trans (ih hm)

/-- A finite history family controls an actual least MR witness at any covering real scale.
Input: GRH, an odd composite above one, and a real scale at least its logarithm.
Claim: its least rejecting prime lies below the recursively reduced history expression.
Proof: use earlier profiles below each entrance and the new actual witness above it.
Role: establish whole-domain coverage without extrapolating a high-range coefficient. -/
theorem leastPrime_le_historyScale (fs : List TriangularProfile)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ historyEnvelope fs L := by
  have h0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn.le)
  induction fs generalizing L with
  | nil =>
    exact
      (compositeLeastPrime_le_log_sq hGRH hn ho hc).trans ((sq_le_sq₀ h0 (h0.trans hlog)).mpr hlog)
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

/-- The cumulative MR majorant from all eight profiles and their reduced histories.
Input: any natural endpoint, including zero. Output: the finite real-scale history expression.
Role: expose the new whole-domain bound without changing the least-witness definition. -/
noncomputable def historyCumulativeEnvelope (N : ℕ) : ℝ :=
  historyEnvelope historyProfiles (Real.log N)

/-- Every total least-witness value through a natural endpoint satisfies the history bound.
Input: GRH and an input no larger than the endpoint. Claim: its total least-witness value is
below the finite history expression. Proof: apply the real-scale bound on odd composites;
all other inputs contribute zero. Role: lift the witness theorem through a finite maximum. -/
theorem compositeLeastPrime_le_history (fs : List TriangularProfile)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n N : ℕ} (hnN : n ≤ N) :
    (compositeLeastPrime n : ℝ) ≤ historyEnvelope fs (Real.log N) := by
  by_cases hn : 1 < n ∧ Odd n ∧ ¬n.Prime
  · exact
      leastPrime_le_historyScale fs hGRH hn.1 hn.2.1 hn.2.2 _
        (Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn.1)) (Nat.cast_le.mpr hnN))
  · rw [compositeLeastPrime, ite_eq_right hn, Nat.cast_zero]
    exact historyEnvelope_nonneg fs _

/-- The maximum least rejecting prime obeys the improved whole-domain history bound.
Input: GRH and any natural endpoint. Claim: the finite maximum is below the new majorant.
Proof: lift each individual bound through a natural floor and the finite supremum.
Role: publish the reduced-history cumulative MR estimate, including empty target ranges. -/
theorem cumulativeLeastPrime_le_history
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ historyCumulativeEnvelope N := by
  have h0 : 0 ≤ historyCumulativeEnvelope N := historyEnvelope_nonneg _ _
  have hb : cumulativeLeastPrime N ≤ ⌊historyCumulativeEnvelope N⌋₊ := by
    apply Finset.sup_le
    intro n hn
    exact
      (Nat.le_floor_iff h0).mpr
        (compositeLeastPrime_le_history historyProfiles hGRH
          (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))
  exact (Nat.cast_le.mpr hb).trans (Nat.floor_le h0)

/-- Each of the original seven improved certificates remains in the history family.
Input: its original finite selector. Claim: membership in the enlarged profile list.
Proof: check only the seven selector cases. Role: preserve every old cumulative candidate. -/
theorem tunedProfile_mem_history (i : Fin 7) : triangularTunedProfile i ∈ historyProfiles := by
  fin_cases i <;>
    simp only [triangularTunedProfile, historyProfiles, List.mem_cons, List.not_mem_nil, or_false,
      or_true, true_or]

/-- The enlarged reduced-history envelope never exceeds the old public cumulative envelope.
Input: any natural endpoint. Claim: non-worsening independently of GRH.
Proof: preserve the global log-square candidate and every old improved profile.
Role: expose the new cumulative estimate while retaining the old public guarantee. -/
theorem historyCumulative_le_high (N : ℕ) :
    historyCumulativeEnvelope N ≤ highCumulativeEnvelope N := by
  exact
    le_min (historyEnvelope_le_sq _ _)
      (Finset.le_inf' _ _ (fun i _ ↦ historyEnvelope_le_member _ _ (tunedProfile_mem_history i) _))

/-- The eighth profile retains the exact reduced history supplied by the first seven.
Input: none. Claim: the earlier envelope at its entrance equals the displayed rational integer.
Proof: evaluate eight fixed real candidates by rational arithmetic, not input enumeration.
Role: certify the improved recovery threshold of the eighth high-range coefficient. -/
theorem history_eighth_entry :
    historyEnvelope historyProfiles.tail 1820000000000 = 937044836000000000000000 := by
  norm_num only [historyEnvelope, historyProfiles, List.tail_cons, triangularP028289,
    triangularP028399, triangularP02891, triangularP02992, triangularP03315, triangularP04145,
    triangularP04603, min_def, max_def, ite_true, ite_false]

/-- The seventh profile retains the exact reduced history supplied by the first six.
Input: none. Claim: the earlier envelope at its entrance is the displayed rational integer.
Proof: rational evaluation of the finite profile recurrence.
Role: certify recovery of the seventh improved coefficient without a coarse entrance square. -/
theorem history_seventh_entry :
    historyEnvelope historyProfiles.tail.tail 1480000000000 = 622051696000000000000000 := by
  norm_num only [historyEnvelope, historyProfiles, List.tail_cons, triangularP028399,
    triangularP02891, triangularP02992, triangularP03315, triangularP04145, triangularP04603,
    min_def, max_def, ite_true, ite_false]

/-- Once its reduced history is covered, the eighth coefficient bounds the entire family.
Input: a real scale satisfying the exact rational recovery condition.
Claim: the new history expression is at most the eighth quadratic value.
Proof: select the eighth maximum and use its certified retained history.
Role: recover the best high-range coefficient earlier than the old entrance-square method. -/
theorem history_eighth_recovered (L : ℝ)
    (hr : (937044836000000000000000 : ℝ) ≤ (1411811 / 5000000 : ℝ) * L ^ 2) :
    historyEnvelope historyProfiles L ≤ (1411811 / 5000000 : ℝ) * L ^ 2 := by
  have hm :
    historyEnvelope historyProfiles L ≤
      max (historyEnvelope historyProfiles.tail 1820000000000) ((1411811 / 5000000 : ℝ) * L ^ 2) :=
    min_le_right _ _
  rw [history_eighth_entry] at hm
  exact hm.trans_eq (max_eq_right hr)

/-- The seventh coefficient is valid as soon as its reduced history is covered.
Input: a real scale satisfying the exact rational recovery inequality.
Claim: the full enlarged envelope is below the seventh quadratic value.
Proof: select the preserved seventh branch and its certified history.
Role: expose the earlier seventh recovery alongside the retained eighth candidate. -/
theorem history_seventh_recovered (L : ℝ)
    (hr : (622051696000000000000000 : ℝ) ≤ (28289 / 100000 : ℝ) * L ^ 2) :
    historyEnvelope historyProfiles L ≤ (28289 / 100000 : ℝ) * L ^ 2 := by
  have hm :
    historyEnvelope historyProfiles L ≤
      max (historyEnvelope historyProfiles.tail.tail 1480000000000)
        ((28289 / 100000 : ℝ) * L ^ 2) :=
    (min_le_left _ _).trans (min_le_right _ _)
  rw [history_seventh_entry] at hm
  exact hm.trans_eq (max_eq_right hr)

/-- The eighth coefficient is strictly smaller than every retained improved coefficient.
Input: one of the original seven selectors. Claim: the exact rational coefficient is smaller.
Proof: the seven scalar comparisons only. Role: certify strict improvement after recovery. -/
theorem eighth_coefficient_lt_tuned (i : Fin 7) :
    (1411811 / 5000000 : ℝ) < (triangularTunedProfile i).C := by
  fin_cases i
  · norm_num only [triangularTunedProfile, triangularP04603]
  · norm_num only [triangularTunedProfile, triangularP04145]
  · norm_num only [triangularTunedProfile, triangularP03315]
  · norm_num only [triangularTunedProfile, triangularP02992]
  · norm_num only [triangularTunedProfile, triangularP02891]
  · norm_num only [triangularTunedProfile, triangularP028399]
  · change (1411811 / 5000000 : ℝ) < 28289 / 100000
    norm_num only

/-- After eighth-profile recovery, the new cumulative formula strictly improves the old one.
Input: a positive endpoint logarithm and the exact reduced-history recovery inequality.
Claim: strict improvement over the whole old minimum, not merely one candidate.
Proof: its least finite profile still has a coefficient strictly above the eighth coefficient.
Role: certify a genuine public cumulative improvement. -/
theorem historyCumulative_lt_high {N : ℕ} (hL : 0 < Real.log (N : ℝ))
    (hr : (937044836000000000000000 : ℝ) ≤ (1411811 / 5000000 : ℝ) * Real.log N ^ 2) :
    historyCumulativeEnvelope N < highCumulativeEnvelope N := by
  have hsq : 0 < Real.log (N : ℝ) ^ 2 := sq_pos_of_pos hL
  apply (history_eighth_recovered _ hr).trans_lt
  apply lt_min
  · have hc : (1411811 / 5000000 : ℝ) < 1 := by norm_num only
    exact (mul_lt_mul_of_pos_right hc hsq).trans_eq (one_mul _)
  · obtain ⟨i, _hi, he⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun i : Fin 7 ↦ profileCumulative (triangularTunedProfile i) (Real.log N))
    rw [he]
    exact (mul_lt_mul_of_pos_right (eighth_coefficient_lt_tuned i) hsq).trans_le (le_max_right _ _)

/-- Above the displayed real scale, the reduced-history envelope strictly beats the old one.
Input: an endpoint logarithm at least two trillion. Claim: strict public improvement.
Proof: the lower scale implies the exact eighth recovery inequality by a squared difference.
Role: provide a simple certified improvement interval without approximate square roots. -/
theorem historyCumulative_lt_high_large {N : ℕ} (hL : 2000000000000 ≤ Real.log (N : ℝ)) :
    historyCumulativeEnvelope N < highCumulativeEnvelope N := by
  have hpos : 0 < Real.log (N : ℝ) := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2000000000000) hL
  apply historyCumulative_lt_high hpos
  nlinarith only [hL, sq_nonneg (Real.log (N : ℝ) - 2000000000000)]

/-- Both reduced recovery thresholds are strictly below the old coarse thresholds.
Input: none. Claim: the squared recovery scales for profiles seven and eight decrease.
Proof: exact rational comparisons. Role: validate the claimed history savings without decimals. -/
theorem history_recovery_improves :
    (622051696000000000000000 : ℝ) / (28289 / 100000) < 1480000000000 ^ 2 / (28289 / 100000) ∧
      (937044836000000000000000 : ℝ) / (1411811 / 5000000) <
        1820000000000 ^ 2 / (1411811 / 5000000) := by
  norm_num only [and_self]

end PseudoPrime.PrimeTestBounds.MillerRabin
