/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.GammaJointEntranceBounds
public import PseudoPrime.PseudoSquare.Bounds.ElementaryOmegaFinal
public import PseudoPrime.LLS.Phase64RetainedExcessJacobiCell

/-! # Common-endpoint and retained fixed-cap bounds on all smaller inputs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For GRH, L>=255 and log B<=L, the negative-witness maximum through B is at most
(9999/10000)L^2. Each admissible input uses the same endpoint; the empty maximum is zero.
This supplies the uniform bound used by Selfridge maximum transfers. -/
theorem QNegOne_le_joint_endpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {L : ℝ} (hL : 255 ≤ L) (hlog : Real.log B ≤ L) :
    (QNegOne B : ℝ) ≤ (9999 / 10000 : ℝ) * L ^ 2 := by
  apply QNegOne_cast_le_of_forall
    (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 9999 / 10000) (sq_nonneg L))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact primeNegOneWitness_cast_le_joint_entrance_endpoint ha.odd ha.not_isSquare hGRH hL
    ((Real.log_le_log (Nat.cast_pos.mpr ha.odd.pos) (Nat.cast_le.mpr ha.le)).trans hlog) _

/-- The coefficient bound evaluated at max(255,log B). The fixed endpoint covers all
smaller inputs, including B=0; no pointwise high-entrance theorem is extrapolated.
This is the common-endpoint candidate in the new uniform envelope. -/
noncomputable def jointEndpointBound (B : ℕ) : ℝ :=
  (9999 / 10000 : ℝ) * (max 255 (Real.log B)) ^ 2

/-- Under GRH, both negative and non-one witness maxima obey the common-endpoint bound.
Specialize the endpoint theorem at max(255,log B) and transfer QNeOne<=QNegOne.
The statement includes every natural endpoint B, with no positivity assumption. -/
theorem witnessMaxima_le_joint_endpoint (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ jointEndpointBound B ∧ (QNeOne B : ℝ) ≤ jointEndpointBound B := by
  have h := QNegOne_le_joint_endpoint hGRH (le_max_left 255 (Real.log B))
    (le_max_right 255 (Real.log B))
  exact ⟨h, (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans h⟩

/-- An odd natural nonsquare is at least three. Exclude one by nonsquareness and two
by parity, then use the successor order. This discharges the elementary bound domain. -/
private theorem three_le_odd_nonsquare {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n) :
    3 ≤ n := by
  have hne : n ≠ 1 := fun h ↦ hns (h ▸ ⟨1, rfl⟩)
  have htwo : n ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hn)
  exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne
    (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hn.pos (Ne.symm hne))) (Ne.symm htwo))

/-- For n>0, expand log(4n) as 2log 2+log n. Both factors are nonzero,
so the logarithm product and power identities apply. Reuse this identity in
low-domain estimates and strict envelope comparisons. -/
private theorem log_four_mul {n : ℕ} (hn : 0 < n) :
    Real.log (4 * (n : ℝ)) = 2 * Real.log 2 + Real.log n := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num only,
    Real.log_mul (by norm_num only) (Nat.cast_ne_zero.mpr hn.ne'), Real.log_pow]
  norm_num only [Nat.cast_ofNat]

/-- For positive n with log n<10, log(4n) lies between one and twelve.
Expand the product and use certified log-two bounds. These inequalities
control both the elementary radius base and its second logarithm. -/
private theorem low_log_four_range {n : ℕ} (hn : 0 < n) (hlog : Real.log n < 10) :
    1 ≤ Real.log (4 * (n : ℝ)) ∧ Real.log (4 * (n : ℝ)) ≤ 12 := by
  have he := log_four_mul hn
  constructor
  · linarith only [he, Real.log_two_gt_d9, Real.log_natCast_nonneg n]
  · linarith only [he, Real.log_two_lt_d9, hlog]

/-- Log twelve is at most three. Compare twelve with 2^4 and apply the certified
log-two upper bound. This small scalar bound replaces any new finite input certificate. -/
private theorem log_twelve_le_three : Real.log (12 : ℝ) ≤ 3 := by
  have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 12)
    (by norm_num only : (12 : ℝ) ≤ 2 ^ 4)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

/-- For positive n with log n<10, the elementary radius is below 4093. Bound log(4n)
between one and twelve and loglog(4n) between zero and three. This closes the low
branch of the retained fixed-cap witness theorem without new finite enumeration. -/
private theorem elementaryRadius_lt_fixed_cap {n : ℕ} (hn : 0 < n)
    (hlog : Real.log n < 10) : elementaryRadius n < 4093 := by
  obtain ⟨hlo, hhi⟩ := low_log_four_range hn hlog
  have hu := (Real.log_le_log (by linarith only [hlo]) hhi).trans log_twelve_le_three
  have hl := Real.log_nonneg hlo
  unfold elementaryRadius
  nlinarith only [hlo, hhi, hu, hl,
    sq_nonneg (Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) - 132 / 5)]

/-- Under GRH, every odd nonsquare with log n<=1609/25 has least negative witness at
most 4093. Above log ten use the retained cell; below it use the elementary radius.
This covers all smaller inputs, rather than just the original bounded logarithmic cell. -/
theorem primeNegOneWitness_le_fixed_cap {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlog : Real.log n ≤ 1609 / 25) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    NumberTheory.primeNegOneWitness n hw ≤ 4093 := by
  by_cases hlo : 10 ≤ Real.log n
  · obtain ⟨p, hp, ho, hb, hv⟩ :=
      LLS.exists_odd_prime_negative_phase64_retained_fixed_cap hGRH hn hns hlo hlog
    exact (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩).trans hb
  · have hm := (elementary_formula_real hGRH (three_le_odd_nonsquare hn hns)).2
    have ha : n ∈ NumberTheory.admissibleFinset n :=
      NumberTheory.mem_admissibleFinset_iff.mpr ⟨hn.pos, le_refl n, hn, hns⟩
    exact Nat.cast_le.mp ((Nat.cast_le.mpr (primeNegOneWitness_le_QNegOne ha)).trans
      (hm.trans (elementaryRadius_lt_fixed_cap hn.pos (lt_of_not_ge hlo)).le))

/-- Under GRH and log B<=1609/25, both witness maxima through B are at most 4093.
Lift the full low-domain witness theorem through the finite maximum. Empty domains
are included by the nonnegative bound; no finite certificate is added. -/
theorem witnessMaxima_le_fixed_cap {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlog : Real.log B ≤ 1609 / 25) : QNegOne B ≤ 4093 ∧ QNeOne B ≤ 4093 := by
  have h : (QNegOne B : ℝ) ≤ (4093 : ℕ) := by
    apply QNegOne_cast_le_of_forall (by norm_num only : (0 : ℝ) ≤ (4093 : ℕ))
    intro n hn
    have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
    exact Nat.cast_le.mpr (primeNegOneWitness_le_fixed_cap ha.odd ha.not_isSquare hGRH
      ((Real.log_le_log (Nat.cast_pos.mpr ha.pos) (Nat.cast_le.mpr ha.le)).trans hlog) _)
  exact ⟨Nat.cast_le.mp h, (QNeOne_le_QNegOne B).trans (Nat.cast_le.mp h)⟩

/-- The minimum of the elementary and common-endpoint bounds and, when valid, 4093.
Guards restrict the retained cap to its proved upper logarithmic endpoint. This
candidate preserves both earlier formulas and introduces no monotonicity requirement. -/
noncomputable def commonEndpointEnvelope (B : ℕ) : ℝ :=
  min (elementaryRadius B) (min (jointEndpointBound B)
    (if Real.log B ≤ 1609 / 25 then 4093 else jointEndpointBound B))

/-- Under GRH and B>=3, both witness maxima obey the combined envelope. Combine the
three separately proved bounds with min, retaining the fixed-cap guard. This is the
public cumulative envelope used by the Selfridge and trial-count consumers. -/
theorem witnessMaxima_le_common_envelope {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hB : 3 ≤ B) :
    (QNegOne B : ℝ) ≤ commonEndpointEnvelope B ∧
      (QNeOne B : ℝ) ≤ commonEndpointEnvelope B := by
  have hj := (witnessMaxima_le_joint_endpoint B hGRH).1
  have hf : (QNegOne B : ℝ) ≤
      if Real.log B ≤ 1609 / 25 then 4093 else jointEndpointBound B := by
    split_ifs with h
    · exact Nat.cast_le.mpr (witnessMaxima_le_fixed_cap hGRH h).1
    · exact hj
  have h := le_min (elementary_formula_real hGRH hB).2 (le_min hj hf)
  exact ⟨h, (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans h⟩

/-- If log B>=64, the elementary radius dominates (log B)^2. Expand log(4B),
use nonnegative loglog and square the larger positive base. This supplies exact
strict comparisons for the new fixed-cap and endpoint candidates. -/
private theorem log_sq_le_elementaryRadius {B : ℕ} (hL : 64 ≤ Real.log B) :
    (Real.log B) ^ 2 ≤ elementaryRadius B := by
  have hp : (0 : ℝ) < B := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by
    intro h
    simp only [h, Nat.cast_zero, Real.log_zero] at hL
    norm_num only at hL))
  have he := log_four_mul (Nat.cast_pos.mp hp)
  have hl : 1 ≤ Real.log (4 * (B : ℝ)) := by linarith only [he, hL, Real.log_two_gt_d9]
  have hh := Real.log_nonneg hl
  unfold elementaryRadius
  nlinarith only [he, hh, hL, Real.log_two_gt_d9,
    sq_nonneg (2 * Real.log 2 + (24 / 5 : ℝ) * Real.log (Real.log (4 * (B : ℝ))) + 3)]

/-- For 64<=log B<=1609/25, the combined envelope is strictly below the elementary
radius. The fixed cap is 4093<64^2, and the elementary radius exceeds log(B)^2.
This certifies a nonempty real-logarithmic improvement interval without decimal roots. -/
theorem commonEnvelope_lt_elementary_cap {B : ℕ}
    (hlo : 64 ≤ Real.log B) (hhi : Real.log B ≤ 1609 / 25) :
    commonEndpointEnvelope B < elementaryRadius B := by
  have hf : commonEndpointEnvelope B ≤ 4093 := by
    exact (min_le_right _ _).trans ((min_le_right _ _).trans_eq (ite_eq_left hhi))
  have he := log_sq_le_elementaryRadius hlo
  exact hf.trans_lt (by nlinarith only [he, hlo, sq_nonneg (Real.log B - 64)])

/-- For log B>=255, the combined envelope is strictly below the elementary radius.
The common-endpoint candidate is 9999/10000 times log(B)^2, a strict saving over
log(B)^2. This comparison is to the elementary candidate, not to all analytic bounds. -/
theorem commonEnvelope_lt_elementary_joint {B : ℕ} (hL : 255 ≤ Real.log B) :
    commonEndpointEnvelope B < elementaryRadius B := by
  have hj : commonEndpointEnvelope B ≤ (9999 / 10000 : ℝ) * (Real.log B) ^ 2 := by
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans_eq
      (congrArg (fun x : ℝ ↦ (9999 / 10000 : ℝ) * x ^ 2) (max_eq_right hL))
  have he := log_sq_le_elementaryRadius (le_trans (by norm_num only) hL)
  exact hj.trans_lt (by nlinarith only [he, hL, sq_nonneg (Real.log B - 255)])

/-- Under GRH, odd nonsquare n with log n<=1609/25 has an actual negative odd-prime
witness at most 4093. Choose the least witness and its membership data. This exposes
the fixed cap independently of the cumulative maximum API. -/
theorem exists_prime_neg_one_le_fixed_cap {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlog : Real.log n ≤ 1609 / 25) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ≤ 4093 ∧ jacobiSym n p = -1 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hm := NumberTheory.primeNegOneWitness_mem n hw
  exact ⟨NumberTheory.primeNegOneWitness n hw, hm.1, hm.2.1,
    primeNegOneWitness_le_fixed_cap hn hns hGRH hlog hw, hm.2.2⟩

end PseudoPrime.PseudoSquare
