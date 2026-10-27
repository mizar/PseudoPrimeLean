/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaReservedRampRows

/-! # Exact rational moments for reusable ramp transport -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The exact kth weighted mass moment of a finite list.
The weight and mass are arbitrary rational functions; no sign assumptions
are imposed. Fixed row weights permit reuse at every target scale. -/
def gammaRationalListMoment {ι : Type*} (rows : List ι) (w m : ι → ℚ) (k : ℕ) : ℚ :=
  (rows.map (fun r ↦ w r * m r ^ k)).sum

/-- Input: arbitrary rational weight, mass, increment and Taylor term count.
Claim: a weighted Taylor atom equals its finite moment expansion.
Proof: distribute the finite sum and rearrange rational products.
This is the algebraic input for a fixed moment table. -/
theorem gamma_weighted_taylor_eq_moments (w m d : ℚ) (n : ℕ) :
    w * gammaPositiveTaylor (m * d) n =
      ∑ k ∈ Finset.range n, d ^ k / (k.factorial : ℚ) * (w * m ^ k) := by
  simp only [gammaPositiveTaylor, Finset.mul_sum, mul_pow]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Input: any finite list and rational weight, mass and increment.
Claim: its Taylor sum equals a polynomial in the increment with exact moments.
Proof: apply the atom identity and interchange finite sums by induction.
No analytic moment bounds are subtracted in this identity. -/
theorem gamma_list_taylor_eq_moments {ι : Type*} (rows : List ι) (w m : ι → ℚ) (d : ℚ) (n : ℕ) :
    (rows.map (fun r ↦ w r * gammaPositiveTaylor (m r * d) n)).sum =
      ∑ k ∈ Finset.range n, d ^ k / (k.factorial : ℚ) * gammaRationalListMoment rows w m k := by
  induction rows with
  | nil =>
    simp only [List.map_nil, List.sum_nil, gammaRationalListMoment, mul_zero, Finset.sum_const_zero]
  | cons r rows
    ih =>
    simp only [List.map_cons, List.sum_cons, gammaRationalListMoment] at ih ⊢
    rw [gamma_weighted_taylor_eq_moments, ih]
    simp only [mul_add, Finset.sum_add_distrib]

/-- Input: arbitrary rational row weights, masses, target scale and moment index.
Claim: the masked moment is the inner moment plus the exact linear-ramp correction.
Proof: partition each row at the two joins and distribute the finite sums.
Both moments use the same fixed weights, so subtraction is an exact identity. -/
theorem gamma_ramp_mask_moment_eq {ι : Type*} (rows : List ι) (w m : ι → ℚ) (x : ℚ) (k : ℕ) :
    gammaRationalListMoment rows (fun r ↦ w r * gammaRationalRampFactor (m r / x)) m k =
      gammaRationalListMoment (rows.filter (fun r ↦ decide (m r / x ≤ 247 / 100))) w m k +
        ((99 / 40) *
              gammaRationalListMoment
                (rows.filter (fun r ↦ decide (247 / 100 < m r / x ∧ m r / x ≤ 99 / 40))) w m k -
            gammaRationalListMoment
                (rows.filter (fun r ↦ decide (247 / 100 < m r / x ∧ m r / x ≤ 99 / 40))) w m
                (k + 1) /
              x) /
          (1 / 200) := by
  induction rows with
  | nil =>
    simp only [gammaRationalListMoment, List.filter_nil, List.map_nil, List.sum_nil, mul_zero,
      zero_div, sub_zero, add_zero]
  | cons r rows ih =>
    by_cases hl : m r / x ≤ 247 / 100
    · have hmid : ¬(247 / 100 < m r / x ∧ m r / x ≤ 99 / 40) := fun h ↦ (not_lt_of_ge hl) h.1
      simp only [List.filter_cons, decide_eq_true hl, decide_eq_false hmid, Bool.false_eq_true,
        ite_true, ite_false, gammaRationalListMoment, List.map_cons, List.sum_cons] at ih ⊢
      rw [gammaRationalRampFactor, ite_eq_left hl, mul_one, ih]
      ring
    · by_cases hr : m r / x ≤ 99 / 40
      · have hmid : 247 / 100 < m r / x ∧ m r / x ≤ 99 / 40 := ⟨lt_of_not_ge hl, hr⟩
        simp only [List.filter_cons, decide_eq_false hl, decide_eq_true hmid, Bool.false_eq_true,
          ite_true, ite_false, gammaRationalListMoment, List.map_cons, List.sum_cons] at ih ⊢
        rw [gammaRationalRampFactor, ite_eq_right hl, ite_eq_left hr, ih, pow_succ]
        ring
      · have hmid : ¬(247 / 100 < m r / x ∧ m r / x ≤ 99 / 40) := fun h ↦ hr h.2
        simp only [List.filter_cons, decide_eq_false hl, decide_eq_false hmid, Bool.false_eq_true,
          ite_false, gammaRationalListMoment, List.map_cons, List.sum_cons] at ih ⊢
        rw [gammaRationalRampFactor, ite_eq_right hl, ite_eq_right hr, mul_zero, zero_mul, zero_add,
          ih]

/-- Input: an arbitrary finite list and two ordered rational thresholds.
Claim: the exact band moment is the difference of the two prefix moments.
Proof: split the upper prefix at the lower threshold.
This permits reuse of a fixed prefix-moment table as the support moves. -/
theorem gamma_list_band_moment_eq_prefix_sub {ι : Type*} (rows : List ι) (w m t : ι → ℚ) {a b : ℚ}
    (hab : a ≤ b) (k : ℕ) :
    gammaRationalListMoment (rows.filter (fun r ↦ decide (a < t r ∧ t r ≤ b))) w m k =
      gammaRationalListMoment (rows.filter (fun r ↦ decide (t r ≤ b))) w m k -
        gammaRationalListMoment (rows.filter (fun r ↦ decide (t r ≤ a))) w m k := by
  have hlo :
    (rows.filter (fun r ↦ decide (t r ≤ b))).filter (fun r ↦ decide (t r ≤ a)) =
      rows.filter (fun r ↦ decide (t r ≤ a)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro r _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.decide_iff]
    exact ⟨And.left, fun h ↦ ⟨h, h.trans hab⟩⟩
  have hmid :
    (rows.filter (fun r ↦ decide (t r ≤ b))).filter (fun r ↦ decide (¬t r ≤ a)) =
      rows.filter (fun r ↦ decide (a < t r ∧ t r ≤ b)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro r _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.decide_iff, not_le]
  have h :=
    List.sum_map_filter_add_sum_map_filter_not (fun r ↦ t r ≤ a) (fun r ↦ w r * m r ^ k)
      (rows.filter (fun r ↦ decide (t r ≤ b)))
  rw [hlo, hmid] at h
  exact (eq_sub_iff_add_eq).mpr (by simpa only [gammaRationalListMoment, add_comm] using h)

/-- The exact kth masked moment from fixed reserved-row weights.
Use inner rows with full weight and middle rows with the linear correction.
The same fixed logLower times rampLower squared is used in both moment tables. -/
def gammaReservedRampMoment (rows : List GammaFiniteRampRow) (x : ℚ) (k : ℕ) : ℚ :=
  gammaRationalListMoment (rows.filter (fun r ↦ decide ((r.index : ℚ) / x ≤ 247 / 100)))
      (fun r ↦ r.logLower * r.rampLower ^ 2) (fun r ↦ (r.index : ℚ)) k +
    ((99 / 40) *
          gammaRationalListMoment
            (rows.filter
              (fun r ↦ decide (247 / 100 < (r.index : ℚ) / x ∧ (r.index : ℚ) / x ≤ 99 / 40)))
            (fun r ↦ r.logLower * r.rampLower ^ 2) (fun r ↦ (r.index : ℚ)) k -
        gammaRationalListMoment
            (rows.filter
              (fun r ↦ decide (247 / 100 < (r.index : ℚ) / x ∧ (r.index : ℚ) / x ≤ 99 / 40)))
            (fun r ↦ r.logLower * r.rampLower ^ 2) (fun r ↦ (r.index : ℚ)) (k + 1) /
          x) /
      (1 / 200)

/-- Input: any reserved rows, target scale and moment index.
Claim: the two fixed-weight moment tables equal the exact masked moment.
Proof: apply the generic ramp-mask identity.
This justifies the subtraction in the executable moment expression. -/
theorem gamma_reserved_ramp_moment_eq (rows : List GammaFiniteRampRow) (x : ℚ) (k : ℕ) :
    gammaReservedRampMoment rows x k =
      gammaRationalListMoment rows
        (fun r ↦ r.logLower * r.rampLower ^ 2 * gammaRationalRampFactor ((r.index : ℚ) / x))
        (fun r ↦ (r.index : ℚ)) k := by
  exact
    (gamma_ramp_mask_moment_eq rows (fun r ↦ r.logLower * r.rampLower ^ 2) (fun r ↦ (r.index : ℚ)) x
        k).symm

/-- Input: arbitrary reserved rows, target scale and moment index.
Claim: each masked moment uses only exact prefix moments at the two joins.
Proof: replace each band moment by the difference of its prefixes.
The displayed subtraction is between exact rational sums with fixed weights. -/
theorem gamma_reserved_ramp_moment_eq_prefix (rows : List GammaFiniteRampRow) (x : ℚ) (k : ℕ) :
    let P := fun (y : ℚ) (j : ℕ) ↦
      gammaRationalListMoment (rows.filter (fun r ↦ decide ((r.index : ℚ) / x ≤ y)))
        (fun r ↦ r.logLower * r.rampLower ^ 2) (fun r ↦ (r.index : ℚ)) j
    gammaReservedRampMoment rows x k =
      P (247 / 100) k +
        ((99 / 40) * (P (99 / 40) k - P (247 / 100) k) -
            (P (99 / 40) (k + 1) - P (247 / 100) (k + 1)) / x) /
          (1 / 200) := by
  dsimp only
  unfold gammaReservedRampMoment
  rw [gamma_list_band_moment_eq_prefix_sub rows (fun r ↦ r.logLower * r.rampLower ^ 2)
      (fun r ↦ (r.index : ℚ)) (fun r ↦ (r.index : ℚ) / x) (by norm_num only) k,
    gamma_list_band_moment_eq_prefix_sub rows (fun r ↦ r.logLower * r.rampLower ^ 2)
      (fun r ↦ (r.index : ℚ)) (fun r ↦ (r.index : ℚ) / x) (by norm_num only) (k + 1)]

/-- The rational transported lower sum evaluated from exact masked moments.
The anchor, target and term count remain parameters; no analytic assumptions
are used by this finite polynomial evaluation. -/
def gammaReservedRampLowerFromMoments (rows : List GammaFiniteRampRow) (a x : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (1 / a - 1 / x) ^ k / (k.factorial : ℚ) * gammaReservedRampMoment rows x k

/-- Input: arbitrary rows, scales and Taylor term count.
Claim: moment evaluation equals the original sum of transported row allowances.
Proof: apply finite Taylor interchange and identify each exact masked moment.
This replaces repeated row-level polynomials by reusable fixed-weight moments. -/
theorem gamma_reserved_ramp_sum_eq_moments (rows : List GammaFiniteRampRow) (a x : ℚ) (n : ℕ) :
    (rows.map (fun r ↦ r.reservedLower a x n)).sum =
      gammaReservedRampLowerFromMoments rows a x n := by
  have heq :
    (rows.map (fun r ↦ r.reservedLower a x n)).sum =
      (rows.map
          (fun r ↦
            (r.logLower * r.rampLower ^ 2 * gammaRationalRampFactor ((r.index : ℚ) / x)) *
              gammaPositiveTaylor ((r.index : ℚ) * (1 / a - 1 / x)) n)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _
    simp only [GammaFiniteRampRow.reservedLower]
    ring
  rw [heq, gamma_list_taylor_eq_moments, gammaReservedRampLowerFromMoments]
  apply Finset.sum_congr rfl
  intro k _
  rw [gamma_reserved_ramp_moment_eq]

/-- Input: distinct checked rows in a positive interval and ordered positive scales.
Claim: exact moment evaluation bounds the actual ramp Mangoldt sum.
Proof: rewrite the row-sum lower theorem by the exact moment identity.
This connects the generic algebra to the analytic input of scalar cells. -/
theorem gamma_reserved_ramp_moments_lower_actual (rows : List GammaFiniteRampRow) (N : ℕ) {a x : ℚ}
    (ha : 0 < a) (hax : a ≤ x) (n : ℕ) (hp : rows.Forall (fun r ↦ r.prime.Prime))
    (hc : rows.Forall (fun r ↦ r.check (2 * a) = true))
    (hn : (rows.map GammaFiniteRampRow.index).Nodup)
    (hm : rows.Forall (fun r ↦ 0 < r.index ∧ r.index ≤ N)) :
    (gammaReservedRampLowerFromMoments rows a x n : ℝ) ≤
      AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x := by
  rw [← gamma_reserved_ramp_sum_eq_moments]
  exact gamma_reserved_ramp_rows_lower_actual rows N ha hax n hp hc hn hm

/-- A proof-carrying finite row certificate reusable at all scales at least a.
The rows and upper index specify the finite input. The remaining fields certify
anchor positivity, prime bases, executable checks at 2a, distinct indices and
positive bounded indices. These invariants suffice for every moment lower bound;
no actual ramp-sum or local-excess estimate is stored as an assumption. -/
structure GammaReservedRampCertificate (a : ℚ) where
  /-- The reusable prime-power rows. -/
  rows : List GammaFiniteRampRow
  /-- Any common upper index for these rows. -/
  upper : ℕ
  /-- The anchor is positive. -/
  anchorPos : 0 < a
  /-- Every base is prime. -/
  primes : rows.Forall (fun r ↦ r.prime.Prime)
  /-- Each numerical row check is valid at twice the anchor. -/
  checks : rows.Forall (fun r ↦ r.check (2 * a) = true)
  /-- No Mangoldt index is counted twice. -/
  indicesNodup : (rows.map GammaFiniteRampRow.index).Nodup
  /-- All row indices lie in the positive finite interval. -/
  support : rows.Forall (fun r ↦ 0 < r.index ∧ r.index ≤ upper)

/-- Input: one finite row certificate, any later rational scale and term count.
Claim: its exact moment evaluation bounds the actual ramp sum.
Proof: discharge all static row hypotheses from the certificate fields.
This is the common entry point for a family of scalar cells. -/
theorem GammaReservedRampCertificate.lower_le_actual {a : ℚ} (c : GammaReservedRampCertificate a)
    {x : ℚ} (hax : a ≤ x) (n : ℕ) :
    (gammaReservedRampLowerFromMoments c.rows a x n : ℝ) ≤
      AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x := by
  exact
    gamma_reserved_ramp_moments_lower_actual c.rows c.upper c.anchorPos hax n c.primes c.checks
      c.indicesNodup c.support

end PseudoPrime.Analysis
