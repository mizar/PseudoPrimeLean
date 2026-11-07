/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleLowCellSound

/-! # Contiguous coverage of the low triple bridge -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Check that consecutive cells cover the rational interval from `lo` to
`hi`. Each step requires overlap with the previous endpoint and the recursion
stops as soon as a cell reaches the final endpoint. -/
def lowBridgeCoverCheck (lo hi : ℚ) : List LowBridgeCell → Bool
  | [] => false
  | c :: cs =>
    decide (c.lo ≤ lo ∧ lo ≤ c.hi) && (decide (hi ≤ c.hi) || lowBridgeCoverCheck c.hi hi cs)

/-- A checked contiguous cell family yields the coefficient `3/10` witness
throughout its covered interval for an ordered uniform Korselt triple with
least factor at least five. Induction selects a cell containing the logarithm,
then the checked cell theorem supplies the witness. -/
theorem lowBridgeCover_sound (cells : List LowBridgeCell) (lo hi : ℚ)
    (hcover : lowBridgeCoverCheck lo hi cells = true)
    (hcheck : cells.all LowBridgeCell.check = true) {n p q r : ℕ} (hn : 1 < n) (ho : Odd n)
    (hnp : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpO : Odd p) (hqO : Odd q)
    (hrO : Odd r) (hpq : p < q) (hqr : q < r) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp5 : 5 ≤ (p : ℝ))
    (hU : Real.log n ≤ 988 / 25) (hlo : (lo : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (hi : ℝ)) :
    ∃ a : ℕ,
      a.Prime ∧
        (a : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (a : ZMod n) := by
  induction cells generalizing lo with
  | nil => simp only [lowBridgeCoverCheck, Bool.false_eq_true] at hcover
  | cons c cs
    ih =>
    have hc :
      (decide (c.lo ≤ lo ∧ lo ≤ c.hi) && (decide (hi ≤ c.hi) || lowBridgeCoverCheck c.hi hi cs)) =
        true := by
      simpa only [lowBridgeCoverCheck] using hcover
    have hparts := Bool.and_eq_true_iff.mp hc
    have hadj : c.lo ≤ lo ∧ lo ≤ c.hi := of_decide_eq_true hparts.1
    have hchecks := Bool.and_eq_true_iff.mp (by simpa only [List.all_cons] using hcheck)
    by_cases hcell : Real.log n ≤ (c.hi : ℝ)
    · exact
        c.sound hchecks.1 hn ho hnp hp hq hr hpO hqO hrO hpq hqr hu hGRH hp5 hU
          (((Rat.cast_le (K := ℝ)).mpr hadj.1).trans hlo) hcell
    · have hnot : ¬hi ≤ c.hi := by
        intro h
        exact hcell (hhi.trans ((Rat.cast_le (K := ℝ)).mpr h))
      have hrest : lowBridgeCoverCheck c.hi hi cs = true := by
        rcases Bool.or_eq_true_iff.mp hparts.2 with hend | hnext
        · exact (hnot (of_decide_eq_true hend)).elim
        · exact hnext
      exact ih c.hi hrest hchecks.2 (le_of_lt (lt_of_not_ge hcell))

/-- The six checked blocks form the complete list of sixty low-bridge cells. -/
def lowBridgeCells : List LowBridgeCell :=
  lowBridgeCells0 ++ lowBridgeCells1 ++ lowBridgeCells2 ++ lowBridgeCells3 ++ lowBridgeCells4 ++
    lowBridgeCells5

/-- Every cell in the combined low-bridge list passes its rational check.
The six previously checked blocks are combined using the list append rule. -/
theorem lowBridgeCells_checked : lowBridgeCells.all LowBridgeCell.check = true := by
  simp only [lowBridgeCells, List.all_append, lowBridgeCells0_checked, lowBridgeCells1_checked,
    lowBridgeCells2_checked, lowBridgeCells3_checked, lowBridgeCells4_checked,
    lowBridgeCells5_checked, Bool.and_self]

set_option maxRecDepth 8192 in
/-- The sixty low-bridge cells cover the whole interval `[39.4,39.52]`.
The rational endpoint overlap check is evaluated by the kernel. -/
theorem lowBridgeCells_cover : lowBridgeCoverCheck (197 / 5) (988 / 25) lowBridgeCells = true := by
  decide +kernel

/-- An ordered odd uniform Korselt triple with logarithm in `[39.4,39.52]`
has a rejecting prime within the `3/10` cutoff under GRH. The prime three is
handled directly; otherwise the certified cells and their cover apply. -/
theorem uniformKorselt_reject_low_bridge {n p q r : ℕ} (hn : 1 < n) (ho : Odd n)
    (hnp : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p < q) (hqr : q < r)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (197 / 5 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 988 / 25) :
    ∃ a : ℕ,
      a.Prime ∧
        (a : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (a : ZMod n) := by
  have hpn : p ∣ n := hnp ▸ dvd_mul_of_dvd_left (dvd_mul_right p q) r
  have hqn : q ∣ n := hnp ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) r
  have hrn : r ∣ n := hnp ▸ dvd_mul_left r (p * q)
  have hp2 := ho.ne_two_of_dvd_nat hpn
  have hq2 := ho.ne_two_of_dvd_nat hqn
  have hr2 := ho.ne_two_of_dvd_nat hrn
  by_cases hp3 : p = 3
  · have hthree : 3 ∣ n := hp3 ▸ hpn
    have hbound : (3 : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
      nlinarith only [hL, sq_nonneg (Real.log n - 197 / 5)]
    exact
      ⟨3, Nat.prime_three, hbound,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho Nat.prime_three hthree⟩
  · have hp5 : 5 ≤ (p : ℝ) := by exact_mod_cast hp.five_le_of_ne_two_of_ne_three hp2 hp3
    apply
      lowBridgeCover_sound lowBridgeCells (197 / 5) (988 / 25) lowBridgeCells_cover
        lowBridgeCells_checked hn ho hnp hp hq hr (hp.odd_of_ne_two hp2) (hq.odd_of_ne_two hq2)
        (hr.odd_of_ne_two hr2) hpq hqr hu hGRH hp5 hU
    · norm_num only [Rat.cast_div, Rat.cast_ofNat]
      exact hL
    · norm_num only [Rat.cast_div, Rat.cast_ofNat]
      exact hU

/-- A three-element finite set of naturals admits an increasing enumeration.
Permuting the three distinct elements provides the factor ordering used below. -/
private theorem lowBridge_ordered_three_set (S : Finset ℕ) (hcard : S.card = 3) :
    ∃ p q r, p < q ∧ q < r ∧ S = {p, q, r} := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hcard
  rcases lt_or_gt_of_ne hpq with hpq' | hqp'
  · rcases lt_or_gt_of_ne hqr with hqr' | hrq'
    · exact ⟨p, q, r, hpq', hqr', hset⟩
    · rcases lt_or_gt_of_ne hpr with hpr' | hrp'
      · refine ⟨p, r, q, hpr', hrq', ?_⟩
        rw [hset]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm]
      · refine ⟨r, p, q, hrp', hpq', ?_⟩
        rw [hset]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]
  · rcases lt_or_gt_of_ne hpr with hpr' | hrp'
    · exact ⟨q, p, r, hqp', hpr', by simpa only [Finset.insert_comm] using hset⟩
    · rcases lt_or_gt_of_ne hqr with hqr' | hrq'
      · refine ⟨q, r, p, hqr', hrp', ?_⟩
        rw [hset]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]
      · refine ⟨r, q, p, hrq', hqp', ?_⟩
        rw [hset]
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]

/-- A uniform Korselt triple has three increasing prime factors whose product
is the input. Squarefreeness supplies the product and finite ordering chooses
the factors in the order required by the low-bridge spacing theorem. -/
theorem uniformKorselt_ordered_factors {n : ℕ} (hu : UniformKorseltTriple n) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ n = p * q * r := by
  obtain ⟨p, q, r, hpq, hqr, hset⟩ := lowBridge_ordered_three_set n.primeFactors hu.2.1
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hprod := (Nat.prod_primeFactors_of_squarefree hu.1).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    have hpq' : p ≠ q := ne_of_lt hpq
    have hpr' : p ≠ r := ne_of_lt (hpq.trans hqr)
    have hqr' : q ≠ r := ne_of_lt hqr
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq', hpr', hqr', or_self, not_false_eq_true, mul_assoc] using hprod
  exact ⟨p, q, r, hp, hq, hr, hpq, hqr, hnprod⟩

/-- Under GRH, every odd uniform Korselt triple on `[39.4,39.52]` has a
rejecting prime within the coefficient `3/10` cutoff. Order its prime factors
and apply the checked sixty-cell bridge. -/
theorem uniformKorselt_reject_394_3952 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (197 / 5 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 988 / 25) :
    ∃ a : ℕ,
      a.Prime ∧
        (a : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (a : ZMod n) := by
  obtain ⟨p, q, r, hp, hq, hr, hpq, hqr, hnp⟩ := uniformKorselt_ordered_factors hu
  exact uniformKorselt_reject_low_bridge hn ho hnp hp hq hr hpq hqr hu hGRH hL hU

end PseudoPrime.PrimeTestBounds.MillerRabin
