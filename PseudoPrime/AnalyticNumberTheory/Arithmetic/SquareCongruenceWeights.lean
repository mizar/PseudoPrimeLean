/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
public import PseudoPrime.NumberTheory.SquareRootCounts

/-!
# Weighted square congruences

Combine the logarithmic weight cap with the residue-root count and quotient count.
The resulting sparse finite sum controls the even prime-power contribution in a
reduced residue class without RH or GRH.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Past the maximum of the quadratic logarithmic weight, increasing its argument
decreases the weight. Assume `0 < z ≤ y` and `log X ≤ 4 log z`.
Factor the difference into two nonnegative factors, without differentiating.
This controls weights by the left endpoints of half-period intervals. -/
theorem log_square_weight_antitone {X z y : ℝ} (hz : 0 < z) (hzy : z ≤ y)
    (hzX : Real.log X ≤ 4 * Real.log z) :
    Real.log y * (Real.log X - 2 * Real.log y) ≤ Real.log z * (Real.log X - 2 * Real.log z) := by
  have hl := Real.log_le_log hz hzy
  have hc : 0 ≤ 2 * Real.log y + 2 * Real.log z - Real.log X := by linarith only [hl, hzX]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hl) hc]

/-- A square Mangoldt weight beyond a positive lower endpoint is bounded by its
quadratic logarithmic weight at that endpoint. Assume `n > 0`, `n² ≤ X`,
`z ≤ n`, and `log X ≤ 4 log z`. Bound Mangoldt by `log n` and use decreasing weights.
This replaces the global weight maximum in later half-period blocks. -/
theorem square_log_weight_le_of_lower_bound {X z : ℝ} (hX : 0 < X) (hz : 0 < z) {n : ℕ} (hn : 0 < n)
    (hnX : (n : ℝ) ^ 2 ≤ X) (hzn : z ≤ n) (hzX : Real.log X ≤ 4 * Real.log z) :
    ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ) ^ 2) ≤
      Real.log z * (Real.log X - 2 * Real.log z) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog := Real.log_le_log (pow_pos hn0 2) hnX
  rw [Real.log_pow] at hlog
  have hm :=
    mul_le_mul_of_nonneg_right (ArithmeticFunction.vonMangoldt_le_log (n := n))
      (sub_nonneg.mpr hlog)
  rw [Real.log_div hX.ne' (pow_pos hn0 2).ne', Real.log_pow, Nat.cast_ofNat]
  exact hm.trans (log_square_weight_antitone hz hzn hzX)

/-- A finite block beyond the maximum point has total square weight bounded by
its cardinality times the nonnegative part of the left-endpoint weight.
Every index must be positive, at least `z`, and have its square at most `X`.
Sum the pointwise decreasing-weight estimate. Half-period counts can then bound the cardinality. -/
theorem square_log_weight_sum_le_of_lower_bound (s : Finset ℕ) {X z : ℝ} (hX : 0 < X) (hz : 0 < z)
    (hn : ∀ n ∈ s, 0 < n) (hnX : ∀ n ∈ s, (n : ℝ) ^ 2 ≤ X) (hzn : ∀ n ∈ s, z ≤ n)
    (hzX : Real.log X ≤ 4 * Real.log z) :
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ) ^ 2)) ≤
      (s.card : ℝ) * max 0 (Real.log z * (Real.log X - 2 * Real.log z)) := by
  calc
    _ ≤ ∑ _ ∈ s, max 0 (Real.log z * (Real.log X - 2 * Real.log z)) :=
      Finset.sum_le_sum
        (fun n hm ↦
          (square_log_weight_le_of_lower_bound hX hz (hn n hm) (hnX n hm) (hzn n hm) hzX).trans
            (le_max_right _ _))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- For positive cutoff X and positive n with n squared at most X, the Mangoldt-weighted
logarithm of X divided by n squared is at most log squared X divided by eight.
Bound Mangoldt by log n and complete the square in the quadratic logarithmic weight.
This is the individual even-prime-power weight estimate of LLS Section 4.1. -/
theorem square_log_weight_le {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : 0 < n) (hnX : (n : ℝ) ^ 2 ≤ X) :
    ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ) ^ 2) ≤ (Real.log X) ^ 2 / 8 := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog := Real.log_le_log (pow_pos hn0 2) hnX
  rw [Real.log_pow] at hlog
  have hw : 0 ≤ Real.log X - 2 * Real.log n := sub_nonneg.mpr hlog
  have hm := mul_le_mul_of_nonneg_right (ArithmeticFunction.vonMangoldt_le_log (n := n)) hw
  rw [Real.log_div hX.ne' (pow_pos hn0 2).ne', Real.log_pow]
  nlinarith only [hm, sq_nonneg (Real.log X - 4 * Real.log n)]

/-- For a nonzero modulus, unit residue and natural cutoff N with N squared at most X,
the square-congruence Mangoldt sum is bounded by the global residue-root count times
one plus the cutoff quotient and the individual logarithmic cap. Inject the selected
finite indices into bounded congruence solutions and sum the pointwise weight estimate.
This preserves the residue-class sparsity needed for the least-prime bound. -/
theorem square_congruence_weighted_sum_le {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (N : ℕ) {X : ℝ}
    (hX : 0 < X) (hNX : (N : ℝ) ^ 2 ≤ X) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ ↦ (n : ZMod q) ^ 2 = (a : ZMod q)),
        ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ) ^ 2)) ≤
      (2 ^ (q.primeFactors.card + 1) * (N / q + 1) : ℕ) * (Real.log X) ^ 2 / 8 := by
  classical
  let s := (Finset.Icc 1 N).filter (fun n : ℕ ↦ (n : ZMod q) ^ 2 = (a : ZMod q))
  let f : s → { n : ℕ // n ≤ N ∧ (n : ZMod q) ^ 2 = (a : ZMod q) } := fun n ↦
    ⟨n.val, (Finset.mem_Icc.mp (Finset.mem_filter.mp n.property).1).2,
      (Finset.mem_filter.mp n.property).2⟩
  have hf : Function.Injective f := by
    intro m n hmn
    apply Subtype.ext
    exact congrArg (fun z : { n : ℕ // n ≤ N ∧ (n : ZMod q) ^ 2 = (a : ZMod q) } ↦ z.val) hmn
  let : Finite { n : ℕ // n ≤ N ∧ (n : ZMod q) ^ 2 = (a : ZMod q) } :=
    ((Set.finite_Iic N).subset (fun _ hn ↦ hn.1)).to_subtype
  have hc :=
    (Nat.card_le_card_of_injective f hf).trans (NumberTheory.card_sq_congruence_le_primeFactors a N)
  have hcard : s.card ≤ 2 ^ (q.primeFactors.card + 1) * (N / q + 1) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc
  have hsum :
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ) ^ 2)) ≤
      ∑ _ ∈ s, (Real.log X) ^ 2 / 8 := by
    apply Finset.sum_le_sum
    intro n hn
    have hni := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hnN : (n : ℝ) ≤ N := Nat.cast_le.mpr hni.2
    have hnX : (n : ℝ) ^ 2 ≤ X := by
      nlinarith only [hnN, (Nat.cast_nonneg n : (0 : ℝ) ≤ n), (Nat.cast_nonneg N : (0 : ℝ) ≤ N),
        hNX]
    exact square_log_weight_le hX (Nat.zero_lt_one.trans_le hni.1) hnX
  have hm :=
    mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr hcard : (s.card : ℝ) ≤ (2 ^ (q.primeFactors.card + 1) * (N / q + 1) : ℕ))
      (div_nonneg (sq_nonneg (Real.log X)) (by norm_num only : (0 : ℝ) ≤ 8))
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  exact hsum.trans (by simpa only [mul_div_assoc] using hm)

/-- For a positive real cutoff and unit residue modulo a nonzero modulus, the Mangoldt
sum on square roots through the cutoff square root is at most two to one plus the
prime-factor count times log squared X divided by eight times square root X over q plus one.
Apply the natural-cutoff bound and replace the floor quotient by the real quotient.
This is the sparse square contribution used for the even prime powers in LLS Section 4.1. -/
theorem square_congruence_weighted_sum_le_sqrt {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) {X : ℝ}
    (hX : 0 < X) :
    (∑ n ∈ (Finset.Icc 1 ⌊Real.sqrt X⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) ^ 2 = (a : ZMod q)),
        ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ) ^ 2)) ≤
      (2 : ℝ) ^ (q.primeFactors.card + 1) * (Real.log X) ^ 2 / 8 * (Real.sqrt X / q + 1) := by
  have hf : (⌊Real.sqrt X⌋₊ : ℝ) ≤ Real.sqrt X := Nat.floor_le (Real.sqrt_nonneg X)
  have hs := Real.sq_sqrt hX.le
  have hfloor : (⌊Real.sqrt X⌋₊ : ℝ) ^ 2 ≤ X := by
    nlinarith only [hf, hs, Real.sqrt_nonneg X,
      (Nat.cast_nonneg ⌊Real.sqrt X⌋₊ : (0 : ℝ) ≤ ⌊Real.sqrt X⌋₊)]
  have hsum := square_congruence_weighted_sum_le a ⌊Real.sqrt X⌋₊ hX hfloor
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hd : (⌊Real.sqrt X⌋₊ / q : ℕ) ≤ Real.sqrt X / q :=
    (Nat.cast_div_le (m := ⌊Real.sqrt X⌋₊) (n := q)).trans (div_le_div_of_nonneg_right hf hq.le)
  have hm :=
    mul_le_mul_of_nonneg_left (add_le_add_right hd 1)
      (div_nonneg
        (mul_nonneg (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (q.primeFactors.card + 1))
          (sq_nonneg (Real.log X)))
        (by norm_num only : (0 : ℝ) ≤ 8))
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at hsum
  exact hsum.trans (by nlinarith only [hm])

open Classical in
/-- For a positive real cutoff, the Mangoldt sum on square indices in one residue class
equals the square-root congruence sum. Squaring bijects the two finite index sets and
Mangoldt is unchanged by squaring. This connects the local root count to the actual
even-prime-power contribution in the residue-class weighted sum. -/
theorem square_residue_sum_eq_root_sum {q : ℕ} (a : ZMod q) {X : ℝ} (hX : 0 < X) :
    (∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n : ℕ ↦ IsSquare n ∧ (n : ZMod q) = a),
        ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ))) =
      ∑ m ∈ (Finset.Icc 1 ⌊Real.sqrt X⌋₊).filter (fun m : ℕ ↦ (m : ZMod q) ^ 2 = a),
        ArithmeticFunction.vonMangoldt m * Real.log (X / (m : ℝ) ^ 2) := by
  classical
  symm
  apply Finset.sum_bij (fun m _ ↦ m ^ 2)
  · intro m hm
    obtain ⟨hmi, hma⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hmi
    have hmS : (m : ℝ) ≤ Real.sqrt X :=
      (Nat.cast_le.mpr hmN).trans (Nat.floor_le (Real.sqrt_nonneg X))
    have hmX : (m : ℝ) ^ 2 ≤ X := by
      nlinarith only [hmS, Real.sqrt_nonneg X, Real.sq_sqrt hX.le,
        (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · exact Nat.succ_le_of_lt (pow_pos (Nat.zero_lt_one.trans_le hm1) 2)
    · exact Nat.le_floor (by simpa only [Nat.cast_pow] using hmX)
    · exact ⟨m, pow_two m⟩
    · simpa only [Nat.cast_pow] using hma
  · intro m hm n hn he
    exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) he
  · intro n hn
    obtain ⟨hni, hs, hna⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hni
    obtain ⟨m, hm⟩ := hs
    have he : m ^ 2 = n := by simpa only [pow_two] using hm.symm
    have hmpos : 0 < m := by nlinarith only [hn1, he]
    have hmX : (m : ℝ) ^ 2 ≤ X := by
      rw [← Nat.cast_pow, he]
      exact (Nat.cast_le.mpr hnX).trans (Nat.floor_le hX.le)
    have hmS : m ≤ ⌊Real.sqrt X⌋₊ := Nat.le_floor ((Real.le_sqrt (Nat.cast_nonneg m) hX.le).mpr hmX)
    have hma : (m : ZMod q) ^ 2 = a := by
      rw [← Nat.cast_pow, he]
      exact hna
    refine ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hmpos, hmS⟩, hma⟩, he⟩
  · intro m hm
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide : (2 : ℕ) ≠ 0), Nat.cast_pow]

open Classical in
/-- For a nonzero modulus, unit residue and positive cutoff, the square-index Mangoldt
contribution is at most two to the prime-factor count times log squared X divided by
four times square root X over q plus one. Reindex by square roots and apply the sparse
weighted congruence bound. This proves the even-power estimate of LLS Section 4.1
before replacing the prime-factor factor by a power of the modulus. -/
theorem square_residue_sum_le {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) {X : ℝ} (hX : 0 < X) :
    (∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n : ℕ ↦ IsSquare n ∧ (n : ZMod q) = (a : ZMod q)),
        ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ))) ≤
      (2 : ℝ) ^ q.primeFactors.card * (Real.log X) ^ 2 / 4 * (Real.sqrt X / q + 1) := by
  rw [square_residue_sum_eq_root_sum (a : ZMod q) hX]
  calc
    _ ≤ (2 : ℝ) ^ (q.primeFactors.card + 1) * (Real.log X) ^ 2 / 8 * (Real.sqrt X / q + 1) :=
      square_congruence_weighted_sum_le_sqrt a hX
    _ = _ := by
      rw [pow_succ]
      ring

open Classical in
/-- For modulus greater than two and a unit residue, sum weights bounded by a
nonnegative constant over square roots in either half of one quotient period.
A residue-root bound `r` gives at most `r/2` terms by negation pairing.
This converts half-period root counts into weighted square-congruence estimates. -/
theorem square_congruence_half_period_sum_le {q r : ℕ} [NeZero q] (hq : 2 < q) (a : (ZMod q)ˣ)
    (hroot : Nat.card { x : ZMod q // x ^ 2 = (a : ZMod q) } ≤ r) (s : Finset ℕ) (k : ℕ)
    (lower : Bool)
    (hperiod :
      ∀ n ∈ s,
        n / q = k ∧
          (n : ZMod q) ^ 2 = (a : ZMod q) ∧ (if lower then 2 * (n % q) < q else ¬2 * (n % q) < q))
    (F : ℕ → ℝ) {W : ℝ} (hW : 0 ≤ W) (hF : ∀ n ∈ s, F n ≤ W) :
    (∑ n ∈ s, F n) ≤ (r : ℝ) / 2 * W := by
  let R := { x : ZMod q // x ^ 2 = (a : ZMod q) }
  let P := fun x : R ↦ if lower then 2 * x.val.val < q else ¬2 * x.val.val < q
  let f : s → { x : R // P x } := fun n ↦
    ⟨⟨(n.val : ZMod q), (hperiod n.val n.property).2.1⟩, by
      simpa only [P, ZMod.val_natCast] using (hperiod n.val n.property).2.2⟩
  have hf : Function.Injective f := by
    intro m n h
    apply Subtype.ext
    have hm : (m.val : ZMod q) = (n.val : ZMod q) := congrArg (fun x ↦ x.val.val) h
    have hd : m.val / q = n.val / q :=
      (hperiod m.val m.property).1.trans (hperiod n.val n.property).1.symm
    have hr : m.val % q = n.val % q := by simpa only [ZMod.val_natCast] using congrArg ZMod.val hm
    calc
      m.val = m.val % q + q * (m.val / q) := (Nat.mod_add_div _ _).symm
      _ = n.val % q + q * (n.val / q) := by rw [hr, hd]
      _ = n.val := Nat.mod_add_div _ _
  have hc : s.card ≤ (Finset.univ.filter P).card := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_subtype] using
      Nat.card_le_card_of_injective f hf
  have he : 2 * (Finset.univ.filter P).card = Nat.card R := by
    cases lower with
    | false => exact PseudoPrime.NumberTheory.two_mul_card_sq_roots_upper_half hq a
    | true => exact PseudoPrime.NumberTheory.two_mul_card_sq_roots_lower_half hq a
  have hcr : 2 * s.card ≤ r := (Nat.mul_le_mul_left 2 hc).trans (he.le.trans hroot)
  have hcReal : (2 : ℝ) * (s.card : ℝ) ≤ r := by exact_mod_cast hcr
  have hrReal : (s.card : ℝ) ≤ (r : ℝ) / 2 := by nlinarith only [hcReal]
  have hs : (∑ n ∈ s, F n) ≤ (s.card : ℝ) * W := by
    calc
      _ ≤ ∑ _ ∈ s, W := Finset.sum_le_sum hF
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  exact hs.trans (mul_le_mul_of_nonneg_right hrReal hW)

/-- For positive cutoff and left endpoint beyond the weight maximum, bound the
Mangoldt-weighted square roots in a half period by `r/2` times the nonnegative
left-endpoint weight. All indices must be positive, at least the endpoint, and
have square at most the cutoff. Apply the decreasing pointwise weight bound.
This retains the decay in successive half-period blocks. -/
theorem square_congruence_half_period_weighted_sum_le_of_lower_bound {q r : ℕ} [NeZero q]
    (hq : 2 < q) (a : (ZMod q)ˣ) (hroot : Nat.card { x : ZMod q // x ^ 2 = (a : ZMod q) } ≤ r)
    (s : Finset ℕ) (k : ℕ) (lower : Bool)
    (hperiod :
      ∀ n ∈ s,
        n / q = k ∧
          (n : ZMod q) ^ 2 = (a : ZMod q) ∧ (if lower then 2 * (n % q) < q else ¬2 * (n % q) < q))
    {X z : ℝ} (hX : 0 < X) (hz : 0 < z) (hn : ∀ n ∈ s, 0 < n) (hnX : ∀ n ∈ s, (n : ℝ) ^ 2 ≤ X)
    (hzn : ∀ n ∈ s, z ≤ n) (hzX : Real.log X ≤ 4 * Real.log z) :
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ) ^ 2)) ≤
      (r : ℝ) / 2 * max 0 (Real.log z * (Real.log X - 2 * Real.log z)) := by
  apply
    square_congruence_half_period_sum_le hq a hroot s k lower hperiod
      (fun n ↦ ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ) ^ 2)) (le_max_left _ _)
  intro n hm
  exact
    (square_log_weight_le_of_lower_bound hX hz (hn n hm) (hnX n hm) (hzn n hm) hzX).trans
      (le_max_right _ _)

/-- For positive cutoff, bound a half period of positive square roots below its
square-root cutoff by `r/2 * log² X/8`, given a residue-root bound `r`.
Combine the global quadratic weight maximum with the half-period root count.
This supplies the initial block before the decreasing-weight estimates apply. -/
theorem square_congruence_half_period_weighted_sum_le {q r : ℕ} [NeZero q] (hq : 2 < q)
    (a : (ZMod q)ˣ) (hroot : Nat.card { x : ZMod q // x ^ 2 = (a : ZMod q) } ≤ r) (s : Finset ℕ)
    (k : ℕ) (lower : Bool)
    (hperiod :
      ∀ n ∈ s,
        n / q = k ∧
          (n : ZMod q) ^ 2 = (a : ZMod q) ∧ (if lower then 2 * (n % q) < q else ¬2 * (n % q) < q))
    {X : ℝ} (hX : 0 < X) (hn : ∀ n ∈ s, 0 < n) (hnX : ∀ n ∈ s, (n : ℝ) ^ 2 ≤ X) :
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ) ^ 2)) ≤
      (r : ℝ) / 2 * ((Real.log X) ^ 2 / 8) := by
  apply
    square_congruence_half_period_sum_le hq a hroot s k lower hperiod
      (fun n ↦ ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ) ^ 2))
      (div_nonneg (sq_nonneg _) (by norm_num only : (0 : ℝ) ≤ 8))
  intro n hm
  exact square_log_weight_le hX (hn n hm) (hnX n hm)

/-- The doubled quotient equals twice the ordinary quotient, plus one exactly
when the remainder lies in the upper half. Division with remainder and the two
remainder ranges prove this identity, used to index half-period blocks. -/
private theorem twice_div_eq_half_period_index {q : ℕ} [NeZero q] (n : ℕ) :
    (2 * n) / q = 2 * (n / q) + if 2 * (n % q) < q then 0 else 1 := by
  have hs := Nat.mod_add_div n q
  have hr := Nat.mod_lt n (NeZero.pos q)
  by_cases h : 2 * (n % q) < q
  · rw [ite_eq_left h, add_zero]
    apply Nat.div_eq_of_lt_le
    · nlinarith only [hs, Nat.zero_le (n % q)]
    · nlinarith only [hs, h]
  · rw [ite_eq_right h]
    have hl : q ≤ 2 * (n % q) := Nat.le_of_not_gt h
    apply Nat.div_eq_of_lt_le
    · nlinarith only [hs, hl]
    · nlinarith only [hs, hr]

/-- The doubled quotient index determines the ordinary quotient and whether
the representative lies in its lower or upper half. Split on the remainder comparison.
This assigns each integer square root to the half-period used in the finite partition. -/
private theorem half_period_index_quotient_and_side {q : ℕ} [NeZero q] (n j : ℕ)
    (hj : (2 * n) / q = j) :
    n / q = j / 2 ∧ (if decide (j % 2 = 0) then 2 * (n % q) < q else ¬2 * (n % q) < q) := by
  have hid := twice_div_eq_half_period_index (q := q) n
  rw [hj] at hid
  by_cases h : 2 * (n % q) < q
  · rw [ite_eq_left h, add_zero] at hid
    have hq : j / 2 = n / q := by
      apply Nat.div_eq_of_lt_le
      · nlinarith only [hid]
      · nlinarith only [hid]
    have he : j % 2 = 0 := by rw [hid, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod]
    exact ⟨hq.symm, by simpa only [he, decide_true, ite_true] using h⟩
  · rw [ite_eq_right h] at hid
    have hq : j / 2 = n / q := by
      apply Nat.div_eq_of_lt_le
      · nlinarith only [hid]
      · nlinarith only [hid]
    have he : j % 2 ≠ 0 := by
      rw [hid, Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod, zero_add]
      norm_num only
    exact ⟨hq.symm, by simpa only [he, decide_false, Bool.false_eq_true, ite_false] using h⟩

open Classical in
/-- For modulus greater than two and a unit residue, sum square-congruence weights
using one nonnegative majorant per half period. Every index must lie in a half period
at most `J`, and its weight must be bounded by that period's supplied majorant.
Partition by `floor(2*n/q)`, apply the `r/2` root count in each block, and sum.
This is the finite-sum interface for the refined small-modulus square contribution. -/
theorem square_congruence_sum_le_half_period_majorants {q r : ℕ} [NeZero q] (hq : 2 < q)
    (a : (ZMod q)ˣ) (hroot : Nat.card { x : ZMod q // x ^ 2 = (a : ZMod q) } ≤ r) (s : Finset ℕ)
    (J : ℕ) (hJ : ∀ n ∈ s, (2 * n) / q ≤ J) (hsquare : ∀ n ∈ s, (n : ZMod q) ^ 2 = (a : ZMod q))
    (F : ℕ → ℝ) (W : ℕ → ℝ) (hW : ∀ j ≤ J, 0 ≤ W j) (hF : ∀ n ∈ s, F n ≤ W ((2 * n) / q)) :
    (∑ n ∈ s, F n) ≤ (r : ℝ) / 2 * ∑ j ∈ Finset.range (J + 1), W j := by
  have hsum :=
    Finset.sum_fiberwise_of_maps_to (fun n hn ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (hJ n hn)))
      F
  rw [← hsum]
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1), (r : ℝ) / 2 * W j := by
      apply Finset.sum_le_sum
      intro j hj
      apply
        square_congruence_half_period_sum_le hq a hroot (s.filter (fun n ↦ (2 * n) / q = j)) (j / 2)
          (decide (j % 2 = 0))
      · intro n hn
        have hs := Finset.mem_filter.mp hn
        have hi := half_period_index_quotient_and_side n j hs.2
        exact ⟨hi.1, hsquare n hs.1, hi.2⟩
      · exact hW j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      · intro n hn
        have hs := Finset.mem_filter.mp hn
        rw [← hs.2]
        exact hF n hs.1
    _ = _ := by rw [Finset.mul_sum]

open Classical in
/-- For a unit residue modulo a modulus greater than two, bound the weighted
square-congruence sum by `r/2` times its half-period endpoint majorants.
All indices are positive, have square at most `X`, and have half-period index at most
`J`; assume the first positive endpoint `q/2` is beyond the weight maximum.
Use the global maximum in period zero and the decreasing weight at `j*q/2` thereafter.
This gives the finite analytic square estimate used in the refined residue certificates. -/
theorem square_congruence_weighted_sum_le_half_periods {q r : ℕ} [NeZero q] (hq : 2 < q)
    (a : (ZMod q)ˣ) (hroot : Nat.card { x : ZMod q // x ^ 2 = (a : ZMod q) } ≤ r) (s : Finset ℕ)
    (J : ℕ) (hJ : ∀ n ∈ s, (2 * n) / q ≤ J) (hsquare : ∀ n ∈ s, (n : ZMod q) ^ 2 = (a : ZMod q))
    {X : ℝ} (hX : 0 < X) (hn : ∀ n ∈ s, 0 < n) (hnX : ∀ n ∈ s, (n : ℝ) ^ 2 ≤ X)
    (hbase : Real.log X ≤ 4 * Real.log ((q : ℝ) / 2)) :
    (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ) ^ 2)) ≤
      (r : ℝ) / 2 *
        ∑ j ∈ Finset.range (J + 1),
          if j = 0 then (Real.log X) ^ 2 / 8
          else
            max 0 (Real.log ((j : ℝ) * q / 2) * (Real.log X - 2 * Real.log ((j : ℝ) * q / 2))) := by
  apply
    square_congruence_sum_le_half_period_majorants hq a hroot s J hJ hsquare
      (fun n ↦ ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ) ^ 2))
  · intro j _
    by_cases hj : j = 0
    · rw [ite_eq_left hj]
      exact div_nonneg (sq_nonneg _) (by norm_num only : (0 : ℝ) ≤ 8)
    · rw [ite_eq_right hj]
      exact le_max_left _ _
  · intro n hm
    by_cases hj : (2 * n) / q = 0
    · rw [ite_eq_left hj]
      exact square_log_weight_le hX (hn n hm) (hnX n hm)
    · rw [ite_eq_right hj]
      have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
      have hj1 : (1 : ℝ) ≤ (((2 * n) / q : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
      have hleft : ((q : ℝ) / 2) ≤ (((2 * n) / q : ℕ) : ℝ) * q / 2 := by nlinarith only [hq0, hj1]
      have hz : (0 : ℝ) < (((2 * n) / q : ℕ) : ℝ) * q / 2 :=
        lt_of_lt_of_le (div_pos hq0 (by norm_num only)) hleft
      have hmul : (((2 * n) / q : ℕ) : ℝ) * q ≤ 2 * n := by
        exact_mod_cast (Nat.le_div_iff_mul_le (NeZero.pos q)).mp (le_refl ((2 * n) / q))
      have hzn : (((2 * n) / q : ℕ) : ℝ) * q / 2 ≤ n := by linarith only [hmul]
      have hl := Real.log_le_log (div_pos hq0 (by norm_num only)) hleft
      have hzX : Real.log X ≤ 4 * Real.log ((((2 * n) / q : ℕ) : ℝ) * q / 2) := by
        linarith only [hbase, hl]
      exact
        (square_log_weight_le_of_lower_bound hX hz (hn n hm) (hnX n hm) hzn hzX).trans
          (le_max_right _ _)

open Classical in
/-- For a positive cutoff and unit residue modulo a modulus greater than two,
bound the actual square-index Mangoldt contribution by the half-period majorants.
Supply a root-count bound, an upper half-period index at floor sqrt X, and the
decreasing-weight condition at q/2. Reindex squares by their roots, bound the root
indices by floor sqrt X, and apply the half-period estimate.
This connects the square estimate to the residue-class prime-power decomposition. -/
theorem square_residue_sum_le_half_periods {q r : ℕ} [NeZero q] (hq : 2 < q) (a : (ZMod q)ˣ)
    (hroot : Nat.card { z : ZMod q // z ^ 2 = (a : ZMod q) } ≤ r) {X : ℝ} (hX : 0 < X) (J : ℕ)
    (hJ : (2 * ⌊Real.sqrt X⌋₊) / q ≤ J) (hbase : Real.log X ≤ 4 * Real.log ((q : ℝ) / 2)) :
    (∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n : ℕ ↦ IsSquare n ∧ (n : ZMod q) = (a : ZMod q)),
        ArithmeticFunction.vonMangoldt n * Real.log (X / (n : ℝ))) ≤
      (r : ℝ) / 2 *
        ∑ j ∈ Finset.range (J + 1),
          if j = 0 then (Real.log X) ^ 2 / 8
          else
            max 0 (Real.log ((j : ℝ) * q / 2) * (Real.log X - 2 * Real.log ((j : ℝ) * q / 2))) := by
  rw [square_residue_sum_eq_root_sum (a : ZMod q) hX]
  apply square_congruence_weighted_sum_le_half_periods hq a hroot _ J
  · intro n hn
    exact
      (Nat.div_le_div_right
            (Nat.mul_le_mul_left 2 (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2)).trans
        hJ
  · intro n hn
    exact (Finset.mem_filter.mp hn).2
  · exact hX
  · intro n hn
    exact Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  · intro n hn
    have hnS :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2).trans
        (Nat.floor_le (Real.sqrt_nonneg X))
    nlinarith only [hnS, Real.sqrt_nonneg X, Real.sq_sqrt hX.le, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · exact hbase

end PseudoPrime.AnalyticNumberTheory.Arithmetic
