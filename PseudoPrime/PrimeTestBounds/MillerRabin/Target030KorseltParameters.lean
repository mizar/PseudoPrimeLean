/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple

/-! # Parameters for finite uniform Korselt triple classification -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A three-element finite set of naturals can be written in increasing order.
The finite case split only permutes the three distinct elements. -/
private theorem ordered_three_set (S : Finset ℕ) (hcard : S.card = 3) :
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

/-- If the predecessor of a positive factor divides the predecessor of a
positive product, it also divides the predecessor of the other factor. The
product is expanded using the factor predecessor for later Korselt reductions. -/
theorem korselt_predecessor_factor {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : b - 1 ∣ a * b - 1) :
    b - 1 ∣ a - 1 := by
  have hab : 1 ≤ a * b := Nat.mul_pos ha hb
  have h1 := congrArg (fun x : ℕ ↦ a * x) (Nat.sub_add_cancel hb)
  have h2 := Nat.sub_add_cancel ha
  have h3 := Nat.sub_add_cancel hab
  have hid : a * b - 1 = a * (b - 1) + (a - 1) := by nlinarith only [h1, h2, h3]
  rw [hid] at h
  exact (Nat.dvd_add_iff_right (dvd_mul_left (b - 1) a)).2 h

/-- For ordered integers above one, Korselt divisibility at the largest factor
provides an integer parameter between 1 and the smallest factor, satisfying
the exact quotient relation used in finite triple enumeration. -/
theorem korselt_parameter_exists {p q r : ℕ} (hp : 1 < p) (hpq : p < q) (hqr : q < r)
    (hk : r - 1 ∣ p * q * r - 1) : ∃ a : ℕ, 1 ≤ a ∧ a < p ∧ a * (r - 1) = p * q - 1 := by
  have hp1 : 1 ≤ p := hp.le
  have hq1 : 1 ≤ q := (hp.trans hpq).le
  have hr1 : 1 ≤ r := (hp.trans (hpq.trans hqr)).le
  have hpq1 : 1 ≤ p * q := Nat.mul_pos hp1 hq1
  have hn1 : 1 ≤ p * q * r := Nat.mul_pos hpq1 hr1
  have hrsub := Nat.sub_add_cancel hr1
  have hpqsub := Nat.sub_add_cancel hpq1
  have hnsub := Nat.sub_add_cancel hn1
  have hmul := congrArg (fun x : ℕ ↦ p * q * x) hrsub
  have hid : p * q * r - 1 = p * q * (r - 1) + (p * q - 1) := by
    nlinarith only [hmul, hpqsub, hnsub]
  rw [hid] at hk
  have hd : r - 1 ∣ p * q - 1 := (Nat.dvd_add_iff_right (dvd_mul_left (r - 1) (p * q))).2 hk
  obtain ⟨a, ha⟩ := hd
  have ha' : a * (r - 1) = p * q - 1 := by simpa only [Nat.mul_comm] using ha.symm
  have hap : 1 ≤ a := by
    by_contra hz
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos hz
    have hprod : 1 < p * q := by nlinarith only [hp, hpq]
    simp only [ha0, Nat.zero_mul] at ha'
    linarith only [ha', hpqsub, hprod]
  have hqsub : q ≤ r - 1 := Nat.le_sub_one_of_lt hqr
  have ham := Nat.mul_le_mul_left a hqsub
  have hlt : p * q - 1 < p * q := Nat.sub_lt (by linarith only [hpq1] : 0 < p * q) (by decide)
  have haplt : a < p := by nlinarith only [ham, ha', hlt, hq1]
  exact ⟨a, hap, haplt, ha'⟩

/-- The parameter relation and the middle-factor Korselt condition imply the
bounded divisor condition for the middle predecessor. Multiplying the quotient
equation gives the identity needed to remove a multiple of that predecessor. -/
theorem korselt_parameter_divisor {p q r a : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hrel : a * (r - 1) = p * q - 1) (hdiv : q - 1 ∣ p * r - 1) : q - 1 ∣ (p - 1) * (p + a) := by
  have hpq : 1 ≤ p * q := Nat.mul_pos hp hq
  have hpr : 1 ≤ p * r := Nat.mul_pos hp hr
  have h1 := congrArg (fun x : ℕ ↦ x * (p + a)) (Nat.sub_add_cancel hp)
  have h2 := congrArg (fun x : ℕ ↦ p ^ 2 * x) (Nat.sub_add_cancel hq)
  have h3 := congrArg (fun x : ℕ ↦ p * a * x) (Nat.sub_add_cancel hr)
  have h4 := congrArg (fun x : ℕ ↦ p * x) (Nat.sub_add_cancel hpq)
  have h5 := congrArg (fun x : ℕ ↦ a * x) (Nat.sub_add_cancel hpr)
  have hm := congrArg (fun x : ℕ ↦ p * x) hrel
  have hid : a * (p * r - 1) = p ^ 2 * (q - 1) + (p - 1) * (p + a) := by
    nlinarith only [h1, h2, h3, h4, h5, hm]
  have hd : q - 1 ∣ a * (p * r - 1) := dvd_mul_of_dvd_right hdiv a
  rw [hid] at hd
  exact (Nat.dvd_add_iff_right (dvd_mul_left (q - 1) (p ^ 2))).2 hd

/-- Ordered factors satisfying the middle and largest Korselt conditions admit
a positive parameter below the smallest factor and the two equations required
by the finite classification. The result supplies the forward enumeration map. -/
theorem korselt_ordered_parameters {p q r : ℕ} (hp : 1 < p) (hpq : p < q) (hqr : q < r)
    (hq : q - 1 ∣ p * q * r - 1) (hr : r - 1 ∣ p * q * r - 1) :
    ∃ a : ℕ, 1 ≤ a ∧ a < p ∧ a * (r - 1) = p * q - 1 ∧ q - 1 ∣ (p - 1) * (p + a) := by
  obtain ⟨a, ha, hap, heq⟩ := korselt_parameter_exists hp hpq hqr hr
  have hpr : 1 ≤ p * r := Nat.mul_pos hp.le (hp.trans (hpq.trans hqr)).le
  have hq1 : 1 ≤ q := (hp.trans hpq).le
  have hq' : q - 1 ∣ p * r * q - 1 := by simpa only [mul_assoc, mul_comm, mul_left_comm] using hq
  have hdiv := korselt_predecessor_factor hpr hq1 hq'
  exact
    ⟨a, ha, hap, heq, korselt_parameter_divisor hp.le hq1 (hp.trans (hpq.trans hqr)).le heq hdiv⟩

/-- A uniform Korselt triple with ordered prime factors admits the quotient
parameter and divisor condition used by the finite search. The two Korselt
divisibilities are extracted from the triple predicate. -/
theorem uniformKorselt_ordered_parameters {n p q r : ℕ} (hn : n = p * q * r) (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpq : p < q) (hqr : q < r) (hu : UniformKorseltTriple n) :
    ∃ a : ℕ, 1 ≤ a ∧ a < p ∧ a * (r - 1) = p * q - 1 ∧ q - 1 ∣ (p - 1) * (p + a) := by
  have hqn : q ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) r
  have hrn : r ∣ n := hn ▸ dvd_mul_left r (p * q)
  apply korselt_ordered_parameters hp.one_lt hpq hqr
  · simpa only [hn] using hu.2.2.1 q hq hqn
  · simpa only [hn] using hu.2.2.1 r hr hrn

/-- A positive quotient parameter satisfying the Korselt relation divides
`p * q - 1` and reconstructs the largest factor by exact natural division.
This supplies the last arithmetic step of the finite enumeration. -/
theorem korselt_parameter_reconstruct {p q r a : ℕ} (ha : 1 ≤ a) (hr : 1 ≤ r)
    (heq : a * (r - 1) = p * q - 1) : a ∣ p * q - 1 ∧ r = (p * q - 1) / a + 1 := by
  refine ⟨⟨r - 1, heq.symm⟩, ?_⟩
  rw [← heq, Nat.mul_div_cancel_left (r - 1) ha, Nat.sub_add_cancel hr]

/-- If three increasing natural factors have product at most `2^22`, their
smallest factor is at most 161. The cube of that factor is bounded by the
product, and the cube of 162 exceeds the input bound. -/
theorem ordered_triple_smallest_le_161 {n p q r : ℕ} (hn : n = p * q * r) (hpq : p < q)
    (hqr : q < r) (hbound : n ≤ 2 ^ 22) : p ≤ 161 := by
  have hpq' : p ≤ q := hpq.le
  have hpr' : p ≤ r := (hpq.trans hqr).le
  have hc : p ^ 3 ≤ n := by
    rw [hn, pow_succ, pow_two]
    exact Nat.mul_le_mul (Nat.mul_le_mul (le_refl p) hpq') hpr'
  by_contra h
  have h162 : 162 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
  have hpow := Nat.pow_le_pow_left h162 3
  norm_num only at hbound hpow
  have hnum : 2 ^ 22 < (162 : ℕ) ^ 3 := by norm_num only
  exact (not_le_of_gt hnum) (hpow.trans (hc.trans hbound))

/-- Every ordered uniform Korselt triple below `2^22` occurs among the finite
parameters with `p ≤ 161` and `1 ≤ a < p`. The divisor conditions and exact
formula reconstruct the remaining factors for the classification search. -/
theorem uniformKorselt_finite_parameters {n p q r : ℕ} (hn : n = p * q * r) (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpq : p < q) (hqr : q < r) (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) :
    p ≤ 161 ∧
      ∃ a : ℕ,
        1 ≤ a ∧ a < p ∧ q - 1 ∣ (p - 1) * (p + a) ∧ a ∣ p * q - 1 ∧ r = (p * q - 1) / a + 1 := by
  obtain ⟨a, ha, hap, heq, hdiv⟩ := uniformKorselt_ordered_parameters hn hp hq hr hpq hqr hu
  have hrec := korselt_parameter_reconstruct ha hr.one_lt.le heq
  exact ⟨ordered_triple_smallest_le_161 hn hpq hqr hbound, a, ha, hap, hdiv, hrec.1, hrec.2⟩

/-- Every uniform Korselt triple at most `2^22` has ordered prime factors and
appears in the bounded parameter search. Squarefreeness identifies the input
with the product of its three distinct prime factors. -/
theorem uniformKorselt_search_complete {n : ℕ} (hu : UniformKorseltTriple n) (hbound : n ≤ 2 ^ 22) :
    ∃ p q r a : ℕ,
      p.Prime ∧
        q.Prime ∧
        r.Prime ∧
        p < q ∧
        q < r ∧
        n = p * q * r ∧
        p ≤ 161 ∧
        1 ≤ a ∧ a < p ∧ q - 1 ∣ (p - 1) * (p + a) ∧ a ∣ p * q - 1 ∧ r = (p * q - 1) / a + 1 := by
  obtain ⟨p, q, r, hpq, hqr, hset⟩ := ordered_three_set n.primeFactors hu.2.1
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
  obtain ⟨hpbound, a, ha, hap, hdiv, hadiv, hrform⟩ :=
    uniformKorselt_finite_parameters hnprod hp hq hr hpq hqr hu hbound
  exact ⟨p, q, r, a, hp, hq, hr, hpq, hqr, hnprod, hpbound, ha, hap, hdiv, hadiv, hrform⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
