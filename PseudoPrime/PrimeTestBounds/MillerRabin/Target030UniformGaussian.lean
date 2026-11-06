/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030High
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianVariableWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusRoots
public import PseudoPrime.LLS.GaussianPrefixSurplus

/-! # Variable-width Gaussian data for uniform Korselt triples -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At logarithmic scale at least 5250, the selected Gaussian radius meets the
radius and 50000-prefix cutoff requirements and stays within the 0.30 bound.
The proof compares the radius with its value at the entrance and checks the
cutoff coefficient by rational arithmetic. -/
theorem target030_gaussian_radius {L : ℝ} (hL : 5250 ≤ L) :
    let r := (377964473009 / 1000000000000 : ℝ) * L
    130 ≤ r ∧
      (50000 : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2 ∧ (21 / 10 : ℝ) * r ^ 2 ≤ (3 / 10 : ℝ) * L ^ 2 := by
  let r := (377964473009 / 1000000000000 : ℝ) * L
  change
    130 ≤ r ∧ (50000 : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2 ∧ (21 / 10 : ℝ) * r ^ 2 ≤ (3 / 10 : ℝ) * L ^ 2
  have hr : (1984 : ℝ) ≤ r := by
    dsimp only [r]
    linarith only [hL]
  have hr2 : (1984 : ℝ) ^ 2 ≤ r ^ 2 := (sq_le_sq₀ (by norm_num only) (by linarith only [hr])).2 hr
  have hc : (21 / 10 : ℝ) * (377964473009 / 1000000000000) ^ 2 ≤ 3 / 10 := by norm_num only
  have hsq : (0 : ℝ) ≤ L ^ 2 := sq_nonneg L
  refine ⟨by linarith only [hr], by nlinarith only [hr2], ?_⟩
  dsimp only [r]
  nlinarith only [mul_le_mul_of_nonneg_right hc hsq]

/-- At scale 5250 and above, rational endpoint certificates bound the square
root from below and the inverse eighth root from above. These estimates control
the Gaussian inverse-width term and tail throughout the high range. -/
theorem target030_gaussian_roots {L : ℝ} (hL : 5250 ≤ L) :
    let r := (377964473009 / 1000000000000 : ℝ) * L
    (4454563371 / 100000000 : ℝ) ≤ Real.sqrt r ∧
      r ^ (-(1 / 8 : ℝ)) ≤ (3870782017 / 10000000000 : ℝ) := by
  let r := (377964473009 / 1000000000000 : ℝ) * L
  change
    (4454563371 / 100000000 : ℝ) ≤ Real.sqrt r ∧ r ^ (-(1 / 8 : ℝ)) ≤ (3870782017 / 10000000000 : ℝ)
  have hr0 : (377964473009 / 1000000000000 : ℝ) * 5250 ≤ r := by
    dsimp only [r]
    linarith only [hL]
  have hcert :
    (4454563371 / 100000000 : ℝ) ^ 2 ≤ (377964473009 / 1000000000000 : ℝ) * 5250 ∧
      1 ≤ ((377964473009 / 1000000000000 : ℝ) * 5250) * (3870782017 / 10000000000 : ℝ) ^ 8 := by
    norm_num only [and_self]
  have hrpos : 0 < r := by linarith only [hr0]
  have hs : (4454563371 / 100000000 : ℝ) ≤ Real.sqrt r :=
    (Real.le_sqrt (by norm_num only) hrpos.le).2 (hcert.1.trans hr0)
  have h8 : 1 ≤ r * (3870782017 / 10000000000 : ℝ) ^ 8 :=
    hcert.2.trans (mul_le_mul_of_nonneg_right hr0 (pow_nonneg (by norm_num only) 8))
  exact ⟨hs, jointSurplus_invEighth_le hrpos (by norm_num only) h8⟩

/-- The rational upper bounds for the Gaussian losses leave a strict positive
margin at logarithmic scale 5250. The inverse eighth-root bound is included in
the last term, so the certificate retains the complete prefix-error tail. -/
theorem target030_gaussian_entry_margin :
    (20115621 / 25000000 : ℝ) * 5250 +
        (1598411439 / 700000000 : ℝ) *
          (((377964473009 / 1000000000000 : ℝ) * 5250) / (4454563371 / 100000000)) +
        (51613 / 1000 - 6 * (1129059 / 200000)) +
        42 * (2129 / 2000) / (5 * (7 / 20) * (4454563371 / 100000000)) +
        (2129 / 2000) * (19356 / 1000 + (7 / 2) * 5250) / ((377964473009 / 1000000000000) * 5250) +
        512 / (9 * ((377964473009 / 1000000000000) * 5250) ^ 2) +
        (1419 / 10) * (3870782017 / 10000000000) / ((377964473009 / 1000000000000) * 5250) <
      (10971611 / 5000000) * ((377964473009 / 1000000000000) * 5250) := by
  norm_num only

/-- The square root of the chosen radius is bounded by a linear function of
the radius on the whole range beginning at 5250. The lower root certificate
allows this estimate without replacing the entry value by a coarser constant. -/
theorem target030_gaussian_sqrt_le {L : ℝ} (hL : 5250 ≤ L) :
    Real.sqrt ((377964473009 / 1000000000000 : ℝ) * L) ≤
      ((377964473009 / 1000000000000 : ℝ) * L) / (4454563371 / 100000000) := by
  let r := (377964473009 / 1000000000000 : ℝ) * L
  have hs := (target030_gaussian_roots hL).1
  change (4454563371 / 100000000 : ℝ) ≤ Real.sqrt r at hs
  have hr : 0 ≤ r := by
    dsimp only [r]
    linarith only [hL]
  have hs2 := Real.sq_sqrt hr
  change Real.sqrt r ≤ r / (4454563371 / 100000000 : ℝ)
  apply (le_div_iff₀ (by norm_num only)).2
  have hm := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg r)
  nlinarith only [hm, hs2]

/-- The rational entry margin persists for every logarithmic scale at least
5250 after the square-root loss is replaced by its linear bound. All other
terms are held at their certified entrance values. -/
theorem target030_gaussian_margin {L : ℝ} (hL : 5250 ≤ L) :
    (20115621 / 25000000 : ℝ) * L +
        (1598411439 / 700000000 : ℝ) *
          (((377964473009 / 1000000000000 : ℝ) * L) / (4454563371 / 100000000)) +
        (51613 / 1000 - 6 * (1129059 / 200000)) +
        42 * (2129 / 2000) / (5 * (7 / 20) * (4454563371 / 100000000)) +
        (2129 / 2000) * (19356 / 1000 + (7 / 2) * 5250) / ((377964473009 / 1000000000000) * 5250) +
        512 / (9 * ((377964473009 / 1000000000000) * 5250) ^ 2) +
        (1419 / 10) * (3870782017 / 10000000000) / ((377964473009 / 1000000000000) * 5250) <
      (10971611 / 5000000) * ((377964473009 / 1000000000000) * L) := by
  have h := target030_gaussian_entry_margin
  linarith only [hL, h]

/-- At scale at least 5250, the full Gaussian residual is bounded by the
rational entrance value. The logarithmic quotient is constant because the
radius is proportional to the logarithm; the inverse powers and tail decrease. -/
theorem target030_gaussian_residual {n : ℕ} (hL : (5250 : ℝ) ≤ Real.log n) :
    let r := (377964473009 / 1000000000000 : ℝ) * Real.log n
    4 *
          (21 * (2129 / 2000 : ℝ) / (10 * (7 / 20 : ℝ) * Real.sqrt r) +
            1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
        13 +
        3 * LLS.PaperStatements.gaussianPrefixError (1129059 / 200000) n (r ^ 2) ≤
      (51613 / 1000 - 6 * (1129059 / 200000)) +
        42 * (2129 / 2000) / (5 * (7 / 20) * (4454563371 / 100000000)) +
        (2129 / 2000) * (19356 / 1000 + (7 / 2) * 5250) / ((377964473009 / 1000000000000) * 5250) +
        512 / (9 * ((377964473009 / 1000000000000) * 5250) ^ 2) +
        (1419 / 10) * (3870782017 / 10000000000) / ((377964473009 / 1000000000000) * 5250) := by
  let r := (377964473009 / 1000000000000 : ℝ) * Real.log n
  let r₀ : ℝ := (377964473009 / 1000000000000 : ℝ) * 5250
  let s₀ : ℝ := 4454563371 / 100000000
  let t₀ : ℝ := 3870782017 / 10000000000
  have hr : r₀ ≤ r := by
    dsimp only [r, r₀]
    linarith only [hL]
  have hr₀ : 0 < r₀ := by
    dsimp only [r₀]; norm_num only
  have hs₀ : 0 < s₀ := by
    dsimp only [s₀]; norm_num only
  have hrpos : 0 < r := hr₀.trans_le hr
  have hs : s₀ ≤ Real.sqrt r := (target030_gaussian_roots hL).1
  have ht : r ^ (-(1 / 8 : ℝ)) ≤ t₀ := (target030_gaussian_roots hL).2
  have hinvr : r⁻¹ ≤ r₀⁻¹ := (inv_le_inv₀ hrpos hr₀).2 hr
  have hinvs : (Real.sqrt r)⁻¹ ≤ s₀⁻¹ := (inv_le_inv₀ (Real.sqrt_pos.mpr hrpos) hs₀).2 hs
  have hw : 0 ≤ r⁻¹ := inv_nonneg.mpr hrpos.le
  have htail := mul_le_mul_of_nonneg_left ht hw
  have hw2 := mul_self_le_mul_self hw hinvr
  have hlog : Real.log n * r⁻¹ = (377964473009 / 1000000000000 : ℝ)⁻¹ := by
    dsimp only [r]
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (by linarith only [hL] : Real.log n ≠ 0), one_mul]
  change
    4 *
          (21 * (2129 / 2000 : ℝ) / (10 * (7 / 20 : ℝ) * Real.sqrt r) +
            1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
        13 +
        3 * LLS.PaperStatements.gaussianPrefixError (1129059 / 200000) n (r ^ 2) ≤
      _
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hrpos.le, jointSurplus_tail_eq hrpos]
  dsimp only [r₀, s₀, t₀] at *
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv] at *
  rw [← inv_pow, pow_two]
  norm_num only at *
  nlinarith only [hinvr, hinvs, hw2, htail, hlog]

/-- An odd uniform Korselt triple supplies an index-four subgroup containing
all strong-MR passing residues, with conductor-log sum exactly `2 log n`.
Enumerating the three prime factors connects the factorization predicate to
the existing common-sign subgroup construction. -/
theorem uniformKorselt_subgroup_data {n : ℕ} [NeZero n] (ho : Odd n) (hu : UniformKorseltTriple n) :
    ∃ H : Subgroup (ZMod n)ˣ,
      H.index = 4 ∧
        (∀ z : ZMod n,
          PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z) ∧
        LLS.PaperStatements.subgroupConductorLogSum H = 2 * Real.log n := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hu.2.1
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hpn := (Nat.mem_primeFactors.mp hpMem).2.1
  have hqn := (Nat.mem_primeFactors.mp hqMem).2.1
  have hrn := (Nat.mem_primeFactors.mp hrMem).2.1
  have hprod := (Nat.prod_primeFactors_of_squarefree hu.1).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
  exact
    three_prime_korselt_conductor_subgroup_data hp hq hr
      (hp.odd_of_ne_two (ho.ne_two_of_dvd_nat hpn)) (hq.odd_of_ne_two (ho.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (ho.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hu.2.2.1 p hp hpn)
      (hu.2.2.1 q hq hqn) (hu.2.2.1 r hr hrn) (hu.2.2.2 p q hp hq hpn hqn)
      (hu.2.2.2 p r hp hr hpn hrn)

/-- Under GRH, a uniform Korselt triple has a Gaussian rejecting-prime witness
at the specified radius when the 7/20-width prefix, cutoff, scalar budget and
residual conditions hold. Its conductor sum is supplied by the arithmetic
subgroup construction rather than assumed separately. -/
theorem uniformKorselt_gaussian_witness {n : ℕ} [NeZero n] (ho : Odd n) (hn : 20000 ≤ n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {P R r : ℝ} {N : ℕ} (hr : 130 ≤ r)
    (hprefix : P ≤ ∑ j ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight j)
    (hcut : (N : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2)
    (hbudget :
      (20115621 / 25000000 : ℝ) * Real.log n + R + (1598411439 / 700000000 : ℝ) * Real.sqrt r ≤
        (10971611 / 5000000 : ℝ) * r)
    (hres :
      4 *
            (21 * (2129 / 2000 : ℝ) / (10 * (7 / 20 : ℝ) * Real.sqrt r) +
              1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
          13 +
          3 * LLS.PaperStatements.gaussianPrefixError P n (r ^ 2) <
        R) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨H, hi, hpass, hC⟩ := uniformKorselt_subgroup_data ho hu
  exact gaussian_seven_twentieths_witness ho hn H hi hpass hGRH hC.le hr hprefix hcut hbudget hres

/-- A uniform Korselt triple above logarithmic scale 5250 has a rejecting
prime within the 0.30 cutoff when the remaining Gaussian budget and residual
inequalities hold. The radius and the 50000-prefix are supplied by their
certified bounds, leaving only the numerical error comparison. -/
theorem uniformKorselt_gaussian_03 {n : ℕ} [NeZero n] (ho : Odd n) (hn : 20000 ≤ n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5250 : ℝ) ≤ Real.log n) {R : ℝ}
    (hbudget :
      (20115621 / 25000000 : ℝ) * Real.log n + R +
          (1598411439 / 700000000 : ℝ) *
            Real.sqrt ((377964473009 / 1000000000000 : ℝ) * Real.log n) ≤
        (10971611 / 5000000 : ℝ) * ((377964473009 / 1000000000000 : ℝ) * Real.log n))
    (hres :
      4 *
            (21 * (2129 / 2000 : ℝ) /
                (10 * (7 / 20 : ℝ) * Real.sqrt ((377964473009 / 1000000000000 : ℝ) * Real.log n)) +
              1839 * (2129 / 2000 : ℝ) /
                (1000 * ((377964473009 / 1000000000000 : ℝ) * Real.log n))) +
          13 +
          3 *
            LLS.PaperStatements.gaussianPrefixError (1129059 / 200000) n
              (((377964473009 / 1000000000000 : ℝ) * Real.log n) ^ 2) <
        R) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hr := target030_gaussian_radius hL
  have hpref :
    (1129059 / 200000 : ℝ) ≤
      ∑ j ∈ Finset.Ioc 0 50000, Analysis.gaussianResolventMangoldtWeight j := by
    simpa only [Nat.floor_ofNat] using
      LLS.gaussian_prefix50000_surplus hGRH.riemann (le_refl (50000 : ℝ))
  obtain ⟨p, hp, hpbound, hreject⟩ :=
    uniformKorselt_gaussian_witness ho hn hu hGRH hr.1 hpref hr.2.1 hbudget hres
  exact ⟨p, hp, hpbound.trans hr.2.2, hreject⟩

/-- Under GRH, an odd uniform Korselt triple of logarithmic scale at least
5250 has a rejecting prime within the 0.30 bound. The rational entrance margin
and monotone residual bounds discharge the Gaussian budget at every such scale. -/
theorem uniformKorselt_reject_03_high {n : ℕ} [NeZero n] (ho : Odd n) (hn : 20000 ≤ n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5250 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let r := (377964473009 / 1000000000000 : ℝ) * Real.log n
  let E :=
    4 *
        (21 * (2129 / 2000 : ℝ) / (10 * (7 / 20 : ℝ) * Real.sqrt r) +
          1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
      13 +
      3 * LLS.PaperStatements.gaussianPrefixError (1129059 / 200000) n (r ^ 2)
  let B :=
    (10971611 / 5000000 : ℝ) * r - (20115621 / 25000000 : ℝ) * Real.log n -
      (1598411439 / 700000000 : ℝ) * Real.sqrt r
  have hres := target030_gaussian_residual hL
  have hmargin := target030_gaussian_margin hL
  have hroot := target030_gaussian_sqrt_le hL
  have hgap : E < B := by
    dsimp only [E, B, r]
    linarith only [hres, hmargin, hroot]
  obtain ⟨R, hR, hRup⟩ := exists_between hgap
  apply uniformKorselt_gaussian_03 ho hn hu hGRH hL (R := R)
  · dsimp only [B, r] at hRup
    linarith only [hRup]
  · exact hR

/-- Under GRH, every odd composite with logarithm at least 5250 has a
rejecting prime within the 0.30 bound. Split into uniform Korselt triples,
handled by the Gaussian margin, and the existing nonuniform index argument. -/
theorem exists_prime_reject_03_log5250 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (5250 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have h100 : (100 : ℝ) ≤ Real.log n := by linarith only [hL]
  by_cases hu : UniformKorseltTriple n
  · have hlarge : 20000 ≤ n :=
      (by norm_num only : (20000 : ℕ) ≤ 10 ^ 27).trans (ten_pow_27_le_of_log100 h100)
    exact uniformKorselt_reject_03_high ho hlarge hu hGRH hL
  · exact exists_prime_reject_03_nonuniform100 hn ho hc hGRH h100 hu

end PseudoPrime.PrimeTestBounds.MillerRabin
