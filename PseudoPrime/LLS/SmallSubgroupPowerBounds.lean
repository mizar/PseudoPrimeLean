/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ExcludedPrimeCountLower
public import PseudoPrime.NumberTheory.PrimeProductSubgroupCounting
public import PseudoPrime.Analysis.SmallSubgroupLogarithmicBudget
public import PseudoPrime.LLS.PaperDefinitions

/-! # Unconditional log-power bounds for primes outside small subgroups -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For 0<beta<1 and A>1/(1-beta), sufficiently large q admits an eligible prime
outside every subgroup H of units with card H<=q^beta, bounded by log(q)^A.
Count products of distinct eligible small primes; strict logarithmic scale margins
force the count past card H. The threshold is uniform in H and no GRH is assumed. -/
theorem eventually_exists_prime_outside_le_log_power_of_card_rpow {beta A : ℝ} (hbeta : 0 < beta)
    (hb1 : beta < 1) (hA : 1 / (1 - beta) < A) :
    Filter.Eventually
      (fun q : ℕ ↦
        ∀ H : Subgroup (ZMod q)ˣ,
          (Nat.card H : ℝ) ≤ (q : ℝ) ^ beta →
            ∃ r : ℕ,
              r.Prime ∧
                ¬r ∣ q ∧ (r : ℝ) ≤ (Real.log q) ^ A ∧ ¬PaperStatements.residueInSubgroup q H r)
      Filter.atTop := by
  obtain ⟨b, c, hb, hbA, hc, hcA, hcb⟩ := Analysis.choose_subgroup_count_parameters hbeta hb1 hA
  have hAp : 0 < A := (zero_lt_one.trans hb).trans hbA
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hgap := hratio.eventually_lt_const (div_pos (sub_pos.mpr hcA) hAp)
  have hL : Filter.Tendsto (fun q : ℕ ↦ Real.log q) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hfloor :=
    hL.eventually (NumberTheory.eventually_rpow_le_nat_floor_rpow (b := 0) (by norm_num only) hAp)
  have hlogc := hL.eventually (Real.tendsto_log_atTop.eventually_ge_atTop (2 * c))
  filter_upwards [NumberTheory.eventually_log_power_le_card_coprime_primes hb hbA, hfloor, hlogc,
    hL.eventually hgap, hL.eventually_ge_atTop 2, Filter.eventually_gt_atTop (0 : ℕ)] with q hMp hf
    hcL hg hLp hq H hH
  let : NeZero q := ⟨hq.ne'⟩
  let L := Real.log (q : ℝ)
  let B := Nat.floor (L ^ A)
  let k := Nat.ceil (c * L / Real.log L)
  let S := B.primesLE \ q.primeFactors
  have hL2 : 2 ≤ L := hLp
  have hL1 : 1 < L := lt_of_lt_of_le (by norm_num only) hL2
  have hLpos : 0 < L := zero_lt_one.trans hL1
  have hBpos : 0 < B := by
    apply (Nat.cast_pos (α := ℝ)).mp
    have hcast : (1 : ℝ) ≤ B := by simpa only [Real.rpow_zero] using hf
    exact zero_lt_one.trans_le hcast
  obtain ⟨hk, hkL, hklo, hkhi⟩ := Analysis.ceil_log_scale_bounds hc hL2 hcL
  have hgapL : c * A * L + A * Real.log L < (1 : ℝ) * L := by
    have hm := (div_lt_div_iff₀ hLpos hAp).mp hg
    calc
      c * A * L + A * Real.log L < c * A * L + (1 - c * A) * L := by nlinarith only [hm]
      _ = (1 : ℝ) * L := by ring
  have hsize : B ^ k < q := by
    have ht :=
      Analysis.prime_power_product_lt_of_log_scale (a := 1) hq hBpos hL1 hAp
        (Nat.floor_le (Real.rpow_nonneg hLpos.le A)) rfl hkhi
        (by simpa only [Nat.cast_one] using hgapL)
    simpa only [pow_one] using ht
  have hcardpos : 0 < Nat.card H := Nat.card_pos
  have hlogH := Real.log_le_log (Nat.cast_pos.mpr hcardpos) hH
  rw [Real.log_rpow (Nat.cast_pos.mpr hq) beta] at hlogH
  have hbudget : Nat.card H * k ^ k < (S.card + 1 - k) ^ k :=
    Analysis.subgroup_power_budget_of_log_scale hcardpos hL1 hb hcb hk hkL hklo hMp hlogH
  obtain ⟨r, hrs, hr, hrB, hout⟩ :=
    NumberTheory.exists_prime_outside_of_card_lt_choose H S k B
      (fun r hr ↦ (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hr).1).2)
      (fun r hr ↦ (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hr).1).1) hsize
      (NumberTheory.card_lt_choose_of_power_budget hbudget)
  have hrd : ¬r ∣ q := fun hd ↦
    (Finset.mem_sdiff.mp hrs).2 (Nat.mem_primeFactors.mpr ⟨hr, hd, hq.ne'⟩)
  exact ⟨r, hr, hrd, (Nat.cast_le.mpr hrB).trans (Nat.floor_le (Real.rpow_nonneg hLpos.le A)), hout⟩

/-- For 0<eta<1 and A>1/eta, sufficiently large q admits a prime at most log(q)^A
not dividing q and outside every H with card H<=q^(1-eta). Substitute beta=1-eta
in the uniform cardinal-exponent bound. This is the small-subgroup LLS analogue. -/
theorem eventually_exists_prime_outside_le_log_power_of_small_card {eta A : ℝ} (he0 : 0 < eta)
    (he1 : eta < 1) (hA : 1 / eta < A) :
    Filter.Eventually
      (fun q : ℕ ↦
        ∀ H : Subgroup (ZMod q)ˣ,
          (Nat.card H : ℝ) ≤ (q : ℝ) ^ (1 - eta) →
            ∃ r : ℕ,
              r.Prime ∧
                ¬r ∣ q ∧ (r : ℝ) ≤ (Real.log q) ^ A ∧ ¬PaperStatements.residueInSubgroup q H r)
      Filter.atTop := by
  have hb0 : 0 < 1 - eta := sub_pos.mpr he1
  have hb1 : 1 - eta < 1 := by linarith only [he0]
  have he : 1 - (1 - eta) = eta := by ring
  have hA' : 1 / (1 - (1 - eta)) < A := by
    rw [he]; exact hA
  exact eventually_exists_prime_outside_le_log_power_of_card_rpow hb0 hb1 hA'

/-- Under the small-subgroup cardinality conditions, the least eligible prime
outside H is at most log(q)^A for all sufficiently large q, uniformly in H.
Minimize the primesOutside predicate after constructing one bounded prime. -/
theorem eventually_exists_least_prime_outside_le_log_power_of_small_card {eta A : ℝ} (he0 : 0 < eta)
    (he1 : eta < 1) (hA : 1 / eta < A) :
    Filter.Eventually
      (fun q : ℕ ↦
        ∀ H : Subgroup (ZMod q)ˣ,
          (Nat.card H : ℝ) ≤ (q : ℝ) ^ (1 - eta) →
            ∃ r ∈ PaperStatements.primesOutside q H,
              (r : ℝ) ≤ (Real.log q) ^ A ∧ ∀ s ∈ PaperStatements.primesOutside q H, r ≤ s)
      Filter.atTop := by
  classical
  apply (eventually_exists_prime_outside_le_log_power_of_small_card he0 he1 hA).mono
  intro q hq H hH
  obtain ⟨r, hr, hd, hb, ho⟩ := hq H hH
  have hex : ∃ s : ℕ, s ∈ PaperStatements.primesOutside q H := ⟨r, hr, hd, ho⟩
  exact
    ⟨Nat.find hex, Nat.find_spec hex, (Nat.cast_le.mpr (Nat.find_min' hex ⟨hr, hd, ho⟩)).trans hb,
      fun s hs ↦ Nat.find_min' hex hs⟩

end PseudoPrime.LLS
