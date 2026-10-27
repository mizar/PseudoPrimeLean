/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaFiniteEulerRowBlocks

/-! # Arithmetic support certificates for finite Gamma Euler upper bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A positive power of a prime times a coprime tail different from
one is not a prime power. Any prime-power representation would have the
same prime base; its tail would divide that prime power and itself, hence
be one by coprimality. This justifies zero rows in a support census. -/
theorem not_prime_power_of_coprime_tail {n p e q : ℕ} (hp : p.Prime) (he : 0 < e) (hq : q ≠ 1)
    (hc : p.Coprime q) (hn : n = p ^ e * q) : ¬IsPrimePow n := by
  intro h
  obtain ⟨r, k, hr, _, hpow⟩ := (isPrimePow_nat_iff n).mp h
  have hpn : p ∣ n := by
    rw [hn]
    exact (dvd_pow_self p he.ne').trans (dvd_mul_right (p ^ e) q)
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow (hpow.symm ▸ hpn))
  subst r
  have hqn : q ∣ n := by
    rw [hn]
    exact dvd_mul_left q (p ^ e)
  have hqp : q ∣ p ^ k := by
    rw [hpow]
    exact hqn
  exact hq (Nat.eq_one_of_dvd_coprimes (hc.pow_left k) hqp (dvd_refl q))

/-- For a positive prime power times a coprime tail, the input is
a prime power exactly when the tail is one. Use the exclusion lemma in
one direction and the positive prime-power representation in the other. -/
theorem prime_power_iff_coprime_tail_eq_one {n p e q : ℕ} (hp : p.Prime) (he : 0 < e)
    (hc : p.Coprime q) (hn : n = p ^ e * q) : IsPrimePow n ↔ q = 1 := by
  constructor
  · intro h
    by_contra hq
    exact not_prime_power_of_coprime_tail hp he hq hc hn h
  · intro hq
    rw [hn, hq, mul_one]
    exact hp.isPrimePow.pow he.ne'

/-- Integer decomposition data for one finite support input.
The fields record the input, a prime base, its exponent, and the residual
tail. A valid nonunit row has positive exponent, coprime base and tail,
and input equal to the prime power times the tail. Unit rows are inactive. -/
structure GammaArithmeticSupportRow where
  index : ℕ
  prime : ℕ
  exponent : ℕ
  tail : ℕ

/-- Check the arithmetic decomposition of a support row, allowing
input one as a separate inactive case. Primality of the base is certified
separately. This check uses integer powers and greatest common divisors. -/
def GammaArithmeticSupportRow.check (r : GammaArithmeticSupportRow) : Bool :=
  decide
    (r.index = 1 ∨
      (0 < r.exponent ∧ r.prime.Coprime r.tail ∧ r.index = r.prime ^ r.exponent * r.tail))

/-- Mark nonunit rows whose residual tail is one. For a valid
row with a prime base, this computable flag is equivalent to prime-power
support. The census compares active inputs with the numerical row indices. -/
def GammaArithmeticSupportRow.active (r : GammaArithmeticSupportRow) : Bool :=
  decide (r.index ≠ 1 ∧ r.tail = 1)

/-- A valid arithmetic row with a prime base is supported by
Mangoldt exactly when its active flag is true. Separate input one and
apply the coprime-tail characterization to all other rows. -/
theorem GammaArithmeticSupportRow.prime_power_iff (r : GammaArithmeticSupportRow)
    (hp : r.prime.Prime) (hc : r.check = true) : IsPrimePow r.index ↔ r.active = true := by
  have h := of_decide_eq_true hc
  by_cases hi : r.index = 1
  · simp only [not_isPrimePow_one, GammaArithmeticSupportRow.active, hi, ne_eq, not_true_eq_false,
      false_and, decide_false, Bool.false_eq_true]
  · obtain ⟨he, hcop, heq⟩ := h.resolve_left hi
    rw [prime_power_iff_coprime_tail_eq_one hp he hcop heq]
    simp only [GammaArithmeticSupportRow.active, hi, ne_eq, not_false_eq_true, true_and,
      decide_eq_true_eq]

/-- Arithmetic rows covering a whole natural interval and whose
active indices are exactly S certify the full prime-power support S.
Reflect each row flag using its prime and decomposition proofs, then
use finite-set extensionality. This supplies the finite upper-bound gate. -/
theorem gamma_arithmetic_support_cover (rows : List GammaArithmeticSupportRow) (lo hi : ℕ)
    (S : Finset ℕ) (hp : rows.Forall (fun r ↦ r.prime.Prime))
    (hc : rows.Forall (fun r ↦ r.check = true))
    (hcover : (rows.map GammaArithmeticSupportRow.index).toFinset = Finset.Ioc lo hi)
    (hactive :
      ((rows.filter GammaArithmeticSupportRow.active).map
            GammaArithmeticSupportRow.index).toFinset =
        S) :
    (Finset.Ioc lo hi).filter IsPrimePow = S := by
  classical
  rw [← hcover, ← hactive]
  apply Finset.ext
  intro n
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨r, hr, rfl⟩, hpow⟩
    exact
      ⟨r,
        ⟨hr,
          (r.prime_power_iff (List.forall_iff_forall_mem.mp hp r hr)
                (List.forall_iff_forall_mem.mp hc r hr)).mp
            hpow⟩,
        rfl⟩
  · rintro ⟨r, ⟨hr, hact⟩, rfl⟩
    exact
      ⟨⟨r, hr, rfl⟩,
        (r.prime_power_iff (List.forall_iff_forall_mem.mp hp r hr)
              (List.forall_iff_forall_mem.mp hc r hr)).mpr
          hact⟩

/-- A certified finite prime list and row membership proofs give
primality of every arithmetic row base. This avoids repeating large
primality certificates for duplicated bases inside an interval census. -/
theorem gamma_support_rows_prime_of_list (rows : List GammaArithmeticSupportRow) (ps : List ℕ)
    (hp : ps.Forall Nat.Prime) (hm : rows.Forall (fun r ↦ r.prime ∈ ps)) :
    rows.Forall (fun r ↦ r.prime.Prime) := by
  apply List.forall_iff_forall_mem.mpr
  intro r hr
  exact List.forall_iff_forall_mem.mp hp r.prime (List.forall_iff_forall_mem.mp hm r hr)

/-- The rational Mangoldt-weight upper allowance for a numerical
row. Multiply the logarithm upper endpoint by the signed Euler upper
endpoint; the existing row checks establish product bound soundness. -/
def GammaFiniteEulerRow.upper (r : GammaFiniteEulerRow) : ℚ :=
  r.logUpper * gammaFiniteEulerUpper r.ratios

/-- A prime numerical row with a successful check has its actual
Mangoldt Euler weight below its rational upper allowance. Reuse the
proved power and logarithm checks and the positive lower Euler endpoint. -/
theorem GammaFiniteEulerRow.weight_le_upper (r : GammaFiniteEulerRow) (hp : r.prime.Prime)
    (hc : r.check = true) : gammaResolventMangoldtWeight r.index ≤ (r.upper : ℝ) := by
  have hh :
    (gammaFiniteEulerRatioCheck r.index r.ratios &&
        rationalLogIntervalCheck r.prime r.logScale r.logTerms r.logLower r.logUpper) &&
      decide (0 ≤ gammaFiniteEulerLower r.ratios) = true :=
    hc
  obtain ⟨hb, hlo⟩ := Bool.and_eq_true_iff.mp hh
  obtain ⟨hpow, hlog⟩ := Bool.and_eq_true_iff.mp hb
  exact (gamma_prime_power_row_check_bounds hp hpow hlog (of_decide_eq_true hlo)).2

/-- A certified numerical row list whose indices equal the whole
prime-power support gives an upper bound for the full actual Euler block.
Remove zero Mangoldt inputs, reindex distinct numerical rows, and sum
their already certified signed upper bounds. -/
theorem gamma_finite_row_block_upper (rows : List GammaFiniteEulerRow) (lo hi : ℕ)
    (hp : rows.Forall (fun r ↦ r.prime.Prime)) (hc : rows.Forall (fun r ↦ r.check = true))
    (hn : (rows.map GammaFiniteEulerRow.index).Nodup)
    (hcover :
      (Finset.Ioc lo hi).filter IsPrimePow = (rows.map GammaFiniteEulerRow.index).toFinset) :
    (∑ m ∈ Finset.Ioc lo hi, gammaResolventMangoldtWeight m) ≤
      (((rows.map GammaFiniteEulerRow.upper).sum : ℚ) : ℝ) := by
  have he :
    (∑ m ∈ (Finset.Ioc lo hi).filter IsPrimePow, gammaResolventMangoldtWeight m) =
      ∑ m ∈ Finset.Ioc lo hi, gammaResolventMangoldtWeight m := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro m hm hn
    have hpow : ¬IsPrimePow m := fun h ↦ hn (Finset.mem_filter.mpr ⟨hm, h⟩)
    rw [gammaResolventMangoldtWeight, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow, zero_mul]
  rw [← he, hcover, List.sum_toFinset gammaResolventMangoldtWeight hn, List.map_map]
  have hu :=
    List.sum_le_sum
      (fun (r : GammaFiniteEulerRow) hr ↦
        r.weight_le_upper (List.forall_iff_forall_mem.mp hp r hr)
          (List.forall_iff_forall_mem.mp hc r hr))
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def]
  exact hu

end PseudoPrime.Analysis
