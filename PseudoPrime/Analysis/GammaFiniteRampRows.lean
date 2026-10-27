/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRationalRampCertificates
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedSummationByParts

/-! # Prime-power rows for certified finite ramp lower bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A prime-power row for a finite ramp lower certificate.
The prime and exponent-minus-one identify the Mangoldt atom. The log fields
enclose log prime; the exponential term count and ramp endpoint certify
the weight at a positive rational scale. Primality and support are separate. -/
structure GammaFiniteRampRow where
  prime : ℕ
  exponent : ℕ
  logScale : ℕ
  logTerms : ℕ
  logLower : ℚ
  logUpper : ℚ
  expTerms : ℕ
  rampLower : ℚ

/-- The positive natural prime power represented by a row.
The exponent-plus-one convention excludes the zero-exponent ambiguity
and permits reuse of finite prime-power support certificates. -/
def GammaFiniteRampRow.index (r : GammaFiniteRampRow) : ℕ :=
  r.prime ^ (r.exponent + 1)

/-- The rational lower Mangoldt-ramp allowance for a row.
Multiply the certified log-prime lower endpoint by the nonnegative
ramp lower endpoint. This retains the actual Mangoldt normalization. -/
def GammaFiniteRampRow.lower (r : GammaFiniteRampRow) : ℚ :=
  r.logLower * r.rampLower

/-- The executable log and ramp checks at rational scale b.
The primality proof and positive scale are supplied separately.
A true check certifies the nonnegative row weight and both numerical inputs. -/
def GammaFiniteRampRow.check (r : GammaFiniteRampRow) (b : ℚ) : Bool :=
  rationalLogIntervalCheck r.prime r.logScale r.logTerms r.logLower r.logUpper &&
    gammaRationalRampLowerCheck ((r.index : ℚ) / b) r.expTerms r.rampLower

/-- A prime row with a true check bounds its actual Mangoldt-ramp atom.
Evaluate Mangoldt on the positive prime power and multiply the proved
log and nonnegative ramp lower bounds. This is the per-row soundness
statement used by all finite lower-sum certificates. -/
theorem GammaFiniteRampRow.lower_le (r : GammaFiniteRampRow) {b : ℚ} (_hb : 0 < b)
    (hp : r.prime.Prime) (hc : r.check b = true) :
    (r.lower : ℝ) ≤
      ArithmeticFunction.vonMangoldt r.index * exponentialRampWeight ((r.index : ℝ) / (b : ℝ)) := by
  obtain ⟨hlog, hramp⟩ := Bool.and_eq_true_iff.mp hc
  have hl := (rationalLogIntervalCheck_sound hlog).1
  have hw := gamma_rational_ramp_lower_check_sound hramp
  norm_num only [Rat.cast_natCast, Rat.cast_div] at hl hw
  have hlog0 := Real.log_nonneg (Nat.one_le_cast.mpr hp.one_lt.le)
  have hm := mul_le_mul hl hw.2 hw.1 hlog0
  rw [GammaFiniteRampRow.lower, Rat.cast_mul]
  rw [GammaFiniteRampRow.index,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero r.exponent),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  exact hm

/-- Distinct certified prime-power rows in (lo,hi] give a lower bound
for the actual full finite ramp sum on that interval at a positive scale.
Sum the row estimates and use nonnegativity of omitted Mangoldt atoms.
Exact support coverage is unnecessary for this one-sided lower bound. -/
theorem gamma_finite_ramp_row_block_lower (rows : List GammaFiniteRampRow) (lo hi : ℕ) {b : ℚ}
    (hb : 0 < b) (hp : rows.Forall (fun r ↦ r.prime.Prime))
    (hc : rows.Forall (fun r ↦ r.check b = true)) (hn : (rows.map GammaFiniteRampRow.index).Nodup)
    (hm : rows.Forall (fun r ↦ lo < r.index ∧ r.index ≤ hi)) :
    (((rows.map GammaFiniteRampRow.lower).sum : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc lo hi,
        ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / (b : ℝ)) := by
  have hl :=
    List.sum_le_sum
      (fun (r : GammaFiniteRampRow) hr ↦
        r.lower_le hb (List.forall_iff_forall_mem.mp hp r hr)
          (List.forall_iff_forall_mem.mp hc r hr))
  have hs : (rows.map GammaFiniteRampRow.index).toFinset ⊆ Finset.Ioc lo hi := by
    intro m hmem
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hmem)
    exact Finset.mem_Ioc.mpr (List.forall_iff_forall_mem.mp hm r hr)
  have ht :=
    Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun m _ _ ↦
        mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := m))
          (exponentialRampWeight_bounds ((m : ℝ) / (b : ℝ))).1)
  rw [List.sum_toFinset
      (fun m ↦ ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / (b : ℝ))) hn,
    List.map_map] at ht
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def]
  exact hl.trans ht

/-- A certified prefix lower bound through N below the actual ramp cutoff
is a lower bound for the actual ramp Mangoldt sum at positive scale b.
Include the natural interval and use nonnegativity on the remaining atoms.
This connects finite block data to the closed-cell principal comparison. -/
theorem gamma_finite_ramp_prefix_lower_actual {b q : ℚ} (_hb : 0 < b) {N : ℕ}
    (hN : N ≤ ⌊(b : ℝ) * (99 / 40)⌋₊)
    (hprefix :
      (q : ℝ) ≤
        ∑ m ∈ Finset.Ioc 0 N,
          ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / (b : ℝ))) :
    (q : ℝ) ≤ AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum b := by
  apply hprefix.trans
  exact
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc le_rfl hN)
      (fun m _ _ ↦
        mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := m))
          (exponentialRampWeight_bounds ((m : ℝ) / (b : ℝ))).1)

/-- Certified rational lower bounds on adjacent natural intervals add
at the same rational scale. Split the disjoint interval sum and preserve
both allowance casts. This composes finite ramp blocks in a balanced tree. -/
theorem gamma_finite_ramp_interval_lower_add {lo mid hi : ℕ} {b c d : ℚ} (hl : lo ≤ mid)
    (hh : mid ≤ hi)
    (hc :
      (c : ℝ) ≤
        ∑ m ∈ Finset.Ioc lo mid,
          ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / (b : ℝ)))
    (hd :
      (d : ℝ) ≤
        ∑ m ∈ Finset.Ioc mid hi,
          ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / (b : ℝ))) :
    ((c + d : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc lo hi,
        ArithmeticFunction.vonMangoldt m * exponentialRampWeight ((m : ℝ) / (b : ℝ)) := by
  have hdis : Disjoint (Finset.Ioc lo mid) (Finset.Ioc mid hi) := by
    apply Finset.disjoint_left.mpr
    intro m hm hn
    exact (not_lt_of_ge (Finset.mem_Ioc.mp hm).2) (Finset.mem_Ioc.mp hn).1
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hl hh, Finset.sum_union hdis, Rat.cast_add]
  exact add_le_add hc hd

end PseudoPrime.Analysis
