/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCheck

/-! # Integer root checks for fixed-grid Euler-center rows -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The numerators of the ten resolvent nodes over the common denominator 20. -/
def eulerTickNode (i : Fin 10) : ℕ :=
  ![11, 13, 16, 20, 26, 34, 46, 64, 90, 140] i

/-- Look up a fixed node, returning none outside the resolvent list. -/
def eulerTickIndex (a : ℚ) : Option (Fin 10) :=
  if a = 11 / 20 then some 0
  else
    if a = 13 / 20 then some 1
    else
      if a = 16 / 20 then some 2
      else
        if a = 20 / 20 then some 3
        else
          if a = 26 / 20 then some 4
          else
            if a = 34 / 20 then some 5
            else
              if a = 46 / 20 then some 6
              else
                if a = 64 / 20 then some 7
                else if a = 90 / 20 then some 8 else if a = 140 / 20 then some 9 else none

/-- The common denominator of the rational root intervals. -/
def eulerTickScale : ℕ :=
  10 ^ 30

/-- Decode adjacent integer ticks as the lower and upper rational roots. -/
def eulerTickRatios (ticks : Fin 10 → ℕ) (a : ℚ) : ℚ × ℚ :=
  match eulerTickIndex a with
  | none => (0, 0)
  | some i => ((ticks i : ℚ) / eulerTickScale, ((ticks i + 1 : ℕ) : ℚ) / eulerTickScale)

/-- Each fixed rational node has its prescribed index. -/
private theorem index_of_node (i : Fin 10) :
    eulerTickIndex ((eulerTickNode i : ℚ) / 20) = some i := by fin_cases i <;> decide +kernel

/-- The fixed node exponent can be supplied without inspecting a rational. -/
private theorem exponent_of_node (i : Fin 10) :
    Analysis.gammaSmallPrimeRatioExponent ((eulerTickNode i : ℚ) / 20) = eulerTickNode i + 10 := by
  fin_cases i <;> decide +kernel

/-- The fixed grid covers all nodes in the analytic checker. -/
private theorem mem_resolvent_node (ab : ℚ × ℚ)
    (hab : ab ∈ AnalyticNumberTheory.Gamma.gammaResolventCoefficients) :
    ∃ i : Fin 10, ab.1 = (eulerTickNode i : ℚ) / 20 := by
  have h :
    AnalyticNumberTheory.Gamma.gammaResolventCoefficients.map Prod.fst =
      List.ofFn (fun i : Fin 10 ↦ (eulerTickNode i : ℚ) / 20) := by
    decide +kernel
  have hm := List.mem_map_of_mem (f := Prod.fst) hab
  rw [h, List.mem_ofFn] at hm
  exact hm.imp fun _ hi ↦ hi.symm

/-- Clearing the positive common denominator gives the rational root bounds. -/
private theorem root_tick_bound (u m e G : ℕ) (hG : 0 < G) (hl : u ^ 20 * m ^ e ≤ G ^ 20)
    (hh : G ^ 20 ≤ (u + 1) ^ 20 * m ^ e) :
    ((u : ℚ) / G) ^ 20 * (m : ℚ) ^ e ≤ 1 ∧ 1 ≤ (((u + 1 : ℕ) : ℚ) / G) ^ 20 * (m : ℚ) ^ e := by
  have hD : 0 < (G : ℚ) ^ 20 := pow_pos (Nat.cast_pos.mpr hG) _
  have hlQ := (Nat.cast_le (α := ℚ)).mpr hl
  have hhQ := (Nat.cast_le (α := ℚ)).mpr hh
  simp only [Nat.cast_mul, Nat.cast_pow] at hlQ hhQ
  simp only [div_pow, div_mul_eq_mul_div]
  exact
    ⟨(div_le_iff₀ hD).mpr (by simpa only [one_mul] using hlQ),
      (le_div_iff₀ hD).mpr (by simpa only [one_mul] using hhQ)⟩

/-- The integer root comparisons imply the existing rational ratio check. -/
private theorem tick_ratio_check {m : ℕ} (hm : 0 < m) (ticks : Fin 10 → ℕ)
    (h :
      ∀ i : Fin 10,
        ticks i ^ 20 * m ^ (eulerTickNode i + 10) ≤ eulerTickScale ^ 20 ∧
          eulerTickScale ^ 20 ≤ (ticks i + 1) ^ 20 * m ^ (eulerTickNode i + 10)) :
    Analysis.gammaFiniteEulerRatioCheck (m : ℚ) (eulerTickRatios ticks) = true := by
  apply decide_eq_true
  refine ⟨Nat.cast_pos.mpr hm, List.forall_iff_forall_mem.mpr ?_⟩
  intro ab hab
  obtain ⟨i, hi⟩ := mem_resolvent_node ab hab
  rw [hi, exponent_of_node]
  simp only [eulerTickRatios, index_of_node, Nat.cast_add]
  have hG : 0 < eulerTickScale := by decide +kernel
  have ht := root_tick_bound (ticks i) m (eulerTickNode i + 10) eulerTickScale hG (h i).1 (h i).2
  refine
    ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      div_nonneg (add_nonneg (Nat.cast_nonneg _) (by norm_num only)) (Nat.cast_nonneg _), ?_, ?_⟩
  · push_cast
    ring
  · simpa only [Nat.cast_add, Nat.cast_one] using ht

/-- Compact data for one prime-power row. The fields `p` and `k` encode the power,
`j` normalizes the logarithm enclosed by `lo` and `hi`, and `ticks` gives one
lower root tick per fixed node. The adjacent upper ticks are implicit. -/
structure EulerTickRow where
  p : ℕ
  k : ℕ
  j : ℕ
  lo : ℚ
  hi : ℚ
  ticks : Fin 10 → ℕ

/-- Decode the compact data for the existing Euler-center consumers. -/
def EulerTickRow.toRow (r : EulerTickRow) : EulerCenterRow :=
  ⟨r.p, r.k, r.j, r.lo, r.hi, eulerTickRatios r.ticks⟩

/-- Check the prime, logarithm and weight sign and compare roots over the integers. -/
def eulerTickCheck (r : EulerTickRow) : Bool :=
  @decide r.p.Prime (Nat.decidablePrime' r.p) &&
    decide
      (∀ i : Fin 10,
        r.ticks i ^ 20 * (r.p ^ (r.k + 1)) ^ (eulerTickNode i + 10) ≤ eulerTickScale ^ 20 ∧
          eulerTickScale ^ 20 ≤
            (r.ticks i + 1) ^ 20 * (r.p ^ (r.k + 1)) ^ (eulerTickNode i + 10)) &&
    Analysis.rationalLogIntervalCheck r.p r.j 32 r.lo r.hi &&
    decide (0 ≤ Analysis.gammaFiniteEulerLower r.toRow.ratios)

/-- A successful compact row check implies the existing rational row check. -/
private theorem euler_tick_sound {r : EulerTickRow} (h : eulerTickCheck r = true) :
    eulerCenterRowCheck r.toRow = true := by
  obtain ⟨h, hn⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, hl⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hp, hr⟩ := Bool.and_eq_true_iff.mp h
  let : Decidable r.p.Prime := Nat.decidablePrime' r.p
  have hprime : r.p.Prime := of_decide_eq_true hp
  have hratio := tick_ratio_check (pow_pos hprime.pos (r.k + 1)) r.ticks (of_decide_eq_true hr)
  exact
    Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hp, hratio⟩, hl⟩, hn⟩

/-- Decode a checked list without rerunning its rational root comparisons. -/
theorem euler_tick_rows_sound {rows : List EulerTickRow} (h : rows.all eulerTickCheck = true) :
    (rows.map EulerTickRow.toRow).all eulerCenterRowCheck = true := by
  rw [List.all_map]
  exact List.all_eq_true.mpr (fun r hr ↦ euler_tick_sound (List.all_eq_true.mp h r hr))

end PseudoPrime.PrimeTestBounds.MillerRabin
