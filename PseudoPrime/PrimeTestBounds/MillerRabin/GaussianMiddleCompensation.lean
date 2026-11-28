/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleBernstein

/-! # Composition of middle Gaussian compensation cells -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Evaluate the clipped Bernstein polynomial on a cell in its normalized coordinate. -/
@[expose]
public noncomputable def middleCompCell (P : Polynomial ℚ) (N : ℕ) (l h : ℚ) (v : ℝ) : ℝ :=
  (Analysis.bernsteinCompensation (P.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)) N).eval
    ((v - (l : ℝ)) / (h : ℝ))

/-- At the left endpoint, compensation is the negative part of the source polynomial. -/
private theorem middle_comp_cell_start (P : Polynomial ℚ) (N : ℕ) (hN : P.natDegree ≤ N) (l h : ℚ) :
    middleCompCell P N l h (l : ℝ) = max 0 (-(P.eval₂ (Rat.castHom ℝ) (l : ℝ))) := by
  have hd := Analysis.bernstein_affine_degree P N hN l (l + h)
  rw [add_sub_cancel_left] at hd
  simp only [middleCompCell, sub_self, zero_div, Analysis.bernstein_compensation_at_zero _ _ hd,
    Polynomial.eval₂_comp, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, mul_zero, zero_add, Rat.coe_castHom]

/-- At the right endpoint of a positive-width cell, compensation is the negative part. -/
private theorem middle_comp_cell_end (P : Polynomial ℚ) (N : ℕ) (hN : P.natDegree ≤ N) (l h : ℚ)
    (hh : 0 < h) :
    middleCompCell P N l h ((l + h : ℚ) : ℝ) =
      max 0 (-(P.eval₂ (Rat.castHom ℝ) ((l + h : ℚ) : ℝ))) := by
  have hd := Analysis.bernstein_affine_degree P N hN l (l + h)
  rw [add_sub_cancel_left] at hd
  simp only [middleCompCell, Rat.cast_add, add_sub_cancel_left,
    div_self ((Rat.cast_pos.mpr hh : (0 : ℝ) < (h : ℝ))).ne',
    Analysis.bernstein_compensation_at_one _ _ hd, Polynomial.eval₂_comp, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, mul_one, Rat.coe_castHom,
    add_comm (h : ℝ) (l : ℝ)]

/-- Join the cell compensation functions from left to right, with a constant terminal value. -/
public noncomputable def middleCompOn (P : Polynomial ℚ) (N : ℕ) : List ℚ → ℚ → ℝ → ℝ
  | [], l, _ => max 0 (-(P.eval₂ (Rat.castHom ℝ) (l : ℝ)))
  | h :: hs, l, v =>
    if v ≤ ((l + h : ℚ) : ℝ) then middleCompCell P N l h v else middleCompOn P N hs (l + h) v

/-- The first cell and the terminal extension share the same start-value rule. -/
public theorem middle_comp_on_start (P : Polynomial ℚ) (N : ℕ) (hN : P.natDegree ≤ N) (hs : List ℚ)
    (hh : ∀ h ∈ hs, 0 < h) (l : ℚ) :
    middleCompOn P N hs l (l : ℝ) = max 0 (-(P.eval₂ (Rat.castHom ℝ) (l : ℝ))) := by
  cases hs with
  | nil => rfl
  | cons h
    hs =>
    have hl : (l : ℝ) ≤ ((l + h : ℚ) : ℝ) :=
      Rat.cast_le.mpr (le_add_of_nonneg_right (hh h List.mem_cons_self).le)
    rw [middleCompOn, ite_eq_left hl, middle_comp_cell_start P N hN]

/-- Positive widths and matching endpoint values make the joined correction continuous. -/
public theorem middle_comp_on_continuous (P : Polynomial ℚ) (N : ℕ) (hN : P.natDegree ≤ N)
    (hs : List ℚ) (hh : ∀ h ∈ hs, 0 < h) (l : ℚ) : Continuous (middleCompOn P N hs l) := by
  induction hs generalizing l with
  | nil => exact continuous_const
  | cons h hs ih =>
    have ht : ∀ w ∈ hs, 0 < w := fun w hw ↦ hh w (List.mem_cons_of_mem h hw)
    rw [show middleCompOn P N (h :: hs) l = _ from funext (fun v ↦ by rw [middleCompOn])]
    refine Continuous.if (fun v hv ↦ ?_) ?_ (ih ht (l + h))
    · rw [Set.mem_singleton_iff.mp (frontier_Iic_subset _ hv), middle_comp_on_start P N hN hs ht,
        middle_comp_cell_end P N hN l h (hh h List.mem_cons_self)]
    · let C :=
        Analysis.bernsteinCompensation (P.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)) N
      change Continuous (fun v : ℝ ↦ C.eval ((v - (l : ℝ)) / (h : ℝ)))
      exact C.continuous.comp ((continuous_id.sub continuous_const).div_const _)

/-- Through the first cell's right endpoint, the joined correction agrees with that cell. -/
public theorem middle_comp_on_cons_left (P : Polynomial ℚ) (N : ℕ) (hs : List ℚ) (l h : ℚ) {v : ℝ}
    (hv : v ≤ ((l + h : ℚ) : ℝ)) : middleCompOn P N (h :: hs) l v = middleCompCell P N l h v := by
  rw [middleCompOn, ite_eq_left hv]

/-- On the closed tail, the joined correction agrees with the remaining cells. -/
public theorem middle_comp_on_cons_right {P : Polynomial ℚ} {N : ℕ} (hN : P.natDegree ≤ N)
    (hs : List ℚ) (hw : ∀ w ∈ hs, 0 < w) (l h : ℚ) (hh : 0 < h) {v : ℝ}
    (hv : ((l + h : ℚ) : ℝ) ≤ v) :
    middleCompOn P N (h :: hs) l v = middleCompOn P N hs (l + h) v := by
  rw [middleCompOn]
  by_cases hle : v ≤ ((l + h : ℚ) : ℝ)
  · rw [ite_eq_left hle, le_antisymm hle hv, middle_comp_cell_end P N hN l h hh,
      middle_comp_on_start P N hN hs hw]
  · rw [ite_eq_right hle]

/-- Split the weighted integral into its first cell and the remaining joined cells. -/
public theorem middle_comp_integral_cons (P : Polynomial ℚ) (N : ℕ) (hN : P.natDegree ≤ N)
    (hs : List ℚ) (hw : ∀ w ∈ hs, 0 < w) (l h : ℚ) (hh : 0 < h) (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ v in (l : ℝ)..((l + h + hs.sum : ℚ) : ℝ), g v * middleCompOn P N (h :: hs) l v) =
      (∫ v in (l : ℝ)..((l + h : ℚ) : ℝ), g v * middleCompCell P N l h v) +
        (∫ v in ((l + h : ℚ) : ℝ)..((l + h + hs.sum : ℚ) : ℝ),
          g v * middleCompOn P N hs (l + h) v) := by
  have hw' : ∀ w ∈ h :: hs, 0 < w := by
    intro w hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hh
    · exact hw w hm
  have hc : Continuous (fun v ↦ g v * middleCompOn P N (h :: hs) l v) :=
    hg.mul (middle_comp_on_continuous P N hN (h :: hs) hw' l)
  have hl : (l : ℝ) ≤ ((l + h : ℚ) : ℝ) := Rat.cast_le.mpr (le_add_of_nonneg_right hh.le)
  have hsum : 0 ≤ hs.sum := List.sum_nonneg (fun w hm ↦ (hw w hm).le)
  have hr : ((l + h : ℚ) : ℝ) ≤ ((l + h + hs.sum : ℚ) : ℝ) :=
    Rat.cast_le.mpr (le_add_of_nonneg_right hsum)
  rw [←
    intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (l : ℝ) ((l + h : ℚ) : ℝ))
      (hc.intervalIntegrable ((l + h : ℚ) : ℝ) ((l + h + hs.sum : ℚ) : ℝ))]
  congr 1
  · apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le hl] at hv
    simp only [middleCompOn, ite_eq_left hv.2]
  · apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le hr] at hv
    exact congrArg (g v * ·) (middle_comp_on_cons_right hN hs hw l h hh hv.1)

/-- Sum the weighted absolute variation integrals over the individual cells. -/
@[expose]
public noncomputable def middleCompVariation (P : Polynomial ℚ) (N : ℕ) (a d : ℚ) : List ℚ → ℚ → ℝ
  | [], _ => 0
  | h :: hs, l =>
    let C :=
      Analysis.bernsteinCompensation (P.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)) N
    let u := fun v : ℝ ↦ (v - (l : ℝ)) / (h : ℝ)
    (∫ v in (l : ℝ)..((l + h : ℚ) : ℝ),
        Real.exp (-(a : ℝ) * v) * |(d : ℝ) * C.eval (u v) - (h : ℝ)⁻¹ * C.derivative.eval (u v)|) +
      middleCompVariation P N a d hs (l + h)

/-- Add the two rational compensation charges over consecutive cells. -/
@[expose]
public def middleCompTotal (charge : ℚ → ℚ → ℚ × ℚ) : List ℚ → ℚ → ℚ × ℚ
  | [], _ => (0, 0)
  | h :: hs, l =>
    let c := charge l h
    let t := middleCompTotal charge hs (l + h)
    (c.1 + t.1, c.2 + t.2)

/-- Record the two analytic upper bounds only on the specified consecutive cells. -/
@[expose]
public def middleCompBounds (P : Polynomial ℚ) (N : ℕ) (a d : ℚ) (charge : ℚ → ℚ → ℚ × ℚ) :
    List ℚ → ℚ → Prop
  | [], _ => True
  | h :: hs, l =>
     (let C :=
        Analysis.bernsteinCompensation (P.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)) N
      let u := fun v : ℝ ↦ (v - (l : ℝ)) / (h : ℝ)
      (∫ v in (l : ℝ)..((l + h : ℚ) : ℝ), Real.exp (-((a + 1 / 2 : ℚ) : ℝ) * v) * C.eval (u v)) ≤
          ((charge l h).1 : ℝ) ∧
        (∫ v in (l : ℝ)..((l + h : ℚ) : ℝ),
            Real.exp (-(a : ℝ) * v) *
              |(d : ℝ) * C.eval (u v) - (h : ℝ)⁻¹ * C.derivative.eval (u v)|) ≤
          ((charge l h).2 : ℝ)) ∧
      middleCompBounds P N a d charge hs (l + h)

/-- Local charge bounds control the joined main integral and the sum of cell variations. -/
public theorem middle_comp_total_le (P : Polynomial ℚ) (N : ℕ) (hN : P.natDegree ≤ N) (a d : ℚ)
    (charge : ℚ → ℚ → ℚ × ℚ) (hs : List ℚ) (hw : ∀ w ∈ hs, 0 < w) (l : ℚ)
    (hcharge : middleCompBounds P N a d charge hs l) :
    (∫ v in (l : ℝ)..((l + hs.sum : ℚ) : ℝ),
          Real.exp (-((a + 1 / 2 : ℚ) : ℝ) * v) * middleCompOn P N hs l v) ≤
        ((middleCompTotal charge hs l).1 : ℝ) ∧
      middleCompVariation P N a d hs l ≤ ((middleCompTotal charge hs l).2 : ℝ) := by
  induction hs generalizing l with
  | nil =>
    simp only [List.sum_nil, add_zero, intervalIntegral.integral_same, middleCompTotal,
      middleCompVariation, Rat.cast_zero, le_refl, and_self]
  | cons h hs ih =>
    have hh := hw h List.mem_cons_self
    have ht : ∀ w ∈ hs, 0 < w := fun w hm ↦ hw w (List.mem_cons_of_mem h hm)
    have hc := hcharge.1
    have htail := ih ht (l + h) hcharge.2
    have hg : Continuous (fun v : ℝ ↦ Real.exp (-((a + 1 / 2 : ℚ) : ℝ) * v)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    rw [List.sum_cons, ← add_assoc, middle_comp_integral_cons P N hN hs ht l h hh _ hg]
    simp only [middleCompTotal, Rat.cast_add, middleCompVariation]
    exact
      ⟨by simpa only [Rat.cast_add, middleCompCell] using add_le_add hc.1 htail.1, by
        simpa only [Rat.cast_add] using add_le_add hc.2 htail.2⟩

/-- Integer affine rows supply both analytic charge bounds for a rational cell. -/
public theorem MiddleIntRow.affine_charges_le (r : MiddleIntRow) (N : ℕ) (i w b : ℤ) (a d : ℚ)
    (hr : 0 < r.den) (hb : 0 < b) (hl : 0 ≤ (i : ℚ) / b) (hh : 0 < (w : ℚ) / b) (ha : 0 ≤ a) :
    let l := (i : ℚ) / b
    let h := (w : ℚ) / b
    let C :=
      Analysis.bernsteinCompensation
        ((r.poly N).comp (Polynomial.C h * Polynomial.X + Polynomial.C l)) N
    let u := fun v : ℝ ↦ (v - (l : ℝ)) / (h : ℝ)
    let charge := (r.affine N i w b).compensationCharges N l h a d
    (∫ v in (l : ℝ)..((l + h : ℚ) : ℝ), Real.exp (-((a + 1 / 2 : ℚ) : ℝ) * v) * C.eval (u v)) ≤
        (charge.1 : ℝ) ∧
      (∫ v in (l : ℝ)..((l + h : ℚ) : ℝ),
          Real.exp (-(a : ℝ) * v) *
            |(d : ℝ) * C.eval (u v) - (h : ℝ)⁻¹ * C.derivative.eval (u v)|) ≤
        (charge.2 : ℝ) := by
  have hd : 0 ≤ ((r.affine N i w b).bernstein N).den :=
    mul_nonneg (mul_nonneg hr.le (pow_nonneg hb.le N)) (Int.natCast_nonneg _)
  have hc := (r.affine N i w b).compensation_charges_le N (d := d) hh hl ha hd
  simpa only [r.poly_affine N i w b hr.ne' hb.ne', Rat.cast_add] using hc

/-- At and beyond the right endpoint, the joined correction is the negative part
of the source value at that endpoint. -/
public theorem middle_comp_on_end {P : Polynomial ℚ} {N : ℕ} (hN : P.natDegree ≤ N) {hs : List ℚ}
    (hw : ∀ w ∈ hs, 0 < w) (l : ℚ) {v : ℝ} (hv : ((l + hs.sum : ℚ) : ℝ) ≤ v) :
    middleCompOn P N hs l v = max 0 (-(P.eval₂ (Rat.castHom ℝ) ((l + hs.sum : ℚ) : ℝ))) := by
  induction hs generalizing l with
  | nil => simp only [middleCompOn, List.sum_nil, add_zero]
  | cons h hs ih =>
    have ht : ∀ w ∈ hs, 0 < w := fun w hm ↦ hw w (List.mem_cons_of_mem h hm)
    have hsum : 0 ≤ hs.sum := List.sum_nonneg (fun w hm ↦ (ht w hm).le)
    have ht0 : ((l + h : ℚ) : ℝ) ≤ ((l + h + hs.sum : ℚ) : ℝ) :=
      Rat.cast_le.mpr (le_add_of_nonneg_right hsum)
    rw [List.sum_cons, ← add_assoc] at hv ⊢
    rw [middleCompOn]
    by_cases he : v ≤ ((l + h : ℚ) : ℝ)
    · rw [ite_eq_left he, le_antisymm he (ht0.trans hv),
        middle_comp_cell_end P N hN l h (hw h List.mem_cons_self), le_antisymm (hv.trans he) ht0]
    · rw [ite_eq_right he]
      exact ih ht (l + h) hv

/-- The joined correction is nonnegative and offsets the negative part of the source
throughout the covered interval. -/
public theorem middle_comp_on_nonneg {P : Polynomial ℚ} {N : ℕ} (hN : P.natDegree ≤ N) {hs : List ℚ}
    (hw : ∀ w ∈ hs, 0 < w) {l : ℚ} {v : ℝ} (hv : v ∈ Set.Icc (l : ℝ) ((l + hs.sum : ℚ) : ℝ)) :
    0 ≤ middleCompOn P N hs l v ∧ 0 ≤ P.eval₂ (Rat.castHom ℝ) v + middleCompOn P N hs l v := by
  induction hs generalizing l with
  | nil =>
    have he : v = (l : ℝ) := le_antisymm (by simpa only [List.sum_nil, add_zero] using hv.2) hv.1
    rw [he, middleCompOn]
    refine ⟨le_max_left _ _, ?_⟩
    rw [add_comm]
    exact neg_le_iff_add_nonneg.mp (le_max_right _ _)
  | cons h hs ih =>
    rw [middleCompOn]
    by_cases he : v ≤ ((l + h : ℚ) : ℝ)
    · rw [ite_eq_left he]
      have hp : (0 : ℝ) < (h : ℝ) := Rat.cast_pos.mpr (hw h List.mem_cons_self)
      have hu : v - (l : ℝ) ≤ (h : ℝ) := by
        rw [Rat.cast_add] at he
        exact sub_le_iff_le_add'.mpr he
      let t : Set.Icc (0 : ℝ) 1 :=
        ⟨_, div_nonneg (sub_nonneg.mpr hv.1) hp.le, (div_le_one hp).mpr hu⟩
      have ht : (h : ℝ) * (t : ℝ) + (l : ℝ) = v := by
        change (h : ℝ) * ((v - (l : ℝ)) / (h : ℝ)) + (l : ℝ) = v
        rw [mul_div_cancel₀ _ hp.ne', sub_add_cancel]
      have hc := Analysis.bernstein_affine_compensation_nonneg P N hN l (l + h) t
      simpa only [add_sub_cancel_left, ht, middleCompCell] using hc
    · rw [ite_eq_right he]
      have hb : v ≤ ((l + h + hs.sum : ℚ) : ℝ) := by
        simpa only [List.sum_cons, add_assoc] using hv.2
      exact ih (fun w hm ↦ hw w (List.mem_cons_of_mem h hm)) ⟨(lt_of_not_ge he).le, hb⟩

/-- Compute and round both charges on an integer grid with denominator `b`.
The scale `S` is used independently for each outward rounding. -/
@[expose]
public def MiddleIntRow.compGridCharge (r : MiddleIntRow) (N : ℕ) (b : ℤ) (a d S l h : ℚ) : ℚ × ℚ :=
  let row := r.affine N (l * b).num (h * b).num b
  let cost := row.compensationCharges N l h a d
  (⌈cost.1 * S⌉ / S, ⌈cost.2 * S⌉ / S)

/-- On a positive integer grid, the rounded charge bounds can be accumulated
by the same analytic partition lemma as individually supplied bounds. -/
public theorem MiddleIntRow.comp_grid_bounds (r : MiddleIntRow) (N : ℕ) {b : ℤ} (hr : 0 < r.den)
    (hb : 0 < b) {a d S : ℚ} (ha : 0 ≤ a) (hS : 0 < S) (ws : List ℕ) (hw : ∀ w ∈ ws, 0 < w)
    (i : ℕ) :
    middleCompBounds (r.poly N) N a d (r.compGridCharge N b a d S)
      (ws.map (fun w : ℕ ↦ ((w : ℤ) : ℚ) / b)) (((i : ℤ) : ℚ) / b) := by
  induction ws generalizing i with
  | nil => trivial
  | cons w ws ih =>
    have hbq : (0 : ℚ) < (b : ℚ) := Int.cast_pos.mpr hb
    have hi : (0 : ℚ) ≤ (((i : ℤ) : ℚ) / b) :=
      div_nonneg
        (by
          rw [Int.cast_natCast]; exact Nat.cast_nonneg i)
        hbq.le
    have hh : (0 : ℚ) < (((w : ℤ) : ℚ) / b) :=
      div_pos (Int.cast_pos.mpr (Int.natCast_pos.mpr (hw w List.mem_cons_self))) hbq
    have hc := r.affine_charges_le N (i : ℤ) (w : ℤ) b a d hr hb hi hh ha
    have hround (q : ℚ) : (q : ℝ) ≤ ((⌈q * S⌉ / S : ℚ) : ℝ) :=
      Rat.cast_le.mpr ((le_div_iff₀ hS).mpr (Int.le_ceil (q * S)))
    refine ⟨?_, ?_⟩
    · dsimp only [MiddleIntRow.compGridCharge]
      rw [div_mul_cancel₀ _ hbq.ne', div_mul_cancel₀ _ hbq.ne']
      simp only [Rat.num_intCast]
      exact ⟨hc.1.trans (hround _), hc.2.trans (hround _)⟩
    · have htail := ih (fun u hu ↦ hw u (List.mem_cons_of_mem w hu)) (i + w)
      simpa only [Nat.cast_add, Int.cast_add, add_div] using htail

/-- A single pair of rational comparisons bounds the full analytic
compensation integral and variation on a checked positive integer grid. -/
public theorem MiddleIntRow.comp_grid_total_le (r : MiddleIntRow) (N : ℕ) {b : ℤ} (hr : 0 < r.den)
    (hb : 0 < b) {a d S I V : ℚ} (ha : 0 ≤ a) (hS : 0 < S) (ws : List ℕ) (hw : ∀ w ∈ ws, 0 < w) :
    let hs := ws.map (fun w : ℕ ↦ ((w : ℤ) : ℚ) / b)
    let total := middleCompTotal (r.compGridCharge N b a d S) hs 0
    total.1 ≤ I →
      total.2 ≤ V →
      (∫ v in (0 : ℝ)..(hs.sum : ℝ),
            Real.exp (-((a + 1 / 2 : ℚ) : ℝ) * v) * middleCompOn (r.poly N) N hs 0 v) ≤
          (I : ℝ) ∧
        middleCompVariation (r.poly N) N a d hs 0 ≤ (V : ℝ) := by
  intro hs total hI hV
  have hN : (r.poly N).natDegree ≤ N :=
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _)
  have hpos (w : ℚ) (h : w ∈ hs) : 0 < w := by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    rw [Int.cast_natCast]
    exact div_pos (Nat.cast_pos.mpr (hw v hv)) (Int.cast_pos.mpr hb)
  have hgrid := r.comp_grid_bounds N hr hb (d := d) ha hS ws hw 0
  simp only [Nat.cast_zero, Int.cast_zero, zero_div] at hgrid
  have h := middle_comp_total_le _ N hN a d (r.compGridCharge N b a d S) hs hpos 0 hgrid
  simpa only [zero_add, Rat.cast_zero] using
    And.intro (h.1.trans (Rat.cast_le.mpr hI)) (h.2.trans (Rat.cast_le.mpr hV))

end PseudoPrime.PrimeTestBounds.MillerRabin
