/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensation
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCompensationAbel

/-! # Dyadic partitions for the high Gaussian compensation -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- These positive dyadic widths cover the log support from zero to five.
The K186 partition groups adjacent cells with the same certified Bernstein sign. -/
private def cellWidths : HighGaussianKernel → List ℕ
  | .k186 =>
    [3983, 1, 4728, 1, 5686, 1, 6383, 1, 8048, 1, 7954, 1, 21455, 1, 9201, 1, 38399, 1, 9492, 1,
      27589, 1, 12183, 1, 39522, 1, 10056, 1, 59016, 1, 36676, 1, 223901]
  | .k196 =>
    [1024, 256, 64, 16, 8, 1, 1, 2, 4, 32, 128, 512, 1024, 256, 64, 16, 4, 1, 1, 2, 8, 32, 128, 512,
      2048, 512, 256, 128, 16, 8, 4, 1, 1, 2, 32, 64, 1024, 2048, 1024, 256, 64, 16, 4, 2, 1, 1, 8,
      32, 128, 512, 4096, 256, 16, 8, 4, 1, 1, 2, 32, 64, 128, 512, 1024, 2048, 1024, 256, 64, 32,
      16, 2, 1, 1, 4, 8, 128, 512, 2048, 2048, 1024, 512, 256, 64, 32, 8, 4, 1, 1, 2, 16, 128, 2048,
      2048, 2048, 1024, 512, 128, 8, 1, 1, 2, 4, 16, 32, 64, 256, 4096, 8192, 4096, 256, 64, 16, 8,
      1, 1, 2, 4, 32, 128, 512, 1024, 2048, 2048, 2048, 1024, 512, 256, 16, 8, 4, 2, 1, 1, 32, 64,
      128, 2048, 32768, 8192, 4096, 2048, 256, 128, 16, 8, 2, 1, 1, 4, 32, 64, 512, 1024, 2048,
      2048, 512, 128, 16, 4, 1, 1, 2, 8, 32, 64, 256, 1024, 2048, 8192, 8192, 4096, 2048, 512, 32,
      16, 8, 1, 1, 2, 4, 64, 128, 256, 1024, 2048, 2048, 2048, 2048, 1024, 256, 32, 8, 1, 1, 2, 4,
      16, 64, 128, 512, 2048, 4096, 16384, 8192, 4096, 2048, 512, 256, 32, 16, 4, 2, 1, 1, 8, 64,
      128, 1024, 2048, 2048, 2048, 2048, 256, 128, 16, 1, 1, 2, 4, 8, 32, 64, 512, 1024, 2048, 4096,
      16384, 32768, 1024, 512, 32, 16, 4, 2, 1, 1, 8, 64, 128, 256, 2048, 2048, 2048, 2048, 2048,
      2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 2048, 1024, 256, 64, 32, 8,
      1, 1, 2, 4, 16, 128, 512, 2048, 8192, 16384, 65536, 131072]

private theorem widths_positive (K : HighGaussianKernel) : ∀ n ∈ cellWidths K, 0 < n := by
  cases K <;> decide +kernel

private theorem widths_sum (K : HighGaussianKernel) : (cellWidths K).sum = 524288 := by
  cases K <;> decide +kernel

private def logCoordinate (i : ℕ) : ℚ :=
  5 * (i : ℚ) / 524288

private def chargeTicks (x : ℚ) : ℤ :=
  ⌈10 ^ 20 * x⌉

private theorem charge_ticks_upper (x : ℚ) : x ≤ (chargeTicks x : ℚ) / 10 ^ 20 := by
  apply (le_div_iff₀ (by norm_num only : (0 : ℚ) < 10 ^ 20)).mpr
  rw [mul_comm]
  exact Int.le_ceil _

private theorem log_coord_add (a b : ℕ) :
    logCoordinate (a + b) = logCoordinate a + logCoordinate b := by
  simp only [logCoordinate, Nat.cast_add, mul_add, add_div]

private def accumulateCharges (f : ℚ → ℚ → ℚ) (ws : List ℕ) (i : ℕ) (a : ℤ) : ℤ :=
  (ws.foldl
      (fun (state : ℕ × ℤ) width ↦
        let l := logCoordinate state.1
        let h := logCoordinate width
        (state.1 + width, state.2 + chargeTicks (f l h)))
      (i, a)).2

/-- Add the per-cell main and variation charges rounded upward to units of
10⁻²⁰. The dyadic partition remains internal to the calculation. -/
public def highCompensationChargeTicks (K : HighGaussianKernel) : ℤ × ℤ :=
  (accumulateCharges K.cellMainBound (cellWidths K) 0 0,
    accumulateCharges K.cellVariationBound (cellWidths K) 0 0)

private def CellBounds (F : ℝ → ℝ) (f : ℚ → ℚ → ℚ) : List ℕ → ℕ → Prop
  | [], _ => True
  | w :: ws, i =>
    ((∫ v in (logCoordinate i : ℝ)..(logCoordinate (i + w) : ℝ), F v) ≤
        (f (logCoordinate i) (logCoordinate w) : ℝ)) ∧
      CellBounds F f ws (i + w)

private theorem integral_le_accumulated (F : ℝ → ℝ) (f : ℚ → ℚ → ℚ)
    (hint : ∀ a b, IntervalIntegrable F MeasureTheory.volume a b) (ws : List ℕ) (i : ℕ)
    (hle : CellBounds F f ws i) (a : ℤ) :
    (a : ℝ) / 10 ^ 20 + (∫ v in (logCoordinate i : ℝ)..(logCoordinate (i + ws.sum) : ℝ), F v) ≤
      (accumulateCharges f ws i a : ℝ) / 10 ^ 20 := by
  induction ws generalizing i a with
  | nil =>
    simp only [List.sum_nil, intervalIntegral.integral_same, add_zero, accumulateCharges,
      List.foldl_nil, le_refl]
  | cons w ws
    ih =>
    rw [List.sum_cons, ← Nat.add_assoc, ←
      intervalIntegral.integral_add_adjacent_intervals
        (hint (logCoordinate i : ℝ) (logCoordinate (i + w) : ℝ)) (hint _ _)]
    let x := f (logCoordinate i) (logCoordinate w)
    have hx : (x : ℝ) ≤ (chargeTicks x : ℝ) / 10 ^ 20 := by exact_mod_cast charge_ticks_upper x
    have hcell := hle.1.trans hx
    have htail := ih (i + w) hle.2 (a + chargeTicks (f (logCoordinate i) (logCoordinate w)))
    simp only [accumulateCharges, List.foldl_cons] at htail ⊢
    rw [Int.cast_add, add_div] at htail
    rw [← add_assoc]
    exact (add_le_add_left (add_le_add_right hcell _) _).trans htail

private def MatchesCells (F : ℝ → ℝ) (G : ℚ → ℚ → ℝ → ℝ) : List ℕ → ℕ → Prop
  | [], _ => True
  | w :: ws, i =>
    (∀ v ∈ Set.uIcc (logCoordinate i : ℝ) (logCoordinate (i + w) : ℝ),
        F v = G (logCoordinate i) (logCoordinate w) v) ∧
      MatchesCells F G ws (i + w)

private theorem log_coord_nonneg (i : ℕ) : 0 ≤ logCoordinate i :=
  div_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg i)) (by norm_num only)

private theorem log_coord_pos {w : ℕ} (hw : 0 < w) : 0 < logCoordinate w :=
  div_pos (mul_pos (by norm_num only) (Nat.cast_pos.mpr hw)) (by norm_num only)

private theorem bounds_of_matches (F : ℝ → ℝ) (G : ℚ → ℚ → ℝ → ℝ) (f : ℚ → ℚ → ℚ)
    (hG : ∀ l h, 0 ≤ l → 0 < h → (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ), G l h v) ≤ (f l h : ℝ))
    (ws : List ℕ) (hw : ∀ w ∈ ws, 0 < w) (i : ℕ) (hm : MatchesCells F G ws i) :
    CellBounds F f ws i := by
  induction ws generalizing i with
  | nil => exact True.intro
  | cons w ws ih =>
    constructor
    · rw [intervalIntegral.integral_congr hm.1, log_coord_add, Rat.cast_add]
      exact hG _ _ (log_coord_nonneg i) (log_coord_pos (hw w List.mem_cons_self))
    · exact ih (fun k hk ↦ hw k (List.mem_cons_of_mem w hk)) (i + w) hm.2

private theorem integral_to_five_le_ticks (K : HighGaussianKernel) (F : ℝ → ℝ) (G : ℚ → ℚ → ℝ → ℝ)
    (f : ℚ → ℚ → ℚ) (hint : ∀ a b, IntervalIntegrable F MeasureTheory.volume a b)
    (hG : ∀ l h, 0 ≤ l → 0 < h → (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ), G l h v) ≤ (f l h : ℝ))
    (hm : MatchesCells F G (cellWidths K) 0) :
    (∫ v in (0 : ℝ)..5, F v) ≤ (accumulateCharges f (cellWidths K) 0 0 : ℝ) / 10 ^ 20 := by
  have hb := bounds_of_matches F G f hG (cellWidths K) (widths_positive K) 0 hm
  have h := integral_le_accumulated F f hint (cellWidths K) 0 hb 0
  norm_num only [widths_sum K, logCoordinate, Nat.cast_ofNat, Nat.cast_zero, Rat.cast_div,
    Rat.cast_mul, Rat.cast_ofNat, Int.cast_zero, zero_mul, mul_zero, zero_div, zero_add] at h
  norm_num only
  exact h

/-- The normalized Bernstein correction evaluated in the log coordinate of one cell. -/
public noncomputable def highCellCompensation (K : HighGaussianKernel) (l h : ℚ) (v : ℝ) : ℝ :=
  let C :=
    Analysis.bernsteinCompensation
      (K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)) (2 * K.degree + 3)
  C.eval ((v - (l : ℝ)) / (h : ℝ))

/-- Adjacent positive-width cells agree at the shared log endpoint. -/
public theorem high_cell_compensation_seam (K : HighGaussianKernel) (l h w : ℚ) (hh : 0 < h) :
    highCellCompensation K l h ((l + h : ℚ) : ℝ) =
      highCellCompensation K (l + h) w ((l + h : ℚ) : ℝ) := by
  have hd := high_rat_profile_degree K
  have he := Analysis.bernstein_compensation_seam K.ratProfile _ _ hd hd l (l + h) (l + h + w)
  rw [add_sub_cancel_left, add_sub_cancel_left] at he
  have hh₀ : (h : ℝ) ≠ 0 := (Rat.cast_pos.mpr hh).ne'
  simpa only [highCellCompensation, Rat.cast_add, add_comm (l : ℝ) (h : ℝ), add_sub_cancel_right,
    div_self hh₀, sub_self, zero_div] using he

private noncomputable def compensationOn (K : HighGaussianKernel) : List ℕ → ℕ → ℝ → ℝ
  | [], i, _ => highCellCompensation K (logCoordinate i) 0 (logCoordinate i : ℝ)
  | w :: ws, i, v =>
    if v ≤ (logCoordinate (i + w) : ℝ) then
      highCellCompensation K (logCoordinate i) (logCoordinate w) v
    else compensationOn K ws (i + w) v

/-- The assembled high Gaussian correction on the dyadic log partition. -/
public noncomputable def highCompensation (K : HighGaussianKernel) (v : ℝ) : ℝ :=
  compensationOn K (cellWidths K) 0 v

private theorem compensation_at_start (K : HighGaussianKernel) (ws : List ℕ) (i : ℕ) (w : ℕ) :
    compensationOn K ws i (logCoordinate i : ℝ) =
      highCellCompensation K (logCoordinate i) (logCoordinate w) (logCoordinate i : ℝ) := by
  have ha (h h' : ℚ) :
    highCellCompensation K (logCoordinate i) h (logCoordinate i : ℝ) =
      highCellCompensation K (logCoordinate i) h' (logCoordinate i : ℝ) := by
    simp only [highCellCompensation, sub_self, zero_div]
    have hd (a : ℚ) :=
      Analysis.bernstein_affine_degree _ _ (high_rat_profile_degree K) (logCoordinate i)
        (logCoordinate i + a)
    have hh := hd h
    have hh' := hd h'
    rw [add_sub_cancel_left] at hh hh'
    rw [Analysis.bernstein_compensation_at_zero _ _ hh,
      Analysis.bernstein_compensation_at_zero _ _ hh']
    simp only [Polynomial.eval₂_comp, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X, mul_zero, zero_add]
  cases ws with
  | nil => exact ha 0 _
  | cons k
    ws =>
    have hk : (logCoordinate i : ℝ) ≤ (logCoordinate (i + k) : ℝ) :=
      Rat.cast_le.mpr (log_coord_add i k ▸ le_add_of_nonneg_right (log_coord_nonneg k))
    simpa only [compensationOn, ite_eq_left hk] using ha (logCoordinate k) (logCoordinate w)

private theorem log_coord_mono_step (i w : ℕ) :
    (logCoordinate i : ℝ) ≤ (logCoordinate (i + w) : ℝ) :=
  Rat.cast_le.mpr (log_coord_add i w ▸ le_add_of_nonneg_right (log_coord_nonneg w))

private theorem matches_of_eq_right {F H : ℝ → ℝ} {G : ℚ → ℚ → ℝ → ℝ} (ws : List ℕ) (i : ℕ)
    (hm : MatchesCells F G ws i) (he : ∀ v, (logCoordinate i : ℝ) ≤ v → H v = F v) :
    MatchesCells H G ws i := by
  induction ws generalizing i with
  | nil => exact True.intro
  | cons w ws ih =>
    have h := log_coord_mono_step i w
    exact
      ⟨fun v hv ↦ (he v (Set.uIcc_of_le h ▸ hv).1).trans (hm.1 v hv),
        ih (i + w) hm.2 (fun v hv ↦ he v (h.trans hv))⟩

private theorem compensation_matches (K : HighGaussianKernel) (ws : List ℕ) (i : ℕ)
    (hw : ∀ w ∈ ws, 0 < w) :
    MatchesCells (compensationOn K ws i) (highCellCompensation K) ws i := by
  induction ws generalizing i with
  | nil => exact True.intro
  | cons w ws ih =>
    constructor
    · intro v hv
      rw [compensationOn, ite_eq_left (Set.uIcc_of_le (log_coord_mono_step i w) ▸ hv).2]
    · apply
        matches_of_eq_right ws (i + w) (ih (i + w) (fun k hk ↦ hw k (List.mem_cons_of_mem w hk)))
      intro v hv
      rw [compensationOn]
      by_cases he : v ≤ (logCoordinate (i + w) : ℝ)
      · rw [ite_eq_left he, le_antisymm he hv, compensation_at_start K ws (i + w) w]
        rw [log_coord_add]
        exact high_cell_compensation_seam K _ _ _ (log_coord_pos (hw w List.mem_cons_self))
      · rw [ite_eq_right he]

private theorem compensation_on_continuous (K : HighGaussianKernel) (ws : List ℕ) (i : ℕ)
    (hw : ∀ w ∈ ws, 0 < w) : Continuous (compensationOn K ws i) := by
  induction ws generalizing i with
  | nil => exact continuous_const
  | cons w ws
    ih =>
    rw [show compensationOn K (w :: ws) i = _ from funext (fun v ↦ by rw [compensationOn])]
    refine
      Continuous.if (fun v hv ↦ ?_) ?_ (ih (i + w) (fun k hk ↦ hw k (List.mem_cons_of_mem w hk)))
    · have he := Set.mem_singleton_iff.mp (frontier_Iic_subset _ hv)
      rw [he, compensation_at_start K ws (i + w) w, log_coord_add]
      exact high_cell_compensation_seam K _ _ _ (log_coord_pos (hw w List.mem_cons_self))
    · let C :=
        Analysis.bernsteinCompensation
          (K.ratProfile.comp
            (Polynomial.C (logCoordinate w) * Polynomial.X + Polynomial.C (logCoordinate i)))
          (2 * K.degree + 3)
      change Continuous (fun v : ℝ ↦ C.eval ((v - (logCoordinate i : ℝ)) / (logCoordinate w : ℝ)))
      exact C.continuous.comp ((continuous_id.sub continuous_const).div_const _)

private theorem matches_weight_mul (g : ℝ → ℝ) {F : ℝ → ℝ} {G : ℚ → ℚ → ℝ → ℝ} (ws : List ℕ) (i : ℕ)
    (hm : MatchesCells F G ws i) :
    MatchesCells (fun v ↦ g v * F v) (fun l h v ↦ g v * G l h v) ws i := by
  induction ws generalizing i with
  | nil => exact True.intro
  | cons w ws ih => exact ⟨fun v hv ↦ congrArg (g v * ·) (hm.1 v hv), ih (i + w) hm.2⟩

/-- The main compensation integral over the full log support is bounded by
the accumulated rational cell charges. -/
public theorem high_compensation_integral_le (K : HighGaussianKernel) :
    (∫ v in (0 : ℝ)..5, Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * v) * highCompensation K v) ≤
      ((highCompensationChargeTicks K).1 : ℝ) / 10 ^ 20 := by
  let g := fun v : ℝ ↦ Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * v)
  have hg : Continuous g := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hc := compensation_on_continuous K _ 0 (widths_positive K)
  exact
    integral_to_five_le_ticks K _ _ K.cellMainBound (fun a b ↦ (hg.mul hc).intervalIntegrable a b)
      (fun _ _ hl hh ↦ high_compensation_main_le K hl hh)
      (matches_weight_mul g _ 0 (compensation_matches K _ 0 (widths_positive K)))

private noncomputable def sumCellIntegrals (G : ℚ → ℚ → ℝ → ℝ) : List ℕ → ℕ → ℝ
  | [], _ => 0
  | w :: ws, i =>
    (∫ v in (logCoordinate i : ℝ)..(logCoordinate i : ℝ) + (logCoordinate w : ℝ),
        G (logCoordinate i) (logCoordinate w) v) +
      sumCellIntegrals G ws (i + w)

private theorem sum_integrals_le_charges (G : ℚ → ℚ → ℝ → ℝ) (f : ℚ → ℚ → ℚ)
    (hG : ∀ l h, 0 ≤ l → 0 < h → (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ), G l h v) ≤ (f l h : ℝ))
    (ws : List ℕ) (hw : ∀ w ∈ ws, 0 < w) (i : ℕ) (a : ℤ) :
    (a : ℝ) / 10 ^ 20 + sumCellIntegrals G ws i ≤ (accumulateCharges f ws i a : ℝ) / 10 ^ 20 := by
  induction ws generalizing i a with
  | nil => simp only [sumCellIntegrals, add_zero, accumulateCharges, List.foldl_nil, le_refl]
  | cons w ws ih =>
    let x := f (logCoordinate i) (logCoordinate w)
    have hx : (x : ℝ) ≤ (chargeTicks x : ℝ) / 10 ^ 20 := by exact_mod_cast charge_ticks_upper x
    have hcell := (hG _ _ (log_coord_nonneg i) (log_coord_pos (hw w List.mem_cons_self))).trans hx
    have htail := ih (fun k hk ↦ hw k (List.mem_cons_of_mem w hk)) (i + w) (a + chargeTicks x)
    simp only [sumCellIntegrals, accumulateCharges, List.foldl_cons]
    rw [← add_assoc]
    rw [Int.cast_add, add_div] at htail
    exact (add_le_add_left (add_le_add_right hcell _) _).trans htail

private noncomputable def variationIntegrand (K : HighGaussianKernel) (l h : ℚ) (v : ℝ) : ℝ :=
  let C :=
    Analysis.bernsteinCompensation
      (K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)) (2 * K.degree + 3)
  let u := (v - (l : ℝ)) / (h : ℝ)
  Real.exp (-(K.pole : ℝ) * v) *
    |((K.pole - 1 / 2 : ℚ) : ℝ) * C.eval u - (h : ℝ)⁻¹ * C.derivative.eval u|

/-- The total high Gaussian variation charge, as a sum over the log cells. -/
public noncomputable def highCompensationVariation (K : HighGaussianKernel) : ℝ :=
  sumCellIntegrals (variationIntegrand K) (cellWidths K) 0

/-- The accumulated rational charges bound the full piecewise variation. -/
public theorem high_compensation_variation_sum_le (K : HighGaussianKernel) :
    highCompensationVariation K ≤ ((highCompensationChargeTicks K).2 : ℝ) / 10 ^ 20 := by
  have h :=
    sum_integrals_le_charges (variationIntegrand K) K.cellVariationBound
      (fun _ _ hl hh ↦ high_compensation_variation_le K hl hh) (cellWidths K) (widths_positive K) 0
      0
  simpa only [highCompensationVariation, highCompensationChargeTicks, Int.cast_zero, zero_div,
    zero_add] using h

private theorem cell_compensation_nonneg (K : HighGaussianKernel) (l h : ℚ) (hh : 0 < h) {v : ℝ}
    (hv : v ∈ Set.Icc (l : ℝ) ((l + h : ℚ) : ℝ)) :
    0 ≤ highCellCompensation K l h v ∧ 0 ≤ K.realProfile.eval v + highCellCompensation K l h v := by
  have hb := high_compensation_cell_nonneg K l (l + h) (lt_add_of_pos_right l hh) hv
  simpa only [highCellCompensation, add_sub_cancel_left] using hb

private theorem compensation_on_nonneg (K : HighGaussianKernel) (ws : List ℕ) (i : ℕ)
    (hw : ∀ w ∈ ws, 0 < w) {v : ℝ}
    (hv : v ∈ Set.Icc (logCoordinate i : ℝ) (logCoordinate (i + ws.sum) : ℝ)) :
    0 ≤ compensationOn K ws i v ∧ 0 ≤ K.realProfile.eval v + compensationOn K ws i v := by
  induction ws generalizing i with
  | nil =>
    have hv₀ : v = (logCoordinate i : ℝ) := le_antisymm (Nat.add_zero i ▸ hv.2) hv.1
    rw [hv₀, compensation_at_start K [] i 1]
    exact
      cell_compensation_nonneg K _ _ (log_coord_pos Nat.one_pos)
        ⟨le_rfl, Rat.cast_le.mpr (le_add_of_nonneg_right (log_coord_nonneg 1))⟩
  | cons w ws ih =>
    rw [compensationOn]
    by_cases he : v ≤ (logCoordinate (i + w) : ℝ)
    · rw [ite_eq_left he]
      exact
        cell_compensation_nonneg K _ _ (log_coord_pos (hw w List.mem_cons_self))
          ⟨hv.1, log_coord_add i w ▸ he⟩
    · rw [ite_eq_right he]
      exact
        ih (i + w) (fun k hk ↦ hw k (List.mem_cons_of_mem w hk))
          ⟨(lt_of_not_ge he).le, by simpa only [List.sum_cons, Nat.add_assoc] using hv.2⟩

/-- On the full log support, the high Gaussian correction and the corrected
physical profile are both nonnegative. -/
public theorem high_compensation_nonneg (K : HighGaussianKernel) {v : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) 5) :
    0 ≤ highCompensation K v ∧ 0 ≤ K.realProfile.eval v + highCompensation K v := by
  apply compensation_on_nonneg K (cellWidths K) 0 (widths_positive K)
  norm_num only [widths_sum K, Nat.zero_add, logCoordinate, Nat.cast_zero, zero_mul, mul_zero,
    zero_div, Nat.cast_ofNat, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
  exact hv

private theorem cell_compensation_left (K : HighGaussianKernel) (l h : ℚ) :
    highCellCompensation K l h (l : ℝ) = max 0 (-K.realProfile.eval (l : ℝ)) := by
  have hd := Analysis.bernstein_affine_degree _ _ (high_rat_profile_degree K) l (l + h)
  rw [add_sub_cancel_left] at hd
  simp only [highCellCompensation, sub_self, zero_div,
    Analysis.bernstein_compensation_at_zero _ _ hd, Polynomial.eval₂_comp, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, mul_zero, zero_add,
    Rat.coe_castHom]
  rw [← Polynomial.eval_map, high_comp_profile_map]

/-- The high Gaussian compensation vanishes at the left end of the support. -/
public theorem high_compensation_at_zero (K : HighGaussianKernel) : highCompensation K 0 = 0 := by
  have hz : (logCoordinate 0 : ℝ) = 0 := by
    simp only [logCoordinate, Nat.cast_zero, mul_zero, zero_div, Rat.cast_zero]
  change compensationOn K (cellWidths K) 0 0 = 0
  rw [← hz, compensation_at_start K (cellWidths K) 0 1, cell_compensation_left, hz,
    (high_real_profile_at_zero K).1, neg_zero, max_self]

private theorem compensation_on_at_end (K : HighGaussianKernel) (ws : List ℕ) (i : ℕ)
    (hw : ∀ w ∈ ws, 0 < w) :
    let b : ℝ := logCoordinate (i + ws.sum)
    compensationOn K ws i b = max 0 (-K.realProfile.eval b) := by
  induction ws generalizing i with
  | nil =>
    change compensationOn K [] i (logCoordinate (i + 0) : ℝ) = _
    simp only [List.sum_nil, Nat.add_zero, compensationOn, cell_compensation_left]
  | cons w ws
    ih =>
    change compensationOn K (w :: ws) i (logCoordinate (i + (w :: ws).sum) : ℝ) = _
    simp only [List.sum_cons, ← Nat.add_assoc, compensationOn]
    let b : ℝ := logCoordinate (i + w + ws.sum)
    let e : ℝ := logCoordinate (i + w)
    by_cases h : b ≤ e
    · have he : (logCoordinate (i + w + ws.sum) : ℝ) = (logCoordinate (i + w) : ℝ) :=
        le_antisymm h (log_coord_mono_step (i + w) ws.sum)
      rw [ite_eq_left h, he]
      have hs :=
        high_cell_compensation_seam K (logCoordinate i) (logCoordinate w) 0
          (log_coord_pos (hw w List.mem_cons_self))
      rw [← log_coord_add] at hs
      exact hs.trans (cell_compensation_left K _ _)
    · rw [ite_eq_right h]
      exact ih (i + w) (fun k hk ↦ hw k (List.mem_cons_of_mem w hk))

/-- At the right end, the correction is the negative part of the
uncompensated profile. In particular, a nonnegative profile value gives zero correction. -/
public theorem high_compensation_at_five (K : HighGaussianKernel) (h : 0 ≤ K.realProfile.eval 5) :
    highCompensation K 5 = 0 := by
  have he := compensation_on_at_end K (cellWidths K) 0 (widths_positive K)
  have h5 : (logCoordinate (0 + (cellWidths K).sum) : ℝ) = 5 := by
    norm_num only [widths_sum K, Nat.zero_add, logCoordinate, Nat.cast_ofNat, Rat.cast_ofNat,
      Rat.cast_mul, Rat.cast_div]
  change
    compensationOn K (cellWidths K) 0 (logCoordinate (0 + (cellWidths K).sum) : ℝ) =
      max 0 (-K.realProfile.eval (logCoordinate (0 + (cellWidths K).sum) : ℝ)) at he
  rw [h5, max_eq_left (neg_nonpos.mpr h)] at he
  exact he

/-- On the unknown Euler range, a character sum between -1 and 3 loses
at most four times the correction relative to the negative profile. -/
public theorem high_compensated_euler_lower (K : HighGaussianKernel) {v τ : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) 5) (hτ₀ : -1 ≤ τ) (hτ₁ : τ ≤ 3) :
    -K.realProfile.eval v - 4 * highCompensation K v ≤ τ * K.realProfile.eval v := by
  obtain ⟨hc, hb⟩ := high_compensation_nonneg K hv
  have h₁ := mul_nonneg (show 0 ≤ τ + 1 from by linarith only [hτ₀]) hb
  have h₂ := mul_nonneg (show 0 ≤ 3 - τ from by linarith only [hτ₁]) hc
  nlinarith only [h₁, h₂]

/-- The unknown Euler portion satisfies H13 after summing the pointwise
compensation inequality with the nonnegative physical Mangoldt weights. -/
public theorem high_compensated_tail_lower (K : HighGaussianKernel) {X : ℝ} (hX : 0 < X) (τ : ℕ → ℝ)
    (hτ : ∀ m, -1 ≤ τ m ∧ τ m ≤ 3) :
    let v := fun m : ℕ ↦ 5 - Real.log ((m : ℝ) / X)
    let w := fun m : ℕ ↦
      ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2) : ℝ) * Real.exp (-(K.pole : ℝ) * v m)
    (∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp 5⌋₊,
        w m * (-K.realProfile.eval (v m) - 4 * highCompensation K (v m))) ≤
      ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp 5⌋₊, w m * (τ m * K.realProfile.eval (v m)) := by
  dsimp only
  apply Finset.sum_le_sum
  intro m hm
  obtain ⟨hm₀, hm₁⟩ := Finset.mem_Ioc.mp hm
  have hl := (Nat.floor_lt hX.le).mp hm₀
  have hu := (Nat.le_floor_iff (mul_nonneg hX.le (Real.exp_pos _).le)).mp hm₁
  have hd : 0 < (m : ℝ) / X := div_pos (hX.trans hl) hX
  have hlog₀ := Real.log_nonneg ((le_div_iff₀ hX).mpr (by simpa only [one_mul] using hl.le))
  have hlog₁ :=
    (Real.log_le_iff_le_exp hd).mpr ((div_le_iff₀ hX).mpr (by simpa only [mul_comm] using hu))
  exact
    mul_le_mul_of_nonneg_left
      (high_compensated_euler_lower K ⟨sub_nonneg.mpr hlog₁, sub_le_self _ hlog₀⟩ (hτ m).1 (hτ m).2)
      (mul_nonneg
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Real.exp_pos _).le)

private theorem sum_high_cutoff (X : ℝ) (hX : 0 < X) (f : ℕ → ℝ) :
    (∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, f m) =
      (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, f m) + ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp 5⌋₊, f m := by
  have hx : X ≤ X * Real.exp 5 := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 5)) hX.le
  have hd : Disjoint (Finset.Ioc 0 ⌊X⌋₊) (Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp 5⌋₊) := by
    refine Finset.disjoint_left.mpr (fun m hm hn ↦ ?_)
    exact (not_lt_of_ge (Finset.mem_Ioc.mp hm).2) (Finset.mem_Ioc.mp hn).1
  rw [← Finset.sum_union hd, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (Nat.floor_mono hx)]

/-- H13 for the full support. The character sum is three on the known
range and remains between minus one and three on the rest of the support. -/
public theorem high_compensated_sum_lower (K : HighGaussianKernel) {X : ℝ} (hX : 0 < X) (τ : ℕ → ℝ)
    (hτ : ∀ m, -1 ≤ τ m ∧ τ m ≤ 3)
    (hknown : ∀ m ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt m ≠ 0 → τ m = 3) :
    let v := fun m : ℕ ↦ 5 - Real.log ((m : ℝ) / X)
    let w := fun m : ℕ ↦
      ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2) : ℝ) * Real.exp (-(K.pole : ℝ) * v m)
    let B := fun m : ℕ ↦ w m * K.realProfile.eval (v m)
    4 * (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, B m) - (∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, B m) -
        4 * (∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp 5⌋₊, w m * highCompensation K (v m)) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, τ m * B m := by
  intro v w B
  rw [sum_high_cutoff X hX B, sum_high_cutoff X hX (fun m ↦ τ m * B m)]
  have hk : (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, τ m * B m) = 3 * (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, B m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hΛ : ArithmeticFunction.vonMangoldt m = 0
    · simp only [B, w, hΛ, zero_mul, mul_zero]
    · rw [hknown m hm hΛ]
  rw [hk]
  have htail := high_compensated_tail_lower K hX τ hτ
  change
    (∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp 5⌋₊,
        w m * (-K.realProfile.eval (v m) - 4 * highCompensation K (v m))) ≤
      _ at htail
  have ht :
    ∀ m : ℕ,
      w m * (-K.realProfile.eval (v m) - 4 * highCompensation K (v m)) =
        -B m - 4 * (w m * highCompensation K (v m)) := by
    intro m
    dsimp only [B]
    ring
  simp only [ht, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at htail
  have he :
    (∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp 5⌋₊, w m * (τ m * K.realProfile.eval (v m))) =
      ∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp 5⌋₊, τ m * B m :=
    Finset.sum_congr rfl (fun _ _ ↦ mul_left_comm _ _ _)
  change
    _ ≤ (∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp 5⌋₊, w m * (τ m * K.realProfile.eval (v m))) at htail
  rw [he] at htail
  linarith only [htail]

private noncomputable def cellLogPoly (K : HighGaussianKernel) (l h : ℚ) : Polynomial ℝ :=
  (Analysis.bernsteinCompensation
        (K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C l))
        (2 * K.degree + 3)).comp
    (Polynomial.C ((h : ℝ)⁻¹) * (Polynomial.X - Polynomial.C (l : ℝ)))

private theorem cell_log_poly_eval (K : HighGaussianKernel) (l h : ℚ) (v : ℝ) :
    (cellLogPoly K l h).eval v = highCellCompensation K l h v := by
  simp only [cellLogPoly, highCellCompensation, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X, div_eq_mul_inv]
  rw [mul_comm]

private theorem cell_log_poly_derivative (K : HighGaussianKernel) (l h : ℚ) (v : ℝ) :
    let C :=
      Analysis.bernsteinCompensation
        (K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)) (2 * K.degree + 3)
    (cellLogPoly K l h).derivative.eval v =
      (h : ℝ)⁻¹ * C.derivative.eval ((v - (l : ℝ)) / (h : ℝ)) := by
  simp only [cellLogPoly, Polynomial.derivative_comp, Polynomial.derivative_C_mul,
    Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, mul_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, div_eq_mul_inv]
  rw [mul_comm ((h : ℝ)⁻¹) (v - (l : ℝ))]

private theorem cell_log_poly_variation (K : HighGaussianKernel) (l h : ℚ) (v : ℝ) :
    Real.exp (-(K.pole : ℝ) * v) *
        |((K.pole : ℝ) - 1 / 2) * (cellLogPoly K l h).eval v -
            (cellLogPoly K l h).derivative.eval v| =
      variationIntegrand K l h v := by
  rw [cell_log_poly_eval, cell_log_poly_derivative]
  simp only [variationIntegrand, highCellCompensation, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_one]

private theorem cell_weight_variation (K : HighGaussianKernel) (l h : ℚ) {X t : ℝ} (hX : 0 < X)
    (ht : 0 < t) :
    Real.sqrt t * |deriv (gaussianCompensationWeight (cellLogPoly K l h) X 5 K.pole) t| =
      variationIntegrand K l h (5 - Real.log (t / X)) / t := by
  rw [gaussian_compensation_variation _ hX ht, cell_log_poly_variation]

private theorem variation_integrand_continuous (K : HighGaussianKernel) (l h : ℚ) :
    Continuous (variationIntegrand K l h) := by
  rw [show variationIntegrand K l h = _ from funext (cell_log_poly_variation K l h) |>.symm]
  let P := cellLogPoly K l h
  exact
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((continuous_const.mul P.continuous).sub P.derivative.continuous).abs

private theorem cell_variation_integral_eq (K : HighGaussianKernel) (l h : ℚ) {X : ℝ} (hX : 0 < X)
    (hh : 0 ≤ h) :
    (∫ t in X * Real.exp (5 - ((l : ℝ) + (h : ℝ)))..X * Real.exp (5 - (l : ℝ)),
        Real.sqrt t * |deriv (gaussianCompensationWeight (cellLogPoly K l h) X 5 K.pole) t|) =
      ∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ), variationIntegrand K l h v := by
  have hlr : (l : ℝ) ≤ (l : ℝ) + (h : ℝ) := le_add_of_nonneg_right (Rat.cast_nonneg.mpr hh)
  rw [← gaussian_log_cell_integral hX hlr (b := 5) (variation_integrand_continuous K l h)]
  apply intervalIntegral.integral_congr
  intro t ht
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left hlr 5)) hX.le
  exact
    cell_weight_variation K l h hX
      ((mul_pos hX (Real.exp_pos _)).trans_le (Set.uIcc_of_le he ▸ ht).1)

private theorem cell_main_integral_eq (K : HighGaussianKernel) (l h : ℚ) {X : ℝ} (hX : 0 < X)
    (hh : 0 ≤ h) :
    (∫ t in X * Real.exp (5 - ((l : ℝ) + (h : ℝ)))..X * Real.exp (5 - (l : ℝ)),
        gaussianCompensationWeight (cellLogPoly K l h) X 5 K.pole t) =
      (Real.sqrt X * Real.exp (5 / 2)) *
        ∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ),
          Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * v) * highCellCompensation K l h v := by
  rw [gaussian_compensation_main_cell _ hX (le_add_of_nonneg_right (Rat.cast_nonneg.mpr hh))]
  simp only [cell_log_poly_eval, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]

private theorem cell_abel_upper (hRH : RiemannHypothesis) (K : HighGaussianKernel) (l h : ℚ) {X : ℝ}
    (hX : 0 < X) (hh : 0 ≤ h) (ha : 1000000 ≤ X * Real.exp (5 - ((l : ℝ) + (h : ℝ)))) :
    let A := X * Real.exp (5 - ((l : ℝ) + (h : ℝ)))
    let B := X * Real.exp (5 - (l : ℝ))
    let f := gaussianCompensationWeight (cellLogPoly K l h) X 5 K.pole
    (∑ m ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, ArithmeticFunction.vonMangoldt m * f m) ≤
      (Real.sqrt X * Real.exp (5 / 2)) *
              (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ),
                Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * v) * highCellCompensation K l h v) +
            (Chebyshev.psi B - B) * f B -
          (Chebyshev.psi A - A) * f A +
        Real.log B ^ 2 / 24 * (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ), variationIntegrand K l h v) := by
  intro A B f
  have hlr : (l : ℝ) ≤ (l : ℝ) + (h : ℝ) := le_add_of_nonneg_right (Rat.cast_nonneg.mpr hh)
  have hab : A ≤ B := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left hlr 5)) hX.le
  have hA : 0 < A := mul_pos hX (Real.exp_pos _)
  have hu :=
    gaussian_compensation_piece hRH ha hab
      (fun t ht ↦
        (gaussian_compensation_hasDerivAt (cellLogPoly K l h) (b := 5) (a := K.pole) hX
            (hA.trans_le ht.1)).differentiableAt)
      (gaussian_compensation_deriv_integrable (cellLogPoly K l h) hX hA)
  rw [cell_main_integral_eq K l h hX hh, cell_variation_integral_eq K l h hX hh] at hu
  exact hu

private noncomputable def physicalCompensation (K : HighGaussianKernel) (X t : ℝ) : ℝ :=
  let v := 5 - Real.log (t / X)
  t ^ (-(1 / 2) : ℝ) * Real.exp (-(K.pole : ℝ) * v) * highCompensation K v

private theorem log_of_physical_mem {X l r t : ℝ} (hX : 0 < X)
    (ht : t ∈ Set.Icc (X * Real.exp (5 - r)) (X * Real.exp (5 - l))) :
    5 - Real.log (t / X) ∈ Set.Icc l r := by
  have ht₀ := (mul_pos hX (Real.exp_pos (5 - r))).trans_le ht.1
  have hd := div_pos ht₀ hX
  have hlo :=
    (Real.le_log_iff_exp_le hd).mpr ((le_div_iff₀ hX).mpr (by simpa only [mul_comm] using ht.1))
  have hhi :=
    (Real.log_le_iff_le_exp hd).mpr ((div_le_iff₀ hX).mpr (by simpa only [mul_comm] using ht.2))
  exact ⟨le_sub_comm.mp hhi, sub_le_comm.mp hlo⟩

private theorem physical_compensation_matches (K : HighGaussianKernel) {X : ℝ} (hX : 0 < X)
    (l h : ℚ)
    (hm :
      ∀ v ∈ Set.Icc (l : ℝ) ((l : ℝ) + (h : ℝ)),
        highCompensation K v = highCellCompensation K l h v)
    {t : ℝ}
    (ht : t ∈ Set.Icc (X * Real.exp (5 - ((l : ℝ) + (h : ℝ)))) (X * Real.exp (5 - (l : ℝ)))) :
    gaussianCompensationWeight (cellLogPoly K l h) X 5 K.pole t = physicalCompensation K X t := by
  have he := hm _ (log_of_physical_mem hX ht)
  simp only [gaussianCompensationWeight, physicalCompensation, cell_log_poly_eval, he]

private theorem physical_compensation_at_ends (K : HighGaussianKernel) {X : ℝ} (hX : 0 < X)
    (hfive : 0 ≤ K.realProfile.eval 5) :
    physicalCompensation K X X = 0 ∧ physicalCompensation K X (X * Real.exp 5) = 0 := by
  constructor
  · simp only [physicalCompensation, div_self hX.ne', Real.log_one, sub_zero,
      high_compensation_at_five K hfive, mul_zero]
  · simp only [physicalCompensation, mul_div_cancel_left₀ _ hX.ne', Real.log_exp, sub_self,
      high_compensation_at_zero, mul_zero]

private theorem cell_abel_global (hRH : RiemannHypothesis) (K : HighGaussianKernel) (l h : ℚ)
    {X : ℝ} (hX : 0 < X) (hh : 0 < h) (ha : 1000000 ≤ X * Real.exp (5 - ((l : ℝ) + (h : ℝ))))
    (hm :
      ∀ v ∈ Set.Icc (l : ℝ) ((l : ℝ) + (h : ℝ)),
        highCompensation K v = highCellCompensation K l h v) :
    let A := X * Real.exp (5 - ((l : ℝ) + (h : ℝ)))
    let B := X * Real.exp (5 - (l : ℝ))
    let F := physicalCompensation K X
    (∑ m ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, ArithmeticFunction.vonMangoldt m * F m) ≤
      (Real.sqrt X * Real.exp (5 / 2)) *
              (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ),
                Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * v) * highCompensation K v) +
            (Chebyshev.psi B - B) * F B -
          (Chebyshev.psi A - A) * F A +
        Real.log B ^ 2 / 24 * (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ), variationIntegrand K l h v) := by
  intro A B F
  let f := gaussianCompensationWeight (cellLogPoly K l h) X 5 K.pole
  have hab : A ≤ B :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr
        (sub_le_sub_left (le_add_of_nonneg_right (Rat.cast_nonneg.mpr hh.le) : (l : ℝ) ≤ _) 5))
      hX.le
  have he {t : ℝ} (ht : t ∈ Set.Icc A B) : f t = F t := physical_compensation_matches K hX l h hm ht
  have hlr : (l : ℝ) ≤ (l : ℝ) + (h : ℝ) := le_add_of_nonneg_right (Rat.cast_nonneg.mpr hh.le)
  have hi :
    (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ),
        Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * v) * highCellCompensation K l h v) =
      ∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ),
        Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * v) * highCompensation K v := by
    apply intervalIntegral.integral_congr
    intro v hv
    exact
      congrArg (Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * v) * ·)
        (hm v (Set.uIcc_of_le hlr ▸ hv)).symm
  have hs :
    (∑ m ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, ArithmeticFunction.vonMangoldt m * f m) =
      ∑ m ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, ArithmeticFunction.vonMangoldt m * F m := by
    apply Finset.sum_congr rfl
    intro m hm'
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hm'
    have hA : 0 ≤ A := (by norm_num only : (0 : ℝ) ≤ 1000000).trans ha
    exact
      congrArg (ArithmeticFunction.vonMangoldt m * ·)
        (he ⟨((Nat.floor_lt hA).mp hlo).le, (Nat.le_floor_iff (hA.trans hab)).mp hhi⟩)
  have hu := cell_abel_upper hRH K l h hX hh.le ha
  change (∑ m ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, ArithmeticFunction.vonMangoldt m * f m) ≤ _ at hu
  have hB := he (t := B) ⟨hab, le_rfl⟩
  have hA := he (t := A) ⟨le_rfl, hab⟩
  dsimp only [f, A, B] at hB hA
  rw [hs, hi, hB, hA] at hu
  exact hu

private theorem sum_natural_interval_split (f : ℕ → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ j ∈ Finset.Ioc a c, f j) = (∑ j ∈ Finset.Ioc a b, f j) + ∑ j ∈ Finset.Ioc b c, f j := by
  have hd : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) :=
    Finset.disjoint_left.mpr
      (fun _ hp hq ↦ (not_lt_of_ge (Finset.mem_Ioc.mp hp).2) (Finset.mem_Ioc.mp hq).1)
  rw [← Finset.sum_union hd, Finset.Ioc_union_Ioc_eq_Ioc hab hbc]

private theorem log_cell_abel_sum (hRH : RiemannHypothesis) (K : HighGaussianKernel) {X : ℝ}
    (hX : 0 < X) (ws : List ℕ) (i : ℕ) (hw : ∀ w ∈ ws, 0 < w)
    (hm : MatchesCells (highCompensation K) (highCellCompensation K) ws i)
    (hmin : 1000000 ≤ X * Real.exp (5 - (logCoordinate (i + ws.sum) : ℝ))) :
    let x := fun j : ℕ ↦ X * Real.exp (5 - (logCoordinate j : ℝ))
    let F := physicalCompensation K X
    let E := fun t : ℝ ↦ (Chebyshev.psi t - t) * F t
    let g := fun v : ℝ ↦ Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * v) * highCompensation K v
    (∑ m ∈ Finset.Ioc ⌊x (i + ws.sum)⌋₊ ⌊x i⌋₊, ArithmeticFunction.vonMangoldt m * F m) ≤
      (Real.sqrt X * Real.exp (5 / 2)) *
              (∫ v in (logCoordinate i : ℝ)..(logCoordinate (i + ws.sum) : ℝ), g v) +
            E (x i) -
          E (x (i + ws.sum)) +
        Real.log (X * Real.exp 5) ^ 2 / 24 * sumCellIntegrals (variationIntegrand K) ws i := by
  induction ws generalizing i with
  | nil =>
    simp only [List.sum_nil, Finset.Ioc_self, Finset.sum_empty, intervalIntegral.integral_same,
      sumCellIntegrals, mul_zero, zero_add, sub_self, add_zero, le_refl]
  | cons w ws ih =>
    intro x F E g
    have hh := log_coord_pos (hw w List.mem_cons_self)
    have hstep (j k : ℕ) : x (j + k) ≤ x j :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left (log_coord_mono_step j k) 5))
        hX.le
    have hmin' : 1000000 ≤ x (i + w + ws.sum) := by
      simpa only [x, List.sum_cons, Nat.add_assoc] using hmin
    have ha : 1000000 ≤ x (i + w) := hmin'.trans (hstep (i + w) ws.sum)
    have he : (logCoordinate (i + w) : ℝ) = (logCoordinate i : ℝ) + (logCoordinate w : ℝ) := by
      rw [log_coord_add, Rat.cast_add]
    have hc :=
      cell_abel_global hRH K (logCoordinate i) (logCoordinate w) hX hh
        (by simpa only [x, he] using ha)
        (fun v hv ↦ hm.1 v (Set.uIcc_of_le (log_coord_mono_step i w) ▸ (he.symm ▸ hv)))
    rw [← he] at hc
    have ht := ih (i + w) (fun k hk ↦ hw k (List.mem_cons_of_mem w hk)) hm.2 hmin'
    have hg : Continuous g :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (compensation_on_continuous K _ 0 (widths_positive K))
    have hi :=
      intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
        (hg.intervalIntegrable (logCoordinate i : ℝ) (logCoordinate (i + w) : ℝ))
        (hg.intervalIntegrable (logCoordinate (i + w) : ℝ) (logCoordinate (i + w + ws.sum) : ℝ))
    have hv :
      0 ≤
        ∫ v in (logCoordinate i : ℝ)..(logCoordinate (i + w) : ℝ),
          variationIntegrand K (logCoordinate i) (logCoordinate w) v :=
      intervalIntegral.integral_nonneg (log_coord_mono_step i w)
        (fun v _ ↦ mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
    have hx : x i ≤ X * Real.exp 5 :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (sub_le_self _ (Rat.cast_nonneg.mpr (log_coord_nonneg i)))) hX.le
    have hxp : 1 ≤ x i := (by norm_num only : (1 : ℝ) ≤ 1000000).trans (ha.trans (hstep i w))
    have hlog := Real.log_le_log (zero_lt_one.trans_le hxp) hx
    have hs := pow_le_pow_left₀ (Real.log_nonneg hxp) hlog 2
    have hb :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs (by norm_num only : (0 : ℝ) ≤ 24))
        hv
    rw [List.sum_cons, ← Nat.add_assoc,
      sum_natural_interval_split _ (Nat.floor_mono (hstep (i + w) ws.sum))
        (Nat.floor_mono (hstep i w)),
      ← hi, sumCellIntegrals, ← he, mul_add, mul_add]
    dsimp only [x, F, g, E] at hc ht hb ⊢
    linarith only [hc, ht, hb]

/-- The exponentially weighted main integral of the assembled compensation. -/
public noncomputable def highCompensationMain (K : HighGaussianKernel) : ℝ :=
  ∫ v in (0 : ℝ)..5, Real.exp (-((K.pole + 1 / 2 : ℚ) : ℝ) * v) * highCompensation K v

/-- H16 for either high kernel. The Mangoldt sum of the compensation is
bounded by its main and variation integrals, with the endpoint terms canceled. -/
public theorem high_compensation_abel_bound (hRH : RiemannHypothesis) (K : HighGaussianKernel)
    {X : ℝ} (hX : 1000000 ≤ X) :
    let v := fun t : ℝ ↦ 5 - Real.log (t / X)
    (∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp 5⌋₊,
        ArithmeticFunction.vonMangoldt m *
          ((m : ℝ) ^ (-(1 / 2) : ℝ) * Real.exp (-(K.pole : ℝ) * v m) * highCompensation K (v m))) ≤
      (Real.sqrt X * Real.exp (5 / 2)) * highCompensationMain K +
        Real.log (X * Real.exp 5) ^ 2 / 24 * highCompensationVariation K := by
  have hp := (by norm_num only : (0 : ℝ) < 1000000).trans_le hX
  have h0 : (logCoordinate 0 : ℝ) = 0 := by
    simp only [logCoordinate, Nat.cast_zero, mul_zero, zero_div, Rat.cast_zero]
  have h5 : (logCoordinate (0 + (cellWidths K).sum) : ℝ) = 5 := by
    norm_num only [widths_sum K, Nat.zero_add, logCoordinate, Nat.cast_ofNat, Rat.cast_ofNat,
      Rat.cast_mul, Rat.cast_div]
  have hab :=
    log_cell_abel_sum hRH K hp (cellWidths K) 0 (widths_positive K)
      (compensation_matches K _ 0 (widths_positive K))
      (by simpa only [h5, sub_self, Real.exp_zero, mul_one] using hX)
  obtain ⟨ha, hb⟩ := physical_compensation_at_ends K hp (high_real_profile_at_five_pos K).le
  simp only [h0, h5, sub_zero, sub_self, Real.exp_zero, mul_one, ha, hb, mul_zero, add_zero] at hab
  exact hab

/-- The H16 upper bound on the compensation sum at physical cutoff X. -/
public noncomputable def highCompensationBound (K : HighGaussianKernel) (X : ℝ) : ℝ :=
  (Real.sqrt X * Real.exp (5 / 2)) * highCompensationMain K +
    Real.log (X * Real.exp 5) ^ 2 / 24 * highCompensationVariation K

/-- Combine the H13 signed Euler lower bound with the H16 Abel estimate for the correction. -/
public theorem high_euler_sum_lower (hRH : RiemannHypothesis) (K : HighGaussianKernel) {X : ℝ}
    (hX : 1000000 ≤ X) (τ : ℕ → ℝ) (hτ : ∀ m, -1 ≤ τ m ∧ τ m ≤ 3)
    (hknown : ∀ m ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt m ≠ 0 → τ m = 3) :
    let v := fun m : ℕ ↦ 5 - Real.log ((m : ℝ) / X)
    let w := fun m : ℕ ↦
      ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2) : ℝ) * Real.exp (-(K.pole : ℝ) * v m)
    let B := fun m : ℕ ↦ w m * K.realProfile.eval (v m)
    4 * (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, B m) - (∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, B m) -
        4 * highCompensationBound K X ≤
      ∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, τ m * B m := by
  intro v w B
  have hp := (by norm_num only : (0 : ℝ) < 1000000).trans_le hX
  have h₁ := high_compensated_sum_lower K hp τ hτ hknown
  have h₂ := high_compensation_abel_bound hRH K hX
  change _ ≤ highCompensationBound K X at h₂
  have h₃ :
    (∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp 5⌋₊, w m * highCompensation K (v m)) ≤
      highCompensationBound K X := by
    simpa only [v, w, mul_assoc] using h₂
  change
    4 * (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, B m) - (∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, B m) -
        4 * (∑ m ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp 5⌋₊, w m * highCompensation K (v m)) ≤
      _ at h₁
  linarith only [h₁, h₃]

/-- The original rounded main charge remains an upper bound on the main integral. -/
public theorem high_comp_main_le_ticks (K : HighGaussianKernel) :
    highCompensationMain K ≤ ((highCompensationChargeTicks K).1 : ℝ) / 10 ^ 20 := by
  exact high_compensation_integral_le K

attribute [irreducible] highCompensationMain highCompensationVariation

end PseudoPrime.PrimeTestBounds.MillerRabin
