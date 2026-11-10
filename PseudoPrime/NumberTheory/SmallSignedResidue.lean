/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-! # Small signed residue representatives -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- If `q < (B+1)²`, every natural `a` has a positive multiplier `v ≤ B`
whose residue modulo `q` has an integer representative of absolute value at
most `B`. Dirichlet approximation gives a real bound strictly below `B+1`;
integrality gives the stated bound. -/
theorem exists_small_signed_residue {a q B : ℕ} (hq : 0 < q) (hB : 0 < B)
    (hsize : q < (B + 1) ^ 2) :
    ∃ v : ℕ, 0 < v ∧ v ≤ B ∧ ∃ u j : ℤ, u.natAbs ≤ B ∧ (v : ℤ) * a = u + j * q := by
  obtain ⟨v, hv0, hvB, hv⟩ := Real.exists_nat_abs_mul_sub_round_le ((a : ℝ) / q) hB
  let j : ℤ := round ((v : ℝ) * ((a : ℝ) / q))
  let u : ℤ := (v : ℤ) * a - j * q
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hBR : (0 : ℝ) < (B : ℝ) + 1 := by exact_mod_cast Nat.succ_pos B
  have hsizeR : (q : ℝ) < ((B : ℝ) + 1) ^ 2 := by exact_mod_cast hsize
  have hmul := mul_le_mul_of_nonneg_right hv hqR.le
  have he : |(u : ℝ)| = |(v : ℝ) * ((a : ℝ) / q) - j| * q := by
    calc
      _ = |((v : ℝ) * ((a : ℝ) / q) - j) * q| := by
        congr 1
        dsimp only [u]
        push_cast
        field_simp [hqR.ne']
      _ = _ := by rw [abs_mul, abs_of_nonneg hqR.le]
  have hsmall : |(u : ℝ)| < (B : ℝ) + 1 := by
    rw [he]
    have hratio : (q : ℝ) / (B + 1) < B + 1 := by
      apply (div_lt_iff₀ hBR).2
      nlinarith only [hsizeR]
    change |(v : ℝ) * ((a : ℝ) / q) - j| * q ≤ 1 / (B + 1) * q at hmul
    have hratio' : (1 : ℝ) / (B + 1) * q < B + 1 := by
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hratio
    exact hmul.trans_lt hratio'
  have hu : u.natAbs ≤ B := by
    have hsmallZ : |u| < (B : ℤ) + 1 := by exact_mod_cast hsmall
    rw [← Int.natCast_natAbs] at hsmallZ
    have hnat : u.natAbs < B + 1 := by exact_mod_cast hsmallZ
    exact Nat.lt_succ_iff.mp hnat
  refine ⟨v, hv0, hvB, u, j, hu, ?_⟩
  dsimp only [u]
  ring

end PseudoPrime.NumberTheory
