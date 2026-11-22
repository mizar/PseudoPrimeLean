/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.BandSound
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.ThetaEntry

/-! # Joint prefix verification from 2657 through 3099 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem band {n : ℕ} (_hl : 2657 ≤ n) (hr : n < 3100) : thetaBand n = (9, 5) := by
  simp only [thetaBand, ite_eq_left hr]

private def extra2657 : ℕ → ℕ
  | 2657 => 1
  | 2659 => 7
  | 2667 => 8
  | 2676 => 7
  | 2684 => 15
  | _ => 0

private theorem part2657 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x)
      ⟨2657, 2624016843000490, 2624050214203841, 64765146252886, 64765146253001⟩
      ⟨2700, 2702944198599586, 2702978763861556, 64765146252886, 64765146253001⟩ := by
  apply
    accepted_band (a := 2657) (b := 2700) (by decide) (by decide) 9 5
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 2657 ≤ 2657) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 2700 ≤ 3100)))
      extra2657 5
  decide +kernel

private def extra2700 : ℕ → ℕ
  | 2700 => 28
  | 2729 => 23
  | _ => 0

private theorem part2700 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x)
      ⟨2700, 2702944198599586, 2702978763861556, 64765146252886, 64765146253001⟩
      ⟨2753, 2766225871758310, 2766261304522331, 64765146252886, 64765146253001⟩ := by
  apply
    accepted_band (a := 2700) (b := 2753) (by decide) (by decide) 9 5
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 2657 ≤ 2700) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 2753 ≤ 3100)))
      extra2700 2
  decide +kernel

private def extra2753 : ℕ → ℕ
  | 2753 => 35
  | 2789 => 19
  | _ => 0

private theorem part2753 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x)
      ⟨2753, 2766225871758310, 2766261304522331, 64765146252886, 64765146253001⟩
      ⟨2809, 2829681029939542, 2829717173603140, 64765146252886, 64765146253001⟩ := by
  apply
    accepted_band (a := 2753) (b := 2809) (by decide) (by decide) 9 5
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 2657 ≤ 2753) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 2809 ≤ 3100)))
      extra2753 2
  decide +kernel

private def extra2809 : ℕ → ℕ
  | 2809 => 27
  | 2837 => 19
  | _ => 0

private theorem part2809 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x)
      ⟨2809, 2829681029939542, 2829717173603140, 64765146252886, 64765146253001⟩
      ⟨2857, 2873403092342649, 2873439405807636, 68735438166433, 68735438166554⟩ := by
  apply
    accepted_band (a := 2809) (b := 2857) (by decide) (by decide) 9 5
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 2657 ≤ 2809) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 2857 ≤ 3100)))
      extra2809 2
  decide +kernel

private def extra2857 : ℕ → ℕ
  | 2857 => 29
  | 2887 => 29
  | _ => 0

private theorem part2857 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x)
      ⟨2857, 2873403092342649, 2873439405807636, 68735438166433, 68735438166554⟩
      ⟨2917, 2929173206715992, 2929210107072707, 68735438166433, 68735438166554⟩ := by
  apply
    accepted_band (a := 2857) (b := 2917) (by decide) (by decide) 9 5
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 2657 ≤ 2857) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 2917 ≤ 3100)))
      extra2857 2
  decide +kernel

private def extra2917 : ℕ → ℕ
  | 2917 => 35
  | _ => 0

private theorem part2917 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x)
      ⟨2917, 2929173206715992, 2929210107072707, 68735438166433, 68735438166554⟩
      ⟨2953, 2953119070685057, 2953156396569880, 68735438166433, 68735438166554⟩ := by
  apply
    accepted_band (a := 2917) (b := 2953) (by decide) (by decide) 9 5
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 2657 ≤ 2917) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 2953 ≤ 3100)))
      extra2917 1
  decide +kernel

private def extra2953 : ℕ → ℕ
  | 2953 => 36
  | _ => 0

private theorem part2953 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x)
      ⟨2953, 2953119070685057, 2953156396569880, 68735438166433, 68735438166554⟩
      ⟨2990, 2993088169398912, 2993125608643046, 68735438166433, 68735438166554⟩ := by
  apply
    accepted_band (a := 2953) (b := 2990) (by decide) (by decide) 9 5
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 2657 ≤ 2953) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 2990 ≤ 3100)))
      extra2953 1
  decide +kernel

private def extra2990 : ℕ → ℕ
  | 2990 => 32
  | _ => 0

private theorem part2990 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x)
      ⟨2990, 2993088169398912, 2993125608643046, 68735438166433, 68735438166554⟩
      ⟨3023, 3025123608336488, 3025161416706470, 68735438166433, 68735438166554⟩ := by
  apply
    accepted_band (a := 2990) (b := 3023) (by decide) (by decide) 9 5
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 2657 ≤ 2990) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 3023 ≤ 3100)))
      extra2990 1
  decide +kernel

private def extra3023 : ℕ → ℕ
  | 3023 => 40
  | _ => 0

private theorem part3023 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x)
      ⟨3023, 3025123608336488, 3025161416706470, 68735438166433, 68735438166554⟩
      ⟨3064, 3065225242960410, 3065263418536082, 68735438166433, 68735438166554⟩ := by
  apply
    accepted_band (a := 3023) (b := 3064) (by decide) (by decide) 9 5
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 2657 ≤ 3023) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 3064 ≤ 3100)))
      extra3023 1
  decide +kernel

private def extra3064 : ℕ → ℕ
  | 3064 => 31
  | 3096 => 3
  | _ => 0

private theorem part3064 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x)
      ⟨3064, 3065225242960410, 3065263418536082, 68735438166433, 68735438166554⟩
      ⟨3100, 3097355316838818, 3097393709094831, 68735438166433, 68735438166554⟩ := by
  apply
    accepted_band (a := 3064) (b := 3100) (by decide) (by decide) 9 5
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 2657 ≤ 3064) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 3100 ≤ 3100)))
      extra3064 2
  decide +kernel

/-- The incoming prefix extends to 3100 with the stated psi estimate. -/
theorem prefix3100 :
    Valid ⟨3100, 3097355316838818, 3097393709094831, 68735438166433, 68735438166554⟩ ∧
      ∀ x : ℝ,
        2657 ≤ x →
          x < 3100 →
          |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
            |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x := by
  have joined0 := segment_comp part2657 part2700
  have joined1 := segment_comp part2753 part2809
  have joined2 := segment_comp part2857 part2917
  have joined3 := segment_comp part2953 part2990
  have joined4 := segment_comp part3023 part3064
  have joined5 := segment_comp joined0 joined1
  have joined6 := segment_comp joined2 joined3
  have joined7 := segment_comp joined5 joined6
  have joined8 := segment_comp joined7 joined4
  exact joined8 theta_entry.1

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
