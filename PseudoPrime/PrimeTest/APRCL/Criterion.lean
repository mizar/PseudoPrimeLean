/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.APRCL.Parameters

/-!
# Elementary final criterion for APR-CL

This file isolates the final divisor-orbit argument from the analytic and cyclotomic APR-CL
kernel. It proves that a prime-factor orbit restriction and a finite residue scan certify
primality when the modulus exceeds the square root of the input.
-/

namespace PseudoPrime.PrimeTest.APRCL

/-- Repeated-multiplication state for the residue sequence modulo `M`, initialized at `1 % M`.
At each step it multiplies the current residue by `n` and reduces modulo `M`. -/
def powerResidueIterate (n M : ℕ) : ℕ → ℕ
  | 0 => 1 % M
  | k + 1 => powerResidueIterate n M k * n % M

/-- The repeated-multiplication state at index `i` is exactly `n^i % M`. -/
theorem powerResidueIterate_eq_pow_mod (n M i : ℕ) :
    powerResidueIterate n M i = n ^ i % M := by
  induction i with
  | zero => simp only [powerResidueIterate, Nat.pow_zero]
  | succ i ih =>
      calc
        powerResidueIterate n M (i + 1) = (n ^ i % M * n) % M := by
          rw [powerResidueIterate, ih]
        _ = (n ^ i * n) % M := Nat.mod_mul_mod _ _ _
        _ = n ^ (i + 1) % M := by rw [Nat.pow_succ]

/-- Once a positive iterate reaches one, all later residues repeat the earlier sequence.
This is the periodicity fact needed to justify stopping the APR-CL residue loop at `r = 1`. -/
theorem powerResidueIterate_add_of_eq_one {n M i k : ℕ}
    (hi : powerResidueIterate n M i = 1) :
    powerResidueIterate n M (i + k) = powerResidueIterate n M k := by
  calc
    powerResidueIterate n M (i + k) = n ^ (i + k) % M :=
      powerResidueIterate_eq_pow_mod n M (i + k)
    _ = (n ^ i * n ^ k) % M := by rw [Nat.pow_add]
    _ = (n ^ i % M * n ^ k) % M := (Nat.mod_mul_mod _ _ _).symm
    _ = n ^ k % M := by
      rw [← powerResidueIterate_eq_pow_mod n M i, hi]
      simp only [one_mul]
    _ = powerResidueIterate n M k :=
      (powerResidueIterate_eq_pow_mod n M k).symm

/-- Every later residue repeats the corresponding residue in the first period once a positive
iterate is one. This iterates the one-period shift and is the exact cycle fact used to justify
the `r = 1` early stop after all earlier residues have been checked. -/
theorem powerResidueIterate_periodic_of_eq_one {n M i q k : ℕ}
    (hi : powerResidueIterate n M i = 1) :
    powerResidueIterate n M (i * q + k) = powerResidueIterate n M k := by
  induction q with
  | zero => simp only [Nat.mul_zero, Nat.zero_add]
  | succ q ih =>
      rw [Nat.mul_succ]
      calc
        powerResidueIterate n M (i * q + i + k) =
            powerResidueIterate n M (i + (i * q + k)) := by
          congr 1
          calc
            i * q + i + k = i * q + (i + k) := Nat.add_assoc _ _ _
            _ = i + (i * q + k) := Nat.add_left_comm _ _ _
        _ = powerResidueIterate n M (i * q + k) := powerResidueIterate_add_of_eq_one hi
        _ = powerResidueIterate n M k := ih

/-- If a residue is one at index `i`, every later residue equals the residue at its index modulo
`i`. For positive `i`, the right-hand index is strictly earlier, so all future scan states have
already been visited when the loop reaches this `1`. -/
theorem powerResidueIterate_eq_mod_index_of_eq_one {n M i j : ℕ}
    (hi : powerResidueIterate n M i = 1) :
    powerResidueIterate n M j = powerResidueIterate n M (j % i) := by
  calc
    powerResidueIterate n M j =
        powerResidueIterate n M (i * (j / i) + j % i) := by rw [Nat.div_add_mod]
    _ = powerResidueIterate n M (j % i) := powerResidueIterate_periodic_of_eq_one hi

/-- If every positive residue before `i` has been checked and the residue at `i` is one, no
later exponent can reveal a new proper divisor. The cycle reduces each later index modulo `i`;
the zero residue is one, and every positive remainder belongs to the already checked prefix. -/
theorem powerResidueIterate_no_proper_after_eq_one {n M i : ℕ}
    (hM : 1 < M) (hiPos : 0 < i) (hprefix : ∀ j, 0 < j → j < i →
      ¬ (1 < powerResidueIterate n M j ∧ powerResidueIterate n M j < n ∧
        powerResidueIterate n M j ∣ n))
    (hi : powerResidueIterate n M i = 1) :
    ∀ j, i ≤ j →
      ¬ (1 < powerResidueIterate n M j ∧ powerResidueIterate n M j < n ∧
        powerResidueIterate n M j ∣ n) := by
  intro j hji
  have hcycle := powerResidueIterate_eq_mod_index_of_eq_one (j := j) hi
  intro hproper
  by_cases hj0 : j % i = 0
  · have hres : powerResidueIterate n M j = 1 := by
      rw [hcycle, hj0]
      change 1 % M = 1
      exact Nat.mod_eq_of_lt hM
    rw [hres] at hproper
    exact Nat.lt_irrefl 1 hproper.1
  · have hjmodPos : 0 < j % i := Nat.pos_of_ne_zero hj0
    have hjmodLt : j % i < i := Nat.mod_lt j hiPos
    apply hprefix (j % i) hjmodPos hjmodLt
    rw [← hcycle]
    exact hproper

/-- Search exponents below the orbit length for a remainder that is a proper divisor of `n`.
The result is `some i` for the first positive exponent with `1 < n^i % M < n` and that
remainder dividing `n`; `none` means no such proper divisor was found. -/
def powerDivisorScan (n M t : ℕ) : Option ℕ :=
  (List.range t).find? (fun i =>
    decide (0 < i ∧ 1 < powerResidueIterate n M i ∧
      powerResidueIterate n M i < n ∧ powerResidueIterate n M i ∣ n))

/-- Tail-recursive implementation of the bounded residue scan. Unlike the specification above,
this carries the current residue forward and performs one modular multiplication per exponent. -/
def powerDivisorScanLoopAux (n M : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _ => none
  | remaining + 1, i, r =>
      if 0 < i ∧ 1 < r ∧ r < n ∧ r ∣ n then some i
      else powerDivisorScanLoopAux n M remaining (i + 1) (r * n % M)
termination_by k _ _ => k

/-- Run the carried-state scan over the exponents `1 ≤ i < t`. -/
def powerDivisorScanLoop (n M t : ℕ) : Option ℕ :=
  powerDivisorScanLoopAux n M (t - 1) 1 (n % M)

/-- Early-stopping scan variant. If the current residue is one, it stops instead of processing
the remaining exponents; correctness follows when all earlier positive residues were checked. -/
def powerDivisorScanLoopEarlyAux (n M : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _ => none
  | remaining + 1, i, r =>
      if 0 < i ∧ 1 < r ∧ r < n ∧ r ∣ n then some i
      else if r = 1 then none
      else powerDivisorScanLoopEarlyAux n M remaining (i + 1) (r * n % M)

/-- Run the early-stopping scan from exponent one. -/
def powerDivisorScanLoopEarly (n M t : ℕ) : Option ℕ :=
  powerDivisorScanLoopEarlyAux n M (t - 1) 1 (n % M)

/-- A successful recursive loop call returns an index in its processed interval with a proper
divisor residue. The state equality ties every multiplication step back to the mathematical power.
-/
theorem powerDivisorScanLoopAux_some_spec {n M remaining i r j : ℕ}
    (hstate : r = powerResidueIterate n M i)
    (hscan : powerDivisorScanLoopAux n M remaining i r = some j) :
    i ≤ j ∧ j < i + remaining ∧ 0 < j ∧
      1 < powerResidueIterate n M j ∧ powerResidueIterate n M j < n ∧
      powerResidueIterate n M j ∣ n := by
  induction remaining generalizing i r j with
  | zero =>
      simp only [powerDivisorScanLoopAux] at hscan
      cases hscan
  | succ remaining ih =>
      by_cases hcur : 0 < i ∧ 1 < r ∧ r < n ∧ r ∣ n
      · have hscan' : some i = some j := by
          simpa only [powerDivisorScanLoopAux, ite_eq_left hcur] using hscan
        have hj : i = j := by injection hscan'
        subst j
        rw [hstate] at hcur
        exact ⟨le_rfl, Nat.lt_add_of_pos_right (Nat.succ_pos remaining),
          hcur.1, hcur.2.1, hcur.2.2.1, hcur.2.2.2⟩
      · have hscan' : powerDivisorScanLoopAux n M remaining (i + 1)
            (r * n % M) = some j := by
          simpa only [powerDivisorScanLoopAux, ite_eq_right hcur] using hscan
        have hnext : r * n % M = powerResidueIterate n M (i + 1) := by
          rw [hstate, powerResidueIterate]
        obtain ⟨hij, hjbound, hjpos, hjlo, hjhi, hjdvd⟩ :=
          ih hnext hscan'
        have hadd : i + 1 + remaining = i + (remaining + 1) :=
          (Nat.add_assoc i 1 remaining).trans
            (congrArg (fun k => i + k) (Nat.add_comm 1 remaining))
        have hjbound' : j < i + (remaining + 1) := Nat.lt_of_lt_of_eq hjbound hadd
        exact ⟨Nat.le_trans (Nat.le_succ i) hij, hjbound', hjpos, hjlo, hjhi, hjdvd⟩

/-- A successful carried-state scan returns a genuine divisor candidate at an exponent below
`t`, matching the specification scan's witness contract. -/
theorem powerDivisorScanLoop_some_spec {n M t i : ℕ}
    (hscan : powerDivisorScanLoop n M t = some i) :
    0 < i ∧ i < t ∧ 1 < powerResidueIterate n M i ∧
      powerResidueIterate n M i < n ∧ powerResidueIterate n M i ∣ n := by
  have hstate : n % M = powerResidueIterate n M 1 := by
    change n % M = 1 % M * n % M
    simpa only [one_mul] using (Nat.mod_mul_mod 1 n M).symm
  obtain ⟨hstart, hbound, hpos, hlo, hhi, hdvd⟩ :=
    powerDivisorScanLoopAux_some_spec hstate hscan
  have honeLt : 1 < 1 + (t - 1) := Nat.lt_of_le_of_lt hstart hbound
  have hsub : 0 < t - 1 := Nat.add_lt_add_iff_left.mp honeLt
  have htlt : 1 < t := Nat.lt_sub_iff_add_lt.mp hsub
  have ht : 1 ≤ t := Nat.le_of_lt htlt
  have heq : 1 + (t - 1) = t :=
    (Nat.add_comm 1 (t - 1)).trans (Nat.sub_add_cancel ht)
  exact ⟨hpos, Nat.lt_of_lt_of_eq hbound heq, hlo, hhi, hdvd⟩

/-- The carried-state loop returns `none` exactly when no exponent in its processed interval
has a proper divisor residue. `hstate` is the loop invariant connecting the current residue to
the corresponding power modulo `M`. -/
theorem powerDivisorScanLoopAux_eq_none_iff {n M remaining i r : ℕ}
    (hstate : r = powerResidueIterate n M i) :
    powerDivisorScanLoopAux n M remaining i r = none ↔
      ∀ j, j < remaining →
        ¬ (0 < i + j ∧ 1 < powerResidueIterate n M (i + j) ∧
          powerResidueIterate n M (i + j) < n ∧
          powerResidueIterate n M (i + j) ∣ n) := by
  induction remaining generalizing i r with
  | zero =>
      simp only [powerDivisorScanLoopAux]
      constructor
      · intro _ j hj
        exact False.elim (Nat.not_lt_zero _ hj)
      · intro _
        trivial
  | succ remaining ih =>
      by_cases hcur : 0 < i ∧ 1 < r ∧ r < n ∧ r ∣ n
      · simp only [powerDivisorScanLoopAux, ite_eq_left hcur]
        constructor
        · intro h
          cases h
        · intro h
          have hbad := h 0 (Nat.zero_lt_succ remaining)
          have hcur' : 0 < i ∧ 1 < powerResidueIterate n M i ∧
              powerResidueIterate n M i < n ∧ powerResidueIterate n M i ∣ n := by
            rw [← hstate]
            exact hcur
          exact False.elim (hbad (by simpa only [Nat.add_zero] using hcur'))
      · have hnext : r * n % M = powerResidueIterate n M (i + 1) := by
          rw [hstate, powerResidueIterate]
        simp only [powerDivisorScanLoopAux, ite_eq_right hcur]
        rw [ih hnext]
        constructor
        · intro h j hj
          by_cases hj0 : j = 0
          · subst j
            have hcurrent :
                ¬ (0 < i ∧ 1 < powerResidueIterate n M i ∧
                  powerResidueIterate n M i < n ∧ powerResidueIterate n M i ∣ n) := by
              intro hp
              have hp' : 0 < i ∧ 1 < r ∧ r < n ∧ r ∣ n := by
                rw [hstate]
                exact hp
              exact hcur hp'
            simpa only [Nat.add_zero] using hcurrent
          · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
            have hklt : k < remaining := by exact Nat.lt_of_succ_lt_succ hj
            have htail := h k hklt
            have heq : (i + 1) + k = i + (k + 1) := by
              rw [Nat.add_assoc, Nat.add_comm 1 k]
            rw [heq] at htail
            exact htail
        · intro h j hj
          have hjNext : j + 1 < remaining + 1 := Nat.succ_lt_succ hj
          have htail := h (j + 1) hjNext
          have heq : i + (j + 1) = (i + 1) + j := by
            rw [Nat.add_assoc, Nat.add_comm 1 j]
          rw [heq] at htail
          exact htail

/-- The early-stopping loop has the same result as the complete loop, provided the incoming
prefix has already been checked and the state is the corresponding modular power. This is the
formal justification for stopping at residue one. -/
theorem powerDivisorScanLoopEarlyAux_eq_loopAux {n M remaining i r : ℕ}
    (hM : 1 < M) (hiPos : 0 < i)
    (hstate : r = powerResidueIterate n M i)
    (hprefix : ∀ j, 0 < j → j < i →
      ¬ (1 < powerResidueIterate n M j ∧ powerResidueIterate n M j < n ∧
        powerResidueIterate n M j ∣ n)) :
    powerDivisorScanLoopEarlyAux n M remaining i r =
      powerDivisorScanLoopAux n M remaining i r := by
  induction remaining generalizing i r with
  | zero => simp only [powerDivisorScanLoopEarlyAux, powerDivisorScanLoopAux]
  | succ remaining ih =>
      by_cases hcur : 0 < i ∧ 1 < r ∧ r < n ∧ r ∣ n
      · simp only [powerDivisorScanLoopEarlyAux, powerDivisorScanLoopAux,
          ite_eq_left hcur]
      · by_cases hr : r = 1
        · have hiOne : powerResidueIterate n M i = 1 := by rw [← hstate, hr]
          have hnoLater := powerResidueIterate_no_proper_after_eq_one hM hiPos hprefix hiOne
          have hfullNone : powerDivisorScanLoopAux n M (remaining + 1) i r = none :=
            (powerDivisorScanLoopAux_eq_none_iff hstate).2 (by
              intro j hj
              have hfuture := hnoLater (i + j) (Nat.le_add_right i j)
              exact fun hbad => hfuture hbad.2)
          simp only [powerDivisorScanLoopEarlyAux, ite_eq_right hcur,
            ite_eq_left hr, hfullNone]
        · have hnext : r * n % M = powerResidueIterate n M (i + 1) := by
            rw [hstate, powerResidueIterate]
          have hprefixNext : ∀ j, 0 < j → j < i + 1 →
              ¬ (1 < powerResidueIterate n M j ∧ powerResidueIterate n M j < n ∧
                powerResidueIterate n M j ∣ n) := by
            intro j hj hjlt
            by_cases hji : j = i
            · subst j
              intro hp
              apply hcur
              have hp' : 0 < i ∧ 1 < r ∧ r < n ∧ r ∣ n := by
                rw [hstate]
                exact ⟨hj, hp.1, hp.2.1, hp.2.2⟩
              exact hp'
            · exact hprefix j hj (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hjlt) hji)
          have hrec := ih (Nat.succ_pos i) hnext hprefixNext
          simp only [powerDivisorScanLoopEarlyAux, ite_eq_right hcur,
            ite_eq_right hr, powerDivisorScanLoopAux]
          exact hrec

/-- From exponent one, the `r = 1` early-stop loop is observationally equal to the complete
carried-state scan. The initial prefix is empty, and the modulus lower bound makes residue zero
at index zero equal to one in the cycle argument. -/
theorem powerDivisorScanLoopEarly_eq_loop {n M t : ℕ} (hM : 1 < M) :
    powerDivisorScanLoopEarly n M t = powerDivisorScanLoop n M t := by
  have hstate : n % M = powerResidueIterate n M 1 := by
    change n % M = 1 % M * n % M
    simpa only [one_mul] using (Nat.mod_mul_mod 1 n M).symm
  have hprefix : ∀ j, 0 < j → j < 1 →
      ¬ (1 < powerResidueIterate n M j ∧ powerResidueIterate n M j < n ∧
        powerResidueIterate n M j ∣ n) := by
    intro j hjpos hjlt _
    exact (Nat.not_lt_of_ge (Nat.succ_le_iff.mpr hjpos)) hjlt
  unfold powerDivisorScanLoopEarly powerDivisorScanLoop
  exact powerDivisorScanLoopEarlyAux_eq_loopAux hM (Nat.zero_lt_succ 0) hstate hprefix

/-- A successful early-stop scan returns the same proper-divisor witness as the full loop. -/
theorem powerDivisorScanLoopEarly_some_spec {n M t i : ℕ} (hM : 1 < M)
    (hscan : powerDivisorScanLoopEarly n M t = some i) :
    0 < i ∧ i < t ∧ 1 < powerResidueIterate n M i ∧
      powerResidueIterate n M i < n ∧ powerResidueIterate n M i ∣ n := by
  apply powerDivisorScanLoop_some_spec
  rw [← powerDivisorScanLoopEarly_eq_loop hM]
  exact hscan

/-- The carried-state scan and the finite specification scan agree on the `none` result.
The auxiliary theorem exposes the processed exponent interval; this wrapper identifies it with
the positive exponents strictly below `t`. -/
theorem powerDivisorScanLoop_eq_none_iff {n M t : ℕ} :
    powerDivisorScanLoop n M t = none ↔
      ∀ i, 0 < i → i < t →
        ¬ (1 < powerResidueIterate n M i ∧ powerResidueIterate n M i < n ∧
          powerResidueIterate n M i ∣ n) := by
  have hstate : n % M = powerResidueIterate n M 1 := by
    change n % M = 1 % M * n % M
    simpa only [one_mul] using (Nat.mod_mul_mod 1 n M).symm
  rw [powerDivisorScanLoop, powerDivisorScanLoopAux_eq_none_iff hstate]
  constructor
  · intro h i hi hit
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    have h' := h j (Nat.lt_sub_iff_add_lt.mpr hit)
    intro hp
    apply h'
    refine ⟨Nat.add_pos_left Nat.zero_lt_one j, ?_⟩
    simpa only [Nat.add_comm] using hp
  · intro h j hj
    have h' := h (j + 1) (Nat.zero_lt_succ j) (Nat.lt_sub_iff_add_lt.mp hj)
    rintro ⟨_, hp⟩
    apply h'
    simpa only [Nat.add_comm] using hp

/-- The early-stop implementation returns the same `none` condition as the complete finite scan.
-/
theorem powerDivisorScanLoopEarly_eq_none_iff {n M t : ℕ} (hM : 1 < M) :
    powerDivisorScanLoopEarly n M t = none ↔
      ∀ i, 0 < i → i < t →
        ¬ (1 < powerResidueIterate n M i ∧ powerResidueIterate n M i < n ∧
          powerResidueIterate n M i ∣ n) := by
  rw [powerDivisorScanLoopEarly_eq_loop hM]
  exact powerDivisorScanLoop_eq_none_iff

/-- Prime inputs produce no candidate in the early-stop loop. -/
theorem powerDivisorScanLoopEarly_eq_none_of_prime {n M t : ℕ}
    (hM : 1 < M) (hn : Nat.Prime n) : powerDivisorScanLoopEarly n M t = none := by
  apply powerDivisorScanLoopEarly_eq_none_iff hM |>.mpr
  intro i hip hit ⟨hlo, hhi, hdiv⟩
  rcases (Nat.dvd_prime hn).mp hdiv with heq | heq
  · exact (Nat.ne_of_gt hlo) heq
  · rw [heq] at hhi
    exact Nat.lt_irrefl _ hhi

/-- Prime inputs are rejected by the carried-state divisor scan. -/
theorem powerDivisorScanLoop_eq_none_of_prime {n M t : ℕ} (hn : Nat.Prime n) :
    powerDivisorScanLoop n M t = none := by
  apply powerDivisorScanLoop_eq_none_iff.mpr
  intro i hip hit ⟨hlo, hhi, hdiv⟩
  rcases (Nat.dvd_prime hn).mp hdiv with heq | heq
  · exact (Nat.ne_of_gt hlo) heq
  · rw [heq] at hhi
    exact Nat.lt_irrefl _ hhi

/-- The finite scan returns `none` exactly when every positive exponent below `t` is rejected.
This connects the executable early-termination search to the hypothesis consumed by the final
prime criterion. -/
theorem powerDivisorScan_eq_none_iff {n M t : ℕ} :
    powerDivisorScan n M t = none ↔
      ∀ i, 0 < i → i < t →
        ¬ (1 < n ^ i % M ∧ n ^ i % M < n ∧ n ^ i % M ∣ n) := by
  simp only [powerDivisorScan, List.find?_eq_none, List.mem_range, decide_eq_true_eq,
    powerResidueIterate_eq_pow_mod]
  constructor
  · intro h i hip hit hproper
    exact h i hit ⟨hip, hproper.1, hproper.2.1, hproper.2.2⟩
  · intro h i hit ⟨hip, hlo, hhi, hdiv⟩
    exact h i hip hit ⟨hlo, hhi, hdiv⟩

/-- A successful scan returns a positive exponent below the scan bound whose remainder divides
the input. The `Option` payload is therefore a concrete factor-search witness, not just a flag. -/
theorem powerDivisorScan_some_spec {n M t i : ℕ}
    (hscan : powerDivisorScan n M t = some i) :
    0 < i ∧ i < t ∧ 1 < n ^ i % M ∧ n ^ i % M < n ∧ n ^ i % M ∣ n := by
  have hfind := List.find?_range_eq_some.mp hscan
  have hpred := of_decide_eq_true hfind.1
  rw [powerResidueIterate_eq_pow_mod] at hpred
  exact ⟨hpred.1, List.mem_range.mp hfind.2.1, hpred.2.1, hpred.2.2.1, hpred.2.2.2⟩

/-- Prime inputs cannot produce a proper divisor in the finite residue scan. This establishes
the prime-side behavior of the executable scan independently of any APR-CL hypotheses. -/
theorem powerDivisorScan_eq_none_of_prime {n M t : ℕ} (hn : Nat.Prime n) :
    powerDivisorScan n M t = none := by
  apply powerDivisorScan_eq_none_iff.mpr
  intro i _ _ ⟨hlo, hhi, hdiv⟩
  rcases (Nat.dvd_prime hn).mp hdiv with heq | heq
  · exact (Nat.ne_of_gt hlo) heq
  · rw [heq] at hhi
    exact Nat.lt_irrefl _ hhi

/-- A prime-factor orbit restriction plus the failed proper-divisor scan proves primality.
Inputs are `2 ≤ n`, `2 ≤ M`, `n < M^2`, an orbit representative for every prime divisor,
and rejection of every scanned remainder strictly between `1` and `n` that divides `n`. A
composite input has a least prime factor at most its square root; the orbit congruence identifies
that factor with a scanned remainder, while exponent zero would force the factor to be one.
This is the elementary A1 consumer of
the orbit theorem and is independent of the APR-CL local kernel. -/
theorem prime_of_powerOrbit_no_divisor {n M t : ℕ} (hn : 2 ≤ n) (hM : 2 ≤ M)
    (hsize : n < M * M)
    (horbit : ∀ ℓ, Nat.Prime ℓ → ℓ ∣ n →
      ∃ i, i < t ∧ Nat.ModEq M ℓ (n ^ i))
    (hnodiv : ∀ i, 0 < i → i < t →
      ¬ (1 < n ^ i % M ∧ n ^ i % M < n ∧ n ^ i % M ∣ n)) : Nat.Prime n := by
  by_contra hnp
  let ℓ := Nat.minFac n
  have hnne : n ≠ 1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hn)
  have hℓprime : Nat.Prime ℓ := Nat.minFac_prime hnne
  have hℓdvd : ℓ ∣ n := Nat.minFac_dvd n
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
  have hℓle : ℓ ≤ n / ℓ := Nat.minFac_le_div hnpos hnp
  have hℓsq : ℓ * ℓ ≤ n := (Nat.le_div_iff_mul_le hℓprime.pos).mp hℓle
  have hℓltM : ℓ < M := by
    by_contra hnot
    have hMle : M ≤ ℓ := Nat.le_of_not_gt hnot
    have hprod : M * M ≤ ℓ * ℓ := Nat.mul_le_mul hMle hMle
    exact Nat.not_le_of_gt hsize (Nat.le_trans hprod hℓsq)
  obtain ⟨i, hit, hres⟩ := horbit ℓ hℓprime hℓdvd
  change ℓ % M = n ^ i % M at hres
  rw [Nat.mod_eq_of_lt hℓltM] at hres
  by_cases hi : i = 0
  · subst i
    simp only [pow_zero, Nat.mod_eq_of_lt
      (Nat.lt_of_lt_of_le (by decide : 1 < 2) hM)] at hres
    exact hℓprime.ne_one hres
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi
    apply hnodiv i hiPos hit
    rw [← hres]
    exact ⟨hℓprime.one_lt, Nat.not_prime_iff_minFac_lt hn |>.mp hnp, hℓdvd⟩

/-- The final divisor-orbit criterion specialized to the APR-CL modulus.
Inputs are a natural parameter, the square-root size bound, the prime-factor orbit condition
modulo `modulus t`, and rejection of every positive-index remainder as a divisor. The modulus
is at least two because it is positive and divisible by two. This is the direct final-stage
consumer for the orbit theorem. The wrapper is valid for the total modulus definition; for the
paper's canonical `e(t)`, use an even parameter as required by the fixed APR-CL setup. -/
theorem prime_of_modulus_powerOrbit_no_divisor {n t : ℕ} (hn : 2 ≤ n)
    (hsize : n < modulus t * modulus t)
    (horbit : ∀ ℓ, Nat.Prime ℓ → ℓ ∣ n →
      ∃ i, i < t ∧ Nat.ModEq (modulus t) ℓ (n ^ i))
    (hnodiv : ∀ i, 0 < i → i < t →
      ¬ (1 < n ^ i % modulus t ∧ n ^ i % modulus t < n ∧ n ^ i % modulus t ∣ n)) :
    Nat.Prime n := by
  apply prime_of_powerOrbit_no_divisor hn
    (Nat.le_of_dvd (modulus_pos t) (two_dvd_modulus t)) hsize horbit hnodiv

/-- The executable divisor scan can be passed directly to the final APR-CL criterion.
If it finds no positive proper-power remainder dividing `n`, the prime-factor orbit condition
and modulus size bound certify primality. -/
theorem prime_of_modulus_powerOrbit_scan_none {n t : ℕ} (hn : 2 ≤ n)
    (hsize : n < modulus t * modulus t)
    (horbit : ∀ ℓ, Nat.Prime ℓ → ℓ ∣ n →
      ∃ i, i < t ∧ Nat.ModEq (modulus t) ℓ (n ^ i))
    (hscan : powerDivisorScan n (modulus t) t = none) : Nat.Prime n := by
  apply prime_of_modulus_powerOrbit_no_divisor hn hsize horbit
  exact (powerDivisorScan_eq_none_iff.mp hscan)

/-- The carried-state residue loop is a direct executable consumer of the final APR-CL criterion.
When its scan finds no proper divisor and the orbit theorem supplies the prime-factor residues,
the input is prime. -/
theorem prime_of_modulus_powerOrbit_scanLoop_none {n t : ℕ} (hn : 2 ≤ n)
    (hsize : n < modulus t * modulus t)
    (horbit : ∀ ℓ, Nat.Prime ℓ → ℓ ∣ n →
      ∃ i, i < t ∧ Nat.ModEq (modulus t) ℓ (n ^ i))
    (hscan : powerDivisorScanLoop n (modulus t) t = none) : Nat.Prime n := by
  apply prime_of_modulus_powerOrbit_no_divisor hn hsize horbit
  intro i hip hit hproper
  exact (powerDivisorScanLoop_eq_none_iff.mp hscan) i hip hit
    (by simpa only [powerResidueIterate_eq_pow_mod] using hproper)

/-- The $r=1$ early-stop loop feeds directly to the final APR-CL prime criterion. -/
theorem prime_of_modulus_powerOrbit_scanLoopEarly_none {n t : ℕ} (hn : 2 ≤ n)
    (hsize : n < modulus t * modulus t)
    (horbit : ∀ ℓ, Nat.Prime ℓ → ℓ ∣ n →
      ∃ i, i < t ∧ Nat.ModEq (modulus t) ℓ (n ^ i))
    (hscan : powerDivisorScanLoopEarly n (modulus t) t = none) : Nat.Prime n := by
  have hM : 1 < modulus t := by
    have := Nat.le_of_dvd (modulus_pos t) (two_dvd_modulus t)
    exact Nat.lt_of_lt_of_le (by decide : 1 < 2) this
  have hfull : powerDivisorScanLoop n (modulus t) t = none := by
    rw [← powerDivisorScanLoopEarly_eq_loop hM]
    exact hscan
  exact prime_of_modulus_powerOrbit_scanLoop_none hn hsize horbit hfull

/-- For each prime divisor of `n`, a common orbit exponent modulo every local
prime-power block is equivalent to an orbit exponent modulo the full APR-CL
modulus. The forward and reverse directions use the exact CRT decomposition. -/
theorem primeFactor_localOrbit_iff_powerOrbit {n t : ℕ} (ht : t ≠ 0) :
    (∀ ℓ, Nat.Prime ℓ → ℓ ∣ n →
      ∃ i, i < t ∧
        Nat.ModEq (2 ^ (2 + Nat.factorization t 2)) ℓ (n ^ i) ∧
        ∀ q ∈ (auxiliaryPrimes t).erase 2,
          Nat.ModEq (q ^ (1 + Nat.factorization t q)) ℓ (n ^ i)) ↔
      (∀ ℓ, Nat.Prime ℓ → ℓ ∣ n →
        ∃ i, i < t ∧ Nat.ModEq (modulus t) ℓ (n ^ i)) := by
  constructor
  · intro hlocal ℓ hprime hdvd
    obtain ⟨i, hit, htwo, hodd⟩ := hlocal ℓ hprime hdvd
    exact ⟨i, hit, (modEq_modulus_iff_local ht).mpr ⟨htwo, hodd⟩⟩
  · intro hfull ℓ hprime hdvd
    obtain ⟨i, hit, hmod⟩ := hfull ℓ hprime hdvd
    obtain ⟨htwo, hodd⟩ := (modEq_modulus_iff_local ht).mp hmod
    exact ⟨i, hit, htwo, hodd⟩

/-- A common exponent for each prime factor that matches every prime-power block
feeds the early-stop divisor scan through the full APR-CL modulus. The local
congruences are the remaining A5/A6 number-theoretic input. -/
theorem prime_of_modulus_localOrbit_scanLoopEarly_none {n t : ℕ}
    (ht : t ≠ 0) (hn : 2 ≤ n)
    (hsize : n < modulus t * modulus t)
    (hlocal : ∀ ℓ, Nat.Prime ℓ → ℓ ∣ n →
      ∃ i, i < t ∧
        Nat.ModEq (2 ^ (2 + Nat.factorization t 2)) ℓ (n ^ i) ∧
        ∀ q ∈ (auxiliaryPrimes t).erase 2,
          Nat.ModEq (q ^ (1 + Nat.factorization t q)) ℓ (n ^ i))
    (hscan : powerDivisorScanLoopEarly n (modulus t) t = none) :
    Nat.Prime n := by
  apply prime_of_modulus_powerOrbit_scanLoopEarly_none hn hsize
  · exact (primeFactor_localOrbit_iff_powerOrbit ht).mp hlocal
  · exact hscan

/-- If each prime factor has residues indexed by the prime divisors of `t`,
and those residues imply every required modulus-block congruence for a matching
exponent, finite CRT supplies one common exponent below `t`. This theorem
isolates the still-required A5/A6 local number-theoretic implication. -/
theorem primeFactor_localOrbit_of_residueConditions {n t : ℕ}
    (ht : t ≠ 0) (a : ℕ → ℕ → ℕ)
    (hblocks : ∀ ℓ, Nat.Prime ℓ → ℓ ∣ n → ∀ i,
      (∀ p ∈ t.primeFactors,
        Nat.ModEq (p ^ Nat.factorization t p) i (a ℓ p)) →
      Nat.ModEq (2 ^ (2 + Nat.factorization t 2)) ℓ (n ^ i) ∧
        ∀ q ∈ (auxiliaryPrimes t).erase 2,
          Nat.ModEq (q ^ (1 + Nat.factorization t q)) ℓ (n ^ i)) :
    ∀ ℓ, Nat.Prime ℓ → ℓ ∣ n →
      ∃ i, i < t ∧
        Nat.ModEq (2 ^ (2 + Nat.factorization t 2)) ℓ (n ^ i) ∧
        ∀ q ∈ (auxiliaryPrimes t).erase 2,
          Nat.ModEq (q ^ (1 + Nat.factorization t q)) ℓ (n ^ i) := by
  intro ℓ hprime hdvd
  obtain ⟨i, hit, hres⟩ := exists_commonExponent_mod_primePowers ht (a ℓ)
  obtain ⟨htwo, hodd⟩ := hblocks ℓ hprime hdvd i hres
  exact ⟨i, hit, htwo, hodd⟩

/-- The finite CRT exponent and block implication feed the executable APR-CL
early-stop scan. Inputs include the size bound and the missing local arithmetic
implication; the conclusion is a proof of primality of the original input. -/
theorem prime_of_residueConditions_scanLoopEarly_none {n t : ℕ}
    (ht : t ≠ 0) (hn : 2 ≤ n)
    (hsize : n < modulus t * modulus t)
    (a : ℕ → ℕ → ℕ)
    (hblocks : ∀ ℓ, Nat.Prime ℓ → ℓ ∣ n → ∀ i,
      (∀ p ∈ t.primeFactors,
        Nat.ModEq (p ^ Nat.factorization t p) i (a ℓ p)) →
      Nat.ModEq (2 ^ (2 + Nat.factorization t 2)) ℓ (n ^ i) ∧
        ∀ q ∈ (auxiliaryPrimes t).erase 2,
          Nat.ModEq (q ^ (1 + Nat.factorization t q)) ℓ (n ^ i))
    (hscan : powerDivisorScanLoopEarly n (modulus t) t = none) :
    Nat.Prime n := by
  exact prime_of_modulus_localOrbit_scanLoopEarly_none ht hn hsize
    (primeFactor_localOrbit_of_residueConditions ht a hblocks) hscan

end PseudoPrime.PrimeTest.APRCL
