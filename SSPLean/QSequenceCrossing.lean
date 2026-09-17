import Mathlib
import SSPLean.QSequencePaths
import SSPLean.PathEnergy
import SSPLean.SpectralDecay
import SSPLean.SpectralRadiusLtOne

/-!
# Discharging the crossing bound: the weighted-path expansion

This module completes the **first proof** ("weighted paths") of the q-sequence bound by
*proving* `SSP.CrossingBound` — the estimate `(Ne)ᵢ² / s ≤ vᵢ` that `QSequencePaths.lean`
had isolated as a hypothesis.  Combined with the identity `vᵢ = 2yᵢ − xᵢ²`, this discharges
the paper's Lemma 5 (`SSP.ComponentBound`) unconditionally, hence the `r ≤ 2s` bound
(`qsequence_ssp_bound_unconditional`, below) is fully machine-verified with no assumed input.

## The argument

For each state `i`, the resolvent identity expands `vᵢ = N gᵢ` as a sum over finite weighted
paths from `i` to the absorbing floor:
`  vᵢ = ∑'_m ∑_{p : Fin(m+1)→Fin s, p₀ = i} pathWeight p · pathEnergy p`   (`hasSum_PWterm`),
where `pathWeight p = pathProd p · b_{p_last}` (the transition-weight product times terminal
absorption) and `pathEnergy p` is the sum of squared level changes plus the final drop to `0`.
The total path weight is `1` (`tsum_TWterm_eq_one`, a telescoping `(Qᵐe)ᵢ − (Qᵐ⁺¹e)ᵢ`), and
every path has energy `≥ xᵢ²/s` by the level-crossing Cauchy–Schwarz bound `path_energy_ge`
(applied to the clamped level sequence, since path levels can exceed `xᵢ`).  Averaging the
per-path bound against the weight-`1` path measure yields `vᵢ ≥ xᵢ²/s`.

The expansion identity itself is proved not by an infinite reindexing but by a **fixed-point
uniqueness** argument (`eq_zero_of_Q_fixed`): the path-sum `Pᵢ := ∑'_m PWtermᵢ m` satisfies the
same recurrence `P = g + Q·P` as `v = N g`, and both are bounded, so they coincide.
-/

open Finset

namespace SSP

/-- Weight of a length-`m` path: transition product times terminal absorption `b`. -/
noncomputable def pathWeight (s : ℕ) (Q : ℕ → ℕ → ℝ) (m : ℕ) (p : Fin (m + 1) → Fin s) : ℝ :=
  pathProd s Q m p * bVec s Q (p (Fin.last m) : ℕ)

/-- Energy of a length-`m` path: squared level changes plus final drop to `0`. -/
noncomputable def pathEnergy (s : ℕ) (Q : ℕ → ℕ → ℝ) (m : ℕ) (p : Fin (m + 1) → Fin s) : ℝ :=
  (∑ r : Fin m, (xVec s Q (p r.succ : ℕ) - xVec s Q (p r.castSucc : ℕ)) ^ 2)
    + (xVec s Q (p (Fin.last m) : ℕ)) ^ 2

/-! ### Basic positivity helpers -/

/-- `0 ≤ Nᵢⱼ` (entrywise Neumann series of nonnegatives). -/
lemma Nmat_nonneg (s : ℕ) (Q : ℕ → ℕ → ℝ) (hQ : ∀ i j, 0 ≤ Q i j) (i j : ℕ) :
    0 ≤ Nmat s Q i j :=
  tsum_nonneg (fun k => matPow_nonneg s Q hQ k i j)

/-- `0 ≤ xᵢ`. -/
lemma xVec_nonneg (s : ℕ) (Q : ℕ → ℕ → ℝ) (hQ : ∀ i j, 0 ≤ Q i j) (i : ℕ) :
    0 ≤ xVec s Q i :=
  matVec_nonneg s (Nmat s Q) eVec (Nmat_nonneg s Q hQ) (fun _ => by simp [eVec]) i

/-- `0 ≤ pathProd` (product of nonnegative transition weights). -/
lemma pathProd_nonneg (s : ℕ) (Q : ℕ → ℕ → ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (m : ℕ) (p : Fin (m + 1) → Fin s) :
    0 ≤ pathProd s Q m p :=
  Finset.prod_nonneg fun _ _ => hQ _ _

/-- `0 ≤ pathWeight`. -/
lemma pathWeight_nonneg (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (m : ℕ) (p : Fin (m + 1) → Fin s) :
    0 ≤ pathWeight s Q m p :=
  mul_nonneg (pathProd_nonneg s Q hQ m p)
    (bVec_nonneg s Q hsub (p (Fin.last m) : ℕ) (p (Fin.last m)).isLt)

/-! ### Step 2: the per-path energy bound -/

/-- Clamping with a constant is 1-Lipschitz: `(min c a - min c b)² ≤ (a - b)²`. -/
lemma min_sub_min_sq_le (c a b : ℝ) : (min c a - min c b) ^ 2 ≤ (a - b) ^ 2 := by
  have habs : |min c a - min c b| ≤ |a - b| := by
    have h := abs_min_sub_min_le_max c a c b
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (a - b))] using h
  rw [← sq_abs (min c a - min c b), ← sq_abs (a - b)]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- **Per-path energy bound (Step 2).**  For any length-`m` path `p` starting at `i < s`,
the path energy is at least `xᵢ² / s`.  Proved by applying `path_energy_ge` to the *clamped*
level sequence `L r = min xᵢ x_{p r}`, and observing that clamping only decreases the energy. -/
lemma pathEnergy_ge (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (_hθ0 : 0 ≤ θ) (_hθ1 : θ < 1) (_hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (_hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (_hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (hs : 0 < s)
    (i : ℕ) (hi : i < s) (m : ℕ) (p : Fin (m + 1) → Fin s) (hp0 : (p 0 : ℕ) = i) :
    (xVec s Q i) ^ 2 / s ≤ pathEnergy s Q m p := by
  -- Clamped level sequence.
  set A : ℝ := xVec s Q i with hAdef
  have hA : 0 ≤ A := xVec_nonneg s Q hQ i
  set L : Fin (m + 1) → ℝ := fun r => min A (xVec s Q (p r : ℕ)) with hLdef
  -- The grid.
  set V : Finset ℝ := insert (0 : ℝ)
      (Finset.image (fun j => min A (xVec s Q j)) (range s)) with hVdef
  -- Apply path_energy_ge.
  have hxnn : ∀ j, 0 ≤ xVec s Q j := xVec_nonneg s Q hQ
  have hkey := path_energy_ge s m hs A hA L (by
      -- L 0 = min A (x (p 0)) = min A A = A
      simp only [hLdef, hp0, ← hAdef]; exact min_self A) V
    (by -- V.card ≤ s + 1
      calc V.card ≤ (Finset.image (fun j => min A (xVec s Q j)) (range s)).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ (range s).card + 1 := by
            exact Nat.add_le_add_right (Finset.card_image_le) 1
        _ = s + 1 := by rw [Finset.card_range])
    (by -- 0 ∈ V
      exact Finset.mem_insert_self _ _)
    (by -- A ∈ V
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_image]
      exact ⟨i, Finset.mem_range.mpr hi, by rw [min_self]⟩)
    (by -- 0 ≤ L r ≤ A
      intro r
      simp only [hLdef]
      exact ⟨le_min hA (hxnn _), min_le_left _ _⟩)
    (by -- L r ∈ V
      intro r
      simp only [hLdef]
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_image]
      exact ⟨(p r : ℕ), Finset.mem_range.mpr (p r).isLt, rfl⟩)
  -- Now bound the clamped energy by the true path energy.
  refine le_trans hkey ?_
  simp only [pathEnergy]
  apply add_le_add
  · -- ∑ (L succ - L castSucc)² ≤ ∑ (x succ - x castSucc)²
    apply Finset.sum_le_sum
    intro r _
    simp only [hLdef]
    exact min_sub_min_sq_le A (xVec s Q (p r.succ : ℕ)) (xVec s Q (p r.castSucc : ℕ))
  · -- (L last)² ≤ (x last)²
    simp only [hLdef]
    have h1 : 0 ≤ min A (xVec s Q (p (Fin.last m) : ℕ)) :=
      le_min hA (hxnn _)
    have h2 : min A (xVec s Q (p (Fin.last m) : ℕ)) ≤ xVec s Q (p (Fin.last m) : ℕ) :=
      min_le_right _ _
    nlinarith [h1, h2]

/-! ### Step 1 & 3: path-sum expansions and the reassembly -/

/-- **Path-sum form of `(Qᵏ w)ᵢ`.**  For any weight vector `w` and `i < s`,
`(Qᵏ w)ᵢ = ∑_{p : Fin(k+1)→Fin s, p 0 = i} pathProd p · w (p last)`. -/
lemma matVec_matPow_eq_pathSum (s : ℕ) (Q : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (k i : ℕ) (hi : i < s) :
    matVec s (matPow s Q k) w i
      = ∑ p : Fin (k + 1) → Fin s,
          (if (p 0 : ℕ) = i then pathProd s Q k p * w (p (Fin.last k) : ℕ) else 0) := by
  simp only [matVec]
  -- expand each matPow entry over paths ending at j, distribute w j inside the if
  have step1 : ∀ j ∈ range s, matPow s Q k i j * w j
      = ∑ p : Fin (k + 1) → Fin s,
          (if (p 0 : ℕ) = i ∧ (p (Fin.last k) : ℕ) = j then pathProd s Q k p * w j else 0) := by
    intro j hj
    rw [matPow_eq_pathSum s Q k i j hi (mem_range.1 hj), sum_mul]
    exact sum_congr rfl fun p _ => by split_ifs <;> ring
  rw [sum_congr rfl step1, Finset.sum_comm]
  -- for each p, collapse the sum over j to j = p last
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single_of_mem ((p (Fin.last k) : ℕ))
        (mem_range.2 (p (Fin.last k)).isLt)]
  · by_cases hp0 : (p 0 : ℕ) = i
    · rw [if_pos hp0, if_pos ⟨hp0, rfl⟩]
    · rw [if_neg hp0, if_neg (fun h => hp0 h.1)]
  · intro j _ hjne
    rw [if_neg (fun h => hjne h.2.symm)]

/-- The length-`m` slice of the weighted-path expansion of `v`. -/
noncomputable def PWterm (s : ℕ) (Q : ℕ → ℕ → ℝ) (i m : ℕ) : ℝ :=
  ∑ p : Fin (m + 1) → Fin s,
    (if (p 0 : ℕ) = i then pathWeight s Q m p * pathEnergy s Q m p else 0)

/-- The length-`m` slice of the total path weight. -/
noncomputable def TWterm (s : ℕ) (Q : ℕ → ℕ → ℝ) (i m : ℕ) : ℝ :=
  ∑ p : Fin (m + 1) → Fin s,
    (if (p 0 : ℕ) = i then pathWeight s Q m p else 0)

/-- `TWterm = (Qᵐ b)ᵢ`, the path-sum form applied to the defect vector `b`. -/
lemma TWterm_eq (s : ℕ) (Q : ℕ → ℕ → ℝ) (i m : ℕ) (hi : i < s) :
    TWterm s Q i m = matVec s (matPow s Q m) (bVec s Q) i := by
  rw [matVec_matPow_eq_pathSum s Q (bVec s Q) m i hi]
  simp only [TWterm, pathWeight]

/-- `0 ≤ TWterm`. -/
lemma TWterm_nonneg (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (i m : ℕ) :
    0 ≤ TWterm s Q i m := by
  refine Finset.sum_nonneg fun p _ => ?_
  split_ifs
  · exact pathWeight_nonneg s Q hQ hsub m p
  · exact le_refl 0

/-- Right-fold form applied to `e`: `(Qᵏ⁺¹ e)ᵢ = (Qᵏ (Qe))ᵢ`, where `(Qe)ⱼ = Σ_l q_{jl}`. -/
lemma matVec_matPow_succ_right_e (s : ℕ) (Q : ℕ → ℕ → ℝ) (k i : ℕ) :
    matVec s (matPow s Q (k + 1)) eVec i
      = matVec s (matPow s Q k) (fun j => ∑ l ∈ range s, Q j l) i := by
  simp only [matVec, eVec, mul_one]
  -- LHS: Σ_j matPow (k+1) i j = Σ_j (Σ_l matPow k i l * Q l j)
  simp only [matPow]
  -- RHS: Σ_j matPow k i j * (Σ_l Q j l)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]

/-- Telescoping term: `(Qᵏ b)ᵢ = (Qᵏ e)ᵢ − (Qᵏ⁺¹ e)ᵢ`. -/
lemma matVec_matPow_bVec_eq (s : ℕ) (Q : ℕ → ℕ → ℝ) (k i : ℕ) :
    matVec s (matPow s Q k) (bVec s Q) i
      = matVec s (matPow s Q k) eVec i - matVec s (matPow s Q (k + 1)) eVec i := by
  rw [matVec_matPow_succ_right_e]
  simp only [matVec, bVec, eVec, mul_one]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Total path weight is `1`** (property (b)):  `∑'_m TWterm i m = 1`.  This is the
telescoping identity `(N b)ᵢ = 1`:  `(Qᵐ b)ᵢ = (Qᵐ e)ᵢ − (Qᵐ⁺¹ e)ᵢ` telescopes to `(Q⁰ e)ᵢ`. -/
lemma tsum_TWterm_eq_one (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (_hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (i : ℕ) (hi : i < s) :
    ∑' m, TWterm s Q i m = 1 := by
  set a : ℕ → ℝ := fun k => matVec s (matPow s Q k) eVec i with ha
  -- TWterm i m = a m - a (m+1)
  have hterm : ∀ m, TWterm s Q i m = a m - a (m + 1) := by
    intro m
    rw [TWterm_eq s Q i m hi, matVec_matPow_bVec_eq]
  -- a 0 = 1
  have ha0 : a 0 = 1 := by
    simp only [ha, matVec, matPow, eVec, mul_one]
    rw [Finset.sum_ite_eq (range s) i (fun _ => (1 : ℝ)), if_pos (mem_range.2 hi)]
  -- a n → 0
  have hlim : Filter.Tendsto a Filter.atTop (nhds 0) := by
    have hbound : ∀ k, a k ≤ C * θ ^ k := fun k => hdecay k i hi
    have hnn : ∀ k, 0 ≤ a k := fun k => matVec_nonneg s (matPow s Q k) eVec
      (matPow_nonneg s Q hQ k) (fun _ => by simp [eVec]) i
    have hθlim : Filter.Tendsto (fun k => C * θ ^ k) Filter.atTop (nhds 0) := by
      have : Filter.Tendsto (fun k => θ ^ k) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1
      simpa using this.const_mul C
    exact squeeze_zero hnn hbound hθlim
  -- HasSum of the telescoping series = a 0.
  have hnn_term : ∀ m, 0 ≤ TWterm s Q i m := fun m =>
    TWterm_nonneg s Q hQ hsub i m
  have hhs : HasSum (fun m => TWterm s Q i m) (a 0) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnn_term]
    -- partial sums: ∑_{m<n} (a m - a (m+1)) = a 0 - a n → a 0
    have hpartial : ∀ n, ∑ m ∈ range n, TWterm s Q i m = a 0 - a n := by
      intro n
      rw [Finset.sum_congr rfl (fun m _ => hterm m)]
      exact Finset.sum_range_sub' a n
    simp only [hpartial]
    have : Filter.Tendsto (fun n => a 0 - a n) Filter.atTop (nhds (a 0 - 0)) :=
      Filter.Tendsto.const_sub (a 0) hlim
    simpa using this
  rw [hhs.tsum_eq, ha0]

/-- Termwise: `PWterm m ≥ TWterm m · (xᵢ²/s)` (using per-path energy ≥ xᵢ²/s and weight ≥ 0). -/
lemma PWterm_ge (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (hs : 0 < s) (i : ℕ) (hi : i < s) (m : ℕ) :
    TWterm s Q i m * ((xVec s Q i) ^ 2 / s) ≤ PWterm s Q i m := by
  simp only [PWterm, TWterm, Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  split_ifs with hp0
  · exact mul_le_mul_of_nonneg_left
      (pathEnergy_ge s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub hs i hi m p hp0)
      (pathWeight_nonneg s Q hQ hsub m p)
  · rw [zero_mul]

/-- Splitting `pathProd` over `Fin.cons`: prepending state `x` multiplies by the first edge. -/
lemma pathProd_cons (s : ℕ) (Q : ℕ → ℕ → ℝ) (m : ℕ)
    (x : Fin s) (p' : Fin (m + 1) → Fin s) :
    pathProd s Q (m + 1) (Fin.cons x p')
      = Q (x : ℕ) (p' 0 : ℕ) * pathProd s Q m p' := by
  simp only [pathProd]
  rw [Fin.prod_univ_succ]
  have hfirst : Q ((Fin.cons x p' : Fin (m + 2) → Fin s) (0 : Fin (m + 1)).castSucc : ℕ)
      ((Fin.cons x p' : Fin (m + 2) → Fin s) (0 : Fin (m + 1)).succ : ℕ)
      = Q (x : ℕ) (p' 0 : ℕ) := by
    rw [show ((0 : Fin (m + 1)).castSucc) = (0 : Fin (m + 2)) from rfl, Fin.cons_zero,
        Fin.cons_succ]
  have hrest : (∏ r : Fin m, Q ((Fin.cons x p' : Fin (m + 2) → Fin s) r.succ.castSucc : ℕ)
      ((Fin.cons x p' : Fin (m + 2) → Fin s) r.succ.succ : ℕ))
      = ∏ r : Fin m, Q (p' r.castSucc : ℕ) (p' r.succ : ℕ) := by
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
  rw [hfirst, hrest]

/-- `pathProd` of a length-0 (single-vertex) path is `1`. -/
lemma pathProd_zero (s : ℕ) (Q : ℕ → ℕ → ℝ) (p : Fin 1 → Fin s) :
    pathProd s Q 0 p = 1 := by
  simp [pathProd]

/-- `PWterm i 0 = bᵢ · xᵢ²`.  (The only length-0 path is the constant path at `i`, whose
weight is `bᵢ` and whose energy is `xᵢ²`.) -/
lemma PWterm_zero (s : ℕ) (Q : ℕ → ℕ → ℝ) (i : ℕ) (hi : i < s) :
    PWterm s Q i 0 = bVec s Q i * (xVec s Q i) ^ 2 := by
  simp only [PWterm]
  rw [Fintype.sum_eq_single (fun _ => (⟨i, hi⟩ : Fin s))]
  · have h0 : ((fun _ : Fin 1 => (⟨i, hi⟩ : Fin s)) 0 : ℕ) = i := rfl
    rw [if_pos h0]
    simp only [pathWeight, pathEnergy, pathProd_zero, one_mul,
      Finset.univ_eq_empty, Finset.sum_empty, zero_add]
  · intro p hp
    have hne : (p 0 : ℕ) ≠ i := by
      intro hval
      apply hp
      funext k
      have hk : k = 0 := Fin.eq_zero k
      subst hk
      exact Fin.ext hval
    rw [if_neg hne]

/-- Last vertex of a `cons`-path is the last vertex of the tail. -/
lemma cons_last (s m : ℕ) (x : Fin s) (p' : Fin (m + 1) → Fin s) :
    ((Fin.cons x p' : Fin (m + 2) → Fin s) (Fin.last (m + 1)) : ℕ) = (p' (Fin.last m) : ℕ) := by
  rw [show (Fin.last (m + 1)) = (Fin.last m).succ from (Fin.succ_last m).symm, Fin.cons_succ]

/-- Splitting `pathEnergy` over `Fin.cons`: prepending state `x` adds the first-edge energy. -/
lemma pathEnergy_cons (s : ℕ) (Q : ℕ → ℕ → ℝ) (m : ℕ)
    (x : Fin s) (p' : Fin (m + 1) → Fin s) :
    pathEnergy s Q (m + 1) (Fin.cons x p')
      = (xVec s Q (p' 0 : ℕ) - xVec s Q (x : ℕ)) ^ 2 + pathEnergy s Q m p' := by
  simp only [pathEnergy]
  rw [Fin.sum_univ_succ]
  rw [cons_last]
  have hfirst : (xVec s Q ((Fin.cons x p' : Fin (m + 2) → Fin s) (0 : Fin (m + 1)).succ : ℕ)
      - xVec s Q ((Fin.cons x p' : Fin (m + 2) → Fin s) (0 : Fin (m + 1)).castSucc : ℕ)) ^ 2
      = (xVec s Q (p' 0 : ℕ) - xVec s Q (x : ℕ)) ^ 2 := by
    rw [show ((0 : Fin (m + 1)).castSucc) = (0 : Fin (m + 2)) from rfl, Fin.cons_zero,
        show ((0 : Fin (m + 1)).succ) = (0 : Fin (m + 1)).succ from rfl, Fin.cons_succ]
  have hrest : (∑ r : Fin m, (xVec s Q ((Fin.cons x p' : Fin (m + 2) → Fin s) r.succ.succ : ℕ)
      - xVec s Q ((Fin.cons x p' : Fin (m + 2) → Fin s) r.succ.castSucc : ℕ)) ^ 2)
      = ∑ r : Fin m, (xVec s Q (p' r.succ : ℕ) - xVec s Q (p' r.castSucc : ℕ)) ^ 2 := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
  rw [hfirst, hrest]
  ring

/-- **The `cons` recurrence for `PWterm`.**  A length-`(m+1)` path from `i` splits into a first
edge `i → l` and a length-`m` path from `l`; the weight factors and the energy adds the first
edge.  Summing over `l` and the tail gives the fixed-point recurrence. -/
lemma PWterm_succ (s : ℕ) (Q : ℕ → ℕ → ℝ) (i m : ℕ) (hi : i < s) :
    PWterm s Q i (m + 1)
      = ∑ l ∈ range s, Q i l *
          ((xVec s Q l - xVec s Q i) ^ 2 * TWterm s Q l m + PWterm s Q l m) := by
  -- STEP A: reindex LHS via consEquiv, collapse the outer x-sum to x = ⟨i,hi⟩.
  have hLHS : PWterm s Q i (m + 1)
      = ∑ p' : Fin (m + 1) → Fin s,
          Q i (p' 0 : ℕ) * (pathWeight s Q m p' *
            ((xVec s Q (p' 0 : ℕ) - xVec s Q i) ^ 2 + pathEnergy s Q m p')) := by
    simp only [PWterm]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1 + 1) => Fin s))]
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_eq_single (⟨i, hi⟩ : Fin s)]
    · -- x = ⟨i,hi⟩ term
      refine Finset.sum_congr rfl fun p' _ => ?_
      have hce : (Fin.consEquiv (fun _ : Fin (m + 1 + 1) => Fin s)) (⟨i, hi⟩, p')
          = Fin.cons (⟨i, hi⟩ : Fin s) p' := rfl
      rw [hce]
      rw [if_pos (by rfl : ((Fin.cons (⟨i, hi⟩ : Fin s) p' : Fin (m + 2) → Fin s) 0 : ℕ) = i)]
      simp only [pathWeight, pathProd_cons, cons_last, pathEnergy_cons]
      ring
    · -- other x terms vanish
      intro x hx
      apply Finset.sum_eq_zero
      intro p' _
      have hce : (Fin.consEquiv (fun _ : Fin (m + 1 + 1) => Fin s)) (x, p')
          = Fin.cons x p' := rfl
      rw [hce, if_neg]
      intro hcon
      apply hx
      apply Fin.ext
      rw [show ((Fin.cons x p' : Fin (m + 2) → Fin s) 0 : ℕ) = (x : ℕ) from by
            rw [show (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc from rfl]; simp] at hcon
      exact hcon
  rw [hLHS]
  -- STEP B: RHS.  Expand TWterm, PWterm and swap the double sum.
  have hRHS : (∑ l ∈ range s, Q i l *
        ((xVec s Q l - xVec s Q i) ^ 2 * TWterm s Q l m + PWterm s Q l m))
      = ∑ l ∈ range s, ∑ p' : Fin (m + 1) → Fin s,
          (if (p' 0 : ℕ) = l then
            Q i l * (pathWeight s Q m p' *
              ((xVec s Q l - xVec s Q i) ^ 2 + pathEnergy s Q m p')) else 0) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [TWterm, PWterm]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p' _ => ?_
    split_ifs <;> ring
  rw [hRHS, Finset.sum_comm]
  -- for each p', collapse the l-sum to l = p' 0
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [Finset.sum_eq_single_of_mem ((p' 0 : ℕ)) (mem_range.2 (p' 0).isLt)]
  · rw [if_pos rfl]
  · intro l _ hlne
    rw [if_neg (fun h => hlne h.symm)]

/-- Uniform upper bound `xⱼ ≤ C·(1−θ)⁻¹` for `j < s`. -/
lemma xVec_le (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (j : ℕ) (hj : j < s) :
    xVec s Q j ≤ C * (1 - θ)⁻¹ := by
  rw [xVec_eq_tsum s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub j hj]
  have hsummable : Summable (fun k => matVec s (matPow s Q k) eVec j) :=
    summable_matVec_matPow s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub eVec j hj
  have hgeo : Summable (fun k => C * θ ^ k) :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_left C
  calc ∑' k, matVec s (matPow s Q k) eVec j
      ≤ ∑' k, C * θ ^ k :=
        Summable.tsum_le_tsum (fun k => hdecay k j hj) hsummable hgeo
    _ = C * (1 - θ)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hθ0 hθ1]

/-- Per-path energy upper bound: `pathEnergy p ≤ (m+1)·(C·(1−θ)⁻¹)²`. -/
lemma pathEnergy_le (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (m : ℕ) (p : Fin (m + 1) → Fin s) :
    pathEnergy s Q m p ≤ (m + 1) * (C * (1 - θ)⁻¹) ^ 2 := by
  set B : ℝ := C * (1 - θ)⁻¹ with hB
  have hBnn : 0 ≤ B := by rw [hB]; have : 0 ≤ (1 - θ)⁻¹ := by positivity
                          exact mul_nonneg hC0 this
  have hxb : ∀ j : Fin s, 0 ≤ xVec s Q (j : ℕ) ∧ xVec s Q (j : ℕ) ≤ B := fun j =>
    ⟨xVec_nonneg s Q hQ _, xVec_le s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub _ j.isLt⟩
  -- edge bound: (x_a - x_b)² ≤ B²
  have hedge : ∀ a b : Fin s, (xVec s Q (a : ℕ) - xVec s Q (b : ℕ)) ^ 2 ≤ B ^ 2 := by
    intro a b
    have ha := hxb a; have hb := hxb b
    nlinarith [ha.1, ha.2, hb.1, hb.2]
  simp only [pathEnergy]
  have hsum : (∑ r : Fin m, (xVec s Q (p r.succ : ℕ) - xVec s Q (p r.castSucc : ℕ)) ^ 2)
      ≤ ∑ _r : Fin m, B ^ 2 :=
    Finset.sum_le_sum fun r _ => hedge (p r.succ) (p r.castSucc)
  have hterm : (xVec s Q (p (Fin.last m) : ℕ)) ^ 2 ≤ B ^ 2 := by
    have := hxb (p (Fin.last m)); nlinarith [this.1, this.2]
  have : (∑ r : Fin m, (xVec s Q (p r.succ : ℕ) - xVec s Q (p r.castSucc : ℕ)) ^ 2)
      + (xVec s Q (p (Fin.last m) : ℕ)) ^ 2 ≤ (∑ _r : Fin m, B ^ 2) + B ^ 2 :=
    add_le_add hsum hterm
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  calc (∑ r : Fin m, (xVec s Q (p r.succ : ℕ) - xVec s Q (p r.castSucc : ℕ)) ^ 2)
        + (xVec s Q (p (Fin.last m) : ℕ)) ^ 2
      ≤ (m : ℝ) * B ^ 2 + B ^ 2 := this
    _ = (m + 1) * B ^ 2 := by ring

/-- The sum of `pathProd` over paths of length `m` starting at `i` is `(Qᵐ e)ᵢ`. -/
lemma sum_pathProd_eq (s : ℕ) (Q : ℕ → ℕ → ℝ) (i m : ℕ) (hi : i < s) :
    (∑ p : Fin (m + 1) → Fin s, (if (p 0 : ℕ) = i then pathProd s Q m p else 0))
      = matVec s (matPow s Q m) eVec i := by
  rw [matVec_matPow_eq_pathSum s Q eVec m i hi]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [eVec, mul_one]

/-- Upper bound on `PWterm`: `PWterm i m ≤ (m+1)·B²·(C·θᵐ)` with `B = C·(1−θ)⁻¹`. -/
lemma PWterm_le (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (i : ℕ) (hi : i < s) (m : ℕ) :
    PWterm s Q i m ≤ (m + 1) * (C * (1 - θ)⁻¹) ^ 2 * (C * θ ^ m) := by
  set B : ℝ := C * (1 - θ)⁻¹ with hB
  have hBnn : 0 ≤ B := by rw [hB]; have : 0 ≤ (1 - θ)⁻¹ := by positivity
                          exact mul_nonneg hC0 this
  have hEnn : (0 : ℝ) ≤ (m + 1) * B ^ 2 := by positivity
  -- PWterm i m ≤ ∑_p [p0=i] pathProd p · 1 · ((m+1)B²) = (m+1)B² (Qᵐe)_i ≤ (m+1)B² θᵐ
  simp only [PWterm, pathWeight]
  have hbound : ∀ p : Fin (m + 1) → Fin s,
      (if (p 0 : ℕ) = i then pathProd s Q m p * bVec s Q (p (Fin.last m) : ℕ)
        * pathEnergy s Q m p else 0)
      ≤ (if (p 0 : ℕ) = i then pathProd s Q m p else 0) * ((m + 1) * B ^ 2) := by
    intro p
    split_ifs with h
    · -- pathProd·b·energy ≤ pathProd·((m+1)B²)  (since 0≤b≤1, energy ≤ (m+1)B²)
      have hpp : 0 ≤ pathProd s Q m p := pathProd_nonneg s Q hQ m p
      have hb1 : bVec s Q (p (Fin.last m) : ℕ) ≤ 1 := by
        simp only [bVec]
        have := sum_nonneg (fun l (_ : l ∈ range s) => hQ (p (Fin.last m) : ℕ) l)
        linarith
      have hb0 : 0 ≤ bVec s Q (p (Fin.last m) : ℕ) :=
        bVec_nonneg s Q hsub _ (p (Fin.last m)).isLt
      have hE := pathEnergy_le s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub m p
      have hEnn' : 0 ≤ pathEnergy s Q m p := by
        simp only [pathEnergy]; positivity
      -- pathProd·b·energy ≤ pathProd·1·((m+1)B²)
      calc pathProd s Q m p * bVec s Q (p (Fin.last m) : ℕ) * pathEnergy s Q m p
          ≤ pathProd s Q m p * 1 * ((m + 1) * B ^ 2) := by
            apply mul_le_mul
            · apply mul_le_mul_of_nonneg_left hb1 hpp
            · exact hE
            · exact hEnn'
            · positivity
        _ = pathProd s Q m p * ((m + 1) * B ^ 2) := by ring
    · rw [zero_mul]
  calc (∑ p : Fin (m + 1) → Fin s,
          (if (p 0 : ℕ) = i then pathProd s Q m p * bVec s Q (p (Fin.last m) : ℕ)
            * pathEnergy s Q m p else 0))
      ≤ ∑ p : Fin (m + 1) → Fin s,
          (if (p 0 : ℕ) = i then pathProd s Q m p else 0) * ((m + 1) * B ^ 2) :=
        Finset.sum_le_sum fun p _ => hbound p
    _ = (∑ p : Fin (m + 1) → Fin s, (if (p 0 : ℕ) = i then pathProd s Q m p else 0))
          * ((m + 1) * B ^ 2) := by rw [← Finset.sum_mul]
    _ = matVec s (matPow s Q m) eVec i * ((m + 1) * B ^ 2) := by
        rw [sum_pathProd_eq s Q i m hi]
    _ ≤ (C * θ ^ m) * ((m + 1) * B ^ 2) :=
        mul_le_mul_of_nonneg_right (hdecay m i hi) hEnn
    _ = (m + 1) * B ^ 2 * (C * θ ^ m) := by ring

/-- Summability of the `PWterm` slices for a fixed start `i < s`. -/
lemma summable_PWterm (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (i : ℕ) (hi : i < s) :
    Summable (fun m => PWterm s Q i m) := by
  set B : ℝ := C * (1 - θ)⁻¹ with hB
  -- comparison with (m+1)·B²·(C·θᵐ)
  have hmaj : Summable (fun m : ℕ => ((m : ℝ) + 1) * B ^ 2 * (C * θ ^ m)) := by
    have h1 : Summable (fun m : ℕ => (m : ℝ) * θ ^ m) := by
      have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := θ)
        (by rw [Real.norm_eq_abs, abs_of_nonneg hθ0]; exact hθ1)
      simpa using this
    have h2 : Summable (fun m : ℕ => θ ^ m) := summable_geometric_of_lt_one hθ0 hθ1
    have hs : Summable (fun m : ℕ => ((m : ℝ) * θ ^ m + θ ^ m) * (B ^ 2 * C)) :=
      ((h1.add h2).mul_right (B ^ 2 * C))
    have heq : (fun m : ℕ => ((m : ℝ) * θ ^ m + θ ^ m) * (B ^ 2 * C))
        = (fun m : ℕ => ((m : ℝ) + 1) * B ^ 2 * (C * θ ^ m)) := by
      funext m; ring
    rwa [heq] at hs
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hmaj
  · -- 0 ≤ PWterm i m
    simp only [PWterm]
    refine Finset.sum_nonneg fun p _ => ?_
    split_ifs with h
    · refine mul_nonneg (pathWeight_nonneg s Q hQ hsub m p) ?_
      simp only [pathEnergy]; positivity
    · exact le_refl 0
  · exact PWterm_le s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub i hi m

/-- **The weighted-path expansion of `v` (property (a)).**  `vᵢ = ∑'_m PWterm i m`, as a
`HasSum`.  (The genuinely infinitary Aldous–Shepp regrouping.) -/
lemma hasSum_PWterm (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (_hs : 0 < s) (i : ℕ) (hi : i < s) :
    HasSum (fun m => PWterm s Q i m) (vVec s Q i) := by
  -- P j := ∑'_m PWterm j m.  We show vVec and P satisfy the same Q-fixed-point recurrence.
  set P : ℕ → ℝ := fun j => ∑' m, PWterm s Q j m with hP
  -- summability facts
  have hsummP : ∀ l < s, Summable (fun m => PWterm s Q l m) := fun l hl =>
    summable_PWterm s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub l hl
  have hsummTW : ∀ l < s, Summable (fun m => TWterm s Q l m) := by
    intro l hl
    by_contra h
    have := tsum_eq_zero_of_not_summable h
    have h1 := tsum_TWterm_eq_one s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub l hl
    rw [this] at h1; exact one_ne_zero h1.symm
  -- The recurrence for P.
  have hPeq : ∀ j, P j = ∑' m, PWterm s Q j m := fun j => rfl
  have hPrec : ∀ i < s, P i = gVec s Q i + ∑ l ∈ range s, Q i l * P l := by
    intro i hi
    rw [hPeq i]
    -- split off m = 0
    rw [(hsummP i hi).tsum_eq_zero_add]
    rw [PWterm_zero s Q i hi]
    -- the tail: ∑'_m PWterm i (m+1) = ∑_l Q i l ((x_l-x_i)²·1 + P l)
    have htail : (∑' m, PWterm s Q i (m + 1))
        = ∑ l ∈ range s, Q i l * ((xVec s Q l - xVec s Q i) ^ 2 + P l) := by
      rw [tsum_congr (fun m => PWterm_succ s Q i m hi)]
      -- swap finite ∑_l with ∑'_m
      rw [Summable.tsum_finsetSum (fun l hl => by
        have hl' := mem_range.1 hl
        exact (((hsummTW l hl').mul_left _).add (hsummP l hl')).mul_left (Q i l))]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' := mem_range.1 hl
      -- ∑'_m Q i l ((x_l-x_i)² TWterm l m + PWterm l m)
      rw [tsum_mul_left]
      congr 1
      rw [Summable.tsum_add ((hsummTW l hl').mul_left _) (hsummP l hl')]
      rw [tsum_mul_left, tsum_TWterm_eq_one s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub l hl']
      rw [hPeq l, mul_one]
    rw [htail]
    -- assemble: b_i x_i² + ∑_l Q i l ((x_l-x_i)² + P l) = g_i + ∑_l Q i l P l
    simp only [gVec]
    rw [Finset.sum_congr rfl (g := fun l => Q i l * (xVec s Q l - xVec s Q i) ^ 2 + Q i l * P l)
          (fun l _ => by ring), Finset.sum_add_distrib]
    ring
  -- vVec satisfies the same recurrence.
  have hVrec : ∀ i < s, vVec s Q i = gVec s Q i + ∑ l ∈ range s, Q i l * vVec s Q l := fun i hi =>
    neumann_apply_fixed_point s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub (gVec s Q) i hi
  -- boundedness of both vVec and P on the state range.
  -- P is bounded: |P j| = P j ≤ (via majorant) some constant. Use ∑' (m+1)B²(C·θ^m).
  set B : ℝ := C * (1 - θ)⁻¹ with hBdef
  have hPnn : ∀ j < s, 0 ≤ P j := by
    intro j hj
    rw [hPeq j]
    exact tsum_nonneg fun m => by
      simp only [PWterm]
      refine Finset.sum_nonneg fun p _ => ?_
      split_ifs with h
      · refine mul_nonneg (pathWeight_nonneg s Q hQ hsub m p) ?_
        simp only [pathEnergy]; positivity
      · exact le_refl 0
  have hPbd : ∀ j < s, P j ≤ ∑' m : ℕ, ((m : ℝ) + 1) * B ^ 2 * (C * θ ^ m) := by
    intro j hj
    rw [hPeq j]
    refine Summable.tsum_le_tsum (fun m => PWterm_le s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub j hj m)
      (hsummP j hj) ?_
    -- majorant summable
    have h1 : Summable (fun m : ℕ => (m : ℝ) * θ ^ m) := by
      have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := θ)
        (by rw [Real.norm_eq_abs, abs_of_nonneg hθ0]; exact hθ1)
      simpa using this
    have h2 : Summable (fun m : ℕ => θ ^ m) := summable_geometric_of_lt_one hθ0 hθ1
    have hs2 : Summable (fun m : ℕ => ((m : ℝ) * θ ^ m + θ ^ m) * (B ^ 2 * C)) :=
      ((h1.add h2).mul_right (B ^ 2 * C))
    have heq : (fun m : ℕ => ((m : ℝ) * θ ^ m + θ ^ m) * (B ^ 2 * C))
        = (fun m : ℕ => ((m : ℝ) + 1) * B ^ 2 * (C * θ ^ m)) := by funext m; ring
    rwa [heq] at hs2
  -- vVec is bounded: |vVec j| ≤ ∑_l |...|.  We just need a uniform D for the difference.
  set D : ℝ := (∑' m : ℕ, ((m : ℝ) + 1) * B ^ 2 * (C * θ ^ m))
      + (∑ l ∈ range s, |vVec s Q l|) with hDdef
  -- d = vVec - P is a bounded Q-fixed point → 0.
  have hdzero : ∀ j < s, vVec s Q j - P j = 0 := by
    refine eq_zero_of_Q_fixed s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub
      (fun j => vVec s Q j - P j) D ?_ ?_
    · -- |vVec j - P j| ≤ D
      intro j hj
      have hv : |vVec s Q j| ≤ ∑ l ∈ range s, |vVec s Q l| :=
        Finset.single_le_sum (f := fun l => |vVec s Q l|) (fun l _ => abs_nonneg _)
          (mem_range.2 hj)
      have hpp : |P j| ≤ ∑' m : ℕ, ((m : ℝ) + 1) * B ^ 2 * (C * θ ^ m) := by
        rw [abs_of_nonneg (hPnn j hj)]; exact hPbd j hj
      have htri : |vVec s Q j - P j| ≤ |vVec s Q j| + |P j| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
      calc |vVec s Q j - P j| ≤ |vVec s Q j| + |P j| := htri
        _ ≤ (∑ l ∈ range s, |vVec s Q l|) + ∑' m : ℕ, ((m : ℝ) + 1) * B ^ 2 * (C * θ ^ m) :=
            add_le_add hv hpp
        _ = D := by rw [hDdef]; ring
    · -- fixed-point: (vVec j - P j) = ∑_l Q j l (vVec l - P l)
      intro j hj
      rw [hVrec j hj, hPrec j hj]
      rw [show (∑ l ∈ range s, Q j l * (vVec s Q l - P l))
            = ∑ l ∈ range s, (Q j l * vVec s Q l - Q j l * P l) from
          Finset.sum_congr rfl fun l _ => by ring]
      rw [Finset.sum_sub_distrib]
      ring
  -- Conclude.
  have hvP : vVec s Q i = P i := by have := hdzero i hi; linarith
  rw [hvP, hPeq i]
  exact (hsummP i hi).hasSum

/-- **The crossing bound, proved.**  For a nonnegative `Q` with row sums `≤ 1` and spectral
radius `< 1` (the faithful paper hypotheses), the crossing estimate `xᵢ²/s ≤ vᵢ` holds. -/
theorem crossingBound_holds (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (hρ : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1) (hs : 0 < s) :
    CrossingBound s Q := by
  obtain ⟨θ, hθ0, hθ1, C, hC0, hdecay⟩ := rowSum_decay_of_spectralRadius s Q hQ hρ
  intro i hi
  set c : ℝ := (xVec s Q i) ^ 2 / s with hc
  -- vᵢ = ∑' PWterm ≥ ∑' (TWterm · c) = (∑' TWterm) · c = 1 · c = c.
  have hPW : HasSum (fun m => PWterm s Q i m) (vVec s Q i) :=
    hasSum_PWterm s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub hs i hi
  -- total weight has sum 1
  have hTWsum : ∑' m, TWterm s Q i m = 1 :=
    tsum_TWterm_eq_one s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub i hi
  have hTWsummable : Summable (fun m => TWterm s Q i m) := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at hTWsum
    exact one_ne_zero hTWsum.symm
  -- ∑' (TWterm · c) = (∑' TWterm) · c = c
  have hmulsum : ∑' m, (TWterm s Q i m * c) = c := by
    rw [hTWsummable.tsum_mul_right, hTWsum, one_mul]
  -- termwise ≤ : TWterm · c ≤ PWterm
  have htermle : ∀ m, TWterm s Q i m * c ≤ PWterm s Q i m := fun m =>
    PWterm_ge s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub hs i hi m
  calc c = ∑' m, (TWterm s Q i m * c) := hmulsum.symm
    _ ≤ ∑' m, PWterm s Q i m :=
        Summable.tsum_le_tsum htermle (hTWsummable.mul_right c) hPW.summable
    _ = vVec s Q i := hPW.tsum_eq

/-! ## Unconditional endgame

With `CrossingBound` now a theorem, the results of `QSequencePaths.lean` that were stated
modulo `CrossingBound` become unconditional. -/

/-- **The paper's Lemma 5, unconditionally proved.**  For a nonnegative, strictly
substochastic `Q` (`hrow` with `θ < 1`) with `0 < s`, the Neumann matrix `N = Nmat s Q`
satisfies `SSP.ComponentBound`: `(Ne)ᵢ² ≤ (2s/(s+1))·(N²e)ᵢ`.  No assumption is left — the
Aldous–Shepp/crossing input is discharged by `crossingBound_holds`. -/
theorem componentBound_unconditional (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (hρ : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1) (hs : 0 < s) :
    ComponentBound s (Nmat s Q) := by
  obtain ⟨θ, hθ0, hθ1, C, hC0, hdecay⟩ := rowSum_decay_of_spectralRadius s Q hQ hρ
  exact componentBound_holds s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub hs
    (crossingBound_holds s Q hQ hsub hρ hs)

/-- **Fully machine-verified `r ≤ 2s`.**  The paper's SSP coefficient bound, with the
`ComponentBound` input now *proved from scratch* via the weighted-paths argument rather than
assumed.  This closes the gap flagged in the docstring of `SSPBound.lean`. -/
theorem qsequence_ssp_bound_unconditional (s : ℕ) (hs : 0 < s) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (hρ : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (w : ℕ → ℝ) (r : ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (hoc1 : ∑ i ∈ range s, w i * rowSum s (Nmat s Q) i = r)
    (hoc2 : ∑ i ∈ range s, w i * rowSum2 s (Nmat s Q) i = r + r ^ 2 / 2) :
    r ≤ 2 * s :=
  ssp_coefficient_bound s hs (Nmat s Q) w r hw hw1
    (componentBound_unconditional s Q hQ hsub hρ hs) hoc1 hoc2

/-! ## `I − Q` invertible form

The same two results, but taking the paper's other hypotheses `Qe ≤ e` and `I − Q` invertible
in place of `ρ(Q) < 1`.  The spectral-radius bound is derived internally from
`Elementary.spectralRadius_lt_one_elementary` (the Perron–Frobenius-free proof). -/

/-- `toMat s Q` is nonnegative when `Q` is. -/
private lemma toMat_nonneg (s : ℕ) (Q : ℕ → ℕ → ℝ) (hQ : ∀ i j, 0 ≤ Q i j) :
    ∀ i j, 0 ≤ toMat s Q i j := fun i j => hQ i j

/-- Row sums of `toMat s Q` are `≤ 1` when `Q` is substochastic on `range s`. -/
private lemma toMat_rowSum_le_one (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) :
    ∀ i : Fin s, ∑ j, toMat s Q i j ≤ 1 := by
  intro i
  have : ∑ j, toMat s Q i j = ∑ j ∈ range s, Q (i : ℕ) j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => Q (i : ℕ) j) s]
    rfl
  rw [this]
  exact hsub (i : ℕ) i.isLt

/-- **The paper's Lemma 5, from `I − Q` invertible.**  Substochastic nonnegative `Q` with
`I − Q` invertible satisfies `SSP.ComponentBound`.  The spectral bound `ρ(Q) < 1` is derived
via `Elementary.spectralRadius_lt_one_elementary` (the Perron–Frobenius-free proof). -/
theorem componentBound_unconditional_of_invertible (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (hinv : IsUnit (1 - toMat s Q)) (hs : 0 < s) :
    ComponentBound s (Nmat s Q) :=
  componentBound_unconditional s Q hQ hsub
    (Elementary.spectralRadius_lt_one_elementary (toMat s Q) (toMat_nonneg s Q hQ)
      (toMat_rowSum_le_one s Q hsub) hinv) hs

/-- **Fully verified `r ≤ 2s`, from `I − Q` invertible.**  As
`qsequence_ssp_bound_unconditional`, but with the paper's `Qe ≤ e` and `I − Q` invertible
hypotheses in place of `ρ(Q) < 1`. -/
theorem qsequence_ssp_bound_unconditional_of_invertible (s : ℕ) (hs : 0 < s) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (hinv : IsUnit (1 - toMat s Q))
    (w : ℕ → ℝ) (r : ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (hoc1 : ∑ i ∈ range s, w i * rowSum s (Nmat s Q) i = r)
    (hoc2 : ∑ i ∈ range s, w i * rowSum2 s (Nmat s Q) i = r + r ^ 2 / 2) :
    r ≤ 2 * s :=
  ssp_coefficient_bound s hs (Nmat s Q) w r hw hw1
    (componentBound_unconditional_of_invertible s Q hQ hsub hinv hs) hoc1 hoc2

/-! ## Stating the bound with the matrix inverse `(I − Q)⁻¹`

The Neumann-series matrix `Nmat s Q` equals `(I − Q)⁻¹` entrywise on the `range s` block
(`SSP.Nmat_eq_invMat`), where `invMat s Q` is the `ℕ → ℕ → ℝ` view of `(1 - toMat s Q)⁻¹`.
Since `rowSum`/`rowSum2` only read indices `< s`, the bound can be restated verbatim with
`invMat` in place of `Nmat`. -/

/-- `rowSum` agrees for `Nmat` and `invMat` at indices `< s` (both only read `range s`). -/
private lemma rowSum_Nmat_eq_invMat (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hρ : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1) (i : ℕ) (hi : i < s) :
    rowSum s (Nmat s Q) i = rowSum s (invMat s Q) i := by
  refine Finset.sum_congr rfl fun j hj => ?_
  exact Nmat_eq_invMat s Q hρ i j hi (mem_range.1 hj)

/-- `rowSum2` agrees for `Nmat` and `invMat` at indices `< s` (both only read `range s`). -/
private lemma rowSum2_Nmat_eq_invMat (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hρ : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1) (i : ℕ) (hi : i < s) :
    rowSum2 s (Nmat s Q) i = rowSum2 s (invMat s Q) i := by
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => ?_
  rw [Nmat_eq_invMat s Q hρ i j hi (mem_range.1 hj),
    Nmat_eq_invMat s Q hρ j l (mem_range.1 hj) (mem_range.1 hl)]

/-- **The paper's Lemma 5, from `I − Q` invertible, stated with `(I − Q)⁻¹`.**  As
`componentBound_unconditional_of_invertible`, but the `SSP.ComponentBound` is stated for
`invMat s Q = (I − Q)⁻¹` (entrywise) rather than the Neumann series `Nmat s Q`.  Since
`rowSum`/`rowSum2` only read the `range s` block — where the two matrices agree
(`Nmat_eq_invMat`) — this is the same statement transported to the inverse form. -/
theorem componentBound_unconditional_of_invertible' (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (hinv : IsUnit (1 - toMat s Q)) (hs : 0 < s) :
    ComponentBound s (invMat s Q) := by
  -- `ρ(Q) < 1` from `I − Q` invertible (PF-free), giving `Nmat = invMat` on the `range s` block.
  have hρ : spectralRadius ℂ ((toMat s Q).map (algebraMap ℝ ℂ)) < 1 :=
    Elementary.spectralRadius_lt_one_elementary (toMat s Q) (toMat_nonneg s Q hQ)
      (toMat_rowSum_le_one s Q hsub) hinv
  intro i hi
  -- Transport the `Nmat` component bound to `invMat` via block agreement of `rowSum`/`rowSum2`.
  rw [← rowSum_Nmat_eq_invMat s Q hρ i hi, ← rowSum2_Nmat_eq_invMat s Q hρ i hi]
  exact componentBound_unconditional_of_invertible s Q hQ hsub hinv hs i hi

/-- **Fully verified `r ≤ 2s`, from `I − Q` invertible, stated with `(I − Q)⁻¹`.**  Identical to
`qsequence_ssp_bound_unconditional_of_invertible`, but the observed coefficients `r` are read
off `invMat s Q = (I − Q)⁻¹` (entrywise) rather than the Neumann series `Nmat s Q`.  The two
matrices agree on the `range s` block (`Nmat_eq_invMat`), so this is the same statement in the
form used by the paper. -/
theorem qsequence_ssp_bound_unconditional_of_invertible' (s : ℕ) (hs : 0 < s) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (hinv : IsUnit (1 - toMat s Q))
    (w : ℕ → ℝ) (r : ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (hoc1 : ∑ i ∈ range s, w i * rowSum s (invMat s Q) i = r)
    (hoc2 : ∑ i ∈ range s, w i * rowSum2 s (invMat s Q) i = r + r ^ 2 / 2) :
    r ≤ 2 * s :=
  ssp_coefficient_bound s hs (invMat s Q) w r hw hw1
    (componentBound_unconditional_of_invertible' s Q hQ hsub hinv hs) hoc1 hoc2

/-- The `ℕ → ℕ → ℝ` view of `I − N⁻¹` (indices `< s`; `0` off-block).  This is the `Q` whose
inverse is `N`: `toMat s (subFromInv s N) = 1 - N⁻¹`, so `1 - toMat s (subFromInv s N) = N⁻¹`. -/
noncomputable def subFromInv (s : ℕ) (N : Matrix (Fin s) (Fin s) ℝ) (i j : ℕ) : ℝ :=
  if h : i < s ∧ j < s then (1 - N⁻¹) ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- `toMat s (subFromInv s N) = 1 - N⁻¹`. -/
lemma toMat_subFromInv (s : ℕ) (N : Matrix (Fin s) (Fin s) ℝ) :
    toMat s (subFromInv s N) = 1 - N⁻¹ := by
  ext i j
  simp only [toMat, Matrix.of_apply, subFromInv, dif_pos (⟨i.isLt, j.isLt⟩ : (i:ℕ) < s ∧ (j:ℕ) < s)]

/-- The `ℕ → ℕ → ℝ` view of a `Fin s` matrix (indices `< s`; `0` off-block).  Matches the shape
read by `rowSum`/`rowSum2`, so the observed coefficients can be stated on `N` directly. -/
noncomputable def ofMat (s : ℕ) (N : Matrix (Fin s) (Fin s) ℝ) (i j : ℕ) : ℝ :=
  if h : i < s ∧ j < s then N ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- **Fully verified `r ≤ 2s`, with the inverse `N` as a `Fin s` matrix and `Q = I − N⁻¹`.**
Instead of supplying the substochastic `Q`, the caller supplies its inverse `N : Matrix (Fin s)
(Fin s) ℝ` (assumed a unit), proves `Q = I − N⁻¹` (`subFromInv s N`) is nonnegative (`hQ`), and
that the row sums of `N⁻¹` are nonnegative (`hNrow`).  The latter is equivalent to `Q` being
substochastic: `∑ⱼ (I − N⁻¹)ᵢⱼ = 1 − ∑ⱼ N⁻¹ᵢⱼ ≤ 1 ⟺ ∑ⱼ N⁻¹ᵢⱼ ≥ 0`.
The `ComponentBound` is still *derived* (not assumed): internally
`Q := subFromInv s N` gives `1 - toMat s Q = N⁻¹`, hence `(I − Q)⁻¹ = N⁻¹⁻¹ = N`, so the observed
coefficients `r` — read off `N` (`ofMat s N`) via `rowSum`/`rowSum2` — are those of `(I − Q)⁻¹`
on the `range s` block. -/
theorem qsequence_ssp_bound_unconditional_of_invMat
    (s : ℕ) (hs : 0 < s) (N : Matrix (Fin s) (Fin s) ℝ) (hNunit : IsUnit N)
    (hQ : ∀ i j, 0 ≤ subFromInv s N i j)
    (hNrow : ∀ i : Fin s, 0 ≤ ∑ j, N⁻¹ i j)
    (w : ℕ → ℝ) (r : ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (hoc1 : ∑ i ∈ range s, w i * rowSum s (ofMat s N) i = r)
    (hoc2 : ∑ i ∈ range s, w i * rowSum2 s (ofMat s N) i = r + r ^ 2 / 2) :
    r ≤ 2 * s := by
  -- Row sums of `Q = I − N⁻¹` are `≤ 1` iff row sums of `N⁻¹` are `≥ 0`
  -- (`∑ⱼ (1 − N⁻¹)ᵢⱼ = 1 − ∑ⱼ N⁻¹ᵢⱼ` since the identity contributes exactly `1` per row).
  have hsub : ∀ i < s, ∑ j ∈ range s, subFromInv s N i j ≤ 1 := by
    intro i hi
    have hrow : ∑ j ∈ range s, subFromInv s N i j = 1 - ∑ j, N⁻¹ ⟨i, hi⟩ j := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => subFromInv s N i j) s]
      have : ∀ j : Fin s, subFromInv s N i j = (1 : Matrix (Fin s) (Fin s) ℝ) ⟨i, hi⟩ j
          - N⁻¹ ⟨i, hi⟩ j := by
        intro j
        rw [subFromInv, dif_pos (⟨hi, j.isLt⟩ : i < s ∧ (j : ℕ) < s)]
        simp [Matrix.sub_apply]
      simp_rw [this, Finset.sum_sub_distrib]
      rw [Finset.sum_congr rfl (fun j _ => rfl)]
      congr 1
      simp [Matrix.one_apply]
    rw [hrow]
    linarith [hNrow ⟨i, hi⟩]
  -- `1 - toMat s Q = N⁻¹`, which is a unit since `N` is; so `(I − Q)⁻¹ = N` on the block.
  have hNinv : IsUnit N⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 hNunit
  have hsub_toMat : (1 : Matrix (Fin s) (Fin s) ℝ) - toMat s (subFromInv s N) = N⁻¹ := by
    rw [toMat_subFromInv, sub_sub_cancel]
  have hinv : IsUnit (1 - toMat s (subFromInv s N)) := hsub_toMat ▸ hNinv
  -- `ofMat s N` agrees with `invMat s (subFromInv s N) = (I − Q)⁻¹` on the `range s` block.
  have hNdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).1 hNunit
  have hagree : ∀ i < s, ∀ j < s, ofMat s N i j = invMat s (subFromInv s N) i j := by
    intro i hi j hj
    rw [ofMat, dif_pos (⟨hi, hj⟩ : i < s ∧ j < s),
      invMat, dif_pos (⟨hi, hj⟩ : i < s ∧ j < s), hsub_toMat,
      Matrix.nonsing_inv_nonsing_inv N hNdet]
  -- `rowSum`/`rowSum2` of `ofMat s N` agree with `invMat s Q` on the `range s` block.
  have hrs : ∀ i, i < s → rowSum s (ofMat s N) i = rowSum s (invMat s (subFromInv s N)) i :=
    fun i hi => Finset.sum_congr rfl fun j hj => hagree i hi j (mem_range.1 hj)
  have hrs2 : ∀ i, i < s → rowSum2 s (ofMat s N) i = rowSum2 s (invMat s (subFromInv s N)) i :=
    fun i hi => Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => by
      rw [hagree i hi j (mem_range.1 hj), hagree j (mem_range.1 hj) l (mem_range.1 hl)]
  -- Transport the moment conditions to `invMat s Q`, then invoke the `'` variant.
  refine qsequence_ssp_bound_unconditional_of_invertible' s hs (subFromInv s N) hQ hsub hinv
    w r hw hw1 ?_ ?_
  · rw [← hoc1]; exact Finset.sum_congr rfl fun i hi => by rw [hrs i (mem_range.1 hi)]
  · rw [← hoc2]; exact Finset.sum_congr rfl fun i hi => by rw [hrs2 i (mem_range.1 hi)]

end SSP
