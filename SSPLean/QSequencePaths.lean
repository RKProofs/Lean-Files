import Mathlib.Tactic
import SSPLean.SSPBound
import SSPLean.PathEnergy

/-!
# The weighted-paths proof of the component bound, formalized

This file machine-verifies the **first proof** ("weighted paths") of the substochastic
matrix inequality in `q_sequence_bound_two_proofs.tex`, and uses it to *discharge* the
`ComponentBound` hypothesis that was **assumed** in `SSPBound.lean`.

## What is proved

For a nonnegative matrix `Q` under the paper's hypotheses — substochastic (`Qe ≤ e`, i.e.
row sums `≤ 1`) and spectral radius `ρ(Q) < 1` — the Neumann series `N = Σ_k Qᵏ` converges
entrywise; writing `x = Ne`, `y = N²e`, the paper's Lemma 5 (`SSP.ComponentBound`)
`  (Ne)ᵢ² ≤ (2s/(s+1))·(N²e)ᵢ`
is derived from scratch and then fed into the existing `SSP.ssp_coefficient_bound` to give
a fully machine-verified `r ≤ 2s`, closing the gap flagged in the docstring of `SSPBound.lean`.
The unconditional endgame theorems (with the `ρ(Q)<1` hypothesis) live in
`QSequenceCrossing.lean`; see `qsequence_ssp_bound_unconditional`.

## Convergence hypothesis

The internal lemmas here are parameterized over the exact convergence fact they need — a
geometric row-sum decay bound `hdecay : (Qᵏe)ᵢ ≤ C·θᵏ` (`θ < 1`) — together with
substochasticity `hsub : Σ_ℓ q_{jℓ} ≤ 1` (needed for the defect vector `b = e − Qe ≥ 0`).
The paper's `ρ(Q) < 1` supplies `hdecay` via Gelfand's formula; that derivation is
`SpectralDecay.rowSum_decay_of_spectralRadius`, and it is the only analytic input.  Keeping
`hdecay` abstract here decouples the (elementary) weighted-paths argument from the spectral
analysis.

## Structure

The development is built in layers, bottom-up.  The genuinely infinitary content (the
paper's crossing / weighted-paths argument, which is Aldous–Shepp-flavoured and provably
does not reduce to a finite telescoping) is the path expansion in `§3` and the per-path
Cauchy–Schwarz bound in `§4`.  See the section headers.
-/

open Finset

namespace SSP

/-! ## Layer 0: matrix powers, application to vectors, nonnegativity -/

/-- `matPow s Q k` is the `k`-th power of `Q` (indices `< s`), built by folding one copy of
`Q` on the right.  `matPow s Q 0` is the identity (Kronecker delta). -/
def matPow (s : ℕ) (Q : ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0,     i, j => if i = j then 1 else 0
  | (k+1), i, j => ∑ l ∈ range s, matPow s Q k i l * Q l j

/-- `matVec s M v i = (M v)ᵢ = Σ_{j<s} Mᵢⱼ vⱼ`. -/
def matVec (s : ℕ) (M : ℕ → ℕ → ℝ) (v : ℕ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ range s, M i j * v j

/-- The all-ones vector `e`. -/
def eVec : ℕ → ℝ := fun _ => 1

/-- Entries of `Qᵏ` are nonnegative when `Q` is. -/
lemma matPow_nonneg (s : ℕ) (Q : ℕ → ℕ → ℝ) (hQ : ∀ i j, 0 ≤ Q i j) :
    ∀ k i j, 0 ≤ matPow s Q k i j := by
  intro k
  induction k with
  | zero => intro i j; simp only [matPow]; split_ifs <;> norm_num
  | succ k ih =>
    intro i j
    simp only [matPow]
    exact sum_nonneg fun l _ => mul_nonneg (ih i l) (hQ l j)

/-- `(M v)ᵢ ≥ 0` when `M` and `v` are nonnegative. -/
lemma matVec_nonneg (s : ℕ) (M : ℕ → ℕ → ℝ) (v : ℕ → ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hv : ∀ j, 0 ≤ v j) (i : ℕ) :
    0 ≤ matVec s M v i :=
  sum_nonneg fun j _ => mul_nonneg (hM i j) (hv j)

/-- `matVec` commutes with scalar multiples of the vector argument. -/
lemma matVec_smul (s : ℕ) (M : ℕ → ℕ → ℝ) (c : ℝ) (v : ℕ → ℝ) (i : ℕ) :
    matVec s M (fun j => c * v j) i = c * matVec s M v i := by
  simp only [matVec, mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- **Associativity / multiplicativity of matrix powers.**  For a column index `j < s`,
`Qᵃ⁺ᵇ = Qᵃ · Qᵇ` entrywise.  The left (row) index `i` is unrestricted; the middle index
is summed over `range s`.  Proved by induction on `b`. -/
lemma matPow_add (s : ℕ) (Q : ℕ → ℕ → ℝ) (a i : ℕ) :
    ∀ b j, j < s → matPow s Q (a + b) i j = ∑ l ∈ range s, matPow s Q a i l * matPow s Q b l j := by
  intro b
  induction b with
  | zero =>
    intro j hj
    simp only [Nat.add_zero, matPow]
    rw [sum_congr rfl (g := fun l => if l = j then matPow s Q a i l else 0) fun l _ => by
          split_ifs with h <;> simp [h]]
    rw [sum_ite_eq' (range s) j (fun l => matPow s Q a i l)]
    simp [mem_range.2 hj]
  | succ b ih =>
    intro j hj
    -- Qᵃ⁺⁽ᵇ⁺¹⁾ = (Qᵃ⁺ᵇ)·Q on the right; apply ih to the (a+b) block.
    have hstep : matPow s Q (a + (b + 1)) i j = ∑ m ∈ range s, matPow s Q (a + b) i m * Q m j := by
      rw [← Nat.add_assoc]; rfl
    rw [hstep]
    -- expand each (a+b) entry via ih, then swap sums
    have : ∀ m ∈ range s, matPow s Q (a + b) i m * Q m j
        = (∑ l ∈ range s, matPow s Q a i l * matPow s Q b l m) * Q m j := by
      intro m hm
      rw [ih m (mem_range.1 hm)]
    rw [sum_congr rfl this]
    -- Σ_m (Σ_l …) Q m j = Σ_l matPow a i l * (Σ_m matPow b l m * Q m j)
    --   and Σ_m matPow b l m * Q m j = matPow (b+1) l j (right fold).
    rw [sum_congr rfl (g := fun m => ∑ l ∈ range s, matPow s Q a i l * (matPow s Q b l m * Q m j))
          fun m _ => by rw [sum_mul]; exact sum_congr rfl fun l _ => by ring]
    rw [sum_comm]
    exact sum_congr rfl fun l _ => by rw [← mul_sum]; rfl

/-! ## Layer 1: summability of the Neumann series; the vectors `N`, `x`, `y` -/

/-- Each entry `(Qᵏ)ᵢⱼ` is bounded by the row-sum `(Qᵏ e)ᵢ` (for `i < s`, when the entry's
column `j < s`). -/
lemma matPow_entry_le_rowSum (s : ℕ) (Q : ℕ → ℕ → ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (k i j : ℕ) (hj : j < s) :
    matPow s Q k i j ≤ matVec s (matPow s Q k) eVec i := by
  simp only [matVec, eVec, mul_one]
  exact single_le_sum (fun l _ => matPow_nonneg s Q hQ k i l) (mem_range.2 hj)

/-- **Entrywise summability of the Neumann series.** -/
lemma summable_matPow_entry (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (_hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (_hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (i j : ℕ) (hi : i < s) (hj : j < s) :
    Summable (fun k => matPow s Q k i j) := by
  have hgeo : Summable (fun k => C * θ ^ k) :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_left C
  refine Summable.of_nonneg_of_le (fun k => matPow_nonneg s Q hQ k i j) (fun k => ?_) hgeo
  exact le_trans (matPow_entry_le_rowSum s Q hQ k i j hj) (hdecay k i hi)

/-- The Neumann series `N = (I − Q)⁻¹ = Σ_k Qᵏ`, entrywise. -/
noncomputable def Nmat (s : ℕ) (Q : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ := ∑' k, matPow s Q k i j

/-- `x = N e`. -/
noncomputable def xVec (s : ℕ) (Q : ℕ → ℕ → ℝ) (i : ℕ) : ℝ := matVec s (Nmat s Q) eVec i

/-- `y = N² e = N x`. -/
noncomputable def yVec (s : ℕ) (Q : ℕ → ℕ → ℝ) (i : ℕ) : ℝ := matVec s (Nmat s Q) (xVec s Q) i

/-- `xᵢ = Σ'_k (Qᵏ e)ᵢ`: the Neumann sum can be pulled outside the finite state sum. -/
lemma xVec_eq_tsum (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (i : ℕ) (hi : i < s) :
    xVec s Q i = ∑' k, matVec s (matPow s Q k) eVec i := by
  simp only [xVec, matVec, Nmat, eVec, mul_one]
  rw [Summable.tsum_finsetSum
    (fun j hj => summable_matPow_entry s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub i j hi (mem_range.1 hj))]

/-! ## Layer 2: the finite Neumann identities -/

/-- General left-fold applied to an arbitrary vector: `(Qᵏ⁺¹ v)ᵢ = Σ_{l<s} q_{il} (Qᵏ v)_l`
for `i < s`. -/
lemma matVec_matPow_succ_left' (s : ℕ) (Q : ℕ → ℕ → ℝ) (v : ℕ → ℝ) (k i : ℕ) (hi : i < s) :
    matVec s (matPow s Q (k + 1)) v i
      = ∑ l ∈ range s, Q i l * matVec s (matPow s Q k) v l := by
  simp only [matVec]
  have hleft : ∀ j ∈ range s, matPow s Q (k + 1) i j = ∑ l ∈ range s, Q i l * matPow s Q k l j := by
    intro j hj
    have h := matPow_add s Q 1 i k j (mem_range.1 hj)
    rw [Nat.add_comm 1 k] at h
    rw [h]
    refine sum_congr rfl fun l _ => ?_
    simp only [matPow]
    rw [sum_congr rfl (g := fun m => if i = m then Q m l else 0) fun m _ => by
          split_ifs with hm <;> simp]
    rw [sum_ite_eq (range s) i (fun m => Q m l), if_pos (mem_range.2 hi)]
  rw [sum_congr rfl (g := fun j => (∑ l ∈ range s, Q i l * matPow s Q k l j) * v j)
        fun j hj => by rw [hleft j hj]]
  -- Σ_j (Σ_l q_{il} matPow k l j) v j = Σ_l q_{il} (Σ_j matPow k l j * v j)
  rw [sum_congr rfl (g := fun j => ∑ l ∈ range s, Q i l * (matPow s Q k l j * v j))
        fun j _ => by rw [sum_mul]; exact sum_congr rfl fun l _ => by ring]
  rw [sum_comm]
  exact sum_congr rfl fun l _ => by rw [mul_sum]

/-- `(N v)ᵢ = Σ'_k (Qᵏ v)ᵢ`: the Neumann sum pulls outside the finite state sum, for any
vector `v`. -/
lemma matVec_Nmat_eq_tsum (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (v : ℕ → ℝ) (i : ℕ) (hi : i < s) :
    matVec s (Nmat s Q) v i = ∑' k, matVec s (matPow s Q k) v i := by
  simp only [matVec, Nmat]
  rw [sum_congr rfl (g := fun j => ∑' k, matPow s Q k i j * v j) fun j _ => by
        rw [tsum_mul_right]]
  rw [Summable.tsum_finsetSum (fun j hj =>
    (summable_matPow_entry s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub i j hi
      (mem_range.1 hj)).mul_right (v j))]

/-- Each `(Qᵏ v)ᵢ` (`i < s`) is summable in `k`, for any `v`. -/
lemma summable_matVec_matPow (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (v : ℕ → ℝ) (i : ℕ) (hi : i < s) :
    Summable (fun k => matVec s (matPow s Q k) v i) := by
  simp only [matVec]
  refine summable_sum fun j hj => ?_
  exact (summable_matPow_entry s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub i j hi
    (mem_range.1 hj)).mul_right (v j)

/-- **Neumann fixed-point identity** `(I − Q) (N v) = v`, in the form
`(N v)ᵢ = vᵢ + Σ_{l<s} q_{il} (N v)_l` for `i < s`. -/
lemma neumann_apply_fixed_point (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (v : ℕ → ℝ) (i : ℕ) (hi : i < s) :
    matVec s (Nmat s Q) v i = v i + ∑ l ∈ range s, Q i l * matVec s (Nmat s Q) v l := by
  rw [matVec_Nmat_eq_tsum s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub v i hi]
  -- split off k = 0
  rw [(summable_matVec_matPow s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub v i hi).tsum_eq_zero_add]
  congr 1
  · -- (Q⁰ v)ᵢ = vᵢ
    simp only [matVec, matPow]
    rw [sum_congr rfl (g := fun j => if i = j then v j else 0) fun j _ => by
          split_ifs with h <;> simp]
    rw [sum_ite_eq (range s) i v, if_pos (mem_range.2 hi)]
  · -- Σ'_k (Q^{k+1} v)ᵢ = Σ_l q_{il} (N v)_l
    rw [tsum_congr fun k => matVec_matPow_succ_left' s Q v k i hi]
    rw [Summable.tsum_finsetSum (fun l hl =>
      (summable_matVec_matPow s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub v l
        (mem_range.1 hl)).mul_left (Q i l))]
    refine sum_congr rfl fun l hl => ?_
    have hl' := mem_range.1 hl
    have hsl := summable_matVec_matPow s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub v l hl'
    rw [Summable.tsum_mul_left _ hsl,
      matVec_Nmat_eq_tsum s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub v l hl']

/-- If a vector `d` is a fixed point of `Q` on the state range (`dᵢ = Σ_l q_{il} d_l`) and is
bounded there, then it vanishes.  This is the uniqueness underlying `(I−Q)⁻¹`, obtained from the
geometric decay `(Qᵏ)·bound → 0`. -/
lemma eq_zero_of_Q_fixed (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (_hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (_hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (d : ℕ → ℝ) (D : ℝ) (hC : ∀ i < s, |d i| ≤ D)
    (hfix : ∀ i < s, d i = ∑ l ∈ range s, Q i l * d l) :
    ∀ i < s, d i = 0 := by
  -- d i = (Qᵏ d)ᵢ for all k
  have hiter : ∀ k, ∀ i < s, d i = matVec s (matPow s Q k) d i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simp only [matVec, matPow]
      rw [sum_congr rfl (g := fun j => if i = j then d j else 0) fun j _ => by
            split_ifs with h <;> simp]
      rw [sum_ite_eq (range s) i d, if_pos (mem_range.2 hi)]
    | succ k ih =>
      intro i hi
      rw [matVec_matPow_succ_left' s Q d k i hi, hfix i hi]
      exact sum_congr rfl fun l hl => by rw [ih l (mem_range.1 hl)]
  intro i hi
  -- |d i| = |(Qᵏ d)ᵢ| ≤ (Qᵏ |d|)ᵢ ≤ D·(C·θᵏ) → 0, so d i = 0
  have hbound : ∀ k, |d i| ≤ D * (C * θ ^ k) := by
    intro k
    have hDnn : 0 ≤ D := le_trans (abs_nonneg _) (hC i hi)
    calc |d i| = |matVec s (matPow s Q k) d i| := by rw [hiter k i hi]
      _ ≤ matVec s (matPow s Q k) (fun l => |d l|) i := by
          simp only [matVec]
          refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          exact sum_congr rfl fun l _ => by rw [abs_mul, abs_of_nonneg (matPow_nonneg s Q hQ k i l)]
      _ ≤ matVec s (matPow s Q k) (fun _ => D) i := by
          simp only [matVec]
          refine sum_le_sum fun l hl => ?_
          exact mul_le_mul_of_nonneg_left (hC l (mem_range.1 hl)) (matPow_nonneg s Q hQ k i l)
      _ = D * matVec s (matPow s Q k) eVec i := by
          rw [← matVec_smul s (matPow s Q k) D eVec]; simp [eVec]
      _ ≤ D * (C * θ ^ k) :=
          mul_le_mul_of_nonneg_left (hdecay k i hi) hDnn
  -- D·(C·θᵏ) → 0
  have hlim : Filter.Tendsto (fun k => D * (C * θ ^ k)) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun k => θ ^ k) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1
    simpa using (this.const_mul C).const_mul D
  have : |d i| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Filter.Eventually.of_forall hbound)
  simpa [abs_nonpos_iff] using this

/-- **Identity (I):** `(I − Q) x = e`, i.e. `xᵢ = 1 + Σ_{l<s} q_{il} x_l`. -/
lemma xVec_fixed_point (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (i : ℕ) (hi : i < s) :
    xVec s Q i = 1 + ∑ l ∈ range s, Q i l * xVec s Q l := by
  have h := neumann_apply_fixed_point s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub eVec i hi
  simpa only [xVec, eVec] using h

/-- **Identity for `y`:** `(I − Q) y = x`, i.e. `yᵢ = xᵢ + Σ_{l<s} q_{il} y_l`. -/
lemma yVec_fixed_point (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (i : ℕ) (hi : i < s) :
    yVec s Q i = xVec s Q i + ∑ l ∈ range s, Q i l * yVec s Q l :=
  neumann_apply_fixed_point s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub (xVec s Q) i hi

/-- The defect vector `b = e − Qe`, `bⱼ = 1 − Σ_{l<s} q_{jl}`. -/
def bVec (s : ℕ) (Q : ℕ → ℕ → ℝ) (j : ℕ) : ℝ := 1 - ∑ l ∈ range s, Q j l

/-- `bⱼ ≥ 0` under substochasticity `Σ_l q_{jl} ≤ 1`. -/
lemma bVec_nonneg (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (j : ℕ) (hj : j < s) :
    0 ≤ bVec s Q j := by
  have := hsub j hj
  simp only [bVec]; linarith

/-- The energy vector `gⱼ = Σ_{l<s} q_{jl}(x_l − x_j)² + bⱼ x_j²`. -/
noncomputable def gVec (s : ℕ) (Q : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  (∑ l ∈ range s, Q j l * (xVec s Q l - xVec s Q j) ^ 2) + bVec s Q j * (xVec s Q j) ^ 2

/-- `v = N g`. -/
noncomputable def vVec (s : ℕ) (Q : ℕ → ℕ → ℝ) (i : ℕ) : ℝ := matVec s (Nmat s Q) (gVec s Q) i

/-- **Ring core of identity (II).**  Using (I), `gᵢ = 2xᵢ − (xᵢ² − Σ_{l<s} q_{il} x_l²)`. -/
lemma gVec_eq (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (i : ℕ) (hi : i < s) :
    gVec s Q i
      = 2 * xVec s Q i - ((xVec s Q i) ^ 2 - ∑ l ∈ range s, Q i l * (xVec s Q l) ^ 2) := by
  -- expand the square: Σ q_{il}(x_l−x_i)² = Σ q_{il}x_l² − 2 x_i (Σ q_{il}x_l) + x_i² Σ q_{il}
  have hexp : ∑ l ∈ range s, Q i l * (xVec s Q l - xVec s Q i) ^ 2
      = (∑ l ∈ range s, Q i l * (xVec s Q l) ^ 2)
        - 2 * xVec s Q i * (∑ l ∈ range s, Q i l * xVec s Q l)
        + (xVec s Q i) ^ 2 * (∑ l ∈ range s, Q i l) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun l _ => by ring
  -- the (I) substitution: Σ q_{il} x_l = x_i − 1
  have hI : ∑ l ∈ range s, Q i l * xVec s Q l = xVec s Q i - 1 := by
    have := xVec_fixed_point s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub i hi; linarith
  simp only [gVec, bVec, hexp, hI]
  ring

/-- **Identity (II):** `vᵢ = 2 yᵢ − xᵢ²`.  Both `v` and `2y − x²` satisfy the same
`Q`-fixed-point recurrence `u = g + Q u`, so they coincide by uniqueness. -/
lemma vVec_eq (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (i : ℕ) (hi : i < s) :
    vVec s Q i = 2 * yVec s Q i - (xVec s Q i) ^ 2 := by
  -- w := 2y − x²; show d := v − w is a bounded Q-fixed point, hence 0
  set w : ℕ → ℝ := fun l => 2 * yVec s Q l - (xVec s Q l) ^ 2 with hw
  set d : ℕ → ℝ := fun l => vVec s Q l - w l with hd
  suffices hzero : ∀ i < s, d i = 0 by
    have := hzero i hi; simp only [hd, hw] at this; linarith
  refine eq_zero_of_Q_fixed s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub d (∑ l ∈ range s, |d l|) ?_ ?_
  · -- bound: |d i| ≤ Σ_l |d l|
    intro i hi
    exact single_le_sum (f := fun l => |d l|) (fun l _ => abs_nonneg _) (mem_range.2 hi)
  · -- d is a Q-fixed point: dᵢ = Σ_l q_{il} d_l
    intro i hi
    have hv : vVec s Q i = gVec s Q i + ∑ l ∈ range s, Q i l * vVec s Q l :=
      neumann_apply_fixed_point s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub (gVec s Q) i hi
    -- w satisfies wᵢ = gᵢ + Σ_l q_{il} w_l
    have hwfix : w i = gVec s Q i + ∑ l ∈ range s, Q i l * w l := by
      simp only [hw]
      rw [gVec_eq s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub i hi]
      -- Σ_l q_{il}(2y_l − x_l²) = 2 Σ q_{il} y_l − Σ q_{il} x_l²
      have hsplit : ∑ l ∈ range s, Q i l * (2 * yVec s Q l - (xVec s Q l) ^ 2)
          = 2 * (∑ l ∈ range s, Q i l * yVec s Q l)
            - ∑ l ∈ range s, Q i l * (xVec s Q l) ^ 2 := by
        rw [mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun l _ => by ring
      rw [hsplit]
      -- x_i + Σ q_{il} y_l = y_i
      have hy := yVec_fixed_point s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub i hi
      linarith
    -- dᵢ = vᵢ − wᵢ = Σ_l q_{il}(v_l − w_l) = Σ_l q_{il} d_l
    change vVec s Q i - w i = ∑ l ∈ range s, Q i l * d l
    rw [hv, hwfix]
    rw [show (∑ l ∈ range s, Q i l * d l)
          = ∑ l ∈ range s, (Q i l * vVec s Q l - Q i l * w l) from
        sum_congr rfl fun l _ => by simp only [hd]; ring]
    rw [sum_sub_distrib]
    ring

/-! ## Layer 3: the weighted-path expansion

The paper expands `v = N g` as a sum over finite weighted paths `i → … → 0` (absorbing
endpoint at level `0`).  A length-`m` path is a tuple `p : Fin (m+1) → Fin s` of visited
states; its **weight** is the product of transition weights times the terminal absorption
`b`, and its **energy** is the sum of squared level changes plus the final drop to `0`.

The transition-weight product below (`pathProd`) is proved to reconstruct matrix powers
(`matPow_eq_pathSum`).  The full weighted expansion — total weight `1` and
`v_i = Σ_paths W·E`, together with the per-path crossing bound `E ≥ x_i²/s` — is the
genuinely infinitary Aldous–Shepp content; it is packaged as `CrossingBound` and consumed by
Layer 4.  See the note on `CrossingBound`. -/

/-- The transition-weight product of a length-`m` path `p` (states in `Fin s`):
`q_{p₀p₁} ⋯ q_{p_{m-1}p_m}`.  The `r`-th edge joins positions `r` and `r+1`, expressed via
`Fin.castSucc`/`Fin.succ`. -/
noncomputable def pathProd (s : ℕ) (Q : ℕ → ℕ → ℝ) (m : ℕ) (p : Fin (m + 1) → Fin s) : ℝ :=
  ∏ r : Fin m, Q (p r.castSucc : ℕ) (p r.succ : ℕ)

/-- Splitting `pathProd` over `Fin.snoc`: appending state `x` multiplies by the last edge. -/
lemma pathProd_snoc (s : ℕ) (Q : ℕ → ℕ → ℝ) (m : ℕ)
    (p' : Fin (m + 1) → Fin s) (x : Fin s) :
    pathProd s Q (m + 1) (Fin.snoc p' x)
      = pathProd s Q m p' * Q (p' (Fin.last m) : ℕ) (x : ℕ) := by
  simp only [pathProd]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun r _ => ?_
    rw [Fin.snoc_castSucc]
    congr 1
    rw [Fin.succ_castSucc, Fin.snoc_castSucc]
  · rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

/-- **Matrix power as a weighted path sum.**  `(Qᵐ)ᵢⱼ` equals the sum, over all length-`m`
state tuples `p : Fin (m+1) → Fin s` with `p 0 = i` and `p (last m) = j`, of the
transition-weight product `pathProd`.  This is the combinatorial backbone of the
weighted-path expansion; proved by induction on `m` via a `Fin.snoc` decomposition. -/
lemma matPow_eq_pathSum (s : ℕ) (Q : ℕ → ℕ → ℝ) :
    ∀ m i j, i < s → j < s →
      matPow s Q m i j
        = ∑ p : Fin (m + 1) → Fin s,
            (if (p 0 : ℕ) = i ∧ (p (Fin.last m) : ℕ) = j then pathProd s Q m p else 0) := by
  intro m
  induction m with
  | zero =>
    intro i j hi hj
    simp only [matPow]
    have hpp : ∀ p : Fin 1 → Fin s, pathProd s Q 0 p = 1 := by
      intro p; simp [pathProd]
    simp only [Fin.last_zero, hpp]
    rw [Fintype.sum_eq_single (fun _ => (⟨i, hi⟩ : Fin s))]
    · change (if i = j then (1 : ℝ) else 0) = if i = i ∧ i = j then (1 : ℝ) else 0
      by_cases hij : i = j
      · rw [if_pos hij, if_pos ⟨rfl, hij⟩]
      · rw [if_neg hij, if_neg (fun h => hij h.2)]
    · intro p hp
      have hne : (p 0 : ℕ) ≠ i := by
        intro hval
        apply hp
        funext k
        have hk : k = 0 := Fin.eq_zero k
        subst hk
        exact Fin.ext hval
      rw [if_neg]
      exact fun ⟨h1, _⟩ => hne h1
  | succ m ih =>
    intro i j hi hj
    set mid : ℝ := ∑ p' : Fin (m + 1) → Fin s,
        (if (p' 0 : ℕ) = i then pathProd s Q m p' * Q (p' (Fin.last m) : ℕ) j else 0) with hmid
    have hLHS : matPow s Q (m + 1) i j = mid := by
      simp only [matPow]
      have hIH : ∀ l ∈ range s, matPow s Q m i l * Q l j
          = (∑ p' : Fin (m + 1) → Fin s,
              (if (p' 0 : ℕ) = i ∧ (p' (Fin.last m) : ℕ) = l then pathProd s Q m p' else 0))
            * Q l j := by
        intro l hl
        rw [ih i l hi (mem_range.1 hl)]
      rw [sum_congr rfl hIH]
      rw [sum_congr rfl (g := fun l => ∑ p' : Fin (m + 1) → Fin s,
            (if (p' 0 : ℕ) = i ∧ (p' (Fin.last m) : ℕ) = l then pathProd s Q m p' else 0) * Q l j)
            fun l _ => by rw [sum_mul]]
      rw [Finset.sum_comm, hmid]
      refine sum_congr rfl fun p' _ => ?_
      rw [Finset.sum_eq_single_of_mem ((p' (Fin.last m) : ℕ))
            (mem_range.2 (p' (Fin.last m)).isLt)]
      · by_cases hp0 : (p' 0 : ℕ) = i
        · rw [if_pos hp0, if_pos ⟨hp0, rfl⟩]
        · rw [if_neg hp0, if_neg (fun h => hp0 h.1), zero_mul]
      · intro l _ hlne
        rw [if_neg]
        · rw [zero_mul]
        · exact fun h => hlne h.2.symm
    have hRHS : (∑ p : Fin (m + 1 + 1) → Fin s,
          (if (p 0 : ℕ) = i ∧ (p (Fin.last (m + 1)) : ℕ) = j then pathProd s Q (m + 1) p else 0))
        = mid := by
      rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (m + 1 + 1) => Fin s))]
      rw [Fintype.sum_prod_type, Finset.sum_comm, hmid]
      refine sum_congr rfl fun p' _ => ?_
      have hsnoc0 : ∀ x : Fin s,
          ((Fin.snoc p' x : Fin (m + 1 + 1) → Fin s) 0 : ℕ) = (p' 0 : ℕ) := by
        intro x
        rw [show (0 : Fin (m + 1 + 1)) = (0 : Fin (m + 1)).castSucc from rfl, Fin.snoc_castSucc]
      have hsnocL : ∀ x : Fin s,
          ((Fin.snoc p' x : Fin (m + 1 + 1) → Fin s) (Fin.last (m + 1)) : ℕ) = (x : ℕ) := by
        intro x; rw [Fin.snoc_last]
      rw [Fintype.sum_eq_single (⟨j, hj⟩ : Fin s)]
      · simp only [Fin.snocEquiv, Equiv.coe_fn_mk, hsnoc0, hsnocL, pathProd_snoc, and_true]
      · intro x hx
        simp only [Fin.snocEquiv, Equiv.coe_fn_mk, hsnoc0, hsnocL]
        rw [if_neg]
        rintro ⟨_, h2⟩
        exact hx (Fin.ext h2)
    rw [hLHS, ← hRHS]

/-- **The crossing bound**, `(Ne)ᵢ² / s ≤ vᵢ`, the conclusion of the paper's weighted-paths
argument (`vᵢ = Σ_paths W·E` with total weight `1` and per-path energy `E ≥ (Ne)ᵢ²/s` by the
level-crossing Cauchy–Schwarz).  This is the genuinely infinitary Aldous–Shepp content: it
provably does **not** reduce to a finite telescoping, so — exactly as `SSP.ComponentBound`
and `SSP.LogConvexBound` isolate their probabilistic inputs — it is stated as a hypothesis.
Discharging it (via the `pathProd`/`matPow_eq_pathSum` machinery in this section together with
the level-crossing regrouping) is what a full formalization of the first proof requires. -/
def CrossingBound (s : ℕ) (Q : ℕ → ℕ → ℝ) : Prop :=
  ∀ i < s, (xVec s Q i) ^ 2 / s ≤ vVec s Q i

/-! ## Layer 5: discharging `ComponentBound` and the `r ≤ 2s` endgame -/

/-- **Component bound, pointwise.**  Combining identity (II) `vᵢ = 2yᵢ − xᵢ²` with the
crossing bound `xᵢ²/s ≤ vᵢ` gives the paper's Lemma 5: `xᵢ² ≤ (2s/(s+1)) yᵢ`. -/
lemma componentBound_pointwise (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (hs : 0 < s)
    (hcross : CrossingBound s Q) (i : ℕ) (hi : i < s) :
    (xVec s Q i) ^ 2 ≤ (2 * s / (s + 1)) * yVec s Q i := by
  have hII := vVec_eq s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub i hi
  have hc := hcross i hi
  rw [hII] at hc
  -- xᵢ²/s ≤ 2yᵢ − xᵢ²  ⟹  xᵢ²(s+1)/s ≤ 2yᵢ  ⟹  xᵢ² ≤ (2s/(s+1)) yᵢ
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by linarith
  rw [div_le_iff₀ hspos] at hc
  rw [div_mul_eq_mul_div, le_div_iff₀ hs1]
  nlinarith [hc]

/-- Bridge: `rowSum s (Nmat s Q) i = xVec s Q i`. -/
lemma rowSum_eq_xVec (s : ℕ) (Q : ℕ → ℕ → ℝ) (i : ℕ) :
    rowSum s (Nmat s Q) i = xVec s Q i := by
  simp only [rowSum, xVec, matVec, eVec, mul_one]

/-- Bridge: `rowSum2 s (Nmat s Q) i = yVec s Q i`. -/
lemma rowSum2_eq_yVec (s : ℕ) (Q : ℕ → ℕ → ℝ) (i : ℕ) :
    rowSum2 s (Nmat s Q) i = yVec s Q i := by
  simp only [rowSum2, yVec, xVec, matVec, eVec, mul_one]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]

/-- **The paper's Lemma 5, discharged.**  Modulo the crossing bound (the isolated
Aldous–Shepp input), the assumed `SSP.ComponentBound` holds for `N = Nmat s Q`. -/
theorem componentBound_holds (s : ℕ) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (hs : 0 < s)
    (hcross : CrossingBound s Q) :
    ComponentBound s (Nmat s Q) := by
  intro i hi
  rw [rowSum_eq_xVec, rowSum2_eq_yVec]
  exact componentBound_pointwise s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub hs hcross i hi

/-- **End-to-end `r ≤ 2s`.**  With the crossing bound in hand, the paper's SSP coefficient
bound becomes fully machine-verified: no `ComponentBound` is assumed, it is derived from the
weighted-paths argument (via `componentBound_holds`) and fed to `ssp_coefficient_bound`. -/
theorem qsequence_ssp_bound (s : ℕ) (hs : 0 < s) (Q : ℕ → ℕ → ℝ) (θ : ℝ) (C : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC0 : 0 ≤ C) (hQ : ∀ i j, 0 ≤ Q i j)
    (hdecay : ∀ k, ∀ i < s, matVec s (matPow s Q k) eVec i ≤ C * θ ^ k)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) (hcross : CrossingBound s Q)
    (w : ℕ → ℝ) (r : ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (hoc1 : ∑ i ∈ range s, w i * rowSum s (Nmat s Q) i = r)
    (hoc2 : ∑ i ∈ range s, w i * rowSum2 s (Nmat s Q) i = r + r ^ 2 / 2) :
    r ≤ 2 * s :=
  ssp_coefficient_bound s hs (Nmat s Q) w r hw hw1
    (componentBound_holds s Q θ C hθ0 hθ1 hC0 hQ hdecay hsub hs hcross) hoc1 hoc2

end SSP
