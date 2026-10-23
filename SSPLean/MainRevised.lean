import SSPLean.SSPBound
import SSPLean.MomentHierarchy
import SSPLean.QSequenceCrossing
import SSPLean.SpectralRadiusLtOne
import SSPLean.BStability
import SSPLean.K2ShortProof
import SSPLean.MainRevisedSupport

/-!
# Results of `main_revised.tex`, in Lean

The numbered index at the end covers all 18 active theorem, lemma and corollary
environments in the October 23, 2026 source. It distinguishes proofs from
conditional or partial formalizations. The paper's theorem, lemma and corollary
counters are independent; the index does not use the older auxiliary file.

Finite matrices use either `Fin s` indices or functions on `ℕ` read on `range s`.
Moment results use the repository's concrete transient and uniformized density
representations, including subprobability initial weights for an atom at zero.

The analytic monotonicity and sharpness theorem (Theorem 1) is still represented
only by a transfer hypothesis. The two-stage sharpness witness remains a partial formalization of Corollary 2.
Legacy declarations for the former A-stability section are retained for callers;
they are not numbered results in the current paper. The full cyclic all-k
hierarchy is false in the revised paper, which supplies a six-state counterexample
at k = 71. The acyclic all-k and cyclic k = 2 inequalities are proved below.
-/

open Finset

namespace SSP.MainRevised

/-! ## §2. Runge–Kutta methods and strong stability preservation -/

/-- **Definition (SSP conditions), paper eq. `KFSconditions`.**  The five conditions whose
largest admissible `r` is the SSP coefficient `𝒞(A,b)`, written for the matrix `N = I + rA`
and weights `wᵗ = r bᵗ N⁻¹` as in paper eq. `NemethSSPconditions`.

`Ninv` stands for `N⁻¹` and `Q = I − N⁻¹`; stating the conditions in terms of a supplied
inverse avoids committing to a matrix-inverse API at this level of generality. -/
structure SSPConditions (s : ℕ) (N Ninv : ℕ → ℕ → ℝ) (w : ℕ → ℝ) : Prop where
  /-- `N⁻¹` is a genuine inverse of `N` on `range s`. -/
  inv_left : ∀ i < s, ∀ j < s, ∑ k ∈ range s, Ninv i k * N k j = if i = j then 1 else 0
  /-- `N⁻¹ 1 ≥ 0`, paper eq. `NSSP2`. -/
  rowSum_nonneg : ∀ i < s, 0 ≤ ∑ j ∈ range s, Ninv i j
  /-- `Q = I − N⁻¹ ≥ 0`, paper eq. `NSSP3`. -/
  sub_nonneg : ∀ i < s, ∀ j < s, 0 ≤ (if i = j then 1 else 0) - Ninv i j
  /-- `w ≥ 0`. -/
  w_nonneg : ∀ i, 0 ≤ w i
  /-- `1 − wᵗ1 ≥ 0`. -/
  w_sum_le_one : ∑ i ∈ range s, w i ≤ 1

/-- **Definition (order conditions), paper eq. `NemethOrderConditions`.**  The order-two
bushy-tree conditions in the `N, w` variables. -/
def OrderTwo (s : ℕ) (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (r : ℝ) : Prop :=
  (∑ i ∈ range s, w i * rowSum s N i = r) ∧
  (∑ i ∈ range s, w i * rowSum2 s N i = r + r ^ 2 / 2)

/-- **Definition (order-three conditions).**  Adds the third bushy-tree condition, as in
Theorem `order3`. -/
def OrderThree (s : ℕ) (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (r : ℝ) : Prop :=
  OrderTwo s N w r ∧
  (∑ i ∈ range s, w i * rowSum3 s N i = r + r ^ 2 + r ^ 3 / 6)

/-- **Theorem `sspthm` (Kraaijevanger; Ferracina–Spijker), as a hypothesis.**

The theorem states that for `f` satisfying the forward-Euler circle condition with
parameter `Δt_FE`, the Runge–Kutta solution is monotone for `0 ≤ Δt ≤ 𝒞(A,b)·Δt_FE`, and
that this is sharp.  Its content is analytic — it quantifies over all `f` in a class and
over a (semi)norm — and it is used in the paper only through the following consequence: any
`r` below the SSP coefficient satisfies the algebraic conditions.  That consequence is what
we isolate, since it is exactly what Corollary `unconditional` consumes. -/
def KFSTransfer (s : ℕ) (Ssp : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → r < Ssp →
    ∃ N Ninv w, SSPConditions s N Ninv w ∧ OrderTwo s N w r

/-! ## §2.3. The SSP bound `r ≤ 2s`

The four lemmas of the paper's §2.3 and its main theorem. -/

/-- **Lemma `wcs` (weighted Cauchy–Schwarz bound).**  Exactly
`SSP.weighted_cauchy_schwarz`. -/
theorem weighted_cauchy_schwarz (s : ℕ) (w u v : ℕ → ℝ) (K : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (huv : ∀ i < s, (u i) ^ 2 ≤ K * v i) :
    (∑ i ∈ range s, w i * u i) ^ 2 ≤ K * ∑ i ∈ range s, w i * v i :=
  SSP.weighted_cauchy_schwarz s w u v K hw hw1 huv

/-- **Lemma `substochastic`, first part.**  From `N⁻¹1 ≥ 0` and `Q = I − N⁻¹` one gets
`Q1 ≤ 1`.  This is the two-line half of the paper's proof; no spectral input is needed. -/
theorem substochastic_rowSum_le (s : ℕ) (Ninv : ℕ → ℕ → ℝ)
    (hNrow : ∀ i < s, 0 ≤ ∑ j ∈ range s, Ninv i j) (i : ℕ) (hi : i < s) :
    ∑ j ∈ range s, ((if i = j then (1:ℝ) else 0) - Ninv i j) ≤ 1 := by
  have hsplit : ∑ j ∈ range s, ((if i = j then (1:ℝ) else 0) - Ninv i j)
      = (∑ j ∈ range s, (if i = j then (1:ℝ) else 0)) - ∑ j ∈ range s, Ninv i j :=
    Finset.sum_sub_distrib _ _
  rw [hsplit]
  have hone : ∑ j ∈ range s, (if i = j then (1:ℝ) else 0) = 1 := by
    simp [Finset.sum_ite_eq, Finset.mem_range, hi]
  rw [hone]
  linarith [hNrow i hi]

/-- **Lemma `substochastic`, second part.**  A nonnegative matrix with row sums at most
one has all entries in `[0,1]`.  This is `SSP.entry_le_one_of_substochastic`. -/
theorem substochastic_entry_mem (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1) :
    ∀ i < s, ∀ j < s, 0 ≤ Q i j ∧ Q i j ≤ 1 :=
  fun i hi j hj => ⟨hQ i j, SSP.entry_le_one_of_substochastic s Q hQ hrow i hi j hj⟩

/-- **Lemma `substochastic`, spectral part.**  `ρ(Q) < 1` for a substochastic `Q` with
`I − Q` invertible.  This is `SSP.Elementary.spectralRadius_lt_one_elementary`, proved in this
repository without Perron–Frobenius (the paper's proof invokes it). -/
theorem substochastic_spectralRadius {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) (hinv : IsUnit (1 - Q)) :
    spectralRadius ℂ (Q.map (algebraMap ℝ ℂ)) < 1 :=
  SSP.Elementary.spectralRadius_lt_one_elementary Q hQ hrow hinv

/-- **Lemma `neumann2`, coefficient identity — counting form only.**

The paper's Lemma `neumann2` is the analytic identity `(I−Q)⁻² = ∑ₖ (k+1) Qᵏ`, obtained by
differentiating a Neumann series (the paper also remarks that a counting proof is available).

This declaration proves the combinatorial core of that remark: the number of pairs
`(j,k)` with `j + k = n` is `n + 1`, so the `Qⁿ` coefficient of `(∑ₖ Qᵏ)²` is `n + 1`.  The
actual convergent matrix identity is `neumann_square_series` below. The scalar
rearrangement `neumann2_weighted_series` is a separate supporting result. -/
theorem neumann_square_coeff (n : ℕ) :
    (Finset.range (n + 1)).card = n + 1 := by
  simp

/-- The same identity in the form used to read off the Cauchy product: for each `n`, the
pairs `(j, n - j)` with `j ≤ n` are exactly `n + 1` in number, so the `Qⁿ` coefficient of
`(∑ₖ Qᵏ)²` is `n + 1`. -/
theorem neumann_square_pairs (n : ℕ) :
    ((Finset.range (n + 1)).image (fun j => (j, n - j))).card = n + 1 := by
  have hinj : Function.Injective (fun j : ℕ => (j, n - j)) := by
    intro a b h
    exact (Prod.ext_iff.1 h).1
  rw [Finset.card_image_of_injective _ hinj]
  simp

/-! ## The analytic half of Lemma `neumann2`

The paper's Lemma `neumann2` is the identity `(I−Q)⁻² = ∑ₖ (k+1) Qᵏ`.  Its combinatorial core
is `neumann_square_coeff` above. The scalar `tsum` rearrangement below is supporting
content; the complete matrix statement is `neumann_square_series`.

The hypothesis is geometric decay, not bare summability.  That is essential and not a
convenience: `pₙ = 1/(n+1)²` is summable while `∑ₙ (n+1)pₙ = ∑ₙ 1/(n+1)` diverges, so the
identity is *false* under `Summable p` alone.  Geometric decay is exactly what the repository
supplies (`SSP.rowSum_decay_of_spectralRadius`, feeding the `hdecay` hypotheses throughout
`SSPLean.QSequencePaths`). -/

/-- The fibre of `(k,j) ↦ k+j` over `n`, equivalent to `Fin (n+1)`.  This is
`neumann_square_pairs` upgraded from a cardinality count to a bijection, which is what the
`tsum` rearrangement consumes. -/
noncomputable def fibreEquiv (n : ℕ) :
    ((fun kj : ℕ × ℕ => kj.1 + kj.2) ⁻¹' {n}) ≃ Fin (n + 1) := by
  refine ⟨fun b => ⟨(b : ℕ × ℕ).1, ?_⟩, fun i => ⟨(i.val, n - i.val), ?_⟩, ?_, ?_⟩
  · have : (b : ℕ × ℕ).1 + (b : ℕ × ℕ).2 = n := b.2
    omega
  · change (i.val, n - i.val).1 + (i.val, n - i.val).2 = n
    simp only []; omega
  · intro b
    have hb : (b : ℕ × ℕ).1 + (b : ℕ × ℕ).2 = n := b.2
    apply Subtype.ext
    change ((b : ℕ × ℕ).1, n - (b : ℕ × ℕ).1) = (b : ℕ × ℕ)
    have : n - (b : ℕ × ℕ).1 = (b : ℕ × ℕ).2 := by omega
    rw [this]
  · intro i; apply Fin.ext; rfl

/-- **Supporting scalar rearrangement for Lemma `neumann2`.** For `p` nonnegative with geometric decay
`pₙ ≤ C θⁿ`, `0 ≤ θ < 1`,
```
  ∑' (kj : ℕ × ℕ), p (kj.1 + kj.2)  =  ∑' n, (n+1) · pₙ .
```
Applied to `pₖ = (Qᵏ1)ᵢ`, it rearranges the scalar plane sum into the weighted
series. Identifying the plane sum with the inverse square also requires the
matrix Neumann identity, proved separately in `neumann_square_series`.

The proof groups the plane sum over the fibres of `(k,j) ↦ k+j`; on the fibre over `n` the
summand is constant at `pₙ`, and the fibre has `n+1` elements by `fibreEquiv`. -/
theorem neumann2_weighted_series (p : ℕ → ℝ) (C θ : ℝ) (hp : ∀ n, 0 ≤ p n)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C) (hd : ∀ n, p n ≤ C * θ ^ n) :
    ∑' (kj : ℕ × ℕ), p (kj.1 + kj.2) = ∑' (n : ℕ), ((n : ℝ) + 1) * p n := by
  have hsum : Summable (fun kj : ℕ × ℕ => p (kj.1 + kj.2)) := by
    have hmaj : Summable (fun kj : ℕ × ℕ => (C * θ ^ kj.1) * θ ^ kj.2) :=
      Summable.mul_of_nonneg ((summable_geometric_of_lt_one hθ0 hθ1).mul_left C)
        (summable_geometric_of_lt_one hθ0 hθ1)
        (fun n => by positivity) (fun n => by positivity)
    refine hmaj.of_nonneg_of_le (fun kj => hp _) (fun kj => ?_)
    calc p (kj.1 + kj.2) ≤ C * θ ^ (kj.1 + kj.2) := hd _
      _ = (C * θ ^ kj.1) * θ ^ kj.2 := by rw [pow_add]; ring
  have hfib := hsum.hasSum.tsum_fiberwise (fun kj : ℕ × ℕ => kj.1 + kj.2)
  rw [← hfib.tsum_eq]
  refine tsum_congr fun n => ?_
  have hconst : ∀ b : ((fun kj : ℕ × ℕ => kj.1 + kj.2) ⁻¹' {n}),
      p ((b : ℕ × ℕ).1 + (b : ℕ × ℕ).2) = p n := by
    intro b
    have : (b : ℕ × ℕ).1 + (b : ℕ × ℕ).2 = n := b.2
    rw [this]
  rw [tsum_congr hconst, tsum_const, nsmul_eq_mul]
  congr 1
  rw [Nat.card_congr (fibreEquiv n), Nat.card_eq_fintype_card, Fintype.card_fin]
  push_cast; ring

/-! ### Lemma `AS` (substochastic sequence inequality)

The standalone series statement is `substochastic_sequence_inequality` below.
It uses the component bound together with convergent matrix Neumann series,
including the square, rather than formalizing the paper's probabilistic proof. -/

/-- **Lemma `componentbound` (componentwise bound), verbatim.**

The paper: if `Q ≥ 0`, `Q1 ≤ 1` and `I − Q` is invertible, then `N = (I−Q)⁻¹` satisfies, for
every `i`,
```
  ((N1)ᵢ)² ≤ (2s/(s+1)) · (N²1)ᵢ .
```
Here `(N1)ᵢ` is `SSP.rowSum s (SSP.invMat s Q) i` and `(N²1)ᵢ` is `SSP.rowSum2 s …`, both
explicit finite sums, and `SSP.invMat s Q` is the entrywise view of `(I−Q)⁻¹`.

The paper derives this from Lemma `AS` via the Neumann series of Lemma `neumann2`, i.e. from
`(∑ₖ pₖ)² ≤ (2s/(s+1)) ∑ₖ (k+1) pₖ` with `pₖ = (Qᵏ1)ᵢ`.  This repository instead proves the
matrix form directly and unconditionally, by the weighted-paths/crossing argument of
`SSPLean.QSequenceCrossing`; that development also yields the Aldous–Shepp statement the
paper's remark refers to, and Appendix A's Lemma (`targetstatement`) is this same inequality
with an independent elementary proof. -/
theorem componentwise_bound (s : ℕ) (hs : 0 < s) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (hinv : IsUnit (1 - SSP.toMat s Q)) :
    ∀ i < s, (SSP.rowSum s (SSP.invMat s Q) i) ^ 2
      ≤ (2 * s / (s + 1)) * SSP.rowSum2 s (SSP.invMat s Q) i :=
  SSP.componentBound_unconditional_of_invertible' s Q hQ hsub hinv hs

/-- **Theorem `alt` (§`altproof`), the restatement of Theorem `SSPbound` with minimal
hypotheses.**

The paper's Theorem `alt`: let `N` be an invertible real `s × s` matrix with `M = N⁻¹`
satisfying `M1 ≥ 0` and `M ≤ I` entrywise; let `w ≥ 0` with `wᵀ1 ≤ 1`, and let `r ≥ 0` satisfy
`wᵀN1 = r` and `wᵀN²1 = r + r²/2`.  Then `r ≤ 2s`.

`M ≤ I` entrywise is `Q := I − N⁻¹ ≥ 0` (`hQ`), and `M1 ≥ 0` is `hNrow`.  Formerly named
`componentBound`, which misdescribed it: the conclusion is `r ≤ 2s`, not the componentwise
inequality of Lemma `componentbound` — that is `componentwise_bound` above. -/
theorem ssp_bound_of_invMat (s : ℕ) (hs : 0 < s) (N : Matrix (Fin s) (Fin s) ℝ)
    (hNunit : IsUnit N) (hQ : ∀ i j, 0 ≤ SSP.subFromInv s N i j)
    (hNrow : ∀ i : Fin s, 0 ≤ ∑ j, N⁻¹ i j)
    (w : ℕ → ℝ) (r : ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (hoc : OrderTwo s (SSP.ofMat s N) w r) :
    r ≤ 2 * s :=
  SSP.qsequence_ssp_bound_unconditional_of_invMat s hs N hNunit hQ hNrow w r hw hw1
    hoc.1 hoc.2

/-- **Theorem `SSPbound`: `r ≤ 2s`.**  The endgame of the paper's §2.3, taking the
component bound as input: `SSP.ssp_coefficient_bound`. -/
theorem ssp_bound (s : ℕ) (hs : 0 < s) (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (r : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (hCB : SSP.ComponentBound s N) (hoc : OrderTwo s N w r) :
    r ≤ 2 * s :=
  SSP.ssp_coefficient_bound s hs N w r hw hw1 hCB hoc.1 hoc.2

/-- **Corollary `unconditional`.**  Every `r` below the SSP coefficient is at most `2s`,
hence so is the coefficient itself.

Two hypotheses package the two inputs the paper's proof uses.  `KFSTransfer` is
Theorem `sspthm`: below the SSP coefficient the algebraic conditions hold.  Rather than
assume the component bound for *every* matrix — which is false, as `N = [[0,1],[0,0]]`
at `s = 2` shows, since there `(N1)₁ = 1` while `(N²1)₁ = 0` — we build it into the
transfer hypothesis, which is where it is actually available: the `N` produced by
`sspthm` is `(I − Q)⁻¹` for a substochastic `Q`, and for such `N` the bound is the
theorem `SSP.componentBound_unconditional` of this repository. -/
def KFSTransferCB (s : ℕ) (Ssp : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → r < Ssp →
    ∃ N Ninv w, SSPConditions s N Ninv w ∧ OrderTwo s N w r ∧ SSP.ComponentBound s N

theorem unconditional_bound (s : ℕ) (hs : 0 < s) (Ssp : ℝ)
    (hKFS : KFSTransferCB s Ssp) :
    Ssp ≤ 2 * s := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr1, hr2⟩ := exists_between hlt
  have hrpos : 0 < r := lt_of_le_of_lt (by positivity) hr1
  obtain ⟨N, Ninv, w, hSSP, hoc, hCB⟩ := hKFS r hrpos hr2
  have := ssp_bound s hs N w r hSSP.w_nonneg hSSP.w_sum_le_one hCB hoc
  linarith

/-- **Corollary `sharp`, the `s = 2` instance.**  The paper exhibits an `s`-stage
second-order family attaining `𝒞 = 2s`.  Checking the family in general needs its explicit
`N⁻¹`; at `s = 2` the data is small enough to verify directly.  Here `N = I + rA` for the
paper's `A = [[1/4, 0], [1/2, 1/4]]` at `r = 4`, with `w = (0, 1)`, and both order-two
conditions hold at `r = 4 = 2s`. -/
theorem sharp_two_stage_ssp :
    ∃ (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i ∈ range 2, w i ≤ 1) ∧ OrderTwo 2 N w 4 := by
  -- `N = I + 4A = [[2,0],[2,2]]` for `A = [[1/4,0],[1/2,1/4]]`, and `w = r N⁻ᵗ b = (0,1)`
  refine ⟨fun i j => if i = 0 then (if j = 0 then 2 else 0) else 2,
          fun i => if i = 1 then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro i; by_cases h : i = 1 <;> simp [h]
  · norm_num [show (2:ℕ) = 1 + 1 from rfl, Finset.sum_range_succ]
  · change ∑ i ∈ range 2, _ * rowSum 2 _ i = (4:ℝ)
    simp only [rowSum, show (2:ℕ) = 1 + 1 from rfl,
      Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  · change ∑ i ∈ range 2, _ * rowSum2 2 _ i = (4:ℝ) + 4 ^ 2 / 2
    simp only [rowSum2, show (2:ℕ) = 1 + 1 from rfl,
      Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num

/-- The sharp `s = 2` witness also satisfies the component bound, with **equality** in the
second component — confirming that `r = 2s` is exactly the boundary of `ssp_bound` and that
the hypotheses of `unconditional_bound` are simultaneously satisfiable. -/
theorem sharp_two_stage_componentBound :
    SSP.ComponentBound 2 (fun i j => if i = 0 then (if j = 0 then 2 else 0) else 2) := by
  intro i hi
  interval_cases i <;>
    simp only [rowSum2, rowSum, show (2:ℕ) = 1 + 1 from rfl,
      Finset.sum_range_succ, Finset.sum_range_zero] <;> norm_num

/-! ## §4. A moment hierarchy

The acyclic all-k hierarchy and cyclic k = 2 inequality are proved. The full
cyclic all-k statement is false in the current paper. -/

/-- **Conjecture `hierarchy`.**  `mₖ₋₁ mₖ₊₁ / mₖ² ≥ (s+k)/(s+k−1)` for the raw moments of a
phase-type variable of order at most `s`.  Recorded as a predicate on a moment sequence;
this is a predicate, not a theorem; the current paper refutes its full cyclic version.
The case `k = 1` is Aldous–Shepp, which in
this repository is `SSP.componentBound_unconditional`. -/
def MomentHierarchy (s : ℕ) (m : ℕ → ℝ) : Prop :=
  ∀ k ≥ 1, ((s : ℝ) + k) / ((s : ℝ) + k - 1) * (m k) ^ 2 ≤ m (k - 1) * m (k + 1)

/-- **Lemma `mixture` (mixture closure).**  If each `Xⱼ` satisfies
`mₖ₋₁ mₖ₊₁ ≥ κ mₖ²`, so does every finite mixture.  The paper's proof is Cauchy–Schwarz on
the mixing weights; here it is, with `n` components and moments given as functions of the
component index. -/
theorem mixture_closure (n : ℕ) (p : ℕ → ℝ) (M0 M1 M2 : ℕ → ℝ) (κ : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hκ : 0 ≤ κ)
    (hM0 : ∀ j, 0 ≤ M0 j) (hM2 : ∀ j, 0 ≤ M2 j) (hM1 : ∀ j, 0 ≤ M1 j)
    (hcomp : ∀ j < n, κ * (M1 j) ^ 2 ≤ M0 j * M2 j) :
    κ * (∑ j ∈ range n, p j * M1 j) ^ 2
      ≤ (∑ j ∈ range n, p j * M0 j) * (∑ j ∈ range n, p j * M2 j) := by
  -- termwise: `√κ · pⱼM1ⱼ ≤ √(pⱼM0ⱼ)·√(pⱼM2ⱼ)`, then Cauchy–Schwarz on the right
  have hterm : ∀ j ∈ range n,
      Real.sqrt κ * (p j * M1 j)
        ≤ Real.sqrt (p j * M0 j) * Real.sqrt (p j * M2 j) := by
    intro j hj
    have hjn := Finset.mem_range.1 hj
    have h1 : Real.sqrt (p j * M0 j) * Real.sqrt (p j * M2 j)
        = p j * Real.sqrt (M0 j * M2 j) := by
      rw [← Real.sqrt_mul (mul_nonneg (hp j) (hM0 j)),
        show p j * M0 j * (p j * M2 j) = (p j) ^ 2 * (M0 j * M2 j) by ring,
        Real.sqrt_mul (sq_nonneg (p j)), Real.sqrt_sq (hp j)]
    have h2 : Real.sqrt κ * M1 j ≤ Real.sqrt (M0 j * M2 j) := by
      have hsq : (Real.sqrt κ * M1 j) ^ 2 ≤ M0 j * M2 j := by
        rw [mul_pow, Real.sq_sqrt hκ]; exact hcomp j hjn
      have hnn : 0 ≤ Real.sqrt κ * M1 j :=
        mul_nonneg (Real.sqrt_nonneg _) (hM1 j)
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hnn] at this
    rw [h1]
    calc Real.sqrt κ * (p j * M1 j) = p j * (Real.sqrt κ * M1 j) := by ring
      _ ≤ p j * Real.sqrt (M0 j * M2 j) := mul_le_mul_of_nonneg_left h2 (hp j)
  have hsum : Real.sqrt κ * ∑ j ∈ range n, p j * M1 j
      ≤ ∑ j ∈ range n, Real.sqrt (p j * M0 j) * Real.sqrt (p j * M2 j) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm
  have hcs : (∑ j ∈ range n, Real.sqrt (p j * M0 j) * Real.sqrt (p j * M2 j)) ^ 2
      ≤ (∑ j ∈ range n, p j * M0 j) * (∑ j ∈ range n, p j * M2 j) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (range n)
      (fun j => Real.sqrt (p j * M0 j)) (fun j => Real.sqrt (p j * M2 j))
    have e0 : ∀ j ∈ range n, Real.sqrt (p j * M0 j) ^ 2 = p j * M0 j :=
      fun j _ => Real.sq_sqrt (mul_nonneg (hp j) (hM0 j))
    have e2 : ∀ j ∈ range n, Real.sqrt (p j * M2 j) ^ 2 = p j * M2 j :=
      fun j _ => Real.sq_sqrt (mul_nonneg (hp j) (hM2 j))
    rw [Finset.sum_congr rfl e0, Finset.sum_congr rfl e2] at h
    exact h
  have hlhs : 0 ≤ Real.sqrt κ * ∑ j ∈ range n, p j * M1 j :=
    mul_nonneg (Real.sqrt_nonneg _)
      (Finset.sum_nonneg fun j _ => mul_nonneg (hp j) (hM1 j))
  have hstep : (Real.sqrt κ * ∑ j ∈ range n, p j * M1 j) ^ 2
      ≤ (∑ j ∈ range n, p j * M0 j) * (∑ j ∈ range n, p j * M2 j) := by
    refine le_trans (pow_le_pow_left₀ hlhs hsum 2) hcs
  rwa [mul_pow, Real.sq_sqrt hκ] at hstep

/-- **Theorem `order3` (conditional sharp order-3 bound).**  Assuming the `k = 2` case of
the hierarchy (here in the `LogConvexBound` form), the order-three conditions force
`r ≤ s − 1 + √(s² − 1)`.  This is `SSP.order3_ssp_bound`. -/
theorem order3_bound (s : ℕ) (hs : 0 < s) (N : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hLC : SSP.LogConvexBound s N w) (hoc : OrderThree s N w r) :
    r ≤ (s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1) :=
  SSP.order3_ssp_bound s hs N w r hr hLC hoc.1.1 hoc.1.2 hoc.2

/-- **Conjecture `hierarchy` at `k = 2`, unconditionally.**  The `k = 2` instance of the
log-convexity hierarchy, in exactly the `SSP.LogConvexBound` form consumed by
`order3_bound`, for the phase-type law of an arbitrary nonnegative substochastic `Q` in the
general invertible transient chart with an arbitrary subprobability initial weight vector `w`
(missing mass is the permitted atom at `0`).

This discharges the hypothesis `hLC` of `order3_bound`: see `order3_bound_unconditional`
below.  The proof is `SSP.K2Concrete.all_transient_initial_laws_short`, which is
the shorter renewal induction in `phase_type_moment_inequality.tex`. It starts at one
state and uses the terminal Aldous--Shepp bound and the lower-order third-moment
inequalities. The excursion construction is proved in `SSPLean.K2ConcreteInitial`;
`SSPLean.K2ShortProof` supplies the induction without a canonical-representation
hypothesis. The `rowSumᵏ`-to-resolvent translation is `SSP.Bridge`. -/
theorem hierarchy_k2 (s : ℕ) (hs : 1 ≤ s) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ (SSP.toMat s Q) i j)
    (hrow : ∀ i : Fin s, ∑ j, (SSP.toMat s Q) i j ≤ 1)
    (hu : IsUnit (1 - SSP.toMat s Q))
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i : Fin s, w (i : ℕ) ≤ 1) :
    SSP.LogConvexBound s (SSP.invMat s Q) w := by
  have hspos : 0 < s := hs
  -- Work in the general transient model.  Unlike `AbsorptionInitial`, this requires only
  -- substochasticity and invertibility, not a one-step operator-norm contraction.
  let X : SSP.K2Concrete.TransientInitial s :=
    { model :=
        { Q := SSP.toMat s Q, hQ := hQ, hrow := hrow, hu := hu, i := ⟨0, hspos⟩ }
      weight := fun i => w (i : ℕ)
      weight_nonneg := fun i => hw _
      weight_sum_le_one := hw1 }
  have h := SSP.K2Concrete.all_transient_initial_laws_short hs X
  -- translate the `rowSumᵏ` sums into the resolvent `mulVec` form
  unfold SSP.LogConvexBound
  have e1 : ∀ i : Fin s, SSP.rowSum s (SSP.invMat s Q) (i : ℕ)
      = ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i := by
    intro i
    simpa using SSP.Bridge.rowSum_invMat_eq Q (i : ℕ) i.isLt
  have e2 : ∀ i : Fin s, SSP.rowSum2 s (SSP.invMat s Q) (i : ℕ)
      = ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i := by
    intro i
    simpa using SSP.Bridge.rowSum2_invMat_eq Q (i : ℕ) i.isLt
  have e3 : ∀ i : Fin s, SSP.rowSum3 s (SSP.invMat s Q) (i : ℕ)
      = ((1 - SSP.toMat s Q)⁻¹.mulVec ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i := by
    intro i
    simpa using SSP.Bridge.rowSum3_invMat_eq Q (i : ℕ) i.isLt
  rw [← Fin.sum_univ_eq_sum_range (fun i => w i * SSP.rowSum2 s (SSP.invMat s Q) i) s,
      ← Fin.sum_univ_eq_sum_range (fun i => w i * SSP.rowSum s (SSP.invMat s Q) i) s,
      ← Fin.sum_univ_eq_sum_range (fun i => w i * SSP.rowSum3 s (SSP.invMat s Q) i) s]
  simp_rw [e1, e2, e3]
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  -- Pull the constants 2 and 6 out of the transient raw moments appearing in `h`.
  have c2 : ∑ i : Fin s, X.weight i *
        (2 * ((1 - (X.component i).Q)⁻¹.mulVec
          ((1 - (X.component i).Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) (X.component i).i)
      = 2 * ∑ i : Fin s, w (i : ℕ) *
        ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp [X, SSP.K2Concrete.TransientInitial.component]
      ring
  have c6 : ∑ i : Fin s, X.weight i *
        (6 * ((1 - (X.component i).Q)⁻¹.mulVec ((1 - (X.component i).Q)⁻¹.mulVec
          ((1 - (X.component i).Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) (X.component i).i)
      = 6 * ∑ i : Fin s, w (i : ℕ) *
        ((1 - SSP.toMat s Q)⁻¹.mulVec ((1 - SSP.toMat s Q)⁻¹.mulVec
          ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ))))) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp [X, SSP.K2Concrete.TransientInitial.component]
      ring
  have c1 : ∑ i : Fin s, X.weight i *
        ((1 - (X.component i).Q)⁻¹.mulVec (fun _ => (1 : ℝ))) (X.component i).i
      = ∑ i : Fin s, w (i : ℕ) *
        ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i := by
    exact Finset.sum_congr rfl fun i _ => by
      simp [X, SSP.K2Concrete.TransientInitial.component]
  unfold SSP.K2AllStages.StageBound SSP.K2Concrete.transientInitialMoment1
    SSP.K2Concrete.transientInitialMoment2 SSP.K2Concrete.transientInitialMoment3
    SSP.K2Concrete.transientMoment1 SSP.K2Concrete.transientMoment2
    SSP.K2Concrete.transientMoment3 at h
  rw [c1, c2, c6] at h
  rw [div_mul_eq_mul_div, div_le_iff₀ hs1]
  nlinarith [h]

/-- **Theorem `order3`, unconditionally.**  For an arbitrary finite nonnegative
substochastic transient matrix, the order-three moment identities imply the sharp bound
`r ≤ s - 1 + √(s² - 1)`.  This is the paper's conditional theorem with its `k = 2`
hierarchy premise discharged by `hierarchy_k2`. -/
theorem order3_bound_unconditional (s : ℕ) (hs : 1 ≤ s) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ i j, 0 ≤ (SSP.toMat s Q) i j)
    (hrow : ∀ i : Fin s, ∑ j, (SSP.toMat s Q) i j ≤ 1)
    (hu : IsUnit (1 - SSP.toMat s Q))
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i : Fin s, w (i : ℕ) ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) (hoc : OrderThree s (SSP.invMat s Q) w r) :
    r ≤ (s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1) := by
  exact order3_bound s (by omega) (SSP.invMat s Q) w r hr
    (hierarchy_k2 s hs Q hQ hrow hu w hw hw1) hoc

/-! ### Equality in Theorem `SSPbound` / `alt` (paper Remark `uniqueness`)

The paper records the `r = 2s` equality case as an open question.  It is proved, as an
equivalence, in `SSPLean.SSPBoundEquality` — which imports this file, so the results cannot
be restated here without a cycle.  The entry points are:

* `SSP.orderTwo_two_mul_iff_halfRateSerialErlang` — equality holds iff `wᵀ𝟙 = 1` and every
  positively weighted state is the head of a serial Erlang chain of common rate `1/2`
  (`IsHalfRateSerialErlang`), up to a relabeling of the transient states.
* `SSP.orderTwo_two_mul_iff_halfRateSerialMat` — the same statement with the chain given as
  the explicit matrix `SSP.halfRateSerialMat s = (1/2)(I + S)`, `S` the forward shift, with
  `SSP.halfRateSerialMat_inv` identifying `(I - Q)⁻¹` as `2` on and above the diagonal.
* `SSP.orderTwo_two_mul_iff_attainsSSPBound` — the abstract half, conditional on
  `ComponentBound`, before the matrix structure is extracted.

The rate `1/2` is forced by the endpoint `r = 2s`, not assumed; the general serial-chain
predicate `IsSerialErlang` allows any rate in `(0, 1]`.  Note this characterizes the
`(Q, w)` / q-sequence side; transporting it to Butcher coefficients `(A, b)` goes through
`KFSTransfer`, which is a hypothesis here rather than a theorem. -/

/-! ## §5. An order barrier for algebraic stability -/

/-- **Definition (Algebraic Stability).**  `B ⪰ 0` and `M = BA + AᵗB − bbᵗ ⪰ 0`, with
`B = diag b`.  Since `B = diag b` is diagonal, `B ⪰ 0` is just `b ≥ 0`; the matrix `M` is
recorded through its quadratic form, as in `SSPLean.BStability`. -/
structure AlgebraicallyStable (s : ℕ) (A : ℕ → ℕ → ℝ) (b : ℕ → ℝ) : Prop where
  b_nonneg : ∀ i, 0 ≤ b i
  M_psd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range s, ∑ j ∈ range s,
    (b i * A i j + b j * A j i - b i * b j) * (x i * x j)

/-- **Lemma `partialsums`.**  Under the ordering `c₁ ≤ ⋯ ≤ c_s`, the two moment conditions
and the partial-sum inequalities force `∑ bᵢcᵢ² ≤ 1/3 − (∑ bᵢ³)/12 < 1/3`.  This is
`SSP.partial_sum_lemma`. -/
theorem partial_sums (b c : ℕ → ℝ) (s : ℕ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i j, i ≤ j → j < s → c i ≤ c j)
    (hsum : ∑ i ∈ range s, b i = 1) (hmean : ∑ i ∈ range s, b i * c i = 1 / 2)
    (hδ : ∀ k ≤ s, (SSP.psum b k) ^ 2 / 2 ≤ ∑ i ∈ range k, b i * c i) :
    ∑ i ∈ range s, b i * (c i) ^ 2 ≤ 1 / 3 - (∑ i ∈ range s, (b i) ^ 3) / 12 :=
  SSP.partial_sum_lemma b c s hb hc hsum hmean hδ

/-- **Theorem `barrier` (order barrier for algebraic stability).**  No Runge–Kutta method
with `A ≥ 0`, `b ≥ 0`, `A1 = c` satisfies the order-three bushy-tree conditions while being
algebraically stable.  This is `SSP.no_order3_algebraically_stable`; the abscissae are
assumed sorted, which the paper's remark justifies by a relabelling. -/
theorem barrier {s : ℕ} {A : ℕ → ℕ → ℝ} {b c : ℕ → ℝ}
    (hA : ∀ i j, 0 ≤ A i j)
    (hc : ∀ i j, i ≤ j → j < s → c i ≤ c j)
    (hrow : ∀ i < s, ∑ j ∈ range s, A i j ≤ c i)
    (h1 : ∑ i ∈ range s, b i = 1)
    (h2 : ∑ i ∈ range s, b i * c i = 1 / 2)
    (h3 : ∑ i ∈ range s, b i * (c i) ^ 2 = 1 / 3)
    (hstab : AlgebraicallyStable s A b) :
    False :=
  SSP.no_order3_algebraically_stable A b c hA hstab.b_nonneg hc hrow h1 h2 h3 hstab.M_psd

/-! ## Additional declarations matching the current numbered statements -/

/-- **Theorem 2 (`thm:SSPbound`)**, directly from the five inverse SSP conditions. -/
theorem ssp_bound_of_conditions (s : ℕ) (hs : 0 < s)
    (N Ninv : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (r : ℝ)
    (hSSP : SSPConditions s N Ninv w) (hoc : OrderTwo s N w r) : r ≤ 2 * s := by
  classical
  let F := SSP.toMat s N
  let M := SSP.toMat s Ninv
  have hleft : M * F = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    change (∑ k : Fin s, Ninv i k * N k j) = if i = j then 1 else 0
    rw [Fin.sum_univ_eq_sum_range (fun k => Ninv i k * N k j) s]
    simpa only [Fin.ext_iff] using hSSP.inv_left i i.isLt j j.isLt
  have hdet := congrArg Matrix.det hleft
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  have hFunit : IsUnit F := by
    apply (Matrix.isUnit_iff_isUnit_det F).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    rw [hz, mul_zero] at hdet
    norm_num at hdet
  have hFinv : F⁻¹ = M := Matrix.inv_eq_left_inv hleft
  have hrows : ∀ i < s, rowSum s (SSP.ofMat s F) i = rowSum s N i := by
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp [SSP.ofMat, F, SSP.toMat, hi, mem_range.mp hj]
  have hrows2 : ∀ i < s, rowSum2 s (SSP.ofMat s F) i = rowSum2 s N i := by
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    simp [SSP.ofMat, F, SSP.toMat, hi, mem_range.mp hj, mem_range.mp hk]
  apply ssp_bound_of_invMat s hs F hFunit
  · intro i j
    unfold SSP.subFromInv
    split_ifs with hij
    · rw [hFinv]
      simpa [M, SSP.toMat, Matrix.sub_apply, Matrix.one_apply, Fin.ext_iff] using
        hSSP.sub_nonneg i hij.1 j hij.2
    · exact le_rfl
  · intro i
    rw [hFinv]
    change 0 ≤ ∑ j : Fin s, Ninv i j
    rw [Fin.sum_univ_eq_sum_range]
    exact hSSP.rowSum_nonneg i i.isLt
  · exact hSSP.w_nonneg
  · exact hSSP.w_sum_le_one
  · constructor
    · rw [Finset.sum_congr rfl (fun i hi => congrArg (fun x => w i * x)
        (hrows i (mem_range.mp hi)))]
      exact hoc.1
    · rw [Finset.sum_congr rfl (fun i hi => congrArg (fun x => w i * x)
        (hrows2 i (mem_range.mp hi)))]
      exact hoc.2

/-- **Corollary 1**, with the component bound derived rather than assumed.
Only the relation between the coefficient and admissible inverse charts remains
an input. This is not a proof of the analytic Theorem 1. -/
theorem unconditional_bound_of_transfer (s : ℕ) (hs : 0 < s) (Ssp : ℝ)
    (hKFS : KFSTransfer s Ssp) : Ssp ≤ 2 * s := by
  by_contra h
  obtain ⟨r, hr1, hr2⟩ := exists_between (lt_of_not_ge h)
  have hrpos : 0 < r := lt_of_le_of_lt (by positivity) hr1
  obtain ⟨N, Ninv, w, hSSP, hoc⟩ := hKFS r hrpos hr2
  have hb := ssp_bound_of_conditions s hs N Ninv w r hSSP hoc
  linarith

/-- **Lemma 2 (`lem:substochastic`), convergent Neumann series and positivity.** -/
theorem substochastic_neumann {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hinv : IsUnit (1 - Q)) :
    spectralRadius ℂ (Q.map (algebraMap ℝ ℂ)) < 1 ∧
      HasSum (fun k : ℕ => Q ^ k) (1 - Q)⁻¹ ∧
        (∀ i j, 0 ≤ (1 - Q)⁻¹ i j) := by
  classical
  have hρ := substochastic_spectralRadius Q hQ hrow hinv
  have hsum := SSP.summable_pow_of_spectralRadius_lt_one Q hρ
  refine ⟨hρ, ?_, ?_⟩
  · simpa only [SSP.tsum_pow_eq_inv_one_sub Q hρ] using hsum.hasSum
  · have hp : ∀ k : ℕ, ∀ i j, 0 ≤ (Q ^ k) i j := by
      intro k
      induction k with
      | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split_ifs <;> positivity
      | succ k ih =>
        intro i j
        rw [pow_succ, Matrix.mul_apply]
        exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (hQ l j))
    intro i j
    have ha : (∑' k : ℕ, Q ^ k) i = ∑' k : ℕ, (Q ^ k) i := tsum_apply hsum
    have hb : (∑' k : ℕ, (Q ^ k) i) j = ∑' k : ℕ, (Q ^ k) i j :=
      tsum_apply ((Pi.summable.mp hsum) i)
    have he := (congrArg (fun f : Fin s → ℝ => f j) ha).trans hb
    rw [← SSP.tsum_pow_eq_inv_one_sub Q hρ, he]
    exact tsum_nonneg (fun k => hp k i j)

/-- **Lemma 3 (`lem:neumann2`), actual matrix identity and convergence.** -/
theorem neumann_square_series {s : ℕ} (Q : Matrix (Fin s) (Fin s) ℝ)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hinv : IsUnit (1 - Q)) :
    spectralRadius ℂ (Q.map (algebraMap ℝ ℂ)) < 1 ∧
      HasSum (fun k : ℕ => ((k : ℝ) + 1) • Q ^ k) ((1 - Q)⁻¹ * (1 - Q)⁻¹) :=
  ⟨substochastic_spectralRadius Q hQ hrow hinv,
    SSP.MainRevisedSupport.neumann_square_hasSum Q
      (substochastic_spectralRadius Q hQ hrow hinv)⟩

/-- **Lemma 4 (`lem:AS`), the substochastic sequence inequality.** -/
theorem substochastic_sequence_inequality (s : ℕ) (hs : 0 < s)
    (Q : ℕ → ℕ → ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hsub : ∀ i < s, ∑ j ∈ range s, Q i j ≤ 1)
    (hρ : spectralRadius ℂ ((SSP.toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (i : Fin s) :
    (∑' k : ℕ, ((SSP.toMat s Q) ^ k).mulVec (fun _ => (1 : ℝ)) i) ^ 2 ≤
      (2 * s / (s + 1)) * ∑' k : ℕ, ((k : ℝ) + 1) *
        ((SSP.toMat s Q) ^ k).mulVec (fun _ => (1 : ℝ)) i :=
  SSP.MainRevisedSupport.substochastic_sequence_inequality s hs Q hQ hsub hρ i

/-- **Theorem 4 (`thm:AldousShepp`), including at most `s` states and an atom at zero.** -/
theorem aldous_shepp {d s : ℕ} (hd : 1 ≤ d) (hds : d ≤ s)
    (X : SSP.K2Concrete.TransientInitial d) :
    ((s : ℝ) + 1) / s * (SSP.K2Concrete.transientInitialMoment1 d X) ^ 2 ≤
      SSP.K2Concrete.transientInitialMoment2 d X := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (lt_of_lt_of_le hd hds)
  have hds' : (d : ℝ) ≤ s := by exact_mod_cast hds
  have hcoef : ((s : ℝ) + 1) / s ≤ ((d : ℝ) + 1) / d := by
    rw [div_le_div_iff₀ hs0 hd0]
    nlinarith
  exact le_trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
    (SSP.K2Concrete.transientInitialAldousSheppMoment hd X)

/-- **Theorem 7 (`thm:cyclic-hierarchy`), ratio form with at most `s` states.** -/
theorem cyclic_hierarchy {d s : ℕ} (hd : 1 ≤ d) (hds : d ≤ s)
    (X : SSP.K2Concrete.TransientInitial d)
    (hm : 0 < SSP.K2Concrete.transientInitialMoment1 d X) :
    ((s : ℝ) + 2) / ((s : ℝ) + 1) ≤
      SSP.K2Concrete.transientInitialMoment1 d X *
        SSP.K2Concrete.transientInitialMoment3 d X /
        (SSP.K2Concrete.transientInitialMoment2 d X) ^ 2 := by
  have hds' : (d : ℝ) ≤ s := by exact_mod_cast hds
  have hcoef : ((s : ℝ) + 2) / ((s : ℝ) + 1) ≤
      ((d : ℝ) + 2) / ((d : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  exact hcoef.trans (SSP.K2Concrete.conjecture_one_k2_short hd X hm)

/-- **Theorem 5 (`thm:OsogamiHarcholBalter`).** The cyclic theorem proves this
inequality for all transient representations, and hence for every acyclic one. -/
theorem osogami_harchol_balter {d s : ℕ} (hd : 1 ≤ d) (hds : d ≤ s)
    (X : SSP.K2Concrete.TransientInitial d)
    (hm : 0 < SSP.K2Concrete.transientInitialMoment1 d X) :
    ((s : ℝ) + 2) / ((s : ℝ) + 1) ≤
      SSP.K2Concrete.transientInitialMoment1 d X *
        SSP.K2Concrete.transientInitialMoment3 d X /
        (SSP.K2Concrete.transientInitialMoment2 d X) ^ 2 :=
  cyclic_hierarchy hd hds X hm

/-- **Theorem 6 (`thm:acyclic-hierarchy`), division-free uniformized density form.**
This form also covers zero moments. `P` is triangular, `u,v` are nonnegative,
and `atom` is the mass at zero. -/
theorem acyclic_hierarchy {s : ℕ} (hs : 1 ≤ s)
    (P : SSP.MatrixMomentReduction.Mat s) (hP : ∀ i j, 0 ≤ P i j)
    (htri : ∀ i j, j < i → P i j = 0)
    (u v : Fin s → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (rate atom : ℝ) (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ((s + k : ℕ) : ℝ) / ((s + k - 1 : ℕ) : ℝ) *
        SSP.MatrixMomentReduction.rawMoment P u v rate atom k ^ 2 ≤
      SSP.MatrixMomentReduction.rawMoment P u v rate atom (k - 1) *
        SSP.MatrixMomentReduction.rawMoment P u v rate atom (k + 1) :=
  SSP.MainRevisedSupport.acyclic_hierarchy hs P hP htri u v hu hv rate atom
    hrate hatom hρ k hk

/-- **Theorem 6 (`thm:acyclic-hierarchy`)**, ratio form with at most `s` states. -/
theorem acyclic_hierarchy_ratio {d s : ℕ} (hd : 1 ≤ d) (hds : d ≤ s)
    (P : SSP.MatrixMomentReduction.Mat d) (hP : ∀ i j, 0 ≤ P i j)
    (htri : ∀ i j, j < i → P i j = 0)
    (u v : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i)
    (rate atom : ℝ) (hrate : 0 < rate) (hatom : 0 ≤ atom)
    (hρ : spectralRadius ℂ (P.map (algebraMap ℝ ℂ)) < 1)
    (hm : 0 < SSP.MatrixMomentReduction.rawMoment P u v rate atom 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ((s + k : ℕ) : ℝ) / ((s + k - 1 : ℕ) : ℝ) ≤
      SSP.MatrixMomentReduction.rawMoment P u v rate atom (k - 1) *
        SSP.MatrixMomentReduction.rawMoment P u v rate atom (k + 1) /
          SSP.MatrixMomentReduction.rawMoment P u v rate atom k ^ 2 :=
  SSP.MainRevisedSupport.acyclic_hierarchy_ratio hd hds P hP htri u v hu hv
    rate atom hrate hatom hρ hm k hk

/-- **Lemma 6 (`lem:alg`), including the zero-denominator convention at `w=0`.** -/
theorem algebraic_inequality (n : ℕ) (hn : 2 ≤ n) (w u β : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w < 1) (hu : 0 ≤ u)
    (hβ : (n : ℝ) / (n - 1) * w ^ 2 ≤ β) (hzero : w = 0 → β = 0) :
    (n + 2 : ℝ) / (n + 1) * (2 * (1 - w) + u + β) ^ 2 ≤
      3 * (1 - w) * (2 * (1 - w) + u + β) + 3 * u +
        (n + 1 : ℝ) / n * (u ^ 2 / (1 - w) + β ^ 2 / w) :=
  SSP.MainRevisedSupport.algebraic_inequality n hn w u β hw0 hw1 hu hβ hzero

/-- **Theorem 8 (`thm:SSPboundP3`)**, from inverse SSP and order-three conditions. -/
theorem order3_bound_of_invMat (s : ℕ) (hs : 1 ≤ s)
    (N : Matrix (Fin s) (Fin s) ℝ) (hNunit : IsUnit N)
    (hQ : ∀ i j, 0 ≤ SSP.subFromInv s N i j)
    (hNrow : ∀ i : Fin s, 0 ≤ ∑ j, N⁻¹ i j)
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i ∈ range s, w i ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) (hoc : OrderThree s (SSP.ofMat s N) w r) :
    r ≤ (s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1) := by
  classical
  let Q := SSP.subFromInv s N
  have hrow : ∀ i : Fin s, ∑ j, SSP.toMat s Q i j ≤ 1 := by
    intro i
    rw [show SSP.toMat s Q = 1 - N⁻¹ from SSP.toMat_subFromInv s N]
    change (∑ j, ((1 : Matrix (Fin s) (Fin s) ℝ) i j - N⁻¹ i j)) ≤ 1
    rw [Finset.sum_sub_distrib]
    have he : (∑ j : Fin s, (1 : Matrix (Fin s) (Fin s) ℝ) i j) = 1 := by
      simp [Matrix.one_apply]
    rw [he]
    linarith [hNrow i]
  have hden : (1 : Matrix (Fin s) (Fin s) ℝ) - SSP.toMat s Q = N⁻¹ := by
    rw [SSP.toMat_subFromInv, sub_sub_cancel]
  have hu : IsUnit (1 - SSP.toMat s Q) :=
    hden ▸ (Matrix.isUnit_nonsing_inv_iff.mpr hNunit)
  have he : ∀ i < s, ∀ j < s, SSP.ofMat s N i j = SSP.invMat s Q i j := by
    intro i hi j hj
    rw [SSP.ofMat, dif_pos (⟨hi, hj⟩ : i < s ∧ j < s),
      SSP.invMat, dif_pos (⟨hi, hj⟩ : i < s ∧ j < s), hden,
      Matrix.nonsing_inv_nonsing_inv N ((Matrix.isUnit_iff_isUnit_det N).mp hNunit)]
  have e1 : ∀ i < s, rowSum s (SSP.ofMat s N) i = rowSum s (SSP.invMat s Q) i :=
    fun i hi => Finset.sum_congr rfl (fun j hj => he i hi j (mem_range.mp hj))
  have e2 : ∀ i < s, rowSum2 s (SSP.ofMat s N) i = rowSum2 s (SSP.invMat s Q) i := by
    intro i hi
    exact Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun l hl => by
      rw [he i hi j (mem_range.mp hj), he j (mem_range.mp hj) l (mem_range.mp hl)]))
  have e3 : ∀ i < s, rowSum3 s (SSP.ofMat s N) i = rowSum3 s (SSP.invMat s Q) i := by
    intro i hi
    exact Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun l hl =>
      Finset.sum_congr rfl (fun m hm => by
        rw [he i hi j (mem_range.mp hj), he j (mem_range.mp hj) l (mem_range.mp hl),
          he l (mem_range.mp hl) m (mem_range.mp hm)])))
  apply order3_bound_unconditional s hs Q (fun i j => hQ i j) hrow hu w hw
  · rwa [Fin.sum_univ_eq_sum_range]
  · exact hr
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hoc.1.1]
      exact Finset.sum_congr rfl (fun i hi => by rw [e1 i (mem_range.mp hi)])
    · rw [← hoc.1.2]
      exact Finset.sum_congr rfl (fun i hi => by rw [e2 i (mem_range.mp hi)])
    · rw [← hoc.2]
      exact Finset.sum_congr rfl (fun i hi => by rw [e3 i (mem_range.mp hi)])

/-- **Lemma 7 (`lem:partialsums`), including the paper's strict inequality.** -/
theorem partial_sums_strict (b c : ℕ → ℝ) (s : ℕ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i j, i ≤ j → j < s → c i ≤ c j)
    (hsum : ∑ i ∈ range s, b i = 1) (hmean : ∑ i ∈ range s, b i * c i = 1 / 2)
    (hδ : ∀ k ≤ s, (SSP.psum b k) ^ 2 / 2 ≤ ∑ i ∈ range k, b i * c i) :
    (∑ i ∈ range s, b i * c i ^ 2 ≤ 1 / 3 - (∑ i ∈ range s, b i ^ 3) / 12) ∧
      (1 / 3 - (∑ i ∈ range s, b i ^ 3) / 12 < (1 : ℝ) / 3) := by
  refine ⟨partial_sums b c s hb hc hsum hmean hδ, ?_⟩
  have hex : ∃ i ∈ range s, 0 < b i := by
    by_contra h
    push Not at h
    have hz : ∑ i ∈ range s, b i = 0 :=
      Finset.sum_eq_zero (fun i hi => le_antisymm (h i hi) (hb i))
    linarith
  obtain ⟨i, hi, hbi⟩ := hex
  have hpos : 0 < ∑ i ∈ range s, b i ^ 3 :=
    Finset.sum_pos' (fun j _ => pow_nonneg (hb j) _) ⟨i, hi, pow_pos hbi _⟩
  linarith

/-- **Theorem 9 (`thm:barrier`), with the stage-sorting step proved.** -/
theorem barrier_unsorted {s : ℕ} (A : Matrix (Fin s) (Fin s) ℝ) (b c : Fin s → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hb : ∀ i, 0 ≤ b i)
    (hrow : ∀ i, ∑ j, A i j = c i)
    (h1 : ∑ i, b i = 1) (h2 : ∑ i, b i * c i = 1 / 2)
    (h3 : ∑ i, b i * c i ^ 2 = 1 / 3)
    (hM : ∀ x : Fin s → ℝ, 0 ≤ ∑ i, ∑ j,
      (b i * A i j + b j * A j i - b i * b j) * (x i * x j)) : False :=
  SSP.MainRevisedSupport.barrier_unsorted A b c hA hb hrow h1 h2 h3 hM

/-! ## Legacy A-stability declarations (not part of the current numbered paper) -/

/-- **Definition (A-stability conditions, Juhl–Shirokoff form).**  There is a symmetric
`R ⪰ 0` with `R1 = b` and `X = RA + AᵗR − bbᵗ ⪰ 0`.  This is the hypothesis set of
`SSPLean.ThreeStageClaim` and `SSPLean.TwoStageClaim`, recorded here in the paper's
notation. -/
structure AStabilityData (s : ℕ) (A R : ℕ → ℕ → ℝ) (b : ℕ → ℝ) : Prop where
  R_symm : ∀ i ∈ range s, ∀ j ∈ range s, R i j = R j i
  R_psd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range s, ∑ j ∈ range s, R i j * (x i * x j)
  R_rowSum : ∀ i ∈ range s, b i = ∑ j ∈ range s, R i j
  X_psd : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range s, ∑ j ∈ range s,
    ((∑ k ∈ range s, R i k * A k j) + (∑ k ∈ range s, R j k * A k i) - b i * b j)
      * (x i * x j)

/-- **Lemma `collapse` ($R$-collapse), the algebraic core.**

The paper's proof runs: `1ᵗM1 = 0` gives `M1 = 0`; then `1ᵗMc = 0` gives `cᵗRc = 1/3`;
comparing with `1ᵗR(c∘c) = bᵗ(c∘c) = 1/3` yields
`0 = 1ᵗR(c∘c) − cᵗRc = ½ ∑ᵢⱼ Rᵢⱼ(cᵢ−cⱼ)²`,
so `Rᵢⱼ > 0` forces `cᵢ = cⱼ`.  The identity in that last display is the algebraic content,
and it is what we record: it holds for any symmetric `R` and any `c`, with no hypotheses. -/
theorem collapse_sum_identity (s : ℕ) (R : ℕ → ℕ → ℝ) (c : ℕ → ℝ)
    (hR : ∀ i ∈ range s, ∀ j ∈ range s, R i j = R j i) :
    (∑ i ∈ range s, ∑ j ∈ range s, R i j * (c j) ^ 2)
      - (∑ i ∈ range s, ∑ j ∈ range s, R i j * (c i * c j))
      = (1/2) * ∑ i ∈ range s, ∑ j ∈ range s, R i j * (c i - c j) ^ 2 := by
  -- Abbreviate the three double sums and expand the square termwise.
  set S1 : ℝ := ∑ i ∈ range s, ∑ j ∈ range s, R i j * (c i) ^ 2 with hS1
  set S2 : ℝ := ∑ i ∈ range s, ∑ j ∈ range s, R i j * (c j) ^ 2 with hS2
  set P : ℝ := ∑ i ∈ range s, ∑ j ∈ range s, R i j * (c i * c j) with hP
  have hexp : ∑ i ∈ range s, ∑ j ∈ range s, R i j * (c i - c j) ^ 2
      = S1 + S2 - 2 * P := by
    rw [hS1, hS2, hP]
    -- rewrite the summand, then split with `sum_add_distrib` / `sum_sub_distrib`
    have step : ∀ i, ∑ j ∈ range s, R i j * (c i - c j) ^ 2
        = ((∑ j ∈ range s, R i j * (c i) ^ 2) + ∑ j ∈ range s, R i j * (c j) ^ 2)
          - ∑ j ∈ range s, 2 * (R i j * (c i * c j)) := by
      intro i
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ range s) => step i),
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  -- Symmetry of `R` identifies `S1` and `S2`.
  have hswap : S1 = S2 := by
    rw [hS1, hS2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [hR j hj i hi]
  rw [hexp, ← hswap]
  linarith

/-- **Conjecture `astability`.**  There is no order-three method with nonnegative
coefficients admitting a symmetric `R ⪰ 0` with `R1 = b` and `X ⪰ 0`.  Open in the paper;
recorded, not proved.  What *is* proved in this repository are the cases `s = 2`
(`SSP.TwoStage.two_stage_claim_inconsistent`) and `s = 3`
(`SSP.ThreeStage.three_stage_claim_inconsistent`), and counterexamples exist for every
`s ≥ 5` (`SSP.claim_false_all_stages_five`), so the conjecture as stated is *false* in
general; `s = 4` is open. -/
def AStabilityBarrier (s : ℕ) : Prop :=
  ∀ (A R : ℕ → ℕ → ℝ) (b c : ℕ → ℝ),
    (∀ i j, 0 ≤ A i j) → (∀ i, 0 ≤ b i) →
    (∀ i ∈ range s, c i = ∑ j ∈ range s, A i j) →
    AStabilityData s A R b →
    ∑ i ∈ range s, b i = 1 → ∑ i ∈ range s, b i * c i = 1/2 →
    ∑ i ∈ range s, b i * (c i) ^ 2 = 1/3 →
    False

end SSP.MainRevised

/-! ## Index: numbered results in `main_revised.tex`

Numbering is from the active October 23, 2026 TeX source. Theorem, lemma and
corollary counters are independent. Every Lean identifier is fully qualified.
"Partial" and "conditional" entries must not be read as proofs of the full
paper statement. A different proof route is acceptable when the statement agrees.

| Paper result | TeX label | Corresponding Lean result | Coverage |
|---|---|---|---|
| Theorem 1 — SSP monotonicity and sharpness | `sspthm` | `SSP.MainRevised.KFSTransfer` | **Missing analytic proof**: this is a predicate/hypothesis, not a theorem. |
| Theorem 2 — SSP bound | `thm:SSPbound` | `SSP.MainRevised.ssp_bound_of_conditions` | Proved from the five inverse SSP conditions and order-two identities; no component-bound hypothesis. |
| Lemma 1 — weighted Cauchy–Schwarz | `lem:wcs` | `SSP.MainRevised.weighted_cauchy_schwarz` | Proved. |
| Lemma 2 — substochastic structure | `lem:substochastic` | `SSP.MainRevised.substochastic_rowSum_le`, `SSP.MainRevised.substochastic_entry_mem`, `SSP.MainRevised.substochastic_neumann` | Proved in these parts, including spectral radius, convergent Neumann series and inverse nonnegativity. |
| Lemma 3 — Neumann series for the square | `lem:neumann2` | `SSP.MainRevised.neumann_square_series` | Proved as an actual matrix `HasSum`, including convergence. |
| Lemma 4 — substochastic sequence inequality | `lem:AS` | `SSP.MainRevised.substochastic_sequence_inequality` | Proved in series form. |
| Lemma 5 — componentwise bound | `lem:componentbound` | `SSP.MainRevised.componentwise_bound` | Proved; also covers the Appendix A restatement. |
| Corollary 1 — unconditional coefficient bound | `cor:unconditional` | `SSP.MainRevised.unconditional_bound_of_transfer` | **Conditional**: assumes `KFSTransfer`; the component bound is derived, but a full `(A,b)` coefficient formalization is still missing. |
| Corollary 2 — sharp family | `cor:sharp` | `SSP.MainRevised.sharp_two_stage_ssp`, `SSP.MainRevised.sharp_two_stage_componentBound` | **Partial**: only two stages and transformed order identities; not the full all-stage SSP coefficient equality. |
| Theorem 3 — alternate SSP bound | `thm:alt` | `SSP.MainRevised.ssp_bound_of_invMat` | Proved; the same inverse-matrix bound as Theorem 2. |
| Theorem 4 — Aldous–Shepp least variability | `thm:AldousShepp` | `SSP.MainRevised.aldous_shepp` | Proved for concrete transient initial laws with at most `s` states, including an atom at zero. |
| Theorem 5 — Osogami least-r-value inequality | `thm:OsogamiHarcholBalter` | `SSP.MainRevised.osogami_harchol_balter` | Proved by the stronger cyclic theorem, including at most `s` states and an atom at zero. |
| Theorem 6 — acyclic all-k hierarchy | `thm:acyclic-hierarchy` | `SSP.MainRevised.acyclic_hierarchy_ratio`, `SSP.MainRevised.acyclic_hierarchy` | Proved in triangular uniformized-density form, including positive-moment ratios, at most `s` states, and an atom at zero; the division-free form also covers zero moments. |
| Theorem 7 — cyclic k=2 hierarchy | `thm:cyclic-hierarchy` | `SSP.MainRevised.cyclic_hierarchy` | Proved in ratio form for concrete transient initial laws with at most `s` states, including an atom at zero. |
| Lemma 6 — algebraic inequality | `lem:alg` | `SSP.MainRevised.algebraic_inequality` | Proved, including `w=0` and `β=0`; Lean division by zero gives the stated convention. |
| Theorem 8 — third-order SSP bound | `thm:SSPboundP3` | `SSP.MainRevised.order3_bound_of_invMat` | Proved directly from inverse SSP conditions and transformed order-three identities. |
| Theorem 9 — algebraic-stability order barrier | `thm:barrier` | `SSP.MainRevised.barrier_unsorted` | Proved, including a permutation to sort stages; no sorted-stage hypothesis. |
| Lemma 7 — partial sums | `lem:partialsums` | `SSP.MainRevised.partial_sums_strict` | Proved, including both the quantitative upper bound and its strict comparison with `1/3`. |

The general cyclic all-k conjecture is not a numbered theorem in this index:
the revised paper disproves it using six states at k = 71. Legacy A-stability
and mixture declarations above are retained for compatibility and do not add
numbered results to the current paper.
-/
