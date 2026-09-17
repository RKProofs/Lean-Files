import Mathlib

/-!
# The algebraic-stability order barrier (paper Section 4), formalized

This file machine-verifies the B-stability/algebraic-stability barrier of the paper
*A stability order barrier and SSP bound for Runge–Kutta methods with non-negative
coefficients* in a **generalized and corrected** form:

* `partial_sum_lemma` — the paper's Lemma 6, with the hypothesis `0 ≤ cᵢ ≤ 1` REMOVED
  (the review found it is never used; only monotonicity of `c` is needed).
* `barrier_bound` — the quantitative core: any nonnegative method with the order-2
  quadrature conditions and PSD algebraic-stability matrix has
  `bᵀc² ≤ 1/3 − (Σᵢ bᵢ³)/12`.
  The hypothesis `A·e = c` is weakened to row sums `≤ c` (`hrow`), which is what makes
  the paper's aggregation argument (Section 4.2) close correctly even when zero-weight
  classes are discarded.
* `quantitative_barrier` — NEW result suggested by the review:
  `bᵀc² ≤ 1/3 − 1/(12 s²)`.
* `no_order3_algebraically_stable` — the paper's Theorem 5 (generalized): the order-3
  quadrature condition `bᵀc² = 1/3` is impossible.  Note `bᵀAc = 1/6` is NOT needed.

Stages are indexed by `0, …, s−1` (sums over `Finset.range s`); the sorted-abscissas
hypothesis `hc` makes explicit the WLOG (stage permutation) that the paper leaves
implicit.  The PSD hypothesis is stated directly as nonnegativity of the quadratic
form of `M = diag(b)·A + Aᵀ·diag(b) − b·bᵀ`, entrywise `Mᵢⱼ = bᵢaᵢⱼ + bⱼaⱼᵢ − bᵢbⱼ`.
-/

open Finset

namespace SSP

/-! ## Partial-sum machinery -/

/-- `psum b k = σ_k`, the k-th partial sum of the weights. -/
noncomputable def psum (b : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range k, b i

/-- `mid b i = m_i`, the midpoint `(σ_i + σ_{i+1})/2`. -/
noncomputable def mid (b : ℕ → ℝ) (i : ℕ) : ℝ := (psum b i + psum b (i + 1)) / 2

lemma psum_succ (b : ℕ → ℝ) (k : ℕ) : psum b (k + 1) = psum b k + b k :=
  sum_range_succ b k

lemma psum_mono (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) {k l : ℕ} (h : k ≤ l) :
    psum b k ≤ psum b l :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h) fun i _ _ => hb i

lemma mid_mono (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) {k l : ℕ} (h : k ≤ l) :
    mid b k ≤ mid b l := by
  unfold mid
  have h1 := psum_mono b hb h
  have h2 := psum_mono b hb (Nat.succ_le_succ h)
  linarith

/-- Telescoping identity: `Σ_{i<n} bᵢ mᵢ² = σ_n³/3 − (Σ_{i<n} bᵢ³)/12`. -/
lemma sum_b_mid_sq (b : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, b i * (mid b i) ^ 2
      = (psum b n) ^ 3 / 3 - (∑ i ∈ range n, (b i) ^ 3) / 12 := by
  induction n with
  | zero => simp [psum]
  | succ k ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    have h : psum b (k + 1) = psum b k + b k := psum_succ b k
    unfold mid
    rw [h]
    ring

/-! ## The Abel/summation-by-parts bound -/

section AbelBound

variable (b c : ℕ → ℝ) (s : ℕ)

/-- `δ_k = ρ_k − σ_k²/2`. -/
noncomputable def delta (b c : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ i ∈ range k, b i * c i) - (psum b k) ^ 2 / 2

lemma delta_zero (b c : ℕ → ℝ) : delta b c 0 = 0 := by simp [delta, psum]

/-- The increment identity `δ_{k+1} − δ_k = b_k (c_k − m_k)`. -/
lemma delta_succ (b c : ℕ → ℝ) (k : ℕ) :
    delta b c (k + 1) = delta b c k + b k * (c k - mid b k) := by
  unfold delta mid
  rw [sum_range_succ, psum_succ]
  ring

/-- Summation-by-parts invariant: for `k < s`,
`Σ_{i<k} bᵢ(cᵢ−mᵢ)(cᵢ+mᵢ) ≤ δ_k (c_k + m_k)`. -/
lemma abel_invariant (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i j, i ≤ j → j < s → c i ≤ c j)
    (hδ : ∀ k ≤ s, 0 ≤ delta b c k) :
    ∀ k, k < s →
      ∑ i ∈ range k, b i * (c i - mid b i) * (c i + mid b i)
        ≤ delta b c k * (c k + mid b k) := by
  intro k
  induction k with
  | zero => intro _; simp [delta_zero]
  | succ k ih =>
    intro hks
    have hk_lt : k < s := Nat.lt_of_succ_lt hks
    have step := ih hk_lt
    rw [sum_range_succ, delta_succ]
    have hq : c k + mid b k ≤ c (k + 1) + mid b (k + 1) := by
      have h1 : c k ≤ c (k + 1) := hc k (k + 1) (Nat.le_succ k) hks
      have h2 : mid b k ≤ mid b (k + 1) := mid_mono b hb (Nat.le_succ k)
      linarith
    have hδk1 : 0 ≤ delta b c (k + 1) := hδ (k + 1) (Nat.le_of_lt hks)
    -- Σ_{i<k+1} ≤ δ_k q_k + b_k(c_k−m_k) q_k = δ_{k+1} q_k ≤ δ_{k+1} q_{k+1}
    have key : delta b c k * (c k + mid b k)
        + b k * (c k - mid b k) * (c k + mid b k)
        = delta b c (k + 1) * (c k + mid b k) := by
      rw [delta_succ]; ring
    calc ∑ i ∈ range k, b i * (c i - mid b i) * (c i + mid b i)
          + b k * (c k - mid b k) * (c k + mid b k)
        ≤ delta b c k * (c k + mid b k)
          + b k * (c k - mid b k) * (c k + mid b k) := by linarith
      _ = delta b c (k + 1) * (c k + mid b k) := key
      _ ≤ delta b c (k + 1) * (c (k + 1) + mid b (k + 1)) := by
          rw [delta_succ] at hδk1 ⊢
          exact mul_le_mul_of_nonneg_left hq hδk1
      _ = (delta b c k + b k * (c k - mid b k)) * (c (k + 1) + mid b (k + 1)) := by
          rw [delta_succ]

end AbelBound

/-! ## The main lemma (paper Lemma 6, generalized: no `c ∈ [0,1]` hypothesis) -/

/-- **Paper Lemma 6, generalized.**  If `b ≥ 0`, `c` is nondecreasing on the stage
range, `Σ b = 1`, `Σ b c = 1/2`, and the prefix condition `σ_k²/2 ≤ ρ_k` holds for
all `k ≤ s`, then `Σ b c² ≤ 1/3 − (Σ b³)/12`.
(The paper additionally assumes `0 ≤ cᵢ ≤ 1`; the review found this is never used.) -/
theorem partial_sum_lemma (b c : ℕ → ℝ) (s : ℕ)
    (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i j, i ≤ j → j < s → c i ≤ c j)
    (hsum : ∑ i ∈ range s, b i = 1)
    (hmean : ∑ i ∈ range s, b i * c i = 1 / 2)
    (hδ : ∀ k ≤ s, (psum b k) ^ 2 / 2 ≤ ∑ i ∈ range k, b i * c i) :
    ∑ i ∈ range s, b i * (c i) ^ 2
      ≤ 1 / 3 - (∑ i ∈ range s, (b i) ^ 3) / 12 := by
  have hδ' : ∀ k ≤ s, 0 ≤ delta b c k := by
    intro k hk; have := hδ k hk; unfold delta; linarith
  -- δ_s = 0
  have hδs : delta b c s = 0 := by
    unfold delta psum
    rw [hmean, hsum]
    norm_num
  -- the summation-by-parts bound at k = s
  have habel : ∑ i ∈ range s, b i * (c i - mid b i) * (c i + mid b i) ≤ 0 := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs; simp
    · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
      have inv := abel_invariant b c (t + 1) hb hc hδ' t (Nat.lt_succ_self t)
      rw [sum_range_succ]
      have key : delta b c t * (c t + mid b t)
          + b t * (c t - mid b t) * (c t + mid b t)
          = delta b c (t + 1) * (c t + mid b t) := by
        rw [delta_succ]; ring
      have : ∑ i ∈ range t, b i * (c i - mid b i) * (c i + mid b i)
          + b t * (c t - mid b t) * (c t + mid b t)
          ≤ delta b c (t + 1) * (c t + mid b t) := by
        rw [← key]; linarith
      rw [hδs] at this
      linarith
  -- expand (c−m)(c+m) = c² − m²
  have hexp : ∑ i ∈ range s, b i * (c i - mid b i) * (c i + mid b i)
      = ∑ i ∈ range s, b i * (c i) ^ 2 - ∑ i ∈ range s, b i * (mid b i) ^ 2 := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  have hcm : ∑ i ∈ range s, b i * (c i) ^ 2 ≤ ∑ i ∈ range s, b i * (mid b i) ^ 2 := by
    rw [hexp] at habel; linarith
  -- compute Σ b m² by telescoping
  have htel := sum_b_mid_sq b s
  unfold psum at htel
  rw [hsum] at htel
  rw [htel] at hcm
  linarith [hcm]

/-! ## The barrier theorems -/

section Barrier

variable {s : ℕ} (A : ℕ → ℕ → ℝ) (b c : ℕ → ℝ)

/-- Prefix-indicator sum reduction. -/
lemma sum_mul_indicator {s k : ℕ} (hk : k ≤ s) (f : ℕ → ℝ) :
    ∑ i ∈ range s, f i * (if i < k then (1 : ℝ) else 0) = ∑ i ∈ range k, f i := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_ite, sum_const_zero, add_zero]
  apply sum_congr _ fun _ _ => rfl
  ext i
  simp only [mem_filter, mem_range]
  omega

/-- **Quantitative core of the barrier (paper Theorem 5, generalized).**
Hypotheses:
* `A ≥ 0`, `b ≥ 0` entrywise, abscissas sorted (`hc`, WLOG by stage permutation);
* row sums of `A` bounded by `c` (`hrow`) — generalizes `A·e = c` and is the form
  needed for the confluent/aggregated case of paper §4.2;
* quadrature conditions `Σb = 1`, `bᵀc = 1/2`;
* PSD algebraic-stability matrix (`hM`, as a quadratic form).

Conclusion: `bᵀc² ≤ 1/3 − (Σ b³)/12`.  Note: `bᵀAc = 1/6` is NOT assumed. -/
theorem barrier_bound
    (hA : ∀ i j, 0 ≤ A i j) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i j, i ≤ j → j < s → c i ≤ c j)
    (hrow : ∀ i < s, ∑ j ∈ range s, A i j ≤ c i)
    (h1 : ∑ i ∈ range s, b i = 1)
    (h2 : ∑ i ∈ range s, b i * c i = 1 / 2)
    (hM : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range s, ∑ j ∈ range s,
          (b i * A i j + b j * A j i - b i * b j) * (x i * x j)) :
    ∑ i ∈ range s, b i * (c i) ^ 2
      ≤ 1 / 3 - (∑ i ∈ range s, (b i) ^ 3) / 12 := by
  apply partial_sum_lemma b c s hb hc h1 h2
  -- derive the prefix condition σ_k²/2 ≤ ρ_k from PSD-ness via the 0-1 indicator
  intro k hk
  set x : ℕ → ℝ := fun i => if i < k then (1 : ℝ) else 0 with hx
  have hqf := hM x
  -- reduce the quadratic form to the k×k prefix block
  have hred : ∑ i ∈ range s, ∑ j ∈ range s,
      (b i * A i j + b j * A j i - b i * b j) * (x i * x j)
      = ∑ i ∈ range k, ∑ j ∈ range k, (b i * A i j + b j * A j i - b i * b j) := by
    have inner : ∀ i, ∑ j ∈ range s,
        (b i * A i j + b j * A j i - b i * b j) * (x i * x j)
        = (∑ j ∈ range k, (b i * A i j + b j * A j i - b i * b j)) * x i := by
      intro i
      rw [← sum_mul_indicator hk (fun j => b i * A i j + b j * A j i - b i * b j),
        sum_mul]
      exact sum_congr rfl fun j _ => by simp only [hx]; ring
    calc ∑ i ∈ range s, ∑ j ∈ range s,
          (b i * A i j + b j * A j i - b i * b j) * (x i * x j)
        = ∑ i ∈ range s,
            (∑ j ∈ range k, (b i * A i j + b j * A j i - b i * b j)) * x i :=
          sum_congr rfl fun i _ => inner i
      _ = ∑ i ∈ range k, ∑ j ∈ range k, (b i * A i j + b j * A j i - b i * b j) := by
          rw [← sum_mul_indicator hk
            (fun i => ∑ j ∈ range k, (b i * A i j + b j * A j i - b i * b j))]
  rw [hred] at hqf
  -- expand the block sum: 2·Σ_{i,j<k} bᵢaᵢⱼ − σ_k²
  have hexpand : ∑ i ∈ range k, ∑ j ∈ range k, (b i * A i j + b j * A j i - b i * b j)
      = 2 * (∑ i ∈ range k, ∑ j ∈ range k, b i * A i j) - (psum b k) ^ 2 := by
    have e1 : ∑ i ∈ range k, ∑ j ∈ range k, (b i * A i j + b j * A j i - b i * b j)
        = (∑ i ∈ range k, ∑ j ∈ range k, b i * A i j)
          + (∑ i ∈ range k, ∑ j ∈ range k, b j * A j i)
          - (∑ i ∈ range k, ∑ j ∈ range k, b i * b j) := by
      simp only [← sum_add_distrib, ← sum_sub_distrib]
    have e2 : ∑ i ∈ range k, ∑ j ∈ range k, b j * A j i
        = ∑ i ∈ range k, ∑ j ∈ range k, b i * A i j := sum_comm
    have e3 : ∑ i ∈ range k, ∑ j ∈ range k, b i * b j = (psum b k) ^ 2 := by
      rw [← sum_mul_sum]
      unfold psum
      ring
    rw [e1, e2, e3]
    ring
  rw [hexpand] at hqf
  -- Σ_{i,j<k} bᵢaᵢⱼ ≤ ρ_k
  have hS : ∑ i ∈ range k, ∑ j ∈ range k, b i * A i j
      ≤ ∑ i ∈ range k, b i * c i := by
    apply sum_le_sum
    intro i hi
    have his : i < s := lt_of_lt_of_le (mem_range.1 hi) hk
    have hAsub : ∑ j ∈ range k, A i j ≤ ∑ j ∈ range s, A i j :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hk) fun j _ _ => hA i j
    have : ∑ j ∈ range k, A i j ≤ c i := le_trans hAsub (hrow i his)
    calc ∑ j ∈ range k, b i * A i j = b i * ∑ j ∈ range k, A i j := by
          rw [mul_sum]
      _ ≤ b i * c i := mul_le_mul_of_nonneg_left this (hb i)
  linarith

/-- **NEW (review E4): quantitative order barrier.**  Every method with nonnegative
coefficients, the order-2 quadrature conditions and PSD algebraic-stability matrix
satisfies `bᵀc² ≤ 1/3 − 1/(12 s²)`: the defect from third order is at least
`1/(12 s²)`. -/
theorem quantitative_barrier
    (hs : 0 < s)
    (hA : ∀ i j, 0 ≤ A i j) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i j, i ≤ j → j < s → c i ≤ c j)
    (hrow : ∀ i < s, ∑ j ∈ range s, A i j ≤ c i)
    (h1 : ∑ i ∈ range s, b i = 1)
    (h2 : ∑ i ∈ range s, b i * c i = 1 / 2)
    (hM : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range s, ∑ j ∈ range s,
          (b i * A i j + b j * A j i - b i * b j) * (x i * x j)) :
    ∑ i ∈ range s, b i * (c i) ^ 2 ≤ 1 / 3 - 1 / (12 * (s : ℝ) ^ 2) := by
  have hbar := barrier_bound A b c hA hb hc hrow h1 h2 hM
  -- power-mean: Σ b³ ≥ (Σ b)³ / s² = 1/s²
  have hpm : ((∑ i ∈ range s, b i) ^ 3) / ((range s).card : ℝ) ^ 2
      ≤ ∑ i ∈ range s, (b i) ^ 3 := by
    have := pow_sum_div_card_le_sum_pow (f := b) (n := 2)
      (fun i _ => hb i) (s := range s)
    simpa using this
  rw [h1, card_range] at hpm
  have hs' : (0 : ℝ) < (s : ℝ) ^ 2 := by positivity
  have : 1 / (s : ℝ) ^ 2 ≤ ∑ i ∈ range s, (b i) ^ 3 := by
    calc (1 : ℝ) / (s : ℝ) ^ 2 = 1 ^ 3 / (s : ℝ) ^ 2 := by norm_num
    _ ≤ ∑ i ∈ range s, (b i) ^ 3 := hpm
  have h12 : (0:ℝ) < 12 * (s:ℝ)^2 := by positivity
  calc ∑ i ∈ range s, b i * (c i) ^ 2
      ≤ 1 / 3 - (∑ i ∈ range s, (b i) ^ 3) / 12 := hbar
    _ ≤ 1 / 3 - (1 / (s : ℝ) ^ 2) / 12 := by linarith
    _ = 1 / 3 - 1 / (12 * (s : ℝ) ^ 2) := by field_simp

/-- **Paper Theorem 5, generalized.**  There is no Runge–Kutta method with
`A ≥ 0`, `b ≥ 0`, sorted abscissas (WLOG), row sums of `A` at most `c`, and the
order-3 quadrature conditions `Σb = 1`, `bᵀc = 1/2`, `bᵀc² = 1/3`, whose
algebraic-stability matrix `M = diag(b)A + Aᵀdiag(b) − bbᵀ` is positive semidefinite.
(Note: the condition `bᵀAc = 1/6` used in the paper's proof is not needed.) -/
theorem no_order3_algebraically_stable
    (hA : ∀ i j, 0 ≤ A i j) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i j, i ≤ j → j < s → c i ≤ c j)
    (hrow : ∀ i < s, ∑ j ∈ range s, A i j ≤ c i)
    (h1 : ∑ i ∈ range s, b i = 1)
    (h2 : ∑ i ∈ range s, b i * c i = 1 / 2)
    (h3 : ∑ i ∈ range s, b i * (c i) ^ 2 = 1 / 3)
    (hM : ∀ x : ℕ → ℝ, 0 ≤ ∑ i ∈ range s, ∑ j ∈ range s,
          (b i * A i j + b j * A j i - b i * b j) * (x i * x j)) :
    False := by
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at h1
    · exact h
  have hq := quantitative_barrier A b c hs hA hb hc hrow h1 h2 hM
  rw [h3] at hq
  have : (0 : ℝ) < 1 / (12 * (s : ℝ) ^ 2) := by positivity
  linarith

end Barrier

end SSP
