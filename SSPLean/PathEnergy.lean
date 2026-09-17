import Mathlib

/-!
# The per-path level-crossing energy bound

This module proves the deepest analytic ingredient of the weighted-paths proof of the
q-sequence bound (`q_sequence_bound_two_proofs.tex`, first proof): the level-crossing
Cauchy–Schwarz estimate.

Given a finite real sequence `L : Fin (n+1) → ℝ` starting at `L 0 = A ≥ 0`, with all values
in `[0, A]` and drawn from a finite "grid" `V` of at most `s` reals containing `0` and `A`,
the total squared variation down to the floor `0`,
`Σ_{r} (L (r+1) − L r)² + (L last)²`, is at least `A² / s`.

This is the finite (per-path) core of the Aldous–Shepp least-variability content: the walk
from level `A` to level `0` must cross each of the ≤ `s` grid gaps, and Cauchy–Schwarz over
the gaps yields the `1/s` factor.  It is used in `QSequencePaths.lean` to bound the energy of
each weighted path.
-/


open Finset

namespace SSP

/-- Super-additivity of squares for nonnegative reals: `∑ aᵢ² ≤ (∑ aᵢ)²`. -/
lemma sum_sq_le_sq_sum {ι : Type*} (t : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ t, 0 ≤ a i) :
    ∑ i ∈ t, (a i) ^ 2 ≤ (∑ i ∈ t, a i) ^ 2 := by
  have hsum : ∀ i ∈ t, (a i) ^ 2 ≤ a i * ∑ j ∈ t, a j := by
    intro i hi
    rw [sq]
    apply mul_le_mul_of_nonneg_left _ (ha i hi)
    exact Finset.single_le_sum ha hi
  calc ∑ i ∈ t, (a i) ^ 2 ≤ ∑ i ∈ t, a i * (∑ j ∈ t, a j) := Finset.sum_le_sum hsum
    _ = (∑ i ∈ t, a i) * (∑ j ∈ t, a j) := by rw [← Finset.sum_mul]
    _ = (∑ i ∈ t, a i) ^ 2 := by rw [sq]

/-- Telescoping over an interval `[m, n)`. -/
lemma sum_Ico_telescope (v : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, (v (i + 1) - v i) = v n - v m := by
  rw [Finset.sum_Ico_eq_sub _ hmn, Finset.sum_range_sub v n, Finset.sum_range_sub v m]
  ring

/-- Width bound: for a monotone `v`, the total width of the gaps `[v i, v (i+1)]` that are
contained in `[a, b]` is at most `b - a`. -/
lemma crossed_width_le (v : ℕ → ℝ) (hv : Monotone v) (K : ℕ) (a b : ℝ) :
    ∑ i ∈ (Finset.range K).filter (fun i => a ≤ v i ∧ v (i + 1) ≤ b), (v (i + 1) - v i)
      ≤ max (b - a) 0 := by
  set S : Finset ℕ := (Finset.range K).filter (fun i => a ≤ v i ∧ v (i + 1) ≤ b) with hS
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe, Finset.sum_empty]; exact le_max_right _ _
  · -- lo = min index, hi = max index; S ⊆ Ico lo (hi+1)
    set lo := S.min' hSne with hlo
    set hi := S.max' hSne with hhi
    have hlomem : lo ∈ S := S.min'_mem hSne
    have hhimem : hi ∈ S := S.max'_mem hSne
    have hsub : S ⊆ Finset.Ico lo (hi + 1) := by
      intro i hi'
      rw [Finset.mem_Ico]
      exact ⟨S.min'_le i hi', Nat.lt_succ_of_le (S.le_max' i hi')⟩
    have hlohi : lo ≤ hi := S.min'_le hi hhimem
    have hnn : ∀ i ∈ Finset.Ico lo (hi + 1), (0:ℝ) ≤ v (i + 1) - v i := by
      intro i _; have := hv (Nat.le_succ i); linarith
    calc ∑ i ∈ S, (v (i + 1) - v i)
        ≤ ∑ i ∈ Finset.Ico lo (hi + 1), (v (i + 1) - v i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi' _ => hnn i hi')
      _ = v (hi + 1) - v lo := sum_Ico_telescope v lo (hi + 1) (by omega)
      _ ≤ b - a := by
          have h1 : v (hi + 1) ≤ b := (Finset.mem_filter.mp hhimem).2.2
          have h2 : a ≤ v lo := (Finset.mem_filter.mp hlomem).2.1
          linarith
      _ ≤ max (b - a) 0 := le_max_left _ _

/-- **Per-path crossing energy bound.**  Let `L : Fin (n+1) → ℝ` be a real sequence with
`L 0 = A`, `0 ≤ A`, all values `L r ∈ [0, A]` lying in a set `V ⊆ ℝ` of size `≤ s` that also
contains `0` and `A`.  Then the total squared variation down to the floor `0`,
`Σ_{r : Fin n} (L r.succ − L r.castSucc)² + (L (Fin.last n))²`, is at least `A² / s`.

(The hypothesis `hV` says every visited level is one of at most `s` grid values; in the
application these are the `≤ s` distinct entries of `x`.) -/
lemma path_energy_ge
    (s n : ℕ) (hs : 0 < s) (A : ℝ) (hA : 0 ≤ A)
    (L : Fin (n + 1) → ℝ) (hL0 : L 0 = A)
    (V : Finset ℝ) (hVcard : V.card ≤ s + 1) (h0V : (0 : ℝ) ∈ V) (hAV : A ∈ V)
    (hLrange : ∀ r, 0 ≤ L r ∧ L r ≤ A) (hLV : ∀ r, L r ∈ V) :
    A ^ 2 / s
      ≤ (∑ r : Fin n, (L r.succ - L r.castSucc) ^ 2) + (L (Fin.last n)) ^ 2 := by
  -- The extended sequence `M : Fin (n+2) → ℝ`, appending a final `0` (the floor).
  set M : Fin (n + 2) → ℝ := Fin.snoc L 0 with hM
  -- Energy equals the sum of squared consecutive differences of `M`.
  have henergy :
      (∑ r : Fin n, (L r.succ - L r.castSucc) ^ 2) + (L (Fin.last n)) ^ 2
        = ∑ r : Fin (n + 1), (M r.succ - M r.castSucc) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · -- the initial `n` differences agree with those of `L`
      apply Finset.sum_congr rfl
      intro r _
      have h1 : M r.castSucc.castSucc = L r.castSucc := by
        rw [hM, Fin.snoc_castSucc]
      have h2 : M r.castSucc.succ = L r.succ := by
        rw [hM, Fin.succ_castSucc, Fin.snoc_castSucc]
      rw [h1, h2]
    · -- the last difference is `0 - L (last)`, squared
      have h1 : M (Fin.last n).castSucc = L (Fin.last n) := by
        rw [hM, Fin.snoc_castSucc]
      have h2 : M (Fin.last n).succ = 0 := by
        rw [hM, Fin.succ_last, Fin.snoc_last]
      rw [h1, h2]
      ring
  rw [henergy]
  -- Dispose of the `A = 0` case.
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · -- `A = 0`: RHS is a sum of squares ≥ 0.
    rw [← hA0]
    simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true, zero_div]
    positivity
  -- Now `0 < A`.
  -- Basic facts about `M`.
  have hMmem : ∀ r, M r ∈ V ∧ 0 ≤ M r ∧ M r ≤ A := by
    intro r
    refine Fin.lastCases ?_ ?_ r
    · rw [hM, Fin.snoc_last]; exact ⟨h0V, le_refl 0, hA⟩
    · intro i
      rw [hM, Fin.snoc_castSucc]
      exact ⟨hLV i, (hLrange i).1, (hLrange i).2⟩
  -- The grid `W = V ∩ [0,A]`.
  set W : Finset ℝ := V.filter (fun t => 0 ≤ t ∧ t ≤ A) with hW
  have hWcard : W.card ≤ s + 1 := le_trans (Finset.card_filter_le _ _) hVcard
  have h0W : (0 : ℝ) ∈ W := by rw [hW, Finset.mem_filter]; exact ⟨h0V, le_refl 0, hA⟩
  have hAW : A ∈ W := by rw [hW, Finset.mem_filter]; exact ⟨hAV, hA, le_refl A⟩
  have hMW : ∀ r, M r ∈ W := by
    intro r
    rw [hW, Finset.mem_filter]
    exact ⟨(hMmem r).1, (hMmem r).2.1, (hMmem r).2.2⟩
  -- Sorted grid via `orderEmbOfFin`.
  set K : ℕ := W.card with hKdef
  have hK : 0 < K := Finset.card_pos.mpr ⟨0, h0W⟩
  -- Since `0 < A`, both `0` and `A` lie in `W` and are distinct, so `2 ≤ K`.
  have hK2 : 2 ≤ K := by
    have hsub : ({0, A} : Finset ℝ) ⊆ W := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h0W
      · exact hAW
    have hcard2 : ({0, A} : Finset ℝ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [ne_of_lt hApos]), Finset.card_singleton]
    calc 2 = ({0, A} : Finset ℝ).card := hcard2.symm
      _ ≤ W.card := Finset.card_le_card hsub
  set t : Fin K ↪o ℝ := W.orderEmbOfFin rfl with ht
  have ht_mem : ∀ i, t i ∈ W := fun i => W.orderEmbOfFin_mem rfl i
  have htmono : StrictMono t := t.strictMono
  -- endpoints
  have htmin : t ⟨0, hK⟩ = 0 := by
    rw [ht, Finset.orderEmbOfFin_zero rfl hK]
    apply le_antisymm
    · exact W.min'_le 0 h0W
    · exact Finset.le_min' _ _ _ (fun y hy => by
        rw [hW, Finset.mem_filter] at hy; exact hy.2.1)
  have htmax : t ⟨K - 1, Nat.sub_lt hK Nat.one_pos⟩ = A := by
    rw [ht, Finset.orderEmbOfFin_last rfl hK]
    apply le_antisymm
    · exact Finset.max'_le _ _ _ (fun y hy => by
        rw [hW, Finset.mem_filter] at hy; exact hy.2.2)
    · exact W.le_max' A hAW
  -- Gap function: g i = t i - (predecessor), with g 0 = 0.
  set g : Fin K → ℝ := fun i =>
    if h : (i : ℕ) = 0 then 0 else t i - t ⟨i - 1, by omega⟩ with hg
  -- g is nonnegative
  have hgnn : ∀ i, 0 ≤ g i := by
    intro i
    simp only [hg]
    split
    · exact le_refl 0
    · rename_i h
      have hlt : (⟨(i:ℕ) - 1, by omega⟩ : Fin K) < i := by
        rw [Fin.lt_def]; simp only; omega
      have := htmono hlt
      linarith
  -- Telescoping: ∑ g i = A.
  -- Auxiliary shifted grid `v : ℕ → ℝ`, `v 0 = 0`, `v (j+1) = t j`.
  set v : ℕ → ℝ := fun j => if hj : j = 0 then 0 else
      if hjK : j - 1 < K then t ⟨j - 1, hjK⟩ else A with hv
  have hgv : ∀ i : Fin K, g i = v (i + 1) - v (i : ℕ) := by
    intro i
    have hvsucc : v ((i:ℕ) + 1) = t i := by
      simp only [hv]
      rw [dif_neg (by omega : ¬ ((i:ℕ)+1 = 0)), Nat.add_sub_cancel, dif_pos i.2]
    by_cases hi0 : (i : ℕ) = 0
    · have hti0 : t i = 0 := by
        rw [show i = ⟨0, hK⟩ from by ext; exact hi0]; exact htmin
      have hg0 : g i = 0 := by simp only [hg, hi0, dif_pos]
      have hvi : v (i : ℕ) = 0 := by rw [hi0]; simp only [hv, dif_pos]
      rw [hg0, hvsucc, hvi, hti0]; ring
    · have hib : (i:ℕ) < K := i.2
      have hpred : (i:ℕ) - 1 < K := by omega
      have hgi : g i = t i - t ⟨(i:ℕ) - 1, hpred⟩ := by
        simp only [hg]; rw [dif_neg hi0]
      have hvi : v (i : ℕ) = t ⟨(i:ℕ) - 1, hpred⟩ := by
        simp only [hv]; rw [dif_neg hi0, dif_pos hpred]
      rw [hgi, hvsucc, hvi]
  have hgsum : ∑ i : Fin K, g i = A := by
    have step1 : ∑ i : Fin K, g i = ∑ i : Fin K, (v (↑i + 1) - v ↑i) :=
      Finset.sum_congr rfl (fun i _ => hgv i)
    rw [step1, Fin.sum_univ_eq_sum_range (fun j => v (j + 1) - v j) K,
      Finset.sum_range_sub v K]
    -- v K = A, v 0 = 0
    have hvK : v K = A := by
      simp only [hv]
      rw [dif_neg (by omega : ¬ K = 0)]
      have hlt : K - 1 < K := by omega
      rw [dif_pos hlt]
      exact htmax
    have hv0 : v 0 = 0 := by simp only [hv, dif_pos]
    rw [hvK, hv0, sub_zero]
  -- `v` as a value function on `ℕ`: `v j = t (j-1)` for `1 ≤ j ≤ K`, `v 0 = 0`, else `A`.
  have hv_eq : ∀ j (hj : j < K), v (j + 1) = t ⟨j, hj⟩ := by
    intro j hj
    simp only [hv]
    rw [dif_neg (by omega : ¬ (j+1 = 0)), Nat.add_sub_cancel, dif_pos hj]
  have hv_pred : ∀ j (hj0 : 0 < j) (hj : j - 1 < K), v j = t ⟨j - 1, hj⟩ := by
    intro j hj0 hj
    have := hv_eq (j - 1) hj
    rwa [Nat.sub_add_cancel hj0] at this
  have hv0 : v 0 = 0 := by simp only [hv, dif_pos]
  have hvK : v K = A := by
    rcases Nat.eq_zero_or_pos K with h | h
    · omega
    · have := hv_eq (K-1) (by omega); rw [Nat.sub_add_cancel h] at this
      rw [this]; exact htmax
  -- `v j = A` for `j ≥ K`.
  have hvA : ∀ j, K ≤ j → v j = A := by
    intro j hj
    rcases Nat.eq_or_lt_of_le hj with h | h
    · rw [← h]; exact hvK
    · simp only [hv]
      rw [dif_neg (by omega : ¬ j = 0), dif_neg (by omega : ¬ (j - 1 < K))]
  -- `v` is monotone (nondecreasing) on all of `ℕ`.
  have hvmono : Monotone v := by
    have hstep : ∀ j, v j ≤ v (j + 1) := by
      intro j
      by_cases hjK : j + 1 ≤ K
      · rw [hv_eq j (by omega)]
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · subst hj0; rw [hv0, htmin]
        · rw [hv_pred j hj0 (by omega)]
          apply le_of_lt; apply htmono
          rw [Fin.lt_def]; simp only; omega
      · rw [hvA j (by omega), hvA (j+1) (by omega)]
    exact monotone_nat_of_le_succ hstep
  -- No grid point lies strictly inside a gap: if `w ∈ W` and `v i < w` then `v (i+1) ≤ w`.
  have hno_interior : ∀ (i : ℕ) (hi : i < K) (w : ℝ), w ∈ W → v i < w → v (i + 1) ≤ w := by
    intro i hi w hwW hlt
    rw [hv_eq i hi]
    -- w ∈ W = range t, so w = t j for some j
    have : w ∈ Set.range t := by rw [ht, Finset.range_orderEmbOfFin]; exact hwW
    obtain ⟨j, rfl⟩ := this
    -- v i < t j  and want  t i ≤ t j, i.e. i ≤ j
    by_contra hcon
    push Not at hcon
    -- t j < t i ⟹ j < i ⟹ t j ≤ t (i-1) = v i, contradicting v i < t j
    have hji : (j : ℕ) < i := by
      have hh : (j : Fin K) < ⟨i, hi⟩ := t.lt_iff_lt.mp hcon
      rw [Fin.lt_def] at hh; simpa using hh
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · omega
    · have hvi : v i = t ⟨i - 1, by omega⟩ := hv_pred i hi0 (by omega)
      rw [hvi] at hlt
      have hle : t j ≤ t ⟨i - 1, by omega⟩ := by
        apply t.le_iff_le.mpr
        rw [Fin.le_def]; simp only; omega
      linarith
  -- The dummy gap `g 0 = 0`, so the genuine gaps are those with index `≠ 0`.
  have hg0 : g (⟨0, hK⟩ : Fin K) = 0 := by
    simp only [hg, dif_pos]
  -- Sum over the `K - 1` genuine gaps equals the full sum (dropping `g 0 = 0`).
  have herase_sum : ∑ i ∈ (Finset.univ : Finset (Fin K)).erase ⟨0, hK⟩, g i = A := by
    rw [Finset.sum_erase (Finset.univ : Finset (Fin K)) hg0]
    exact hgsum
  have herase_sq : ∑ i ∈ (Finset.univ : Finset (Fin K)).erase ⟨0, hK⟩, (g i) ^ 2
      = ∑ i : Fin K, (g i) ^ 2 := by
    exact Finset.sum_erase (Finset.univ : Finset (Fin K))
      (by rw [hg0]; norm_num : (g (⟨0, hK⟩ : Fin K)) ^ 2 = 0)
  -- Cauchy–Schwarz over the `K - 1` genuine gaps: A² ≤ (K - 1) · ∑ g².
  have hCS : A ^ 2 ≤ ((K : ℝ) - 1) * ∑ i : Fin K, (g i) ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin K)).erase ⟨0, hK⟩) (f := g)
    rw [herase_sum, herase_sq] at hcs
    have hcard : ((Finset.univ : Finset (Fin K)).erase ⟨0, hK⟩).card = K - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    rw [hcard] at hcs
    have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ K)]; norm_num
    rwa [hcast] at hcs
  -- Crux: energy ≥ ∑ g².
  -- ℕ-indexed gap widths `G j = v (j+1) - v j`.
  set G : ℕ → ℝ := fun j => v (j + 1) - v j with hG
  have hGnn : ∀ j, 0 ≤ G j := fun j => by have := hvmono (Nat.le_succ j); simp only [hG]; linarith
  -- `∑_{i:Fin K} (g i)² = ∑_{j ∈ range K} (G j)²`.
  have hgG : ∑ i : Fin K, (g i) ^ 2 = ∑ j ∈ Finset.range K, (G j) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (G j) ^ 2) K]
    apply Finset.sum_congr rfl
    intro i _
    rw [hgv i, hG]
  -- Crossed set for a step with endpoints [a,b].
  set av : Fin (n + 1) → ℝ := fun r => min (M r.castSucc) (M r.succ) with hav
  set bv : Fin (n + 1) → ℝ := fun r => max (M r.castSucc) (M r.succ) with hbv
  set Cr : Fin (n + 1) → Finset ℕ := fun r =>
    (Finset.range K).filter (fun j => av r ≤ v j ∧ v (j + 1) ≤ bv r) with hCr
  -- (A) Per-step bound: ∑_{j ∈ Cr r} (G j)² ≤ (M r.succ - M r.castSucc)².
  have hstep : ∀ r : Fin (n + 1),
      ∑ j ∈ Cr r, (G j) ^ 2 ≤ (M r.succ - M r.castSucc) ^ 2 := by
    intro r
    have hab : av r ≤ bv r := min_le_max
    have hwidth : ∑ j ∈ Cr r, G j ≤ bv r - av r := by
      have := crossed_width_le v hvmono K (av r) (bv r)
      rw [max_eq_left (by linarith : (0:ℝ) ≤ bv r - av r)] at this
      exact this
    have hsum_nn : 0 ≤ ∑ j ∈ Cr r, G j := Finset.sum_nonneg (fun j _ => hGnn j)
    calc ∑ j ∈ Cr r, (G j) ^ 2 ≤ (∑ j ∈ Cr r, G j) ^ 2 :=
          sum_sq_le_sq_sum _ G (fun j _ => hGnn j)
      _ ≤ (bv r - av r) ^ 2 := by
          apply sq_le_sq'
          · linarith
          · exact hwidth
      _ = (M r.succ - M r.castSucc) ^ 2 := by
          have : (bv r - av r) ^ 2 = (M r.succ - M r.castSucc) ^ 2 := by
            simp only [hav, hbv]
            rcases le_total (M r.castSucc) (M r.succ) with h | h
            · rw [min_eq_left h, max_eq_right h]
            · rw [min_eq_right h, max_eq_left h]; ring
          exact this
  -- Auxiliary: `M` value facts.
  have hM0 : M 0 = A := by
    rw [hM, show (0 : Fin (n+2)) = (0 : Fin (n+1)).castSucc from rfl, Fin.snoc_castSucc, hL0]
  have hMlast : M (Fin.last (n + 1)) = 0 := by rw [hM, Fin.snoc_last]
  have hMnn : ∀ k, 0 ≤ M k := fun k => (hMmem k).2.1
  have hMleA : ∀ k, M k ≤ A := fun k => (hMmem k).2.2
  -- (B) Crossing: each gap `j < K` is crossed by at least one step.
  have hcross : ∀ j, j < K → ∃ r : Fin (n + 1), j ∈ Cr r := by
    intro j hjK
    -- j = 0 handled by the final step (min reaches 0); j ≥ 1 by discrete IVT.
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · -- gap 0: v 0 = 0, v 1 = t 0 = 0. Use r = last: M r.succ = 0.
      refine ⟨Fin.last n, ?_⟩
      rw [hCr, Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr hjK, ?_, ?_⟩
      · -- av (last n) ≤ v j = v 0 = 0
        subst hj0
        rw [hav, hv0]
        have : M (Fin.last n).succ = 0 := by rw [Fin.succ_last]; exact hMlast
        calc min (M (Fin.last n).castSucc) (M (Fin.last n).succ)
            ≤ M (Fin.last n).succ := min_le_right _ _
          _ = 0 := this
      · -- v (0+1) = v 1 = t 0 = 0 ≤ bv (last)
        subst hj0
        have hv1 : v (0 + 1) = 0 := by rw [hv_eq 0 hK, htmin]
        rw [hv1, hbv]
        exact le_trans (hMnn _) (le_max_left _ _)
    · -- gap j ≥ 1: v j = t (j-1) < t j = v (j+1); use discrete IVT with threshold τ.
      have hvj_lt : v j < v (j + 1) := by
        rw [hv_pred j hj0 (by omega), hv_eq j hjK]
        apply htmono; rw [Fin.lt_def]; simp only; omega
      -- `v (j+1) = t j ∈ W ⊆ [0, A]`, so `v (j+1) ≤ A`.
      have hvj1_le_A : v (j + 1) ≤ A := by
        rw [hv_eq j hjK]
        have : t ⟨j, hjK⟩ ∈ W := ht_mem _
        rw [hW, Finset.mem_filter] at this; exact this.2.2
      have hvj_nn : 0 ≤ v j := hvmono (Nat.zero_le j) |>.trans' (by rw [hv0])
      set τ : ℝ := (v j + v (j + 1)) / 2 with hτ
      have hτ_lo : v j < τ := by rw [hτ]; linarith
      have hτ_hi : τ < v (j + 1) := by rw [hτ]; linarith
      -- The set of indices where M > τ; contains 0, excludes last.
      set S : Finset (Fin (n + 2)) := Finset.univ.filter (fun k => τ < M k) with hSdef
      have h0S : (0 : Fin (n + 2)) ∈ S := by
        rw [hSdef, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [hM0]; linarith⟩
      have hSne : S.Nonempty := ⟨0, h0S⟩
      set k : Fin (n + 2) := S.max' hSne with hk
      have hkS : k ∈ S := S.max'_mem hSne
      have hMk : τ < M k := by rw [hSdef, Finset.mem_filter] at hkS; exact hkS.2
      -- k ≠ last, since M last = 0 < τ.
      have hk_ne_last : k ≠ Fin.last (n + 1) := by
        intro hcon
        rw [hcon, hMlast] at hMk
        linarith
      have hk_lt : (k : ℕ) < n + 1 := by
        have := Fin.val_lt_last hk_ne_last
        simpa using this
      -- The step `r` with `r.castSucc = k`.
      refine ⟨⟨(k : ℕ), hk_lt⟩, ?_⟩
      set r : Fin (n + 1) := ⟨(k : ℕ), hk_lt⟩ with hr
      have hrcast : r.castSucc = k := by
        rw [hr]; ext; simp [Fin.castSucc]
      have hrsucc_val : (r.succ : ℕ) = (k : ℕ) + 1 := by rw [hr]; simp
      -- M (r.succ) ≤ τ by maximality of k.
      have hMrsucc : M r.succ ≤ τ := by
        by_contra hcon
        push Not at hcon
        have hmem : r.succ ∈ S := by
          rw [hSdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hcon⟩
        have : r.succ ≤ k := S.le_max' _ hmem
        rw [Fin.le_def, hrsucc_val, hk] at this
        omega
      -- Now assemble the crossing.
      rw [hCr, Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr hjK, ?_, ?_⟩
      · -- av r ≤ v j : since M r.succ ≤ τ < v(j+1), and M r.succ ∈ W, get M r.succ ≤ v j.
        rw [hav]
        have hMrsucc_W : M r.succ ∈ W := hMW _
        have : M r.succ ≤ v j := by
          by_contra hcon
          push Not at hcon
          have := hno_interior j hjK (M r.succ) hMrsucc_W hcon
          linarith
        exact le_trans (min_le_right _ _) this
      · -- v (j+1) ≤ bv r : since M r.castSucc = M k > τ > v j, and M k ∈ W, get v(j+1) ≤ M k.
        simp only [hbv]
        rw [hrcast]
        have hMk_W : M k ∈ W := hMW _
        have : v (j + 1) ≤ M k := hno_interior j hjK (M k) hMk_W (lt_trans hτ_lo hMk)
        exact le_trans this (le_max_left _ _)
  -- Double counting.
  have hdc : ∑ j ∈ Finset.range K, (G j) ^ 2
      ≤ ∑ r : Fin (n + 1), ∑ j ∈ Cr r, (G j) ^ 2 := by
    -- Rewrite each inner sum over the fixed set `range K` via an indicator, then swap.
    have hrw : ∀ r : Fin (n + 1),
        ∑ j ∈ Cr r, (G j) ^ 2
          = ∑ j ∈ Finset.range K,
              (if (av r ≤ v j ∧ v (j + 1) ≤ bv r) then (G j) ^ 2 else 0) := by
      intro r
      rw [hCr]
      exact Finset.sum_filter _ _
    rw [Finset.sum_congr rfl (fun r _ => hrw r), Finset.sum_comm]
    -- Now bound each `j` term below by `(G j)²` (gap `j` is crossed at least once).
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨r₀, hr₀⟩ := hcross j (Finset.mem_range.mp hj)
    have hr₀' : av r₀ ≤ v j ∧ v (j + 1) ≤ bv r₀ := by
      rw [hCr, Finset.mem_filter] at hr₀; exact hr₀.2
    -- the r₀ term equals (G j)², all terms nonneg
    calc (G j) ^ 2 = (if (av r₀ ≤ v j ∧ v (j + 1) ≤ bv r₀) then (G j) ^ 2 else 0) := by
          rw [if_pos hr₀']
      _ ≤ ∑ r : Fin (n + 1),
            (if (av r ≤ v j ∧ v (j + 1) ≤ bv r) then (G j) ^ 2 else 0) := by
          apply Finset.single_le_sum (f := fun r =>
            (if (av r ≤ v j ∧ v (j + 1) ≤ bv r) then (G j) ^ 2 else 0))
          · intro r _; split <;> positivity
          · exact Finset.mem_univ r₀
  have hcrux : ∑ i : Fin K, (g i) ^ 2 ≤ ∑ r : Fin (n + 1), (M r.succ - M r.castSucc) ^ 2 :=
    calc ∑ i : Fin K, (g i) ^ 2 = ∑ j ∈ Finset.range K, (G j) ^ 2 := hgG
      _ ≤ ∑ r : Fin (n + 1), ∑ j ∈ Cr r, (G j) ^ 2 := hdc
      _ ≤ ∑ r : Fin (n + 1), (M r.succ - M r.castSucc) ^ 2 :=
          Finset.sum_le_sum (fun r _ => hstep r)
  -- Assemble.  Number of genuine gaps `K - 1 ≤ s` (from `K ≤ s + 1`).
  have hKs : (K : ℝ) - 1 ≤ s := by
    have : (K : ℝ) ≤ (s : ℝ) + 1 := by exact_mod_cast hWcard
    linarith
  have hsq_nn : (0:ℝ) ≤ ∑ i : Fin K, (g i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [div_le_iff₀ (by positivity : (0:ℝ) < s)]
  calc A ^ 2 ≤ ((K : ℝ) - 1) * ∑ i : Fin K, (g i) ^ 2 := hCS
    _ ≤ (s : ℝ) * ∑ i : Fin K, (g i) ^ 2 := by
        apply mul_le_mul_of_nonneg_right hKs hsq_nn
    _ ≤ (s : ℝ) * ∑ r : Fin (n + 1), (M r.succ - M r.castSucc) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hcrux (by positivity)
    _ = (∑ r : Fin (n + 1), (M r.succ - M r.castSucc) ^ 2) * s := by ring

end SSP
