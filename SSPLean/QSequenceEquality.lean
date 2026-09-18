import SSPLean.K2ErlangSharp

/-!
# Equality witness for the q-sequence bound

This file formalizes the serial equal-rate chain described by the equality discussion for
`q_sequence_bound_two_proofs.tex`.

Lean indexes `Fin s` from zero.  Thus, if `v : Fin s ≃ Fin s` records the relabeling
`v₁, …, vₛ`, the paper notation `v₁ = i` is represented by

```
  v ⟨0, hs⟩ = i
```

where `hs : 0 < s` proves that the zero index exists.
-/

open Matrix Finset

set_option autoImplicit false

namespace SSP.QSequenceEquality

/-- The canonical serial `s`-stage chain with common transition/absorption rate `lam`.

There is a self-loop of weight `1-lam` at every state, an edge of weight `lam` from state
`r` to state `r+1`, and absorption of weight `lam` from the last state. -/
noncomputable def serialErlangQ (s : ℕ) (lam : ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  (1 - lam) • (1 : Matrix (Fin s) (Fin s) ℝ) +
    lam • SSP.K2Concrete.erlangShiftQ s

/-- Entrywise form of `serialErlangQ`. -/
theorem serialErlangQ_apply (s : ℕ) (lam : ℝ) (r c : Fin s) :
    serialErlangQ s lam r c =
      if c = r then 1 - lam else if c.val = r.val + 1 then lam else 0 := by
  classical
  unfold serialErlangQ SSP.K2Concrete.erlangShiftQ
  by_cases hcr : c = r
  · subst c
    have hshift : (if h : r.val + 1 < s then
        if r = (⟨r.val + 1, h⟩ : Fin s) then (1 : ℝ) else 0 else 0) = 0 := by
      split
      · rename_i h
        rw [if_neg]
        intro heq
        have := congrArg Fin.val heq
        change r.val = r.val + 1 at this
        omega
      · rfl
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, if_pos, hshift]
    ring
  · have hrc : r ≠ c := fun h => hcr h.symm
    by_cases hr : r.val + 1 < s
    · by_cases hc : c = ⟨r.val + 1, hr⟩
      · have hcval : c.val = r.val + 1 := congrArg Fin.val hc
        have hid : (1 : Matrix (Fin s) (Fin s) ℝ) r c = 0 := by
          simp [hrc]
        have hshift :
            (if c = (⟨r.val + 1, hr⟩ : Fin s) then (1 : ℝ) else 0) = 1 := by simp [hc]
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hid, hr, dif_pos,
          hshift, hcr, if_false, hcval, if_true]
        norm_num
      · have hcval : c.val ≠ r.val + 1 := by
          intro h
          apply hc
          exact Fin.ext h
        have hid : (1 : Matrix (Fin s) (Fin s) ℝ) r c = 0 := by
          simp [hrc]
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hid, hr, dif_pos,
          hc, if_false, hcr, hcval]
        ring
    · have hcval : c.val ≠ r.val + 1 := by omega
      have hid : (1 : Matrix (Fin s) (Fin s) ℝ) r c = 0 := by
        simp [hrc]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hid, hr,
        hcr, hcval, if_false]
      simp

/-- Structural equality condition, invariant under a relabeling of the transient states.

The equivalence `v` lists the states in their serial order.  Its first entry is the prescribed
initial state `i`, which is the formal content of the notation `v₁ = i`. -/
def IsSerialErlang {s : ℕ} (hs : 0 < s) (Q : Matrix (Fin s) (Fin s) ℝ) (i : Fin s) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
    ∃ v : Fin s ≃ Fin s,
      v ⟨0, hs⟩ = i ∧
      ∀ r c : Fin s,
        Q (v r) (v c) =
          if c = r then 1 - lam else if c.val = r.val + 1 then lam else 0

/-- The canonical ordering is a serial Erlang ordering, and its first state is `0`. -/
theorem serialErlangQ_isSerial {s : ℕ} (hs : 0 < s) {lam : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    IsSerialErlang hs (serialErlangQ s lam) ⟨0, hs⟩ := by
  refine ⟨lam, hlam0, hlam1, Equiv.refl (Fin s), rfl, ?_⟩
  intro r c
  simpa using serialErlangQ_apply s lam r c

/-- Factoring the resolvent denominator of the common-rate serial chain. -/
theorem one_sub_serialErlangQ (s : ℕ) (lam : ℝ) :
    (1 : Matrix (Fin s) (Fin s) ℝ) - serialErlangQ s lam =
      lam • (1 - SSP.K2Concrete.erlangShiftQ s) := by
  ext r c
  simp only [serialErlangQ, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- Explicit resolvent of the common-rate serial chain. -/
theorem serialErlangQ_inverse {s : ℕ} {lam : ℝ} (hlam : lam ≠ 0) :
    (1 - serialErlangQ s lam)⁻¹ =
      lam⁻¹ • SSP.K2Concrete.erlangResolvent s := by
  apply Matrix.inv_eq_right_inv
  rw [one_sub_serialErlangQ]
  ext r c
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  have hbase := congrFun₂ (SSP.K2Concrete.one_sub_erlangShiftQ_mul_erlangResolvent s) r c
  simp only [Matrix.mul_apply] at hbase
  rw [← hbase]
  apply Finset.sum_congr rfl
  intro x _
  field_simp

/-- The fundamental vector has equally spaced levels. -/
theorem serialErlangQ_fundamental {s : ℕ} {lam : ℝ} (hlam : lam ≠ 0) (r : Fin s) :
    ((1 - serialErlangQ s lam)⁻¹.mulVec (fun _ => (1 : ℝ))) r =
      lam⁻¹ * (s - r.val) := by
  rw [serialErlangQ_inverse hlam]
  rw [Matrix.smul_mulVec]
  change lam⁻¹ * (SSP.K2Concrete.erlangResolvent s).mulVec (fun _ => (1 : ℝ)) r = _
  rw [SSP.K2Concrete.erlangResolvent_one]

/-- Applying the resolvent twice gives the second weighted q-sequence sum. -/
theorem serialErlangQ_second {s : ℕ} {lam : ℝ} (hlam : lam ≠ 0) (r : Fin s) :
    ((1 - serialErlangQ s lam)⁻¹.mulVec
        ((1 - serialErlangQ s lam)⁻¹.mulVec (fun _ => (1 : ℝ)))) r =
      lam⁻¹ ^ 2 * SSP.K2Concrete.erlangV2 s r := by
  rw [serialErlangQ_inverse hlam]
  have hone : (SSP.K2Concrete.erlangResolvent s).mulVec (fun _ => (1 : ℝ)) =
      SSP.K2Concrete.erlangV1 s := by
    funext j
    rw [SSP.K2Concrete.erlangResolvent_one]
    rfl
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, hone]
  change lam⁻¹ *
      ((SSP.K2Concrete.erlangResolvent s).mulVec
        (lam⁻¹ • SSP.K2Concrete.erlangV1 s)) r = _
  rw [Matrix.mulVec_smul]
  rw [SSP.K2Concrete.erlangResolvent_mulVec_v1]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Equality in the q-sequence bound.**

For the serial `s`-stage chain, started in its first state, the component inequality is an
equality.  The restrictions `0 < lam ≤ 1` make the matrix substochastic; algebraically only
`lam ≠ 0` is needed for this identity. -/
theorem serialErlangQ_equality {s : ℕ} (hs : 0 < s) {lam : ℝ} (hlam : lam ≠ 0) :
    (((1 - serialErlangQ s lam)⁻¹.mulVec (fun _ => (1 : ℝ))) ⟨0, hs⟩) ^ 2 =
      (2 * (s : ℝ) / ((s : ℝ) + 1)) *
        ((1 - serialErlangQ s lam)⁻¹.mulVec
          ((1 - serialErlangQ s lam)⁻¹.mulVec (fun _ => (1 : ℝ)))) ⟨0, hs⟩ := by
  rw [serialErlangQ_fundamental hlam, serialErlangQ_second hlam]
  simp only [SSP.K2Concrete.erlangV2, SSP.K2Concrete.erlangV1]
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hs1R : (s : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Simultaneously relabeling the rows, columns, and vector coordinates does not change a
matrix-vector product. -/
theorem reindex_mulVec {s : ℕ} (v : Fin s ≃ Fin s) (A : Matrix (Fin s) (Fin s) ℝ)
    (z : Fin s → ℝ) (r : Fin s) :
    ((Matrix.reindex v v) A).mulVec (fun j => z (v.symm j)) (v r) = A.mulVec z r := by
  classical
  unfold Matrix.mulVec dotProduct
  simp only [Matrix.reindex_apply]
  rw [← Equiv.sum_comp v]
  simp

/-- Relabeling does not change either resolvent moment at corresponding states. -/
theorem reindex_resolvent_moments {s : ℕ} (v : Fin s ≃ Fin s)
    (A : Matrix (Fin s) (Fin s) ℝ) (r : Fin s) :
    ((((Matrix.reindex v v) A)⁻¹.mulVec (fun _ => (1 : ℝ))) (v r) =
        (A⁻¹.mulVec (fun _ => (1 : ℝ))) r) ∧
      ((((Matrix.reindex v v) A)⁻¹.mulVec
          (((Matrix.reindex v v) A)⁻¹.mulVec (fun _ => (1 : ℝ)))) (v r) =
        (A⁻¹.mulVec (A⁻¹.mulVec (fun _ => (1 : ℝ)))) r) := by
  classical
  have hinv : ((Matrix.reindex v v) A)⁻¹ = (Matrix.reindex v v) A⁻¹ :=
    Matrix.inv_reindex v v A
  rw [hinv]
  have hfirst := reindex_mulVec v A⁻¹ (fun _ => (1 : ℝ)) r
  have hfun : ((Matrix.reindex v v) A⁻¹).mulVec (fun _ => (1 : ℝ)) =
      fun j => (A⁻¹.mulVec (fun _ => (1 : ℝ))) (v.symm j) := by
    funext j
    let q : Fin s := v.symm j
    have h := reindex_mulVec v A⁻¹ (fun _ => (1 : ℝ)) q
    simpa [q] using h
  constructor
  · exact hfirst
  · rw [hfun]
    exact reindex_mulVec v A⁻¹ (A⁻¹.mulVec (fun _ => (1 : ℝ))) r

/-- **The relabeling-invariant sharpness statement.**

If `Q` is a common-rate serial chain in some state ordering `v`, and `i = v 0` is its first
phase, then the q-sequence component bound at `i` is an equality. -/
theorem IsSerialErlang.equality {s : ℕ} {hs : 0 < s}
    {Q : Matrix (Fin s) (Fin s) ℝ} {i : Fin s} (h : IsSerialErlang hs Q i) :
    (((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ))) i) ^ 2 =
      (2 * (s : ℝ) / ((s : ℝ) + 1)) *
        ((1 - Q)⁻¹.mulVec ((1 - Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) i := by
  classical
  obtain ⟨lam, hlam0, _hlam1, v, hv0, hQ⟩ := h
  have hQeq : Q = (Matrix.reindex v v) (serialErlangQ s lam) := by
    ext a b
    have hab := hQ (v.symm a) (v.symm b)
    change Q a b = serialErlangQ s lam (v.symm a) (v.symm b)
    rw [serialErlangQ_apply]
    simpa only [Equiv.apply_symm_apply] using hab
  have hden : (1 : Matrix (Fin s) (Fin s) ℝ) - Q =
      (Matrix.reindex v v) (1 - serialErlangQ s lam) := by
    rw [hQeq]
    ext a b
    simp [Matrix.reindex_apply, Matrix.one_apply]
  rw [hden, hv0.symm]
  obtain ⟨hfirst, hsecond⟩ :=
    reindex_resolvent_moments v (1 - serialErlangQ s lam) ⟨0, hs⟩
  rw [hfirst, hsecond]
  exact serialErlangQ_equality hs (ne_of_gt hlam0)

/-! ## Rigidity input for the converse

The following lemma reverses all *averaging* steps in the weighted-path proof.  It says that
equality in the component bound makes every absorbing path of positive weight attain the
minimum possible path energy.  The remaining converse is therefore a finite rigidity problem
for equality in the level-crossing Cauchy--Schwarz estimate. -/

/-- Equality in the component bound is equivalent to equality in the crossing bound. -/
theorem vVec_eq_crossing_of_component_eq
    (s : ℕ) (Q : ℕ → ℕ → ℝ) (theta C : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hC0 : 0 ≤ C)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hdecay : ∀ k, ∀ a < s,
      SSP.matVec s (SSP.matPow s Q k) SSP.eVec a ≤ C * theta ^ k)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (hs : 0 < s) (i : ℕ) (hi : i < s)
    (heq : (SSP.xVec s Q i) ^ 2 =
      (2 * (s : ℝ) / ((s : ℝ) + 1)) * SSP.yVec s Q i) :
    SSP.vVec s Q i = (SSP.xVec s Q i) ^ 2 / s := by
  have hv := SSP.vVec_eq s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub i hi
  rw [hv]
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hs1 : (s : ℝ) + 1 ≠ 0 := by positivity
  field_simp at heq ⊢
  nlinarith [heq]

/-- If the component bound is sharp, each positive-weight absorbing path is itself sharp in
the path-energy estimate. -/
theorem pathEnergy_eq_of_component_eq
    (s : ℕ) (Q : ℕ → ℕ → ℝ) (theta C : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hC0 : 0 ≤ C)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hdecay : ∀ k, ∀ a < s,
      SSP.matVec s (SSP.matPow s Q k) SSP.eVec a ≤ C * theta ^ k)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (hs : 0 < s) (i : ℕ) (hi : i < s)
    (heq : (SSP.xVec s Q i) ^ 2 =
      (2 * (s : ℝ) / ((s : ℝ) + 1)) * SSP.yVec s Q i)
    (m : ℕ) (p : Fin (m + 1) → Fin s) (hp0 : (p 0 : ℕ) = i)
    (hpw : 0 < SSP.pathWeight s Q m p) :
    SSP.pathEnergy s Q m p = (SSP.xVec s Q i) ^ 2 / s := by
  let c : ℝ := (SSP.xVec s Q i) ^ 2 / s
  have hPW : HasSum (fun n => SSP.PWterm s Q i n) (SSP.vVec s Q i) :=
    SSP.hasSum_PWterm s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub hs i hi
  have hTWsum : ∑' n, SSP.TWterm s Q i n = 1 :=
    SSP.tsum_TWterm_eq_one s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub i hi
  have hTWsummable : Summable (fun n => SSP.TWterm s Q i n) := by
    by_contra hn
    rw [tsum_eq_zero_of_not_summable hn] at hTWsum
    exact one_ne_zero hTWsum.symm
  have hgap_nonneg : ∀ n,
      0 ≤ SSP.PWterm s Q i n - SSP.TWterm s Q i n * c := by
    intro n
    exact sub_nonneg.mpr
      (SSP.PWterm_ge s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub hs i hi n)
  have hgap_summable : Summable
      (fun n => SSP.PWterm s Q i n - SSP.TWterm s Q i n * c) :=
    hPW.summable.sub (hTWsummable.mul_right c)
  have hgap_sum : ∑' n, (SSP.PWterm s Q i n - SSP.TWterm s Q i n * c) = 0 := by
    rw [hPW.summable.tsum_sub (hTWsummable.mul_right c), hPW.tsum_eq,
      hTWsummable.tsum_mul_right, hTWsum, one_mul,
      vVec_eq_crossing_of_component_eq s Q theta C htheta0 htheta1 hC0 hQ hdecay
        hsub hs i hi heq]
    simp [c]
  have hgap_m : SSP.PWterm s Q i m - SSP.TWterm s Q i m * c = 0 := by
    have hle := hgap_summable.le_tsum m (fun n _ => hgap_nonneg n)
    rw [hgap_sum] at hle
    exact le_antisymm hle (hgap_nonneg m)
  have hgap_form :
      SSP.PWterm s Q i m - SSP.TWterm s Q i m * c =
        ∑ q : Fin (m + 1) → Fin s,
          (if (q 0 : ℕ) = i then
            SSP.pathWeight s Q m q * (SSP.pathEnergy s Q m q - c) else 0) := by
    simp only [SSP.PWterm, SSP.TWterm, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> ring
  rw [hgap_form] at hgap_m
  have hterm_nonneg : ∀ q : Fin (m + 1) → Fin s,
      0 ≤ if (q 0 : ℕ) = i then
        SSP.pathWeight s Q m q * (SSP.pathEnergy s Q m q - c) else 0 := by
    intro q
    split_ifs with hq
    · exact mul_nonneg (SSP.pathWeight_nonneg s Q hQ hsub m q)
        (sub_nonneg.mpr
          (SSP.pathEnergy_ge s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub hs
            i hi m q hq))
    · exact le_rfl
  have hzero :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun q (_ : q ∈ Finset.univ) => hterm_nonneg q)).mp hgap_m
  have hpzero := hzero p (Finset.mem_univ p)
  rw [if_pos hp0] at hpzero
  rcases mul_eq_zero.mp hpzero with hw | henergy
  · exact (ne_of_gt hpw hw).elim
  · dsimp [c] at henergy ⊢
    linarith

/-- Finite Cauchy--Schwarz rigidity used by the converse.  If `n ≤ s` increments sum to a
positive number `A`, while their squared energy is the `s`-stage minimum `A²/s`, then in fact
`n=s` and every increment is `A/s`. -/
theorem increments_rigid {n s : ℕ} (hn0 : 0 < n) (hns : n ≤ s)
    (A : ℝ) (hA : 0 < A) (d : Fin n → ℝ)
    (hsum : ∑ r, d r = A) (henergy : ∑ r, (d r) ^ 2 = A ^ 2 / s) :
    n = s ∧ ∀ r, d r = A / s := by
  have hs0 : 0 < s := lt_of_lt_of_le hn0 hns
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := d)
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  rw [hsum, henergy] at hcs
  have hsn : (s : ℝ) ≤ n := by
    have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
    calc
      (s : ℝ) = (s : ℝ) * A ^ 2 / A ^ 2 := by field_simp
      _ ≤ (n : ℝ) * A ^ 2 / A ^ 2 := by
        apply div_le_div_of_nonneg_right _ hA2.le
        calc
          (s : ℝ) * A ^ 2 ≤ (s : ℝ) * ((n : ℝ) * (A ^ 2 / s)) := by
            exact mul_le_mul_of_nonneg_left hcs hsR.le
          _ = (n : ℝ) * A ^ 2 := by field_simp
      _ = n := by field_simp
  have hsnNat : s ≤ n := by exact_mod_cast hsn
  have hne : n = s := Nat.le_antisymm hns hsnNat
  subst n
  constructor
  · rfl
  · intro r
    let mu : ℝ := A / s
    have hdev : ∑ j : Fin s, (d j - mu) ^ 2 = 0 := by
      have hcard : ∑ _j : Fin s, (1 : ℝ) = s := by simp
      have hmid : ∑ j : Fin s, 2 * d j * mu = 2 * mu * ∑ j : Fin s, d j := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring
      calc
        ∑ j : Fin s, (d j - mu) ^ 2
            = (∑ j : Fin s, (d j) ^ 2) - 2 * mu * (∑ j : Fin s, d j) +
                (∑ _j : Fin s, (1 : ℝ)) * mu ^ 2 := by
              simp_rw [sub_sq]
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              rw [hmid]
              ring
        _ = A ^ 2 / s - 2 * mu * A + (s : ℝ) * mu ^ 2 := by
              rw [henergy, hsum, hcard]
        _ = 0 := by
              dsimp [mu]
              field_simp
              ring
    have hnonneg : ∀ j : Fin s, 0 ≤ (d j - mu) ^ 2 := fun _ => sq_nonneg _
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin s))) => hnonneg j)).mp hdev r
      (Finset.mem_univ r)
    have : d r - mu = 0 := sq_eq_zero_iff.mp hz
    dsimp [mu] at this ⊢
    linarith

/-- From every transient state there is a finite absorbing path of positive weight. -/
theorem exists_positive_absorbing_path
    (s : ℕ) (Q : ℕ → ℕ → ℝ) (theta C : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hC0 : 0 ≤ C)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hdecay : ∀ k, ∀ a < s,
      SSP.matVec s (SSP.matPow s Q k) SSP.eVec a ≤ C * theta ^ k)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (a : ℕ) (ha : a < s) :
    ∃ m, ∃ p : Fin (m + 1) → Fin s,
      (p 0 : ℕ) = a ∧ 0 < SSP.pathWeight s Q m p := by
  have hsum : ∑' m, SSP.TWterm s Q a m = 1 :=
    SSP.tsum_TWterm_eq_one s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub a ha
  have hexm : ∃ m, 0 < SSP.TWterm s Q a m := by
    by_contra hn
    push Not at hn
    have hz : ∀ m, SSP.TWterm s Q a m = 0 := by
      intro m
      exact le_antisymm (hn m) (SSP.TWterm_nonneg s Q hQ hsub a m)
    simp_rw [hz] at hsum
    norm_num at hsum
  obtain ⟨m, hm⟩ := hexm
  unfold SSP.TWterm at hm
  have hexp : ∃ p : Fin (m + 1) → Fin s,
      0 < if (p 0 : ℕ) = a then SSP.pathWeight s Q m p else 0 := by
    by_contra hn
    push Not at hn
    have := Finset.sum_nonpos (fun p (_ : p ∈ Finset.univ) => hn p)
    linarith
  obtain ⟨p, hp⟩ := hexp
  by_cases hp0 : (p 0 : ℕ) = a
  · rw [if_pos hp0] at hp
    exact ⟨m, p, hp0, hp⟩
  · rw [if_neg hp0] at hp
    linarith

/-- A finite relational route can be cycle-erased without changing its first or last vertex.
The resulting route is a sublist, remains a chain, and has no repeated vertices. -/
theorem exists_nodup_chain_sublist {alpha : Type*} [DecidableEq alpha]
    (R : alpha → alpha → Prop) (l : List alpha) (hne : l ≠ []) (hchain : l.IsChain R) :
    ∃ l' : List alpha,
      List.Sublist l' l ∧ l'.Nodup ∧ l'.IsChain R ∧
        l'.head? = l.head? ∧ l'.getLast? = l.getLast? := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
      cases l with
      | nil => exact (hne rfl).elim
      | cons a tail =>
          by_cases ha : a ∈ tail
          · obtain ⟨k, hk, hka⟩ := List.mem_iff_getElem.mp ha
            let u := tail.drop k
            have hu_ne : u ≠ [] := by
              intro hempty
              have hlen : u.length = 0 := by simp [hempty]
              simp only [u, List.length_drop] at hlen
              omega
            have hu_head : u.head? = some a := by
              simp only [u, List.head?_drop]
              simp [List.getElem?_eq_getElem hk, hka]
            have hu_last : u.getLast? = (a :: tail).getLast? := by
              have hcons : (a :: tail).getLast? = tail.getLast? := by
                cases tail with
                | nil => simp at ha
                | cons b rest => simp
              change (tail.drop k).getLast? = (a :: tail).getLast?
              rw [List.getLast?_drop, if_neg (Nat.not_le_of_lt hk), ← hcons]
            have hu_len : u.length < (a :: tail).length := by
              simp only [u, List.length_drop, List.length_cons]
              omega
            have hu_chain : u.IsChain R := hchain.tail.drop k
            obtain ⟨u', hu'sub, hu'nodup, hu'chain, hu'head, hu'last⟩ :=
              ih u.length (by rw [← hn]; exact hu_len) u hu_ne hu_chain rfl
            refine ⟨u', hu'sub.trans ?_, hu'nodup, hu'chain, ?_, ?_⟩
            · exact (List.drop_sublist k tail).trans (List.Sublist.cons _ (List.Sublist.refl tail))
            · rw [hu'head, hu_head]
              simp
            · rw [hu'last, hu_last]
          · cases tail with
            | nil =>
                exact ⟨[a], List.Sublist.refl [a], by simp, List.isChain_singleton a, rfl, rfl⟩
            | cons b rest =>
                have htail_chain : (b :: rest).IsChain R := hchain.tail
                have htail_ne : (b :: rest) ≠ [] := List.cons_ne_nil _ _
                have htail_len : (b :: rest).length < (a :: b :: rest).length := by simp
                obtain ⟨u, husub, hunodup, huchain, huhead, hulast⟩ :=
                  ih (b :: rest).length (by rw [← hn]; exact htail_len)
                    (b :: rest) htail_ne htail_chain rfl
                obtain ⟨u', rfl⟩ := List.head?_eq_some_iff.mp (by simpa using huhead)
                have hab : R a b := by
                  rw [List.isChain_cons_cons] at hchain
                  exact hchain.1
                have hanot : a ∉ b :: u' := by
                  intro hamem
                  apply ha
                  exact husub.subset hamem
                refine ⟨a :: b :: u', husub.cons_cons a, List.Nodup.cons hanot hunodup,
                  huchain.cons_cons hab, rfl, ?_⟩
                simpa using hulast

/-- The last element of `List.ofFn p` is the value at `Fin.last`. -/
theorem getLast?_ofFn_succ {alpha : Type*} :
    ∀ {m : ℕ} (p : Fin (m + 1) → alpha),
      (List.ofFn p).getLast? = some (p (Fin.last m)) := by
  intro m
  induction m with
  | zero =>
      intro p
      simp [List.ofFn_succ]
  | succ m ih =>
      intro p
      rw [List.ofFn_succ, List.getLast?_cons, ih]
      simp only [Option.getD_some]
      congr

/-- A positive weighted path contains a cycle-free positive route with the same initial and
terminal states.  In particular the route has at most `s` vertices. -/
theorem positive_path_has_simple_route
    (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (i m : ℕ) (p : Fin (m + 1) → Fin s) (hp0 : (p 0 : ℕ) = i)
    (hpw : 0 < SSP.pathWeight s Q m p) :
    ∃ l : List (Fin s), l.Nodup ∧
      l.IsChain (fun a b : Fin s => 0 < Q (a : ℕ) (b : ℕ)) ∧
      l.head? = some ⟨i, by simpa [hp0] using (p 0).isLt⟩ ∧
      (∃ z : Fin s, l.getLast? = some z ∧ 0 < SSP.bVec s Q z) ∧
      l.length ≤ s := by
  classical
  have hprod0 : 0 ≤ SSP.pathProd s Q m p := SSP.pathProd_nonneg s Q hQ m p
  have hb0 : 0 ≤ SSP.bVec s Q (p (Fin.last m) : ℕ) :=
    SSP.bVec_nonneg s Q hsub _ (p (Fin.last m)).isLt
  have hprodpos : 0 < SSP.pathProd s Q m p := by
    unfold SSP.pathWeight at hpw
    rcases (mul_pos_iff.mp hpw) with h | h
    · exact h.1
    · linarith
  have hbpos : 0 < SSP.bVec s Q (p (Fin.last m) : ℕ) := by
    unfold SSP.pathWeight at hpw
    rcases (mul_pos_iff.mp hpw) with h | h
    · exact h.2
    · linarith
  let route : List (Fin s) := List.ofFn p
  have hroute_ne : route ≠ [] := by simp [route]
  have hroute_chain :
      route.IsChain (fun a b : Fin s => 0 < Q (a : ℕ) (b : ℕ)) := by
    rw [List.isChain_iff_getElem]
    intro k hk
    have hk' : k < m := by
      simp only [route, List.length_ofFn] at hk
      omega
    simp only [route, List.getElem_ofFn]
    change 0 < Q (p ⟨k, by omega⟩ : ℕ) (p ⟨k + 1, by omega⟩ : ℕ)
    have hfacne :
        Q (p ⟨k, by omega⟩ : ℕ) (p ⟨k + 1, by omega⟩ : ℕ) ≠ 0 := by
      have hall := (Finset.prod_ne_zero_iff.mp (ne_of_gt hprodpos))
        (⟨k, hk'⟩ : Fin m) (Finset.mem_univ _)
      simpa only [SSP.pathProd, Fin.castSucc_mk, Fin.succ_mk] using hall
    exact lt_of_le_of_ne
      (hQ (p ⟨k, by omega⟩ : ℕ) (p ⟨k + 1, by omega⟩ : ℕ)) hfacne.symm
  obtain ⟨l, hlsub, hlnodup, hlchain, hlhead, hllast⟩ :=
    exists_nodup_chain_sublist
      (fun a b : Fin s => 0 < Q (a : ℕ) (b : ℕ)) route hroute_ne hroute_chain
  have hroute_head : route.head? = some ⟨i, by simpa [hp0] using (p 0).isLt⟩ := by
    have hp0fin : p 0 = ⟨i, by simpa [hp0] using (p 0).isLt⟩ := Fin.ext hp0
    simp [route, hp0fin]
  have hroute_last : route.getLast? = some (p (Fin.last m)) := by
    exact getLast?_ofFn_succ p
  refine ⟨l, hlnodup, hlchain, ?_, ?_, ?_⟩
  · rw [hlhead, hroute_head]
  · exact ⟨p (Fin.last m), hllast.trans hroute_last, hbpos⟩
  · simpa using hlnodup.length_le_card

/-- From a positive absorbing path one may remove cycles and re-enumerate the resulting
route as an injective positive absorbing path of at most `s` vertices. -/
theorem exists_positive_simple_absorbing_path
    (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (i m : ℕ) (p : Fin (m + 1) → Fin s) (hp0 : (p 0 : ℕ) = i)
    (hpw : 0 < SSP.pathWeight s Q m p) :
    ∃ n, ∃ q : Fin (n + 1) → Fin s,
      Function.Injective q ∧ n + 1 ≤ s ∧ (q 0 : ℕ) = i ∧
        0 < SSP.pathWeight s Q n q := by
  classical
  obtain ⟨l, hlnodup, hlchain, hlhead, ⟨z, hllast, hbpos⟩, hllen⟩ :=
    positive_path_has_simple_route s Q hQ hsub i m p hp0 hpw
  cases l with
  | nil => simp at hlhead
  | cons a tail =>
      let q : Fin (tail.length + 1) → Fin s := (a :: tail).get
      have hq0 : (q 0 : ℕ) = i := by
        have hi : i < s := by rw [← hp0]; exact (p 0).isLt
        have ha : a = ⟨i, hi⟩ := by simpa using hlhead
        simp [q, ha]
      have hqinj : Function.Injective q := by
        exact hlnodup.injective_get
      have hprodpos : 0 < SSP.pathProd s Q tail.length q := by
        apply Finset.prod_pos
        intro r _
        have hedge := hlchain.getElem r.val (by
          simp only [List.length_cons]
          omega)
        change 0 < Q (q r.castSucc : ℕ) (q r.succ : ℕ)
        change 0 < Q ((a :: tail)[r.val] : Fin s) ((a :: tail)[r.val + 1] : Fin s)
        exact hedge
      have hblast : 0 < SSP.bVec s Q (q (Fin.last tail.length) : ℕ) := by
        have hof : List.ofFn q = a :: tail := by
          exact List.ofFn_get (a :: tail)
        have hlastq : (List.ofFn q).getLast? = some z := by
          rw [hof]
          exact hllast
        rw [getLast?_ofFn_succ] at hlastq
        have hqz : q (Fin.last tail.length) = z := Option.some.inj hlastq
        simpa [hqz] using hbpos
      refine ⟨tail.length, q, hqinj, ?_, hq0, ?_⟩
      · simpa using hllen
      · unfold SSP.pathWeight
        exact mul_pos hprodpos hblast

/-- A finite chain of differences telescopes from its first to its last value. -/
theorem sum_fin_succ_sub {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∑ r : Fin n, (f r.castSucc - f r.succ) = f 0 - f (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (fun r : Fin (n + 1) => f r.succ)
      simp only [Fin.succ_zero_eq_one, Fin.succ_castSucc] at htail ⊢
      rw [htail]
      rw [Fin.succ_last]
      have hzero : (Fin.castSucc (0 : Fin (n + 1)) : Fin (n + 2)) = 0 := Fin.ext rfl
      have hlast : (Fin.last n.succ : Fin (n + 2)) = Fin.last (n + 1) := Fin.ext rfl
      rw [hzero, hlast]
      ring

/-- The cycle-free absorbing path supplied above is rigid under equality: it uses all `s`
states, and every level drop (including the last drop to the cemetery state) is `x_i / s`. -/
theorem exists_rigid_simple_path
    (s : ℕ) (Q : ℕ → ℕ → ℝ) (theta C : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hC0 : 0 ≤ C)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hdecay : ∀ k, ∀ a < s,
      SSP.matVec s (SSP.matPow s Q k) SSP.eVec a ≤ C * theta ^ k)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (hs : 0 < s) (i : ℕ) (hi : i < s)
    (heq : (SSP.xVec s Q i) ^ 2 =
      (2 * (s : ℝ) / ((s : ℝ) + 1)) * SSP.yVec s Q i) :
    ∃ n, ∃ q : Fin (n + 1) → Fin s,
      Function.Injective q ∧ n + 1 = s ∧ (q 0 : ℕ) = i ∧
        0 < SSP.pathWeight s Q n q ∧
        (∀ r : Fin n,
          SSP.xVec s Q (q r.castSucc : ℕ) - SSP.xVec s Q (q r.succ : ℕ) =
            SSP.xVec s Q i / s) ∧
        SSP.xVec s Q (q (Fin.last n) : ℕ) = SSP.xVec s Q i / s := by
  obtain ⟨m, p, hp0, hpw⟩ :=
    exists_positive_absorbing_path s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub i hi
  obtain ⟨n, q, hqinj, hnle, hq0, hqw⟩ :=
    exists_positive_simple_absorbing_path s Q hQ hsub i m p hp0 hpw
  let A : ℝ := SSP.xVec s Q i
  have hA : 0 < A := by
    have hx := SSP.xVec_fixed_point s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub i hi
    have hsum0 : 0 ≤ ∑ l ∈ range s, Q i l * SSP.xVec s Q l := by
      apply Finset.sum_nonneg
      intro a _
      exact mul_nonneg (hQ _ _) (SSP.xVec_nonneg s Q hQ _)
    dsimp [A]
    linarith
  let d : Fin (n + 1) → ℝ := Fin.lastCases
    (SSP.xVec s Q (q (Fin.last n) : ℕ))
    (fun r : Fin n =>
      SSP.xVec s Q (q r.castSucc : ℕ) - SSP.xVec s Q (q r.succ : ℕ))
  have hdsum : ∑ r, d r = A := by
    rw [Fin.sum_univ_castSucc]
    simp only [d, Fin.lastCases_castSucc, Fin.lastCases_last]
    have htel := sum_fin_succ_sub
      (fun r : Fin (n + 1) => SSP.xVec s Q (q r : ℕ))
    rw [htel]
    dsimp [A]
    rw [hq0]
    ring
  have hdenergy : ∑ r, (d r) ^ 2 = A ^ 2 / s := by
    have hpath := pathEnergy_eq_of_component_eq s Q theta C htheta0 htheta1 hC0 hQ
      hdecay hsub hs i hi heq n q hq0 hqw
    rw [Fin.sum_univ_castSucc]
    simp only [d, Fin.lastCases_castSucc, Fin.lastCases_last]
    calc
      (∑ x : Fin n,
          (SSP.xVec s Q (q x.castSucc : ℕ) - SSP.xVec s Q (q x.succ : ℕ)) ^ 2) +
            SSP.xVec s Q (q (Fin.last n) : ℕ) ^ 2 =
          SSP.pathEnergy s Q n q := by
            unfold SSP.pathEnergy
            congr 1
            apply Finset.sum_congr rfl
            intro r _
            ring
      _ = A ^ 2 / s := by simpa [A] using hpath
  obtain ⟨hns, hd⟩ :=
    increments_rigid (n := n + 1) (s := s) (by omega) hnle A hA d hdsum hdenergy
  refine ⟨n, q, hqinj, hns, hq0, hqw, ?_, ?_⟩
  · intro r
    simpa only [d, Fin.lastCases_castSucc] using hd r.castSucc
  · simpa only [d, Fin.lastCases_last] using hd (Fin.last n)

/-- Equality supplies an ordering of all states in which the `x`-levels are equally spaced;
the consecutive edges and the final absorption defect are all strictly positive. -/
theorem exists_rigid_ordering
    (s : ℕ) (Q : ℕ → ℕ → ℝ) (theta C : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hC0 : 0 ≤ C)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hdecay : ∀ k, ∀ a < s,
      SSP.matVec s (SSP.matPow s Q k) SSP.eVec a ≤ C * theta ^ k)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (hs : 0 < s) (i : ℕ) (hi : i < s)
    (heq : (SSP.xVec s Q i) ^ 2 =
      (2 * (s : ℝ) / ((s : ℝ) + 1)) * SSP.yVec s Q i) :
    ∃ v : Fin s ≃ Fin s,
      (v ⟨0, hs⟩ : ℕ) = i ∧
      (∀ (r : Fin s) (hr : r.val + 1 < s),
        SSP.xVec s Q (v r : ℕ) - SSP.xVec s Q (v ⟨r.val + 1, hr⟩ : ℕ) =
          SSP.xVec s Q i / s) ∧
      SSP.xVec s Q (v ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ : ℕ) =
        SSP.xVec s Q i / s ∧
      (∀ (r : Fin s) (hr : r.val + 1 < s),
        0 < Q (v r : ℕ) (v ⟨r.val + 1, hr⟩ : ℕ)) ∧
      0 < SSP.bVec s Q (v ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ : ℕ) := by
  obtain ⟨n, q, hqinj, hns, hq0, hqw, hgaps, hlastx⟩ :=
    exists_rigid_simple_path s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub
      hs i hi heq
  subst s
  have hqsurj : Function.Surjective q := Finite.injective_iff_surjective.mp hqinj
  let v : Fin (n + 1) ≃ Fin (n + 1) := Equiv.ofBijective q ⟨hqinj, hqsurj⟩
  have hprod0 : 0 ≤ SSP.pathProd (n + 1) Q n q :=
    SSP.pathProd_nonneg (n + 1) Q hQ n q
  have hb0 : 0 ≤ SSP.bVec (n + 1) Q (q (Fin.last n) : ℕ) :=
    SSP.bVec_nonneg (n + 1) Q hsub _ (q (Fin.last n)).isLt
  have hprodpos : 0 < SSP.pathProd (n + 1) Q n q := by
    unfold SSP.pathWeight at hqw
    rcases mul_pos_iff.mp hqw with h | h
    · exact h.1
    · linarith
  have hbpos : 0 < SSP.bVec (n + 1) Q (q (Fin.last n) : ℕ) := by
    unfold SSP.pathWeight at hqw
    rcases mul_pos_iff.mp hqw with h | h
    · exact h.2
    · linarith
  have hedges : ∀ r : Fin n, 0 < Q (q r.castSucc : ℕ) (q r.succ : ℕ) := by
    intro r
    have hfacne := (Finset.prod_ne_zero_iff.mp (ne_of_gt hprodpos)) r (Finset.mem_univ r)
    have hfac0 := hQ (q r.castSucc : ℕ) (q r.succ : ℕ)
    exact lt_of_le_of_ne hfac0 (by
      simpa only [SSP.pathProd] using hfacne.symm)
  refine ⟨v, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [v] using hq0
  · intro r hr
    let r' : Fin n := ⟨r.val, by omega⟩
    have hcast : r'.castSucc = r := Fin.ext rfl
    have hsucc : r'.succ = ⟨r.val + 1, hr⟩ := Fin.ext rfl
    simpa only [v, Equiv.ofBijective_apply, hcast, hsucc] using hgaps r'
  · have hlast : (⟨n + 1 - 1, Nat.sub_lt (by omega) zero_lt_one⟩ : Fin (n + 1)) =
        Fin.last n := Fin.ext (by simp)
    simpa only [v, Equiv.ofBijective_apply, hlast] using hlastx
  · intro r hr
    let r' : Fin n := ⟨r.val, by omega⟩
    have hcast : r'.castSucc = r := Fin.ext rfl
    have hsucc : r'.succ = ⟨r.val + 1, hr⟩ := Fin.ext rfl
    simpa only [v, Equiv.ofBijective_apply, hcast, hsucc] using hedges r'
  · have hlast : (⟨n + 1 - 1, Nat.sub_lt (by omega) zero_lt_one⟩ : Fin (n + 1)) =
        Fin.last n := Fin.ext (by simp)
    simpa only [v, Equiv.ofBijective_apply, hlast] using hbpos

/-- Equal adjacent gaps and a final value `c` force the descending arithmetic progression. -/
theorem eq_nat_sub_mul_of_equal_gaps {s : ℕ} (hs : 0 < s) (f : Fin s → ℝ) (c : ℝ)
    (hgap : ∀ (r : Fin s) (hr : r.val + 1 < s), f r - f ⟨r.val + 1, hr⟩ = c)
    (hlast : f ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ = c) :
    ∀ r : Fin s, f r = ((s - r.val : ℕ) : ℝ) * c := by
  intro r
  induction hk : s - r.val using Nat.strong_induction_on generalizing r with
  | h k ih =>
      by_cases hr : r.val + 1 < s
      · let r' : Fin s := ⟨r.val + 1, hr⟩
        have hklt : s - r'.val < k := by
          dsimp [r']
          omega
        have hkr' : s - r'.val = k - 1 := by
          dsimp [r']
          omega
        have hnext := ih (s - r'.val) hklt r' rfl
        have hthis := hgap r hr
        rw [hkr'] at hnext
        rw [hnext] at hthis
        have hkpos : 0 < k := by omega
        have hkreal : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
          exact_mod_cast (show k = (k - 1) + 1 by omega)
        have hfr : f r = (k : ℝ) * c := by
          rw [hkreal]
          linarith [hthis]
        rw [hfr]
      · have hrval : r.val = s - 1 := by omega
        have hre : r = ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ := Fin.ext hrval
        rw [hre, hlast]
        have hkone : k = 1 := by omega
        rw [hkone]
        norm_num

/-- For integer-valued levels, the sum of squared jumps down to zero is at least the
initial level.  Upward jumps and jumps down by more than one make the inequality strict. -/
theorem nat_sub_sq_ge_sub (a b : ℕ) :
    (a : ℝ) - b ≤ ((a : ℝ) - b) ^ 2 := by
  by_cases hab : a ≤ b
  · have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
    nlinarith [sq_nonneg ((a : ℝ) - b)]
  · have habN : b + 1 ≤ a := by omega
    have habR : (b : ℝ) + 1 ≤ a := by exact_mod_cast habN
    nlinarith [sq_nonneg ((a : ℝ) - b - 1)]

theorem nat_path_energy_ge_start {m : ℕ} (L : Fin (m + 1) → ℕ) :
    (L 0 : ℝ) ≤
      (∑ r : Fin m, ((L r.castSucc : ℝ) - L r.succ) ^ 2) +
        (L (Fin.last m) : ℝ) ^ 2 := by
  have hedges :
      ∑ r : Fin m, ((L r.castSucc : ℝ) - L r.succ) ≤
        ∑ r : Fin m, ((L r.castSucc : ℝ) - L r.succ) ^ 2 := by
    exact Finset.sum_le_sum fun r _ => nat_sub_sq_ge_sub (L r.castSucc) (L r.succ)
  have hlast : (L (Fin.last m) : ℝ) ≤ (L (Fin.last m) : ℝ) ^ 2 := by
    have hnat : L (Fin.last m) = 0 ∨ 1 ≤ L (Fin.last m) := by omega
    rcases hnat with h | h
    · simp [h]
    · have hR : (1 : ℝ) ≤ L (Fin.last m) := by exact_mod_cast h
      nlinarith
  have htel := sum_fin_succ_sub (fun r : Fin (m + 1) => (L r : ℝ))
  linarith

/-- Equality in `nat_path_energy_ge_start` forces every jump to stay level or descend by
exactly one integer level. -/
theorem nat_path_energy_eq_imp_step {m : ℕ} (L : Fin (m + 1) → ℕ)
    (heq :
      (∑ r : Fin m, ((L r.castSucc : ℝ) - L r.succ) ^ 2) +
          (L (Fin.last m) : ℝ) ^ 2 = L 0) :
    ∀ r : Fin m, L r.castSucc = L r.succ ∨ L r.castSucc = L r.succ + 1 := by
  intro r
  let gap : Fin m → ℝ := fun t =>
    ((L t.castSucc : ℝ) - L t.succ) ^ 2 -
      ((L t.castSucc : ℝ) - L t.succ)
  have hgap0 : ∀ t, 0 ≤ gap t := by
    intro t
    exact sub_nonneg.mpr (nat_sub_sq_ge_sub (L t.castSucc) (L t.succ))
  have hlast0 : 0 ≤ (L (Fin.last m) : ℝ) ^ 2 - L (Fin.last m) := by
    have hnat : L (Fin.last m) = 0 ∨ 1 ≤ L (Fin.last m) := by omega
    rcases hnat with h | h
    · simp [h]
    · have hR : (1 : ℝ) ≤ L (Fin.last m) := by exact_mod_cast h
      nlinarith
  have htel := sum_fin_succ_sub (fun t : Fin (m + 1) => (L t : ℝ))
  have htel' :
      (∑ t : Fin m, (L t.castSucc : ℝ)) - (∑ t : Fin m, (L t.succ : ℝ)) =
        (L 0 : ℝ) - L (Fin.last m) := by
    rw [← Finset.sum_sub_distrib]
    exact htel
  have hsum0 : (∑ t, gap t) +
      ((L (Fin.last m) : ℝ) ^ 2 - L (Fin.last m)) = 0 := by
    simp only [gap, Finset.sum_sub_distrib]
    linarith [htel']
  have hrle : gap r ≤ (∑ t, gap t) +
      ((L (Fin.last m) : ℝ) ^ 2 - L (Fin.last m)) := by
    exact le_add_of_le_of_nonneg
      (Finset.single_le_sum (fun t _ => hgap0 t) (Finset.mem_univ r)) hlast0
  have hrgap : gap r = 0 := by
    rw [hsum0] at hrle
    exact le_antisymm hrle (hgap0 r)
  dsimp [gap] at hrgap
  have hsquare : ((L r.castSucc : ℝ) - L r.succ) ^ 2 =
      (L r.castSucc : ℝ) - L r.succ := by linarith
  have hz : (L r.castSucc : ℝ) - L r.succ = 0 ∨
      (L r.castSucc : ℝ) - L r.succ = 1 := by
    apply eq_zero_or_one_of_sq_eq_self
    simpa only [pow_two] using hsquare
  rcases hz with hz | hz
  · left
    exact_mod_cast (sub_eq_zero.mp hz)
  · right
    have hzNat : L r.castSucc = 1 + L r.succ := by
      exact_mod_cast (eq_add_of_sub_eq hz)
    omega

theorem nat_path_energy_eq_imp_last {m : ℕ} (L : Fin (m + 1) → ℕ)
    (heq :
      (∑ r : Fin m, ((L r.castSucc : ℝ) - L r.succ) ^ 2) +
          (L (Fin.last m) : ℝ) ^ 2 = L 0) :
    L (Fin.last m) = 0 ∨ L (Fin.last m) = 1 := by
  have hsteps := nat_path_energy_eq_imp_step L heq
  have hedges :
      ∑ r : Fin m, ((L r.castSucc : ℝ) - L r.succ) ^ 2 =
        ∑ r : Fin m, ((L r.castSucc : ℝ) - L r.succ) := by
    apply Finset.sum_congr rfl
    intro r _
    rcases hsteps r with h | h
    · rw [h]
      norm_num
    · have hcast : (L r.castSucc : ℝ) = L r.succ + 1 := by exact_mod_cast h
      rw [hcast]
      ring
  have htel := sum_fin_succ_sub (fun r : Fin (m + 1) => (L r : ℝ))
  have hsquare : (L (Fin.last m) : ℝ) ^ 2 = L (Fin.last m) := by
    rw [hedges] at heq
    linarith
  have h01 : (L (Fin.last m) : ℝ) = 0 ∨ (L (Fin.last m) : ℝ) = 1 := by
    apply eq_zero_or_one_of_sq_eq_self
    simpa only [pow_two] using hsquare
  rcases h01 with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast h

/-- Enumerating a nonempty positive-edge list whose last vertex has positive defect gives a
positive weighted path. -/
theorem positive_chain_to_weighted_path
    (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (a : Fin s) (tail : List (Fin s))
    (hchain : (a :: tail).IsChain
      (fun u w : Fin s => 0 < Q (u : ℕ) (w : ℕ)))
    (hb : 0 < SSP.bVec s Q ((a :: tail).getLast (List.cons_ne_nil _ _) : ℕ)) :
    ∃ m, ∃ p : Fin (m + 1) → Fin s,
      List.ofFn p = a :: tail ∧ 0 < SSP.pathWeight s Q m p := by
  let p : Fin (tail.length + 1) → Fin s := (a :: tail).get
  have hprod : 0 < SSP.pathProd s Q tail.length p := by
    apply Finset.prod_pos
    intro r _
    have hedge := hchain.getElem r.val (by
      simp only [List.length_cons]
      omega)
    change 0 < Q (p r.castSucc : ℕ) (p r.succ : ℕ)
    change 0 < Q ((a :: tail)[r.val] : Fin s) ((a :: tail)[r.val + 1] : Fin s)
    exact hedge
  have hof : List.ofFn p = a :: tail := List.ofFn_get (a :: tail)
  have hlast : p (Fin.last tail.length) =
      (a :: tail).getLast (List.cons_ne_nil _ _) := by
    have hopt := getLast?_ofFn_succ p
    rw [hof, List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil _ _)] at hopt
    exact Option.some.inj hopt.symm
  refine ⟨tail.length, p, hof, ?_⟩
  unfold SSP.pathWeight
  rw [hlast]
  exact mul_pos hprod hb

/-- Once an ordering has positive consecutive edges from its first state, any further positive
edge can be embedded in a positive absorbing path beginning at that first state. -/
theorem exists_positive_path_through_edge
    (s : ℕ) (Q : ℕ → ℕ → ℝ) (theta C : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hC0 : 0 ≤ C)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hdecay : ∀ k, ∀ a < s,
      SSP.matVec s (SSP.matPow s Q k) SSP.eVec a ≤ C * theta ^ k)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (v : Fin s ≃ Fin s)
    (hforward : ∀ (r : Fin s) (hr : r.val + 1 < s),
      0 < Q (v r : ℕ) (v ⟨r.val + 1, hr⟩ : ℕ))
    (r c : Fin s) (hedge : 0 < Q (v r : ℕ) (v c : ℕ)) :
    ∃ m, ∃ p : Fin (m + 1) → Fin s, ∃ k : Fin m,
      p 0 = v ⟨0, lt_of_le_of_lt (Nat.zero_le _) r.isLt⟩ ∧
        0 < SSP.pathWeight s Q m p ∧
        p k.castSucc = v r ∧ p k.succ = v c := by
  obtain ⟨m, p, hp0, hpw⟩ := exists_positive_absorbing_path s Q theta C
    htheta0 htheta1 hC0 hQ hdecay hsub (v c : ℕ) (v c).isLt
  obtain ⟨l, _hlnodup, hlchain, hlhead, ⟨z, hllast, hbpos⟩, _hllen⟩ :=
    positive_path_has_simple_route s Q hQ hsub (v c : ℕ) m p hp0 hpw
  have hrle : r.val + 1 ≤ s := by omega
  let pref : List (Fin s) := List.ofFn
    (fun t : Fin (r.val + 1) => v ⟨t.val, lt_of_lt_of_le t.isLt hrle⟩)
  have hpref_ne : pref ≠ [] := by simp [pref]
  have hpref_chain : pref.IsChain
      (fun a b : Fin s => 0 < Q (a : ℕ) (b : ℕ)) := by
    rw [List.isChain_iff_getElem]
    intro j hj
    simp only [pref, List.length_ofFn] at hj ⊢
    have hjr : j + 1 < s := lt_of_lt_of_le hj hrle
    simpa only [List.getElem_ofFn] using
      hforward ⟨j, by omega⟩ hjr
  have hpref_head : pref.head? = some (v ⟨0, by omega⟩) := by simp [pref]
  have hpref_last : pref.getLast? = some (v r) := by
    rw [getLast?_ofFn_succ]
    congr 2
  have hfull_chain : (pref ++ l).IsChain
      (fun a b : Fin s => 0 < Q (a : ℕ) (b : ℕ)) := by
    apply hpref_chain.append hlchain
    intro x hx y hy
    rw [hpref_last] at hx
    rw [hlhead] at hy
    simp only [Option.mem_def, Option.some.injEq] at hx hy
    subst x
    subst y
    exact hedge
  have hfull_ne : pref ++ l ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    simp [pref] at this
  have hfull_last : (pref ++ l).getLast? = some z := by
    rw [List.getLast?_append_of_ne_nil]
    · exact hllast
    · intro hnil
      simp [hnil] at hlhead
  have hblast : 0 < SSP.bVec s Q ((pref ++ l).getLast hfull_ne : ℕ) := by
    rw [List.getLast?_eq_getLast_of_ne_nil hfull_ne] at hfull_last
    have hz : (pref ++ l).getLast hfull_ne = z := Option.some.inj hfull_last
    simpa [hz] using hbpos
  cases hfull : pref ++ l with
  | nil => exact (hfull_ne hfull).elim
  | cons a tail =>
      have hchain' : (a :: tail).IsChain
          (fun u w : Fin s => 0 < Q (u : ℕ) (w : ℕ)) := by
        rw [← hfull]
        exact hfull_chain
      have hb' : 0 < SSP.bVec s Q ((a :: tail).getLast (List.cons_ne_nil _ _) : ℕ) := by
        have hget : (a :: tail).getLast (List.cons_ne_nil _ _) =
            (pref ++ l).getLast hfull_ne := by
          apply List.getLast_congr
          exact hfull.symm
        simpa [hget] using hblast
      obtain ⟨n, q, hqof, hqw⟩ :=
        positive_chain_to_weighted_path s Q hQ hsub a tail hchain' hb'
      have hlen : n + 1 = (pref ++ l).length := by
        calc
          n + 1 = (List.ofFn q).length := by simp
          _ = (a :: tail).length := congrArg List.length hqof
          _ = (pref ++ l).length := congrArg List.length hfull.symm
      have hlne : l ≠ [] := by
        intro hnil
        simp [hnil] at hlhead
      have hrn : r.val < n := by
        simp only [pref, List.length_append, List.length_ofFn] at hlen
        have : 0 < l.length := by
          cases l with
          | nil => exact (hlne rfl).elim
          | cons b rest => simp
        omega
      let k : Fin n := ⟨r.val, hrn⟩
      have hq0 : q 0 = v ⟨0, by omega⟩ := by
        have hheadq : (List.ofFn q).head? = some (q 0) := by simp
        rw [hqof, ← hfull, List.head?_append_of_ne_nil _ hpref_ne, hpref_head] at hheadq
        exact Option.some.inj hheadq.symm
      have hqk : q k.castSucc = v r := by
        have hget := congrArg (fun xs : List (Fin s) => xs[r.val]?) hqof
        rw [← hfull] at hget
        have hleft : r.val < (List.ofFn q).length := by simp; omega
        have hright : r.val < (pref ++ l).length := by rw [← hlen]; omega
        rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] at hget
        have heq := Option.some.inj hget
        change (List.ofFn q).get ⟨r.val, hleft⟩ =
          (pref ++ l).get ⟨r.val, hright⟩ at heq
        rw [List.get_ofFn] at heq
        have hrpref : r.val < pref.length := by simp [pref]
        have happ : (pref ++ l).get ⟨r.val, hright⟩ = pref.get ⟨r.val, hrpref⟩ := by
          simp [List.getElem_append, hrpref]
        have hpval : pref.get ⟨r.val, hrpref⟩ = v r := by
          simp only [pref, List.get_ofFn]
          congr 1
        rw [happ, hpval] at heq
        simpa [k] using heq
      have hqks : q k.succ = v c := by
        have hget := congrArg (fun xs : List (Fin s) => xs[r.val + 1]?) hqof
        rw [← hfull] at hget
        have hleft : r.val + 1 < (List.ofFn q).length := by simp; omega
        have hright : r.val + 1 < (pref ++ l).length := by rw [← hlen]; omega
        rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] at hget
        have heq := Option.some.inj hget
        change (List.ofFn q).get ⟨r.val + 1, hleft⟩ =
          (pref ++ l).get ⟨r.val + 1, hright⟩ at heq
        rw [List.get_ofFn] at heq
        have hheadl : l[0]? = some (v c) := by
          simpa [List.head?_eq_getElem?] using hlhead
        have hlpos : 0 < l.length := by
          cases l with
          | nil => exact (hlne rfl).elim
          | cons b rest => simp
        have hl0 : l[0]'hlpos = v c := by
          rw [List.getElem?_eq_getElem hlpos] at hheadl
          exact Option.some.inj hheadl
        have happ : (pref ++ l).get ⟨r.val + 1, hright⟩ = l.get ⟨0, hlpos⟩ := by
          simp [List.getElem_append, pref]
        rw [happ] at heq
        have heq' := heq.trans hl0
        simpa [k] using heq'
      exact ⟨n, q, k, hq0, hqw, hqk, hqks⟩

/-- Under equality, every positive transition in the rigid ordering is either a self-loop or
the edge to the immediately following phase. -/
theorem positive_edge_is_self_or_next
    (s : ℕ) (Q : ℕ → ℕ → ℝ) (theta C : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hC0 : 0 ≤ C)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hdecay : ∀ k, ∀ a < s,
      SSP.matVec s (SSP.matPow s Q k) SSP.eVec a ≤ C * theta ^ k)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (hs : 0 < s) (i : ℕ) (hi : i < s)
    (heq : (SSP.xVec s Q i) ^ 2 =
      (2 * (s : ℝ) / ((s : ℝ) + 1)) * SSP.yVec s Q i) :
    ∃ v : Fin s ≃ Fin s,
      (v ⟨0, hs⟩ : ℕ) = i ∧
      (∀ r : Fin s, SSP.xVec s Q (v r : ℕ) =
        ((s - r.val : ℕ) : ℝ) * (SSP.xVec s Q i / s)) ∧
      (∀ (r : Fin s) (hr : r.val + 1 < s),
        0 < Q (v r : ℕ) (v ⟨r.val + 1, hr⟩ : ℕ)) ∧
      0 < SSP.bVec s Q (v ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ : ℕ) ∧
      ∀ r c : Fin s, 0 < Q (v r : ℕ) (v c : ℕ) → c = r ∨ c.val = r.val + 1 := by
  obtain ⟨v, hv0, hgaps, hlast, hforward, hbpos⟩ :=
    exists_rigid_ordering s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub hs i hi heq
  let A : ℝ := SSP.xVec s Q i
  let g : ℝ := A / s
  have hA : 0 < A := by
    have hx := SSP.xVec_fixed_point s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub i hi
    have hsum0 : 0 ≤ ∑ l ∈ range s, Q i l * SSP.xVec s Q l := by
      apply Finset.sum_nonneg
      intro a _
      exact mul_nonneg (hQ _ _) (SSP.xVec_nonneg s Q hQ _)
    dsimp [A]
    linarith
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hg : 0 < g := by dsimp [g]; positivity
  have hxlevels : ∀ r : Fin s,
      SSP.xVec s Q (v r : ℕ) = ((s - r.val : ℕ) : ℝ) * g := by
    apply eq_nat_sub_mul_of_equal_gaps hs
    · intro r hr
      simpa only [g, A] using hgaps r hr
    · simpa only [g, A] using hlast
  refine ⟨v, hv0, hxlevels, hforward, hbpos, ?_⟩
  intro r c hedge
  obtain ⟨m, p, k, hp0, hpw, hpkr, hpkc⟩ :=
    exists_positive_path_through_edge s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub
      v hforward r c hedge
  have hp0i : (p 0 : ℕ) = i := by rw [hp0, hv0]
  have henergy := pathEnergy_eq_of_component_eq s Q theta C htheta0 htheta1 hC0 hQ
    hdecay hsub hs i hi heq m p hp0i hpw
  let L : Fin (m + 1) → ℕ := fun t => s - (v.symm (p t)).val
  have hxp : ∀ t : Fin (m + 1), SSP.xVec s Q (p t : ℕ) = (L t : ℝ) * g := by
    intro t
    have hx := hxlevels (v.symm (p t))
    simpa only [L, Equiv.apply_symm_apply] using hx
  have hsumfactor :
      ∑ t : Fin m,
          (SSP.xVec s Q (p t.succ : ℕ) - SSP.xVec s Q (p t.castSucc : ℕ)) ^ 2 =
        g ^ 2 * ∑ t : Fin m, ((L t.castSucc : ℝ) - L t.succ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [hxp, hxp]
    ring
  have hlastfactor : SSP.xVec s Q (p (Fin.last m) : ℕ) ^ 2 =
      g ^ 2 * (L (Fin.last m) : ℝ) ^ 2 := by
    rw [hxp]
    ring
  have hAeq : A = (s : ℝ) * g := by
    dsimp [g]
    field_simp
  have hrhs : A ^ 2 / s = (s : ℝ) * g ^ 2 := by
    rw [hAeq]
    field_simp
  have hnatenergy :
      (∑ t : Fin m, ((L t.castSucc : ℝ) - L t.succ) ^ 2) +
          (L (Fin.last m) : ℝ) ^ 2 = s := by
    unfold SSP.pathEnergy at henergy
    rw [hsumfactor, hlastfactor, hrhs] at henergy
    have hg2 : 0 < g ^ 2 := sq_pos_of_pos hg
    nlinarith
  have hL0 : L 0 = s := by
    dsimp [L]
    rw [hp0]
    simp
  have hnatenergy' :
      (∑ t : Fin m, ((L t.castSucc : ℝ) - L t.succ) ^ 2) +
          (L (Fin.last m) : ℝ) ^ 2 = L 0 := by
    simpa [hL0] using hnatenergy
  have hstep := nat_path_energy_eq_imp_step L hnatenergy' k
  have hLr : L k.castSucc = s - r.val := by
    dsimp [L]
    rw [hpkr]
    simp
  have hLc : L k.succ = s - c.val := by
    dsimp [L]
    rw [hpkc]
    simp
  rw [hLr, hLc] at hstep
  rcases hstep with hsame | hnext
  · left
    apply Fin.ext
    omega
  · right
    omega

/-- For a positive sharp path expressed in the rigid ordering, the terminal transient state
has integer level one, hence is the last phase. -/
theorem positive_path_terminal_rank_one
    (s : ℕ) (Q : ℕ → ℕ → ℝ) (theta C : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hC0 : 0 ≤ C)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hdecay : ∀ k, ∀ a < s,
      SSP.matVec s (SSP.matPow s Q k) SSP.eVec a ≤ C * theta ^ k)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (hs : 0 < s) (i : ℕ) (hi : i < s)
    (heq : (SSP.xVec s Q i) ^ 2 =
      (2 * (s : ℝ) / ((s : ℝ) + 1)) * SSP.yVec s Q i)
    (v : Fin s ≃ Fin s) (hv0 : (v ⟨0, hs⟩ : ℕ) = i)
    (hxlevels : ∀ r : Fin s,
      SSP.xVec s Q (v r : ℕ) =
        ((s - r.val : ℕ) : ℝ) * (SSP.xVec s Q i / s))
    (m : ℕ) (p : Fin (m + 1) → Fin s)
    (hp0 : p 0 = v ⟨0, hs⟩) (hpw : 0 < SSP.pathWeight s Q m p) :
    s - (v.symm (p (Fin.last m))).val = 1 := by
  let A : ℝ := SSP.xVec s Q i
  let g : ℝ := A / s
  have hA : 0 < A := by
    have hx := SSP.xVec_fixed_point s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub i hi
    have hsum0 : 0 ≤ ∑ l ∈ range s, Q i l * SSP.xVec s Q l := by
      apply Finset.sum_nonneg
      intro a _
      exact mul_nonneg (hQ _ _) (SSP.xVec_nonneg s Q hQ _)
    dsimp [A]
    linarith
  have hg : 0 < g := by
    dsimp [g]
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    positivity
  have hp0i : (p 0 : ℕ) = i := by rw [hp0, hv0]
  have henergy := pathEnergy_eq_of_component_eq s Q theta C htheta0 htheta1 hC0 hQ
    hdecay hsub hs i hi heq m p hp0i hpw
  let L : Fin (m + 1) → ℕ := fun t => s - (v.symm (p t)).val
  have hxp : ∀ t : Fin (m + 1), SSP.xVec s Q (p t : ℕ) = (L t : ℝ) * g := by
    intro t
    have hx := hxlevels (v.symm (p t))
    simpa only [L, g, A, Equiv.apply_symm_apply] using hx
  have hsumfactor :
      ∑ t : Fin m,
          (SSP.xVec s Q (p t.succ : ℕ) - SSP.xVec s Q (p t.castSucc : ℕ)) ^ 2 =
        g ^ 2 * ∑ t : Fin m, ((L t.castSucc : ℝ) - L t.succ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [hxp, hxp]
    ring
  have hlastfactor : SSP.xVec s Q (p (Fin.last m) : ℕ) ^ 2 =
      g ^ 2 * (L (Fin.last m) : ℝ) ^ 2 := by
    rw [hxp]
    ring
  have hAeq : A = (s : ℝ) * g := by
    dsimp [g]
    field_simp
  have hrhs : A ^ 2 / s = (s : ℝ) * g ^ 2 := by
    rw [hAeq]
    field_simp
  have hnatenergy :
      (∑ t : Fin m, ((L t.castSucc : ℝ) - L t.succ) ^ 2) +
          (L (Fin.last m) : ℝ) ^ 2 = s := by
    unfold SSP.pathEnergy at henergy
    rw [hsumfactor, hlastfactor, hrhs] at henergy
    have hg2 : 0 < g ^ 2 := sq_pos_of_pos hg
    nlinarith
  have hL0 : L 0 = s := by
    dsimp [L]
    rw [hp0]
    simp
  have hnatenergy' :
      (∑ t : Fin m, ((L t.castSucc : ℝ) - L t.succ) ^ 2) +
          (L (Fin.last m) : ℝ) ^ 2 = L 0 := by
    simpa [hL0] using hnatenergy
  have hlast01 := nat_path_energy_eq_imp_last L hnatenergy'
  rcases hlast01 with hzero | hone
  · have hpos : 0 < L (Fin.last m) := by
      dsimp [L]
      omega
    omega
  · exact hone

/-- In the rigid ordering, a positive absorption defect can occur only at the last phase. -/
theorem equality_ordering_support
    (s : ℕ) (Q : ℕ → ℕ → ℝ) (theta C : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hC0 : 0 ≤ C)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hdecay : ∀ k, ∀ a < s,
      SSP.matVec s (SSP.matPow s Q k) SSP.eVec a ≤ C * theta ^ k)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (hs : 0 < s) (i : ℕ) (hi : i < s)
    (heq : (SSP.xVec s Q i) ^ 2 =
      (2 * (s : ℝ) / ((s : ℝ) + 1)) * SSP.yVec s Q i) :
    ∃ v : Fin s ≃ Fin s,
      (v ⟨0, hs⟩ : ℕ) = i ∧
      (∀ r : Fin s, SSP.xVec s Q (v r : ℕ) =
        ((s - r.val : ℕ) : ℝ) * (SSP.xVec s Q i / s)) ∧
      (∀ r c : Fin s, 0 < Q (v r : ℕ) (v c : ℕ) → c = r ∨ c.val = r.val + 1) ∧
      (∀ r : Fin s, 0 < SSP.bVec s Q (v r : ℕ) → r.val = s - 1) := by
  obtain ⟨v, hv0, hxlevels, hforward, _hbLast, hedges⟩ :=
    positive_edge_is_self_or_next s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub
      hs i hi heq
  refine ⟨v, hv0, hxlevels, hedges, ?_⟩
  intro r hb
  let p : Fin (r.val + 1) → Fin s :=
    fun t => v ⟨t.val, lt_of_lt_of_le t.isLt (by omega : r.val + 1 ≤ s)⟩
  have hp0 : p 0 = v ⟨0, hs⟩ := by
    apply congrArg v
    apply Fin.ext
    rfl
  have hplast : p (Fin.last r.val) = v r := by
    apply congrArg v
    apply Fin.ext
    simp
  have hprod : 0 < SSP.pathProd s Q r.val p := by
    apply Finset.prod_pos
    intro t _
    change 0 < Q (p t.castSucc : ℕ) (p t.succ : ℕ)
    have ht : t.val + 1 < s := by omega
    change 0 < Q (v ⟨t.val, by omega⟩ : ℕ) (v ⟨t.val + 1, ht⟩ : ℕ)
    exact hforward ⟨t.val, by omega⟩ ht
  have hpw : 0 < SSP.pathWeight s Q r.val p := by
    unfold SSP.pathWeight
    rw [hplast]
    exact mul_pos hprod hb
  have hterminal := positive_path_terminal_rank_one s Q theta C htheta0 htheta1 hC0 hQ
    hdecay hsub hs i hi heq v hv0 hxlevels r.val p hp0 hpw
  rw [hplast, Equiv.symm_apply_apply] at hterminal
  omega

theorem sum_eq_two_of_support {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (f : alpha → ℝ) (a b : alpha) (hab : a ≠ b)
    (hsupp : ∀ c, c ≠ a → c ≠ b → f c = 0) :
    ∑ c, f c = f a + f b := by
  have hbmem : b ∈ (Finset.univ : Finset alpha).erase a := by
    exact Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  have hrest : ∑ c ∈ (Finset.univ : Finset alpha).erase a, f c = f b := by
    exact Finset.sum_eq_single_of_mem b hbmem (fun c hc hcb =>
      hsupp c (Finset.ne_of_mem_erase hc) hcb)
  rw [← Finset.sum_erase_add (Finset.univ : Finset alpha) f (Finset.mem_univ a), hrest]
  ring

theorem sum_eq_one_of_support {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (f : alpha → ℝ) (a : alpha) (hsupp : ∀ c, c ≠ a → f c = 0) :
    ∑ c, f c = f a := by
  exact Finset.sum_eq_single a (fun c _ hca => hsupp c hca) (by simp)

/-- The reverse equality case: a sharp component forces the common-rate serial chain, up to
relabeling of the transient states. -/
theorem isSerialErlang_of_component_eq
    (s : ℕ) (Q : ℕ → ℕ → ℝ) (theta C : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hC0 : 0 ≤ C)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hdecay : ∀ k, ∀ a < s,
      SSP.matVec s (SSP.matPow s Q k) SSP.eVec a ≤ C * theta ^ k)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (hs : 0 < s) (i : ℕ) (hi : i < s)
    (heq : (SSP.xVec s Q i) ^ 2 =
      (2 * (s : ℝ) / ((s : ℝ) + 1)) * SSP.yVec s Q i) :
    IsSerialErlang hs (fun a b : Fin s => Q (a : ℕ) (b : ℕ)) ⟨i, hi⟩ := by
  classical
  obtain ⟨v, hv0, hxlevels, hedges, hbSupport⟩ :=
    equality_ordering_support s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub
      hs i hi heq
  let A : ℝ := SSP.xVec s Q i
  let g : ℝ := A / s
  let lam : ℝ := g⁻¹
  have hA : 0 < A := by
    have hx := SSP.xVec_fixed_point s Q theta C htheta0 htheta1 hC0 hQ hdecay hsub i hi
    have hsum0 : 0 ≤ ∑ l ∈ range s, Q i l * SSP.xVec s Q l := by
      apply Finset.sum_nonneg
      intro a _
      exact mul_nonneg (hQ _ _) (SSP.xVec_nonneg s Q hQ _)
    dsimp [A]
    linarith
  have hg : 0 < g := by
    dsimp [g]
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    positivity
  have hlam0 : 0 < lam := by dsimp [lam]; positivity
  have hzero_of_outside : ∀ (r c : Fin s), c ≠ r → c.val ≠ r.val + 1 →
      Q (v r : ℕ) (v c : ℕ) = 0 := by
    intro r c hcr hcnext
    apply le_antisymm (le_of_not_gt ?_) (hQ _ _)
    intro hpos
    rcases hedges r c hpos with h | h
    · exact hcr h
    · exact hcnext h
  have hinter : ∀ (r : Fin s) (hr : r.val + 1 < s),
      Q (v r : ℕ) (v r : ℕ) = 1 - lam ∧
      Q (v r : ℕ) (v ⟨r.val + 1, hr⟩ : ℕ) = lam := by
    intro r hr
    let rn : Fin s := ⟨r.val + 1, hr⟩
    have hrne : r ≠ rn := by intro h; have := congrArg Fin.val h; simp [rn] at this
    have hsupp : ∀ c : Fin s, c ≠ r → c ≠ rn →
        Q (v r : ℕ) (v c : ℕ) = 0 := by
      intro c hcr hcn
      apply hzero_of_outside r c hcr
      intro hcval
      apply hcn
      exact Fin.ext hcval
    have hrowsum : ∑ l ∈ range s, Q (v r : ℕ) l =
        Q (v r : ℕ) (v r : ℕ) + Q (v r : ℕ) (v rn : ℕ) := by
      rw [← Fin.sum_univ_eq_sum_range (fun l => Q (v r : ℕ) l) s]
      rw [← Equiv.sum_comp v]
      exact sum_eq_two_of_support (fun c : Fin s => Q (v r : ℕ) (v c : ℕ))
        r rn hrne hsupp
    have hb0 : SSP.bVec s Q (v r : ℕ) = 0 := by
      apply le_antisymm (le_of_not_gt ?_)
        (SSP.bVec_nonneg s Q hsub _ (v r).isLt)
      intro hbpos
      have := hbSupport r hbpos
      omega
    have hqsum : Q (v r : ℕ) (v r : ℕ) + Q (v r : ℕ) (v rn : ℕ) = 1 := by
      unfold SSP.bVec at hb0
      rw [hrowsum] at hb0
      linarith
    have hweighted : ∑ l ∈ range s, Q (v r : ℕ) l * SSP.xVec s Q l =
        Q (v r : ℕ) (v r : ℕ) * SSP.xVec s Q (v r : ℕ) +
        Q (v r : ℕ) (v rn : ℕ) * SSP.xVec s Q (v rn : ℕ) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun l => Q (v r : ℕ) l * SSP.xVec s Q l) s]
      rw [← Equiv.sum_comp v]
      apply sum_eq_two_of_support
        (fun c : Fin s => Q (v r : ℕ) (v c : ℕ) * SSP.xVec s Q (v c : ℕ))
        r rn hrne
      intro c hcr hcn
      rw [hsupp c hcr hcn, zero_mul]
    have hxfix := SSP.xVec_fixed_point s Q theta C htheta0 htheta1 hC0 hQ hdecay
      hsub (v r : ℕ) (v r).isLt
    rw [hweighted] at hxfix
    have hgap : SSP.xVec s Q (v r : ℕ) - SSP.xVec s Q (v rn : ℕ) = g := by
      rw [hxlevels r, hxlevels rn]
      dsimp [g, A, rn]
      have hnat : s - r.val = (s - (r.val + 1)) + 1 := by omega
      rw [hnat, Nat.cast_add]
      norm_num
      ring
    have hnextmul : Q (v r : ℕ) (v rn : ℕ) * g = 1 := by
      rw [← hgap]
      linear_combination hxfix + SSP.xVec s Q (v r : ℕ) * hqsum
    have hnext : Q (v r : ℕ) (v rn : ℕ) = lam := by
      dsimp [lam]
      exact eq_inv_of_mul_eq_one_left hnextmul
    exact ⟨by rw [← hnext]; linarith, hnext⟩
  let last : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
  have hlastSupp : ∀ c : Fin s, c ≠ last → Q (v last : ℕ) (v c : ℕ) = 0 := by
    intro c hcl
    apply hzero_of_outside last c hcl
    dsimp [last]
    omega
  have hlastWeighted :
      ∑ l ∈ range s, Q (v last : ℕ) l * SSP.xVec s Q l =
        Q (v last : ℕ) (v last : ℕ) * SSP.xVec s Q (v last : ℕ) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun l => Q (v last : ℕ) l * SSP.xVec s Q l) s]
    rw [← Equiv.sum_comp v]
    apply sum_eq_one_of_support
    intro c hcl
    rw [hlastSupp c hcl, zero_mul]
  have hlastx : SSP.xVec s Q (v last : ℕ) = g := by
    rw [hxlevels last]
    have hone : s - last.val = 1 := by dsimp [last]; omega
    rw [hone]
    norm_num
    rfl
  have hlastfix := SSP.xVec_fixed_point s Q theta C htheta0 htheta1 hC0 hQ hdecay
    hsub (v last : ℕ) (v last).isLt
  rw [hlastWeighted, hlastx] at hlastfix
  have hlastdiag : Q (v last : ℕ) (v last : ℕ) = 1 - lam := by
    dsimp [lam]
    apply (eq_sub_iff_add_eq).mpr
    field_simp
    nlinarith
  have hlam1 : lam ≤ 1 := by
    have := hQ (v last : ℕ) (v last : ℕ)
    rw [hlastdiag] at this
    linarith
  refine ⟨lam, hlam0, hlam1, v, ?_, ?_⟩
  · apply Fin.ext
    simpa using hv0
  · intro r c
    by_cases hcr : c = r
    · subst c
      rw [if_pos rfl]
      by_cases hr : r.val + 1 < s
      · exact (hinter r hr).1
      · have hre : r = last := by apply Fin.ext; dsimp [last]; omega
        simpa [hre] using hlastdiag
    · rw [if_neg hcr]
      by_cases hc : c.val = r.val + 1
      · rw [if_pos hc]
        have hr : r.val + 1 < s := by simpa [hc] using c.isLt
        have hce : c = ⟨r.val + 1, hr⟩ := Fin.ext hc
        subst c
        exact (hinter r hr).2
      · rw [if_neg hc]
        exact hzero_of_outside r c hcr hc

/-- The Neumann-series vectors agree with the two resolvent moments under the spectral-radius
hypothesis. -/
theorem xVec_eq_resolvent_apply
    (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hRho : spectralRadius ℂ ((SSP.toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (i : ℕ) (hi : i < s) :
    SSP.xVec s Q i =
      ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ))) ⟨i, hi⟩ := by
  rw [← SSP.rowSum_eq_xVec]
  unfold SSP.rowSum Matrix.mulVec dotProduct
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => SSP.Nmat s Q i j) s]
  apply Finset.sum_congr rfl
  intro j _
  rw [SSP.Nmat_eq_invMat s Q hRho i j hi j.isLt]
  simp only [SSP.invMat, dif_pos (⟨hi, j.isLt⟩ : i < s ∧ (j : ℕ) < s), mul_one]

theorem yVec_eq_resolvent_second_apply
    (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hRho : spectralRadius ℂ ((SSP.toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (i : ℕ) (hi : i < s) :
    SSP.yVec s Q i =
      ((1 - SSP.toMat s Q)⁻¹.mulVec
        ((1 - SSP.toMat s Q)⁻¹.mulVec (fun _ => (1 : ℝ)))) ⟨i, hi⟩ := by
  simp only [Matrix.mulVec, dotProduct, mul_one]
  unfold SSP.yVec SSP.xVec SSP.matVec
  simp only [SSP.eVec, mul_one]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => SSP.Nmat s Q i j * ∑ l ∈ range s, SSP.Nmat s Q j l) s]
  apply Finset.sum_congr rfl
  intro j _
  rw [SSP.Nmat_eq_invMat s Q hRho i j hi j.isLt]
  simp only [SSP.invMat, dif_pos (⟨hi, j.isLt⟩ : i < s ∧ (j : ℕ) < s)]
  rw [← Fin.sum_univ_eq_sum_range (fun l => SSP.Nmat s Q (j : ℕ) l) s]
  apply congrArg (fun z : ℝ => (1 - SSP.toMat s Q)⁻¹ ⟨i, hi⟩ j * z)
  apply Finset.sum_congr rfl
  intro l _
  rw [SSP.Nmat_eq_invMat s Q hRho j l j.isLt l.isLt]
  simp only [SSP.invMat,
    dif_pos (⟨j.isLt, l.isLt⟩ : (j : ℕ) < s ∧ (l : ℕ) < s), mul_one]

/-- **Equality characterization for the q-sequence component bound.** -/
theorem component_eq_iff_isSerialErlang
    (s : ℕ) (Q : ℕ → ℕ → ℝ)
    (hQ : ∀ a b, 0 ≤ Q a b)
    (hsub : ∀ a < s, ∑ b ∈ range s, Q a b ≤ 1)
    (hRho : spectralRadius ℂ ((SSP.toMat s Q).map (algebraMap ℝ ℂ)) < 1)
    (hs : 0 < s) (i : ℕ) (hi : i < s) :
    ((SSP.xVec s Q i) ^ 2 =
        (2 * (s : ℝ) / ((s : ℝ) + 1)) * SSP.yVec s Q i) ↔
      IsSerialErlang hs (SSP.toMat s Q) ⟨i, hi⟩ := by
  constructor
  · intro heq
    obtain ⟨theta, htheta0, htheta1, C, hC0, hdecay⟩ :=
      SSP.rowSum_decay_of_spectralRadius s Q hQ hRho
    exact isSerialErlang_of_component_eq s Q theta C htheta0 htheta1 hC0 hQ hdecay
      hsub hs i hi heq
  · intro hserial
    have hres := hserial.equality
    rw [xVec_eq_resolvent_apply s Q hRho i hi,
      yVec_eq_resolvent_second_apply s Q hRho i hi]
    exact hres

end SSP.QSequenceEquality
