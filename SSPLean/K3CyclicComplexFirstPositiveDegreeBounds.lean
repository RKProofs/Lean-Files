import SSPLean.K3CyclicComplexFirstDegreeBounds
import SSPLean.K3CyclicComplexFirstPositiveCoefficient

/-! # Structural degree bounds for the positive-m full compact certificate -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.PositiveCoeff

open Dense ComplexCoeff

theorem bounded_bone : Bounded bone 0 0 := by
  simp [bone, Bounded, brat]

theorem bounded_m : Bounded m 0 1 := by
  simpa [m] using (bounded_brat (1 / 3)).mul bounded_br

theorem bounded_z : Bounded z 1 2 := by
  have hthree : Bounded (brat 3) 0 2 :=
    (bounded_brat 3).mono (by omega) (by omega)
  have htwoR : Bounded (bmul (brat 2) br) 0 2 :=
    ((bounded_brat 2).mul bounded_br).mono (by omega) (by omega)
  have hr2 : Bounded (bpow br 2) 0 2 := by
    simpa using bounded_br.pow 2
  have hbracket :
      Bounded (bsub (bsub (brat 3) (bmul (brat 2) br)) (bpow br 2)) 0 2 :=
    (hthree.sub htwoR).sub hr2
  simpa [z] using
    (bounded_brat (1 / 12)).mul (bounded_btau.mul hbracket)

theorem derivativeTriple_bounded (n : ℕ) :
    Bounded (derivativeTriple n).1 (n / 2) n ∧
      Bounded (derivativeTriple n).2.1 ((n + 1) / 2) (n + 1) ∧
      Bounded (derivativeTriple n).2.2 ((n + 2) / 2) (n + 2) := by
  induction n with
  | zero =>
      simp only [derivativeTriple, initialTriple]
      have hmneg : Bounded (bneg m) 0 1 := bounded_m.neg
      have hm2 : Bounded (bpow m 2) 1 2 :=
        (bounded_m.pow 2).mono (by omega) (by omega)
      exact ⟨bounded_bone, hmneg, hm2⟩
  | succ n ih =>
      simp only [derivativeTriple, nextTriple]
      refine ⟨ih.2.1, ih.2.2, ?_⟩
      have htop : Bounded (derivativeTriple n).2.2
          ((n + 3) / 2) (n + 3) := ih.2.2.mono (by omega) (by omega)
      have hmiddle := bounded_z.mul ih.2.1
      have hbottom := bounded_z.mul ih.1
      exact (htop.sub (hmiddle.mono (by omega) (by omega))).add
        (hbottom.mono (by omega) (by omega))

theorem derivative_bounded (n : ℕ) :
    Bounded (derivativeTriple n).1 (n / 2) n :=
  (derivativeTriple_bounded n).1

theorem derivativeTableAux_spec (n : ℕ) :
    (derivativeTableAux n).1.reverse =
        (List.range n).map (fun k => (derivativeTriple k).1) ∧
      (derivativeTableAux n).2 = derivativeTriple n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      simp only [derivativeTableAux]
      rw [ih.2]
      constructor
      · rw [List.reverse_cons, ih.1, List.range_succ, List.map_append]
        simp
      · rfl

theorem derivativeTable_getD {count j : ℕ} (hj : j < count) :
    (derivativeTable count).getD j bzero = (derivativeTriple j).1 := by
  unfold derivativeTable
  rw [(derivativeTableAux_spec count).1,
    List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem curvatureCoefficientFrom_bounded {derivatives : List Bi} {N : ℕ}
    (hderivatives : ∀ j, j ≤ N →
      derivatives.getD j bzero = (derivativeTriple j).1) :
    Bounded (curvatureCoefficientFrom derivatives N) (N / 2) N := by
  unfold curvatureCoefficientFrom
  apply foldl_badd_bounded (bounded_bzero (N / 2) N)
  intro j hj
  have hjN : j ≤ N := Nat.le_of_lt_succ (List.mem_range.mp hj)
  rw [hderivatives j hjN, hderivatives (N - j) (Nat.sub_le N j)]
  have hp := (derivative_bounded j).mul (derivative_bounded (N - j))
  have hp' : Bounded
      (bmul (derivativeTriple j).1 (derivativeTriple (N - j)).1)
      (N / 2) N := hp.mono (by omega) (by omega)
  simpa using (bounded_brat (ComplexCoeff.kernel N j)).mul hp'

theorem powerTableUpTo_member {count : ℕ} (hcount : count ≤ order + 1)
    {p : Bi} (hp : p ∈ powerTableUpTo count) :
    Bounded p (order / 2) order := by
  simp only [powerTableUpTo, List.mem_map] at hp
  obtain ⟨N, hNmem, rfl⟩ := hp
  have hNlt : N < count := List.mem_range.mp hNmem
  have hN : N ≤ order := by omega
  have hcurv : Bounded
      (curvatureCoefficientFrom (derivativeTable count) N) (N / 2) N := by
    apply curvatureCoefficientFrom_bounded
    intro j hj
    exact derivativeTable_getD (by omega)
  exact ((bounded_brat ((10 : ℚ) ^ N / Nat.factorial N)).mul hcurv).mono
    (by omega) (by omega)

theorem timeBernPolyFrom_bounded {powers : List Bi} {k : ℕ}
    (hk : k < powers.length)
    (hpowers : ∀ p ∈ powers, Bounded p (order / 2) order) :
    Bounded (timeBernPolyFrom powers k) (order / 2) order := by
  unfold timeBernPolyFrom
  apply foldl_badd_bounded (bounded_bzero (order / 2) order)
  intro N hN
  have hNlt : N < powers.length := by
    have := List.mem_range.mp hN
    omega
  have hpower : Bounded (powers.getD N bzero) (order / 2) order := by
    apply hpowers
    rw [List.getD_eq_getElem _ _ hNlt]
    exact List.getElem_mem hNlt
  simpa using
    (bounded_brat ((Nat.choose k N : ℚ) / Nat.choose order N)).mul hpower

theorem timeBernPoly_bounded {k : ℕ} (hk : k ≤ order) :
    Bounded (timeBernPolyFrom (powerTableUpTo (k + 1)) k)
      (order / 2) order := by
  apply timeBernPolyFrom_bounded
  · simp [powerTableUpTo]
  · intro p hp
    exact powerTableUpTo_member (by omega) hp

theorem foldl_badd_congr {α : Type*} {l : List α} {f g : α → Bi}
    {acc : Bi} (h : ∀ a ∈ l, f a = g a) :
    l.foldl (fun p a => badd p (f a)) acc =
      l.foldl (fun p a => badd p (g a)) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih =>
      simp only [List.foldl_cons]
      rw [h a (by simp)]
      apply ih
      intro b hb
      exact h b (by simp [hb])

theorem curvatureCoefficientFrom_congr {d e : List Bi} {N : ℕ}
    (h : ∀ j, j ≤ N → d.getD j bzero = e.getD j bzero) :
    curvatureCoefficientFrom d N = curvatureCoefficientFrom e N := by
  unfold curvatureCoefficientFrom
  apply foldl_badd_congr
  intro j hj
  have hjN : j ≤ N := Nat.le_of_lt_succ (List.mem_range.mp hj)
  rw [h j hjN, h (N - j) (Nat.sub_le N j)]

theorem powerTableUpTo_getD_eq {a b N : ℕ}
    (hNa : N < a) (hNb : N < b) :
    (powerTableUpTo a).getD N bzero =
      (powerTableUpTo b).getD N bzero := by
  rw [List.getD_eq_getElem _ _ (by simp [powerTableUpTo]; omega),
    List.getD_eq_getElem _ _ (by simp [powerTableUpTo]; omega)]
  simp only [powerTableUpTo, List.getElem_map, List.getElem_range]
  congr 1
  apply curvatureCoefficientFrom_congr
  intro j hj
  rw [derivativeTable_getD (by omega), derivativeTable_getD (by omega)]

theorem timeBernPolyFrom_prefix_eq {a b k : ℕ}
    (hka : k < a) (hkb : k < b) :
    timeBernPolyFrom (powerTableUpTo a) k =
      timeBernPolyFrom (powerTableUpTo b) k := by
  unfold timeBernPolyFrom
  apply foldl_badd_congr
  intro N hN
  have hNk : N ≤ k := Nat.le_of_lt_succ (List.mem_range.mp hN)
  have hp := powerTableUpTo_getD_eq (a := a) (b := b) (N := N)
    (by omega) (by omega)
  rw [hp]

end SSP.K3CyclicComplex.PositiveCoeff
