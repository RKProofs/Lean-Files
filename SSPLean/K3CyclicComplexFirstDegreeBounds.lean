import Mathlib.Data.List.GetD
import SSPLean.K3CyclicComplexFirstCoefficient

/-! # Structural degree bounds for the complex first-start coefficients -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex

open Dense

namespace ComplexCoeff

def Bounded (p : Bi) (outer inner : ℕ) : Prop :=
  p.length ≤ outer + 1 ∧ ∀ row ∈ p, row.length ≤ inner + 1

theorem uadd_length (p q : Uni) :
    (uadd p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [uadd]
  | cons a p ih =>
      cases q with
      | nil => simp [uadd]
      | cons b q => simp [uadd, ih, Nat.succ_max_succ]

@[simp] theorem uscale_length (a : ℚ) (p : Uni) :
    (uscale a p).length = p.length := by simp [uscale]

theorem umul_length_le (p q : Uni) :
    (umul p q).length ≤ p.length + q.length - 1 := by
  induction p generalizing q with
  | nil => simp [umul]
  | cons a p ih =>
      cases q with
      | nil => simp [umul]
      | cons b q =>
          simp only [umul, uadd_length]
          simp only [uscale_length, List.length_cons]
          apply max_le
          · omega
          · cases p with
            | nil =>
                have hq : 1 ≤ (b :: q).length := by simp
                simp only [umul, List.length_nil]
                omega
            | cons c p =>
                have h := ih (b :: q)
                simp only [List.length_cons] at h ⊢
                omega

theorem badd_length (p q : Bi) :
    (badd p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [badd]
  | cons a p ih =>
      cases q with
      | nil => simp [badd]
      | cons b q => simp [badd, ih, Nat.succ_max_succ]

@[simp] theorem bscale_length (a : Uni) (p : Bi) :
    (bscale a p).length = p.length := by simp [bscale]

theorem bmul_length_le (p q : Bi) :
    (bmul p q).length ≤ p.length + q.length - 1 := by
  induction p generalizing q with
  | nil => simp [bmul]
  | cons a p ih =>
      cases q with
      | nil => simp [bmul]
      | cons b q =>
          simp only [bmul, badd_length]
          simp only [bscale_length, List.length_cons]
          apply max_le
          · omega
          · cases p with
            | nil =>
                have hq : 1 ≤ (b :: q).length := by simp
                simp only [bmul, List.length_nil]
                omega
            | cons c p =>
                have h := ih (b :: q)
                simp only [List.length_cons] at h ⊢
                omega

theorem rows_bounded_badd {p q : Bi} {n : ℕ}
    (hp : ∀ row ∈ p, row.length ≤ n)
    (hq : ∀ row ∈ q, row.length ≤ n) :
    ∀ row ∈ badd p q, row.length ≤ n := by
  induction p generalizing q with
  | nil => simpa [badd] using hq
  | cons a p ih =>
      cases q with
      | nil => simpa [badd] using hp
      | cons b q =>
          intro row hrow
          simp only [badd, List.mem_cons] at hrow
          rcases hrow with hrow | hrow
          · subst row
            rw [uadd_length]
            exact max_le (hp a (by simp)) (hq b (by simp))
          · exact ih (fun x hx => hp x (by simp [hx]))
              (fun x hx => hq x (by simp [hx])) row hrow

theorem rows_bounded_bscale {a : Uni} {p : Bi} {m n : ℕ}
    (ha : a.length ≤ m + 1)
    (hp : ∀ row ∈ p, row.length ≤ n + 1) :
    ∀ row ∈ bscale a p, row.length ≤ m + n + 1 := by
  intro row hrow
  simp only [bscale, List.mem_map] at hrow
  obtain ⟨q, hq, rfl⟩ := hrow
  have hmul := umul_length_le a q
  have hqLen := hp q hq
  omega

theorem rows_bounded_bmul {p q : Bi} {m n : ℕ}
    (hp : ∀ row ∈ p, row.length ≤ m + 1)
    (hq : ∀ row ∈ q, row.length ≤ n + 1) :
    ∀ row ∈ bmul p q, row.length ≤ m + n + 1 := by
  induction p with
  | nil => simp [bmul]
  | cons a p ih =>
      cases q with
      | nil => simp [bmul]
      | cons b q =>
          apply rows_bounded_badd
          · exact rows_bounded_bscale (hp a (by simp)) hq
          · intro row hrow
            simp only [List.mem_cons] at hrow
            rcases hrow with rfl | hrow
            · simp
            · exact ih (fun x hx => hp x (by simp [hx])) row hrow

theorem Bounded.mono {p : Bi} {outer inner outer' inner' : ℕ}
    (h : Bounded p outer inner) (ho : outer ≤ outer') (hi : inner ≤ inner') :
    Bounded p outer' inner' := by
  constructor
  · exact le_trans h.1 (Nat.add_le_add_right ho 1)
  · intro row hrow
    have := h.2 row hrow
    omega

theorem bounded_bzero (outer inner : ℕ) : Bounded bzero outer inner := by
  simp [Bounded, bzero]

theorem bounded_bone : Bounded bone 0 0 := by
  simp [Bounded, bone, brat]

theorem bounded_br : Bounded br 0 1 := by
  simp [Bounded, br]

theorem bounded_btau : Bounded btau 1 0 := by
  simp [Bounded, btau]

theorem Bounded.add {p q : Bi} {outer inner : ℕ}
    (hp : Bounded p outer inner) (hq : Bounded q outer inner) :
    Bounded (badd p q) outer inner := by
  constructor
  · rw [badd_length]
    exact max_le hp.1 hq.1
  · exact rows_bounded_badd hp.2 hq.2

theorem Bounded.mul {p q : Bi} {outerP innerP outerQ innerQ : ℕ}
    (hp : Bounded p outerP innerP) (hq : Bounded q outerQ innerQ) :
    Bounded (bmul p q) (outerP + outerQ) (innerP + innerQ) := by
  constructor
  · cases p with
    | nil => simp [bmul]
    | cons a p =>
        cases q with
        | nil => simp [bmul]
        | cons b q =>
            have hlen := bmul_length_le (a :: p) (b :: q)
            have hpLen := hp.1
            have hqLen := hq.1
            simp only [List.length_cons] at hpLen hqLen hlen ⊢
            omega
  · exact rows_bounded_bmul hp.2 hq.2

theorem bounded_brat (a : ℚ) : Bounded (brat a) 0 0 := by
  simp [Bounded, brat]

theorem Bounded.neg {p : Bi} {outer inner : ℕ}
    (hp : Bounded p outer inner) : Bounded (bneg p) outer inner := by
  constructor
  · simpa [bneg] using hp.1
  · simpa [bneg] using
      (rows_bounded_bscale (a := [-1]) (m := 0) (n := inner) (by simp) hp.2)

theorem Bounded.sub {p q : Bi} {outer inner : ℕ}
    (hp : Bounded p outer inner) (hq : Bounded q outer inner) :
    Bounded (bsub p q) outer inner := by
  exact hp.add hq.neg

theorem Bounded.pow {p : Bi} {outer inner : ℕ}
    (hp : Bounded p outer inner) (n : ℕ) :
    Bounded (bpow p n) (n * outer) (n * inner) := by
  induction n with
  | zero => simp [Bounded, bpow]
  | succ n ih =>
      simpa [bpow, Nat.succ_mul, add_comm] using hp.mul ih

theorem bounded_trace : Bounded trace 0 1 := by
  unfold trace
  exact (bounded_bone.mono (by omega) (by omega)).add bounded_br

theorem bounded_z : Bounded z 1 2 := by
  unfold z
  have hthree : Bounded (brat 3) 0 2 :=
    (bounded_brat 3).mono (by omega) (by omega)
  have htwoR : Bounded (bmul (brat 2) br) 0 2 :=
    ((bounded_brat 2).mul bounded_br).mono (by omega) (by omega)
  have hr2 : Bounded (bpow br 2) 0 2 := by
    simpa using bounded_br.pow 2
  have hbracket :
      Bounded (bsub (bsub (brat 3) (bmul (brat 2) br)) (bpow br 2)) 0 2 :=
    (hthree.sub htwoR).sub hr2
  have ht : Bounded
      (bmul btau (bsub (bsub (brat 3) (bmul (brat 2) br)) (bpow br 2))) 1 2 := by
    simpa using bounded_btau.mul hbracket
  simpa using (bounded_brat (1 / 12)).mul ht

theorem bounded_pair : Bounded pair 1 2 := by
  unfold pair
  have hr2 : Bounded (bpow br 2) 0 2 := by
    simpa using bounded_br.pow 2
  have hfirst : Bounded (bmul (brat (1 / 3)) (bpow br 2)) 1 2 :=
    ((bounded_brat (1 / 3)).mul hr2).mono (by omega) (by omega)
  have hsecond : Bounded (bmul (brat (2 / 3)) br) 1 2 :=
    ((bounded_brat (2 / 3)).mul bounded_br).mono (by omega) (by omega)
  exact (hfirst.add hsecond).add bounded_z

theorem bounded_feedback : Bounded feedback 1 3 := by
  unfold feedback
  have hleft : Bounded (badd bone (bmul (brat (1 / 3)) br)) 0 1 :=
    bounded_bone.mono (by omega) (by omega) |>.add
      ((bounded_brat (1 / 3)).mul bounded_br)
  have hr2 : Bounded (bpow br 2) 1 2 :=
    (bounded_br.pow 2).mono (by omega) (by omega)
  have hright :
      Bounded (badd (bmul (brat (1 / 9)) (bpow br 2)) z) 1 2 :=
    (((bounded_brat (1 / 9)).mul hr2).mono (by omega) (by omega)).add bounded_z
  simpa using hleft.mul hright

theorem derivativeTriple_bounded (n : ℕ) :
    Bounded (derivativeTriple n).1 (n / 2) n ∧
      Bounded (derivativeTriple n).2.1 ((n + 1) / 2) (n + 1) ∧
      Bounded (derivativeTriple n).2.2 ((n + 2) / 2) (n + 2) := by
  induction n with
  | zero =>
      simp only [derivativeTriple, initialTriple]
      exact ⟨bounded_bone, bounded_bzero 0 1, bounded_bzero 1 2⟩
  | succ n ih =>
      simp only [derivativeTriple, nextTriple]
      refine ⟨ih.2.1, ih.2.2, ?_⟩
      have ht := bounded_trace.mul ih.2.2
      have hp := bounded_pair.mul ih.2.1
      have hf := bounded_feedback.mul ih.1
      have ht' : Bounded (bmul trace (derivativeTriple n).2.2)
          ((n + 3) / 2) (n + 3) := ht.mono (by omega) (by omega)
      have hp' : Bounded (bmul pair (derivativeTriple n).2.1)
          ((n + 3) / 2) (n + 3) := hp.mono (by omega) (by omega)
      have hf' : Bounded (bmul feedback (derivativeTriple n).1)
          ((n + 3) / 2) (n + 3) := hf.mono (by omega) (by omega)
      exact (ht'.sub hp').add hf'

theorem derivative_bounded (n : ℕ) :
    Bounded (derivative n) (n / 2) n := by
  exact (derivativeTriple_bounded n).1

theorem derivativeTableAux_spec (n : ℕ) :
    (derivativeTableAux n).1.reverse = (List.range n).map derivative ∧
      (derivativeTableAux n).2 = derivativeTriple n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      simp only [derivativeTableAux]
      rw [ih.2]
      constructor
      · rw [List.reverse_cons, ih.1, List.range_succ, List.map_append]
        simp [derivative]
      · rfl

theorem derivativeTable_eq (count : ℕ) :
    derivativeTable count = (List.range count).map derivative := by
  exact (derivativeTableAux_spec count).1

theorem derivativeTable_getD {count j : ℕ} (hj : j < count) :
    (derivativeTable count).getD j bzero = derivative j := by
  rw [derivativeTable_eq, List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem curvatureTerm_bounded {N j : ℕ} (hj : j ≤ N) :
    Bounded
      (bmul (brat (kernel N j))
        (bmul (derivative j) (derivative (N - j))))
      (N / 2) N := by
  have hp := (derivative_bounded j).mul (derivative_bounded (N - j))
  have hp' : Bounded (bmul (derivative j) (derivative (N - j)))
      (N / 2) N := hp.mono (by omega) (by omega)
  simpa using (bounded_brat (kernel N j)).mul hp'

theorem foldl_badd_bounded {α : Type*} {l : List α} {f : α → Bi}
    {acc : Bi} {outer inner : ℕ}
    (hacc : Bounded acc outer inner)
    (hf : ∀ a ∈ l, Bounded (f a) outer inner) :
    Bounded (l.foldl (fun p a => badd p (f a)) acc) outer inner := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons a l ih =>
      apply ih (hacc.add (hf a (by simp)))
      intro b hb
      exact hf b (by simp [hb])

theorem curvatureCoefficient_bounded (N : ℕ) :
    Bounded (curvatureCoefficient N) (N / 2) N := by
  unfold curvatureCoefficient
  dsimp only
  apply foldl_badd_bounded (bounded_bzero (N / 2) N)
  intro j hj
  have hjN : j ≤ N := Nat.le_of_lt_succ (List.mem_range.mp hj)
  rw [derivativeTable_getD (Nat.lt_succ_of_le hjN),
    derivativeTable_getD (Nat.lt_succ_of_le (Nat.sub_le N j))]
  exact curvatureTerm_bounded hjN

theorem curvatureCoefficient_outer_degree {N : ℕ} :
    (curvatureCoefficient N).length ≤ N / 2 + 1 :=
  (curvatureCoefficient_bounded N).1

theorem curvatureCoefficient_inner_degree {N b : ℕ} :
    ((curvatureCoefficient N).getD b []).length ≤ N + 1 := by
  by_cases hb : b < (curvatureCoefficient N).length
  · apply (curvatureCoefficient_bounded N).2
    rw [List.getD_eq_getElem _ _ hb]
    exact List.getElem_mem hb
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

end ComplexCoeff

end SSP.K3CyclicComplex
