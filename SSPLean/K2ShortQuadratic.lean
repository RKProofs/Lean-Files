import SSPLean.K2AllStages

/-!
# The two-variable quadratic in `phase_type_moment_inequality.tex`

This is Lemma 2 of the shorter renewal proof. Only the terminal excursion needs an
Aldous--Shepp second-moment bound. The return variable `a` is merely nonnegative.
-/

set_option autoImplicit false

namespace SSP.K2Short

noncomputable def G (n v a B : ℝ) : ℝ :=
  (n+1)*(3*(1-v)*(2*(1-v)+a+B)+3*a+
    (n+1)/n*(a^2/(1-v)+B^2/v))-(n+2)*(2*(1-v)+a+B)^2

noncomputable def Qa (n v : ℝ) : ℝ := (n+1)^2/(n*(1-v))-(n+2)
noncomputable def QB (n v : ℝ) : ℝ := (n+1)^2/(n*v)-(n+2)
noncomputable def B0 (n v : ℝ) : ℝ := n/(n-1)*v^2
noncomputable def L (n v : ℝ) : ℝ := 2*(n-1)+(n+5)*v-2*n*(n+2)/(n-1)*v^2
noncomputable def F (n v : ℝ) : ℝ :=
  2*v*(1+n*(n+2)*(1-v))-(n-1)*(n+5)*(1-v)

/-- Elementary chord inequality for a concave quadratic. -/
theorem chord_nonneg (A b c l r t : ℝ) (hA : A ≤ 0) (hlr : l < r)
    (htl : l ≤ t) (htr : t ≤ r)
    (hl : 0 ≤ A*l^2+b*l+c) (hr : 0 ≤ A*r^2+b*r+c) :
    0 ≤ A*t^2+b*t+c := by
  have hid : (r-l)*(A*t^2+b*t+c) =
      (r-t)*(A*l^2+b*l+c)+(t-l)*(A*r^2+b*r+c)
        +(-A)*(t-l)*(r-t)*(r-l) := by ring
  have hneg : 0 ≤ -A := neg_nonneg.mpr hA
  have hrt : 0 ≤ r-t := by linarith
  have htl : 0 ≤ t-l := by linarith
  have hrl : 0 ≤ r-l := by linarith
  have hp : 0 ≤ (r-l)*(A*t^2+b*t+c) := by
    rw [hid]
    positivity
  exact nonneg_of_mul_nonneg_right hp (sub_pos.mpr hlr)

theorem corner_identity (n v : ℝ) (hn : n ≠ 0) (hn1 : n ≠ 1)
    (_hv : v ≠ 0) (hh : 1-v ≠ 0) :
    G n v 0 (B0 n v) =
      (2*(n-1)*(1-v)^2+4*n*(1-v)*v+n*v^2)/(n-1)^2
        *(v-(n-1)*(1-v))^2 := by
  unfold G B0
  field_simp [hn, hn1, _hv, hh]
  ring

theorem corner_nonneg (n v : ℝ) (hn : 2 ≤ n) (hv0 : 0 < v) (hv1 : v < 1) :
    0 ≤ G n v 0 (B0 n v) := by
  have hh : 0 ≤ 1-v := by linarith
  have hn1 : 0 ≤ n-1 := by linarith
  rw [corner_identity n v (by linarith) (by linarith) (ne_of_gt hv0) (by linarith)]
  positivity

theorem coefficients (n v : ℝ) (hn : 2 ≤ n) (hv0 : 0 < v) (hv1 : v < 1) :
    0 < Qa n v ∧ 0 < QB n v ∧ 0 < Qa n v*QB n v-(n+2)^2 := by
  have hn0 : 0 < n := by linarith
  have hh : 0 < 1-v := by linarith
  have ea : Qa n v = (1+n*(n+2)*v)/(n*(1-v)) := by
    unfold Qa
    field_simp
    ring
  have eb : QB n v = (1+n*(n+2)*(1-v))/(n*v) := by
    unfold QB
    field_simp
    ring
  have ed : Qa n v*QB n v-(n+2)^2 = (n+1)^2/(n^2*(1-v)*v) := by
    unfold Qa QB
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [ea]; positivity
  · rw [eb]; positivity
  · rw [ed]; positivity

/-- A feasible vertex on the `a=0` edge lies below the explicit threshold. -/
theorem vertex_threshold (n v : ℝ) (hn : 2 ≤ n) (hv0 : 0 < v) (hv1 : v < 1)
    (hf : F n v < 0) : v < 8*(n-1)/(9*n) := by
  let t := 8*(n-1)/(9*n)
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]
    rw [div_lt_one (by positivity)]
    linarith
  have he : F n t = (n-1)*(n+5)*(7*n+8)/(81*n) := by
    dsimp [t]
    unfold F
    field_simp
    ring
  have hend : 0 ≤ F n t := by rw [he]; positivity
  by_contra hnot
  have htv : t ≤ v := le_of_not_gt hnot
  have hch := chord_nonneg (-2*n*(n+2))
    (2+2*n*(n+2)+(n-1)*(n+5)) (-(n-1)*(n+5)) t 1 v
    (by nlinarith) ht1 htv hv1.le
    (by convert hend using 1; simp [F]; ring)
    (by ring_nf; norm_num)
  have : 0 ≤ F n v := by convert hch using 1; unfold F; ring
  linarith

/-- The two exceptional cubic certificates, expanded at their thresholds. -/
theorem cubic_three_pos (v : ℝ) (hv : 3/4 < v) :
    0 < 21*v^3-19*v^2+8*v-4 := by
  have he : 21*v^3-19*v^2+8*v-4 =
      21*(v-3/4)^3+113/4*(v-3/4)^2+239/16*(v-3/4)+11/64 := by ring
  rw [he]
  positivity

theorem cubic_four_pos (v : ℝ) (hv : 5/6 < v) :
    0 < 101*v^3-135*v^2+108*v-54 := by
  have he : 101*v^3-135*v^2+108*v-54 =
      101*(v-5/6)^3+235/2*(v-5/6)^2+1121/12*(v-5/6)+151/216 := by ring
  rw [he]
  positivity

/-- Negative slope on the lower `B` edge forces a positive discriminant complement. -/
theorem lower_edge_discriminant (n : ℕ) (hn : 2 ≤ n) (v : ℝ)
    (hv0 : 0 < v) (hv1 : v < 1) (hL : L n v < 0) :
    0 ≤ 4*Qa n v*G n v 0 (B0 n v)-(L n v)^2 := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hh : 0 < 1-v := by linarith
  have hn1 : (0 : ℝ) < n-1 := by linarith
  by_cases hn5 : 5 ≤ n
  · have hn5r : (5 : ℝ) ≤ n := by exact_mod_cast hn5
    have he : (n : ℝ)^2-4*n-3 = ((n : ℝ)-5)*(n+1)+2 := by ring
    have hpoly : 0 < (n : ℝ)^2-4*n-3 := by rw [he]; positivity
    have hch := chord_nonneg (-2*(n : ℝ)*(n+2)/(n-1)) (n+5) (2*(n-1))
      0 1 v (by
        apply div_nonpos_of_nonpos_of_nonneg
        · nlinarith
        · linarith) (by norm_num) hv0.le hv1.le
      (by norm_num; linarith) (by
        have he1 : -2*(n : ℝ)*(n+2)/(n-1)+(n+5)+2*(n-1) =
            ((n : ℝ)^2-4*n-3)/(n-1) := by field_simp [ne_of_gt hn1]; ring
        have hp : 0 ≤ ((n : ℝ)^2-4*n-3)/(n-1) := by positivity
        convert he1.symm ▸ hp using 1; ring)
    have : 0 ≤ L n v := by convert hch using 1; unfold L; ring
    linarith
  · have hcases : n=2 ∨ n=3 ∨ n=4 := by omega
    rcases hcases with rfl | rfl | rfl
    · have hvt : 5/9 < v := by
        by_contra hnot
        have hc := chord_nonneg (-16) 7 2 0 (5/9) v (by norm_num)
          (by norm_num) hv0.le (le_of_not_gt hnot) (by norm_num) (by norm_num)
        norm_num [L] at hL
        linarith
      have hid : 2*(1-v)*(4*Qa 2 v*G 2 v 0 (B0 2 v)-(L 2 v)^2) =
          18*v^2*(9*v-5) := by
        unfold Qa G B0 L
        field_simp
        ring
      have hr : 0 ≤ 18*v^2*(9*v-5) := by
        have : 0 < 9*v-5 := by linarith
        positivity
      exact nonneg_of_mul_nonneg_right (hid.symm ▸ hr) (by positivity)
    · have hvt : 3/4 < v := by
        by_contra hnot
        have hc := chord_nonneg (-15) 8 4 0 (3/4) v (by norm_num)
          (by norm_num) hv0.le (le_of_not_gt hnot) (by norm_num) (by norm_num)
        norm_num [L] at hL
        linarith
      have hid : 3*(1-v)*(4*Qa 3 v*G 3 v 0 (B0 3 v)-(L 3 v)^2) =
          8*(21*v^3-19*v^2+8*v-4) := by
        unfold Qa G B0 L
        field_simp
        ring
      have hr : 0 ≤ 8*(21*v^3-19*v^2+8*v-4) := by
        have := cubic_three_pos v hvt
        positivity
      exact nonneg_of_mul_nonneg_right (hid.symm ▸ hr) (by positivity)
    · have hvt : 5/6 < v := by
        by_contra hnot
        have hc := chord_nonneg (-16) 9 6 0 (5/6) v (by norm_num)
          (by norm_num) hv0.le (le_of_not_gt hnot) (by norm_num) (by norm_num)
        norm_num [L] at hL
        linarith
      have hid : 4*(1-v)*(4*Qa 4 v*G 4 v 0 (B0 4 v)-(L 4 v)^2) =
          20/9*(101*v^3-135*v^2+108*v-54) := by
        unfold Qa G B0 L
        field_simp
        ring
      have hr : 0 ≤ 20/9*(101*v^3-135*v^2+108*v-54) := by
        have := cubic_four_pos v hvt
        positivity
      exact nonneg_of_mul_nonneg_right (hid.symm ▸ hr) (by positivity)

/-- Lemma 2: the simplified renewal quadratic is nonnegative on its feasible quadrant. -/
theorem quadratic_nonneg (n : ℕ) (hn : 2 ≤ n) (v a B : ℝ)
    (hv0 : 0 < v) (hv1 : v < 1) (ha : 0 ≤ a) (hB : B0 n v ≤ B) :
    0 ≤ G n v a B := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < n-1 := by linarith
  have hh : 0 < 1-v := by linarith
  obtain ⟨hQa, hQB, hdet⟩ := coefficients n v hnr hv0 hv1
  let C := G n v 0 (B0 n v)
  let gB := 2*QB n v*B0 n v-(n+5)*(1-v)
  have hC : 0 ≤ C := corner_nonneg n v hnr hv0 hv1
  have hid : ∀ x y, G n v x (B0 n v+y) =
      SSP.K2AllStages.quad2 C (L n v) gB (2*Qa n v) (-2*(n+2)) (2*QB n v) x y := by
    intro x y
    dsimp [C, gB]
    unfold G Qa QB B0 L SSP.K2AllStages.quad2
    field_simp
    ring
  have hstar : (-2*(n+2))*gB-(2*QB n v)*L n v < 0 := by
    have he : n*v*((-2*(n+2))*gB-(2*QB n v)*L n v) =
        -2*(n+1)*(3+(2*(n : ℝ)^2-5)*(1-v)) := by
      dsimp [gB]
      unfold QB B0 L
      field_simp
      ring
    have hnn : 0 < 2*(n : ℝ)^2-5 := by nlinarith
    have hr : -2*(n+1)*(3+(2*(n : ℝ)^2-5)*(1-v)) < 0 := by
      have : 0 < 2*(n+1)*(3+(2*(n : ℝ)^2-5)*(1-v)) := by positivity
      linarith
    have hm : n*v*((-2*(n+2))*gB-(2*QB n v)*L n v) < 0 := he.symm ▸ hr
    exact neg_of_mul_neg_right hm (by positivity)
  have hfaceB : ∀ y, 0 ≤ y → 0 ≤
      SSP.K2AllStages.quad2 C (L n v) gB (2*Qa n v) (-2*(n+2)) (2*QB n v) 0 y := by
    intro y hy
    have hd : gB < 0 → 0 ≤ 2*(2*QB n v)*C-gB^2 := by
      intro hg
      have heF : (n-1)*gB = F n v := by
        dsimp [gB]
        unfold QB B0 F
        field_simp
        ring
      have hf : F n v < 0 := by rw [← heF]; exact mul_neg_of_pos_of_neg hn1 hg
      have ht := vertex_threshold n v hnr hv0 hv1 hf
      have hvbound : 0 < 8*(n-1)-9*n*v := by
        rw [lt_div_iff₀ (by positivity)] at ht
        linarith
      have he : 2*(2*QB n v)*C-gB^2 =
          (n+1)^2*(1-v)^2/(n*v)*(8*(n-1)-9*n*v) := by
        dsimp [C, gB]
        unfold QB G B0
        field_simp
        ring
      rw [he]
      positivity
    have hc := SSP.K2AllStages.quad1_nonneg C gB (2*QB n v) y hC (by positivity) hy hd
    simpa [SSP.K2AllStages.quad2] using hc
  have hfaceA : ∀ x, 0 ≤ x → 0 ≤
      SSP.K2AllStages.quad2 C (L n v) gB (2*Qa n v) (-2*(n+2)) (2*QB n v) x 0 := by
    intro x hx
    have hd : L n v < 0 → 0 ≤ 2*(2*Qa n v)*C-(L n v)^2 := by
      intro hg
      have ht := lower_edge_discriminant n hn v hv0 hv1 hg
      dsimp [C]
      nlinarith
    have hc := SSP.K2AllStages.quad1_nonneg C (L n v) (2*Qa n v) x hC (by positivity) hx hd
    simpa [SSP.K2AllStages.quad2] using hc
  have hc := SSP.K2AllStages.quad2_nonneg_on_quadrant C (L n v) gB
    (2*Qa n v) (-2*(n+2)) (2*QB n v) (by positivity)
    (by nlinarith) hstar hfaceB hfaceA a (B-B0 n v) ha (sub_nonneg.mpr hB)
  rw [← hid] at hc
  simpa using hc

end SSP.K2Short
