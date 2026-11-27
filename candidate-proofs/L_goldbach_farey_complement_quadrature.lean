import Mathlib

open Set MeasureTheory

namespace GoldbachFarey

/-- Coordinates in the unimodular basis of the two neighboring fractions. -/
private theorem between_endpoints {a q b s Q d c : ℕ}
    (hdet : b*q = a*s+1) (hn : Q < q+s) (hd : 0 < d) (hdQ : d ≤ Q)
    {x δ : ℝ} (hδ : 0 ≤ δ) (hl : δ < (q:ℝ)*x-a) (hr : δ < (b:ℝ)-s*x) :
    δ < |(d:ℝ)*x-c| := by
  let X : ℤ := (b:ℤ)*d-s*c
  let Y : ℤ := (q:ℤ)*c-a*d
  have hD : (b:ℤ)*q-a*s = 1 := by
    have h : (b:ℤ)*q = (a:ℤ)*s+1 := by exact_mod_cast hdet
    linarith
  have den : (q:ℤ)*X+s*Y = d := by
    calc
      _ = (d:ℤ)*((b:ℤ)*q-a*s) := by dsimp [X,Y]; ring
      _ = _ := by rw [hD, mul_one]
  have num : (a:ℤ)*X+b*Y = c := by
    calc
      _ = (c:ℤ)*((b:ℤ)*q-a*s) := by dsimp [X,Y]; ring
      _ = _ := by rw [hD, mul_one]
  have coords : (d:ℝ)*x-c = (X:ℝ)*((q:ℝ)*x-a) - (Y:ℝ)*((b:ℝ)-s*x) := by
    have hd' : (q:ℝ)*X+s*Y = d := by exact_mod_cast den
    have hc' : (a:ℝ)*X+b*Y = c := by exact_mod_cast num
    rw [← hd', ← hc']
    ring
  have opposite : (1 ≤ X ∧ Y ≤ 0) ∨ (X ≤ 0 ∧ 1 ≤ Y) := by
    have nq : (0:ℤ) ≤ q := Int.natCast_nonneg _
    have ns : (0:ℤ) ≤ s := Int.natCast_nonneg _
    have pos : (0:ℤ) < d := by exact_mod_cast hd
    have small : (d:ℤ) < q+s := by exact_mod_cast hdQ.trans_lt hn
    by_cases hX : 0 < X
    · refine Or.inl ⟨by omega, ?_⟩
      by_contra! hY
      have hx : 1 ≤ X := by omega
      have hy : 1 ≤ Y := by omega
      nlinarith only [mul_le_mul_of_nonneg_left hx nq, mul_le_mul_of_nonneg_left hy ns, den, small]
    · refine Or.inr ⟨by omega, ?_⟩
      by_contra! hY
      have hx : X ≤ 0 := by omega
      have hy : Y ≤ 0 := by omega
      linarith only [mul_nonpos_of_nonneg_of_nonpos nq hx, mul_nonpos_of_nonneg_of_nonpos ns hy, den, pos]
  rw [coords]
  rcases opposite with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · have h1 : (1:ℝ) ≤ X := by exact_mod_cast hx
    have h0 : (Y:ℝ) ≤ 0 := by exact_mod_cast hy
    have h := mul_le_mul_of_nonneg_right h1 (hδ.trans hl.le)
    have k := mul_nonpos_of_nonpos_of_nonneg h0 (hδ.trans hr.le)
    exact lt_of_lt_of_le (by linarith : δ < (X:ℝ)*(q*x-a)-(Y:ℝ)*(b-s*x)) (le_abs_self _)
  · have h0 : (X:ℝ) ≤ 0 := by exact_mod_cast hx
    have h1 : (1:ℝ) ≤ Y := by exact_mod_cast hy
    have h := mul_le_mul_of_nonneg_right h1 (hδ.trans hr.le)
    have k := mul_nonpos_of_nonpos_of_nonneg h0 (hδ.trans hl.le)
    exact lt_of_lt_of_le (by linarith : δ < -((X:ℝ)*(q*x-a)-(Y:ℝ)*(b-s*x))) (neg_le_abs _)

private theorem endpoints_coprime {a q b s : ℕ} (h : b*q = a*s+1) :
    a.Coprime q ∧ b.Coprime s := by
  have cancel {g : ℕ} (h1 : g ∣ b*q) (h2 : g ∣ a*s) : g = 1 := by
    have hd := Nat.dvd_sub h1 h2
    rw [h, Nat.add_sub_cancel_left] at hd
    exact Nat.dvd_one.mp hd
  exact ⟨cancel ((Nat.gcd_dvd_right a q).mul_left b) ((Nat.gcd_dvd_left a q).mul_right s),
    cancel ((Nat.gcd_dvd_left b s).mul_right q) ((Nat.gcd_dvd_right b s).mul_left a)⟩

private def arcs (Q : ℕ) (δ : ℝ) :=
  {t : ℝ | ∃ d c : ℕ, 1 ≤ d ∧ d ≤ Q ∧ c ≤ d ∧ c.Coprime d ∧ |t-(c:ℝ)/d| ≤ δ/d}

private theorem scaled_error (x : ℝ) (c d : ℕ) (hd : 0 < d) :
    |(d:ℝ)*x-c| = |x-(c:ℝ)/d| * (d:ℝ) := by
  have h : (0:ℝ) < d := by exact_mod_cast hd
  calc
    _ = |(x-(c:ℝ)/d)*(d:ℝ)| := by congr 1; field_simp [h.ne']
    _ = _ := by rw [abs_mul, abs_of_pos h]

private theorem cell {Q a q b s : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ Q) (hs : 1 ≤ s)
    (hsQ : s ≤ Q) (ha : a ≤ q) (hb : b ≤ s) (hdet : b*q = a*s+1)
    (hgap : Q < q+s) {δ : ℝ} (hδ : 0 ≤ δ) :
    (arcs Q δ)ᶜ ∩ Icc ((a:ℝ)/q) ((b:ℝ)/s) = Ioo (((a:ℝ)+δ)/q) (((b:ℝ)-δ)/s) := by
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  obtain ⟨ha',hb'⟩ := endpoints_coprime hdet
  ext t
  constructor
  · rintro ⟨hmiss,hlo,hhi⟩
    have left : δ/q < |t-(a:ℝ)/q| :=
      lt_of_not_ge fun h => hmiss ⟨q,a,hq,hqQ,ha,ha',h⟩
    have right : δ/s < |t-(b:ℝ)/s| :=
      lt_of_not_ge fun h => hmiss ⟨s,b,hs,hsQ,hb,hb',h⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)] at left
    rw [abs_of_nonpos (sub_nonpos.mpr hhi)] at right
    constructor
    · rw [add_div]; linarith
    · rw [sub_div]; linarith
  · rintro ⟨hl,hr⟩
    have hl' := (div_lt_iff₀ hq').mp hl
    have hr' := (lt_div_iff₀ hs').mp hr
    constructor
    · rintro ⟨d,c,hd,hdQ,_,_,hh⟩
      have he := between_endpoints (x := t) (c := c) hdet hgap hd hdQ hδ
        (by linarith only [hl', mul_comm t (q:ℝ)]) (by linarith only [hr',mul_comm t (s:ℝ)])
      rw [scaled_error _ _ _ hd] at he
      exact he.not_ge ((le_div_iff₀ (by exact_mod_cast hd : (0:ℝ) < d)).mp hh)
    · exact ⟨(div_le_iff₀ hq').mpr (by linarith), (le_div_iff₀ hs').mpr (by linarith)⟩


private theorem leaf_length {Q a q b s : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ Q)
    (hs : 1 ≤ s) (hsQ : s ≤ Q) (ha : a ≤ q) (hb : b ≤ s) (hdet : b*q = a*s+1)
    (hgap : Q < q+s) {δ : ℝ} (hδ : 0 ≤ δ) :
    volume ((arcs Q δ)ᶜ ∩ Icc ((a:ℝ)/q) ((b:ℝ)/s)) =
      ENNReal.ofReal ((1-δ*((q:ℝ)+s))/((q:ℝ)*s)) := by
  rw [cell hq hqQ hs hsQ ha hb hdet hgap hδ, Real.volume_Ioo]
  congr 1
  have h : (b:ℝ)*q = (a:ℝ)*s+1 := by exact_mod_cast hdet
  field_simp [show (q:ℝ) ≠ 0 by positivity, show (s:ℝ) ≠ 0 by positivity]
  linarith only [h]

/-- Refine a unimodular interval by its mediant until the sum of its
denominators exceeds the cutoff. -/
private theorem find_leaf (Q a q b s : ℕ) (x : ℝ) (hq : 1 ≤ q) (hqQ : q ≤ Q)
    (hs : 1 ≤ s) (hsQ : s ≤ Q) (ha : a ≤ q) (hb : b ≤ s) (hdet : b*q = a*s+1)
    (hx : x ∈ Icc ((a:ℝ)/q) ((b:ℝ)/s)) :
    ∃ A U B V : ℕ, 1 ≤ U ∧ U ≤ Q ∧ 1 ≤ V ∧ V ≤ Q ∧ A ≤ U ∧ B ≤ V ∧ B*U=A*V+1 ∧
      Q < U+V ∧ x ∈ Icc ((A:ℝ)/U) ((B:ℝ)/V) := by
  by_cases small : q+s ≤ Q
  · have hsum : a+b ≤ q+s := Nat.add_le_add ha hb
    by_cases left : x ≤ (((a+b:ℕ):ℝ)/(q+s:ℕ))
    · have hleft : (a+b)*q = a*(q+s)+1 := by nlinarith only [hdet]
      exact find_leaf Q a q (a+b) (q+s) x hq hqQ (by omega) small ha hsum hleft ⟨hx.1,left⟩
    · have hright : b*(q+s) = (a+b)*s+1 := by nlinarith only [hdet]
      exact find_leaf Q (a+b) (q+s) b s x (by omega) small hs hsQ hsum hb hright ⟨le_of_not_ge left,hx.2⟩
  · exact ⟨a,q,b,s,hq,hqQ,hs,hsQ,ha,hb,hdet,lt_of_not_ge small,hx⟩
termination_by 2*Q-(q+s)
decreasing_by all_goals omega

/-- Common divisors divide the determinant. -/
private theorem coprime_den {a q b s : ℕ} (h : b*q = a*s+1) : q.Coprime s := by
  have hd := Nat.dvd_sub ((Nat.gcd_dvd_left q s).mul_left b) ((Nat.gcd_dvd_right q s).mul_left a)
  rw [h, Nat.add_sub_cancel_left] at hd
  exact Nat.dvd_one.mp hd

private theorem no_interior {Q a q b s c d : ℕ} (hdet : b*q=a*s+1) (hgap : Q<q+s)
    (hq : 0 < q) (hs : 0 < s) (hd : 0 < d) (hdQ : d ≤ Q) :
    (c:ℝ)/d ∉ Ioo ((a:ℝ)/q) ((b:ℝ)/s) := by
  rintro ⟨h1,h2⟩
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have h1 := (div_lt_iff₀ hq').mp h1
  have h2 := (lt_div_iff₀ hs').mp h2
  have bad := between_endpoints (c := c) hdet hgap hd hdQ (le_refl (0:ℝ))
    (show 0 < q*((c:ℝ)/d)-a by linarith only [h1, mul_comm ((c:ℝ)/d) (q:ℝ)])
    (show 0 < (b:ℝ)-s*((c:ℝ)/d) by linarith only [h2,mul_comm ((c:ℝ)/d) (s:ℝ)])
  simp [mul_div_cancel₀, hd'.ne'] at bad

private def valid (q s : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 ≤ q ∧ p.2 ≤ s ∧ p.2*q=p.1*s+1

/-- Subtraction on a coprime denominator pair reverses one mediant step. -/
private theorem exists_points (q s : ℕ) (hq : 0 < q) (hs : 0 < s) (h : q.Coprime s) :
    ∃ p : ℕ × ℕ, valid q s p := by
  rcases lt_trichotomy q s with hlt | heq | hgt
  · obtain ⟨⟨a,b⟩,ha,hb,hd⟩ := exists_points q (s-q) hq (by omega)
      ((Nat.coprime_sub_self_right hlt.le).mpr h)
    refine ⟨(a,a+b),ha,by omega,?_⟩
    dsimp at *
    have hqsum : q+(s-q)=s := by omega
    rw [← hqsum]
    nlinarith only [hd]
  · subst s
    have h1 : q = 1 := by simpa [Nat.Coprime] using h
    subst q
    exact ⟨(0,1),by norm_num [valid]⟩
  · obtain ⟨⟨a,b⟩,ha,hb,hd⟩ := exists_points (q-s) s (by omega) hs
      ((Nat.coprime_sub_self_left hgt.le).mpr h)
    refine ⟨(a+b,b),by omega,hb,?_⟩
    dsimp at *
    have hqsum : (q-s)+s=q := by omega
    rw [← hqsum]
    nlinarith only [hd]
termination_by q+s
decreasing_by all_goals omega

private noncomputable def points (q s : ℕ) : ℕ × ℕ := by
  classical
  exact if h : ∃ p : ℕ × ℕ, valid q s p then h.choose else (0,0)

private theorem points_valid {q s : ℕ} (hq : 0 < q) (hs : 0 < s) (h : q.Coprime s) :
    valid q s (points q s) := by
  unfold points
  rw [dite_eq_left (exists_points q s hq hs h)]
  exact (exists_points q s hq hs h).choose_spec

private theorem unique_points {q s a b a' b' : ℕ} (hq : 0 < q)
    (h : valid q s (a,b)) (h' : valid q s (a',b')) : (a,b)=(a',b') := by
  obtain ⟨ha,hb,hd⟩ := h
  obtain ⟨ha',hb',hd'⟩ := h'
  dsimp at *
  have hl {u v : ℕ} (hu : u ≤ q) (hv : v ≤ s) (hd : v*q=u*s+1) : u < q := by
    apply lt_of_le_of_ne hu
    rintro rfl
    nlinarith only [Nat.mul_le_mul_right u hv,hd]
  have hmod : a*s+1 ≡ a'*s+1 [MOD q] := by rw [← hd, ← hd']; simp [Nat.ModEq]
  have hm := Nat.ModEq.cancel_right_of_coprime (coprime_den hd) (hmod.add_right_cancel' 1)
  have haeq : a=a' := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hl ha hb hd), Nat.mod_eq_of_lt (hl ha' hb' hd')] using hm
  subst a'
  have hbeq := Nat.eq_of_mul_eq_mul_right hq (hd.trans hd'.symm)
  exact Prod.ext rfl hbeq

private theorem den_of_fraction_eq {a q c d : ℕ} (hq : 0 < q) (hd : 0 < d)
    (ha : a.Coprime q) (hc : c.Coprime d) (he : (a:ℝ)/q=(c:ℝ)/d) : q=d := by
  have hq' : (q:ℝ) ≠ 0 := by positivity
  have hd' : (d:ℝ) ≠ 0 := by positivity
  have h : a*d=c*q := by exact_mod_cast (div_eq_div_iff hq' hd').mp he
  apply Nat.dvd_antisymm
  · exact ha.symm.dvd_of_dvd_mul_left (h ▸ dvd_mul_left _ _)
  · exact hc.symm.dvd_of_dvd_mul_left (h.symm ▸ dvd_mul_left _ _)

private def denoms (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).filter (fun p => Q < p.1+p.2 ∧ p.1.Coprime p.2)

private theorem mem_denoms {Q : ℕ} {p : ℕ × ℕ} :
    p ∈ denoms Q ↔ (1 ≤ p.1 ∧ p.1 ≤ Q) ∧ (1 ≤ p.2 ∧ p.2 ≤ Q) ∧ Q < p.1+p.2 ∧ p.1.Coprime p.2 := by
  simp only [denoms, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_assoc]

private noncomputable def gapInterval (δ : ℝ) (p : ℕ × ℕ) : Set ℝ :=
  let ab := points p.1 p.2
  Ioo (((ab.1:ℝ)+δ)/p.1) (((ab.2:ℝ)-δ)/p.2)

private theorem as_cell {Q : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {p : ℕ × ℕ} (hp : p ∈ denoms Q) :
    let ab := points p.1 p.2
    (arcs Q δ)ᶜ ∩ Icc ((ab.1:ℝ)/p.1) ((ab.2:ℝ)/p.2) = gapInterval δ p := by
  obtain ⟨⟨hq,hqQ⟩,⟨hs,hsQ⟩,hh,hc⟩ := mem_denoms.mp hp
  obtain ⟨ha,hb,hd⟩ := points_valid hq hs hc
  exact cell hq hqQ hs hsQ ha hb hd hh hδ

private theorem gap_union {Q : ℕ} (hQ : 0 < Q) (δ : ℝ) (hδ : 0 ≤ δ) :
    (arcs Q δ)ᶜ ∩ Icc 0 1 = ⋃ p ∈ denoms Q, gapInterval δ p := by
  ext t
  simp only [mem_iUnion]
  constructor
  · rintro ⟨hout,hx⟩
    have hstart : t ∈ Icc ((0:ℝ)/1) ((1:ℝ)/1) := by simpa using hx
    obtain ⟨a,q,b,s,hq,hqQ,hs,hsQ,ha,hb,hdet,hgap,ht⟩ := find_leaf Q 0 1 1 1 t
      (by decide) hQ (by decide) hQ (by decide) (by decide) (by decide) (by simpa using hstart)
    have hc := coprime_den hdet
    have hp : (q,s) ∈ denoms Q := mem_denoms.mpr ⟨⟨hq,hqQ⟩,⟨hs,hsQ⟩,hgap,hc⟩
    have he : (a,b) = points q s :=
      unique_points hq (show valid q s (a,b) from ⟨ha,hb,hdet⟩) (points_valid hq hs hc)
    refine ⟨(q,s),hp,?_⟩
    rw [← as_cell hδ hp]
    exact ⟨hout,by simpa only [← he] using ht⟩
  · rintro ⟨p,hp,ht⟩
    rw [← as_cell hδ hp] at ht
    obtain ⟨⟨hq,_⟩,⟨hs,_⟩,_,hc⟩ := mem_denoms.mp hp
    obtain ⟨_,hb,_⟩ := points_valid hq hs hc
    exact ⟨ht.1, (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans ht.2.1,
      ht.2.2.trans ((div_le_one (by exact_mod_cast hs : (0:ℝ)<p.2)).mpr (by exact_mod_cast hb))⟩

private theorem inside_gap {δ : ℝ} (hδ : 0 ≤ δ) {p : ℕ × ℕ} {x : ℝ}
    (hx : x ∈ gapInterval δ p) :
    x ∈ Ioo (((points p.1 p.2).1:ℝ)/p.1) (((points p.1 p.2).2:ℝ)/p.2) := by
  obtain ⟨hl,hr⟩ := hx
  simp only [add_div,sub_div] at hl hr
  have l := div_nonneg hδ (Nat.cast_nonneg p.1)
  have r := div_nonneg hδ (Nat.cast_nonneg p.2)
  exact ⟨by linarith,by linarith⟩

private theorem same_endpoints {l r u v x : ℝ} (hx : x ∈ Ioo l r) (hy : x ∈ Ioo u v)
    (hu : u ∉ Ioo l r) (hv : v ∉ Ioo l r) (hl : l ∉ Ioo u v) (hr : r ∉ Ioo u v) :
    l=u ∧ r=v := by
  obtain ⟨hlx,hxr⟩ := hx
  obtain ⟨hux,hxv⟩ := hy
  exact ⟨le_antisymm (le_of_not_gt fun h => hl ⟨h,hlx.trans hxv⟩)
    (le_of_not_gt fun h => hu ⟨h,hux.trans hxr⟩),
    le_antisymm (le_of_not_gt fun h => hv ⟨hlx.trans hxv,h⟩)
    (le_of_not_gt fun h => hr ⟨hux.trans hxr,h⟩)⟩

private theorem pairwise_gaps {Q : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    PairwiseDisjoint (↑(denoms Q)) (gapInterval δ) := by
  intro p hp z hz hne
  apply Set.disjoint_left.mpr
  intro t ht ht'
  obtain ⟨⟨hq,hqQ⟩,⟨hs,hsQ⟩,hh,hc⟩ := mem_denoms.mp hp
  obtain ⟨⟨hu,huQ⟩,⟨hv,hvQ⟩,hh',hc'⟩ := mem_denoms.mp hz
  obtain ⟨_,_,hd⟩ := points_valid hq hs hc
  obtain ⟨_,_,hd'⟩ := points_valid hu hv hc'
  have e := same_endpoints (inside_gap hδ ht) (inside_gap hδ ht')
    (no_interior hd hh hq hs hu huQ) (no_interior hd hh hq hs hv hvQ)
    (no_interior hd' hh' hu hv hq hqQ) (no_interior hd' hh' hu hv hs hsQ)
  obtain ⟨hl,hr⟩ := endpoints_coprime hd
  obtain ⟨hl',hr'⟩ := endpoints_coprime hd'
  exact hne (Prod.ext (den_of_fraction_eq hq hu hl hl' e.1) (den_of_fraction_eq hs hv hr hr' e.2))

private theorem complement_volume {Q : ℕ} (hQ : 0 < Q) {δ : ℝ} (hδ : 0 ≤ δ) :
    volume ((arcs Q δ)ᶜ ∩ Icc 0 1) =
      ∑ p ∈ denoms Q, ENNReal.ofReal ((1-δ*((p.1:ℝ)+p.2))/((p.1:ℝ)*p.2)) := by
  rw [gap_union hQ δ hδ, measure_biUnion_finset (pairwise_gaps hδ) (fun _ _ => measurableSet_Ioo)]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨⟨hq,hqQ⟩,⟨hs,hsQ⟩,hh,hc⟩ := mem_denoms.mp hp
  obtain ⟨ha,hb,hd⟩ := points_valid hq hs hc
  rw [← as_cell hδ hp]
  exact leaf_length hq hqQ hs hsQ ha hb hd hh hδ

private theorem covers_iff {Q : ℕ} (hQ : 0 < Q) {δ : ℝ} (hδ : 0 ≤ δ) :
    Icc (0:ℝ) 1 ⊆ arcs Q δ ↔ 1 ≤ δ*((Q:ℝ)+1) := by
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQ
  constructor
  · intro cover
    by_contra! small
    let t : ℝ := 1 / ((Q:ℝ)+1)
    have ht : 0 < t := by dsimp [t]; positivity
    have he : t * ((Q:ℝ)+1) = 1 := by dsimp [t]; field_simp
    have hδt : δ < t := by
      exact (lt_div_iff₀ (by positivity : 0 < (Q:ℝ)+1)).mpr small
    have hx : t ∈ Icc (0:ℝ) 1 := ⟨ht.le, (div_le_one (by positivity : 0<(Q:ℝ)+1)).mpr (by linarith)⟩
    have hgap : t ∈ Ioo (((0:ℝ)+δ)/1) (((1:ℝ)-δ)/Q) := by
      constructor
      · simpa using hδt
      · apply (lt_div_iff₀ hQR).mpr
        linarith only [he,hδt]
    have hcell := cell (Q := Q) (a := 0) (q := 1) (b := 1) (s := Q) (by decide) hQ hQ
      (le_refl _) (by decide) hQ (by simp) (by omega) hδ
    norm_num only [Nat.cast_zero,Nat.cast_one] at hcell
    have hmem : t ∈ (arcs Q δ)ᶜ ∩ Icc (0:ℝ) ((1:ℝ)/Q) := by
      rw [hcell]
      simpa using hgap
    exact hmem.1 (cover hx)
  · intro h t ht
    by_contra ht'
    have hmem : t ∈ (arcs Q δ)ᶜ ∩ Icc (0:ℝ) 1 := ⟨ht',ht⟩
    rw [gap_union hQ δ hδ] at hmem
    obtain ⟨p,hp'⟩ := mem_iUnion.mp hmem
    obtain ⟨hp,hx⟩ := mem_iUnion.mp hp'
    obtain ⟨⟨hq,_⟩,⟨hs,_⟩,hh,hc⟩ := mem_denoms.mp hp
    obtain ⟨_,_,hdet⟩ := points_valid hq hs hc
    have hq' : (0:ℝ) < p.1 := by exact_mod_cast hq
    have hs' : (0:ℝ) < p.2 := by exact_mod_cast hs
    let ab := points p.1 p.2
    have hd : (ab.2:ℝ)*p.1=(ab.1:ℝ)*p.2+1 := by exact_mod_cast hdet
    have hl := mul_lt_mul_of_pos_right ((div_lt_iff₀ hq').mp hx.1) hs'
    have hr := mul_lt_mul_of_pos_right ((lt_div_iff₀ hs').mp hx.2) hq'
    have hsum : (Q:ℝ)+1 ≤ (p.1:ℝ)+p.2 := by exact_mod_cast hh
    have bad := h.trans (mul_le_mul_of_nonneg_left hsum hδ)
    dsimp only [ab] at hd
    nlinarith only [hl,hr,hd,bad]

private theorem integrate_gaps {Q : ℕ} (hQ : 0 < Q) {δ : ℝ} (hδ : 0 ≤ δ)
    (f : ℝ → ℂ) (hf : IntegrableOn f (Icc 0 1)) :
    (∫ x in (arcs Q δ)ᶜ ∩ Icc 0 1, f x) = ∑ p ∈ denoms Q, ∫ x in gapInterval δ p, f x := by
  rw [gap_union hQ δ hδ]
  apply integral_biUnion_finset _ (fun _ _ => measurableSet_Ioo) (pairwise_gaps hδ)
  intro p hp
  apply hf.mono_set
  intro x hx
  have hem : x ∈ ⋃ p ∈ denoms Q, gapInterval δ p := mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,hx⟩⟩
  rw [← gap_union hQ δ hδ] at hem
  exact hem.2

end GoldbachFarey

open GoldbachFarey

/-- The complement of the project's reduced-rational arcs has an exact measure and
a disjoint integration formula, even when the original arcs overlap. -/
theorem PEqualNP.Outside.L_goldbach_farey_complement_quadrature :
    ∀ (Q : ℕ) (δ : ℝ), 0 < Q → 0 ≤ δ →
      let A := {x : ℝ | ∃ d c : ℕ, 1 ≤ d ∧ d ≤ Q ∧ c ≤ d ∧ c.Coprime d ∧ |x-(c:ℝ)/d| ≤ δ/d}
      let D := ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).filter (fun p => Q < p.1+p.2 ∧ p.1.Coprime p.2)
      (Set.Icc (0:ℝ) 1 ⊆ A ↔ 1 ≤ δ*((Q:ℝ)+1)) ∧
      MeasureTheory.volume (Aᶜ ∩ Set.Icc (0:ℝ) 1) =
        ∑ p ∈ D, ENNReal.ofReal ((1-δ*((p.1:ℝ)+p.2))/((p.1:ℝ)*p.2)) ∧
      ∃ ab : ℕ × ℕ → ℕ × ℕ,
        (∀ p ∈ D, (ab p).1 ≤ p.1 ∧ (ab p).2 ≤ p.2 ∧ (ab p).2*p.1 = (ab p).1*p.2+1) ∧
        ∀ f : ℝ → ℂ, MeasureTheory.IntegrableOn f (Set.Icc 0 1) →
          (∫ x in Aᶜ ∩ Set.Icc (0:ℝ) 1, f x) =
            ∑ p ∈ D, ∫ x in Set.Ioo ((((ab p).1:ℝ)+δ)/p.1) ((((ab p).2:ℝ)-δ)/p.2), f x := by
  intro Q δ hQ hδ A D
  refine ⟨covers_iff hQ hδ, complement_volume hQ hδ, fun p => points p.1 p.2, ?_, ?_⟩
  · intro p hp
    obtain ⟨⟨hq,_⟩,⟨hs,_⟩,_,hc⟩ := mem_denoms.mp hp
    exact points_valid hq hs hc
  · intro f h
    exact integrate_gaps hQ hδ f h
