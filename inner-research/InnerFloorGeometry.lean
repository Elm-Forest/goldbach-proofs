import Mathlib

/- Geometry reduction only; this file does not claim the published asymptotic estimate. -/
namespace InnerFloorResearch

def arcSet (B : ℕ) (r n : ℝ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ r / ((q : ℝ) * n)}

theorem arcSet_mono {B C : ℕ} {r s n : ℝ}
    (hB : B ≤ C) (hr : r ≤ s) (hn : 0 ≤ n) :
    arcSet B r n ⊆ arcSet C s n := by
  intro t ht
  obtain ⟨q,a,hq,hqb,ha,hcop,hclose⟩ := ht
  exact ⟨q,a,hq,hqb.trans hB,ha,hcop,hclose.trans
    (div_le_div_of_nonneg_right hr (mul_nonneg (Nat.cast_nonneg q) hn))⟩

theorem inner_remainder_eq (Q B : ℕ) (r R u n : ℝ)
    (hr : r ≤ R) (hu : u ≤ R) (hn : 0 ≤ n) :
    (((arcSet B R n \ arcSet Q r n) \
      (arcSet Q R n \ arcSet Q r n)) ∩ arcSet B u n) =
      arcSet B u n \ arcSet Q R n := by
  have hA := arcSet_mono (B := Q) (C := Q) (r := r) (s := R) le_rfl hr hn
  have hI := arcSet_mono (B := B) (C := B) (r := u) (s := R) le_rfl hu hn
  ext t
  constructor
  · rintro ⟨⟨⟨hw,ha⟩,hl⟩,hi⟩
    exact ⟨hi,fun h => hl ⟨h,ha⟩⟩
  · rintro ⟨hi,hl⟩
    have ha : t ∉ arcSet Q r n := fun h => hl (hA h)
    exact ⟨⟨⟨hI hi,ha⟩,fun h => hl h.1⟩,hi⟩

theorem medium_witness (Q B : ℕ) (u R n : ℝ)
    (hu : u ≤ R) (hn : 0 ≤ n) {t : ℝ}
    (ht : t ∈ arcSet B u n \ arcSet Q R n) :
    ∃ q a : ℕ, Q < q ∧ 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / (q : ℝ)| ≤ u / ((q : ℝ) * n) := by
  obtain ⟨hi,hl⟩ := ht
  obtain ⟨q,a,hq,hqb,ha,hcop,hclose⟩ := hi
  have hlarge : Q < q := by
    by_contra! hsmall
    apply hl
    exact ⟨q,a,hq,hsmall,ha,hcop,hclose.trans
      (div_le_div_of_nonneg_right hu (mul_nonneg (Nat.cast_nonneg q) hn))⟩
  exact ⟨q,a,hlarge,hq,hqb,ha,hcop,hclose⟩


/-- Separation for two reduced rational windows with independently specified widths.
The cross-multiplication argument adapts MajorNumeratorDilation's
cross_eq_of_overlap (Apache-2.0; original separation credited to wzhxzkk, PR 153). -/
theorem overlap_center_eq {q r a b : ℕ} {u v n t : ℝ}
    (hq : 0 < q) (hr : 0 < r) (hn : 0 < n)
    (hc : a.Coprime q) (hd : b.Coprime r)
    (hsmall : u*(r:ℝ)+v*(q:ℝ)<n)
    (ha : |t-(a:ℝ)/q| ≤ u/((q:ℝ)*n))
    (hb : |t-(b:ℝ)/r| ≤ v/((r:ℝ)*n)) :
    q=r ∧ a=b := by
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have hrr : 0 < (r:ℝ) := by exact_mod_cast hr
  have hprod : 0 < (q:ℝ)*r := mul_pos hqr hrr
  have hrad : u/((q:ℝ)*n)+v/((r:ℝ)*n)<1/((q:ℝ)*r) := by
    calc
      _ = (u*(r:ℝ)+v*(q:ℝ))/((q:ℝ)*r*n) := by
        field_simp
      _ < n/((q:ℝ)*r*n) := (div_lt_div_iff_of_pos_right (by positivity)).2 hsmall
      _ = _ := by field_simp
  have he : a*r=b*q := by
    by_contra hne
    have hsep : 1/((q:ℝ)*r) ≤ |(a:ℝ)/q - b/r| := by
      rw [show (a:ℝ)/q - b/r = (a*r-b*q)/(q*r) by field_simp,
        abs_div, abs_of_pos hprod]
      apply (div_le_div_iff_of_pos_right hprod).2
      rcases lt_or_gt_of_ne hne with hab | hba
      · have hgap : (a:ℝ)*r + 1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
        linarith [neg_le_abs ((a:ℝ)*r-b*q)]
      · have hgap : (b:ℝ)*q + 1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
        linarith [le_abs_self ((a:ℝ)*r-b*q)]
    have ht := abs_sub_le ((a:ℝ)/q) t ((b:ℝ)/r)
    rw [abs_sub_comm ((a:ℝ)/q) t] at ht
    linarith
  have hdiv1 : q ∣ r := hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left q b)
  have hdiv2 : r ∣ q := hd.symm.dvd_of_dvd_mul_left (he.symm ▸ dvd_mul_left r a)
  obtain rfl := Nat.dvd_antisymm hdiv1 hdiv2
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

def mediumBand (Q B : ℕ) (u n : ℝ) : Set ℝ :=
  {t | ∃ q a : ℕ, Q<q ∧ 1≤q ∧ q≤B ∧ a≤q ∧ a.Coprime q ∧
    |t-(a:ℝ)/q| ≤ u/((q:ℝ)*n)}

/-- The excluded low-modulus mask can be dropped exactly once the rational
separation inequality holds. This statement makes no estimate of prime sums. -/
theorem masked_medium_eq (Q B : ℕ) (u R n : ℝ)
    (hu : 0≤u) (huR : u≤R) (hn : 0<n)
    (hsmall : u*(Q:ℝ)+R*(B:ℝ)<n) :
    arcSet B u n \ arcSet Q R n = mediumBand Q B u n := by
  ext t
  constructor
  · exact fun ht => medium_witness Q B u R n huR hn.le ht
  · rintro ⟨q,a,hqQ,hq,hqB,ha,hcop,hclose⟩
    refine ⟨⟨q,a,hq,hqB,ha,hcop,hclose⟩,?_⟩
    rintro ⟨r,b,hr,hrQ,hb,hd,hnear⟩
    have hsmall' : u*(r:ℝ)+R*(q:ℝ)<n :=
      (add_le_add
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hrQ) hu)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hqB) (hu.trans huR))).trans_lt hsmall
    have he := overlap_center_eq (by omega : 0<q) (by omega : 0<r)
      hn hcop hd hsmall' hclose hnear
    omega

theorem mediumBand_unique (Q B : ℕ) (u n : ℝ) (hu : 0≤u) (hn : 0<n)
    (hsmall : 2*u*(B:ℝ)<n)
    {q r a b : ℕ} {t : ℝ}
    (hq : Q<q) (hr : Q<r) (hqB : q≤B) (hrB : r≤B)
    (hc : a.Coprime q) (hd : b.Coprime r)
    (ha : |t-(a:ℝ)/q| ≤ u/((q:ℝ)*n))
    (hb : |t-(b:ℝ)/r| ≤ u/((r:ℝ)*n)) :
    q=r ∧ a=b := by
  apply overlap_center_eq (by omega : 0<q) (by omega : 0<r) hn hc hd _ ha hb
  have h1 := mul_le_mul_of_nonneg_left (show (q:ℝ)≤B by exact_mod_cast hqB) hu
  have h2 := mul_le_mul_of_nonneg_left (show (r:ℝ)≤B by exact_mod_cast hrB) hu
  linarith

end InnerFloorResearch
