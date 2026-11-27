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

end InnerFloorResearch
