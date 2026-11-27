import Mathlib

/-! A finite doubling cover of the actual integer window starts.
There is no logarithmic loss in summing bounds proportional to block length. -/
open Finset
namespace InnerFloorResearch
noncomputable section

theorem positiveBlockSum_le (f : ℕ → ℝ) (hf : ∀ y, 0 ≤ f y)
    (X N : ℕ) (hX : 0 < X) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ Z : ℕ, X ≤ Z → Z ≤ N →
      (∑ y∈Ico Z (2*Z),f y) ≤ M*(Z:ℝ)) :
    (∑ y∈Ico X N,f y) ≤ 2*M*(N:ℝ) := by
  have H : ∀ L : ℕ, ∀ Z : ℕ, X ≤ Z → N-Z ≤ L →
      (∑ y∈Ico Z N,f y) ≤ M*(2*(N:ℝ)-((min Z N:ℕ):ℝ)) := by
    intro L
    induction L with
    | zero =>
      intro Z hZ hL
      have hNZ : N ≤ Z := by omega
      have hI : Ico Z N = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        have hh := mem_Ico.mp hy
        omega
      simp only [hI,sum_empty,min_eq_right hNZ]
      have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
      nlinarith only [mul_nonneg hM hN]
    | succ L ih =>
      intro Z hZ hL
      by_cases hNZ : N ≤ Z
      · have hI : Ico Z N = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro y hy
          have hh := mem_Ico.mp hy
          omega
        simp only [hI,sum_empty,min_eq_right hNZ]
        have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
        nlinarith only [mul_nonneg hM hN]
      have hZN : Z < N := by omega
      rw [min_eq_left hZN.le]
      by_cases hclose : N ≤ 2*Z
      · have hs : Ico Z N ⊆ Ico Z (2*Z) := by
          intro y hy
          exact mem_Ico.mpr ⟨(mem_Ico.mp hy).1,(mem_Ico.mp hy).2.trans_le hclose⟩
        apply (sum_le_sum_of_subset_of_nonneg hs (fun y _ _ => hf y)).trans
        apply (hb Z hZ hZN.le).trans
        have hR : (Z:ℝ) ≤ N := by exact_mod_cast hZN.le
        nlinarith only [mul_le_mul_of_nonneg_left hR hM]
      · have h2Z : 2*Z < N := by omega
        have h2 : X ≤ 2*Z := by omega
        have hshort : N-2*Z ≤ L := by omega
        have hI : Ico Z N = Ico Z (2*Z) ∪ Ico (2*Z) N := by
          ext y
          simp only [mem_Ico,mem_union]
          omega
        have hdis : Disjoint (Ico Z (2*Z)) (Ico (2*Z) N) := by
          exact disjoint_left.mpr fun y hy hz => (not_lt_of_ge (mem_Ico.mp hz).1) (mem_Ico.mp hy).2
        have hrest := ih (2*Z) h2 hshort
        rw [min_eq_left h2Z.le] at hrest
        rw [hI,sum_union hdis]
        apply (add_le_add (hb Z hZ hZN.le) hrest).trans
        push_cast
        ring_nf
        exact le_rfl
  have h := H (N-X) X le_rfl le_rfl
  apply h.trans
  have hm' : (0:ℝ) ≤ ((min X N:ℕ):ℝ) := Nat.cast_nonneg _
  nlinarith only [mul_nonneg hM hm']

end
end InnerFloorResearch
