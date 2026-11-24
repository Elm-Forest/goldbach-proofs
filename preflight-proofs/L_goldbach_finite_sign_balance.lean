import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_finite_sign_balance :
    ∀ (n m : ℕ) (b : ℕ → Fin m → ℝ), ∃ s : ℕ → ℝ,
      (∀ k, s k = 1 ∨ s k = -1) ∧
      (∑ j, (∑ k ∈ Finset.range n, s k * b k j)^2) ≤
      ∑ j, ∑ k ∈ Finset.range n, (b k j)^2 := by
  intro n m b
  induction n with
  | zero =>
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨s, hs, hb⟩ := ih
    let A : Fin m → ℝ := fun j => ∑ k ∈ Finset.range n, s k * b k j
    let E : ℝ → ℝ := fun z => ∑ j, (A j + z * b n j)^2
    have hpair : E 1 + E (-1) =
        2 * ((∑ j, (A j)^2) + ∑ j, (b n j)^2) := by
      unfold E
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    let z : ℝ := if E 1 ≤ E (-1) then 1 else -1
    have hz : z = 1 ∨ z = -1 := by
      unfold z
      split_ifs <;> simp
    have he : E z ≤ (∑ j, (A j)^2) + ∑ j, (b n j)^2 := by
      unfold z
      split_ifs with h
      · linarith
      · have h' := le_of_lt (lt_of_not_ge h)
        linarith
    refine ⟨fun k => if k = n then z else s k, ?_, ?_⟩
    · intro k
      split_ifs
      · exact hz
      · exact hs k
    · have hinner (j : Fin m) :
          (∑ k ∈ Finset.range (n+1), (if k = n then z else s k) * b k j) =
          A j + z * b n j := by
        rw [Finset.sum_range_succ]
        simp only [if_pos rfl]
        have hsum : (∑ k ∈ Finset.range n, (if k = n then z else s k) * b k j) =
            A j := by
          unfold A
          apply Finset.sum_congr rfl
          intro k hk
          simp [Nat.ne_of_lt (Finset.mem_range.mp hk)]
        rw [hsum]
      calc
        _ = E z := by
          unfold E
          simp only [hinner]
        _ ≤ (∑ j, (A j)^2) + ∑ j, (b n j)^2 := he
        _ ≤ ∑ j, ∑ k ∈ Finset.range (n+1), (b k j)^2 := by
          simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
          exact add_le_add_right hb _
