import Mathlib

theorem PEqualNP.Outside.L_lib_124 :
    ∀ p' q : ℕ, p' < q → ∀ k : ℕ, ∃ i : ℕ, 2 * k * p' ^ i ≤ q ^ i := by
  intro p' q hpq k
  have hstep : p' + 1 ≤ q := Nat.succ_le_of_lt hpq
  have hgrowth : ∀ n : ℕ, (p' + n) * p' ^ n ≤ p' * q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        (p' + (n + 1)) * p' ^ (n + 1) =
            ((p' + n + 1) * p') * p' ^ n := by rw [pow_succ]; ring
        _ ≤ ((p' + n) * (p' + 1)) * p' ^ n := by
          apply Nat.mul_le_mul_right
          nlinarith
        _ = ((p' + n) * p' ^ n) * (p' + 1) := by ring
        _ ≤ (p' * q ^ n) * q := Nat.mul_le_mul ih hstep
        _ = p' * q ^ (n + 1) := by rw [pow_succ, mul_assoc]
  by_cases hp : p' = 0
  · subst p'
    exact ⟨1, by simp⟩
  · have hpos : 0 < p' := Nat.pos_of_ne_zero hp
    refine ⟨2 * k * p', ?_⟩
    apply Nat.le_of_mul_le_mul_left (c := p') _ hpos
    calc
      p' * (2 * k * p' ^ (2 * k * p')) =
          (2 * k * p') * p' ^ (2 * k * p') := by ring
      _ ≤ (p' + 2 * k * p') * p' ^ (2 * k * p') :=
        Nat.mul_le_mul_right _ (by omega)
      _ ≤ p' * q ^ (2 * k * p') := hgrowth _
