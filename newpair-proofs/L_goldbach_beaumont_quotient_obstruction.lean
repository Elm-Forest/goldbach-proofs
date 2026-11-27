import Mathlib

/-! In every nontrivial residue ring, the prime 2 and a larger composite
number have the same image modulo m. The composite is 2*(m+1). -/

theorem PEqualNP.Outside.L_goldbach_beaumont_quotient_obstruction :
    ∀ m : ℕ, 1 < m →
      ∃ a b : ℕ, a ≠ b ∧ a % m = b % m ∧ Nat.Prime a ∧ ¬ Nat.Prime b := by
  intro m hm
  refine ⟨2, 2 * (m + 1), ?_, ?_, Nat.prime_two, ?_⟩
  · omega
  · calc
      2 % m = (2 * m + 2) % m := by simp [Nat.add_mod]
      _ = (2 * (m+1)) % m := by congr 1; omega
  · intro hp
    have hdvd : 2 ∣ 2 * (m+1) := by simp
    rcases hp.eq_one_or_self_of_dvd 2 hdvd with h | h
    · omega
    · omega
