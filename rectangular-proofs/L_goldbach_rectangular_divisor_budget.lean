import Mathlib

/- The harmonic and gcd estimates are adapted from muxkin's goldbach-proofs
PR 2468, commit 3d9be84b446f4e30f46b52e1c83dc7e49e4535d9, Apache-2.0.
The extension to separate rectangular bounds is new here. -/

open Finset
open scoped BigOperators
noncomputable section

private def harmonicBox (M : ℕ) : ℝ := ∑ d ∈ Icc 1 M,(d:ℝ)⁻¹
private def invHit (q u : ℕ) : ℝ := if q∣u then (u:ℝ)⁻¹ else 0

private theorem invHit_nonneg (q u : ℕ) : 0≤ invHit q u := by unfold invHit; split_ifs <;> positivity
private theorem harmonicBox_nonneg (M : ℕ) : 0≤harmonicBox M := sum_nonneg fun _ _ => by positivity

private theorem hitHarmonic (M q : ℕ) (hq : 0<q) :
    (∑ u ∈ Icc 1 M,invHit q u) ≤ (q:ℝ)⁻¹*harmonicBox M := by
  let S := Icc 1 (M/q)
  have hs : (Icc 1 M).filter (q∣·) = S.image (fun k => q*k) := by
    ext u
    constructor
    · intro h
      obtain ⟨huk,huq⟩ := mem_filter.mp h
      obtain ⟨k,rfl⟩ := huq
      obtain ⟨h1,h2⟩ := mem_Icc.mp huk
      exact mem_image.mpr ⟨k,mem_Icc.mpr ⟨by cases k <;> simp_all,
        (Nat.le_div_iff_mul_le hq).mpr (by simpa [mul_comm] using h2)⟩,rfl⟩
    · intro h
      obtain ⟨k,hk,rfl⟩ := mem_image.mp h
      obtain ⟨hk1,hk2⟩ := mem_Icc.mp hk
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hq hk1,by simpa [mul_comm] using (Nat.le_div_iff_mul_le hq).mp hk2⟩,dvd_mul_right _ _⟩
  unfold invHit
  rw [←sum_filter,hs,sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hq h)]
  simp only [Nat.cast_mul,mul_inv,←mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self _ _)) (fun _ _ _ => by positivity)

private theorem gcdHarmonic (M n : ℕ) (hn : 0<n) :
    (∑ q ∈ Icc 1 M, (q.gcd n:ℝ)*(q:ℝ)⁻¹) ≤ n.divisors.card*harmonicBox M := by
  have hb (q : ℕ) (hq : 0<q) :
      (q.gcd n:ℝ)*(q:ℝ)⁻¹ ≤ ∑ d ∈ n.divisors,(d:ℝ)*invHit d q := by
    have hg : q.gcd n ∈ n.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _,hn.ne'⟩
    have hsingle := single_le_sum (f:=fun d : ℕ => (d:ℝ)*invHit d q)
      (fun d hd => mul_nonneg (Nat.cast_nonneg _) (invHit_nonneg _ _)) hg
    simpa [invHit,Nat.gcd_dvd_left] using hsingle
  calc
    _ ≤ ∑ q ∈ Icc 1 M, ∑ d ∈ n.divisors,(d:ℝ)*invHit d q := sum_le_sum fun _ h => hb _ (mem_Icc.mp h).1
    _ = ∑ d ∈ n.divisors,(d:ℝ)*∑ q ∈ Icc 1 M,invHit d q := by rw [sum_comm]; simp only [mul_sum]
    _ ≤ ∑ _ ∈ n.divisors,harmonicBox M := by
      apply sum_le_sum; intro d hd
      have hd0 := Nat.pos_of_mem_divisors hd
      have hdR : (d:ℝ)≠0 := by exact_mod_cast hd0.ne'
      calc
        _ ≤ (d:ℝ)*((d:ℝ)⁻¹*harmonicBox M) := mul_le_mul_of_nonneg_left (hitHarmonic M d hd0) (by positivity)
        _ = _ := by field_simp
    _ = _ := by simp


private theorem rectDivisor (A D : ℕ) (T : ℕ→ℝ) (hT : ∀ q,0≤T q) :
    (∑ u ∈ Icc 1 A, ∑ v ∈ Icc 1 D, ((∑ q ∈ (u.gcd v).divisors,T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹)) ≤
      (∑ q ∈ Icc 1 (min A D),T q*(q:ℝ)⁻¹^2)*harmonicBox A*harmonicBox D := by
  let S := Icc 1 A
  let V := Icc 1 D
  let W := Icc 1 (min A D)
  have he (u v : ℕ) (hu : u∈S) (hv : v∈V) :
      (∑ q ∈ (u.gcd v).divisors,T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹ =
        ∑ q ∈ W,T q*invHit q u*invHit q v := by
    have hu0 := (mem_Icc.mp hu).1
    have hv0 := (mem_Icc.mp hv).1
    have hg0 : 0<u.gcd v := Nat.gcd_pos_of_pos_left _ hu0
    have hdiv : (u.gcd v).divisors = W.filter (fun q => q∣u ∧ q∣v) := by
      ext q
      simp only [W,Nat.mem_divisors,mem_filter,mem_Icc,Nat.dvd_gcd_iff,ne_eq,
        Nat.ne_of_gt hg0,not_false_eq_true,and_true]
      constructor
      · intro h
        exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hu0,
          le_min ((Nat.le_of_dvd hu0 h.1).trans (mem_Icc.mp hu).2)
            ((Nat.le_of_dvd hv0 h.2).trans (mem_Icc.mp hv).2)⟩,h⟩
      · exact And.right
    rw [hdiv,sum_filter,sum_mul,sum_mul]
    apply sum_congr rfl
    intro q hq
    by_cases ha : q∣u <;> by_cases hb : q∣v <;> simp [invHit,ha,hb]
  calc
    _ = ∑ u ∈ S,∑ v ∈ V,∑ q ∈ W,T q*invHit q u*invHit q v := by
      exact sum_congr rfl fun u hu => sum_congr rfl fun v hv => he u v hu hv
    _ = ∑ q ∈ W,T q*(∑ u ∈ S,invHit q u)*(∑ v ∈ V,invHit q v) := by
      trans ∑ u ∈ S, ∑ q ∈ W,∑ v ∈ V,T q*invHit q u*invHit q v
      · exact sum_congr rfl fun _ _ => sum_comm
      · rw [sum_comm]
        apply sum_congr rfl
        intro q hq
        simp only [←mul_sum,←sum_mul]
    _ ≤ ∑ q ∈ W, T q*((q:ℝ)⁻¹*harmonicBox A)*((q:ℝ)⁻¹*harmonicBox D) := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hitHarmonic A q (mem_Icc.mp hq).1) (hT q))
        (hitHarmonic D q (mem_Icc.mp hq).1) (sum_nonneg fun u _ => invHit_nonneg q u)
        (mul_nonneg (hT q) (mul_nonneg (by positivity) (harmonicBox_nonneg A)))
    _ = _ := by
      rw [sum_mul,sum_mul]
      apply sum_congr rfl
      intro q hq
      ring

theorem PEqualNP.Outside.L_goldbach_rectangular_divisor_budget :
    ∀ (A D : ℕ) (T : ℕ→ℝ), (∀ q,0≤T q) →
    (∑ u ∈ Finset.Icc 1 A, ∑ v ∈ Finset.Icc 1 D, ((∑ q ∈ (u.gcd v).divisors,T q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹)) ≤
      (∑ q ∈ Finset.Icc 1 (min A D),T q*(q:ℝ)⁻¹^2)*
      (∑ u ∈ Finset.Icc 1 A,(u:ℝ)⁻¹)*(∑ v ∈ Finset.Icc 1 D,(v:ℝ)⁻¹) := by
  intro A D T hT
  exact rectDivisor A D T hT

end
