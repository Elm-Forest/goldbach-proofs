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

private def rectCost (n M B H u v : ℕ) : ℝ :=
  (1+Real.log ((n:ℝ)+2))^2 + (M:ℝ)*(u.gcd v:ℝ)^2/((u:ℝ)*v) +
  (n:ℝ)/((u:ℝ)*v) *
    ((∑ q ∈ (u.gcd v).divisors.filter (·≤B),(q.gcd n:ℝ)*q/H) +
     ∑ q ∈ (u.gcd v).divisors.filter (B<·),(q.gcd n:ℝ))

private theorem rectCostBound (n A D B H : ℕ) (hn : 0<n) (hB : 0<B) (hH : B≤H) :
    (∑ u ∈ Icc 1 A,∑ v ∈ Icc 1 D,rectCost n (max A D) B H u v) ≤
      (A:ℝ)*D*(1+Real.log ((n:ℝ)+2))^2 +
      (A:ℝ)*D*harmonicBox A*harmonicBox D +
      ((n:ℝ)/B)*n.divisors.card*harmonicBox (min A D)*harmonicBox A*harmonicBox D := by
  let X := Icc 1 A
  let Y := Icc 1 D
  let W := Icc 1 (min A D)
  let M := max A D
  let K := fun (f : ℕ→ℝ) (u v : ℕ) => (∑ q ∈ (u.gcd v).divisors,f q)*(u:ℝ)⁻¹*(v:ℝ)⁻¹
  let f := fun q : ℕ => (q:ℝ)^2
  let t := fun q : ℕ => (q.gcd n:ℝ)*q
  have hbR : 0<(B:ℝ) := by exact_mod_cast hB
  have hHH : (B:ℝ)≤H := by exact_mod_cast hH
  have HA (u v : ℕ) (hu : u∈X) :
      rectCost n M B H u v ≤ (1+Real.log ((n:ℝ)+2))^2+(M:ℝ)*K f u v + ((n:ℝ)/B)*K t u v := by
    have hg : 0<u.gcd v := Nat.gcd_pos_of_pos_left _ (mem_Icc.mp hu).1
    let s := (u.gcd v).divisors
    have hl : (u.gcd v:ℝ)^2 ≤ ∑ q ∈ s,f q := by
      exact single_le_sum (f:=f) (fun _ _ => sq_nonneg _) (Nat.mem_divisors.mpr ⟨dvd_rfl,hg.ne'⟩)
    have hk : (∑ q ∈ s.filter (·≤B),(q.gcd n:ℝ)*q/H)+(∑ q ∈ s.filter (B<·),(q.gcd n:ℝ)) ≤
        (∑ q ∈ s,t q)/B := by
      rw [sum_filter,sum_filter,←sum_add_distrib,sum_div]
      apply sum_le_sum
      intro q hq
      by_cases hqB : q≤B
      · simp only [hqB,not_lt.mpr hqB,ite_true,ite_false,add_zero,t]
        exact div_le_div_of_nonneg_left (by positivity) hbR hHH
      · simp only [hqB,lt_of_not_ge hqB,ite_true,ite_false,zero_add,t]
        apply (le_div_iff₀ hbR).mpr
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show B≤q by omega)) (by positivity)
    unfold rectCost
    change _ + _ + ((n:ℝ)/_)* _ ≤ _
    have hl' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl
      (inv_nonneg.mpr (Nat.cast_nonneg u))) (inv_nonneg.mpr (Nat.cast_nonneg v))) (Nat.cast_nonneg M)
    have hk' := mul_le_mul_of_nonneg_left hk (by positivity : 0≤(n:ℝ)/((u:ℝ)*v))
    have hmiddle : (M:ℝ)*(u.gcd v:ℝ)^2/((u:ℝ)*v) ≤ (M:ℝ)*K f u v := by
      simpa only [K,s,div_eq_mul_inv,mul_inv,mul_assoc] using hl'
    calc
      _ ≤ (1+Real.log ((n:ℝ)+2))^2+(M:ℝ)*K f u v + ((n:ℝ)/((u:ℝ)*v))*((∑ q ∈ s,t q)/B) :=
        by exact add_le_add (add_le_add le_rfl hmiddle) hk'
      _ = _ := by simp only [K,s,div_eq_mul_inv,mul_inv]; ring
  have hf := rectDivisor A D f (fun q => sq_nonneg _)
  have ht := rectDivisor A D t (fun q => by dsimp only [t]; positivity)
  have hF : (∑ q ∈ W,f q * (q:ℝ)⁻¹^2)= ((min A D:ℕ):ℝ) := by
    calc
      _ = ∑ _ ∈ W,(1:ℝ) := by
        apply sum_congr rfl
        intro q hq
        dsimp only [f]
        have hx : (q:ℝ)≠0 := by exact_mod_cast (show 0<q from (mem_Icc.mp hq).1).ne'
        field_simp
      _ = _ := by simp [W]
  have hT : (∑ q ∈ W,t q * (q:ℝ)⁻¹^2)≤n.divisors.card*harmonicBox (min A D) := by
    apply le_trans _ (gcdHarmonic (min A D) n hn)
    apply sum_le_sum
    intro q hq
    dsimp only [t]
    have hx : (q:ℝ)≠0 := by exact_mod_cast (show 0<q from (mem_Icc.mp hq).1).ne'
    exact le_of_eq (by field_simp)
  change _ ≤ (∑ q ∈ W,f q*_) * _ * _ at hf
  rw [hF] at hf
  change _ ≤ (∑ q ∈ W,t q*_) * _ * _ at ht
  have hτ := ht.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT
    (harmonicBox_nonneg A)) (harmonicBox_nonneg D))
  have hMM : (M:ℝ)*((min A D:ℕ):ℝ) = (A:ℝ)*D := by
    dsimp [M]
    by_cases h : A≤D
    · rw [max_eq_right h,min_eq_left h]
      ring
    · rw [max_eq_left (le_of_not_ge h),min_eq_right (le_of_not_ge h)]
  calc
    _ ≤ ∑ u ∈ X,∑ v ∈ Y,((1+Real.log ((n:ℝ)+2))^2+(M:ℝ)*K f u v+((n:ℝ)/B)*K t u v) :=
      sum_le_sum fun u hu => sum_le_sum fun v _ => HA u v hu
    _ = (A:ℝ)*D*(1+Real.log ((n:ℝ)+2))^2+(M:ℝ)*(∑ u ∈ X,∑ v ∈ Y,K f u v)+
          ((n:ℝ)/B)*(∑ u ∈ X,∑ v ∈ Y,K t u v) := by
      simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,X,Y,Nat.card_Icc,Nat.add_sub_cancel]
      ring
    _ ≤ _ := by
      have ha := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg M)
      have hb := mul_le_mul_of_nonneg_left hτ (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg B))
      change (M:ℝ)*(∑ u ∈ X,∑ v ∈ Y,K f u v) ≤ _ at ha
      change ((n:ℝ)/B)*(∑ u ∈ X,∑ v ∈ Y,K t u v) ≤ _ at hb
      have ha' : (M:ℝ)*(∑ u ∈ X,∑ v ∈ Y,K f u v) ≤
          (A:ℝ)*D*harmonicBox A*harmonicBox D := by
        apply ha.trans_eq
        rw [← hMM]
        ring
      linarith

theorem Conjectures.Goldbach.RectangularCornerBudget :
    ∀ (n A D B H : ℕ), 0<n → 0<B → B≤H →
      let L := fun N : ℕ => ∑ q ∈ Finset.Icc 1 N,(q:ℝ)⁻¹
      let C := fun u v : ℕ => (1+Real.log ((n:ℝ)+2))^2 +
        ((max A D:ℕ):ℝ)*(u.gcd v:ℝ)^2/((u:ℝ)*v) +
        (n:ℝ)/((u:ℝ)*v) *
          ((∑ q ∈ (u.gcd v).divisors.filter (·≤B),(q.gcd n:ℝ)*q/H) +
           ∑ q ∈ (u.gcd v).divisors.filter (B<·),(q.gcd n:ℝ))
      (∑ u ∈ Finset.Icc 1 A,∑ v ∈ Finset.Icc 1 D,C u v) ≤
        (A:ℝ)*D*(1+Real.log ((n:ℝ)+2))^2 +
        (A:ℝ)*D*L A*L D + ((n:ℝ)/B)*n.divisors.card*L (min A D)*L A*L D := by
  intro n A D B H hn hB hH
  exact rectCostBound n A D B H hn hB hH

end
